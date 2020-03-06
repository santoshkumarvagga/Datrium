##############################################################
# Copyright (c) 2012-2020 Datrium, Inc. All rights reserved. #
#                -- Datrium Confidential --                  #
##############################################################

import uuid

import testtypes
import vim
import os
import time
import yaml
import json
import re
import sys
from datetime import datetime

import dalibs.retry as retry
import dalibs.ssh as ssh
import dalibs.popen as subprocess

import Workloads
import upgrade_test_lib

ipprefix = '10.80.'

@testtypes.testbeds('large_HA_dittos')
class VSSProviderTest(testtypes.SystemTest):
    def setUp(self):
        super(VSSProviderTest, self).setUp()

        '''
        Logs to be collected on test failures:
        C:\home\bin\build\
                vss*.pml
                appEvents.log
                sysEvents.log
                vsstrace.log
        C:\programdata\datrium\*
        '''
        self.collect_ga_logs = False
        self.collect_perf_logs = False
        self.dest_dir = "/cygdrive/c/home/bin/build/"

        # Bug 38906: There are friquent failures with connection timeout.
        # Failures started happening after disabling TLS1.0 and installing
        # patch in Windows 2008 OVF. Testing with TLS1.0 for now and monitoring
        # if its Windows patch issue or something wrong with our RPC.
        self.isTLS12 = False
        self.trace_started = False
        self.vswriter_started = False
        self.label = 'Datastore1'
        self.testname = "vssbasetest"
        self._vcobj = None
        self.dva.start()
        self.create_inventory()
        self.configure()
        self.wait_for_datastore_in_vc()
        self.win2k8R2_ovf = 'windows2008R2_vss_TLS10'
        self.test_upgrade = False
        self.test_mem_leak = False
        self.db_list =['model','testDB','employee-db', 'employee_data', \
                       'employee-email@','employee+name',"'(openbracketdb'", \
                       "closebracketdb')'", 'employees#', '#specialcharcterdb@',\
                       'mix-special#chardb@', "('db_with-special#char')"]
        self.multi_db_list = []

    @property
    def vcobj(self):
        if self._vcobj is None:
            self._vcobj = self.dva.vcenters[0].wait_vc()
        return self._vcobj

    def create_inventory(self):
        self.dva.vcenters[0].config_hosts(self.dva.frontends)

    def configure(self, install_vaai=False):
        if self.isTLS12 == True:
            self.logger.info('===================================================')
            self.logger.info('======= Testing VSS with TLS1.0 disabled ==========')
            self.logger.info('===================================================')
            self.win2k8R2_ovf = 'windows2008R2_vss'
            self.dva.setconf('ConfSecureMode.strictFlag=true')
            self.dva.controllers[0].active.check_call('procmgr-cli  restart SysMgmt')
        else:
            self.win2k8R2_ovf = 'windows2008R2_vss_TLS10'

        self.dva.setconf('ConfOS.deinitTimeoutSecs=360')
        # install vaai vib if needed
        if install_vaai:
            for fe in self.dva.frontends:
                # upgrade_vib should handle reboot for vaai vib
                fe.upgrade_vib(vibname=fe.vaai_vibname, vibpath=fe.vaai_vibpath)

        # mount datastore
        is_vib_installed = True
        for fe in self.dva.frontends:
            fe.check_call('/bin/esxcli software acceptance set --level CommunitySupported')
            vib_exists = fe.has_vib(fe.vaai_vibname)
            is_vib_installed &= vib_exists
            status = "%sinstalled" % ("" if vib_exists else "not ")
            self.logger.info("Check: [%s] is %s on [%s]" % (fe.vaai_vibname,
                                                            status, fe.ipaddr))

            self.logger.debug("mounting datastore with label: [%s]" % self.label)
            fe.mount(self.label)

            return is_vib_installed

    def tearDown(self):
        # Stopping DVFS and Snapple process to check for memory leak.
        # I have observed that DVFS takes more than 1 minute to shutdown, so adding
        # kill timeout to be 5 minutes.
        if self.test_mem_leak:
            self.dva.controllers[0].active.check_call('procmgr-cli stop -s -d 380 DVFS')
            self.dva.controllers[0].active.check_call('procmgr-cli  stop -s -d 380 Snapple')
            time.sleep(60)
        cores = self.dva.cores
        assert not cores, cores

    def wait_for_datastore_in_vc(self, timeout=2*60, sleeptime=2):
        '''
        Wait for datastore to be available in VC.
        There is a delay between when ESX claims an NFS Datastore is mounted,
        and when VC is made aware of the Datastore entity.
        '''
        for attempt in retry.retry(timeout=timeout, sleeptime=sleeptime):
            datastores = [x.name for x in self.vcobj.find(vim.Datastore)]
            self.logger.debug('datastores: %s' % datastores)
            if self.label in datastores:
                return

    def get_guest_ip(self, vm):
        '''
        Helper function for getting guest IP.  Retry loop is to be resilient against
        flaky tools / guest IP reporting from VC.
        '''
        for attempt in retry.retry(attempts=240, timeout=240, sleeptime=1):
            vm_ip = vm.guest.ipAddress
            # Make sure ip is assigned by dhcp server
            if vm_ip is not None and ipprefix in vm_ip:
                return vm_ip

    def upload_file(self,
                    ip,
                    file_path):
        try:
            ssh.put(ip,
                    file_path,
                    self.dest_dir,
                    max_connect_attempts=100,
                    connect_timeout=60*60*30,
                    username='Administrator',
                    password='sha1c0w')
        except Exception as e:
            self.logger.error("Exception while uploading file %s : %s" % (file_path, e))
            raise

    def call_win_cmd_output(self,
                            ip,
                            cmd):
        return ssh.check_output(ip,
                                cmd,
                                username='Administrator',
                                password='sha1c0w')


    def prep_test_vm(self, vmname, ovf_path, noVSS, datrium_VSS_agent):
        '''
        1. Deploys a Windows VM.
        2. Installs guest agent.
        '''
        self.logger.info("Deploying VM")
        workload = Workloads.DeployVM.DeployVM(
            vc=self.dva.vcenters[0].ipaddr,
            vc_username=self.dva.vcenters[0].username,
            vc_password=self.dva.vcenters[0].password,
            ovf=ovf_path,
            vmname=vmname,
            datastore_label='Datastore1',
            archivedir=self.runtimedir,
            poweron=True,
            timeout=60*60*120)
        workload.execute()
        workload.wait()
        vm = self.vcobj.vm(vmname)

        ssh.check_call(
            self.get_guest_ip(vm),
            ["mkdir -p %s" % self.dest_dir],
            max_connect_attempts=100,
            connect_timeout=60*60*30,
            username='Administrator',
            password='sha1c0w')

        #Enable timesync on the guest vm
        tools_path = "/cygdrive/c/Program Files/VMware/VMware Tools"
        output = self.call_win_cmd_output(self.get_guest_ip(vm),
                                          "cd '%s'; ./VMwareToolboxCmd.exe timesync enable" % tools_path)

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "vss_test.py"))

        output = self.call_win_cmd_output(self.get_guest_ip(vm),
                                          "cd %s; python vss_test.py -n %s -p datrium#1" %
                                          (self.dest_dir, self.dva.controllers[0].mgmtip))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join('/net/fs-04/tank0/build/workloads/ovf', "HammerDB.tar.gz"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "vsstrace.exe"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "vsstrace.sh"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "Procmon64.exe"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "vswriter.exe"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "vswriter.sh"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "vswriter_config.xml"))
        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "get_Mailbox_directories.py"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "get_eseutil_command.py"))

        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "generate_mail_logs.py"))
        self.upload_file(self.get_guest_ip(vm),
                         os.path.join(os.path.dirname(__file__), "removeTools.bat"))

        # Adding a minute of sleep, as in case of Exchange services are still being started.
        if ovf_path in ['win2012-sql', 'win2012-exch', 'win2016-sql2016', 'win2019-sql2016',
                        'win2016-sql2017', 'win2012R2-exch2013', 'win2016-exch2016-cu14', 'win2019-exch2019']:
            # HKEY_LOCAL_MACHINE\System\CurrentControlSet\Services\VSS\Settings
            self.call_win_cmd(vm,
                              "reg add HKLM\\\\System\\\\CurrentControlSet\\\\Services\\\\VSS\\\\Settings /v IdleTimeout /t REG_DWORD /d 12000000")
            self.call_win_cmd(vm,
                              "reg add HKLM\\\\System\\\\CurrentControlSet\\\\Services\\\\VSS\\\\Settings /v DisableDTCFreeze /t REG_DWORD /d 1")
            self.call_win_cmd(vm,
                              "reg add HKLM\\\\System\\\\CurrentControlSet\\\\Services\\\\VSS\\\\Settings /v DisableKTMFreeze /t REG_DWORD /d 1")
            '''HammerDB.tar.gz contains
            1.'auto_hammerdb.sh' which will create a database
            2.'get_hammer_db_data.py' which will extract all data from table and save it in .csv file
            3. 'hammer_db_workload.py' which will generate workload in sql'''
            self.call_win_cmd(vm,"cd %s; tar -zxf HammerDB.tar.gz -C /cygdrive/c" % (self.dest_dir),False)

            # Sleeping 4 minutes for all services to come up.
            time.sleep(240)
        # disable VSS service.
        if noVSS:
            # HKEY_LOCAL_MACHINE\System\CurrentControlSet\Services\VSS
            self.call_win_cmd(vm,
                              "reg add HKLM\\\\System\\\\CurrentControlSet\\\\Services\\\\VSS /v Start /t REG_DWORD /d 4 /f")
            output = self.call_win_cmd_output(self.get_guest_ip(vm),
                              'sc query "VSS" | findstr STATE')
            if "RUNNING" in output:
                self.call_win_cmd(vm,
                                  "net stop VSS")
            # Sleeping 1 minutes for service to down.
            time.sleep(60)
        if datrium_VSS_agent:
            try:
                if self.test_upgrade:
                    self.start_test('C56803')
                    installers = [
                        'Datrium-VSS-Provider-1.1.0.0.msi',
                        'Datrium-VSS-Provider-1.2.0.0.msi',
                        'Datrium-VSS-Provider-1.3.0.0.msi',
                        'Datrium-VSS-Provider-1.4.0.0.msi',
                        'Datrium-VSS-Provider-1.5.0.0.msi',
                        'Datrium-VSS-Provider-1.6.0.0.msi'
                        ]
                    self.logger.info("Testing upgrades")
                    for installer in installers:
                        self.logger.info("Installing guest agent %s", installer)
                        self.call_win_cmd(vm,
                            "cd %s; msiexec /i %s /quiet /qn /norestart /log install.log NETSHELF_IP=%s ADMIN_PASSWD=%s " %
                            (self.dest_dir, installer, self.dva.controllers[0].mgmtip, 'datrium#1'),
                            False)
                    self.post_test_pass('C56803')
                try:
                    '''Installing latest version of VSS agent, if host supports'''
                    self.call_win_cmd(vm,
                        "cd %s; msiexec /i Datrium-VSS-Provider-1.7.0.0.msi /quiet /qn /norestart /log install.log NETSHELF_IP=%s ADMIN_PASSWD=%s " %
                        (self.dest_dir, self.dva.controllers[0].mgmtip, 'datrium#1'),
                        False)
                except subprocess.CalledProcessError as e:
                    '''for those hosts not compatible for VSS agent 1.7,  VSS agent 1.6 will be installed back'''
                    self.logger.info('This host is not compatible for VSS agent 1.7 and higher')
                    self.call_win_cmd(vm,
                        "cd %s; msiexec /i Datrium-VSS-Provider-1.6.0.0.msi /quiet /qn /norestart /log install.log NETSHELF_IP=%s ADMIN_PASSWD=%s " %
                        (self.dest_dir, self.dva.controllers[0].mgmtip, 'datrium#1'),
                        False)
            except Exception as e:
                self.logger.info('Unexpected Exception raised during VSS Agent installation, %s' %e)
                self.download_file(self.get_guest_ip(vm),
                                   '%s/install.log' % (self.dest_dir))
                raise

            self.logger.info("Deployed VSS VM")
            # wait for guest agent
            self.wait_for_agent(vmname, 600)
        return vm

    def poweron_vm(self, vm):
        '''
        Utility function for powering on a VM.
        '''
        self.logger.info("Powering on %s" % vm.name)
        workload = Workloads.PowerOnVM.PowerOnVM(
            vc=self.dva.vcenters[0].ipaddr,
            vc_username=self.dva.vcenters[0].username,
            vc_password=self.dva.vcenters[0].password,
            vmname=vm.name)
        workload.execute()
        workload.wait()
        return vm

    def poweroff_vm(self, vm):
        '''
        Utility function for powering off a VM.
        '''
        self.logger.info("Powering off %s" % vm.name)
        workload = Workloads.PowerOffVM.PowerOffVM(
            vc=self.dva.vcenters[0].ipaddr,
            vc_username=self.dva.vcenters[0].username,
            vc_password=self.dva.vcenters[0].password,
            vmname=vm.name)
        workload.execute()
        workload.wait()
        return vm

    def shutdown_vm(self, vm):
        '''
        Utility function for shut down vm gracefully.
        '''
        self.logger.info("Shutting down %s" % vm.name)
        workload = Workloads.ShutdownVM.ShutdownVM(
            vc=self.dva.vcenters[0].ipaddr,
            vc_username=self.dva.vcenters[0].username,
            vc_password=self.dva.vcenters[0].password,
            vmname=vm.name)
        workload.execute()
        workload.wait()
        return vm

    def delete_vm(self, vm):
        '''
        Utility function for deleting a VM.
        '''
        self.logger.info("Deleting %s" % vm.name)
        if vm.runtime.powerState == vim.VirtualMachine.PowerState.poweredOn:
            self.poweroff_vm(vm)
        vm.Destroy_Task().wait()

    def get_datrium_snapshots(self, vmId):
        '''
        Utility function for getting most recent Datrium snapshots of a VM.
        '''
        pg_cli = ['protection groups',
                  'snapshots',
                  'show',
                  '11111111-1111-1111-1111-111111111111']
        # Take app consistent snap
        output = self.dva.cli(pg_cli, load_json=True, timeout=0)
        pgSnapId = None
        for snaps in output["summary"]:
            if snaps["name"] == "adhoc_app_consistent_snap":
                pgSnapId = snaps["identifier"]

        output = self.dva.cli([
            'vms',
            'snapshots',
            'show',
            '--output-format', 'json',
            '--vm-id', vmId,
            '--protection-group-snapshot-id', pgSnapId])

        self.logger.info("vm snapshots show output: %s", output)
        summary = yaml.load(output)["summary"]
        assert summary, "No snapshot found"

        return summary

    def prepare_vm(self, test_type='appconsistent', noVSS = False, datrium_VSS_agent = True):
        # Disable SR because this test can run for a while and it
        # takes too long.
        if test_type =='no_VSS':
            vmname = "testvm_noVSS_" + str(time.time())
        elif test_type == 'no_Datrium_VSS_agent':
            vmname = "testvm_no_datrium_VSS_agent_" + str(time.time())
        else:
            vmname = "testvm_" + str(time.time())+ test_type
        self.dva.cli([
            'datastores',
            'sr',
            'disable'])

        ovf_path = self.win2k8R2_ovf
        if test_type == 'sql':
            ovf_path = 'win2012-sql'
        elif test_type == 'win2016-sql-2016':
            ovf_path ='win2016-sql2016'
        elif test_type =='win2019-sql-2016':
            ovf_path = 'win2019-sql2016'
        elif test_type =='win2016-sql-2017':
            ovf_path = 'win2016-sql2017'
        elif test_type == 'exch':
            ovf_path = 'win2012-exch'
        elif test_type == 'win2012R2-exch2013':
            ovf_path = 'win2012R2-exch2013'
        elif test_type == 'no_VSS':
            ovf_path = self.win2k8R2_ovf
        elif test_type == 'no_Datrium_VSS_agent':
            ovf_path = self.win2k8R2_ovf
        elif test_type == 'win2016-exch2016-cu14':
            ovf_path = 'win2016-exch2016-cu14'
        elif test_type == 'win2019-exch2019':
            ovf_path = 'win2019-exch2019'
        else:
            assert test_type == 'appconsistent', "Unknown test_type provided, using ovf path for 'win2k8R2_ovf' instead."

        vm = self.prep_test_vm(vmname, ovf_path, noVSS, datrium_VSS_agent) #"testvm-" + str(time.time()))

        # Test adhoc snapshot
        output = self.dva.cli([
            'vms',
            'show',
            '--output-format', 'json'])
        self.logger.info("vms show result: %s", output)

        parsed_output = yaml.load(output)

        for s in parsed_output["summary"]:
            if s["name"] == vmname:
                vm_summary = s
                break

        return vm, vm_summary

    def start_vss_trace(self, vm, success):
        if not self.collect_ga_logs:
            return
        ip = ''
        try:
            ip = self.get_guest_ip(vm)
            self.trace_started = True
        except Exception as e:
            self.logger.error('Exception while gettign vm ip %s' % e)
            if success:
                raise
            return

        if self.collect_perf_logs:
            self.call_win_cmd(vm,
                              'echo "start c:\\home\\bin\\build\\Procmon64.exe -accepteula /quiet /minimized /backingfile C:\\home\\bin\\build\\vss.pml" > %s/proctrace.bat' %
                              (self.dest_dir),
                              False)

            self.call_win_cmd(vm,
                              'echo "sleep 2" >> %s/proctrace.bat' %
                              (self.dest_dir),
                              False)

            self.call_win_cmd(vm,
                              'cd %s; cmd /c proctrace.bat' %
                              (self.dest_dir),
                              False)

        # start vss trace
        self.vsstrace_started = False
        for i in range(5):
            if self.vsstrace_started:
                break
            self.call_win_cmd(vm,
                              "cd %s; sh ./vsstrace.sh" %
                              (self.dest_dir),
                              False)
            output = self.call_win_cmd_output(ip, "ps auf")
            for l in output.splitlines():
                if 'vsstrace' in l:
                    self.vsstrace_started = True
                    break

    def stop_vss_trace(self, vm):
        ip = ''
        if not self.trace_started:
            return

        ip = self.get_guest_ip(vm)
        assert ip != ''

        if self.collect_perf_logs:
            self.call_win_cmd(vm,
                              '%sProcmon64.exe /quiet /Terminate' % (self.dest_dir),
                              False)

        # Get vss trace logs
        if self.vsstrace_started:
            # sleep some time for vss trace to thaw
            time.sleep(5)
            self.call_win_cmd(vm,
                              "kill -2 $(ps aux | grep 'vsstrace' | awk '{print $1}')",
                              False)


        self.logger.info("=================== Powershell Application logs ==========================")
        self.call_win_cmd(vm,
                          "powershell -Command 'Get-EventLog -LogName Application -After $(Get-Date).AddDays(-1) | Format-Table -Wrap | Out-File -Width 300 C:\\home\\bin\\build\\appEvents.log;[Environment]::Exit(0)'",
                          False)

        self.logger.info("=================== Powershell System logs ==========================")
        self.call_win_cmd(vm,
                          "powershell -Command 'Get-EventLog -LogName System -After $(Get-Date).AddDays(-1) | Format-Table -Wrap | Out-File -Width 300 C:\\home\\bin\\build\\sysEvents.log;[Environment]::Exit(0)'",
                          False)

    def download_file(self, ip, file_path):
        try:
            ssh.get(ip,
                    file_path,
                    self.dva.directory,
                    username='Administrator',
                    password='sha1c0w',
                    max_connect_attempts=100,
                    connect_timeout=60*60*30)
        except Exception as e:
            self.logger.error("Failed downloading file %s, : %s" % (file_path, e))

    def collect_agent_logs(self, vm):
        ip = ''
        if not self.trace_started:
            return

        ip = self.get_guest_ip(vm)
        assert ip != ''

        fl = []
        if self.collect_perf_logs:
            output = self.call_win_cmd_output(ip,
                                              'cd %s; ls vss*.pml' %
                                              (self.dest_dir))

            fl = output.split()
        output = self.call_win_cmd_output(ip,
                                          'cd /cygdrive/c/programdata/datrium; ls')
        logs = output.split()
        for l in logs:
            self.download_file(ip,
                               '/cygdrive/c/programdata/datrium/%s' % (l))

        if self.vsstrace_started:
            fl.append('vsstrace.log')
        fl.append('appEvents.log')
        fl.append('sysEvents.log')
        for f in fl:
            self.download_file(ip,
                               '%s/%s' % (self.dest_dir, f))

    def create_database(self, vm):
    #Create database with special character

        try:
            self.upload_file(self.get_guest_ip(vm),\
                             os.path.join(os.path.dirname(__file__), "create_new_database.py"))
            output = self.call_win_cmd_output(self.get_guest_ip(vm),\
                                              "cd %s; python create_new_database.py" %(self.dest_dir))
            return output

        except Exception as e:
            self.logger.debug('Failed to create database %s' % e)
            raise

    def get_new_databases(self,vm):
    # Extract database list created on current date

        try:
            self.upload_file(self.get_guest_ip(vm),\
                             os.path.join(os.path.dirname(__file__), "get_new_databases.py"))
            output = self.call_win_cmd_output(self.get_guest_ip(vm),\
                                              "cd %s; python get_new_databases.py" %(self.dest_dir))
            return output

        except Exception as e:
            self.logger.debug('Databases not available %s' % e)
            raise

    def check_database_created(self,vm):
        databases = self.get_new_databases(vm)

        #created a list of database that should be created for special character
        db_created =['tempdb','employee-db', 'employee_data', 'employee-email@', \
                     'employee+name',"'(openbracketdb'","closebracketdb')'", \
                     'employees#', '#specialcharcterdb@', 'mix-special#chardb@', "('db_with-special#char')"]

        self.db_num = len(databases)
        if self.db_num > len(db_created):
            for i in range(255):
               db_created.append('databases{}'.format(i))

        for i in range(self.db_num):
            assert db_created[i] in databases

    def create_multi_database(self, vm):
        try:
            self.upload_file(self.get_guest_ip(vm), \
                             os.path.join(os.path.dirname(__file__), "create_multi_db.py"))
            output = self.call_win_cmd_output(self.get_guest_ip(vm),\
                                              "cd %s; python create_multi_db.py" %(self.dest_dir))
            return output

        except Exception as e:
            self.logger.debug('Failed to create database %s' % e)
            raise


    def make_snapshot_isolation_true(self,vm):
        try:
            self.upload_file(self.get_guest_ip(vm), \
                             os.path.join(os.path.dirname(__file__), "snapshot_isolation.py"))
            output = self.call_win_cmd_output(self.get_guest_ip(vm),\
                                              "cd %s; python snapshot_isolation.py" %(self.dest_dir))
            return output

        except Exception as e:
            self.logger.debug('Failed to make snapshot isolation true for databases %s' % e)
            raise

    def get_db_with_snapshotisolation_true(self, vm):
        try:
            self.upload_file(self.get_guest_ip(vm), \
                             os.path.join(os.path.dirname(__file__), "check_db_snapshot_isolation.py"))
            output = self.call_win_cmd_output(self.get_guest_ip(vm),\
                                              "cd %s; python check_db_snapshot_isolation.py" %(self.dest_dir))
            return output

        except Exception as e:
            self.logger.debug('Failed to get databases with snapshot isolation true %s' % e)
            raise

    def check_db_with_snapshotisolation_true(self, vm):
        databases = self.get_db_with_snapshotisolation_true(vm)
        assert 'employee_data' and 'employee-email@' and 'employee+name'in databases

    def db_count_for_log_truncation(self, vm):
        # Will return db_count for more than 250+ database
        if self.db_num > len(self.db_list):
            for i in range(255):
                self.multi_db_list.append('databases{}'.format(i))
        return len(self.multi_db_list)

    def adhoc_snap(self, vm, vm_summary, success, copyonly=True):
        # Do not wait for guest agent in case CRASH consistent snap is expected
        if success:
            self.wait_for_agent(vm_summary["name"], 300)

        self.start_vss_trace(vm, success)

        snap_cli = ['vms',
                'take-snapshot',
                 vm_summary["vmId"],
                '--retention', 'forever',
                '--snapshot-name', 'adhoc_app_consistent_snap',
                '--app-consistent',
                '--output-format', 'json',
                ]
        if copyonly == False:
            snap_cli.append('--app-log-truncation')

        # Take app consistent snap
        output = self.dva.cli(snap_cli, timeout=0)

        self.logger.info("vm take-snapshot output: %s", output)
        task = yaml.load(output)["task"]
        assert task, "Task not found %s" % output
        assert task["state"] == 'SUCCESS', task
        assert task["progress"] == 100, task

        # Verify number of snapshots
        snapshots = self.get_datrium_snapshots(vm_summary["vmId"])
        assert len(snapshots) == 1, "Unexpected number of snapshots %s" % snapshots

        self.stop_vss_trace(vm)
        # Verify consistency
        testPass = True
        consistency = snapshots[0]["consistency"]
        errstr = ''
        if success:
            if consistency is not None and consistency == "CRASH":
                errstr = "Expecting app consistent snapshot, but it is crash consistent"
                self.logger.error(errstr)
                testPass = False
        else:
            if consistency is not None and consistency == "APP":
                errstr = "Expecting crash consistent snapshot, but it is app consistent"
                self.logger.error(errstr)
                testPass = False

        # download logs before asserting
        if not testPass:
            self.collect_agent_logs(vm)

        self.trace_started = False
        self.vsstrace_started = False

        assert testPass, errstr

        keyvalues = task["keyValues"]
        for kv in keyvalues:
            if kv['key'] == 'vmSnapId':
                return kv['val']['stringVal']

        assert False, "No vmSnapId found in task"

    def uninstall_VSS_agent(self, vm, vm_summary):
        self.wait_for_agent(vm_summary["name"], 300)
        try:
            self.call_win_cmd(vm, "cd %s; msiexec /uninstall Datrium-VSS-Provider-1.7.0.0.msi /quiet " %
                           (self.dest_dir), False)
        except Exception as e:
            self.logger.info("Agent uninstallation failed with error %s"% e)
            raise
        fe = self.dva.frontends[0]
        guestInfo = fe.check_output('/opt/datrium/bin/dacli vms show --output-format=json')
        vms = yaml.load(guestInfo)["vms"]
        # After uninstall VSS Agent in vm but detected in host.
        if len(vms) == 1:
            guestAgentUp = True
        else:
            guestAgentUp = False
        assert guestAgentUp, 'VSS Agent is expected to be installed'
        self.poweroff_vm(vm)
        fe.reboot()
        fe.wait_for_reboot()
        # wait for get state of vm on host
        for attempt in retry.retry(attempts=20, timeout=200, sleeptime=10):
            try:
                self.poweron_vm(vm)
                break
            except Exception as e:
                self.logger.debug('The operation is not allowed in the current state.')
        self.get_guest_ip(vm)
        # getting correct guestinfo
        for attempt in retry.retry(attempts=10, timeout=200, sleeptime=20):
            try:
                guestInfo = fe.check_output('/opt/datrium/bin/dacli vms show --output-format=json')
                vms = yaml.load(guestInfo)["vms"]
                break
            except Exception as e:
                self.logger.debug('invalid guestInfo')
        if len(vms) == 1:
            guestAgentUp = True
        else:
            guestAgentUp = False
        assert not guestAgentUp, 'Datrium VSS Agent not uninstalled'
        # take snapshot -app consistent will report the agent is detected, until host is rebooted. snapshot will be crash consistent (not app-consistent).
        vmSnapId = self.adhoc_snap(vm, vm_summary, guestAgentUp)

    @testtypes.stress_disable()
    @testtypes.suites('vss-provider-test')
    def test_vss_provider(self):
        '''
        Tests app consistent snapshot.

        1. Deploys a VM.
        2. Installs guest agent.
        3. Triggers adhoc app consistent snapshot.
        4. Verifies app consistent snapshot was taken.
        5. Restore VM.
        '''
        self.start_test('C12195')
        self.test_upgrade = True
        self.collect_ga_logs = True
        vm, vm_summary = self.prepare_vm('win2012R2-exch2013')

        # Take snap
        vmSnapId = self.adhoc_snap(vm, vm_summary, True)

        # Clean up
        self.delete_vm(vm)
        self.restoreVmSnap(vmSnapId, vm_summary)
        vm = self.vcobj.register_vm("Datastore1", vm_summary['path'], vm_summary['name'])
        self.poweron_vm(vm)
        self.wait_for_agent(vm_summary['name'], 300)
        self.post_test_pass('C12195')

        self.logger.info("=======Test uninstallation of VSS Provider======");
        ######################################
        # Test uninstallation of VSS Provider
        ######################################
        '''
        1. Datrium-vss-agent should not be running.
        2. From ESXi host:
            - dacli guestinfo
            - vm will report vss agent installed, until host is rebooted.
            - take snapshot -app consistent will report the agent is detected, snapshot will
                be crash consistent (not app-consistent) until host is rebooted.
        '''
        self.delete_adhoc_snapshots()
        self.start_test('C12196')
        self.uninstall_VSS_agent(vm, vm_summary)
        self.post_test_pass('C12196')
        self.delete_vm(vm)
        vm, vm_summary = self.prepare_vm('win2012R2-exch2013')

        self.logger.info("=======Test snap_pass_change======");

        ########################
        # Test snap_pass_change
        ########################
        '''
        1. Delete previous snap.
        2. Change admin password.
        3. Verify app consistent snapshot.
        '''

        self.delete_adhoc_snapshots()
        # Change admin password
        self.dva.cli([
                 'config',
                 'password',
                 'set',
                 '--password', 'sha1c0w',
                 '--admin-password', 'datrium#1'])

        # Take snap
        self.adhoc_snap(vm, vm_summary, True)

        self.logger.info("====Test  provider_ip_change ======");
        ###########################
        # Test  provider_ip_change
        ###########################
        '''
        1. Delete previous snapshot.
        2. Change gues IP by adding and removing NIC.
        3. Verify app consistent snapshot.
        '''
        self.start_test('C12198')

        self.delete_adhoc_snapshots()
        ipbefore = self.get_guest_ip(vm)
        network = 'VM Network'
        networkadptr = 'Network adapter 1'

        # fetch adapter name from devices, just in case.
        vm_devices = vm.config.hardware.device
        for dev in vm_devices:
            if isinstance(dev, (vim.VirtualE1000, vim.VirtualVmxnet3)):
                networkadptr = dev.deviceInfo.label

        vm.AddDevices_Task({'nic': network})
        vm.RemoveNic_Task(networkadptr)

        ipafter = self.get_guest_ip(vm)
        # Wait till vm ip is changed
        for attempt in retry.retry(attempts=240, timeout=241, sleeptime=1):
            ipafter = self.get_guest_ip(vm)
            if ipafter != ipbefore:
                break

        self.logger.info("ipbefore = %s, ipafter = %s", ipbefore, ipafter)
        assert ipbefore != ipafter

        # Take snap
        self.adhoc_snap(vm, vm_summary, True)
        self.post_test_pass('C12198')

        self.logger.info("=======Test without_vmwtools======= ");
        #########################
        # Test without_vmwtools
        #########################
        '''
        1. Delete previous snapshot.
        2. Remove vmware tools.
        3. Verify crash consistent snapshot
        '''
        self.start_test('C12252')
        self.delete_adhoc_snapshots()
        self.logger.info("Removing Vmware tools from the guest")

        try:
            dest_dir = "/cygdrive/c/home/bin/build/"
            ssh.put(self.get_guest_ip(vm),
                    os.path.join(os.path.dirname(__file__), "removeTools.bat"),
                    dest_dir,
                    max_connect_attempts=100,
                    connect_timeout=60*60*30)

            ssh.check_call(self.get_guest_ip(vm),
                           "cd %s; cmd /c start /b removeTools.bat  > tools.log" %
                           (dest_dir))
        except (ssh.SSHException, ssh.HostConnectError) as e:
            self.logger.debug('Expected Exception occured while executing removetools %s' % e)
        except Exception as e:
            self.logger.debug('Unexpected Exception occured while executing remove tools %s' % e)
            raise

        self.logger.info("Vmware tools removed from the guest")

        time.sleep(120)

        # Take snap
        self.adhoc_snap(vm, vm_summary, False)
        self.post_test_pass('C12252')

    def create_pg(self,pgname = "PG2"):
        output = self.dva.cli([
                     "protection",
                     "groups",
                     "create", pgname,
                     "--output-format", "json"]);
        pgId = json.loads(output)["groupId"]
        return pgId

    def delete_pg(self, pgId):
        self.dva.cli([
            "protection",
            "groups",
            "delete", pgId,
            "--force"])

    def add_vm_to_pg(self, pgId, vmxPath, logTruncation=False,appConsistent=True):
        pg_cli = ["protection",
              "groups",
              "members", "add", pgId]
        if logTruncation:
            pg_cli.append('--app-log-truncation')
        if appConsistent:
            pg_cli.append('--app-consistent-vm-path')
        else:
            pg_cli.append('--vm-path')
        pg_cli.append(vmxPath)

        self.dva.cli(pg_cli, timeout=0)

    def take_pg_snapshot(self, pgId, vm):
        if type(vm) is list:
            for v in vm:
                self.start_vss_trace(v, True)
        else:
            self.start_vss_trace(vm, True)
        pgsnap_name = "manual_" + str(time.time())
        output = self.dva.cli([
                        "protection",
                        "groups",
                        "take-snapshot", pgId,
                        "--snapshot-name", pgsnap_name,
                        "--retention", "3600",
                        "--output-format", "json"], timeout=0)

        if  type(vm) is list:
            for v in vm:
                self.stop_vss_trace(v)
        else:
            self.stop_vss_trace(vm)
        task = json.loads(output)["task"]
        assert task, "Task not found"
        kvPairs = task["keyValues"]
        assert kvPairs, "Task has no kvpairs"
        assert len(kvPairs) is not 0
        for kvp in kvPairs:
            if (kvp["key"] == "pgSnapId"):
                return kvp["val"]["stringVal"]

        assert False, "No pgSnapId found"

    def check_pg_snap_consistency(self, pgSnapId, consistency, vm):
        output = self.dva.cli([
                        "vms",
                        "snapshots",
                        "show",
                        "--protection-group-snapshot-id", pgSnapId,
                        "--output-format", "json"])
        summary = json.loads(output)["summary"]
        assert summary, "Summary not found"

        # for each vm check consistency
        vmSnapId = ""
        testPass = True
        for s in summary:
            if consistency:
                if consistency is not None and consistency == "CRASH":
                    errstr = "Expecting app consistent snapshot, but it is crash consistent"
                    self.logger.error(errstr)
                    testPass = False
            else:
                if consistency is not None and consistency == "APP":
                    errstr = "Expecting crash consistent snapshot, but it is app consistent"
                    self.logger.error(errstr)
                    testPass = False
            vmSnapId = s["identifier"]

        if not testPass:
            self.collect_agent_logs(vm)

        self.trace_started = False
        self.vsstrace_started = False

        assert testPass, errstr

        return vmSnapId

    def check_pg_snap_with_mulitiple_vm_snap_consistency(self, pgSnapId, VSS_vm):
        output = self.dva.cli([
                        "vms",
                        "snapshots",
                        "show",
                        "--protection-group-snapshot-id", pgSnapId,
                        "--output-format", "json"])
        summary = json.loads(output)["summary"]
        assert summary, "Summary not found"
        # for each vm check consistency
        vmSnapId = ""
        testPass = True
        appSnapCount = 0
        crashSnapCount= 0
        for s in summary:
            if self.vcobj.vm(s["vmName"]) in VSS_vm and s["consistency"] == "CRASH":
                errstr = "Expecting app consistent snapshot, but it is crash consistent"
                self.logger.info(errstr)
                testPass = False
                if not testPass:
                    self.collect_agent_logs(self.vcobj.vm(s["vmName"]))
                assert testPass,errstr
            if self.vcobj.vm(s["vmName"]) not in VSS_vm and s["consistency"] == "APP":
                errstr = "Expecting crash consistent snapshot, but it is app consistent"
                self.logger.info(errstr)
                testPass = False
                if not testPass:
                    self.collect_agent_logs(self.vcobj.vm(s["vmName"]))
                assert testPass,errstr
            if s["consistency"] == "CRASH":
                crashSnapCount +=1
            if s["consistency"] == "APP":
                appSnapCount +=1
        self.logger.info("appSnapCount=%d " % appSnapCount)
        self.logger.info("crashSnapCount=%d " % crashSnapCount)
        self.logger.info("totalSnap=%d " % len(summary))
        self.trace_started = False
        self.vsstrace_started = False
        return len(summary)

    def restoreVmSnap(self, vmSnapId, vm_summary):
        '''
        Given SnapId and vmId , restore a vm snap.
        It verify's that vmx path returned from the restore task
        is same as vmx path of the original vm.
        '''
        output = self.dva.cli([
                            "vms",
                            "restore",
                            "--snapshot-id", vmSnapId,
                            "--force",
                            "--output-format", "json",
                            vm_summary["vmId"]],
                            load_json=True)
        task = output["task"]
        assert task, "Task not found"
        assert task["state"] == "SUCCESS", "Clone task failed"
        keyValues = task["keyValues"]
        assert keyValues, "KeyValues not found"
        for kv in keyValues:
            if kv["key"] == 'vmxPath':
                assert vm_summary['path'] == kv["val"]["stringVal"][1:], "Vmx path didnt match"

    def restorePgSnap(self, pgId, pgSnapId):
        '''
        Restore PG snap.
        Unfortunately there is nothing to verify against.
        '''
        output = self.dva.cli([
                            "protection groups",
                            "restore",
                            "--force",
                            "--snapshot-id", pgSnapId,
                            "--output-format", "json",
                            pgId],
                            load_json=True)
        task = output["task"]
        assert task, "Task not found"
        assert task["state"] == "SUCCESS", "Clone task failed"

    def cloneVmSnap(self, vmSnapId, cloneName):
        output = self.dva.cli([
                           "vms",
                           "snapshots",
                           "clone", vmSnapId,
                           "--new-name", cloneName,
                           "--output-format", "json"])

        task = json.loads(output)["task"]
        assert task, "Task not found"
        assert task["state"] == "SUCCESS", "Clone task failed"
        keyValues = task["keyValues"]
        assert keyValues, "KeyValues not found"
        for kv in keyValues:
            if kv["key"] == 'vmxPath':
                return kv["val"]["stringVal"]

    def wait_for_agent(self, vmName, maxTime):
        # Wait for guest agent to come up for successful app consistent snap
        fe = self.dva.frontends[0]
        guestAgentDown = True
        curWaitTime = 0
        while guestAgentDown is True and curWaitTime < maxTime:
            guestInfo = fe.check_output('/opt/datrium/bin/dacli vms show --output-format=json')
            vms = json.loads(guestInfo)["vms"]
            # Make sure that ip returned by vms show is dhcp assigned. Sometime
            # propcollector returns stale value.
            if len(vms) >= 1:
                for vm_ in vms:
                    if vmName in vm_["vmxpath"] and ipprefix in vm_["ip"]:
                        guestAgentDown = False
                        continue
            time.sleep(5)
            curWaitTime += 5

        assert guestAgentDown  is False, "Guest agent didnt came up in %d seconds" % (maxTime)

    @testtypes.stress_disable()
    @testtypes.suites('vss-provider-test')
    def test_pg_snap(self):
        '''
        Test PG app consistent snap for Windows VM also check agent too old event along with
        Steps:
        1. Prepare VM.
        2. Create PG and add newly created VM to PG.
        3. Set ConfGuestAgent.minAgentVersionReq to 1.30.
        4. Take PG Snapshot.
        5. Verify SnapStoreProtGrpGuestAgentOldEvent event occured.
        6. Restore VM from PG snapshot.
        7. Restore PG snap as whole.
        '''
        self.collect_ga_logs = True
        vm, vm_summary = self.prepare_vm()
        pgId = self.create_pg()
        assert pgId

        self.add_vm_to_pg(pgId, vm_summary['path'])

        self.start_test('C26374')
        # setting min required agent version to 1.30
        from_time = self.dva.controllers[0].time()
        self.dva.setconf('ConfGuestAgent.minAgentVersionReq=65566')
        pgSnapId = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId

        # check pg snap consistnecy
        vmSnapId = self.check_pg_snap_consistency(pgSnapId, True, vm)
        assert vmSnapId
        self.dva.wait_for_event('SnapStoreProtGrpGuestAgentOldEvent', fromTime=from_time);
        self.start_test('C26374')
        for event in self.dva.events():
            self.logger.info(event['eventType'])

        self.delete_vm(vm)

        self.restoreVmSnap(vmSnapId, vm_summary)
        vm = self.vcobj.register_vm("Datastore1", vm_summary['path'], vm_summary['name'])
        self.poweron_vm(vm)
        self.delete_vm(vm)
        self.restorePgSnap(pgId, pgSnapId)
        vm = self.vcobj.register_vm("Datastore1", vm_summary['path'], vm_summary['name'])
        self.poweron_vm(vm)

    @testtypes.stress_disable()
    @testtypes.suites('vss-provider-test')
    def test_cycle_clone_test(self):
        '''
        Tests app consistent snapshot.

        1. Deploys a VM.
        2. Installs guest agent.
        3. Create PG
        4. Add VM to PG
        5. Take PG snapshot.
        6. Clone VM from PG snapshot.
        7. Take PG Snapshot.
        8. Repeat 4-7 after disabling clone uuid override for writable clone test.
        '''
        self.start_test('C34090')
        self.collect_ga_logs = True
        vm, vm_summary = self.prepare_vm()

        # create PG
        curVm = vm_summary["path"]
        prevVm = None

        for i in range(1, 5):
            pgId = self.create_pg()
            assert pgId

            if i == 2:
                # allow uuid to be modified during clone
                self.dva.setconf('ConfVmAnalysis.disableCloneUuidOverride=true')
            self.add_vm_to_pg(pgId, curVm)

            # take pg snap
            pgSnapId = self.take_pg_snapshot(pgId, vm)
            assert pgSnapId

            # check pg snap consistnecy
            vmSnapId = self.check_pg_snap_consistency(pgSnapId, True, vm)
            assert vmSnapId

            self.poweroff_vm(vm)

            vmName = "clone-vm%d" % (i)
            vmClonePath = self.cloneVmSnap(vmSnapId, vmName)
            vm =  self.vcobj.register_vm("Datastore1", vmClonePath, vmName)
            self.poweron_vm(vm)
            self.wait_for_agent(vmName, 300)

            prevVm = curVm
            curVm = vmClonePath
        self.post_test_pass('C34090')

    def get_last_log_backup(self, vm, db_count):
        dest_dir = "/cygdrive/c/"
        try:
            self.upload_file(self.get_guest_ip(vm),\
                             os.path.join(os.path.dirname(__file__), "get_last_log_backup_time.py"))
            output = self.call_win_cmd_output(self.get_guest_ip(vm),\
                                              "cd %s; python get_last_log_backup_time.py -n %s" %(self.dest_dir,db_count ))
            return output

        except Exception as e:
            self.logger.debug('Failed to get backup log of databases %s' % e)
            raise



    def call_win_cmd(self, vm, cmd, retry=True):
        for i in range(1, 6):
            try:
                ssh.check_call(self.get_guest_ip(vm),\
                               cmd,\
                               username='Administrator',\
                               password='sha1c0w')
                break
            except Exception as e:
                self.logger.debug('Unexpected Exception occured %s while executing cmd %s' % (e, cmd))
                if not retry or i == 5:
                    raise

    def change_service_creds(self, vm, obj='\".\\Administrator\"', obj_password='\"sha1c0w\"'):
        self.call_win_cmd(vm,
                          "sc config DatriumGuestSnapshot obj=%s password=%s"
                          % (obj, obj_password))
        self.call_win_cmd(vm, "net stop DatriumGuestSnapshot")
        time.sleep(15)
        self.call_win_cmd(vm, "net start DatriumGuestSnapshot")

    def delete_adhoc_snapshots(self):
        pg_cli = ['protection groups',
                  'snapshots',
                  'show',
                  '11111111-1111-1111-1111-111111111111']
        # Take app consistent snap
        output = self.dva.cli(pg_cli, load_json=True, timeout=0)
        for s in output["summary"]:
            pg_del_cli = ['protection groups',
                          'snapshots',
                          'delete',
                          s["identifier"]]
            self.dva.cli(pg_del_cli)

    def run_vswriter_on_guest(self, vm):
        # Install vswriter on Guest allowing one snap failure.
        dest_dir = "/cygdrive/c/home/bin/build/"
        reg_path = "HKLM\\\\Software\\\\Datrium\\\\"
        Writer_Id = "5affb034-969f-4919-8875-88f830d0ef89"

        self.vswriter_started = False

        for i in range(5):
            if self.vswriter_started == True:
                break
            self.call_win_cmd(vm,
                              "cd %s; sh ./vswriter.sh" %
                              (self.dest_dir),
                              False)
            output = self.call_win_cmd_output(self.get_guest_ip(vm), "vssadmin.exe list writers")
            for l in output.splitlines():
                if Writer_Id in l:
                    self.vswriter_started = True
                    break
        # Add entry in the WRITER_WHITE_LIST
        self.call_win_cmd(vm, "reg ADD %s /v WRITER_WHITE_LIST /t REG_MULTI_SZ /D {%s}" % (reg_path, Writer_Id), False)
        self.logger.info("Successfully added vswriter to WRITER_WHITE_LIST")

    def remove_vswriter_on_guest(self, vm):
        reg_path = "HKLM\\\\Software\\\\Datrium\\\\"
        try:
            self.call_win_cmd(vm, "kill -9 $(ps aux | grep 'vswriter' | awk '{print $1}')", False)
            self.call_win_cmd(vm, "reg delete %s /v WRITER_WHITE_LIST /f" % reg_path, False)
        except Exception as e:
            self.logger.info("vswriter removal failed with error %s" % e)
            raise
        self.logger.info("Successfully removed vswriter from WRITER_WHITE_LIST")
        self.vswriter_started = False

    def check_sql_log_truncation(self, vm, test_start_time, log_truncation, db_count):
        o = self.get_last_log_backup(vm, db_count)

        # check log_truncation for more than 250db
        if db_count > len(self.db_list):
            for i in range(db_count):
                assert self.multi_db_list[i] in o

        # check log_truncation for special character database
        else:
            for i in range(db_count):
                assert self.db_list[i] in o

        for l in o.splitlines():
            if ',' in l:
                dbname, bkp_time = l.split(',')
                self.logger.info(dbname)
                self.logger.info(bkp_time)
                if db_count > len(self.db_list):
                    assert dbname.strip() in self.multi_db_list
                else:
                    assert dbname.strip() in self.db_list

                if log_truncation:
                    assert test_start_time < datetime.strptime(bkp_time.strip(), "%Y-%m-%d %H:%M:%S")
                else:
                    assert test_start_time > datetime.strptime(bkp_time.strip(), "%Y-%m-%d %H:%M:%S")


    def start_workload_hammerdb(self,vm):
        self.call_win_cmd(vm,
                              "cd /cygdrive/c/HammerDB; ./auto_hammerdb.sh")
        self.call_win_cmd(vm,
                              "cd /cygdrive/c/HammerDB; python hammer_db_workload.py")

    def check_data_consistent(self,vm):
        self.call_win_cmd(vm,
                              "cd /cygdrive/c/HammerDB; python get_hammer_db_data.py")
        out = self.call_win_cmd_output(self.get_guest_ip(vm),"cd /cygdrive/c/HammerDB; md5sum out.csv")
        return out


    def sql_log_truncation(self, test_type):
        '''
        Test for event/notification in case of log truncation failure.
        Since service credentials by default is LocalSystem with no backup priveleges,
        expect log truncation to fail.

        1. Deploys a VM.
        2. Installs guest agent.
        3. Triggers adhoc app consistent snapshot with log truncation option.
        4. Check for event SnapStoreVMACSnapLogTruncationErrorWarningEvent.
        '''
        self.start_test('C41839')
        self.collect_ga_logs = True
        self.test_upgrade = True
        vm, vm_summary = self.prepare_vm(test_type)

        self.wait_for_agent(vm_summary["name"], 300)
        self.logger.info("Trigger log truncation with service creds LocalSystem.")

        from_time = self.dva.controllers[0].time()
        # Take log truncation snap
        self.adhoc_snap(vm, vm_summary, True, False)

        self.dva.wait_for_event('SnapStoreVMACSnapLogTruncationErrorWarningEvent', fromTime=from_time)
        self.post_test_pass('C41839')

        '''Database names with special characters
        1.Create few DBs with DB names containing special characters('-', '@', '#', '_', '(', ')', '+' )
        2.Create few DBs with DB names containing mix of special characters.
        3.Generate some data on the DBs to increase the log size.
        4.Take snapshot of VM with log truncation option.
        '''
        self.start_test('C71549')
        # create new databases and generate log inside that table
        self.create_database(vm)
        self.check_database_created(vm)

        test_start_time = datetime.now()
        self.change_service_creds(vm)

        self.delete_adhoc_snapshots()

        self.logger.info("App ready for log truncation with new databases.")

        # Take snap
        self.adhoc_snap(vm, vm_summary, True, False)
        self.check_sql_log_truncation(vm, test_start_time, True, len(self.db_list))
        self.post_test_pass('C71549')

        '''Create few DBs with DB property snapshot_isolation set as TRUE (default value being FALSE).
        Generate some data on the DBs to increase the log size.
        Take snapshot of VM with log truncation option.
        '''
        self.start_test('C71553')
        # change db property with snapshot isolation true
        self.make_snapshot_isolation_true(vm)
        self.check_db_with_snapshotisolation_true(vm)

        test_start_time = datetime.now()
        self.change_service_creds(vm)

        self.delete_adhoc_snapshots()

        self.logger.info("App ready for log truncation with snapshot_isolated databases.")

        # Take snap
        self.adhoc_snap(vm, vm_summary, True, False)

        self.check_sql_log_truncation(vm, test_start_time, True, len(self.db_list))
        self.post_test_pass('C71553')

        '''Tests app consistent snapshot with log truncation.

        1. Change svc credentials to administrator
        2. Triggers adhoc app consistent snapshot with log truncation option.
        3. Verifies that snapshot consistency is "APP"
        4. Verify that there is entry in [msdb] dbo.backupset table for database with start time after test started.
        '''
        self.start_test('C41837')

        test_start_time = datetime.now()
        self.change_service_creds(vm)

        self.delete_adhoc_snapshots()

        self.logger.info("App ready for log truncation.")

        # Take snap
        time.sleep(10)
        self.adhoc_snap(vm, vm_summary, True, False)

        self.check_sql_log_truncation(vm, test_start_time, True,len(self.db_list) )
        self.post_test_pass('C41837')

        '''
        Tests no log truncation happens in SQL server, if APP consistent snapshot fails.

        1. Copy and run vswriter and add registry entry.
        2. Trigger adhoc app consistent snapshot with log truncatoin option.
        3. Verify that snapshot creation is successful but, consistency is not "APP"
        4. Verify that there is entry in [msdb] dbo.backupset table for database with start time after test started.
        5. Verify that log truncation has not happened.
        6. Remove vswriter and clear the registry entry.
        '''
        self.start_test('C41841')
        test_start_time = datetime.now()
        self.delete_adhoc_snapshots()
        # Copy and run vswriter. Then add entry in guest registry.
        # Currently it is set for only one failure
        self.run_vswriter_on_guest(vm)
        from_time = self.dva.controllers[0].time()
        self.logger.info("Test no log truncation, if APP consistent snapshot fails in SQL.")
        self.adhoc_snap(vm, vm_summary, False, False)
        # Check for failure of APP snapshot.
        self.dva.wait_for_event('SnapStoreProtGrpTakeSnapSuccessEvent', fromTime=from_time)
        self.dva.wait_for_event('SnapStoreVMACSnapQuiesceErrorInfoEvent', fromTime=from_time)
        # Check that no log truncation happened.

        self.check_sql_log_truncation(vm, test_start_time, False, len(self.db_list))
        self.logger.info('Log not truncated on SQL server when APP snap fails')
        #Remove the vswriter from the guest
        self.remove_vswriter_on_guest(vm)
        self.post_test_pass('C41841')

        '''
        Adding VM with log truncation option in PG

        1. Create a PG named PG_log_truncation.
        2. Add this VM with the log truncation option.
        3. Take a PG snapshot and verify log truncation for the VM.
        '''
        self.start_test('C41838')
        self.logger.info("Adding VM to PG with log truncation.")
        test_start_time = datetime.now()
        pgId = self.create_pg()
        assert pgId
        self.add_vm_to_pg(pgId, vm_summary['path'], True)

        # take pg snap
        pgSnapId = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId

        # check pg snap consistnecy
        vmSnapId = self.check_pg_snap_consistency(pgSnapId, True, vm)
        assert vmSnapId


        self.check_sql_log_truncation(vm, test_start_time, True, len(self.db_list))

        self.post_test_pass('C41838')

        '''
        Restore VM from snapshot with/without log truncation

        Take log truncation snapshot
        Take another log truncation snapshot, say "after-log-truncation-snapshot"
        Now power-off the VM and restore to "log-truncation-snap"
        Power on VM and check the log status.
        Now power-off the VM and restore to "after-log-truncation-snap"
        Power on VM and check the log status.
        '''
        self.start_test('C41842')
        self.logger.info("Restore VM from log truncation snapshot.")
        test_start_time = datetime.now()

        # take first pg snap
        self.wait_for_agent(vm_summary["name"], 600)
        pgSnapId_1 = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId_1

        # check pg snap consistnecy
        vmSnapId_1 = self.check_pg_snap_consistency(pgSnapId_1, True, vm)
        assert vmSnapId_1

         # take second pg snap
        self.wait_for_agent(vm_summary["name"], 600)
        pgSnapId_2 = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId_2

        # check pg snap consistnecy
        vmSnapId_2 = self.check_pg_snap_consistency(pgSnapId_2, True, vm)
        assert vmSnapId_2

        self.delete_vm(vm)

        # Restore to vmSnapId_1, which doesn't have latest log truncation
        self.restoreVmSnap(vmSnapId_1, vm_summary)
        vm = self.vcobj.register_vm("Datastore1", vm_summary['path'], vm_summary['name'])
        self.poweron_vm(vm)

        self.logger.info("Check for no log truncated in first snapshot")

        self.check_sql_log_truncation(vm, test_start_time, False, len(self.db_list))

        self.delete_vm(vm)

        # Restore to vmSnapId_2, which has log truncation due to vmSnapId_1
        self.restoreVmSnap(vmSnapId_2, vm_summary)

        vm = self.vcobj.register_vm("Datastore1", vm_summary['path'], vm_summary['name'])
        self.poweron_vm(vm)
        self.logger.info("Check for log truncated in second snapshot")

        self.check_sql_log_truncation(vm, test_start_time, True, len(self.db_list))
        self.post_test_pass('C41842')

        '''Create around 300 databases.
        Take VSS snapshot with/without log truncation.
        Check if the BCD size has grown above 5MB.'''

        self.start_test('C85955')
        # create new databases and generate log inside that table
        self.create_multi_database(vm)
        self.check_database_created(vm)

        test_start_time = datetime.now()
        self.change_service_creds(vm)

        self.delete_adhoc_snapshots()

        self.logger.info("App ready for log truncation with new databases.")

        # Take snap
        self.adhoc_snap(vm, vm_summary, True, False)
        db_count = self.db_count_for_log_truncation(vm)
        self.check_sql_log_truncation(vm, test_start_time, True, db_count)
        self.post_test_pass('C85955')


        '''Start SQL Workload
        Create App-Consistent PG to back up MSSQL
        Shutdown down original MSSQL VM
        Clone VM from this PG
        Check Data is consistent
        Repeat 3-5'''
        self.start_test('C12237')
        self.logger.info("Adding VM to PG with log truncation.")
        test_start_time = datetime.now()
        # Start SQL Workload
        self.start_workload_hammerdb(vm)
        pgId = self.create_pg()
        assert pgId
        self.add_vm_to_pg(pgId, vm_summary['path'], True)

        # take pg snap
        pgSnapId = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId
        out1 = self.check_data_consistent(vm)


        # check pg snap consistnecy
        vmSnapId = self.check_pg_snap_consistency(pgSnapId, True, vm)
        assert vmSnapId

        self.poweroff_vm(vm)

        vmName = "hammerdb_clone"
        vmClonePath = self.cloneVmSnap(vmSnapId, vmName)
        vm =  self.vcobj.register_vm("Datastore1", vmClonePath, vmName)

        self.poweron_vm(vm)
        out2 = self.check_data_consistent(vm)

        assert out1 == out2
        self.logger.info("data is consistent")
        self.wait_for_agent(vmName, 300)
        self.post_test_pass('C12237')

        self.delete_adhoc_snapshots()
        self.delete_pg(pgId)
        self.delete_vm(vm)

    @testtypes.stress_disable()
    @testtypes.suites('vss-provider-test')
    def test_sql_log_truncation(self):
        self.start_test('C71981')
        self.sql_log_truncation('sql')
        self.post_test_pass('C71981')

        self.start_test('C71982')
        self.sql_log_truncation('win2016-sql-2016')
        self.post_test_pass('C71982')

        self.start_test('C71983')
        self.sql_log_truncation('win2016-sql-2017')
        self.post_test_pass('C71983')

        self.start_test('C71984')
        self.sql_log_truncation('win2019-sql-2016')
        self.post_test_pass('C71984')

    def get_database_path(self,vm):
            """gets all specific database directories under given path as list"""
            dest_dir = "/cygdrive/c/home/bin/build/"
            try:
                output = ssh.check_output(self.get_guest_ip(vm),
                                "cd %s; python get_Mailbox_directories.py" % (dest_dir),
                                username='Administrator',
                                password='sha1c0w')
            except (ssh.SSHException, ssh.HostConnectError) as e:
                self.logger.debug('Exception raised while getting database path,  %s' % e)
            except Exception as e:
                self.logger.debug('Unexpected Exception raised while getting database path, %s' % e)
                raise
            return output.split(',')

    def get_eseutil_cmd(self, vm):
        """fetches 3 letter pattern for eseutil command like E00, E01, etc in order to list all files having such pattern in the directory"""
        databases_name = self.get_database_path(vm)
        self.logger.info("databases are:",databases_name)
        eseutil_cmd_list=[]
        #enter into this database, and fetch any file starting with E and get its next two digits like E00 or E00.
        db_path="C:\Program Files\Microsoft\Exchange Server\V15\Mailbox\{}"
        db_full_path=db_path.format(databases_name[0])
        self.logger.info("full path",db_full_path)
        dest_dir = "/cygdrive/c/home/bin/build/"
        try:
            output = ssh.check_output(self.get_guest_ip(vm),
                            "cd %s; python get_eseutil_command.py '%s'" % (dest_dir, db_full_path),
                            username='Administrator',
                            password='sha1c0w')
        except (ssh.SSHException, ssh.HostConnectError) as e:
            self.logger.debug('Exception raised while getting fetching 3 letter(like E00) pattern for eseutil command, %s' % e)
        except Exception as e:
            self.logger.debug('Unexpected Exception raised while getting fetching 3 letter(like E00) pattern for eseutil command, %s' % e)
            raise
        self.logger.info("output is: ",output)
        return output

    def get_first_log_file(self, vm):
        """gets the first log file among the list of log files in the mailbox directory"""
        op = []
        db_names_list=self.get_database_path(vm)
        self.logger.info("required mailbox database names are:",db_names_list)
        eseutil_cmds=self.get_eseutil_cmd(vm)
        db_path = os.path.join("/cygdrive/c/Program Files/Microsoft/Exchange Server/V15/Mailbox/",db_names_list[0]) #fetches first mailbox database name
        cmd_join = 'cd {}; '.format("'"+db_path+"'")
        multiple_cmd = cmd_join + eseutil_cmds
        try:
            op = ssh.check_output(self.get_guest_ip(vm),
                                 "%s" %multiple_cmd,
                                 username='Administrator',
                                 password='sha1c0w')
        except (ssh.SSHException, ssh.HostConnectError) as e:
            self.logger.debug('Exception raised while getting first log file, %s' % e)
        except subprocess.CalledProcessError as e:
            op = e.output
            for l in op.splitlines():
                if 'Log file:' in l:
                    self.logger.info('First log file =>' + l)
                    return l
            assert False, "No log file found"
        except Exception as e:
            self.logger.debug('Unexpected Exception raised while getting first log file, %s' % e)
            raise
        else: #usefull to fetch first log file when no exception is raised.
            for l in op.splitlines():
                if 'Log file:' in l:
                    self.logger.info('First log file =>' + l)
                    return l
            assert False, "No log file found"

    def build_logs(self, vm, account_id):
        #builds log files for truncation
        dest_dir = "/cygdrive/c/home/bin/build/"
        try:
            output = ssh.check_output(self.get_guest_ip(vm),
                            "cd %s; python generate_mail_logs.py %s" % (dest_dir, account_id.strip("'")),
                            username='Administrator',
                            password='sha1c0w')
        except (ssh.SSHException, ssh.HostConnectError) as e:
            self.logger.debug('Exception raised while generating logs, %s' % e)
        except Exception as e:
            self.logger.debug('Unexpected Exception raised while generating logs, %s' % e)
            raise

    def exch_log_truncation(self, test_type):
        '''
        Tests app consistent snapshot.

        1. Deploys a VM.
        2. Installs guest agent.
        4. None first log file before snapshot.
        5. Triggers adhoc app consistent snapshot with log truncatoin option.
        6. Verifies that first log file after snapshot and not same as before.
        '''
        self.start_test('C41837')
        self.collect_ga_logs = True
        self.test_upgrade = True
        #'account_id' are login credentials for exchange.
        account_password = 'sha1c0w' #same for all combinations
        if test_type == 'win2012R2-exch2013':
            account_id = 'Administrator@win2012-vss.com'
        elif test_type == 'win2016-exch2016-cu14' or test_type == 'win2019-exch2019':
            account_id = 'Administrator@exchange.com'
        else:
            assert False, "Invalid test_type parameter"
        vm, vm_summary = self.prepare_vm(test_type)
        self.wait_for_agent(vm_summary["name"], 300)
        self.delete_adhoc_snapshots()
        self.logger.info("App ready for log truncation.")
        pre_snap_log = self.get_first_log_file(vm)
        # Take snap
        self.adhoc_snap(vm, vm_summary, True, False)
        post_snap_log = self.get_first_log_file(vm)
        self.logger.info('Pre_snap(%s) , Post_snap(%s)' % (pre_snap_log, post_snap_log))
        assert pre_snap_log != post_snap_log, "error while executing %s combination" %test_type
        self.post_test_pass('C41837')
        # build logs for truncation
        self.build_logs(vm, account_id)
        time.sleep(20)
        '''
        Adding VM with log truncation option in PG

        1. Create a PG named PG_log_truncation.
        2. Add this VM with the log truncation option.
        3. Take a PG snapshot and verify log truncation for the VM.
        '''
        self.start_test('C41838')
        self.logger.info("Adding VM to PG with log truncation.")
        test_start_time = datetime.now()
        pgId = self.create_pg()
        assert pgId, "error while executing %s combination" %test_type
        self.add_vm_to_pg(pgId, vm_summary['path'], True)
        # get the first log file before log truncation
        pre_snap_log = self.get_first_log_file(vm)
        # take pg snap
        pgSnapId = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId, "error while executing %s combination" %test_type

        # check pg snap consistnecy
        vmSnapId = self.check_pg_snap_consistency(pgSnapId, True, vm)
        assert vmSnapId, "error while executing %s combination" %test_type
        # get the first log file after log truncation
        post_snap_log = self.get_first_log_file(vm)
        self.logger.info('Pre_snap(%s) , Post_snap(%s)' % (pre_snap_log, post_snap_log))
        # verify log truncation
        assert pre_snap_log != post_snap_log, "error while executing %s combination" %test_type
        self.post_test_pass('C41838')
        # build logs for truncation
        self.build_logs(vm, account_id)
        time.sleep(20)
        '''
        Restore VM from snapshot with/without log truncation

        Take log truncation snapshot
        Take another log truncation snapshot, say "after-log-truncation-snapshot"
        Now power-off the VM and restore to "log-truncation-snap"
        Power on VM and check the log status.
        Now power-off the VM and restore to "after-log-truncation-snap"
        Power on VM and check the log status.
        '''
        self.start_test('C41842')
        self.logger.info("Restore VM from log truncation snapshot.")
        # get the first log file before first PG snapshot
        pre_snap_log_first = self.get_first_log_file(vm)
        # take first pg snap
        self.wait_for_agent(vm_summary["name"], 600)
        pgSnapId_1 = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId_1, "error while executing %s combination" %test_type

        # check pg snap consistnecy
        vmSnapId_1 = self.check_pg_snap_consistency(pgSnapId_1, True, vm)
        assert vmSnapId_1, "error while executing %s combination" %test_type

        # take second pg snap
        self.wait_for_agent(vm_summary["name"], 600)
        pgSnapId_2 = self.take_pg_snapshot(pgId, vm)
        assert pgSnapId_2, "error while executing %s combination" %test_type

        # check pg snap consistnecy
        vmSnapId_2 = self.check_pg_snap_consistency(pgSnapId_2, True, vm)
        assert vmSnapId_2, "error while executing %s combination" %test_type

        self.delete_vm(vm);

        # Restore to vmSnapId_1, which doesn't have latest log truncation
        self.restoreVmSnap(vmSnapId_1, vm_summary)
        vm = self.vcobj.register_vm("Datastore1", vm_summary['path'], vm_summary['name'])
        self.poweron_vm(vm)
        #get first log file after reverting to first PG snapshot
        post_snap_log_first = self.get_first_log_file(vm)
        self.logger.info("Check for no log truncated in first snapshot")
        self.logger.info('pre_snap_log_first(%s) , post_snap_log_first(%s)' % (pre_snap_log_first, post_snap_log_first))
        assert pre_snap_log_first == post_snap_log_first, "error while executing %s combination" %test_type

        self.delete_vm(vm)

        # Restore to vmSnapId_2, which has log truncation due to vmSnapId_1
        self.restoreVmSnap(vmSnapId_2, vm_summary)
        vm = self.vcobj.register_vm("Datastore1", vm_summary['path'], vm_summary['name'])
        self.poweron_vm(vm)

        # get the first log file after restore to second PG snapshot
        post_snap_log_second = self.get_first_log_file(vm)
        self.logger.info("Check for log truncated in second snapshot")
        # verify log truncation
        self.logger.info('pre_snap_log_first(%s) , post_snap_log_second(%s)' % (pre_snap_log_first, post_snap_log_second))
        assert pre_snap_log_first != post_snap_log_second, "error while executing %s combination" %test_type

        self.post_test_pass('C41842')
        '''
        Tests no log truncation happens in Exch server, if APP consistent snapshot fails.

        1. Copy and run vswriter and add registry entry.
        2. Trigger adhoc app consistent snapshot with log truncatoin option.
        3. Verify that snapshot creation is successful but, consistency is not "APP"
        4. Verify that log truncation has not happened.
        5. Remove vswriter and clear the registry entry.
        '''
        self.start_test('C41841')
        test_start_time = datetime.now()
        self.delete_adhoc_snapshots()
        from_time = self.dva.controllers[0].time()
        self.logger.info("Test no log truncation, if APP consistent snapshot fails in Exch.")
        # Copy and run vswriter. Then add entry in guest registry.
        # Currently it is set for only one failure
        self.run_vswriter_on_guest(vm)
        pre_snap_log = self.get_first_log_file(vm)
        self.adhoc_snap(vm, vm_summary, False, False)
        # Check for failure of APP snapshot.
        self.dva.wait_for_event('SnapStoreProtGrpTakeSnapSuccessEvent', fromTime=from_time)
        self.dva.wait_for_event('SnapStoreVMACSnapQuiesceErrorInfoEvent', fromTime=from_time)
        # Check that no log truncation happened.
        post_snap_log = self.get_first_log_file(vm)
        self.logger.info('Pre_snap(%s) , Post_snap(%s)' % (pre_snap_log, post_snap_log))
        assert pre_snap_log == post_snap_log, "error while executing %s combination" %test_type
        self.logger.info('Log not truncated on exchange server when APP snap fails')
        # Remove the vswriter from the guest
        self.remove_vswriter_on_guest(vm)
        self.post_test_pass('C41841')
        self.delete_adhoc_snapshots()
        self.delete_pg(pgId)
        self.delete_vm(vm)

    @testtypes.stress_disable()
    @testtypes.suites('vss-provider-test')
    def test_exch_log_truncation(self):
        ''' testrunner default timeout is 4 hours, in this time we can only execute 2 windows-exchange flavours
                1) windows 2016 and exchange 2016
                2) windows 2012R2 and exchange 2013
        '''
        # for windows 2016 and exchange 2016
        self.start_test('C71986')
        self.logger.info("Testing for win2016-exch2016")
        self.exch_log_truncation('win2016-exch2016-cu14')
        self.logger.info("Testing completed for win2016-exch2016")
        self.post_test_pass('C71986')
        # for windows 2012R2 and exchange 2013
        self.start_test('C71985')
        self.logger.info("Testing for win2012R2-exch2013")
        self.exch_log_truncation('win2012R2-exch2013')
        self.logger.info("Testing completed for win2012R2-exch2013")
        self.post_test_pass('C71985')

    @testtypes.stress_disable()
    @testtypes.suites('vss-provider-test')
    def test_pg_snap_with_vms(self):
        '''
        Test PG app consistent snapshot for Windows VMs with
        Steps:
        1. Prepare VMs of VSS enabled and VSS agent installed.
        2. Create PG and add vms in PG.
        3. Take PG Snapshot.
        4. Verify successful app-consistent snaps for all vms.
        '''
        self.collect_ga_logs = True
        self.start_test('C12248')
        # create PG
        pgId1 = self.create_pg("PG_All_VSS_Enabled")
        assert pgId1
        VSS_vms = {}
        for i in range(4):
            vm, vm_summary = self.prepare_vm('win2016-sql-2016')
            VSS_vms[vm] = vm_summary
            # adding  vms with VSS in pg
            self.add_vm_to_pg(pgId1, vm_summary['path'])
        VSS_vm_pg = VSS_vms.keys()
        for i in range(2):
            for key, vm_summary in VSS_vms.items():
                self.wait_for_agent(vm_summary["name"], 600)
            # take pg snap
            pgSnapId = self.take_pg_snapshot(pgId1, VSS_vm_pg)
            assert pgSnapId
            # check pg_snap consistnecy
            totalSnap = self.check_pg_snap_with_mulitiple_vm_snap_consistency(pgSnapId, VSS_vm_pg)
            assert totalSnap == 4, "totalSnap is less than vms in pg"
        self.post_test_pass('C12248')
        '''
        Test PG snapshot for Windows VMs with
        Steps:
        1. Prepare VMs of VSS enabled with VSS agent installed/not and VSS disable.
        2. Create PG and add vms in PG.
        3. Take PG Snapshot.
        4. Verify count should be correct, for crash consistent and app consistent vm.
            (VMs w/out vss agent installed but selected for app-consistent snap; crash consistent snapshot should have been performed).
        '''

        self.start_test('C12249')
        VSS_no_agent_vms = {}
        noVSS_vms = {}
        # create PG
        pgId2 = self.create_pg("PG_Mixed_VSS_Enabled")
        assert pgId2
        for i in range(2):
            # Prepare VMs of VSS enabled without vss agent installed
            vm, vm_summary = self.prepare_vm("no_Datrium_VSS_agent", False , False)
            VSS_no_agent_vms[vm] = vm_summary
            # adding  vms with VSS enabled without datrium vss agent in pg
            self.add_vm_to_pg(pgId2, vm_summary['path'], False, False)
        for i in range(2):
            # Prepare VMs of VSS disable
            vm, vm_summary = self.prepare_vm("no_VSS", True , False)
            noVSS_vms[vm] = vm_summary
            # adding vms with VSS Disable in pg
            self.add_vm_to_pg(pgId2, vm_summary['path'], False, False)
        for key, vm_summary in VSS_vms.items():
            # adding vms with VSS in pg
            self.add_vm_to_pg(pgId2, vm_summary['path'])
        for i in range(2):
            for key, vm_summary in VSS_vms.items():
                self.wait_for_agent(vm_summary["name"], 600)
            # take pg snap
            pgSnapId = self.take_pg_snapshot(pgId2, VSS_vm_pg)
            assert pgSnapId
            # check pg_snap consistnecy
            totalSnap = self.check_pg_snap_with_mulitiple_vm_snap_consistency(pgSnapId, VSS_vm_pg)
            assert totalSnap == 8, "totalSnap is less than vms in pg"
        self.post_test_pass('C12249')

        '''
        Test PG app consistent snap for Windows VM  with
        Steps:
        1. Prepare VMs of VSS enabled with VSS agent installed and VSS disable.
        2. Create two PG and Put some of the same VSS vms in both PGs.
        3. Take PGs Snapshot.
        4. Verify count should be correct, for crash consistent and app consistent vm.
        '''
        self.start_test('C12250')
        # We can use above two PG with same VSS vms in both PGs
        for i in range(2):
            for key, vm_summary in VSS_vms.items():
                self.wait_for_agent(vm_summary["name"], 600)
            # take pg1 snap
            pg1SnapId = self.take_pg_snapshot(pgId1, VSS_vm_pg)
            assert pg1SnapId
            # check pg1_snap consistnecy
            totalSnap = self.check_pg_snap_with_mulitiple_vm_snap_consistency(pg1SnapId, VSS_vm_pg)
            assert totalSnap == 4, "totalSnap is less than vms in pg"
            for key, vm_summary in VSS_vms.items():
                self.wait_for_agent(vm_summary["name"], 600)
            # take pg2 snap
            pg2SnapId = self.take_pg_snapshot(pgId2, VSS_vm_pg)
            assert pg2SnapId
            # check pg2_snap consistnecy
            totalSnap = self.check_pg_snap_with_mulitiple_vm_snap_consistency(pg2SnapId, VSS_vm_pg)
            assert totalSnap == 8, "totalSnap is less than vms in pg"
        self.post_test_pass('C12250')
        self.delete_pg(pgId1)
        self.delete_pg(pgId2)

        '''
        Test PG snapshot for Windows VMs with
        Steps:
        1. Prepare VMs of VSS enabled with VSS agent installed and VSS disable.
        2. Create PG and add vms in PG.
        3. Take PG Snapshot.
        4. Verify mixed type of snapshot created : app/non-app consistent snapshot
           count should be correct, for crash consistent and app consistent vm.
        '''
        self.start_test('C12251')
        # create PG
        pgId = self.create_pg("PG_Mixed_Type_Snapshot_Created")
        assert pgId
        for key, vm_summary in noVSS_vms.items():
            # adding vms with VSS disable in pg
            self.add_vm_to_pg(pgId, vm_summary['path'], False, False)
        for key, vm_summary in VSS_vms.items():
            # adding vms with VSS in pg
            self.add_vm_to_pg(pgId, vm_summary['path'])
        for i in range(2):
            for key, vm_summary in VSS_vms.items():
                self.wait_for_agent(vm_summary["name"], 600)
            # take pg snap
            pgSnapId = self.take_pg_snapshot(pgId, VSS_vm_pg)
            assert pgSnapId
            # check pg_snap consistnecy
            totalSnap = self.check_pg_snap_with_mulitiple_vm_snap_consistency(pgSnapId, VSS_vm_pg)
            assert totalSnap == 6, "totalSnap is less than vms in pg"
        self.post_test_pass('C12251')
        self.delete_pg(pgId)

    @testtypes.suites('vss-provider-test')
    def upgrade_dvx_software(self):
        ''' Upgrade DVX software while creating/restoring snapshot

            Deploy carbon fixed build dittos
            create a windows VSS vm on it
            create a PG, add this APP-consistent enabled vm  to it and initiate the schedules PG snapshot for every 3 minute
            from existing dittos, upgrade to nitrogen fixed build
            let the schedule run in background during dvx upgrade, check its status after dvx upgrade.
        '''
        # deployed fixed carbon build 569 dittos, from which we upgrade to a nitrogen build later.
        self.collect_ga_logs = True
        vm, vm_summary = self.prepare_vm('win2012R2-exch2013')

        # Note the controller1 ip of deployed carbon build
        carbon_mgmt_ip = self.dva.controllers[0].ipaddr
        self.logger.debug('got carbon build controller 1 ip: ', carbon_mgmt_ip)

        # first put the version in upgrade center
        ssh.check_call('upgrade-center-qa.datrium.com', 'python /home/damon/get_image.py -R -b 5.1.x -i 760', username = 'root', password = 'sha1c0w')

        # the software version for this build will be
        nitrogen_dvx_version = '5.1.1.2-38149_dee2561'

        # create a pg
        pgId = self.create_pg()
        assert pgId, "error while creating a PG"

        # add vm to it without need to check for log truncation
        self.add_vm_to_pg(pgId, vm_summary['path'], False)

        #create a pg schedule
        self.dva.cli('protection groups schedules add %s --schedule-name "3 MIN RPO" --schedule "0 */3 * * * ?" --retention 86400' %pgId)
        # check for Scheduled PG status
        self.dva.show_schedule(pgId)

        # enable root login for your dvx
        output = ssh.check_output(carbon_mgmt_ip, 'entersupportmode; dev root enable', username = 'admin', password = 'datrium#1')
        reg_obj=re.search(r'.{8}-.{4}-.{4}-.{4}-.{12}', output)
        if reg_obj:
            self.logger.info("dev mode password is : ", reg_obj.group())
            root_password = str(reg_obj.group())
            self.logger.info("root password is : ",root_password)

        # point your DVX to upgrade center specified and change root account password to generic password 'sha1c0w'
        ssh.check_call(carbon_mgmt_ip,'echo https://upgrade-center-qa.datrium.com:443 > /tmp/upgrade_center_url.override; plat_client.py --platform --enable-root-login --password sha1c0w', username='root', password = root_password)

        # using methods in from 'upgrade_test_lib.py' for dvx upgrade.
        base_time, _, task_id = upgrade_test_lib.start_upgrade(self.dva.controllers[0], False, True,"5.1.1.2-38149_dee2561")
        result, msg = upgrade_test_lib.wait_controller_task(self.dva.controllers[0], task_id, 1600, False)

        assert result == 'Success' and msg == 'DVX system upgraded', ('dvx controller upgrade failed: %s' % msg)

        # check for Scheduled PG status after DVX upgrade
        self.dva.show_schedule(pgId)

    @testtypes.testbeds('HA_dittos')
    @testtypes.no_abort_on_failure()
    @testtypes.suites('vss-provider-test')
    @testtypes.set_testbeds(upgrade_test_lib.emit_testbed(ctr=1, host=1, vc = 1, build='5.0.x'))
    def test_upgradevss(self):
        self.start_test('C12204')
        self.upgrade_dvx_software()
        self.post_test_pass('C12204')