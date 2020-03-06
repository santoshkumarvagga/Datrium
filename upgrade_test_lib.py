##############################################################
# Copyright (c) 2015-2019 Datrium, Inc. All rights reserved. #
#                -- Datrium Confidential --                  #
##############################################################

import json
import logging
import os
import sys
import random
import re
import tarfile
import threading
import time
import copy
import abc
import datetime
from distutils.version import LooseVersion

import yaml

import async
import dalibs.popen as subprocess
import dalibs.retry as retry
import dalibs.ssh as ssh
import nfsperftool
import nplus1_test_lib
import server_plat_test_lib
import software_version_lib
import TestBeds
import upgrade_center_lib

import Helpers.Common.DaExecHelper as DaExecHelper

# FIXME(sachin): move Prod/Test/Helpers/ControllerHelpers/MasterActiveHelper.py here
import Helpers.ControllerHelpers.MasterActiveHelper as MasterActiveHelper
import Helpers.Common.DaTestTempFileDirHelper as DaTestTempFileDirHelper

curr_function_name = lambda: sys._getframe(1).f_code.co_name

g_release_to_version = {
        '5.1.x'   : [],
        '5.0.x'   : ['5.0.1.0-36088_8251a01',
                     '5.0.1.1-36094_d752d95',
                     '5.0.1.2-36100_5322403'],
        '4.1.x'   : ['4.1.1.3-33297_7280abd',
                     '4.1.1.1-33279_c3a37e9',
                     '4.1.1.0-33234_34d8481'],
        '4.0.x'   : ['4.0.4.1-30476_2500990',
                     '4.0.4.0-30471_2f4126b',
                     '4.0.3.2-30467_c0b7048',
                     '4.0.3.1-30463_dec984f',
                     '4.0.3.0-30458_f357e20',
                     '4.0.2.0-30408_8a1e4c6',
                     '4.0.1.1-30335_92da128',
                     '4.0.1.0-30307_cd13893'],
        '3.1.x'   : ['3.1.1.3-27748_fcc1c5c',
                     '3.1.1.2-27737_576932f',
                     '3.1.1.1-27733_9f5b41c',
                     '3.1.1.0-27717_bf0506c'],
}

upgrade_check_points_list = [10, 15, 20, 25, 30, 35, 40, 60, 61, 62, 63, 64, 65, 80, 85, 100]

upgrade_check_point = {
        'UPGRADE_PROGRESS_TASK_STARTING'                 : 0,
        'UPGRADE_PROGRESS_TASK_STARTED'                  : 5,
        'UPGRADE_PROGRESS_CHECK_PASSED'                  : 10,
        'UPGRADE_PROGRESS_IMAGE_DOWNLOADED_LOCALLY'      : 15,
        'UPGRADE_PROGRESS_IMAGE_DEPLOYED'                : 20,
        'UPGRADE_PROGRESS_EXEC_PRE_CLUSTER_UPGRADE'      : 25,
        'UPGRADE_PROGRESS_NONDISRUPT_STARTED'            : 30,
        'UPGRADE_PROGRESS_AGENTS_DOWNLOAD_START'         : 35,
        'UPGRADE_PROGRESS_AGENTS_DOWNLOAD_CONVERGED'     : 40,
        'UPGRADE_PROGRESS_AGENTS_PREPARE_CONVERGED'      : 60,
        'UPGRADE_PROGRESS_AGENTS_READY'                  : 61,
        'UPGRADE_PROGRESS_HOSTS_SWITCHOVER_CALLED'       : 62,
        'UPGRADE_PROGRESS_HOSTS_SWITCHOVER_WAITED'       : 63,
        'UPGRADE_PROGRESS_OTHER_NODES_SWITCHOVER_CALLED' : 64,
        'UPGRADE_PROGRESS_DISRUPTIVE_STARTED'            : 65,
        'UPGRADE_PROGRESS_VCPLUGIN_REREGISTERED'         : 80,
        'UPGRADE_PROGRESS_EXEC_POST_CLUSTER_UPGRADE'     : 85,
        'UPGRADE_PROGRESS_TASK_FINISHED'                 : 100,
    }

def __get_a_version_with_esx67_support(list_of_releases, min_version_with_esx67_support, **kwargs):
    list_of_compatible_versions = []
    for current_version in list_of_releases:
        if (LooseVersion(current_version) >= LooseVersion(min_version_with_esx67_support)):
            list_of_compatible_versions.append(current_version)

    assert len(list_of_compatible_versions) > 0, (
               'Unable to find any compatible version %s %s'
               % (list_of_releases, min_version_with_esx67_support))
    return random.choice(list_of_compatible_versions)


def _release_to_version(target, **kwargs):
    """
    Find out the exact version of a previous released target.

    @param target: release target
    @return: full version string
    """
    version_to_return = None
    latest_release = sorted(g_release_to_version, reverse=True)[0]
    g_release_to_version['release'] = g_release_to_version[latest_release]
    assert target in g_release_to_version, 'Invalid release target %s' % target

    if len(g_release_to_version[target]) > 0:
        version_to_return = random.choice(g_release_to_version[target])
    return version_to_return


def get_patch_releases_from_version(version):
    """
    Get all the available patches from the given version string.

    @param version: version, 4.0.3.0-30458_f357e20
    @return: list of patch releases build top excluding the given version
    """
    assert software_version_lib.is_version_string(version), ('%s is not a valid version' % version)
    major, minor, maintenance, _, _, _, _ = software_version_lib.parse_version_string(version)
    versions = []
    for release in g_release_to_version:
        if '%s.%s.' % (major, minor) in release:
            versions.extend(g_release_to_version[release])
    patches = []
    fixed_build_dir = '/colo/build/workloads/fixed_builds'
    for ver in versions:
        if '%s.%s.%s.' % (major, minor, maintenance) in ver and ver not in version:
            patches.append(os.path.join(fixed_build_dir, ver, 'Prod/Build'))
    return patches


def get_release_buildtop(target):
    """
    Get the build top directory of a previous released target.

    @param target: release target
    @return: build top directory
    """
    fixed_build_dir = '/colo/build/workloads/fixed_builds'
    release_version = _release_to_version(target)
    assert release_version is not None, 'No fixed build for %s' % target
    return os.path.join(fixed_build_dir, release_version, 'Prod/Build')


def emit_testbed(ctr=1, host=0, host_12_cpus=False, host_3_ssds=False, number_of_ssds=1,
                 tester=0, vc=0, ucenter=0, build=None, linux=0, HA=True, **kwargs):
    """
    Emit testbed string used in set testbed.

    @param ctr: number of HA controller nodes
    @param host: number of esx hosts
    @param host_12_cpus: if the host needs 12 cpus
    @param host_3_ssds: if the host needs 3 SSDs, default is 2
    @param tester: number of testers (DesktopTester is always used to run binary)
    @param vc: number of vSphere centers
    @param ucenter: number of Upgrade Centers
    @param build: current, stable, future, or release target
    @param linux: number of linux hosts
    @param HA: If True deploy 2 controllers in HA else single controller
    @returns: testbed string
    """
    # Testbed components.
    ha_res = """
        { 'HA': %s, 'resources': { 'disks': [
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False},
            {'gbytes': 5, 'ssd': False}, ] } }
    """ % HA

    host_ssd_res = {'disks': []}

    # TODO ARUN: remove host_3_ssds argument and update test plans
    # with number_of_ssds=3
    if host_3_ssds:
        number_of_ssds = 3
    if number_of_ssds > 1:
        size = 60
        disks = []
        for ssd in range(0, number_of_ssds):
            size = size + ssd * 10
            disks.append({'gbytes': size, 'ssd': True})
        host_ssd_res['disks'] = disks

    insane_mode_res = {'ncpus': 12}

    tb_str = '{'
    if ctr:
        tb_str += "'VirtualControllerNode':[%d, %s], " % (ctr, ha_res)
    host_res = {}
    if host_12_cpus:
        host_res.update(insane_mode_res)
    if number_of_ssds > 1:
        host_res.update(host_ssd_res)
    if host:
        if host_res:
            tb_str += "'VirtualFrontEnd':[%d, {'resources':%s}], " % (
                host, host_res)
        else:
            tb_str += "'VirtualFrontEnd':%d, " % host
    if linux:
        if host_res:
            tb_str += "'VirtualKVMFrontEnd':[%d, {'resources':%s}], " % (
                linux, host_res)
        else:
            tb_str += "'VirtualKVMFrontEnd':%d, " % linux
    if tester:
        tb_str += "'DesktopTester':%d, " % tester
    if vc:
        tb_str += "'VirtualVCenter':%d, " % vc
    if ucenter:
        tb_str += "'VirtualUCenter':%d, " % ucenter
    tb_str += '}'
    # Testbed build.
    # To override stable build. Use environment variable LATEST_STABLE_OVERRIDE.
    # For example: LATEST_STABLE_OVERRIDE=jenkins_build-main-master_1234
    builds = {
        'current': '@buildtop',
        'future': '@future',
        'stable': '@%s' % (os.getenv('LATEST_STABLE_OVERRIDE') or 'jenkins_last-stable'),
    }
    if build is not None:
        tb_str += builds[build] if build in builds else get_fixed_path_of_release_build(target=build)
    return tb_str


# dedupe the following once all upgrade tests are ported
def get_fixed_path_of_current_build(**kwargs):
    # a wrapper around _release_to_version() to get current build's fixed
    # built path which can be given as an input to @testtypes.set_testbeds()
    return '@buildtop'

def get_fixed_path_of_future_build(**kwargs):
    # a wrapper around _release_to_version() to get future build's fixed
    # built path which can be given as an input to @testtypes.set_testbeds()
    return '@future'


def get_fixed_path_of_release_build(**kwargs):
    # a wrapper around _release_to_version() to release build's fixed
    # built path which can be given as an input to @testtypes.set_testbeds()
    release_version = _release_to_version(kwargs.get('target', 'release'))
    if release_version is not None:
        return '@fixed_%s' % release_version
    return '@prev_release_stable'


def get_fixed_path_of_stable_build(**kwargs):
    # a wrapper around _release_to_version() to last stable
    # built path which can be given as an input to @testtypes.set_testbeds()
    return '@jenkins_last-stable'

class BuildInfo(object):
    '''
    When we run dabuild info on a built url we get the following store what we care about, for now.
    dabuild info http://jenkins.datrium.com/job/build-main-4.1.x/586/
    tags: ['<b><font color=blue>4.1.1.0-32916_afb7007</font></b>', 'autosupport',
        'baseline', 'baseline-release', 'boothalt', 'build-main-archive', 'build-main-fake',
        'downgrade-fe-stable', 'dvfs1', 'dvfs2', 'fe', 'ha', 'ha-d', 'physical', 'stable0',
        'stable1', 'upgrade-ctr-future', 'upgrade-fe-future', 'upgrade-fe-stable', 'upgrade-sanity']
    stable: True
    released: False
    mountpoint: /colo/build/jobs/build-main-4.1.x/builds/586/archive
    started_at: 2018-10-08 07:30:24
    binary_url: http://jenkins.datrium.com/job/build-main-4.1.x/586/artifact/OS/Build/x86_64/da-os-Release.bin
    sha1: afb7007c8f2bdf885482f07b0586c047f2f9df69
    ended_at: 2018-10-08 08:26:45
    url: http://jenkins.datrium.com/job/build-main-4.1.x/586/
    bugs:
    artifacts: True
    version: 4.1.1.0-32916_afb7007
    time: 2018-10-08 08:26:45'''
    def __init__(self, **kwargs):
        self.build_url = kwargs.get('build_url', None)
        self.mount_point = kwargs.get('mount_point', None)
        self.binary_url_dbg = kwargs.get('binary_url_dbg', None)
        self.binary_url_prod = kwargs.get('binary_url_prod', None)
        self.software_version = kwargs.get('software_version', None)

        assert(self.build_url != None)
        assert(self.mount_point != None)
        assert(self.binary_url_dbg != None)
        assert(self.binary_url_prod != None)
        assert(self.software_version != None)

    def get_software_version(self):
        logging.info('%s() software version: %s', curr_function_name(), self.software_version)
        return self.software_version

    def get_binary_url(self, current_version=None):

        assert current_version != None
        url_to_return = None
        # FIXME: this does not belong here move the logic somewhere else
        if (current_version.strip().endswith('_g')):
            url_to_return = self.binary_url_dbg
        else:
            url_to_return = self.binary_url_prod

        logging.info('%s() current_version: %s url_to_return: %s',
                    curr_function_name(), current_version, url_to_return)
        return url_to_return

    def get_build_url(self):
        logging.info('%s() build_url: %s', curr_function_name(), self.build_url)
        return self.build_url

class StableBuildHelper(object):
    def __init__(self, **kwargs):
        self.path_to_da_python_interpreter = '/da/ToolsAndLibs/CodingScripts/python'
        self.path_to_dabuild = kwargs.get('path_to_dabuild', None)
        if self.path_to_dabuild == None:
            self.path_to_dabuild = '/da/ToolsAndLibs/CodingScripts/dabuild.py'

        self.list_of_stable_build_info_objects = []

    def create_build_info_object_from_output(self, output):
        build_url = None
        mount_point = None
        binary_url = None
        binary_url_dbg = None
        binary_url_prod = None
        software_version = None
        for line in output:
            if (line.strip().startswith('url:')):
                build_url = line.strip().split()[1]
            elif (line.strip().startswith('mountpoint:')):
                mount_point = line.strip().split()[1]
            elif (line.strip().startswith('binary_url:')):
                binary_url = line.strip().split()[1]
                binary_url_prod = binary_url
                # ensure dabuild doesnt switch between type of build url
                assert 'da-os-Release.bin' in binary_url_prod
                binary_url_dbg = binary_url.replace('da-os-Release.bin', 'da-os-Debug.bin')
            elif (line.strip().startswith('version:')):
                software_version = line.strip().split()[1]
            else:
                continue

        assert(build_url != None)
        assert(mount_point != None)
        assert(binary_url != None)
        assert(binary_url_dbg != None)
        assert(binary_url_prod != None)
        assert(software_version != None)

        return BuildInfo(build_url=build_url,
                  mount_point=mount_point,
                  binary_url_prod=binary_url_prod,
                  binary_url_dbg=binary_url_dbg,
                  software_version=software_version)

    def populate_build_info(self, build_url):

        exec_helper = DaExecHelper.LocalExecHelper(logger=logging.getLogger('upgrade_test_lib'))
        cmd = '%s %s info %s' % (self.path_to_da_python_interpreter, self.path_to_dabuild, build_url)
        cmd_info = exec_helper.exec_cmd(cmd=cmd)
        assert cmd_info.get_exit_code() == 0, 'Failed to get info for buildurl: %s' % (build_url)

        build_info = self.create_build_info_object_from_output(cmd_info.get_stdout_in_lines())
        assert build_info.get_build_url() == build_url

        self.list_of_stable_build_info_objects.append(build_info)
        logging.debug('%s() Create buildinfo from %s', curr_function_name(), build_url)

    def populate_all_stable_builds(self, branch, **kwargs):
        self.list_of_stable_build_info_objects = [] # drop all known builds
        cmd = '%s %s stable -b %s' % (self.path_to_da_python_interpreter, self.path_to_dabuild, branch)
        exec_helper = DaExecHelper.LocalExecHelper(logger=logging.getLogger('upgrade_test_lib'))

        cmd_info = exec_helper.exec_cmd(cmd=cmd)
        assert cmd_info.get_exit_code() == 0, (
            'Failed to get stable build information %s' % (cmd_info.get_stderr()))

        list_of_build_urls = []
        for line in cmd_info.get_stdout_in_lines():
            if (line.strip().startswith('http')):
                list_of_build_urls.append(line.strip().split()[0].strip())

        assert len(list_of_build_urls) > 0, 'no stable build found! in branch: %s' % (branch)
        for build_url in list_of_build_urls:
            self.populate_build_info(build_url)

    def get_stable_build_objects(self):
        return copy.deepcopy(self.list_of_stable_build_info_objects)

    def get_stable_build_to_upgrade_to(self, current_running_version, **kwargs):
        # TODO: add an option in command line to exclude a or a list of builds from this

        stable_builds = self.get_stable_build_objects()
        assert len(stable_builds) > 0, 'did you populate stable builds?'

        # this list will contain latest first, for now use latest, later start randomizing
        for build in stable_builds:
            # an example build number: 4.1.1.0-32915_dae0a70_p_g it can contain _p_g_
            # for this comparison we dont care about that, just 4.1.1.0-32915 is what we need
            if (LooseVersion(current_running_version.split('_')[0]) ==
                    LooseVersion(build.get_software_version().split('_')[0])):
                continue

            return build

        assert 0, 'Not reachable'

    def get_stable_build_to_download(self, version_to_exclude, upgrade_download_task_helper,
                                     **kwargs):
        """
        Return a build info from stable builds which is not already
        downloaded and not currently running.
        If you want to introduce negative test case
        reuse the same build info which you downloaded the last time.
        """

        stable_builds = self.get_stable_build_objects()
        assert len(stable_builds) > 0, 'did you populate stable builds?'

        current_running_version = upgrade_download_task_helper.get_current_running_version_on_active()

        # it is possible in a large scale setup if caller issues a failover
        # after he retrieves this object, that node might have a different
        # version locally downloaded in its image bank, possibly due to
        # a download command which partially succeeded in the past
        current_downloaded_version = upgrade_download_task_helper.get_current_downloaded_version()

        # this list will contain latest first, for now use latest, later start randomizing
        for build in stable_builds:
            # an example build number: 4.1.1.0-32915_dae0a70_p_g it can contain _p_g_
            # for this comparison we dont care about that, just 4.1.1.0-32915 is what we need
            # it is possible this is none, because when test starts there is nothing downloaded
            if current_downloaded_version != None:
                if (LooseVersion(current_downloaded_version.split('_')[0]) ==
                        LooseVersion(build.get_software_version().split('_')[0])):
                    continue

            if (LooseVersion(current_running_version.split('_')[0]) ==
                    LooseVersion(build.get_software_version().split('_')[0])):
                continue

            # it is possible this is none, because when test starts there is nothing downloaded
            if version_to_exclude != None:
                if (LooseVersion(version_to_exclude.split('_')[0]) ==
                    LooseVersion(build.get_software_version().split('_')[0])):
                    continue

            return build

        assert 0, 'Unable to find a stable build which is not downloaded and not running'

def get_current_branch_from_this_version(current_version):
    branch = None

    # example version number is 5.0.1.0-36088_8251a01_g get '5.0.1.0' from it
    current_version = current_version.split('-')[0]

    if current_version == '5.1.100.0':
        branch = 'master'

    if current_version == '5.1.1.0':
        branch = '5.1.x'

    if current_version == '5.0.1.0':
        branch = '5.0.x'

    if current_version == '4.1.1.0':
        branch = '4.1.x'

    assert branch != None, 'Could not find a branch %s' % (current_version)

    return branch

class RunningTaskOnUpgradeMgr(object):
    def __init__(self, pre_task_start_time, task_start_time_in_ns, task_id, **kwargs):
        self.pre_task_start_time = pre_task_start_time
        self.task_start_time_in_ns = task_start_time_in_ns
        self.__task_id = task_id

        self.__task_complete = False
        self.__task_succeeded = None

    def get_task_start_time_in_utc_in_string(self):
        '''
        this will match what is shown on dev software show
        '''
        return datetime.datetime.utcfromtimestamp(self.task_start_time_in_ns / 10 ** 9).strftime("%Y-%m-%dT%H:%M:%S")

    def get_task_id(self):
        return self.__task_id

    def is_task_complete(self):
        return self.__task_complete

    def set_task_complete(self, state):
        '''
        This function must be invoked exactly once
        '''
        assert self.__task_complete == False, 'Please dont reuse the object'
        self.__task_complete = True

        assert self.__task_succeeded == None, 'Please dont reuse the object'
        assert state == False or state == True
        self.__task_succeeded = state

    def did_succeed(self):
        assert self.__task_succeeded != None, 'Did you wait for the task to complete?'
        return self.__task_succeeded

class UpgradeErrorInjector(object):
    '''
    A simple error helper class for injecting error during test
    '''
    __metaclass__ = abc.ABCMeta
    def __init__(self, **kwargs):
        # FIXME(sachin): use consistent way of creating this
        self.master_active_executor = kwargs.get('master_active_executor', None)
        assert self.master_active_executor != None, (
            'Please provide master_active_executor in %s' % kwargs)

        self.logger = kwargs.get('logger', None)
        assert self.logger != None, 'Please provide logger in %s' % kwargs

        self.error_injection_frequency = kwargs.get('error_injection_frequency', 0)
        self.num_invocations = 0

    def get_this_event(self, event_type, since_when, **kwargs):
        cmd = 'events show --event-type %s ' % event_type
        cmd += '--show-all --from-time %s --output-format=json' % since_when
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
        return yaml.load(cmd_info.get_stdout())

    def should_inject_error(self, **kwargs):
        '''
        if self.num_invocations % self.error_injection_frequency == 0, returns True
        else False

        self.num_invocations is incremented on every invocation
        '''

        self.num_invocations += 1

        if self.error_injection_frequency == 0:
            return False

        if self.num_invocations % self.error_injection_frequency == 0:
            return True

        return False

    def set_stress_counter(self, stress_counter_name, stress_counter_value, component_id, **kwargs):
        # first enable stress counters if caller did not specify to disable
        enable_stress = kwargs.get('enable_stress', True)
        if enable_stress == True:
            cmd = 'dev conf set ConfStressCounter.enabled=true'
        else:
            cmd = 'dev conf set ConfStressCounter.enabled=false'
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd)
        assert cmd_info.get_exit_code() == 0, 'failed to set conf %s' % cmd_info.get_debug_info()

        # now enable the asked for stress counter
        cmd = 'dev conf set ConfStressCounter.%s=%s' % (stress_counter_name, stress_counter_value)
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd)
        assert cmd_info.get_exit_code() == 0, 'failed to set conf %s' % cmd_info.get_debug_info()

        assert self.wait_for_compliance(stress_counter_name, component_id,
                                        int(stress_counter_value)) == True, (
            'Stress counter %s not in compliance' % stress_counter_name)

    def wait_for_compliance(self, stress_counter_name,
                            component_id, expected_value, **kwargs):
        # this supports only int64 stress counters if you need something else
        # please add another and switch based on kwargs.get(typeof_stress)
        num_retries = kwargs.get('num_retries', 5)
        # other value types of not tested, test and add caller
        value_type = kwargs.get('value_type', 'int64Val')
        while num_retries >= 0:
            num_retries -= 1
            cmd = 'dev conf show ConfStressCounter --output-format=json'
            cmd_info = self.master_active_executor.exec_cmd(cmd=cmd)
            result = yaml.load(cmd_info.get_stdout())
            current_component_nodes = []
            for node in result['actual']:
                if component_id in node['componentId']:
                    current_component_nodes.append(node)

            atleast_one_not_compliant = False
            for node in current_component_nodes:
                if node.get('compliance') != 'COMPLIANT':
                    break

                for pairs in node.get('field'):
                    if pairs.get('key') == stress_counter_name:
                        if pairs.get('val').get(value_type) == expected_value:
                            pass
                        else:
                            atleast_one_not_compliant = True

            if atleast_one_not_compliant == False:
                return True

            if num_retries > 0:
                self.logger.info('Sleeping for 30 seconds to check for compliance')
                time.sleep(30)

        return False

    # these methods must be implemented by each injector class
    @abc.abstractmethod
    def inject_error_if(self, **kwargs):
        assert 0, 'Not implemented'

    @abc.abstractmethod
    def is_enabled(self, **kwargs):
        assert 0, 'Not implemented'

    @abc.abstractmethod
    def verify_events(self, **kwargs):
        assert 0, 'Not implemented'

    @abc.abstractmethod
    def reset_stress_counter(self, **kwargs):
        assert 0, 'Not implemented'

class UpgradeMgrFailHAMgrFailUpInjector(UpgradeErrorInjector):
    def __init__(self, **kwargs):
        super(UpgradeMgrFailHAMgrFailUpInjector, self).__init__(**kwargs)

        self.component_id = 'UpgradeMgr'
        self.stress_counter_name = 'upgradeMgrFailHAMgrFailUp'
        self.stress_counter_value = 1
        self.stress_reset_value = 0

    def inject_error_if(self, **kwargs):
        if self.should_inject_error() == False:
            return # nothing to do

        self.set_stress_counter(self.stress_counter_name,
                                self.stress_counter_value, self.component_id)

    def is_enabled(self, **kwargs):
        # FIXME(sachin): write a read function this might sleep
        return self.wait_for_compliance(self.stress_counter_name, self.component_id, 1, num_retries=1)

    def verify_events(self, task_info, **kwargs):
        assert task_info.is_task_complete() == True, (
            'Cant verify events for an incomplete task! %s' % task_info.get_task_id())

        upgrade_start_event_result = self.get_this_event('UpgradeStartEvent',
                                                         task_info.get_task_start_time_in_utc_in_string())
        upgrade_rollback_event_result = self.get_this_event('UpgradeFailAndRollbackEvent',
                                                            task_info.get_task_start_time_in_utc_in_string())
        upgrade_success_event_result = self.get_this_event('UpgradeSuccessEvent',
                                                           task_info.get_task_start_time_in_utc_in_string())

        upgrade_start_event = upgrade_start_event_result.get('events')
        upgrade_rollback_event = upgrade_rollback_event_result.get('events')
        upgrade_success_event = upgrade_success_event_result.get('events')

        # if this blows up we dont want to test to fail with failed to verify event
        # so just return the failure back, let the caller dump a bunch of things
        # with exception so that triaging will becomes less painful
        if (len(upgrade_start_event) != 1):
            self.logger.error("Upgrade start event verification error: %s", upgrade_start_event_result)
            return False

        if self.is_enabled() == True:
            if (len(upgrade_rollback_event) != 1):
                self.logger.error("Upgrade rollback event verification error: %s", upgrade_rollback_event_result)
                return False
            else:
                return True
        else:
            if (len(upgrade_success_event) != 1):
                self.logger.error("Upgrade success event verification error: %s", upgrade_success_event_result)
                return False
            else:
                return True

        assert 0, 'Cant be here'

    def reset_stress_counter(self, **kwargs):
        # we could cache this internally but if its from previous
        # process cycle, state will be messed up so just use the command
        self.set_stress_counter(self.stress_counter_name,
                                self.stress_reset_value, self.component_id,
                                enable_stress=False)

class UserSpecifiedBuildInfo(object):
    def __init__(self, daos_file_abs_path, version):
        self.daos_file_abs_path = daos_file_abs_path
        self.version = version

    def get_path_to_file(self):
        return self.daos_file_abs_path

    def get_software_version(self):
        return self.version

    def get_dest_path_on_dvx(self):
        dest_location = '/da/data/%s' %(self.daos_file_abs_path.strip().split('/')[-1])
        return dest_location

class TarFileHelper(DaTestTempFileDirHelper.TestFileDirHelper):
    def __init__(self, **kwargs):
        super(TarFileHelper, self).__init__(**kwargs)
        self.open_tar_file_handles = []

    def __del__(self):
        for tar_file_handle in self.open_tar_file_handles:
            try:
                tar_file_handle.close()
            except:
                pass

    def open_tar_file(self, file_name):
        assert self.is_this_a_file(file_name) # caller must check for this
        assert tarfile.is_tarfile(file_name)
        tar_file_handle = tarfile.open(file_name)
        self.open_tar_file_handles.append(tar_file_handle)
        return tar_file_handle

    def get_this_file_contents(self, tar_file_name, file_name):
        tar_file_handle = self.open_tar_file(tar_file_name)
        assert tar_file_handle != None

        assert file_name in tar_file_handle.getnames(), (
            '%s not present in %s' %(file_name, tar_file_handle.getnames()))
        requested_file_handle = tar_file_handle.extractfile(file_name)
        # readlines here since it returns as an array split by '\n' easier to parse
        contents = requested_file_handle.readlines()
        requested_file_handle.close()

        return contents

class UserSpecifiedBuildUpgradeLooptestRunner(object):
    def __init__(self, upgrade_download_helper, **kwargs):
        # ud_helper stands for upgrade download helper to reduce length of lines
        self.ud_helper = upgrade_download_helper
        self.logger = kwargs.get('logger', None)
        assert self.logger != None, 'please provide logger in %s' % kwargs

        self.tar_file_helper = TarFileHelper(**kwargs)

        # __populate_user_specified_builds() will populate this
        self.list_of_build_infos = []

    def __insert_build_info(self, version, daos_filepath):
        build_info_to_insert = None
        for build_info in self.list_of_build_infos:
            if build_info.get_software_version() == version:
                build_info_to_insert = build_info

        assert build_info_to_insert == None, (
            'Dont allow duplicate builds for now found dup %s %s from already inserted %s %s' %
            (version, daos_filepath, build_info_to_insert.get_software_version(),
             build_info_to_insert.get_path_to_file()))

        self.logger.info('Inserting new build info %s %s', version, daos_filepath)
        self.list_of_build_infos.append(UserSpecifiedBuildInfo(daos_filepath, version))

    def __check_if_can_upgrade(self, target_version):
        """
        check if current version is release/debug and target_version
        is matching, else upgrade will fail and we will need to debug
        This is not supported, just block it here
        """
        current_running_version = self.ud_helper.get_current_running_version_on_active()
        is_current_running_debug = current_running_version.strip().endswith('_g')
        is_target_debug = target_version.strip().endswith('_g')

        # we need EXNOR of these two values:
        # return true if both are true or both are false else return false
        return not(is_current_running_debug ^ is_target_debug)

    def __get_version_of_this_build(self, daos_file, **kwargs):
        version_from_spec = None
        tar_file_helper = TarFileHelper(**kwargs)
        spec_contents = tar_file_helper.get_this_file_contents(daos_file, 'SPEC')

        for line in spec_contents:
            if line.startswith('OSVersion'):
                version_from_spec = line.split('=')[1].strip()
                break

        assert version_from_spec != None, 'Unable to find version from %s' % (daos_file)
        return version_from_spec

    def __populate_user_specified_builds(self, **kwargs):
        first_build_file = kwargs.get('first_build', None)
        assert first_build_file != None, 'Please provide --first-build <abs path to file>'
        second_build_file = kwargs.get('second_build', None)
        assert second_build_file != None, 'Please provide --second-build <abs path to file>'

        assert self.tar_file_helper.is_this_a_file(first_build_file) == True, (
            '%s not a file!' % (first_build_file))
        assert self.tar_file_helper.is_this_a_file(second_build_file) == True, (
            '%s not a file!' % (second_build_file))

        first_build_version = self.__get_version_of_this_build(first_build_file, **kwargs)
        second_build_version = self.__get_version_of_this_build(second_build_file, **kwargs)

        assert self.__check_if_can_upgrade(first_build_version) == True, (
            'Please ensure you have provided same type of build %s as current running version %s'
            % (first_build_version, self.ud_helper.get_current_running_version_on_active()))

        assert self.__check_if_can_upgrade(second_build_version) == True, (
            'Please ensure you have provided same type of build %s as current running version %s'
            % (first_build_version, self.ud_helper.get_current_running_version_on_active()))

        # this function will take care of duplicates
        self.__insert_build_info(first_build_version, first_build_file)
        self.__insert_build_info(second_build_version, second_build_file)

    def get_next_build_to_attempt_upgrade_to(self):
        assert len(self.list_of_build_infos) >= 2, (
            'For this to run, we need atleast 2 private builds current %s' %
            (self.list_of_build_infos))
        current_running_version = self.ud_helper.get_current_running_version_on_active()
        for build_info in self.list_of_build_infos:
            if build_info.get_software_version() != current_running_version:
                self.logger.info('Returning %s %s',
                            build_info.get_software_version(),
                            build_info.get_path_to_file())
                return build_info

        assert 0, ('Should not be here! %s %s %s' %
                   (current_running_version,
                    len(self.list_of_build_infos), self.list_of_build_infos))

    def run_upgrade_loop_test(self, **kwargs):
        self.__populate_user_specified_builds(**kwargs)
        master_active_executor = self.ud_helper.get_master_active_executor()
        error_injection_frequency = kwargs.get('error_injection_frequency')

        failup_stress_injector =\
            UpgradeMgrFailHAMgrFailUpInjector(master_active_executor=master_active_executor,
                                              **kwargs)

        num_iterations = int(kwargs.get('num_iterations'))
        if error_injection_frequency > 0:
            # increase num iterations if stress is supposed to be introduced
            num_iterations *= 2

        failup_stress_injector.reset_stress_counter()
        # if the frequency is set to 2, arming this so that stress will fire on the first upgrade
        # TODO:(sachin): do the math and arm this based on the frequency
        failup_stress_injector.inject_error_if()

        num_seconds_to_sleep = int(kwargs.get('timeout_between_upgrades'))
        while num_iterations > 0:
            num_iterations -= 1

            failup_stress_injector.inject_error_if()
            build_info = self.get_next_build_to_attempt_upgrade_to()
            expect_success = (failup_stress_injector.is_enabled() != True)

            task_info = self.ud_helper.trigger_upgrade_and_wait_to_finish(build_info,
                                                                          expect_success=expect_success)
            success = failup_stress_injector.verify_events(task_info)
            # there is some work needed here to put this inside trigger_upgrade_and_wait_to_finish
            assert success == True, 'Failed to verify events associated with stress counter'
            stress_enabled = failup_stress_injector.is_enabled()
            failup_stress_injector.reset_stress_counter()

            current_running_version = self.ud_helper.get_current_running_version_on_active()
            # check here until trigger_upgrade_and_wait_to_finish() is implemented to do this
            if stress_enabled == False:
                assert build_info.get_software_version() in current_running_version, (
                    'upgrade did not succeed expected: %s found: %s'
                    % (current_running_version, build_info.get_software_version()))

            if num_iterations > 0:
                self.logger.info('Sleeping for %s seconds before next iteration', num_seconds_to_sleep)
                time.sleep(num_seconds_to_sleep)

        # reset this once again before releasing the testbed
        failup_stress_injector.reset_stress_counter()

class UpgradeDownloadTaskHelper(object):
    '''
    A helper class to start tasks on UpgradeMgr and wait for it to complete
    Currently supports upgrade and download tasks.
    '''

    def __init__(self, **kwargs):
        self.logger = kwargs.get('logger', None)
        if self.logger == None:
            self.logger = logging.getLogger('upgrade_test_lib')

        self.master_active_executor = kwargs.get('master_active_executor', None)
        assert self.master_active_executor != None

    def get_master_active_executor(self):
        return self.master_active_executor

    def copy_to_master(self, local_file_path, remote_file_path, **kwargs):
        # FIXME(sachin): check if local_file_path exists before invoking
        self.master_active_executor.copy_file_to_master_active(local_file_path, remote_file_path, **kwargs)

    def __parse_task_submit_output(self, cmd_info):
        '''
        FIXME(sachin): use this format everywhere
        :param cmd_info : an object returned from executor trying to execute a command
                          which attempts to start a task on UpgradeMgr
        :return: returns values for keys success and returnMessage
        :raises: none
        '''
        assert cmd_info.get_exit_code() == 0, 'Did you forget to check this?'

        results = yaml.load(cmd_info.get_stdout())
        assert len(results) == 2, 'Num pairs in result != 2 %s' % cmd_info.get_debug_info()
        assert results.has_key('success') == True, (
            'key success missing %s' % cmd_info.get_debug_info())
        assert results.has_key('returnMessage') == True, (
            'key returnMessage missing %s' % cmd_info.get_debug_info())

        return results.get('success'), results.get('returnMessage')

    def force_refresh_image_cache_on_upgrade_mgr(self, **kwargs):
        cmd = 'dev software show --refresh --output-format=json'
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)

    def __get_current_running_task_id_and_start_time(self, **kwargs):
        # FIXME(sachin): put this string somewhere so that when we want to enable
        # --refresh we can do it at one place and it'll just work
        cmd = 'dev software show --output-format=json'
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
        results = yaml.load(cmd_info.get_stdout())
        assert results.has_key('taskHistory') == True, (
            'Key taskHistory missing %s' % cmd_info.get_debug_info())
        tasks = results.get('taskHistory')
        for task in tasks:
            if task.get('state') == 'Running':
                return task.get('id'), task.get('startTime')

        assert 0, 'Did not find a running task! %s' % tasks

    def __start_this_task(self, **kwargs):
        cmd = kwargs.get('cmd', None)
        assert cmd != None

        date_cmd = 'date +"%Y-%m-%dT%H:%M:%S"'
        cmd_info = self.master_active_executor.exec_cmd(cmd=date_cmd, assert_on_non_zero=True)
        pre_task_start_time = cmd_info.get_stdout().rstrip()

        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
        task_started, _ = self.__parse_task_submit_output(cmd_info)
        assert task_started == True, 'Unable to start task %s' % cmd_info.get_debug_info()

        # FIXME(sachin): there can be very quick tasks, since we have pre_task_start_time
        # we can get any task which was submitted after this time
        task_id, task_start_time_in_ns = self.__get_current_running_task_id_and_start_time()
        self.logger.info('Task with cmd: %s started with id: %s', cmd, task_id)

        return RunningTaskOnUpgradeMgr(pre_task_start_time, task_start_time_in_ns, task_id)

    def get_current_remotely_available_versions(self, **kwargs):
        remote_images = []
        # when we upload stable builds to upgrade center, lower versions
        # will not be shown per bug 44289 hence using dev software show here
        cmd = 'dev software show --output-format=json'
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
        results = yaml.load(cmd_info.get_stdout())
        assert results.has_key('softwareImages') == True, (
            'Unable to find current running version %s' % cmd_info.get_debug_info())
        images = results.get('softwareImages')
        assert len(images) > 0, (
            'Unable to find current running version %s' % cmd_info.get_debug_info())
        for image in images:
            if image.get('status') == 'Remote':
                remote_images.append(image.get('version'))

        self.logger.info('Found %s images which are available on upgrade center', remote_images)
        return remote_images

    def wait_for_this_image_to_show_up_on_upgrade_center(self, expected_version, timeout, **kwargs):
        deadline = time.time() + timeout
        while True:
            if time.time() > deadline:
                break
            remote_images = self.get_current_remotely_available_versions(**kwargs)
            for remote_image in remote_images:
                # when we query from dabuild we get only version
                # depending on whether or not its debug build running version
                # might contain a _g at the end
                if expected_version in remote_image:
                    self.logger.info('Found %s in %s', expected_version, remote_images)
                    return True
            else:
                self.logger.info('Did not find %s in %s, yet', expected_version, remote_images)
                self.force_refresh_image_cache_on_upgrade_mgr()
                continue

        return False

    def get_current_running_version_on_active(self, **kwargs):
        cmd = 'dvx software show --output-format=json'
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
        results = yaml.load(cmd_info.get_stdout())
        assert results.has_key('softwareImages') == True, (
            'Unable to find current running version %s' % cmd_info.get_debug_info())
        images = results.get('softwareImages')
        assert len(images) > 0, (
            'Unable to find current running version %s' % cmd_info.get_debug_info())
        for image in images:
            if image.get('status') == 'Running':
                return image.get('version')

        assert 0, 'Unable to find current running version %s' % cmd_info.get_debug_info()

    def get_downloaded_versions_from_upgrade_util(self, **kwargs):
        cmd = 'upgrade_util.py list-local 2>/dev/null'
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
        output = cmd_info.get_stdout()

        # ugly parsing, but read through: we need version numbers only
        #['status_code=0 total_images=2\r',
        #'msg=okay\r',
        #'5.1.1.0-37040_5833327_p_g\r',
        #'2019-05-30 13:24:59\r',
        #'None\r',
        #'5.1.1.0-37000_986e8ba_g\r',
        #'2019-05-28 10:01:19\r',
        #'invalid_due_to_dev_cmd\r',
        #'']
        output = output.replace('\r', '').split('\n')
        line1 = output[0]
        assert 'status_code=0' in line1, '%s' % output

        line1 = line1.replace('status_code=0 ', '')
        total_images = int(line1.split('=')[1])

        assert total_images > 0, 'No images found through upgrade_util %s' % cmd_info.get_debug_info()

        # first version is found at idx == 2 and the next 2 + 3, same logic below
        # we will continue to look until we exhaust total_images
        version_number_idx = 2
        version_numbers = []
        pending_images = total_images
        for idx, line in enumerate(output):
            if idx == 0 or idx == 1:
                continue

            if idx == version_number_idx:
                version_numbers.append(line)
                version_number_idx += 3
                pending_images -= 1
                if pending_images == 0:
                    break

        assert pending_images == 0
        assert len(version_numbers) == total_images

        return version_numbers

    def ensure_this_version_is_downloaded(self, version, **kwargs):
        """
        Given a version number we need to verify from 3 places:
        1. dev software show and ensure downloaded version matches this
        2. upgrade_util.py list-local parsing this is quite difficult
        do we need to do plat_tool as well?
        """
        assert version != None

        current_downloaded_version = self.get_current_downloaded_version()
        assert current_downloaded_version != None, 'Can not find downloaded version'
        assert LooseVersion(version.split('_')[0]) == \
                LooseVersion(current_downloaded_version.split('_')[0]) , (
                'Loose version of the downloaded version %s does not match incoming %s' % (
                current_downloaded_version, version))

        local_versions_from_upgrade_util = self.get_downloaded_versions_from_upgrade_util()
        found = False
        for local_version in local_versions_from_upgrade_util:
            if LooseVersion(local_version.split('_')[0]) == LooseVersion(version.split('_')[0]):
                found = True
                break

        assert found == True, (
            'Unable to find the incoming version %s from upgrade_util %s' % (
            version, local_versions_from_upgrade_util))

    def get_current_downloaded_version(self, **kwargs):
        cmd = 'dev software show --output-format=json'
        cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
        results = yaml.load(cmd_info.get_stdout())
        assert results.has_key('softwareImages') == True, (
            'Unable to find current running version %s' % cmd_info.get_debug_info())

        images = results.get('softwareImages')
        # there should be atleast running version here hence the assert
        assert len(images) > 0, (
            'Unable to find downloaded version %s' % cmd_info.get_debug_info())

        # there must be only one image at all times which is downloaded however
        # due to disk replacement etc we have seen multiple so lets have some room
        downloaded_images = []
        for image in results.get('softwareImages'):
            if image.get('status') == 'Downloaded':
                downloaded_images.append(image)

        if len(downloaded_images) == 0:
            return None

        assert len(downloaded_images) == 1, (
            'Found more than one downloaded image! %s' % downloaded_images)

        # {'buildTime': '2019-05-20 13:46:52',
        # 'releaseNoteUrl': 'invalid_due_to_dev_cmd',
        # 'status': 'Downloaded',
        # 'version': '5.1.1.0-36970_2de7593_g'},
        # this is how it looks like we only care about version
        return downloaded_images[0]['version']

    def trigger_upgrade_with_this_cmd(self, **kwargs):
        '''
        cmd must be present in **kwargs which tells how should be upgrade
        triggered, i.e., the owner of this object can choose from:
        1. download a bundle and then do dvx software upgrade <downloaded_version>
        2. dev software upgrade <localfile>
        3. dev software upgrade <http link>
        4. dvx software upgrade <a non downloaded version from upgrade center>
        5. dev software upgrade <https link>, do we need this at all? upto caller
        '''
        return self.__start_this_task(**kwargs)

    def trigger_download_with_this_cmd(self, **kwargs):
        '''
        The owner of this object can choose from:
        1. dev software download <local file on active>
        2. dev software download <http link>
        3. dev software download <https link>
        4. dev software download <version on upgrade center>
        '''
        return self.__start_this_task(**kwargs)

    def __check_task_state(self, task_info, cmd_info):
        results = yaml.load(cmd_info.get_stdout())
        # FIXME(sachin): put these keys in one place
        assert results.has_key('taskHistory') == True, (
            'Key taskHistory missing %s' % cmd_info.get_debug_info())
        tasks = results.get('taskHistory')
        assert len(tasks) > 0, (
            'Unable to find task_id: %s in current list %s'
            % (task_info.get_task_id(), cmd_info.get_debug_info()))
        found_task = None
        for task in tasks:
            if task.get('id') == task_info.get_task_id():
                found_task = task
                break

        assert found_task != None, (
            'Unable to find task: %s from list %s' % (task_info.get_task_id(), tasks))

        progressPercent = found_task.get('progress')
        assert progressPercent <= 100, 'Progress percent greater than 100! %s' % found_task

        expected_states = ['Success', 'Error']
        if found_task.get('state') in expected_states:
            self.logger.info('Task %s complete %s', task_info.get_task_id(), found_task)
            if found_task.get('state') == 'Success':
                success = True
            else:
                success = False

            assert task_info.is_task_complete() == False, 'Are you reusing the task_info object?'
            task_info.set_task_complete(success)

            # task is complete
            return True

        # we found the task but it hasn't completed at this time.
        return False

    def did_this_task_complete(self, task_info, **kwargs):
        '''
        A helper function to check if a previously submitted task
        has completed.
        '''
        # if you plan to kill and issue failover please wait
        # for it to recover before killing again
        # FIXME(sachin): put all these things in a config file or some common place
        timeout = kwargs.get('timeout', 180)
        # failover time + 10 seconds buffer
        failure_timeout = kwargs.get('failure_timeout', 150)

        time_to_sleep_between_retries = int(kwargs.get('time_to_sleep_between_retries', 60))

        deadline = time.time() + timeout
        # put this string in one place and reuse
        cmd = 'dvx software show --output-format=json'
        while True:
            if time.time() > deadline:
                break

            try:
                cmd_info = self.master_active_executor.exec_cmd(cmd=cmd, assert_on_non_zero=True)
                if self.__check_task_state(task_info, cmd_info):
                    return True # task has completed
                time.sleep(time_to_sleep_between_retries)
                continue
            except:
                # we will retry until the deadline is hit
                self.logger.exception('Unable to get task state')
                time.sleep(failure_timeout)
                continue

        # either task did not complete or we could not determine given current
        # timeout, its upto caller to handle it
        return False

    def wait_for_this_task_completion(self, task_info, **kwargs):
        '''
        A helper function to wait for a previously submitted task.
        With error injection we will introduce failovers very often
        so we wont know how many times we can hit dvx software show error
        so take an optional timeout value(which is the max value upgrade)
        can take(set it to say 4 hours), and we will retry for this time
        no matter what happens.
        '''
        expect_success = kwargs.get('expect_success', False)

        # wait for 3 hours on a blocking call before declaring failure
        timeout = kwargs.get('timeout', 10800)
        self.logger.info('Will wait for task: %s to complete for %s',
                         task_info.get_task_id(), timeout)

        new_args = dict(kwargs)
        new_args['timeout'] = timeout

        task_complete = self.did_this_task_complete(task_info, **new_args)
        assert task_complete == True, 'Task not complete with task_id = %s' % task_info.get_task_id()

        if expect_success == True:
            # TODO(sachin):
            # concat the following and throw that string with the exception, reduce the need to pez mount
            # 1. task status of task_id
            # 2. all precheck events filed since the time we started this task
            # 3. any internal events which were filed since we started this task
            # 4. last 100 lines of upgrade_util.log
            # 5. current running version and downloaded versions
            # 6. find out the type of task from task_id, if upgrade ensure requested version is target
            #   on all controller and hosts. Everything should be determined through dvx's floating ip
            #   dont rely on dva, otherwise standalone test wont work.
            # do these before making upgrade tests use this
            assert task_info.did_succeed() == True, (
                'Expected task with id to succeed %s' % task_info.get_task_id())

        return task_info

    def __choose_a_way_to_upgrade_and_do_pre_steps(self, build_info, **kwargs):

        requested_type_of_upgrade = kwargs.get('requested_type_of_upgrade', None)

        # FIXME(sachin): these two lines are temp asserts since all options
        # are not implemented, I will add implementation add a caller for it
        # starting with upgrade loop test
        assert requested_type_of_upgrade == 'local_file_based_direct_upgrade'
        assert isinstance(build_info, UserSpecifiedBuildInfo)

        assert isinstance(build_info, UserSpecifiedBuildInfo) or isinstance(build_info, BuildInfo)

        # FIXME(sachin): write a one liner comment for each of the below
        url_based_upgrade_options = ['url_based_download_and_upgrade',
                                     'url_based_direct_upgrade']
        local_file_based_upgrade_options = ['local_file_based_download_and_upgrade',
                                            'local_file_based_direct_upgrade']
        type_of_upgrades = url_based_upgrade_options + local_file_based_upgrade_options

        if requested_type_of_upgrade != None:
            assert requested_type_of_upgrade in type_of_upgrades, (
                'Please provide one from already implemented in %s provided: %s' %
                (type_of_upgrades, requested_type_of_upgrade))

            # if caller provided a UserSpecifiedBuildInfo() and requested
            # url_based_download_and_upgrade || url_based_direct_upgrade cant do
            if isinstance(build_info, UserSpecifiedBuildInfo):
                assert requested_type_of_upgrade in local_file_based_upgrade_options, (
                    'Can not do %s with UserSpecifiedBuildInfo() dont specify and randomize or use %s'
                    % (requested_type_of_upgrade, local_file_based_upgrade_options))
            else:
                assert isinstance(build_info, BuildInfo)

        # lets choose one if not specified
        if requested_type_of_upgrade == None:
            if isinstance(build_info, UserSpecifiedBuildInfo):
                requested_type_of_upgrade = random.choice(local_file_based_upgrade_options)
            else:
                requested_type_of_upgrade = type_of_upgrades

        cmd = None
        if requested_type_of_upgrade == 'url_based_download_and_upgrade':
            # this is already supported, will enable when there is a caller
            # for it so that its tested
            assert isinstance(build_info, BuildInfo)
            assert 0, 'Not implemented yet'
        elif requested_type_of_upgrade == 'url_based_direct_upgrade':
            # this is already supported, will enable when there is a caller
            # for it so that its tested
            assert isinstance(build_info, BuildInfo)
            assert 0, 'Not implemented yet'
        elif requested_type_of_upgrade == 'local_file_based_download_and_upgrade':
            # need to implement trigger_download_and_wait_to_finish()
            # just invoke here with respective option set cmd and return
            assert isinstance(build_info, UserSpecifiedBuildInfo) or isinstance(build_info, BuildInfo)
            assert 0, 'Not implemented yet'
        elif requested_type_of_upgrade == 'local_file_based_direct_upgrade':
            if isinstance(build_info, UserSpecifiedBuildInfo):
                self.copy_to_master(build_info.get_path_to_file(),
                    build_info.get_dest_path_on_dvx())
                # with bug 44289 we treat lower build number of as a downgrade and force is
                # needed so that customer can not downgrade to a lower patch from GUI
                # this does not mean anything except if --disruptive is enabled except for
                # this flag. The right way to is to get current version, and if this version
                # is lower to that, then we force, however this is used by loop test which
                # will switch between various stable builds which most likely will be lower build
                cmd = 'dev software upgrade %s --force' % build_info.get_dest_path_on_dvx()
                cmd += ' --output-format=json --no-confirm'
            else:
                assert isinstance(build_info, BuildInfo)
                # wget the file to local and set cmd
                assert 0, 'Not implemented yet'
        else:
            assert 0, 'Cant be here!'

        assert cmd != None
        # caller must use command to trigger upgrade on master active controller
        return cmd

    def trigger_upgrade_and_wait_to_finish(self,
                                           build_info,
                                           **kwargs):
        '''
        Given a build_info it can be one of the two types:
            UserSpecifiedBuildInfo() which is built from a user specified build
             or BuildInfo() built from stable build
        This function chooses a way to upgrade(unless specified by caller) from:
            dev software download <local file>
            dev software download <url> if this build if of type BuildInfo()
            +
            dev software upgrade <local file>
            dev software upgade <url> if this build is of type BuildInfo()

        TODO: make caller pass an optional upgrade center ip address so we could
        also exercise dev software download <version> and dev software upgrade <version>
        '''
        # FIXME(sachin): 39605 This is temporary until we move
        # stuff from upgrade_loop test to this file and modify
        # loop test caller to go through here
        requested_type_of_upgrade = 'local_file_based_direct_upgrade'
        assert isinstance(build_info, UserSpecifiedBuildInfo)
        cmd = self.__choose_a_way_to_upgrade_and_do_pre_steps(build_info,
                                                              requested_type_of_upgrade=requested_type_of_upgrade,
                                                              **kwargs)
        task_info = self.trigger_upgrade_with_this_cmd(cmd=cmd)
        # stress counter not implemented yet
        # dont add expect_success here
        # need to add did_upgrade_behave() which should create all known
        # stress counter helpers, and check if any is enabled if it is
        # check if it could cause failure, in which case succeed the test
        # else blow up
        # else its upto caller to specify expect_success = True otherwise
        # he wont know if there is a failure. should we flip this to true?
        # so that all callers know and they are careful to disable
        # while enabling stress counters
        return self.wait_for_this_task_completion(task_info)

def get_upgrade_download_task_helper(controller_ip):
    kwargs = dict()
    kwargs['logger'] = logger=logging.getLogger('upgrade_test_lib')
    kwargs['dvx_ip'] = controller_ip
    master_active_executor = MasterActiveHelper.get_master_active_helper(**kwargs)
    return UpgradeDownloadTaskHelper(master_active_executor=master_active_executor, **kwargs)

def get_event_value(event, key, val_type):
    """
    Extract value from a single event instance.

    @param event: event instance
    @param key: unique key
    @param val_type: value type as 'stringVal', 'enumVal', 'msgVal', etc
    @return: the value associated with the key and type
    """
    for v in event['keyValues']:
        if v['key'] == key:
            return v['val'][val_type]
    else:
        return None

def _get_event_op_string(event):
    """
    Get event value using the 'op' key and 'stringVal' type.

    @param event: event instance
    @returns: the associated value
    """
    return get_event_value(event, 'op', 'stringVal')


def _get_event_cause_string(event):
    """
    Get event value using the 'cause' key and 'stringVal' type.

    @param event: event instance
    @returns: the associated value
    """
    return get_event_value(event, 'cause', 'stringVal')


def _get_event_resolution_string(event):
    """
    Get event value using the 'resolution' key and 'stringVal' type.

    @param event: event instance
    @returns: the associated value
    """
    return get_event_value(event, 'resolution', 'stringVal')


def get_host_version(host):
    """
    Get datrium head software version on the host.

    @param host: host instance
    @return: software version
    """
    if isinstance(host, TestBeds.hosttypes.standalone.KVMFrontEnd):
        return host.version
    else:
        return host.check_output(
            'source /opt/datrium/etc/profile.datrium; da_setup --get_running_version').rstrip()


def get_controller_version(controller):
    """
    Get controller software version.
    We don't use controller.version because it returns the master's version
    (via dvx software show) even if it is invoked on the passive controller.
    Using 'cat /etc/Version.txt' ensures that we return the passive's version
    if invoked on the passive.
    @param controller: controller instance
    @return: software version
    """
    return controller.check_output('cat /etc/Version.txt')


def get_float_ip(controller, is_data):
    """
    Get controller's floating IP.

    @param controller: controller instance
    @param is_data: data or management floating IP
    @return: requested floating IP
    """
    output = controller.check_output('network show --output-format=json')
    return yaml.load(output)['data' if is_data else 'management']['floating']


def _get_controller_events(controller, event_types, from_time,
                           wait_for_n_events):
    """
    Get controller events based on the type and timestamp.

    @param controller: controller instance
    @param event_types: event names separated by space
    @param from_time: get events on or after this time, if specified.
                      Note that the timestamp should be local to the controller.
    @param wait_for_n_events: will wait for at least "n" events or timeout.
                              Obviously, 0 implies no wait.
    @return: list of requested events
    """

    for _ in retry.retry(timeout=300, sleeptime=5):
        cmd = 'events show --event-type %s --show-all --output-format=json' % event_types
        if from_time:
            cmd += ' --from-time %s' % from_time
        output = controller.check_output(cmd)
        res = yaml.load(output)['events']
        if len(res) >= wait_for_n_events:
            return res


def set_dvx_conf(controller, arg, comply_comp=False):
    """
    Set DVX config variable.

    @param controller: controller instance
    @param arg: argument to set
    @param comply_comp: if specified, wait for the named component for compliance
    @return: None
    """
    for _ in retry.retry(timeout=300, sleeptime=0.5):
        try:
            controller.check_call('dev conf set %s' % arg)
            break
        except subprocess.CalledProcessError:
            continue
    else:
        assert False, 'Timed out dev conf set %s' % arg

    if comply_comp:
        confgrp = arg.split('.')[0]
        for _ in retry.retry(timeout=300, sleeptime=0.5):
            try:
                output = controller.check_output('dev conf show %s --output-format=json' % confgrp)
                for c in yaml.load(output)['actual']:
                    if comply_comp in c['componentId'] and c['compliance'] == 'COMPLIANT':
                        return
            except subprocess.CalledProcessError:
                continue
        else:
            assert False, 'Timed out waiting compliance for %s' % arg


def remove_host_cores(host):
    """
    Remove core dumps on the host.

    @param host: host instance
    @return: None
    """
    # Starting in 1.1.0, /var/core points to /var/log/datrium/core on the
    # dasys datastore, which points to the dacore datastore on that
    # same drive.
    core_dir = '/var/core'
    output = host.check_output('ls -l %s' % core_dir)
    if '/var/log/datrium/core' in output:
        core_dir = '/var/log/datrium/core'
        output = host.check_output('ls -l %s' % core_dir)
    assert '/vmfs/volumes' in output, '%s not set correctly: %s' % (core_dir, output)
    host.check_output('ls -l %s/' % core_dir)
    host.check_call('rm -f %s/*zdump.*' % core_dir)
    host.check_output('ls -l %s/' % core_dir)


def reboot_host(host, forced):
    """
    Reboot the host. Wait for IP address.

    @param host: host instance
    @param forced: forced reboot or not.
    @return: None
    """
    # Check for core files before rebooting.
    out = host.check_output('ls -l /var/core')
    assert 'zdump' not in out, out
    logging.info('Rebooting host %s, forced %s', host.ipaddr, forced)
    reboot_cmd = 'reboot'
    if forced:
        reboot_cmd += ' -f'
    host.check_call(reboot_cmd)
    # Wait for reboot to finish.
    host.wait_for_reboot(timeout=600)
    host.wait_ipaddr(timeout=300)
    host.wait_for_hostd(timeout=300)
    # Install NfsPerfTool after the reboot.
    host.install_test_binaries()


def remove_host_bogus_mount_point(host):
    """
    If we reboot after using the bogus mount point to do umount_hosts(), the bogus
    mount point can still be there retrying after the reboot. This function remove it.

    @param host: host instance
    @return: None
    """
    host.call('esxcfg-nas -d bogus')


def wait_host_procmgr(host):
    """
    Wait for host procmgr to start.

    @param host: host instance
    @return: None
    """
    for _ in retry.retry(timeout=240, sleeptime=20):
        try:
            out = host.check_output(host.binary('procmgr_cli.py') + ' show')
            if 'Mode/Changing' in out:
                break
        except subprocess.CalledProcessError:
            pass


def poweroff_passive_node(controller):
    """
    Power-off a controller node.

    @param controller: controller instance
    @return None
    """
    controller.passive.vm.PowerOffVM_Task().wait()


def mount_hosts(hosts, label='Datastore1'):
    """
    Mount the hosts to controller.

    @param hosts: list of host instances
    @param label: mount point label
    @return: None
    """
    # TODO(rtang): retire this, moved to server_plat_test_lib.py
    for host in hosts:
        host.mount(label=label)


def get_host_label(controller, label="Datastore1"):
    """
    Get datastore name

    @param controller: controller instance
    """
    return get_dvx_name(controller) + "-" + label


def get_dvx_name(controller):
    """
    Get NetShelf name.

    @param controller: controller instance
    """
    return yaml.load(controller.cli('config dvx show --output-format json'))['name']


def get_volume_labels(hosts):
    """
    get volume labels

    @param hosts: list of host instances
    """
    # TODO(rtang): Moved to server_plat_test_lib.py. Remove this later.
    if not isinstance(hosts, (tuple, list)):
        hosts = [hosts]
    vol_labels = []
    for host in hosts:
        if isinstance(host, TestBeds.hosttypes.standalone.KVMFrontEnd):
            vol_labels += host.get_mount_labels()
        else:
            output = host.esxcli('--formatter=json --debug storage nfs list')
            for vol in json.loads(output):
                vol_labels.append(str(vol['VolumeName'].encode('utf-8')))
    return list(set(vol_labels))


def mount_hosts_pre_2_0_x(hosts, controller, use_premount, label):
    """
    Mount the hosts to controller.

    @param hosts: list of host instances
    @param controller: controller instance
    @param use_premount: whether to call premount before mount
    @param label: mount point label
    @return: None
    """
    # TODO(rtang): retire this, moved to server_plat_test_lib.py
    data_ip = get_float_ip(controller, True)
    assert data_ip, 'Data floating IP not configured on controller %s' % controller.ipaddr

    for host in hosts:
        assert not host.is_mounted(label), '%s already mounted on host %s' % (label, host.ipaddr)
        if use_premount:
            try:
                host.check_call('if [ -f /opt/datrium/bin/premount_cli ]; then ' +
                                ' /opt/datrium/bin/premount_cli ' + data_ip +
                                ' ; else /opt/datrium/bin/premount ' + data_ip + ' ; fi')
            except:
                # If premount fails, dump its result.
                host.check_call('cat /tmp/.premount_result')
                raise
        host.check_call('/bin/esxcfg-nas -a -o localhost -s /%s/Datastore1 "%s"' % (data_ip, label))
        assert host.is_mounted(label), "Mount failed on host %s" % host.ipaddr

    wait_hosts_mount_point_writable(hosts, label)


#FIXME(sachin): nuke this function once standalone.py:umount() supports dacli umount
def umount_hosts(hosts, controller, set_bogus, remove_from_ctr, labels):
    """
    Un-mount the hosts from controller.

    @param hosts: list of host instances
    @param controller: controller instance
    @param set_bogus: set the bogus mount point as a workaround
    @param remove_from_ctr: explicitly remove hosts from controller
    @param labels: single or list of mount point labels
    @return: None
    """
    # TODO(rtang): Moving to server_plat_test_lib, remove.
    if not isinstance(labels, (tuple, list)):
        labels = [labels]

    nfh_hosts = []
    sfh_hosts = []
    for host in hosts:
        if host.is_NFH_mode:
            nfh_hosts.append(host)
        else:
            sfh_hosts.append(host)

    for host in nfh_hosts + sfh_hosts:  # un-mount NFH hosts first.
        for label in labels:
            # Asserting could be problematic while switching to "dacli datastores", just log it.
            if not host.is_mounted(label):
                logging.debug('Mount point %s does not exist on host %s' % (label, host.ipaddr))
            if isinstance(host, TestBeds.hosttypes.standalone.KVMFrontEnd) or host.use_old_mount:
                host.umount(label=label)
            else:
                for _ in retry.retry(attempts=5, sleeptime=35, raises=False):
                    # Allow min 140 secs for a NFH to be able to unmount.
                    # For a SFH, retry up to 25 seconds to unmount due to opened file.
                    try:
                        # TODO(Arun): In future when we have multiple datastores
                        # mounted, we may need to make changes in this, because it
                        # might not unmount all and then we may need to pass in the
                        # label name
                        # TODO(kyle) Workaround for upgrade tests.
                        # This needs to move to server_plat_test_lib and needs to be more robust.
                        mounted = server_plat_test_lib.dacli_get_mounted_datastores(host)
                        for d in mounted:
                            host.check_output('/opt/datrium/bin/dacli datastores umount -n %s' % d['vol_name'])
                        if not host.is_mounted(label):
                            break
                    except subprocess.CalledProcessError as e:
                        logging.debug(e.output)
                        if 'Busy' in e.output:
                            continue
                        elif 'not mounted with NFS' not in e.output:
                            # Debug info to see what process failed the umount.
                            logging.warn(host.check_output("lsof"))
                            raise Exception('Umount failed')

                if set_bogus:
                    try:  # expect mount to fail
                        host.check_call('/bin/esxcfg-nas -a -o localhost -s /localhost/Datastore1 bogus')
                        assert False, 'Mounting bogus controller succeeded?'
                    except subprocess.CalledProcessError:
                        pass

        if remove_from_ctr:
            try:  # host may have been removed (failure) or still in use (--force)
                controller.check_call('hosts remove %s --force' % host.ipaddr)
            except subprocess.CalledProcessError:
                pass


def unmount_hosts_pre_2_0_x(hosts, label):
    """
    Un-mount the hosts from controller.

    @param hosts: list of host instances
    @param label: mount point label
    @return: None
    """
    for host in hosts:
        assert host.is_mounted(label), 'Mount point %s does not exist on host %s' % (
            label, host.ipaddr)
        host.check_output('/bin/esxcfg-nas -d "%s"' % label)


def write_hosts_mountpoint(hosts, labels, filename, content):
    """
    Write a tiny test file on hosts' mount point.

    @param hosts: list of host instances
    @param labels: list of mount point labels
    @param filename: file name
    @param content: file content
    @return: None
    """
    # TODO(rtang): remove this once all upgrade tests are migrated to use
    #              server_plat_test_lib.write_hosts_mountpoint()
    if not isinstance(labels, (tuple, list)):
        labels = [labels]
    for i, host in enumerate(hosts):
        for label in labels:
            assert host.is_mounted_and_writable(label), (
                'Mount point %s does not exist on host %s' % (label, host.ipaddr))
            host.check_call('echo "%s" > %s/host_%d_%s' %
                            (content, host.mntpath(label), i, filename))


def verify_hosts_mountpoint(hosts, labels, filename, content):
    """
    Verify the previously written file on hosts' mount point.

    @param hosts: list of host instances
    @param labels: list of mount point labels
    @param filename: file name
    @param content: file content
    @return: None
    """
    # TODO(rtang): remove this once all upgrade tests are migrated to use
    #              server_plat_test_lib.verify_hosts_mountpoint()
    if not isinstance(labels, (tuple, list)):
        labels = [labels]
    # Verify hosts' mount points exists.
    for i, host in enumerate(hosts):
        for label in labels:
            assert host.is_mounted(label), 'Mount point %s does not exist on host %s' % (
                label, host.ipaddr)

            # Verify hosts' mount points accessible and writable.
            wait_hosts_mount_point_writable([host], label)

            # Verify hosts' mount points file content.
            output = host.check_output('cat %s/host_%d_%s' %
                                       (host.mntpath(label), i, filename)).rstrip()
            assert output == content, (
                'Failed to verify mount point on host %s, read="%s", expect="%s"' %
                (host.ipaddr, output, content))


def verify_hosts_mountpoint_after_reboot(hosts, label, filename, content):
    """
    Verify the hosts' mount point after reboot.
    After reboot, it may take up to 300 secs for host to re-establish the mount point.

    @param hosts: list of host instances
    @param label: mount point label
    @param filename: file name
    @param content: file content
    @return: None
    """
    # TODO(rtang): Move this function to server_plat_test_lib.py
    for _ in retry.retry(timeout=300, sleeptime=10):
        try:
            verify_hosts_mountpoint(hosts, label, filename, content)
            break
        except (subprocess.CalledProcessError, AssertionError) as err:
            logging.error(err)


def _verify_start_end_event(controller, start_event, end_event, base_time):
    """
    Verify the latest task's start and end events and return their timestamps.

    @param controller: controller instance
    @param start_event: name of the start event
    @param end_event: name of the end event
    @param base_time: the timestamp just before the task
    @return: upgrade start and end time stamp
    """
    logging.info('Verifying start and finish events, %s and %s', start_event, end_event)
    events = _get_controller_events(controller, start_event, base_time, 1)
    start_time = int(events[0]['triggerTime'])

    events = _get_controller_events(controller, end_event, base_time, 1)
    end_time = int(events[0]['triggerTime'])

    logging.info('Timestamps: %s=%s %s=%s', start_event, start_time, end_event, end_time)
    assert start_time < end_time, 'Start time is not before end time'
    return start_time, end_time


def verify_upgrade_events(controller, base_time):
    """
    Verify controller events for normal upgrade.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @return: upgrade start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'UpgradeStartEvent',
                                                   'UpgradeSuccessEvent', base_time)

    # No failure events.
    logging.info('Verifying failure events')
    events = [e for e in
              _get_controller_events(controller, 'UpgradeFailureDetailEvent', base_time, 0)
              if start_time < int(e['triggerTime']) < end_time]
    assert len(events) == 0, 'Upgrade failed: %s' % _get_event_op_string(events[0])

    return start_time, end_time


def verify_upgrade_events_fail_start(controller, base_time, expected_msg):
    """
    Verify controller events when upgrade fails to start.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @param expected_msg: expected text in the failure event
    @return: upgrade start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'UpgradeStartEvent',
                                                   'UpgradeFailToStartEvent', base_time)

    # There is a specific failure event.
    logging.info('Verifying failure events')
    events = [e for e in
              _get_controller_events(controller, 'UpgradeFailureDetailEvent', base_time, 1)
              if start_time < int(e['triggerTime']) < end_time]
    assert (len(events) == 1 and expected_msg in _get_event_op_string(events[0])), (
        'Failed to verify UpgradeFailureDetailEvent: %s' % events)

    return start_time, end_time


def verify_upgrade_events_complete_with_error(controller, base_time, expected_msg):
    """
    Verify controller events when upgrade completed with error.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @param expected_msg: expected text in the failure event
    @return: upgrade start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'UpgradeStartEvent',
                                                   'UpgradeCompleteWithErrorEvent', base_time)

    # There is a specific failure event.
    logging.info('Verifying failure events')
    events = [e for e in
              _get_controller_events(controller, 'UpgradeFailureDetailEvent', base_time, 1)
              if start_time < int(e['triggerTime']) < end_time]
    assert (len(events) == 1 and expected_msg in _get_event_op_string(events[0])), (
        'Failed to verify UpgradeFailureDetailEvent: %s' % events)
    return start_time, end_time


def verify_upgrade_events_passiveoff(controller, base_time):
    """
    Verify controller events for upgrade when passive controller is powered off.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @return: upgrade start and end time stamps
    """
    timeout_msg = 'Passive controller(s) failed to upgrade'

    start_time, end_time = _verify_start_end_event(controller, 'UpgradeStartEvent',
                                                   'UpgradeCompleteWithErrorEvent', base_time)

    # There is a specific failure event.
    logging.info('Verifying failure events')
    events = [e for e in
              _get_controller_events(controller, 'UpgradeFailureDetailEvent', base_time, 1)
              if start_time < int(e['triggerTime']) < end_time]
    assert (len(events) == 1 and timeout_msg in _get_event_op_string(events[0])), (
        'Failed to verify UpgradeFailureDetailEvent: %s' % events)

    return start_time, end_time


def _verify_failup_failure_event(controller, base_time, start_time, end_time):
    """
    Verify the failup failure event.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @return: None
    """
    # [Legacy] Remove the old text after release is set to Helium codebase.
    failure_msgs = ['Failed to initiate controller failover',  # Old text
                    'Failed to switch software version on']

    def is_switchover_fail_msg(event):
        for f in failure_msgs:
            if f in event:
                return True
        return False

    events = [e for e in
              _get_controller_events(controller, 'UpgradeFailureDetailEvent', base_time, 1)
              if start_time < int(e['triggerTime']) < end_time and
              is_switchover_fail_msg(_get_event_op_string(e))]
    assert len(events) == 1, 'Failed to verify failup failure event: %s' % events


def verify_upgrade_events_rollback(controller, base_time):
    """
    Verify controller events in the context of upgrade rollback.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @return: upgrade start and end time stamps
    """
    # [Legacy] Remove the old text after release is set to Helium codebase.
    rollback_msgs = ['Peer controller software rolled back',  # Old text
                     'Upgrade has been cancelled on all components']

    start_time, end_time = _verify_start_end_event(controller, 'UpgradeStartEvent',
                                                   'UpgradeFailAndRollbackEvent', base_time)

    # There is a specific failure event.
    logging.info('Verifying failure events')
    _verify_failup_failure_event(controller, base_time, start_time, end_time)

    # There is a specific progress event.
    logging.info('Verifying progress events')
    events = [e for e in _get_controller_events(controller, 'UpgradeProgressEvent', base_time, 1)
              if start_time < int(e['triggerTime']) < end_time and
              _get_event_op_string(e) in rollback_msgs]
    assert len(events) == 1, 'Failed to verify rollback progress event: %s' % events

    return start_time, end_time


def verify_upgrade_events_rollback_fail(controller, base_time, expected_msg):
    """
    Verify controller events when upgrade and rollback with failures.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @param expected_msg: expected text in the failure event
    @return: upgrade start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'UpgradeStartEvent',
                                                   'UpgradeRollbackFailEvent', base_time)

    # There is a specific event for fail-up failure.
    logging.info('Verifying failure events')
    _verify_failup_failure_event(controller, base_time, start_time, end_time)

    # There is a specific event for rollback failure.
    events = [e for e in
              _get_controller_events(controller, 'UpgradeFailureDetailEvent', base_time, 1)
              if start_time < int(e['triggerTime']) < end_time and
              expected_msg in _get_event_op_string(e)]
    assert len(events) == 1, 'Failed to verify UpgradeFailureDetailEvent: %s' % events

    return start_time, end_time


def verify_upgrade_events_disallow_old_release(controller, base_time,
                                               allowed_release, **kwargs):
    """
    Verify controller events after disallowing upgrading from prior to last release.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade
    @param allowed_release: the release number which is allowed to upgrade from
    @return: upgrade start and end time stamps
    """
    cause = 'Upgrading from prior to %s release not permitted' % allowed_release
    resolution = 'Upgrade to %s release first' % allowed_release

    event_helper = kwargs.get('event_helper', None)
    assert event_helper != None

    # FIXME(Sachin): move this inside event helper
    start_time, end_time = _verify_start_end_event(controller,
                                                   'UpgradeStartEvent',
                                                   'UpgradeFailToStartEvent',
                                                   base_time)

    event_verified = False
    upgrade_check_events_list = event_helper.get_upgrade_check_events_list()
    for upgrade_check_event in upgrade_check_events_list:
        if upgrade_check_event.get_error_code() == 10102:
            assert upgrade_check_event.get_cause() == cause, (
                'Cause of the event does not match: expected: %s, current: %s'
                % (cause, upgrade_check_event.get_cause()))
            assert upgrade_check_event.get_resolution() == resolution, (
                'Resolution of the event does not match: expected %s, current %s'
                % (resolution, upgrade_check_event.get_resolution()))
            event_verified = True

    assert event_verified == True, (
        'Unable to verify event associated with 10102 %s' % event_helper.get_events())

    return start_time, end_time

def verify_host_below_esxi60_upgrade_check_failure(controller, base_time, **kwargs):
    '''
    This is to verify production code complies with Bug-41071

    @param controller: controller object, need to verify UpgradeStartEvent and UpgradeFailToStartEvent
    @param: base_time: used to populate UpgradeStartEvent and UpgradeFailToStartEvent, in case
        if there is more than one attempt to upgrade during the test, we populate the events
        from this time
    @param **kwargs: currently event_helper is passed using this, adding a kwargs in case
        we need to pass an arg to any of the helper functions this function uses and caller
        needs to pass it an arg, when that makes no sense to this function.
    '''
    # current 5.5u2 maps to 5.5.0
    # so the error string will be ESXi with version 5.5.0 is not supported. Host: <IP address>
    cause1 = 'ESXi with version'
    cause2 = 'is not supported'
    resolution = 'Please upgrade the host to a supported release'
    start_time, end_time = _verify_start_end_event(controller,
                                                   'UpgradeStartEvent',
                                                   'UpgradeFailToStartEvent',
                                                    base_time)

    logging.info('Verifying upgrade precheck failed for ESXi host with kernel version below 6.0')

    event_helper = kwargs.get('event_helper', None)
    assert event_helper != None

    event_verified = False
    upgrade_check_events_list = event_helper.get_upgrade_check_events_list()
    for upgrade_check_event in upgrade_check_events_list:
        if upgrade_check_event.get_error_code() == 11063:
            assert cause1 in upgrade_check_event.get_cause() and cause2 in upgrade_check_event.get_cause(), (
                'Cause of the event does not match: expected: %s %s, current: %s'
                % (cause1, cause2, upgrade_check_event.get_cause()))
            assert upgrade_check_event.get_resolution() == resolution, (
                'Resolution of the event does not match: expected %s, current %s'
                % (resolution, upgrade_check_event.get_resolution()))
            event_verified = True

    assert event_verified == True, (
        'Unable to verify event associated with 11063 %s' % event_helper.get_events())

    return start_time, end_time

def verify_node_upgrade_events(master_node, num_events, base_time):
    """
    Verify controller events for addon nodes upgrade.

    @param master_node: Master controller node instance
    @param num_events: number of node upgrade events expected
    @param base_time: the timestamp just before upgrade
    @return: None
    """
    logging.info("Verifying addon nodes upgrade events")
    event_type = 'NodeUpgradeStartEvent'
    events = _get_controller_events(master_node, event_type, base_time, num_events)
    assert len(events) == num_events, (
        "%d node upgrade events observed, expecting %d" % (len(events), num_events))


def verify_node_add_events(master_node, num_events, base_time):
    """
    Verify controller events for node added.

    @param master_node: Master controller node instance
    @param num_events: number of node added events expected
    @param base_time: the timestamp just before adding node
    @return: None
    """
    logging.info("Verifying node add events")
    event_type = 'NodeAddedEvent'
    events = _get_controller_events(master_node, event_type, base_time, num_events)
    assert len(events) == num_events, (
        "%d node added events observed, expecting %d" % (len(events), num_events))


def verify_download_events(controller, base_time):
    """
    Verify controller events for normal download.

    @param controller: controller instance
    @param base_time: the timestamp just before download
    @return: download start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'DownloadStartEvent',
                                                   'DownloadSuccessEvent', base_time)

    # No failure events.
    logging.info('Verifying failure events')
    events = [e for e in _get_controller_events(controller, 'DownloadFailEvent', base_time, 0)
              if start_time < int(e['triggerTime']) < end_time]
    assert len(events) == 0, 'Download failed: %s' % get_event_value(events[0], 'reason',
                                                                     'stringVal')

    return start_time, end_time


def verify_download_events_fail(controller, base_time, expected_msg):
    """
    Verify controller events when download fails.

    @param controller: controller instance
    @param base_time: the timestamp just before download
    @param expected_msg: expected text in the failure event
    @return: download start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'DownloadStartEvent',
                                                   'DownloadFailEvent', base_time)

    # There is a specific failure event.
    logging.info('Verifying failure events')
    events = [e for e in _get_controller_events(controller, 'DownloadFailEvent', base_time, 1)
              if start_time < int(e['triggerTime']) <= end_time]
    assert len(events) == 1 and expected_msg in get_event_value(events[0], 'reason', 'stringVal'), (
        'Failed to verify DownloadFailEvent: %s' % events)

    return start_time, end_time


def verify_host_events(controller, num_events, start_time, end_time):
    """
    Verify host upgrade events.

    @param controller: controller instance
    @param num_events: number of host upgrade events expected
    @param start_time: event trigger time start
    @param end_time: event trigger time end
    @return: None
    """
    logging.info("Verifying host upgrade events")
    event_type = 'HostUpgradeStartEvent'
    events = [e for e in _get_controller_events(controller, event_type, None, num_events)
              if start_time < int(e['triggerTime']) < end_time]
    assert len(events) == num_events, (
        "%d host upgrade events observed, expecting %d" % (len(events), num_events))


def verify_controller_version(controller_node, version, ha=True):
    """
    Verify both active and passive controllers software version.

    @param controller_node: controller node instance
    @param version: expected version
    @param ha: if controller node is HA
    @return: None
    """
    node_name = controller_node.rolename
    active_controller_ver = get_controller_version(controller_node.active)
    assert active_controller_ver == version, (
        '%s active controller version mismatch, actual=%s, expect=%s' %
        (node_name, active_controller_ver, version))

    if ha:
        passive_controller_ver = get_controller_version(controller_node.passive)
        assert passive_controller_ver == version, (
            '%s passive controller version mismatch, actual=%s, expect=%s' %
            (node_name, passive_controller_ver, version))


def verify_controllers_version(controller_nodes, version):
    """
    Verify controllers software version.

    @param controller_nodes: controller node instances
    @param version: expected version
    @return: None
    """
    for controller_node in controller_nodes:
        verify_controller_version(controller_node, version)


def verify_hosts_version(hosts, version):
    """
    Verify datrium head software version on the hosts.

    @param hosts: list of host instances
    @param version: expected version
    @return: None
    """
    for host in hosts:
        ver = get_host_version(host)
        assert ver == version, 'Version mismatch on host %s, actual=%s, expect=%s' % (
            host.ipaddr, ver, version)


def get_vib_version(host):
    """
    Get datrium head VIB version on a host.

    @param host: host instance
    @return: short (1.0.4.2-seqnum) and long version
    """
    output = host.esxcli('software vib list | grep %s' % host.head_vibname)
    short_ver = output.strip().split()[1]
    output = host.check_output('cat /opt/datrium_initial_bundle/Version.txt')
    long_ver = output.strip()
    return short_ver, long_ver


def verify_vib_version(host, version):
    """
    Verify datrium head VIB version on a host.

    @param host: host instance
    @param version: expected version
    @return: None
    """
    short_ver, long_ver = get_vib_version(host)
    assert version == long_ver and version.startswith(short_ver), (
        'VIB version mismatch on host %s, actual=%s, %s, expect=%s'
        % (host.ipaddr, short_ver, long_ver, version))


def remove_hosts_vib(hosts):
    """
    Remove datrium head VIB from hosts.

    @param hosts: list of host instances
    @return: None
    """
    for host in hosts:
        # VIB removal is not implemented in standalone.py
        host.esxcli('software vib remove -n %s' % host.head_vibname)
        try:  # expect not to find datrium VIB
            host.esxcli('software vib list | grep datrium-head -i').strip()
            assert False, 'VIB uninstall failed on host %s' % host.ipaddr
        except subprocess.CalledProcessError:
            pass


def upgrade_host_vib(host, buildtop):
    """
    Upgrade datrium head VIB on a host.

    @param host: host instance
    @param buildtop: build top directory of the new VIB
    @return: None
    """
    path = os.path.join(buildtop, host.buildpath % host.dva.buildtype, 'head_bundle')
    vibpath = os.path.abspath(os.path.join(path, '%s.zip' % host.head_vibname))
    assert os.path.exists(vibpath), 'VIB %s does not exist' % vibpath
    host.upgrade(vibpath=vibpath, force_vib_install=True)


def install_host_tinyvib(host, vibpath=None, controller=None):
    assert controller or vibpath, 'must provide either controller or vibpath params'
    if controller:
        path = 'http://%s/static/ESXVIBHyperDriver' % controller.ipaddr
    else:
        vibzip = '%s.zip' % host.tiny_vibname
        assert vibpath.endswith(vibzip), 'vibpath must end with %s' % vibzip
        dstdir = '/var/tmp'
        host.put(vibpath, dstdir)
        path = os.path.join(dstdir, vibzip)

    for _ in retry.retry(attempts=3, sleeptime=5):
        try:
            out = host.esxcli('software vib install -d %s --no-sig-check' % path)
            assert 'Reboot Required: true' not in out
            break
        except subprocess.CalledProcessError as e:
            logging.warning(e.output)
            if host.has_vib(host.tiny_vibname):
                logging.info('Ignore error since %s has been installed.',
                             host.tiny_vibname)
                break
    time.sleep(5)

    # esx.conf variable should be there.
    host.check_call('grep -q DatriumNetshelfIp /etc/vmware/esx.conf')

    # check config agent is running.
    out = host.check_output('/etc/init.d/datrium_hyperdriver status')
    assert 'Datrium HyperDriver is running' in out, out
    out = host.check_output('ps -c|grep config_agent.sh')
    assert 'watchdog' in out, out
    assert '/bin/sh /opt/datrium_hyperdriver/bin/config_agent.sh' in out, out


def remove_host_tinyvib(host):
    try:
        # Sometimes vib removal failed with:
        # "can't remove '/tardisks/datrium_.v00': Device or resource busy".
        # The reason could be that datrium_hyperdriver or config_agent has
        # not completely terminated when the VIB is removed.
        #
        # VIB removal is not common for customer. In the test we can stop
        # the hyperdriver first before removing the VIB.
        host.check_call('/etc/init.d/datrium_hyperdriver stop')
    except:
        logging.error('Error stopping datrium_hyperdriver.')
    finally:
        time.sleep(5)

    try:
        host.esxcli('software vib remove -n datrium-hyperdriver-esx')
        time.sleep(5)
    except subprocess.CalledProcessError:
        host.call('lsof >/tmp/lsof2.out')
        raise

    # check for clean-up.
    host.check_call('grep -q DatriumNetshelfIp /etc/vmware/esx.conf')
    # check that config_agent.sh is not running.
    out = host.check_output('ps -c|grep config_agent.sh')
    assert 'watchdog' not in out, out
    assert '/bin/sh /opt/datrium_hyperdriver/bin/config_agent.sh' not in out, out


def bootstrap_host_tinyvib(host, controller):
    # bootstrap from the controller floating IP and verify.

    # make sure we can ping DataNode
    assert host.ping_host(controller.dataip, max_pkt_loss=50), (
        'Unable to ping %s' % controller.dataip)

    for _ in retry.retry(attempts=3, sleeptime=5):
        try:
            host.check_call('/opt/datrium_hyperdriver/bin/da %s' % controller.dataip)
            break
        except subprocess.CalledProcessError:
            assert host.ping_host(controller.dataip, max_pkt_loss=50), (
                'Unable to ping %s' % controller.dataip)
            host.check_call('/opt/datrium_hyperdriver/bin/da -d')

    time.sleep(5)
    verify_host_tinyvib_bootstrap(host, controller)


def select_all_ssds(host):
    # wait for platmgr & select all SSDs
    time_out = time.time() + 30
    while time.time() < time_out:
        out = host.check_output('ps -cu | grep esx_platmgr | grep -v grep | wc -l')
        if int(out.strip()) != 0:
            break
        time.sleep(1)
    assert int(out.strip()) != 0, out

    host.check_call('touch /var/log/esx_platmgr.log')
    time_out = time.time() + 30
    while time.time() < time_out:
        out = host.check_output('grep platmgr_0_api /var/log/esx_platmgr.log | wc -l')
        if int(out.strip()) != 0:
            break
        time.sleep(1)
    assert int(out.strip()) != 0, out

    # XXX (x): even after waiting for esx_platmgr to be ready, the check_call below
    #          can fail. Change to call() to avoid that.
    host.call('/opt/datrium/bin/dacli ssd add all --force')


def host_tinyvib_bootstrapped_ip(host):
    import IPy
    try:
        _ip = str(IPy.IP(host.check_output('/opt/datrium_hyperdriver/bin/da -l').strip()))
    except ValueError:
        _ip = None
    return _ip


def verify_host_tinyvib_bootstrap(host, controller):
    assert controller.dataip == host_tinyvib_bootstrapped_ip(host)
    out = host.check_output('ls -l /opt/datrium')
    assert 'da-sys' in out, out
    time_out = time.time() + 300
    while time.time() < time_out:
        out = host.check_output('/opt/datrium_hyperdriver/bin/da -c')
        if 'converged' in out:
            break
        time.sleep(1)
    assert 'converged' in out, out
    # make sure firewall is set.
    out = host.check_output('localcli network firewall ruleset list')
    assert 'datriumNfs' in out, out


def unbootstrap_host_tinyvib(host):
    mounts = host.datrium_mounts()
    assert not mounts, "Can't unbootstrap with existing mounts: %s" % mounts

    host.check_call('/opt/datrium_hyperdriver/bin/da -d')
    out = host.check_output('/opt/datrium_hyperdriver/bin/da -l')
    assert not out.strip(), out

    for _ in retry.retry(attempts=3, sleeptime=3):
        host.call('esxcli storage filesystem rescan')
        out = host.check_output('df -h')  # SSDs are cleaned.
        if 'datrium' not in out:
            break
        logging.info(out)

    out = host.check_output('ls /')  # ramfs are cleaned
    assert 'da-sys' not in out and 'dakv' not in out, out
    out = host.check_output('ls -l /var/core')  # core link is restored.
    assert '/scratch/core' in out, out
    out = host.check_output('ls -l /var/log/')  # log link is gone.
    assert 'datrium ->' not in out, out

    time.sleep(5)


def start_hosts_io(hosts, zkhosts, labels, file_size):
    """
    Start IO on all hosts simultaneously.

    @param hosts: list of host instances
    @param zkhosts: list of Zookeeper hosts
    @param labels: list of mount point labels on host
    @param file_size: file size in MB
    @return: IO runner handle
    """
    # TODO(rtang): Moving to server_plat_test_lib.py, remove.
    io_runner = nfsperftool.NfsIORunner(fes=hosts, zkhosts=zkhosts, mount_labels=labels,
                                        file_size=nfsperftool.MB * file_size,
                                        io_size=nfsperftool.MB)
    io_runner.start()
    return io_runner


def stop_hosts_io(io_runner):
    """
    Stop IO from all hosts.

    @param io_runner: IO runner handle
    @return: None
    """
    # TODO(rtang): Moving to server_plat_test_lib.py, remove.
    io_runner.stop_io()
    io_runner.check_exceptions_join()


def run_hosts_io(hosts, zkhosts, labels, file_size, duration):
    """
    Run IO on all hosts simultaneously for a given period of time.

    @param hosts: list of host instances
    @param zkhosts: list of Zookeeper hosts
    @param labels: list of mount point labels on host
    @param file_size: file size in MB
    @param duration: seconds to run the IO
    @return: None
    """
    # TODO(rtang): Moving to server_plat_test_lib.py, remove.
    io_runner = start_hosts_io(hosts, zkhosts, labels, file_size)
    time.sleep(duration)
    stop_hosts_io(io_runner)


def verify_controller_synced(controller_node):
    """
    Verify that controller is in HA-synced state.

    @param controller_node: controller node instance
    @return: None
    """
    assert controller_node.HA_is_synced(), 'Controller not in synced state'


def verify_controllers_synced(controller_nodes):
    """
    Verify that controller nodes are in HA-synced state.

    @param controller_nodes: controller nodes instances
    @return: None
    """
    for controller_node in controller_nodes:
        verify_controller_synced(controller_node)


def wait_controller_synced(controller):
    """
    Wait for controller is in HA-synced state.

    @param controller: controller instance
    @return: None
    """
    for _ in retry.retry(timeout=900, sleeptime=15):
        try:
            if controller.HA_is_synced():
                break
        except (subprocess.CalledProcessError, ssh.SSHException):
            continue


def start_download(controller, is_force, version_or_url):
    """
    Start downloading image on the controller.
    For a synchronous return, no task is triggered.

    Note: This function does not support 1.0.6.x code base.

    @param controller: controller instance
    @param is_force: download with force or not
    @param version_or_url: software version to download, or URL or path to the software image
    @return: base timestamp, command output and task ID
    """
    # Get the base timestamp just before the download.
    # Sleep one second to ensure download indeed happens later in the next second.
    base_time = controller.check_output('date +"%Y-%m-%dT%H:%M:%S"').rstrip()
    time.sleep(1)

    cmd = '%s software download %s' % ('dev' if is_force else 'dvx', version_or_url)
    if is_force:
        cmd += ' --force'
    task_id = None
    output = controller.check_output(cmd)
    # Pre 1.0.6.x code base does not support below Download message.
    is_started = re.search('Download of (.+) started', output)
    if is_started:
        version = is_started.group(1)
        assert software_version_lib.is_version_string(version), (
            '%s is not a valid version' % version)
        task_id = _get_controller_latest_task_id(controller, version)
    return base_time, output, task_id


def _get_controller_latest_task_id(controller, version):
    """
    Get the latest controller task ID.

    @param controller: controller instance
    @param version: version string
    @return: latest task ID
    """
    cmd = 'dvx software show --task-only --output-format=json'
    output = None
    for _ in retry.retry(timeout=300, sleeptime=10):
        try:
            output = controller.check_output(cmd)
            break
        # Handle Upgrade Manager crash for negative test cases.
        except subprocess.CalledProcessError:
            continue

    latest_task_start_time = 0
    latest_task_id = None
    for t in yaml.load(output)['taskHistory']:
        if t['taskParam'] == version:
            start_time = int(t['startTime'])
            if start_time > latest_task_start_time:
                latest_task_start_time = start_time
                latest_task_id = t['id']

    return latest_task_id


def _get_controller_task_by_id(controller, task_id):
    """
    Get the controller task by its ID.

    @param controller: controller instance
    @param task_id: task ID
    @return: task
    """
    cmd = 'dvx software show --task-only --output-format=json'
    output = controller.check_output(cmd)
    for t in yaml.load(output)['taskHistory']:
        if t['id'] == task_id:
            return t

    return None


def get_dvx_can_add_node_result(controller):
    """
    executes dvx can-add-node

    @param controller: controller instance
    @return touple containing canAddNode result in boolean and returnMessage
        returnMessage will be None if canAddNode is true
    """

    cmd = 'dvx can-add-node --output-format json'
    output = controller.cli(cmd.split(), internal=True)

    result = yaml.load(output)

    assert len(result) <= 2, "Num pairs in result <= 2"
    assert result.has_key('canAddNode') == True, "Key canAddNode missing!"
    if len(result) == 2:
        return result.get('canAddNode'), result.get('returnMessage')

    # returnMessage is optional and we will not populate it if canAddNode is true
    assert result.get('canAddNode') == True, 'canAddNode is not True, yet no msg %s' % result
    return result.get('canAddNode'), None


def upload_controller_image(controller, image):
    """
    Upload DaOS image to controller and save it to disks using the download CLI command.
    So that we can later operate based on version.

    Note: due to using start_download(), this function does not support 1.0.x code base.

    @param controller: controller instance
    @param image: image information which contains its version and file path
    @returns: None
    """
    # Make sure we operate on active controller.
    controller_ip = get_float_ip(controller, True)
    scp_controller_image(controller_ip, image['path'], '/da/data/daOS.bin')
    _, output, task_id = start_download(controller, True, '/da/data/daOS.bin')
    result, msg = wait_controller_task(controller, task_id, 1800, True)
    assert result == 'Success' and msg == 'Software image downloaded', (
        'Upload controller image failed: %s' % msg)


def upload_controller_image_10x(controller, image):
    """
    Upload DaOS image to controller and prepare the Upgrade Center description file.
    So that we can later operate based on version.

    Note: this function deals with 1.0.x backward compatibility.

    @param controller: controller instance
    @param image: image information which contains its version and file path
    @returns: None
    """
    # Make sure we operate on active controller.
    controller_ip = get_float_ip(controller, True)
    scp_controller_image(controller_ip, image['path'], '/da/data/daOS.bin')
    desp = [['/da/data/daOS.bin', image['version'], 'bogus_date', 'bogus_rel']]
    ssh.check_call(controller_ip, 'echo \'%s\' > /tmp/upgrade_center_des.override' %
                   json.dumps(desp))


def scp_controller_image(controller_ip, image_path, dest_path):
    """
    Upload DaOS image to controller.

    @param controller_ip: controller ip address
    @param image_path: source image file path on test runner
    @param dest_path: destination image file path on controller
    @return: None
    """
    ssh.put(controller_ip, image_path, dest_path)


def run_check_dupip_cmd(controller, **kwargs):
    # TODO(sachin): improve this to assert if we found a conflict once json output is available
    # dev tools check-duplicate-ip --across-dvx --output-format json
    # usage: check-duplicate-ip [-h] [--across-dvx] [--ip ip [DATA | MGMT]]
    # check-duplicate-ip: error: unrecognized arguments: --output-format json
    # dev tools check-duplicate-ip --output-format json --across-dvx
    # usage: check-duplicate-ip [-h] [--across-dvx] [--ip ip [DATA | MGMT]]
    # check-duplicate-ip: error: unrecognized arguments: --output-format json
    # when test fails we can inspect the logs to see if there was ip conflict

    check_ip_conflict_cmd = 'dev tools check-duplicate-ip --across-dvx'
    controller.check_output(check_ip_conflict_cmd)


def start_upgrade(controller, is_disruptive, is_force, version):
    """
    Start upgrading the controllers.
    For a synchronous return, no task is triggered.

    @param controller: controller instance
    @param is_disruptive: disruptive or non-disruptive upgrade mode
    @param is_force: upgrade with force or not
    @param version: software version to upgrade to
    @return: base timestamp, command output and upgrade task ID
    """
    # Get the base timestamp just before the upgrade.
    # Sleep one second to ensure upgrade indeed happens later in the next second.
    base_time = controller.check_output('date +"%Y-%m-%dT%H:%M:%S"').rstrip()
    time.sleep(1)
    # TODO(kyle, rtang) All upgrades should go through one interface, i.e., Standalone.upgrade()
    # instead of calling start_upgrade directly.
    # Newer deployments pass params via the machine.id, make sure it's in the .vmx file.
    for peer in controller.peers:
        if hasattr(peer, 'update_machineid'):
            peer.update_machineid(reconfig=True)
    # Issue upgrade command.
    cmd = '%s software upgrade %s' % ('dev' if is_disruptive or is_force else 'dvx', version)
    if is_disruptive:
        cmd += ' --disruptive'
    if is_force:
        cmd += ' --force'
    if not software_version_lib.is_lower_version(get_controller_version(controller),
                                                 '1.1.102.0-20478_2b9ed17'):
        cmd += ' --no-confirm'

    try:
        run_check_dupip_cmd(controller)
    except:
        pass

    output = controller.check_output(cmd)
    task_id = None
    if re.search('Upgrade .*started', output):
        task_id = _get_controller_latest_task_id(controller, version)
    return base_time, output, task_id

def induce_pre_n_plus_1_misalignment(dva):
    """
    N+1 requires that active controller on MASTER (node1) is the same as active
    controller on all other ADDON nodes.  To test this path of pre-cluster-upgrade,
    induce failovers on some of the ADDON nodes so that they have a different active
    controller than that of MASTER.

    @param dva: DVA object associated with the testbed.
    """
    logging.info('Inducing pre-N+1 controller misalignement')

    # Identify MASTER node's active controller number.
    master_active_controller_num = None
    for node in dva.controllers:
        if node.node_role_master:
            master_active_controller_num = node.active.controller_num
            break
    assert master_active_controller_num is not None

    # Identify list of ADDON nodes that have the same active controller as the MASTER node.
    aligned_addon_nodes = []
    for node in dva.controllers:
        if node.node_role_addon and node.active.controller_num == master_active_controller_num:
            aligned_addon_nodes.append(node)
    if len(aligned_addon_nodes) == 0:
        logging.info('Nothing to do. Number of nodes %s, number of aligned addons is zero',
                     len(dva.controllers))
        return

    # Induce failovers on a randomly chosen list of addon nodes that are currently aligned.
    misalign_all_addons = random.choice(['True', 'False'])
    if misalign_all_addons:
        num_misalignments_needed = len(aligned_addon_nodes)
    else:
        num_misalignments_needed = random.randint(1, len(aligned_addon_nodes))
    logging.info('Will induce %s failovers out of %s aligned addon nodes', num_misalignments_needed,
                 len(aligned_addon_nodes))
    failover_nodes = []
    while num_misalignments_needed > 0:
        node = random.choice(aligned_addon_nodes)
        logging.info('Inducing failover on node%s to make controller%s as active',
                     node.peers[0].node_num, master_active_controller_num)
        node.HA_failover()
        failover_nodes.append(node)
        aligned_addon_nodes.remove(node)
        num_misalignments_needed -= 1

    # Wait for the nodes that we triggered failover on to finish resync.
    for node in failover_nodes:
        node.HA_wait_for_synced()

def get_pre_post_cluster_upgrade_result(controller, cmd):
    # use cli if we plan to add this command to support mode
    output = controller.check_output(cmd)
    result = yaml.load(output)
    assert len(result) == 2, 'Num pairs in result != 2 %s' %(result)
    assert result.has_key('success') == True, 'Key success missing! %s' % (result)
    assert result.has_key('returnMessage') == True, 'Key returnMessage missing! %s' % (result)

    return result.get('success'), result.get('returnMessage')


def start_pre_cluster_upgrade(controller, version,
                              is_disruptive=False, is_force=False):
    is_disruptive_str = ''
    is_force_str = ''
    if (is_disruptive == True):
        is_disruptive_str = '--disruptive'
    if (is_force == True):
        is_force_str = '--force'

    cmd = 'dev software pre-cluster-upgrade %s %s %s --output-format=json'\
            % (version, is_disruptive_str, is_force_str)

    return get_pre_post_cluster_upgrade_result(controller, cmd)


def start_post_cluster_upgrade(controller, version,
                               is_disruptive=False, is_force=False):
    is_disruptive_str = ''
    is_force_str = ''
    if (is_disruptive == True):
        is_disruptive_str = '--disruptive'
    if (is_force == True):
        is_force_str = '--force'

    cmd = 'dev software post-cluster-upgrade %s %s %s --output-format=json'\
            % (version, is_disruptive_str, is_force_str)

    return get_pre_post_cluster_upgrade_result(controller, cmd)


def start_pre_cluster_upgrade_ensure_success(controller, version,
                                             is_disruptive=False, is_force=False):
    success, return_msg = start_pre_cluster_upgrade(controller, version,
                                             is_disruptive=is_disruptive, is_force=is_force)
    assert success == True, 'pre-cluster-upgrade failed to start! %s' % (return_msg)

    return _get_controller_latest_task_id(controller, version)


def start_pre_cluster_upgrade_ensure_failure(controller, version,
                                            is_disruptive=False, is_force=False):
    success, return_msg = start_pre_cluster_upgrade(controller, version,
                                             is_disruptive=is_disruptive, is_force=is_force)
    assert success == False, 'pre-cluster-upgrade started! %s' % (return_msg)

    return None


def start_post_cluster_upgrade_ensure_success(controller, version,
                                             is_disruptive=False, is_force=False):
    success, return_msg = start_post_cluster_upgrade(controller, version,
                                             is_disruptive=is_disruptive, is_force=is_force)
    assert success == True, 'post-cluster-upgrade failed to start! %s' % (return_msg)

    return _get_controller_latest_task_id(controller, version)


def start_post_cluster_upgrade_ensure_failure(controller, version,
                                            is_disruptive=False, is_force=False):
    success, return_msg = start_post_cluster_upgrade(controller, version,
                                             is_disruptive=is_disruptive, is_force=is_force)

    assert success == False, 'post-cluster-upgrade started! %s' % (return_msg)

    return None


def wait_controller_task(controller, task_id, timeout, raise_ssh_exception=True):
    """
    Wait for controller to finish task.

    @param controller: controller instance
    @param task_id: upgrade task ID
    @param timeout: timeout in seconds
    @param raise_ssh_exception: whether ssh exception should be raised or ignored, default raise
    @return: task outcomes: success or error, result message
    """
    import IDL.Protos.Extensions.Exception_pb2
    assert task_id, 'Invalid task ID: %s' % task_id
    dup_ip_check_cmd_failed = False
    for attempt in retry.retry(timeout=timeout, sleeptime=10):
        logging.info('Waiting for controller task %s, attempt count %d', task_id, attempt)
        if not controller.ipaddr:
            controller.wait_ipaddr()
        try:
            if dup_ip_check_cmd_failed == False:
                run_check_dupip_cmd(controller)
        except:
            # this is a common routine used by all tests however the command was introduced in a recent version
            # FeUpgradeFixedPathTestPlan.FeUpgradeFixedPathTest.test_released_VIB_reboot_handling deploys from
            # 3.x which does not contain this command hence ignore if we are not able to get the output
            # so we wont retry to execute this command if it failed atleast once
            dup_ip_check_cmd_failed = True

        try:
            task = _get_controller_task_by_id(controller, task_id)
            if task is not None and task['progress'] == 100:
                logging.info('%s task (%s) finished: %s %s', task['kind'], task['id'],
                             task['state'], task['description'])
                return task['state'], task['description']
        # Handle ssh disruption due to controller reboot or failover.
        except (subprocess.CalledProcessError,
                IDL.Protos.Extensions.Exception_pb2.DaExceptionConnectFailed):
            continue
        except ssh.SSHException:
            if not raise_ssh_exception:
                continue
            raise


def wait_hosts_upgrade(hosts, version):
    """
    Wait for hosts to finish upgrade by comparing with target version.

    @param hosts: list of host instances
    @param version: target version
    """
    for attempt in retry.retry(timeout=600, sleeptime=10):
        logging.info('Waiting for hosts upgrade, attempt count %d', attempt)
        for host in hosts:
            if get_host_version(host) != version:
                break
        else:
            break


def get_image_version(bin_file):
    """
    Get software version from image file.

    @param bin_file: image file path
    @return: software version
    """
    val = None
    with tarfile.open(bin_file, 'r') as tar:
        assert 'SPEC' in tar.getnames(), 'No SPEC in image file list: %s' % tar.getnames()
        f = tar.extractfile('SPEC')
        for l in f:
            if l.startswith('OSVersion'):
                val = l.split('=')[1].strip()
                break
        f.close()
    assert val, 'Cannot get version from image SPEC file'
    return val


def get_images_info(images, build_type='Debug'):
    """
    Get image version and file path.

    @param images: list of tuples of build top directory and whether it is future build
    @param build_type: 'Debug' or 'Release' build. Test case can pass in dva.buildtype.
    @return: a list of image information which contains its version and file path
    """
    info = []
    for (buildtop, is_future) in images:
        # FIXME(sachin): simplify this with an if and else
        path = os.path.join(buildtop, '../../OS/Build' + ('_999999' if is_future else ''),
                            'x86_64/da-os-%s.bin' % build_type)
        assert os.path.isfile(path), 'Image file not found: %s' % path
        ver = get_image_version(path)
        assert is_future == ('999999_abcdef' in ver), 'Image %s is_future %s' % (ver, is_future)
        info.append({'version': ver, 'path': path})
    return info


def _get_software_info(controller, is_refresh):
    """
    Run the given CLI command and return its json output verbatim.

    @param controller: controller instance
    @param is_refresh: use refresh flag or not
    @return: command output parsed into json structure
    """
    cmd = 'dvx software show --output-format=json'
    if is_refresh:
        cmd += ' --refresh'
    return yaml.load(controller.check_output(cmd))


def get_running_image(controller):
    """
    Get controller's running image.

    @param controller: controller instance
    @return: running image in json format
    """
    imgs = _get_software_info(controller, False)['softwareImages']
    running_imgs = [img for img in imgs if img['status'] == 'Running']
    assert len(running_imgs) == 1, 'Found %d running image(s) on %s' % (len(running_imgs),
                                                                        controller.ipaddr)
    return running_imgs[0]


def get_remote_images(controller, is_refresh):
    """
    Get list of remote images available on the Upgrade Center.

    @param controller: controller instance
    @param is_refresh: use refresh flag or not
    @return: list of remote images and remote image message
    """
    result = _get_software_info(controller, is_refresh)
    imgs = result['softwareImages']
    remote_message = result['remoteImageMsg']
    remote_images = [img for img in imgs if img['status'] == 'Remote']
    return remote_images, remote_message


def wait_for_this_image_to_show_on_ucenter(controller, version, timeout=300):
    deadline = time.time() + timeout
    while True:
        if time.time() > deadline:
            break

        remote_image_infos, _ = get_remote_images(controller, True)
        if len(remote_image_infos) == 0:
            continue

        remotely_available_versions = []
        for remote_image_info in remote_image_infos:
            remotely_available_versions.append(remote_image_info.get('version'))

        for remotely_available_version in remotely_available_versions:
            if version in remotely_available_version:
                logging.info('%s found in %s', version, remote_image_infos)
                return

    assert 0, 'Unable to find %s on remote images %s' % (version, remote_image_infos)


def remove_controller_image(controller, version):
    """
    Given a controller object find out where is pool passive and
    and removed the image corresponding to the version(arg)
    """
    pool_active, pool_passive = controller.HA_get_pool_roles()
    cmd = '/da/bin/plat_tool.py --remove-sw-image --sw-image-ver %s' % version
    pool_active.check_output(cmd)
    # Because upgradeMgr caching the local images, we need to run dvx software show --refresh.
    _get_software_info(pool_active, True)


def _get_process_id(ip, process):
    """
    Get the PID for the given process.

    @param ip: IP address
    @param process: process name
    @return: process id
    """
    p = '[' + process[:1] + ']' + process[1:]
    cmd = "ps x | grep '%s' | awk '{print $1}'" % p
    pid = ssh.check_output(ip, cmd).strip()
    logging.info('%s\'s pid is %s', process, pid)
    return None if not pid else int(pid)


def _kill_upgrade_mgr(controller):
    """
    Kill the UpgradeMgr process.

    @param controller: controller instance
    @return: exit code
    """
    # Make sure we operate on active controller.
    controller_ip = get_float_ip(controller, True)
    for attempt in retry.retry(timeout=600, sleeptime=60):
        logging.info('Getting UpgradeMgr process id, attempt count %d', attempt)
        pid = _get_process_id(controller_ip, 'UpgradeMgr')
        if pid:
            logging.info('Killing UpgradeMgr %s ...' % pid)
            return ssh.call(controller_ip, 'kill -9 %d' % pid)


def inject_upgrademgr_crash(controller):
    """
    Kill the UpgradeMgr process after some delay.
    Because dittos upgrade usually finishes in 15 minutes,
    the delay is randomly chosen in this range.

    @param controller: controller instance
    @return: None
    """
    delay = random.randint(1, 900)
    logging.info('Will kill UpgradeMgr in %d secs', delay)
    threading.Timer(delay, _kill_upgrade_mgr, [controller]).start()


def get_last_refresh_time(controller):
    """
    Get controller last software refresh time.

    @param controller: controller instance
    @return: last refresh time
    """
    return _get_software_info(controller, False)['lastRefreshTime']


def set_web_proxy(controller, proxy_server, proxy_port):
    """
    Set web proxy on the controller.
    Set the proxy through 'dev conf' instead of 'config web-proxy' because the latter validates the
    proxy settings before accepting. In our case, we need a negative test case with an invalid
    proxy server.

    @param controller: controller instance
    @param proxy_server: proxy server name
    @param proxy_port: proxy server port
    @return: None
    """
    controller.check_output('dev conf set ConfWebproxy.proxyServer=%s ConfWebproxy.proxyPort=%d' %
                            (proxy_server, proxy_port))


def unset_web_proxy(controller):
    """
    Unset the web proxy server setting on the controller.

    @param controller: controller instance
    @return: None
    """
    controller.check_output('config web-proxy unset')


def start_upgrade_check(controller, version):
    """
    Start upgrade check on the controller.

    @param controller: controller instance
    @param version: software version against which upgrade checks are performed
    @return: base timestamp, command output and upgrade check task ID
    """
    # Get the base timestamp just before the upgrade check.
    # Sleep one second to ensure upgrade check indeed happens later in the next second.
    base_time = controller.check_output('date +"%Y-%m-%dT%H:%M:%S"').rstrip()
    time.sleep(1)
    # Issue upgrade check command.
    output = controller.check_output('dvx software upgrade-check %s' % version)
    task_id = None
    if re.search('Upgrade check .*started', output):
        task_id = _get_controller_latest_task_id(controller, version)
    return base_time, output, task_id


def verify_upgrade_check_success_events(controller, base_time):
    """
    Verify controller events for successful upgrade check.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade check
    @return: upgrade check start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'UpgradeCheckStartEvent',
                                                   'UpgradeCheckSuccessEvent', base_time)

    # No failure events.
    logging.info('Verifying failure events')
    events = [e for e in
              _get_controller_events(controller,
                                     'UpgradeCheckInternalErrorEvent UpgradeCheckErrorDetailEvent',
                                     base_time, 0)
              if start_time < int(e['triggerTime']) < end_time]
    assert len(events) == 0, 'Upgrade failed with error codes: %s' % _get_events_error_codes(events)

    return start_time, end_time


def verify_upgrade_check_fail_error_events(controller, base_time, error_codes):
    """
    Verify controller events for failed upgrade check with errors.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade check
    @param error_codes: list of expected error codes
    @return: upgrade start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'UpgradeCheckStartEvent',
                                                   'UpgradeCheckFailEvent', base_time)

    # There are failure events.
    logging.info('Verifying failure events')
    event_error_codes = []
    for _ in retry.retry(timeout=300, sleeptime=5):
        events = [e for e in
                  _get_controller_events(controller,
                                         'UpgradeCheckInternalErrorEvent UpgradeCheckErrorDetailEvent',
                                         base_time, 1)
                  if int(e['triggerTime']) > start_time]

        # TODO(rtang):
        # There are duplicated host check errors because both controller and host are
        # running the same kind checks on host. After Lithium the number of events should match
        # exactly. For now, just remove duplicate event codes from the list.

        # assert sorted(_get_events_error_codes(events)) == sorted(error_codes), (
        event_error_codes = _get_events_error_codes(events)
        logging.info('Looking for %s in %s', error_codes, event_error_codes)
        if set(error_codes) <= set(event_error_codes):
            return start_time, end_time

        logging.error('Unable to find error code %s from %s in this iteration, will retry', error_codes, event_error_codes)


def verify_upgrade_check_fw_needed_events(controller, base_time):
    """
    Verify controller events for fw needed upgrade check.

    @param controller: controller instance
    @param base_time: the timestamp just before upgrade check
    @return: upgrade check start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(controller, 'UpgradeCheckStartEvent',
                                                   'UpgradeCheckSuccessEvent', base_time)

    # Look for FWUpgradeNeededEvent
    logging.info('Verifying FWUpgradeNeededEvent')
    events = [e for e in
              _get_controller_events(controller,
                                     'FWUpgradeNeededEvent',
                                     base_time, 0)
              if start_time < int(e['triggerTime']) < end_time]
    assert len(events) > 0, 'Failed to find FWUpgradeNeededEvent'

    return start_time, end_time


def _get_events_error_codes(events):
    """
    Get events value using the 'errorCode' key and 'stringVal' type.

    @param events: lis of event instances
    @returns: the list of associated values
    """
    return [int(get_event_value(event, 'errorCode', 'stringVal')) for event in events]


def wait_hosts_mount_point_writable(hosts, label):
    """
    Wait till host NFS mount point is mounted, accessible and writable.

    @param hosts: list of host instances
    @param label: mount point label
    @return: None
    """
    for _ in retry.retry(timeout=300, sleeptime=5):
        for host in hosts:
            if not host.is_mounted_and_writable(label):
                break
        else:
            break


def verify_upgrade_events_vc_reregister_fail(master_node, base_time):
    """
    Verify controller events when upgrade completed successful with
    VCenter plugin re-register failure event.

    @param master_node: Master controller node instance
    @param base_time: the timestamp just before upgrade
    @return: upgrade start and end time stamps
    """
    start_time, end_time = _verify_start_end_event(
        master_node, 'UpgradeStartEvent', 'UpgradeSuccessEvent', base_time)

    # There is a specific failure event.
    logging.info("Verifying VC plugin re-register failure event")
    # This event may show up between 2 to 50 mins after upgrade is completed.
    events = master_node.dva.wait_for_event(
        eventtype='VCenterPluginReregisterFailureEvent',
        fromTime=start_time / 10 ** 9, timeout=3000)
    assert len(events) == 1, (
        'Failed to verify VCenterPluginReregisterFailureEvent: %s' % events)
    return start_time, end_time


def get_all_datastores(controller):
    """
    Get all the datastores from controller.

    @param controller: controller instance
    @return: list available datastores' name in json format
    """
    cmd = 'datastores show --output-format=json'
    output = json.loads(controller.cli(cmd))
    return [ds['identifier'] for ds in output['status']]


def has_datastore(controller, datastore_name):
    """
    Check if the datastore exists on controller.

    @param controller: controller instance
    @param datastore_name: datastore name
    @return: True or False
    """
    return datastore_name in get_all_datastores(controller)


def create_datastores(controller, datastore_names):
    """
    Create datastore(s).

    @param controller: controller instance
    @param datastore_names: name of the datastores, such as DataStore1
    @return: None
    """
    assert isinstance(datastore_names, (tuple, list)), (
        "Expected type 'list' or 'tuple', got '%s' instead" % type(datastore_names).__name__)

    for ds in datastore_names:
        if not has_datastore(controller, ds):
            logging.info('Create datastore "%s"', ds)
            cmd = 'datastores create "%s"' % ds
            output = controller.cli(cmd)
            assert 'Datastore created' in output, 'Failed to create datastore %s' % ds
        else:
            logging.info('Datastore "%s" already exist', ds)


def delete_datastores(controller, datastore_names):
    """
    Delete datastore(s).

    @param controller: controller instance
    @param datastore_names: name of the datastores
    @return: None
    """
    assert isinstance(datastore_names, (tuple, list)), (
        "Expected type 'list' or 'tuple', got '%s' instead" % type(datastore_names).__name__)

    for ds in datastore_names:
        logging.info('Delete datastore "%s"', ds)
        if has_datastore(controller, ds):
            cmd = 'datastores delete "%s" --force --password %s' % (ds, controller.root_password)
            output = controller.cli(cmd)
            assert 'Datastore deleted' in output, 'Failed to delete datastore %s' % ds
        else:
            logging.info('Datastore "%s" does not exist', ds)


def disable_datastores(controller, datastore_names):
    """
    Disable datastore(s).

    @param controller: controller instance
    @param datastore_names: name of the datastores
    @return: None
    """
    assert isinstance(datastore_names, (tuple, list)), (
        "Expected type 'list' or 'tuple', got '%s' instead" % type(datastore_names).__name__)

    for ds in datastore_names:
        logging.info('Disable datastore "%s"', ds)
        if has_datastore(controller, ds):
            cmd = 'datastores disable --force "%s"' % ds
            output = controller.cli(cmd)
            assert 'Datastore disabled' in output, 'Failed to disable datastore %s' % ds
        else:
            logging.info('Datastore "%s" does not exist', ds)


def get_drive_state(controller):
    """
    Get controller disk drives state.

    @param controller: controller instance
    @return: drive state in dictionary format, {1 : 'ACTIVE', 2 : 'MISSING'}
    """
    pattern = r'DISK\.(node\d+)\.disk(\d+)'
    cmd = '/da/bin/plat_client.py --storage --list-disk'
    output = controller.check_output(cmd)
    drives_state = {}
    node_name = controller.node_name
    for line in output.split('\n'):
        m = re.match(pattern, line)
        # extract drive states corresponding to the controller(node).
        if m and node_name == m.group(1):
            drives_state[int(m.group(2))] = line.split()[1]

    logging.debug('Drive states: %s', drives_state)
    return drives_state


def is_drive_attached(controller, slot_num):
    """
    Is the disk drive at slot number attached.

    @param controller: controller instance
    @param slot_num: slot number
    @return: True or False
    """
    drives_state = get_drive_state(controller)
    return drives_state.get(slot_num) == 'ACTIVE'


def detach_drive(controller, slot_num):
    """
    Softly detach a drive, used to simulate physical ejection.

    @param controller: controller instance
    @param slot_num: drive slot number, e.g. 1
    @return: SCSI ID of the detached drive.
    """
    cmd = '/da/bin/plat_client.py --storage --detach-drive disk%02d'
    output = controller.check_output(cmd % slot_num)
    assert is_drive_attached(controller, slot_num) is False, (
            'Failed to detach drive at slot %02d' % slot_num)
    return output.strip()


def reduce_prepare_timeout(controller, master_timeout=1530, agent_timeout=1500):
    """
    Reduce prepare timeout for virtual controller.
    Since it does not need to do firmware upgrade.

    :param controller: controller instance
    :return: None
    """
    # Virtual controller does not need to do firmware upgrade.
    # Change the timeout so that in case of failure test time can be shortened.
    if isinstance(controller, TestBeds.hosttypes.VirtualControllerNode):
        master_conf_string = 'ConfMasterSvr.timeoutAgentsPrepare=%s' % master_timeout
        agent_conf_string = 'ConfAgentSvr.timeoutPrepare=%s' % agent_timeout
        set_dvx_conf(controller, master_conf_string, 'UpgradeMgr')
        set_dvx_conf(controller, agent_conf_string, 'UpgradeMgr')

def set_download_timeout(controller, master_timeout=930, agent_timeout=900):
    """
    Reduce download timeout for UpgradeMgr(manager) and UpgradeMgr(agent)

    :param controller: controller instance
    :return: None
    """
    # Virtual controller does not need to do firmware upgrade.
    # Change the timeout so that in case of failure test time can be shortened.
    if isinstance(controller, TestBeds.hosttypes.VirtualControllerNode):
        master_conf_string = 'ConfMasterSvr.timeoutAgentsDownload=%s' % master_timeout
        agent_conf_string = 'ConfAgentSvr.timeoutDownload=%s' % agent_timeout
        set_dvx_conf(controller, master_conf_string, 'UpgradeMgr')
        set_dvx_conf(controller, agent_conf_string, 'UpgradeMgr')


def disable_upgrade_stress_counters(dva):
    '''
    '''
    # Disable stress counter.
    set_dvx_conf(dva.master, 'ConfStressCounter.enabled=false', 'UpgradeMgr')
    set_dvx_conf(dva.master, 'ConfStressCounter.upgradeMgrFailHAMgrFailUp=0',
                                  'UpgradeMgr')

def enable_upgrade_stress_counters(dva):
    '''
    FIXME(sachin): rename this to enable_upgrade_rollback_stress
    '''
    # Enable stress counter to trigger upgrade rollback.
    set_dvx_conf(dva.master, 'ConfStressCounter.enabled=true', 'UpgradeMgr')
    set_dvx_conf(dva.master, 'ConfStressCounter.upgradeMgrFailHAMgrFailUp=1',
                                  'UpgradeMgr')

def upgrade_and_perform_checks(dva, upgrade_version, expected_version, expect_failure=False):
    '''
    '''
    base_time, _, task_id = start_upgrade(dva.master, False, False,
                                          upgrade_version)
    result, msg = wait_controller_task(dva.master, task_id, 6000, False)
    if expect_failure:
        assert result == 'Error', 'Upgrade task did not fail: %s' % msg
    else:
        assert result == 'Success', 'Upgrade task failed: %s' % msg

    perform_post_upgrade_checks(dva, expected_version, base_time, expect_failure)

def perform_post_upgrade_checks(dva, expected_version, base_time, expect_failure=False):
    '''
    '''
    filename = 'testfile.txt'
    content = 'helloworld ABCDEFG 123456 !@#$%^'
    # Controller should not be upgraded.
    verify_controller_version(dva.master, expected_version)
    verify_controller_synced(dva.master)
    if expect_failure:
        start, end = verify_upgrade_events_rollback(dva.master, base_time)
        num_events = len(dva.frontends) * 2
    else:
        start, end = verify_upgrade_events(dva.master, base_time)
        num_events = len(dva.frontends)
    # Hosts should be upgraded and then rolled back.
    verify_hosts_version(dva.frontends, expected_version)
    host_vol_labels = server_plat_test_lib.get_volume_labels(dva.frontends)
    server_plat_test_lib.verify_hosts_mountpoint(host_vol_labels, filename, content)
    # Two HostUpgradeStartEvent events should be generated.
    # One from version 0 to version 1, the other from version 1 to version 0.
    verify_host_events(dva.master, num_events, start, end)

def component_down_during_upgrade(dva, misaligned_component):
    '''
    Bring down a component before or during upgrade
    @param dva: dva instance
    @param misaligned_component: component to fail controller | node | datastore | pool
    '''

    # Selcet the node on which failure is to be introduced
    node = random.choice(dva.controllers)

    # fail a component in the node
    # if misaligned_component == 'controller':
    #     nplus1_test_lib.disrupt_controller(random.choice(node.peers), disruption_type='poweroff')
    if misaligned_component == 'node':
        assert len(dva.controllers) >= 3, 'number of nodes is less than 3'
        assert nplus1_test_lib.is_nplus1_enabled(dva), 'nplus1 is not enabled'
        fail_controller = async.Async()
        for controller in node.peers:
            fail_controller.task(nplus1_test_lib.disrupt_controller, controller,
                                 disruption_type='poweroff')
        fail_controller.joinAll()
    else:
        assert(0)

def misalign_a_component(dva, controller_name, misaligned_component, pool_ds_on_same_ctrl):
    '''
    Misalign a node or a component in the node
    @param dva: dva instance
    @param controller_name: controller on which components are to be aligned
    @param misaligned_component: component to align datastore | pool
    @param pool_ds_on_same_ctrl: pool and datastore to be on same controller True | False
    '''
    if misaligned_component == 'pool_ds':
        controller_with_pool_and_ds_active(dva, controller_name, pool_ds_on_same_ctrl)
    elif misaligned_component == 'datastore':
        controller_with_ds_active(dva, controller_name)
    elif misaligned_component == 'controller':
        controller_with_role_active(dva, controller_name)
    else:
        assert(0)

def controller_with_ds_active(dva, controller_name):
    '''
    Make a controller both datastore and pool active
    @param node: node on which need we need to perform
    '''
    for node in dva.controllers:
        logging.info('=== Wait for %s to be in redundant state ===', node.node_name)
        nplus1_test_lib.wait_for_ha_state(dva, node.node_name)
        ds_active, ds_passive = node.HA_get_ds_roles()
        if ds_passive.controller_id == controller_name:
            logging.info('making :: %s datastore active', ds_passive.controller_id)
            node.datastore_failover()
            node.HA_wait_for_synced()
            ds_active, ds_passive = node.HA_get_ds_roles()
            assert controller_name == ds_active.controller_id, (
                                '%s is not ds active' % ds_active.controller_id)
            logging.info('%s is :: datastore active', ds_active.controller_id)
            break

def controller_with_role_active(dva, controller_name):
    '''
    Make a controller active
    @param dva: dva instance
    @param controller_name: name of the controller to have role active
    '''
    logging.info('make all :: %s in the cluster active', controller_name)
    for node in dva.controllers:
        logging.info('=== Wait for %s to be in redundant state ===', node.node_name)
        nplus1_test_lib.wait_for_ha_state(dva, node.node_name)
        active, passive = node.HA_get_roles()
        if not active.controller_id.endswith(controller_name):
            logging.info('making :: %s active', passive.controller_id)
            node.active.controller_failover()
            node.HA_wait_for_synced()
        active, _ = node.HA_get_roles()
        assert active.controller_id.endswith(controller_name), (
                                '%s is not active' % controller_name)
        logging.info('%s is :: active', active.controller_id)

def get_controller_object_on_this_number_on_this_node(node, controller_name):
    """
    Given a node object return peers[0] if asked is controller1 else peers[1]

    This is for tests which want to do something on N?C1 or N?C2
    """

    assert controller_name == 'controller1' or controller_name == 'controller2'
    if controller_name == 'controller1':
        return node.peers[0]
    return node.peers[1]

def get_platform_settings(controller):
    """
    Given a controller object return platform settings to caller
    """
    cmd = 'plat_tool.py --print-settings 2>/dev/null'
    stdout = controller.check_output(cmd)
    match = re.search('Settings\((\{.*\})\)', stdout)
    assert match, 'unable to get platform settings %s' % stdout
    settings_dict = eval(match.group(1))
    return settings_dict

def controller_with_pool_and_ds_active(dva, controller_name, pool_ds_on_same_controller):
    '''
    Make a controller both datastore and pool active
    @param node: node on which need we need to perform
    '''
    if pool_ds_on_same_controller:
        assert controller_name, 'missing controller name'
        for node in dva.controllers:
            logging.info('=== Wait for %s to be in redundant state ===', node.node_name)
            nplus1_test_lib.wait_for_ha_state(dva, node.node_name)
            pool_active, pool_passive = node.HA_get_pool_roles()
            ds_active, ds_passive = node.HA_get_ds_roles()
            if not pool_active.controller_id.endswith(controller_name):
                logging.info('making :: %s pool active', pool_passive.controller_id)
                node.pool_failover()
                node.HA_wait_for_synced()
                pool_active, pool_passive = node.HA_get_pool_roles()
                assert pool_active.controller_id.endswith(controller_name), (
                                '%s is not pool active' % pool_active.controller_id)
                logging.info('%s is :: pool active', pool_active.controller_id)
            if not ds_active.controller_id.endswith(controller_name):
                logging.info('making :: %s datastore active', ds_passive.controller_id)
                node.datastore_failover()
                node.HA_wait_for_synced()
                ds_active, ds_passive = node.HA_get_ds_roles()
                assert ds_active.controller_id.endswith(controller_name), (
                                '%s is not datastore active' % ds_active.controller_id)
                logging.info('%s is :: datastore active', ds_active.controller_id)
    else:
        for node in dva.controllers:
            logging.info('=== Wait for %s to be in redundant state ===', node.node_name)
            nplus1_test_lib.wait_for_ha_state(dva, node.node_name)
            pool_active, pool_passive = node.HA_get_pool_roles()
            ds_active, ds_passive = node.HA_get_ds_roles()
            if pool_active.controller_id == ds_active.controller_id:
                logging.info('making :: %s datastore active', ds_passive.controller_id)
                node.datastore_failover()
                node.HA_wait_for_synced()
            ds_active, ds_passive = node.HA_get_ds_roles()
            assert pool_active.controller_id != ds_active.controller_id, (
                            '%s is both pool and ds active' % pool_active.controller_id)
            logging.info('pool active controller :: %s', pool_active.controller_id)
            logging.info('datastore active controller :: %s', ds_active.controller_id)

def wait_for_check_point(controller, task_id, check_point, timeout=1200, sleep_time=30, allow_go_past_cp=False):
    '''
    '''
    for _ in retry.retry(timeout=timeout, sleeptime=sleep_time):
        logging.info('querying task id %s', task_id)
        t = None
        try:
            t = _get_controller_task_by_id(controller, task_id)
        except:
            logging.info('UpgradeMgr is current unavailable, lets retry')
            continue

        assert t, 'no task found'
        assert t['state'] != 'Error', 'upgrade failed'
        if isinstance(check_point, str):
            progress = upgrade_check_point[check_point]
        else:
            progress = check_point
        if t['progress'] == progress:
            logging.info('got expected progress :: %d and checkpoint :: %s', progress, check_point)
            return
        if allow_go_past_cp and t['progress'] > progress:
            logging.info('got progress :: %d past checkpoint :: %s', progress, check_point)
            return
        logging.info('current progress :: %d, expected progress :: %d', t['progress'], progress)

def seperate_pool_and_datastore_actives(dva):
    '''
    Given a dva, separates pool and datastore actives from all controllers
    '''
    if len(dva.controllers) == 1:
        logging.info('DVX has less than 2 data nodes, can not separate pool and datastore actives')
        return

    for node in dva.controllers:
        logging.info('=== Wait for %s to be in redundant state ===', node.node_name)
        nplus1_test_lib.wait_for_ha_state(dva, node.node_name)
        pool_active, pool_passive = node.HA_get_pool_roles()
        ds_active, ds_passive = node.HA_get_ds_roles()
        if pool_active.controller_id == ds_active.controller_id:
            logging.info('making :: %s datastore active', ds_passive.controller_id)
            node.datastore_failover()
            node.HA_wait_for_synced()
        ds_active, ds_passive = node.HA_get_ds_roles()
        assert pool_active.controller_id != ds_active.controller_id, (
                        '%s is both pool and ds active' % pool_active.controller_id)
        logging.info('pool active controller :: %s', pool_active.controller_id)
        logging.info('datastore active controller :: %s', ds_active.controller_id)

def ensure_datastore_actives_are_on_unique_nodes(dva):
    dva.wait_for_ha_redundant()

    for node in dva.controllers:
        ds_active, ds_passive = node.HA_get_ds_roles()
        if ds_active.node_num != node.node_num:
            node.datastore_failover()
            # we wait for ha state below

    dva.wait_for_ha_redundant()

def merge_pool_and_datastore_actives(dva):
    '''
    Given a dva, merges pool and datastore actives on all controllers

    At this point there is a possibility that one of the node has 2
    datastore actives and 1 pool active. So in order to guarantee merge
    we need to cross check all datastore actives and ensure they are
    on different nodes and then merge pool with the same top or bottom
    wherever it is running
    '''
    if len(dva.controllers) == 1:
        logging.info('Not supported for a single node DVX')
        return

    dva.wait_for_ha_redundant()
    # ensure there is at most one datastore active on each node
    ensure_datastore_actives_are_on_unique_nodes(dva)

    for node in dva.controllers:
        pool_active, pool_passive = node.HA_get_pool_roles()
        ds_active, ds_passive = node.HA_get_ds_roles()

        if pool_active.controller_id != ds_active.controller_id:
            node.pool_failover()

    dva.wait_for_ha_redundant()

    # at this point each node should have at-most one datastore active
    # (it does not matter whether top or bottom) and pool active must be
    # on the same controller, lets assert that before returning
    for node in dva.controllers:
        pool_active, pool_passive = node.HA_get_pool_roles()
        ds_active, ds_passive = node.HA_get_ds_roles()
        assert pool_active.controller_id == ds_active.controller_id, (
                        '%s is not both pool and ds active' % pool_active.controller_id)
        assert pool_active.node_num == node.node_num, (
                        'Node number mismatch between pool active and node! %s %s'
                        % (pool_active.node_num, node.node_num))
        assert ds_active.node_num == node.node_num, (
                        'Node number mismatch between ds active and node! %s %s'
                        % (ds_active.node_num, node.node_num))

def align_carbon_controllers_for_upgrade(dva):
    '''
    When we upgrade from Carbon to Nitrogen all bottom controllers will be active
    '''
    logging.info('Aligning the controllers for upgrade')

    expected_controller_name = 'controller2'

    dva.wait_for_ha_redundant()

    for node in dva.controllers:
        active, passive = node.HA_get_roles()
        if not active.controller_id.endswith(expected_controller_name):
            assert passive.controller_id.endswith(expected_controller_name), (
                "expected passive controller to be %s its not %s" % (
                expected_controller_name, passive.controller_id))
            node.active.controller_failover()

    dva.wait_for_ha_redundant()

    # lets verify what we wanted is done
    for node in dva.controllers:
        active, _ = node.HA_get_roles()
        assert active.controller_id.endswith(expected_controller_name), (
            'Expected active to be on %s its not %s' % (
            expected_controller_name, active.controller_id))

    logging.info('Aligned the controllers for upgrade')

def is_atleast_one_controller_misaligned_for_upgrade_from_carbon(dva):
    logging.info('Checking if all controllers are aligned for carbon to nitrogen upgrade')
    aligned_controller_name = 'controller2'

    dva.wait_for_ha_redundant()
    for node in dva.controllers:
        active, _ = node.HA_get_roles()
        if not active.controller_id.endswith(aligned_controller_name):
            logging.info('node name %s is misaligned hence returning True, controller: %s',
                         node.node_name, active.controller_id)
            return True

    logging.info('All controllers are aligned for upgrade from carbon to nitrogen')
    return False

def random_misalign_carbon_controllers_for_upgrade(dva):
    # lets first align before misaligning
    align_carbon_controllers_for_upgrade(dva)
    aligned_controller_name = 'controller2'

    dva.wait_for_ha_redundant()
    for node in dva.controllers:
        active, _ = node.HA_get_roles()
        if active.controller_id.endswith(aligned_controller_name):
            if random.choice([0, 1]) == 1:
                logging.info('Issuing a failover on %s', active.controller_id)
                node.active.controller_failover()

    dva.wait_for_ha_redundant()
    if is_atleast_one_controller_misaligned_for_upgrade_from_carbon(dva):
        return

    logging.info('randomization did not misalign controllers from carbon to nitrogen upgrade')
    random_node = random.choice(dva.controllers)
    active, _ = random_node.HA_get_roles()
    assert active.controller_id.endswith(aligned_controller_name), (
        'node %s is misaligned is_atleast_one_controller_misaligned_for_upgrade_from_carbon '
        'messed up. active %s expected %s' % (
        random_node.node_name, active.controller_id, aligned_controller_name))
    random_node.active.controller_failover()

    dva.wait_for_ha_redundant()

    assert is_atleast_one_controller_misaligned_for_upgrade_from_carbon(dva), (
        'Unable to misalign controllers for carbon to nitrogen upgrade')

def is_nitrogen_running(dva):
    '''
    A helper to find out if the current running version is nitrogen build or higher
    '''
    running_version = get_controller_version(dva.controllers[0])
    major, minor, maintenance, _, _, _, _ = software_version_lib.parse_version_string(running_version)

    if major < 5:
        return False

    if minor < 1:
        return False

    return True

def restart_upgrade_agent_on_all_nodes(dva):
    cmd = 'procmgr_cli.py kill -f UpgradeMgr'
    controller_to_issue_cmd_on = []
    if is_nitrogen_running(dva) == False:
        for node in dva.controllers:
            active, _ = node.HA_get_roles()
            controller_to_issue_cmd_on.append(active)
    else:
        for node in dva.controllers:
            pool_active, _ = node.HA_get_pool_roles()
            controller_to_issue_cmd_on.append(pool_active)

    for controller in controller_to_issue_cmd_on:
        controller.check_output(cmd)

def failover_active_on_all_nodes(dva):
    dva.wait_for_ha_redundant()
    for node in dva.controllers:
        logging.info('Issuing a controller failover on node %s', node.node_num)
        node.active.controller_failover()
    dva.wait_for_ha_redundant()

def choose_a_random_misalignment(dva):
    '''
    Given a dva, for all nodes, randomly issues pool failover and or datastore failover
    If carbon build issues failover on atleast one controller
    '''
    if is_nitrogen_running(dva) == False:
        random_misalign_carbon_controllers_for_upgrade(dva)
        return

    failover_choices = ['issue_failover', 'do_not_issue_failover']

    # to guarantee there is a misalignment, we need to align first
    merge_pool_and_datastore_actives(dva)

    for node in dva.controllers:
        # nplus1_test_lib.wait_for_ha_state(dva, node.node_name)
        # lets try without this and see if something blows up
        # given all operations below are independent operations
        # we need not wait for ha state before issuing failover
        if random.choice(failover_choices) == 'issue_failover':
            logging.info('Issuing pool failover to node %s', node.node_num)
            node.pool_failover()
        else:
            logging.info('Not issuing pool failover to node %s', node.node_num)

        if random.choice(failover_choices) == 'issue_failover':
            logging.info('Issuing datastore failover to node %s', node.node_num)
            node.datastore_failover()
        else:
            logging.info('Not issuing pool failover to node %s', node.node_num)

        # lets not wait for ha state until all randomized failovers are complete

    dva.wait_for_ha_redundant()
