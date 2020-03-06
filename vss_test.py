##############################################################
# Copyright (c) 2016-2020 Datrium, Inc. All rights reserved. #
#                -- Datrium Confidential --                  #
##############################################################

import argparse
import os
import subprocess
import urllib
import ssl

# Tests VSS setup executable

def test_setup(netshelf, password):
    print "Downloading installer"

    installer_urls = [
            ('http://git.datrium.com/gitweb/?p=ToolsAndLibs/WinX64ToWinX64.git;a=blob;f=datrium-guest-agents/Datrium-VSS-Provider-1.1.0.0.msi;h=f41baab70a2f7e4f46e2bc088affb6c7b3291a84;hb=refs/heads/master', 'Datrium-VSS-Provider-1.1.0.0.msi'),
            ('http://git.datrium.com/gitweb/?p=ToolsAndLibs/WinX64ToWinX64.git;a=blob;f=datrium-guest-agents/Datrium-VSS-Provider-1.2.0.0.msi;h=3939e1e062f84deac96178ae6ecdc6b1895ca922;hb=refs/heads/master', 'Datrium-VSS-Provider-1.2.0.0.msi'),
            ('http://git.datrium.com/gitweb/?p=ToolsAndLibs/WinX64ToWinX64.git;a=blob;f=datrium-guest-agents/Datrium-VSS-Provider-1.3.0.0.msi;h=cc46f0f83ae8a669f77b63df80aa8c0543a3a112;hb=refs/heads/master', 'Datrium-VSS-Provider-1.3.0.0.msi'),
            ('http://git.datrium.com/gitweb/?p=ToolsAndLibs/WinX64ToWinX64.git;a=blob;f=datrium-guest-agents/Datrium-VSS-Provider-1.4.0.0.msi;h=164b42cb2aa1506d93644f612c25c96846999fb1;hb=refs/heads/master', 'Datrium-VSS-Provider-1.4.0.0.msi'),
            ('http://git.datrium.com/gitweb/?p=ToolsAndLibs/WinX64ToWinX64.git;a=blob;f=datrium-guest-agents/Datrium-VSS-Provider-1.5.0.0.msi;h=2002665ed36bd17d51de179a8e63b28b98c16236;hb=refs/heads/master', 'Datrium-VSS-Provider-1.5.0.0.msi'),
            ('http://git.datrium.com/gitweb/?p=ToolsAndLibs/WinX64ToWinX64.git;a=blob;f=datrium-guest-agents/Datrium-VSS-Provider-1.6.0.0.msi;h=6aea565e4d2700fea2f6550d9b836f8008493a70;hb=refs/heads/master', 'Datrium-VSS-Provider-1.6.0.0.msi')
            ]

    # download all versions of vss provider installers
    for url, installer in installer_urls:
        urllib.urlretrieve(url, installer, context=ssl._create_unverified_context())

    # download current versions of vss provider installer
    urllib.urlretrieve("https://%s/static/Datrium-VSS-Provider-1.7.0.0.msi" % netshelf,
                       "Datrium-VSS-Provider-1.7.0.0.msi",
                       context=ssl._create_unverified_context())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-n', '--netshelf', type=str, required=True)
    parser.add_argument('-p', '--password', type=str, required=True)

    args = parser.parse_args()
    test_setup(args.netshelf, args.password)
