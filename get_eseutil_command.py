##############################################################
# Copyright (c) 2018-2020 Datrium, Inc. All rights reserved. #
#                -- Datrium Confidential --                  #
##############################################################

"""This module fetches the pattern string to list all the files matching that pattern in the specified mailbox directory"""
import os
import sys
files = os.listdir(sys.argv[1])
for f in files:
    if f.endswith('.log'): #consider only LOG files
        E_id = f[:3]       #fetch the starting first 3 letters in LOG file name like E00, E01, etc to give as a input parameter to eseutil list files command
        temp_cmd = "eseutil /ml {}"
        eseutil_cmd = temp_cmd.format(E_id)
        break
sys.stdout.write(eseutil_cmd)
