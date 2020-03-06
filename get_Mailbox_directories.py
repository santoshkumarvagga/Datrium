##############################################################
# Copyright (c) 2018-2020 Datrium, Inc. All rights reserved. #
#                -- Datrium Confidential --                  #
##############################################################

"""This module gets all the mailbox directories other than "address" folder since no need to check for log truncation in that folder"""
import os
import re
import sys
dirs=os.listdir("C:\Program Files\Microsoft\Exchange Server\V15\Mailbox")
reg_obj = re.compile('^address$') #exclude this folder for log truncation check
not_required_db = []  #used to filter out "address" folder
only_db = []          #gets name of databases other than "address" folder
for i in dirs:
    mat_obj = reg_obj.findall(i)
    if len(mat_obj) > 0:
            not_required_db.append(mat_obj[0])
            for j in dirs:
                if j in not_required_db:
                    pass
                else:
                    only_db.append(j)
length = len(only_db)
count = 1
for i in only_db:
    sys.stdout.write(i)
    if count < length:
        sys.stdout.write(',')
    count = count + 1
