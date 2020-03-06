##############################################################
# Copyright (c) 2018-2020 Datrium, Inc. All rights reserved. #
#                -- Datrium Confidential --                  #
##############################################################

"""This module generates mail logs in a specified mailbox database by sending e-mails to that user, the number of e-mails sent can be varied"""
import smtplib,sys,random,string,time
def send_mails(mail_id):
    TO = mail_id
    SUBJECT = 'TEST MAIL'
    TEXT = ''.join([random.choice(string.ascii_letters + string.digits) for n in xrange(1000000)]) #will send 976KB string per mail

    # exchange Sign In
    exchange_sender = mail_id

    server = smtplib.SMTP("localhost")

    BODY = '\n'.join(['To: %s' % TO,
                        'From: %s' % exchange_sender,
                        'Subject: %s' % SUBJECT,
                        '', TEXT])
    print "Started Generating logs."
    for i in range(0,300): #will send 300 e-mails
        try:
            server.sendmail(exchange_sender, [TO], BODY)
            print 'email sent'
        except:
            print("error sending mail")
    print 'Finished generating logs.'
acc_id = sys.argv[1]
send_mails(acc_id)
