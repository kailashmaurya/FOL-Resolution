import os
import time

for i in xrange(1,17):
    os.system('copy /Y .\cases\input{0}.txt .\input.txt'.format(i))
    print("-->On test case #{0}<--".format(i))
    start_time = time.time()
    os.system('python Resolution.py')
    print("Runing time: {0}ms".format(int((time.time() - start_time) * 1000)))
    os.system('FC .\output.txt .\cases\output{0}.txt'.format(i))
    os.system('copy /Y .\output.txt .\cases\Your_output{0}.txt'.format(i))
    os.system('del .\output.txt')