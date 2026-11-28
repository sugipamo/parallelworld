import os
import sys

# pwt: the tests' own way of asking the pw executable (pw kernel, pw lean) for one operation at a time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
