"""
config
==================

"""


#############################################################################
#  Copyright (C) 2020                                                       #
#                Maximilian Jaroschek (maximilian@mjaroschek.com),          #
#                                                                           #
#  Distributed under the terms of the GNU General Public License (GPL)      #
#  either version 2, or (at your option) any later version                  #
#                                                                           #
#  http://www.gnu.org/licenses/                                             #
#############################################################################

global_systype='d'
global_systype_warning=True
systype_d=['diff','d']
systype_ad=['adj_diff','ad']
systype_s=['shift','s']
systype_as=['adj_shift','as']
systype_error_string="Specify valid system type: " + repr(systype_d[0]) + " for differential systems, " + repr(systype_s[0]) + " for difference systems."

def systype_fallback():
    r"""
    Return a valid systype and possibly print a warning message. Raises an error
    if no valid global systype is set.

    Output:
        - The global systype.

    Algorithm:
        - none
    """
    if global_systype==None or not (global_systype in systype_d or global_systype in systype_s):
        raise ValueError(systype_error_string)
    if global_systype_warning:
        print(r"Interpreting as default type: " + repr(global_systype))
    return global_systype

def set_global_systype(systype,warning=True):
    systype=systype.lower()
    if systype in systype_d:
        print(r"All systems will now be interpretet as differential systems.")
    elif systype in systype_s:
        print(r"All systems will now be interpretet as difference systems.")
    else:
        raise ValueError(systype_error_string)
    global global_systype
    global global_systype_warning
    global_systype=systype
    global_systype_warning=warning
