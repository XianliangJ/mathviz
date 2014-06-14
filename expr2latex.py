# SELF-CONTAINED VERSION ready for conversion to js

# expr2latex
#   converts a math formula written in MATLAB-like syntax into LaTeX syntax
#
# Created on 2009-08-04 by Philip Guo


### BEGIN inlined_ply/lex.py

# -----------------------------------------------------------------------------
# ply: lex.py
#
# Copyright (C) 2001-2011,
# David M. Beazley (Dabeaz LLC)
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
# 
# * Redistributions of source code must retain the above copyright notice,
#   this list of conditions and the following disclaimer.  
# * Redistributions in binary form must reproduce the above copyright notice, 
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.  
# * Neither the name of the David Beazley or Dabeaz LLC may be used to
#   endorse or promote products derived from this software without
#  specific prior written permission. 
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
# -----------------------------------------------------------------------------

__version__    = "3.4"
__tabversion__ = "3.2"       # Version of table file used

import re, sys, types, copy, os

# This tuple contains known string types
try:
    # Python 2.6
    StringTypes = (types.StringType, types.UnicodeType)
except AttributeError:
    # Python 3.0
    StringTypes = (str, bytes)

# Extract the code attribute of a function. Different implementations
# are for Python 2/3 compatibility.

if sys.version_info[0] < 3:
    def func_code(f):
        return f.func_code
else:
    def func_code(f):
        return f.__code__

# This regular expression is used to match valid token names
_is_identifier = re.compile(r'^[a-zA-Z0-9_]+$')

# Exception thrown when invalid token encountered and no default error
# handler is defined.

class LexError(Exception):
    def __init__(self,message,s):
         self.args = (message,)
         self.text = s

# Token class.  This class is used to represent the tokens produced.
class LexToken(object):
    def __str__(self):
        return "LexToken(%s,%r,%d,%d)" % (self.type,self.value,self.lineno,self.lexpos)
    def __repr__(self):
        return str(self)

# This object is a stand-in for a logging object created by the 
# logging module.  

class PlyLogger(object):
    def __init__(self,f):
        self.f = f
    def critical(self,msg,*args,**kwargs):
        self.f.write((msg % args) + "\n")

    def warning(self,msg,*args,**kwargs):
        self.f.write("WARNING: "+ (msg % args) + "\n")

    def error(self,msg,*args,**kwargs):
        self.f.write("ERROR: " + (msg % args) + "\n")

    info = critical
    debug = critical

# Null logger is used when no output is generated. Does nothing.
class NullLogger(object):
    def __getattribute__(self,name):
        return self
    def __call__(self,*args,**kwargs):
        return self

# -----------------------------------------------------------------------------
#                        === Lexing Engine ===
#
# The following Lexer class implements the lexer runtime.   There are only
# a few public methods and attributes:
#
#    input()          -  Store a new string in the lexer
#    token()          -  Get the next token
#    clone()          -  Clone the lexer
#
#    lineno           -  Current line number
#    lexpos           -  Current position in the input string
# -----------------------------------------------------------------------------

class Lexer:
    def __init__(self):
        self.lexre = None             # Master regular expression. This is a list of
                                      # tuples (re,findex) where re is a compiled
                                      # regular expression and findex is a list
                                      # mapping regex group numbers to rules
        self.lexretext = None         # Current regular expression strings
        self.lexstatere = {}          # Dictionary mapping lexer states to master regexs
        self.lexstateretext = {}      # Dictionary mapping lexer states to regex strings
        self.lexstaterenames = {}     # Dictionary mapping lexer states to symbol names
        self.lexstate = "INITIAL"     # Current lexer state
        self.lexstatestack = []       # Stack of lexer states
        self.lexstateinfo = None      # State information
        self.lexstateignore = {}      # Dictionary of ignored characters for each state
        self.lexstateerrorf = {}      # Dictionary of error functions for each state
        self.lexreflags = 0           # Optional re compile flags
        self.lexdata = None           # Actual input data (as a string)
        self.lexpos = 0               # Current position in input text
        self.lexlen = 0               # Length of the input text
        self.lexerrorf = None         # Error rule (if any)
        self.lextokens = None         # List of valid tokens
        self.lexignore = ""           # Ignored characters
        self.lexliterals = ""         # Literal characters that can be passed through
        self.lexmodule = None         # Module
        self.lineno = 1               # Current line number
        self.lexoptimize = 0          # Optimized mode

    def clone(self,object=None):
        c = copy.copy(self)

        # If the object parameter has been supplied, it means we are attaching the
        # lexer to a new object.  In this case, we have to rebind all methods in
        # the lexstatere and lexstateerrorf tables.

        if object:
            newtab = { }
            for key, ritem in self.lexstatere.items():
                newre = []
                for cre, findex in ritem:
                     newfindex = []
                     for f in findex:
                         if not f or not f[0]:
                             newfindex.append(f)
                             continue
                         newfindex.append((getattr(object,f[0].__name__),f[1]))
                newre.append((cre,newfindex))
                newtab[key] = newre
            c.lexstatere = newtab
            c.lexstateerrorf = { }
            for key, ef in self.lexstateerrorf.items():
                c.lexstateerrorf[key] = getattr(object,ef.__name__)
            c.lexmodule = object
        return c

    # ------------------------------------------------------------
    # writetab() - Write lexer information to a table file
    # ------------------------------------------------------------
    def writetab(self,tabfile,outputdir=""):
        if isinstance(tabfile,types.ModuleType):
            return
        basetabfilename = tabfile.split(".")[-1]
        filename = os.path.join(outputdir,basetabfilename)+".py"
        tf = open(filename,"w")
        tf.write("# %s.py. This file automatically created by PLY (version %s). Don't edit!\n" % (tabfile,__version__))
        tf.write("_tabversion   = %s\n" % repr(__version__))
        tf.write("_lextokens    = %s\n" % repr(self.lextokens))
        tf.write("_lexreflags   = %s\n" % repr(self.lexreflags))
        tf.write("_lexliterals  = %s\n" % repr(self.lexliterals))
        tf.write("_lexstateinfo = %s\n" % repr(self.lexstateinfo))

        tabre = { }
        # Collect all functions in the initial state
        initial = self.lexstatere["INITIAL"]
        initialfuncs = []
        for part in initial:
            for f in part[1]:
                if f and f[0]:
                    initialfuncs.append(f)

        for key, lre in self.lexstatere.items():
             titem = []
             for i in range(len(lre)):
                  titem.append((self.lexstateretext[key][i],_funcs_to_names(lre[i][1],self.lexstaterenames[key][i])))
             tabre[key] = titem

        tf.write("_lexstatere   = %s\n" % repr(tabre))
        tf.write("_lexstateignore = %s\n" % repr(self.lexstateignore))

        taberr = { }
        for key, ef in self.lexstateerrorf.items():
             if ef:
                  taberr[key] = ef.__name__
             else:
                  taberr[key] = None
        tf.write("_lexstateerrorf = %s\n" % repr(taberr))
        tf.close()

    # ------------------------------------------------------------
    # readtab() - Read lexer information from a tab file
    # ------------------------------------------------------------
    def readtab(self,tabfile,fdict):
        if isinstance(tabfile,types.ModuleType):
            lextab = tabfile
        else:
            if sys.version_info[0] < 3:
                exec("import %s as lextab" % tabfile)
            else:
                env = { }
                exec("import %s as lextab" % tabfile, env,env)
                lextab = env['lextab']

        if getattr(lextab,"_tabversion","0.0") != __version__:
            raise ImportError("Inconsistent PLY version")

        self.lextokens      = lextab._lextokens
        self.lexreflags     = lextab._lexreflags
        self.lexliterals    = lextab._lexliterals
        self.lexstateinfo   = lextab._lexstateinfo
        self.lexstateignore = lextab._lexstateignore
        self.lexstatere     = { }
        self.lexstateretext = { }
        for key,lre in lextab._lexstatere.items():
             titem = []
             txtitem = []
             for i in range(len(lre)):
                  titem.append((re.compile(lre[i][0],lextab._lexreflags | re.VERBOSE),_names_to_funcs(lre[i][1],fdict)))
                  txtitem.append(lre[i][0])
             self.lexstatere[key] = titem
             self.lexstateretext[key] = txtitem
        self.lexstateerrorf = { }
        for key,ef in lextab._lexstateerrorf.items():
             self.lexstateerrorf[key] = fdict[ef]
        self.begin('INITIAL')

    # ------------------------------------------------------------
    # input() - Push a new string into the lexer
    # ------------------------------------------------------------
    def input(self,s):
        # Pull off the first character to see if s looks like a string
        c = s[:1]
        if not isinstance(c,StringTypes):
            raise ValueError("Expected a string")
        self.lexdata = s
        self.lexpos = 0
        self.lexlen = len(s)

    # ------------------------------------------------------------
    # begin() - Changes the lexing state
    # ------------------------------------------------------------
    def begin(self,state):
        if not state in self.lexstatere:
            raise ValueError("Undefined state")
        self.lexre = self.lexstatere[state]
        self.lexretext = self.lexstateretext[state]
        self.lexignore = self.lexstateignore.get(state,"")
        self.lexerrorf = self.lexstateerrorf.get(state,None)
        self.lexstate = state

    # ------------------------------------------------------------
    # push_state() - Changes the lexing state and saves old on stack
    # ------------------------------------------------------------
    def push_state(self,state):
        self.lexstatestack.append(self.lexstate)
        self.begin(state)

    # ------------------------------------------------------------
    # pop_state() - Restores the previous state
    # ------------------------------------------------------------
    def pop_state(self):
        self.begin(self.lexstatestack.pop())

    # ------------------------------------------------------------
    # current_state() - Returns the current lexing state
    # ------------------------------------------------------------
    def current_state(self):
        return self.lexstate

    # ------------------------------------------------------------
    # skip() - Skip ahead n characters
    # ------------------------------------------------------------
    def skip(self,n):
        self.lexpos += n

    # ------------------------------------------------------------
    # opttoken() - Return the next token from the Lexer
    #
    # Note: This function has been carefully implemented to be as fast
    # as possible.  Don't make changes unless you really know what
    # you are doing
    # ------------------------------------------------------------
    def token(self):
        # Make local copies of frequently referenced attributes
        lexpos    = self.lexpos
        lexlen    = self.lexlen
        lexignore = self.lexignore
        lexdata   = self.lexdata

        while lexpos < lexlen:
            # This code provides some short-circuit code for whitespace, tabs, and other ignored characters
            if lexdata[lexpos] in lexignore:
                lexpos += 1
                continue

            # Look for a regular expression match
            for lexre,lexindexfunc in self.lexre:
                m = lexre.match(lexdata,lexpos)
                if not m: continue

                # Create a token for return
                tok = LexToken()
                tok.value = m.group()
                tok.lineno = self.lineno
                tok.lexpos = lexpos

                i = m.lastindex
                func,tok.type = lexindexfunc[i]

                if not func:
                   # If no token type was set, it's an ignored token
                   if tok.type:
                      self.lexpos = m.end()
                      return tok
                   else:
                      lexpos = m.end()
                      break

                lexpos = m.end()

                # If token is processed by a function, call it

                tok.lexer = self      # Set additional attributes useful in token rules
                self.lexmatch = m
                self.lexpos = lexpos

                newtok = func(tok)

                # Every function must return a token, if nothing, we just move to next token
                if not newtok:
                    lexpos    = self.lexpos         # This is here in case user has updated lexpos.
                    lexignore = self.lexignore      # This is here in case there was a state change
                    break

                # Verify type of the token.  If not in the token map, raise an error
                if not self.lexoptimize:
                    if not newtok.type in self.lextokens:
                        raise LexError("%s:%d: Rule '%s' returned an unknown token type '%s'" % (
                            func_code(func).co_filename, func_code(func).co_firstlineno,
                            func.__name__, newtok.type),lexdata[lexpos:])

                return newtok
            else:
                # No match, see if in literals
                if lexdata[lexpos] in self.lexliterals:
                    tok = LexToken()
                    tok.value = lexdata[lexpos]
                    tok.lineno = self.lineno
                    tok.type = tok.value
                    tok.lexpos = lexpos
                    self.lexpos = lexpos + 1
                    return tok

                # No match. Call t_error() if defined.
                if self.lexerrorf:
                    tok = LexToken()
                    tok.value = self.lexdata[lexpos:]
                    tok.lineno = self.lineno
                    tok.type = "error"
                    tok.lexer = self
                    tok.lexpos = lexpos
                    self.lexpos = lexpos
                    newtok = self.lexerrorf(tok)
                    if lexpos == self.lexpos:
                        # Error method didn't change text position at all. This is an error.
                        raise LexError("Scanning error. Illegal character '%s'" % (lexdata[lexpos]), lexdata[lexpos:])
                    lexpos = self.lexpos
                    if not newtok: continue
                    return newtok

                self.lexpos = lexpos
                raise LexError("Illegal character '%s' at index %d" % (lexdata[lexpos],lexpos), lexdata[lexpos:])

        self.lexpos = lexpos + 1
        if self.lexdata is None:
             raise RuntimeError("No input string given with input()")
        return None

    # Iterator interface
    def __iter__(self):
        return self

    def next(self):
        t = self.token()
        if t is None:
            raise StopIteration
        return t

    __next__ = next

# -----------------------------------------------------------------------------
#                           ==== Lex Builder ===
#
# The functions and classes below are used to collect lexing information
# and build a Lexer object from it.
# -----------------------------------------------------------------------------

# -----------------------------------------------------------------------------
# get_caller_module_dict()
#
# This function returns a dictionary containing all of the symbols defined within
# a caller further down the call stack.  This is used to get the environment
# associated with the yacc() call if none was provided.
# -----------------------------------------------------------------------------

def get_caller_module_dict(levels):
    try:
        raise RuntimeError
    except RuntimeError:
        e,b,t = sys.exc_info()
        f = t.tb_frame
        while levels > 0:
            f = f.f_back                   
            levels -= 1
        ldict = f.f_globals.copy()
        if f.f_globals != f.f_locals:
            ldict.update(f.f_locals)

        return ldict

# -----------------------------------------------------------------------------
# _funcs_to_names()
#
# Given a list of regular expression functions, this converts it to a list
# suitable for output to a table file
# -----------------------------------------------------------------------------

def _funcs_to_names(funclist,namelist):
    result = []
    for f,name in zip(funclist,namelist):
         if f and f[0]:
             result.append((name, f[1]))
         else:
             result.append(f)
    return result

# -----------------------------------------------------------------------------
# _names_to_funcs()
#
# Given a list of regular expression function names, this converts it back to
# functions.
# -----------------------------------------------------------------------------

def _names_to_funcs(namelist,fdict):
     result = []
     for n in namelist:
          if n and n[0]:
              result.append((fdict[n[0]],n[1]))
          else:
              result.append(n)
     return result

# -----------------------------------------------------------------------------
# _form_master_re()
#
# This function takes a list of all of the regex components and attempts to
# form the master regular expression.  Given limitations in the Python re
# module, it may be necessary to break the master regex into separate expressions.
# -----------------------------------------------------------------------------

def _form_master_re(relist,reflags,ldict,toknames):
    if not relist: return []
    regex = "|".join(relist)
    try:
        lexre = re.compile(regex,re.VERBOSE | reflags)

        # Build the index to function map for the matching engine
        lexindexfunc = [ None ] * (max(lexre.groupindex.values())+1)
        lexindexnames = lexindexfunc[:]

        for f,i in lexre.groupindex.items():
            handle = ldict.get(f,None)
            if type(handle) in (types.FunctionType, types.MethodType):
                lexindexfunc[i] = (handle,toknames[f])
                lexindexnames[i] = f
            elif handle is not None:
                lexindexnames[i] = f
                if f.find("ignore_") > 0:
                    lexindexfunc[i] = (None,None)
                else:
                    lexindexfunc[i] = (None, toknames[f])
        
        return [(lexre,lexindexfunc)],[regex],[lexindexnames]
    except Exception:
        m = int(len(relist)/2)
        if m == 0: m = 1
        llist, lre, lnames = _form_master_re(relist[:m],reflags,ldict,toknames)
        rlist, rre, rnames = _form_master_re(relist[m:],reflags,ldict,toknames)
        return llist+rlist, lre+rre, lnames+rnames

# -----------------------------------------------------------------------------
# def _statetoken(s,names)
#
# Given a declaration name s of the form "t_" and a dictionary whose keys are
# state names, this function returns a tuple (states,tokenname) where states
# is a tuple of state names and tokenname is the name of the token.  For example,
# calling this with s = "t_foo_bar_SPAM" might return (('foo','bar'),'SPAM')
# -----------------------------------------------------------------------------

def _statetoken(s,names):
    nonstate = 1
    parts = s.split("_")
    for i in range(1,len(parts)):
         if not parts[i] in names and parts[i] != 'ANY': break
    if i > 1:
       states = tuple(parts[1:i])
    else:
       states = ('INITIAL',)

    if 'ANY' in states:
       states = tuple(names)

    tokenname = "_".join(parts[i:])
    return (states,tokenname)


# -----------------------------------------------------------------------------
# LexerReflect()
#
# This class represents information needed to build a lexer as extracted from a
# user's input file.
# -----------------------------------------------------------------------------
class LexerReflect(object):
    def __init__(self,ldict,log=None,reflags=0):
        self.ldict      = ldict
        self.error_func = None
        self.tokens     = []
        self.reflags    = reflags
        self.stateinfo  = { 'INITIAL' : 'inclusive'}
        self.files      = {}
        self.error      = 0

        if log is None:
            self.log = PlyLogger(sys.stderr)
        else:
            self.log = log

    # Get all of the basic information
    def get_all(self):
        self.get_tokens()
        self.get_literals()
        self.get_states()
        self.get_rules()
        
    # Validate all of the information
    def validate_all(self):
        self.validate_tokens()
        self.validate_literals()
        self.validate_rules()
        return self.error

    # Get the tokens map
    def get_tokens(self):
        tokens = self.ldict.get("tokens",None)
        if not tokens:
            self.log.error("No token list is defined")
            self.error = 1
            return

        if not isinstance(tokens,(list, tuple)):
            self.log.error("tokens must be a list or tuple")
            self.error = 1
            return
        
        if not tokens:
            self.log.error("tokens is empty")
            self.error = 1
            return

        self.tokens = tokens

    # Validate the tokens
    def validate_tokens(self):
        terminals = {}
        for n in self.tokens:
            if not _is_identifier.match(n):
                self.log.error("Bad token name '%s'",n)
                self.error = 1
            if n in terminals:
                self.log.warning("Token '%s' multiply defined", n)
            terminals[n] = 1

    # Get the literals specifier
    def get_literals(self):
        self.literals = self.ldict.get("literals","")

    # Validate literals
    def validate_literals(self):
        try:
            for c in self.literals:
                if not isinstance(c,StringTypes) or len(c) > 1:
                    self.log.error("Invalid literal %s. Must be a single character", repr(c))
                    self.error = 1
                    continue

        except TypeError:
            self.log.error("Invalid literals specification. literals must be a sequence of characters")
            self.error = 1

    def get_states(self):
        self.states = self.ldict.get("states",None)
        # Build statemap
        if self.states:
             if not isinstance(self.states,(tuple,list)):
                  self.log.error("states must be defined as a tuple or list")
                  self.error = 1
             else:
                  for s in self.states:
                        if not isinstance(s,tuple) or len(s) != 2:
                               self.log.error("Invalid state specifier %s. Must be a tuple (statename,'exclusive|inclusive')",repr(s))
                               self.error = 1
                               continue
                        name, statetype = s
                        if not isinstance(name,StringTypes):
                               self.log.error("State name %s must be a string", repr(name))
                               self.error = 1
                               continue
                        if not (statetype == 'inclusive' or statetype == 'exclusive'):
                               self.log.error("State type for state %s must be 'inclusive' or 'exclusive'",name)
                               self.error = 1
                               continue
                        if name in self.stateinfo:
                               self.log.error("State '%s' already defined",name)
                               self.error = 1
                               continue
                        self.stateinfo[name] = statetype

    # Get all of the symbols with a t_ prefix and sort them into various
    # categories (functions, strings, error functions, and ignore characters)

    def get_rules(self):
        tsymbols = [f for f in self.ldict if f[:2] == 't_' ]

        # Now build up a list of functions and a list of strings

        self.toknames = { }        # Mapping of symbols to token names
        self.funcsym =  { }        # Symbols defined as functions
        self.strsym =   { }        # Symbols defined as strings
        self.ignore   = { }        # Ignore strings by state
        self.errorf   = { }        # Error functions by state

        for s in self.stateinfo:
             self.funcsym[s] = []
             self.strsym[s] = []

        if len(tsymbols) == 0:
            self.log.error("No rules of the form t_rulename are defined")
            self.error = 1
            return

        for f in tsymbols:
            t = self.ldict[f]
            states, tokname = _statetoken(f,self.stateinfo)
            self.toknames[f] = tokname

            if hasattr(t,"__call__"):
                if tokname == 'error':
                    for s in states:
                        self.errorf[s] = t
                elif tokname == 'ignore':
                    line = func_code(t).co_firstlineno
                    file = func_code(t).co_filename
                    self.log.error("%s:%d: Rule '%s' must be defined as a string",file,line,t.__name__)
                    self.error = 1
                else:
                    for s in states: 
                        self.funcsym[s].append((f,t))
            elif isinstance(t, StringTypes):
                if tokname == 'ignore':
                    for s in states:
                        self.ignore[s] = t
                    if "\\" in t:
                        self.log.warning("%s contains a literal backslash '\\'",f)

                elif tokname == 'error':
                    self.log.error("Rule '%s' must be defined as a function", f)
                    self.error = 1
                else:
                    for s in states: 
                        self.strsym[s].append((f,t))
            else:
                self.log.error("%s not defined as a function or string", f)
                self.error = 1

        # Sort the functions by line number
        for f in self.funcsym.values():
            if sys.version_info[0] < 3:
                f.sort(lambda x,y: cmp(func_code(x[1]).co_firstlineno,func_code(y[1]).co_firstlineno))
            else:
                # Python 3.0
                f.sort(key=lambda x: func_code(x[1]).co_firstlineno)

        # Sort the strings by regular expression length
        for s in self.strsym.values():
            if sys.version_info[0] < 3:
                s.sort(lambda x,y: (len(x[1]) < len(y[1])) - (len(x[1]) > len(y[1])))
            else:
                # Python 3.0
                s.sort(key=lambda x: len(x[1]),reverse=True)

    # Validate all of the t_rules collected 
    def validate_rules(self):
        for state in self.stateinfo:
            # Validate all rules defined by functions

            

            for fname, f in self.funcsym[state]:
                line = func_code(f).co_firstlineno
                file = func_code(f).co_filename
                self.files[file] = 1

                tokname = self.toknames[fname]
                if isinstance(f, types.MethodType):
                    reqargs = 2
                else:
                    reqargs = 1
                nargs = func_code(f).co_argcount
                if nargs > reqargs:
                    self.log.error("%s:%d: Rule '%s' has too many arguments",file,line,f.__name__)
                    self.error = 1
                    continue

                if nargs < reqargs:
                    self.log.error("%s:%d: Rule '%s' requires an argument", file,line,f.__name__)
                    self.error = 1
                    continue

                if not f.__doc__:
                    self.log.error("%s:%d: No regular expression defined for rule '%s'",file,line,f.__name__)
                    self.error = 1
                    continue

                try:
                    c = re.compile("(?P<%s>%s)" % (fname,f.__doc__), re.VERBOSE | self.reflags)
                    if c.match(""):
                        self.log.error("%s:%d: Regular expression for rule '%s' matches empty string", file,line,f.__name__)
                        self.error = 1
                except re.error:
                    _etype, e, _etrace = sys.exc_info()
                    self.log.error("%s:%d: Invalid regular expression for rule '%s'. %s", file,line,f.__name__,e)
                    if '#' in f.__doc__:
                        self.log.error("%s:%d. Make sure '#' in rule '%s' is escaped with '\\#'",file,line, f.__name__)
                    self.error = 1

            # Validate all rules defined by strings
            for name,r in self.strsym[state]:
                tokname = self.toknames[name]
                if tokname == 'error':
                    self.log.error("Rule '%s' must be defined as a function", name)
                    self.error = 1
                    continue

                if not tokname in self.tokens and tokname.find("ignore_") < 0:
                    self.log.error("Rule '%s' defined for an unspecified token %s",name,tokname)
                    self.error = 1
                    continue

                try:
                    c = re.compile("(?P<%s>%s)" % (name,r),re.VERBOSE | self.reflags)
                    if (c.match("")):
                         self.log.error("Regular expression for rule '%s' matches empty string",name)
                         self.error = 1
                except re.error:
                    _etype, e, _etrace = sys.exc_info()
                    self.log.error("Invalid regular expression for rule '%s'. %s",name,e)
                    if '#' in r:
                         self.log.error("Make sure '#' in rule '%s' is escaped with '\\#'",name)
                    self.error = 1

            if not self.funcsym[state] and not self.strsym[state]:
                self.log.error("No rules defined for state '%s'",state)
                self.error = 1

            # Validate the error function
            efunc = self.errorf.get(state,None)
            if efunc:
                f = efunc
                line = func_code(f).co_firstlineno
                file = func_code(f).co_filename
                self.files[file] = 1

                if isinstance(f, types.MethodType):
                    reqargs = 2
                else:
                    reqargs = 1
                nargs = func_code(f).co_argcount
                if nargs > reqargs:
                    self.log.error("%s:%d: Rule '%s' has too many arguments",file,line,f.__name__)
                    self.error = 1

                if nargs < reqargs:
                    self.log.error("%s:%d: Rule '%s' requires an argument", file,line,f.__name__)
                    self.error = 1

        for f in self.files:
            self.validate_file(f)


    # -----------------------------------------------------------------------------
    # validate_file()
    #
    # This checks to see if there are duplicated t_rulename() functions or strings
    # in the parser input file.  This is done using a simple regular expression
    # match on each line in the given file.  
    # -----------------------------------------------------------------------------

    def validate_file(self,filename):
        import os.path
        base,ext = os.path.splitext(filename)
        if ext != '.py': return         # No idea what the file is. Return OK

        try:
            f = open(filename)
            lines = f.readlines()
            f.close()
        except IOError:
            return                      # Couldn't find the file.  Don't worry about it

        fre = re.compile(r'\s*def\s+(t_[a-zA-Z_0-9]*)\(')
        sre = re.compile(r'\s*(t_[a-zA-Z_0-9]*)\s*=')

        counthash = { }
        linen = 1
        for l in lines:
            m = fre.match(l)
            if not m:
                m = sre.match(l)
            if m:
                name = m.group(1)
                prev = counthash.get(name)
                if not prev:
                    counthash[name] = linen
                else:
                    self.log.error("%s:%d: Rule %s redefined. Previously defined on line %d",filename,linen,name,prev)
                    self.error = 1
            linen += 1
            
# -----------------------------------------------------------------------------
# lex(module)
#
# Build all of the regular expression rules from definitions in the supplied module
# -----------------------------------------------------------------------------
def lex(module=None,object=None,debug=0,optimize=0,lextab="lextab",reflags=0,nowarn=0,outputdir="", debuglog=None, errorlog=None):
    global lexer
    ldict = None
    stateinfo  = { 'INITIAL' : 'inclusive'}
    lexobj = Lexer()
    lexobj.lexoptimize = optimize
    global token,input

    if errorlog is None:
        errorlog = PlyLogger(sys.stderr)

    if debug:
        if debuglog is None:
            debuglog = PlyLogger(sys.stderr)

    # Get the module dictionary used for the lexer
    if object: module = object

    if module:
        _items = [(k,getattr(module,k)) for k in dir(module)]
        ldict = dict(_items)
    else:
        ldict = get_caller_module_dict(2)

    # Collect parser information from the dictionary
    linfo = LexerReflect(ldict,log=errorlog,reflags=reflags)
    linfo.get_all()
    if not optimize:
        if linfo.validate_all():
            raise SyntaxError("Can't build lexer")

    if optimize and lextab:
        try:
            lexobj.readtab(lextab,ldict)
            token = lexobj.token
            input = lexobj.input
            lexer = lexobj
            return lexobj

        except ImportError:
            pass

    # Dump some basic debugging information
    if debug:
        debuglog.info("lex: tokens   = %r", linfo.tokens)
        debuglog.info("lex: literals = %r", linfo.literals)
        debuglog.info("lex: states   = %r", linfo.stateinfo)

    # Build a dictionary of valid token names
    lexobj.lextokens = { }
    for n in linfo.tokens:
        lexobj.lextokens[n] = 1

    # Get literals specification
    if isinstance(linfo.literals,(list,tuple)):
        lexobj.lexliterals = type(linfo.literals[0])().join(linfo.literals)
    else:
        lexobj.lexliterals = linfo.literals

    # Get the stateinfo dictionary
    stateinfo = linfo.stateinfo

    regexs = { }
    # Build the master regular expressions
    for state in stateinfo:
        regex_list = []

        # Add rules defined by functions first
        for fname, f in linfo.funcsym[state]:
            line = func_code(f).co_firstlineno
            file = func_code(f).co_filename
            regex_list.append("(?P<%s>%s)" % (fname,f.__doc__))
            if debug:
                debuglog.info("lex: Adding rule %s -> '%s' (state '%s')",fname,f.__doc__, state)

        # Now add all of the simple rules
        for name,r in linfo.strsym[state]:
            regex_list.append("(?P<%s>%s)" % (name,r))
            if debug:
                debuglog.info("lex: Adding rule %s -> '%s' (state '%s')",name,r, state)

        regexs[state] = regex_list

    # Build the master regular expressions

    if debug:
        debuglog.info("lex: ==== MASTER REGEXS FOLLOW ====")

    for state in regexs:
        lexre, re_text, re_names = _form_master_re(regexs[state],reflags,ldict,linfo.toknames)
        lexobj.lexstatere[state] = lexre
        lexobj.lexstateretext[state] = re_text
        lexobj.lexstaterenames[state] = re_names
        if debug:
            for i in range(len(re_text)):
                debuglog.info("lex: state '%s' : regex[%d] = '%s'",state, i, re_text[i])

    # For inclusive states, we need to add the regular expressions from the INITIAL state
    for state,stype in stateinfo.items():
        if state != "INITIAL" and stype == 'inclusive':
             lexobj.lexstatere[state].extend(lexobj.lexstatere['INITIAL'])
             lexobj.lexstateretext[state].extend(lexobj.lexstateretext['INITIAL'])
             lexobj.lexstaterenames[state].extend(lexobj.lexstaterenames['INITIAL'])

    lexobj.lexstateinfo = stateinfo
    lexobj.lexre = lexobj.lexstatere["INITIAL"]
    lexobj.lexretext = lexobj.lexstateretext["INITIAL"]
    lexobj.lexreflags = reflags

    # Set up ignore variables
    lexobj.lexstateignore = linfo.ignore
    lexobj.lexignore = lexobj.lexstateignore.get("INITIAL","")

    # Set up error functions
    lexobj.lexstateerrorf = linfo.errorf
    lexobj.lexerrorf = linfo.errorf.get("INITIAL",None)
    if not lexobj.lexerrorf:
        errorlog.warning("No t_error rule is defined")

    # Check state information for ignore and error rules
    for s,stype in stateinfo.items():
        if stype == 'exclusive':
              if not s in linfo.errorf:
                   errorlog.warning("No error rule is defined for exclusive state '%s'", s)
              if not s in linfo.ignore and lexobj.lexignore:
                   errorlog.warning("No ignore rule is defined for exclusive state '%s'", s)
        elif stype == 'inclusive':
              if not s in linfo.errorf:
                   linfo.errorf[s] = linfo.errorf.get("INITIAL",None)
              if not s in linfo.ignore:
                   linfo.ignore[s] = linfo.ignore.get("INITIAL","")

    # Create global versions of the token() and input() functions
    token = lexobj.token
    input = lexobj.input
    lexer = lexobj

    # If in optimize mode, we write the lextab
    if lextab and optimize:
        lexobj.writetab(lextab,outputdir)

    return lexobj

# -----------------------------------------------------------------------------
# runmain()
#
# This runs the lexer as a main program
# -----------------------------------------------------------------------------

def runmain(lexer=None,data=None):
    if not data:
        try:
            filename = sys.argv[1]
            f = open(filename)
            data = f.read()
            f.close()
        except IndexError:
            sys.stdout.write("Reading from standard input (type EOF to end):\n")
            data = sys.stdin.read()

    if lexer:
        _input = lexer.input
    else:
        _input = input
    _input(data)
    if lexer:
        _token = lexer.token
    else:
        _token = token

    while 1:
        tok = _token()
        if not tok: break
        sys.stdout.write("(%s,%r,%d,%d)\n" % (tok.type, tok.value, tok.lineno,tok.lexpos))

# -----------------------------------------------------------------------------
# @TOKEN(regex)
#
# This decorator function can be used to set the regex expression on a function
# when its docstring might need to be set in an alternative way
# -----------------------------------------------------------------------------

def TOKEN(r):
    def set_doc(f):
        if hasattr(r,"__call__"):
            f.__doc__ = r.__doc__
        else:
            f.__doc__ = r
        return f
    return set_doc

# Alternative spelling of the TOKEN decorator
Token = TOKEN


### BEGIN inlined_ply/yacc.py

# -----------------------------------------------------------------------------
# ply: yacc.py
#
# Copyright (C) 2001-2011,
# David M. Beazley (Dabeaz LLC)
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
# 
# * Redistributions of source code must retain the above copyright notice,
#   this list of conditions and the following disclaimer.  
# * Redistributions in binary form must reproduce the above copyright notice, 
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.  
# * Neither the name of the David Beazley or Dabeaz LLC may be used to
#   endorse or promote products derived from this software without
#  specific prior written permission. 
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
# -----------------------------------------------------------------------------
#
# This implements an LR parser that is constructed from grammar rules defined
# as Python functions. The grammer is specified by supplying the BNF inside
# Python documentation strings.  The inspiration for this technique was borrowed
# from John Aycock's Spark parsing system.  PLY might be viewed as cross between
# Spark and the GNU bison utility.
#
# The current implementation is only somewhat object-oriented. The
# LR parser itself is defined in terms of an object (which allows multiple
# parsers to co-exist).  However, most of the variables used during table
# construction are defined in terms of global variables.  Users shouldn't
# notice unless they are trying to define multiple parsers at the same
# time using threads (in which case they should have their head examined).
#
# This implementation supports both SLR and LALR(1) parsing.  LALR(1)
# support was originally implemented by Elias Ioup (ezioup@alumni.uchicago.edu),
# using the algorithm found in Aho, Sethi, and Ullman "Compilers: Principles,
# Techniques, and Tools" (The Dragon Book).  LALR(1) has since been replaced
# by the more efficient DeRemer and Pennello algorithm.
#
# :::::::: WARNING :::::::
#
# Construction of LR parsing tables is fairly complicated and expensive.
# To make this module run fast, a *LOT* of work has been put into
# optimization---often at the expensive of readability and what might
# consider to be good Python "coding style."   Modify the code at your
# own risk!
# ----------------------------------------------------------------------------

__version__    = "3.4"
__tabversion__ = "3.2"       # Table version

#-----------------------------------------------------------------------------
#                     === User configurable parameters ===
#
# Change these to modify the default behavior of yacc (if you wish)
#-----------------------------------------------------------------------------

yaccdebug   = 1                # Debugging mode.  If set, yacc generates a
                               # a 'parser.out' file in the current directory

debug_file  = 'parser.out'     # Default name of the debugging file
tab_module  = 'parsetab'       # Default name of the table module
default_lr  = 'LALR'           # Default LR table generation method

error_count = 3                # Number of symbols that must be shifted to leave recovery mode

yaccdevel   = 0                # Set to True if developing yacc.  This turns off optimized
                               # implementations of certain functions.

resultlimit = 40               # Size limit of results when running in debug mode.

pickle_protocol = 0            # Protocol to use when writing pickle files

import re, types, sys, os.path

# Compatibility function for python 2.6/3.0
if sys.version_info[0] < 3:
    def func_code(f):
        return f.func_code
else:
    def func_code(f):
        return f.__code__

# Compatibility
try:
    MAXINT = sys.maxint
except AttributeError:
    MAXINT = sys.maxsize

# Python 2.x/3.0 compatibility.
def load_ply_lex():
    #if sys.version_info[0] < 3:
    #    import lex
    #else:
    #    import ply.lex as lex
    #return lex
    global lexer
    class DummyLexer:
        lexer = lexer
    return DummyLexer

# This object is a stand-in for a logging object created by the 
# logging module.   PLY will use this by default to create things
# such as the parser.out file.  If a user wants more detailed
# information, they can create their own logging object and pass
# it into PLY.

class PlyLogger(object):
    def __init__(self,f):
        self.f = f
    def debug(self,msg,*args,**kwargs):
        self.f.write((msg % args) + "\n")
    info     = debug

    def warning(self,msg,*args,**kwargs):
        self.f.write("WARNING: "+ (msg % args) + "\n")

    def error(self,msg,*args,**kwargs):
        self.f.write("ERROR: " + (msg % args) + "\n")

    critical = debug

# Null logger is used when no output is generated. Does nothing.
class NullLogger(object):
    def __getattribute__(self,name):
        return self
    def __call__(self,*args,**kwargs):
        return self
        
# Exception raised for yacc-related errors
class YaccError(Exception):   pass

# Format the result message that the parser produces when running in debug mode.
def format_result(r):
    repr_str = repr(r)
    if '\n' in repr_str: repr_str = repr(repr_str)
    if len(repr_str) > resultlimit:
        repr_str = repr_str[:resultlimit]+" ..."
    result = "<%s @ 0x%x> (%s)" % (type(r).__name__,id(r),repr_str)
    return result


# Format stack entries when the parser is running in debug mode
def format_stack_entry(r):
    repr_str = repr(r)
    if '\n' in repr_str: repr_str = repr(repr_str)
    if len(repr_str) < 16:
        return repr_str
    else:
        return "<%s @ 0x%x>" % (type(r).__name__,id(r))

#-----------------------------------------------------------------------------
#                        ===  LR Parsing Engine ===
#
# The following classes are used for the LR parser itself.  These are not
# used during table construction and are independent of the actual LR
# table generation algorithm
#-----------------------------------------------------------------------------

# This class is used to hold non-terminal grammar symbols during parsing.
# It normally has the following attributes set:
#        .type       = Grammar symbol type
#        .value      = Symbol value
#        .lineno     = Starting line number
#        .endlineno  = Ending line number (optional, set automatically)
#        .lexpos     = Starting lex position
#        .endlexpos  = Ending lex position (optional, set automatically)

class YaccSymbol:
    def __str__(self):    return self.type
    def __repr__(self):   return str(self)

# This class is a wrapper around the objects actually passed to each
# grammar rule.   Index lookup and assignment actually assign the
# .value attribute of the underlying YaccSymbol object.
# The lineno() method returns the line number of a given
# item (or 0 if not defined).   The linespan() method returns
# a tuple of (startline,endline) representing the range of lines
# for a symbol.  The lexspan() method returns a tuple (lexpos,endlexpos)
# representing the range of positional information for a symbol.

class YaccProduction:
    def __init__(self,s,stack=None):
        self.slice = s
        self.stack = stack
        self.lexer = None
        self.parser= None
    def __getitem__(self,n):
        if n >= 0: return self.slice[n].value
        else: return self.stack[n].value

    def __setitem__(self,n,v):
        self.slice[n].value = v

    def __getslice__(self,i,j):
        return [s.value for s in self.slice[i:j]]

    def __len__(self):
        return len(self.slice)

    def lineno(self,n):
        return getattr(self.slice[n],"lineno",0)

    def set_lineno(self,n,lineno):
        self.slice[n].lineno = lineno

    def linespan(self,n):
        startline = getattr(self.slice[n],"lineno",0)
        endline = getattr(self.slice[n],"endlineno",startline)
        return startline,endline

    def lexpos(self,n):
        return getattr(self.slice[n],"lexpos",0)

    def lexspan(self,n):
        startpos = getattr(self.slice[n],"lexpos",0)
        endpos = getattr(self.slice[n],"endlexpos",startpos)
        return startpos,endpos

    def error(self):
       raise SyntaxError


# -----------------------------------------------------------------------------
#                               == LRParser ==
#
# The LR Parsing engine.
# -----------------------------------------------------------------------------

class LRParser:
    def __init__(self,lrtab,errorf):
        self.productions = lrtab.lr_productions
        self.action      = lrtab.lr_action
        self.goto        = lrtab.lr_goto
        self.errorfunc   = errorf

    def errok(self):
        self.errorok     = 1

    def restart(self):
        del self.statestack[:]
        del self.symstack[:]
        sym = YaccSymbol()
        sym.type = '$end'
        self.symstack.append(sym)
        self.statestack.append(0)

    def parse(self,input=None,lexer=None,debug=0,tracking=0,tokenfunc=None):
        if debug or yaccdevel:
            if isinstance(debug,int):
                debug = PlyLogger(sys.stderr)
            return self.parsedebug(input,lexer,debug,tracking,tokenfunc)
        elif tracking:
            return self.parseopt(input,lexer,debug,tracking,tokenfunc)
        else:
            return self.parseopt_notrack(input,lexer,debug,tracking,tokenfunc)
        

    # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    # parsedebug().
    #
    # This is the debugging enabled version of parse().  All changes made to the
    # parsing engine should be made here.   For the non-debugging version,
    # copy this code to a method parseopt() and delete all of the sections
    # enclosed in:
    #
    #      #--! DEBUG
    #      statements
    #      #--! DEBUG
    #
    # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    def parsedebug(self,input=None,lexer=None,debug=None,tracking=0,tokenfunc=None):
        lookahead = None                 # Current lookahead symbol
        lookaheadstack = [ ]             # Stack of lookahead symbols
        actions = self.action            # Local reference to action table (to avoid lookup on self.)
        goto    = self.goto              # Local reference to goto table (to avoid lookup on self.)
        prod    = self.productions       # Local reference to production list (to avoid lookup on self.)
        pslice  = YaccProduction(None)   # Production object passed to grammar rules
        errorcount = 0                   # Used during error recovery 

        # --! DEBUG
        debug.info("PLY: PARSE DEBUG START")
        # --! DEBUG

        # If no lexer was given, we will try to use the lex module
        if not lexer:
            lex = load_ply_lex()
            lexer = lex.lexer

        # Set up the lexer and parser objects on pslice
        pslice.lexer = lexer
        pslice.parser = self

        # If input was supplied, pass to lexer
        if input is not None:
            lexer.input(input)

        if tokenfunc is None:
           # Tokenize function
           get_token = lexer.token
        else:
           get_token = tokenfunc

        # Set up the state and symbol stacks

        statestack = [ ]                # Stack of parsing states
        self.statestack = statestack
        symstack   = [ ]                # Stack of grammar symbols
        self.symstack = symstack

        pslice.stack = symstack         # Put in the production
        errtoken   = None               # Err token

        # The start state is assumed to be (0,$end)

        statestack.append(0)
        sym = YaccSymbol()
        sym.type = "$end"
        symstack.append(sym)
        state = 0
        while 1:
            # Get the next symbol on the input.  If a lookahead symbol
            # is already set, we just use that. Otherwise, we'll pull
            # the next token off of the lookaheadstack or from the lexer

            # --! DEBUG
            debug.debug('')
            debug.debug('State  : %s', state)
            # --! DEBUG

            if not lookahead:
                if not lookaheadstack:
                    lookahead = get_token()     # Get the next token
                else:
                    lookahead = lookaheadstack.pop()
                if not lookahead:
                    lookahead = YaccSymbol()
                    lookahead.type = "$end"

            # --! DEBUG
            debug.debug('Stack  : %s',
                        ("%s . %s" % (" ".join([xx.type for xx in symstack][1:]), str(lookahead))).lstrip())
            # --! DEBUG

            # Check the action table
            ltype = lookahead.type
            t = actions[state].get(ltype)

            if t is not None:
                if t > 0:
                    # shift a symbol on the stack
                    statestack.append(t)
                    state = t
                    
                    # --! DEBUG
                    debug.debug("Action : Shift and goto state %s", t)
                    # --! DEBUG

                    symstack.append(lookahead)
                    lookahead = None

                    # Decrease error count on successful shift
                    if errorcount: errorcount -=1
                    continue

                if t < 0:
                    # reduce a symbol on the stack, emit a production
                    p = prod[-t]
                    pname = p.name
                    plen  = p.len

                    # Get production function
                    sym = YaccSymbol()
                    sym.type = pname       # Production name
                    sym.value = None

                    # --! DEBUG
                    if plen:
                        debug.info("Action : Reduce rule [%s] with %s and goto state %d", p.str, "["+",".join([format_stack_entry(_v.value) for _v in symstack[-plen:]])+"]",-t)
                    else:
                        debug.info("Action : Reduce rule [%s] with %s and goto state %d", p.str, [],-t)
                        
                    # --! DEBUG

                    if plen:
                        targ = symstack[-plen-1:]
                        targ[0] = sym

                        # --! TRACKING
                        if tracking:
                           t1 = targ[1]
                           sym.lineno = t1.lineno
                           sym.lexpos = t1.lexpos
                           t1 = targ[-1]
                           sym.endlineno = getattr(t1,"endlineno",t1.lineno)
                           sym.endlexpos = getattr(t1,"endlexpos",t1.lexpos)

                        # --! TRACKING

                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                        # The code enclosed in this section is duplicated 
                        # below as a performance optimization.  Make sure
                        # changes get made in both locations.

                        pslice.slice = targ
                        
                        try:
                            # Call the grammar rule with our special slice object
                            del symstack[-plen:]
                            del statestack[-plen:]
                            p.callable(pslice)
                            # --! DEBUG
                            debug.info("Result : %s", format_result(pslice[0]))
                            # --! DEBUG
                            symstack.append(sym)
                            state = goto[statestack[-1]][pname]
                            statestack.append(state)
                        except SyntaxError:
                            # If an error was set. Enter error recovery state
                            lookaheadstack.append(lookahead)
                            symstack.pop()
                            statestack.pop()
                            state = statestack[-1]
                            sym.type = 'error'
                            lookahead = sym
                            errorcount = error_count
                            self.errorok = 0
                        continue
                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    
                    else:

                        # --! TRACKING
                        if tracking:
                           sym.lineno = lexer.lineno
                           sym.lexpos = lexer.lexpos
                        # --! TRACKING

                        targ = [ sym ]

                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                        # The code enclosed in this section is duplicated 
                        # above as a performance optimization.  Make sure
                        # changes get made in both locations.

                        pslice.slice = targ

                        try:
                            # Call the grammar rule with our special slice object
                            p.callable(pslice)
                            # --! DEBUG
                            debug.info("Result : %s", format_result(pslice[0]))
                            # --! DEBUG
                            symstack.append(sym)
                            state = goto[statestack[-1]][pname]
                            statestack.append(state)
                        except SyntaxError:
                            # If an error was set. Enter error recovery state
                            lookaheadstack.append(lookahead)
                            symstack.pop()
                            statestack.pop()
                            state = statestack[-1]
                            sym.type = 'error'
                            lookahead = sym
                            errorcount = error_count
                            self.errorok = 0
                        continue
                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

                if t == 0:
                    n = symstack[-1]
                    result = getattr(n,"value",None)
                    # --! DEBUG
                    debug.info("Done   : Returning %s", format_result(result))
                    debug.info("PLY: PARSE DEBUG END")
                    # --! DEBUG
                    return result

            if t == None:

                # --! DEBUG
                debug.error('Error  : %s',
                            ("%s . %s" % (" ".join([xx.type for xx in symstack][1:]), str(lookahead))).lstrip())
                # --! DEBUG

                # We have some kind of parsing error here.  To handle
                # this, we are going to push the current token onto
                # the tokenstack and replace it with an 'error' token.
                # If there are any synchronization rules, they may
                # catch it.
                #
                # In addition to pushing the error token, we call call
                # the user defined p_error() function if this is the
                # first syntax error.  This function is only called if
                # errorcount == 0.
                if errorcount == 0 or self.errorok:
                    errorcount = error_count
                    self.errorok = 0
                    errtoken = lookahead
                    if errtoken.type == "$end":
                        errtoken = None               # End of file!
                    if self.errorfunc:
                        global errok,token,restart
                        errok = self.errok        # Set some special functions available in error recovery
                        token = get_token
                        restart = self.restart
                        if errtoken and not hasattr(errtoken,'lexer'):
                            errtoken.lexer = lexer
                        tok = self.errorfunc(errtoken)
                        del errok, token, restart   # Delete special functions

                        if self.errorok:
                            # User must have done some kind of panic
                            # mode recovery on their own.  The
                            # returned token is the next lookahead
                            lookahead = tok
                            errtoken = None
                            continue
                    else:
                        if errtoken:
                            if hasattr(errtoken,"lineno"): lineno = lookahead.lineno
                            else: lineno = 0
                            if lineno:
                                sys.stderr.write("yacc: Syntax error at line %d, token=%s\n" % (lineno, errtoken.type))
                            else:
                                sys.stderr.write("yacc: Syntax error, token=%s" % errtoken.type)
                        else:
                            sys.stderr.write("yacc: Parse error in input. EOF\n")
                            return

                else:
                    errorcount = error_count

                # case 1:  the statestack only has 1 entry on it.  If we're in this state, the
                # entire parse has been rolled back and we're completely hosed.   The token is
                # discarded and we just keep going.

                if len(statestack) <= 1 and lookahead.type != "$end":
                    lookahead = None
                    errtoken = None
                    state = 0
                    # Nuke the pushback stack
                    del lookaheadstack[:]
                    continue

                # case 2: the statestack has a couple of entries on it, but we're
                # at the end of the file. nuke the top entry and generate an error token

                # Start nuking entries on the stack
                if lookahead.type == "$end":
                    # Whoa. We're really hosed here. Bail out
                    return

                if lookahead.type != 'error':
                    sym = symstack[-1]
                    if sym.type == 'error':
                        # Hmmm. Error is on top of stack, we'll just nuke input
                        # symbol and continue
                        lookahead = None
                        continue
                    t = YaccSymbol()
                    t.type = 'error'
                    if hasattr(lookahead,"lineno"):
                        t.lineno = lookahead.lineno
                    t.value = lookahead
                    lookaheadstack.append(lookahead)
                    lookahead = t
                else:
                    symstack.pop()
                    statestack.pop()
                    state = statestack[-1]       # Potential bug fix

                continue

            # Call an error function here
            raise RuntimeError("yacc: internal parser error!!!\n")

    # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    # parseopt().
    #
    # Optimized version of parse() method.  DO NOT EDIT THIS CODE DIRECTLY.
    # Edit the debug version above, then copy any modifications to the method
    # below while removing #--! DEBUG sections.
    # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!


    def parseopt(self,input=None,lexer=None,debug=0,tracking=0,tokenfunc=None):
        lookahead = None                 # Current lookahead symbol
        lookaheadstack = [ ]             # Stack of lookahead symbols
        actions = self.action            # Local reference to action table (to avoid lookup on self.)
        goto    = self.goto              # Local reference to goto table (to avoid lookup on self.)
        prod    = self.productions       # Local reference to production list (to avoid lookup on self.)
        pslice  = YaccProduction(None)   # Production object passed to grammar rules
        errorcount = 0                   # Used during error recovery 

        # If no lexer was given, we will try to use the lex module
        if not lexer:
            lex = load_ply_lex()
            lexer = lex.lexer
        
        # Set up the lexer and parser objects on pslice
        pslice.lexer = lexer
        pslice.parser = self

        # If input was supplied, pass to lexer
        if input is not None:
            lexer.input(input)

        if tokenfunc is None:
           # Tokenize function
           get_token = lexer.token
        else:
           get_token = tokenfunc

        # Set up the state and symbol stacks

        statestack = [ ]                # Stack of parsing states
        self.statestack = statestack
        symstack   = [ ]                # Stack of grammar symbols
        self.symstack = symstack

        pslice.stack = symstack         # Put in the production
        errtoken   = None               # Err token

        # The start state is assumed to be (0,$end)

        statestack.append(0)
        sym = YaccSymbol()
        sym.type = '$end'
        symstack.append(sym)
        state = 0
        while 1:
            # Get the next symbol on the input.  If a lookahead symbol
            # is already set, we just use that. Otherwise, we'll pull
            # the next token off of the lookaheadstack or from the lexer

            if not lookahead:
                if not lookaheadstack:
                    lookahead = get_token()     # Get the next token
                else:
                    lookahead = lookaheadstack.pop()
                if not lookahead:
                    lookahead = YaccSymbol()
                    lookahead.type = '$end'

            # Check the action table
            ltype = lookahead.type
            t = actions[state].get(ltype)

            if t is not None:
                if t > 0:
                    # shift a symbol on the stack
                    statestack.append(t)
                    state = t

                    symstack.append(lookahead)
                    lookahead = None

                    # Decrease error count on successful shift
                    if errorcount: errorcount -=1
                    continue

                if t < 0:
                    # reduce a symbol on the stack, emit a production
                    p = prod[-t]
                    pname = p.name
                    plen  = p.len

                    # Get production function
                    sym = YaccSymbol()
                    sym.type = pname       # Production name
                    sym.value = None

                    if plen:
                        targ = symstack[-plen-1:]
                        targ[0] = sym

                        # --! TRACKING
                        if tracking:
                           t1 = targ[1]
                           sym.lineno = t1.lineno
                           sym.lexpos = t1.lexpos
                           t1 = targ[-1]
                           sym.endlineno = getattr(t1,"endlineno",t1.lineno)
                           sym.endlexpos = getattr(t1,"endlexpos",t1.lexpos)

                        # --! TRACKING

                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                        # The code enclosed in this section is duplicated 
                        # below as a performance optimization.  Make sure
                        # changes get made in both locations.

                        pslice.slice = targ
                        
                        try:
                            # Call the grammar rule with our special slice object
                            del symstack[-plen:]
                            del statestack[-plen:]
                            p.callable(pslice)
                            symstack.append(sym)
                            state = goto[statestack[-1]][pname]
                            statestack.append(state)
                        except SyntaxError:
                            # If an error was set. Enter error recovery state
                            lookaheadstack.append(lookahead)
                            symstack.pop()
                            statestack.pop()
                            state = statestack[-1]
                            sym.type = 'error'
                            lookahead = sym
                            errorcount = error_count
                            self.errorok = 0
                        continue
                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    
                    else:

                        # --! TRACKING
                        if tracking:
                           sym.lineno = lexer.lineno
                           sym.lexpos = lexer.lexpos
                        # --! TRACKING

                        targ = [ sym ]

                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                        # The code enclosed in this section is duplicated 
                        # above as a performance optimization.  Make sure
                        # changes get made in both locations.

                        pslice.slice = targ

                        try:
                            # Call the grammar rule with our special slice object
                            p.callable(pslice)
                            symstack.append(sym)
                            state = goto[statestack[-1]][pname]
                            statestack.append(state)
                        except SyntaxError:
                            # If an error was set. Enter error recovery state
                            lookaheadstack.append(lookahead)
                            symstack.pop()
                            statestack.pop()
                            state = statestack[-1]
                            sym.type = 'error'
                            lookahead = sym
                            errorcount = error_count
                            self.errorok = 0
                        continue
                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

                if t == 0:
                    n = symstack[-1]
                    return getattr(n,"value",None)

            if t == None:

                # We have some kind of parsing error here.  To handle
                # this, we are going to push the current token onto
                # the tokenstack and replace it with an 'error' token.
                # If there are any synchronization rules, they may
                # catch it.
                #
                # In addition to pushing the error token, we call call
                # the user defined p_error() function if this is the
                # first syntax error.  This function is only called if
                # errorcount == 0.
                if errorcount == 0 or self.errorok:
                    errorcount = error_count
                    self.errorok = 0
                    errtoken = lookahead
                    if errtoken.type == '$end':
                        errtoken = None               # End of file!
                    if self.errorfunc:
                        global errok,token,restart
                        errok = self.errok        # Set some special functions available in error recovery
                        token = get_token
                        restart = self.restart
                        if errtoken and not hasattr(errtoken,'lexer'):
                            errtoken.lexer = lexer
                        tok = self.errorfunc(errtoken)
                        del errok, token, restart   # Delete special functions

                        if self.errorok:
                            # User must have done some kind of panic
                            # mode recovery on their own.  The
                            # returned token is the next lookahead
                            lookahead = tok
                            errtoken = None
                            continue
                    else:
                        if errtoken:
                            if hasattr(errtoken,"lineno"): lineno = lookahead.lineno
                            else: lineno = 0
                            if lineno:
                                sys.stderr.write("yacc: Syntax error at line %d, token=%s\n" % (lineno, errtoken.type))
                            else:
                                sys.stderr.write("yacc: Syntax error, token=%s" % errtoken.type)
                        else:
                            sys.stderr.write("yacc: Parse error in input. EOF\n")
                            return

                else:
                    errorcount = error_count

                # case 1:  the statestack only has 1 entry on it.  If we're in this state, the
                # entire parse has been rolled back and we're completely hosed.   The token is
                # discarded and we just keep going.

                if len(statestack) <= 1 and lookahead.type != '$end':
                    lookahead = None
                    errtoken = None
                    state = 0
                    # Nuke the pushback stack
                    del lookaheadstack[:]
                    continue

                # case 2: the statestack has a couple of entries on it, but we're
                # at the end of the file. nuke the top entry and generate an error token

                # Start nuking entries on the stack
                if lookahead.type == '$end':
                    # Whoa. We're really hosed here. Bail out
                    return

                if lookahead.type != 'error':
                    sym = symstack[-1]
                    if sym.type == 'error':
                        # Hmmm. Error is on top of stack, we'll just nuke input
                        # symbol and continue
                        lookahead = None
                        continue
                    t = YaccSymbol()
                    t.type = 'error'
                    if hasattr(lookahead,"lineno"):
                        t.lineno = lookahead.lineno
                    t.value = lookahead
                    lookaheadstack.append(lookahead)
                    lookahead = t
                else:
                    symstack.pop()
                    statestack.pop()
                    state = statestack[-1]       # Potential bug fix

                continue

            # Call an error function here
            raise RuntimeError("yacc: internal parser error!!!\n")

    # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    # parseopt_notrack().
    #
    # Optimized version of parseopt() with line number tracking removed. 
    # DO NOT EDIT THIS CODE DIRECTLY. Copy the optimized version and remove
    # code in the #--! TRACKING sections
    # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    def parseopt_notrack(self,input=None,lexer=None,debug=0,tracking=0,tokenfunc=None):
        lookahead = None                 # Current lookahead symbol
        lookaheadstack = [ ]             # Stack of lookahead symbols
        actions = self.action            # Local reference to action table (to avoid lookup on self.)
        goto    = self.goto              # Local reference to goto table (to avoid lookup on self.)
        prod    = self.productions       # Local reference to production list (to avoid lookup on self.)
        pslice  = YaccProduction(None)   # Production object passed to grammar rules
        errorcount = 0                   # Used during error recovery 

        # If no lexer was given, we will try to use the lex module
        if not lexer:
            lex = load_ply_lex()
            lexer = lex.lexer
        
        # Set up the lexer and parser objects on pslice
        pslice.lexer = lexer
        pslice.parser = self

        # If input was supplied, pass to lexer
        if input is not None:
            lexer.input(input)

        if tokenfunc is None:
           # Tokenize function
           get_token = lexer.token
        else:
           get_token = tokenfunc

        # Set up the state and symbol stacks

        statestack = [ ]                # Stack of parsing states
        self.statestack = statestack
        symstack   = [ ]                # Stack of grammar symbols
        self.symstack = symstack

        pslice.stack = symstack         # Put in the production
        errtoken   = None               # Err token

        # The start state is assumed to be (0,$end)

        statestack.append(0)
        sym = YaccSymbol()
        sym.type = '$end'
        symstack.append(sym)
        state = 0
        while 1:
            # Get the next symbol on the input.  If a lookahead symbol
            # is already set, we just use that. Otherwise, we'll pull
            # the next token off of the lookaheadstack or from the lexer

            if not lookahead:
                if not lookaheadstack:
                    lookahead = get_token()     # Get the next token
                else:
                    lookahead = lookaheadstack.pop()
                if not lookahead:
                    lookahead = YaccSymbol()
                    lookahead.type = '$end'

            # Check the action table
            ltype = lookahead.type
            t = actions[state].get(ltype)

            if t is not None:
                if t > 0:
                    # shift a symbol on the stack
                    statestack.append(t)
                    state = t

                    symstack.append(lookahead)
                    lookahead = None

                    # Decrease error count on successful shift
                    if errorcount: errorcount -=1
                    continue

                if t < 0:
                    # reduce a symbol on the stack, emit a production
                    p = prod[-t]
                    pname = p.name
                    plen  = p.len

                    # Get production function
                    sym = YaccSymbol()
                    sym.type = pname       # Production name
                    sym.value = None

                    if plen:
                        targ = symstack[-plen-1:]
                        targ[0] = sym

                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                        # The code enclosed in this section is duplicated 
                        # below as a performance optimization.  Make sure
                        # changes get made in both locations.

                        pslice.slice = targ
                        
                        try:
                            # Call the grammar rule with our special slice object
                            del symstack[-plen:]
                            del statestack[-plen:]
                            p.callable(pslice)
                            symstack.append(sym)
                            state = goto[statestack[-1]][pname]
                            statestack.append(state)
                        except SyntaxError:
                            # If an error was set. Enter error recovery state
                            lookaheadstack.append(lookahead)
                            symstack.pop()
                            statestack.pop()
                            state = statestack[-1]
                            sym.type = 'error'
                            lookahead = sym
                            errorcount = error_count
                            self.errorok = 0
                        continue
                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    
                    else:

                        targ = [ sym ]

                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                        # The code enclosed in this section is duplicated 
                        # above as a performance optimization.  Make sure
                        # changes get made in both locations.

                        pslice.slice = targ

                        try:
                            # Call the grammar rule with our special slice object
                            p.callable(pslice)
                            symstack.append(sym)
                            state = goto[statestack[-1]][pname]
                            statestack.append(state)
                        except SyntaxError:
                            # If an error was set. Enter error recovery state
                            lookaheadstack.append(lookahead)
                            symstack.pop()
                            statestack.pop()
                            state = statestack[-1]
                            sym.type = 'error'
                            lookahead = sym
                            errorcount = error_count
                            self.errorok = 0
                        continue
                        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

                if t == 0:
                    n = symstack[-1]
                    return getattr(n,"value",None)

            if t == None:

                # We have some kind of parsing error here.  To handle
                # this, we are going to push the current token onto
                # the tokenstack and replace it with an 'error' token.
                # If there are any synchronization rules, they may
                # catch it.
                #
                # In addition to pushing the error token, we call call
                # the user defined p_error() function if this is the
                # first syntax error.  This function is only called if
                # errorcount == 0.
                if errorcount == 0 or self.errorok:
                    errorcount = error_count
                    self.errorok = 0
                    errtoken = lookahead
                    if errtoken.type == '$end':
                        errtoken = None               # End of file!
                    if self.errorfunc:
                        global errok,token,restart
                        errok = self.errok        # Set some special functions available in error recovery
                        token = get_token
                        restart = self.restart
                        if errtoken and not hasattr(errtoken,'lexer'):
                            errtoken.lexer = lexer
                        tok = self.errorfunc(errtoken)
                        del errok, token, restart   # Delete special functions

                        if self.errorok:
                            # User must have done some kind of panic
                            # mode recovery on their own.  The
                            # returned token is the next lookahead
                            lookahead = tok
                            errtoken = None
                            continue
                    else:
                        if errtoken:
                            if hasattr(errtoken,"lineno"): lineno = lookahead.lineno
                            else: lineno = 0
                            if lineno:
                                sys.stderr.write("yacc: Syntax error at line %d, token=%s\n" % (lineno, errtoken.type))
                            else:
                                sys.stderr.write("yacc: Syntax error, token=%s" % errtoken.type)
                        else:
                            sys.stderr.write("yacc: Parse error in input. EOF\n")
                            return

                else:
                    errorcount = error_count

                # case 1:  the statestack only has 1 entry on it.  If we're in this state, the
                # entire parse has been rolled back and we're completely hosed.   The token is
                # discarded and we just keep going.

                if len(statestack) <= 1 and lookahead.type != '$end':
                    lookahead = None
                    errtoken = None
                    state = 0
                    # Nuke the pushback stack
                    del lookaheadstack[:]
                    continue

                # case 2: the statestack has a couple of entries on it, but we're
                # at the end of the file. nuke the top entry and generate an error token

                # Start nuking entries on the stack
                if lookahead.type == '$end':
                    # Whoa. We're really hosed here. Bail out
                    return

                if lookahead.type != 'error':
                    sym = symstack[-1]
                    if sym.type == 'error':
                        # Hmmm. Error is on top of stack, we'll just nuke input
                        # symbol and continue
                        lookahead = None
                        continue
                    t = YaccSymbol()
                    t.type = 'error'
                    if hasattr(lookahead,"lineno"):
                        t.lineno = lookahead.lineno
                    t.value = lookahead
                    lookaheadstack.append(lookahead)
                    lookahead = t
                else:
                    symstack.pop()
                    statestack.pop()
                    state = statestack[-1]       # Potential bug fix

                continue

            # Call an error function here
            raise RuntimeError("yacc: internal parser error!!!\n")

# -----------------------------------------------------------------------------
#                          === Grammar Representation ===
#
# The following functions, classes, and variables are used to represent and
# manipulate the rules that make up a grammar. 
# -----------------------------------------------------------------------------

import re

# regex matching identifiers
_is_identifier = re.compile(r'^[a-zA-Z0-9_-]+$')

# -----------------------------------------------------------------------------
# class Production:
#
# This class stores the raw information about a single production or grammar rule.
# A grammar rule refers to a specification such as this:
#
#       expr : expr PLUS term 
#
# Here are the basic attributes defined on all productions
#
#       name     - Name of the production.  For example 'expr'
#       prod     - A list of symbols on the right side ['expr','PLUS','term']
#       prec     - Production precedence level
#       number   - Production number.
#       func     - Function that executes on reduce
#       file     - File where production function is defined
#       lineno   - Line number where production function is defined
#
# The following attributes are defined or optional.
#
#       len       - Length of the production (number of symbols on right hand side)
#       usyms     - Set of unique symbols found in the production
# -----------------------------------------------------------------------------

class Production(object):
    reduced = 0
    def __init__(self,number,name,prod,precedence=('right',0),func=None,file='',line=0):
        self.name     = name
        self.prod     = tuple(prod)
        self.number   = number
        self.func     = func
        self.callable = None
        self.file     = file
        self.line     = line
        self.prec     = precedence

        # Internal settings used during table construction
        
        self.len  = len(self.prod)   # Length of the production

        # Create a list of unique production symbols used in the production
        self.usyms = [ ]             
        for s in self.prod:
            if s not in self.usyms:
                self.usyms.append(s)

        # List of all LR items for the production
        self.lr_items = []
        self.lr_next = None

        # Create a string representation
        if self.prod:
            self.str = "%s -> %s" % (self.name," ".join(self.prod))
        else:
            self.str = "%s -> <empty>" % self.name

    def __str__(self):
        return self.str

    def __repr__(self):
        return "Production("+str(self)+")"

    def __len__(self):
        return len(self.prod)

    def __nonzero__(self):
        return 1

    def __getitem__(self,index):
        return self.prod[index]
            
    # Return the nth lr_item from the production (or None if at the end)
    def lr_item(self,n):
        if n > len(self.prod): return None
        p = LRItem(self,n)

        # Precompute the list of productions immediately following.  Hack. Remove later
        try:
            p.lr_after = Prodnames[p.prod[n+1]]
        except (IndexError,KeyError):
            p.lr_after = []
        try:
            p.lr_before = p.prod[n-1]
        except IndexError:
            p.lr_before = None

        return p
    
    # Bind the production function name to a callable
    def bind(self,pdict):
        if self.func:
            self.callable = pdict[self.func]

# This class serves as a minimal standin for Production objects when
# reading table data from files.   It only contains information
# actually used by the LR parsing engine, plus some additional
# debugging information.
class MiniProduction(object):
    def __init__(self,str,name,len,func,file,line):
        self.name     = name
        self.len      = len
        self.func     = func
        self.callable = None
        self.file     = file
        self.line     = line
        self.str      = str
    def __str__(self):
        return self.str
    def __repr__(self):
        return "MiniProduction(%s)" % self.str

    # Bind the production function name to a callable
    def bind(self,pdict):
        if self.func:
            self.callable = pdict[self.func]


# -----------------------------------------------------------------------------
# class LRItem
#
# This class represents a specific stage of parsing a production rule.  For
# example: 
#
#       expr : expr . PLUS term 
#
# In the above, the "." represents the current location of the parse.  Here
# basic attributes:
#
#       name       - Name of the production.  For example 'expr'
#       prod       - A list of symbols on the right side ['expr','.', 'PLUS','term']
#       number     - Production number.
#
#       lr_next      Next LR item. Example, if we are ' expr -> expr . PLUS term'
#                    then lr_next refers to 'expr -> expr PLUS . term'
#       lr_index   - LR item index (location of the ".") in the prod list.
#       lookaheads - LALR lookahead symbols for this item
#       len        - Length of the production (number of symbols on right hand side)
#       lr_after    - List of all productions that immediately follow
#       lr_before   - Grammar symbol immediately before
# -----------------------------------------------------------------------------

class LRItem(object):
    def __init__(self,p,n):
        self.name       = p.name
        self.prod       = list(p.prod)
        self.number     = p.number
        self.lr_index   = n
        self.lookaheads = { }
        self.prod.insert(n,".")
        self.prod       = tuple(self.prod)
        self.len        = len(self.prod)
        self.usyms      = p.usyms

    def __str__(self):
        if self.prod:
            s = "%s -> %s" % (self.name," ".join(self.prod))
        else:
            s = "%s -> <empty>" % self.name
        return s

    def __repr__(self):
        return "LRItem("+str(self)+")"

# -----------------------------------------------------------------------------
# rightmost_terminal()
#
# Return the rightmost terminal from a list of symbols.  Used in add_production()
# -----------------------------------------------------------------------------
def rightmost_terminal(symbols, terminals):
    i = len(symbols) - 1
    while i >= 0:
        if symbols[i] in terminals:
            return symbols[i]
        i -= 1
    return None

# -----------------------------------------------------------------------------
#                           === GRAMMAR CLASS ===
#
# The following class represents the contents of the specified grammar along
# with various computed properties such as first sets, follow sets, LR items, etc.
# This data is used for critical parts of the table generation process later.
# -----------------------------------------------------------------------------

class GrammarError(YaccError): pass

class Grammar(object):
    def __init__(self,terminals):
        self.Productions  = [None]  # A list of all of the productions.  The first
                                    # entry is always reserved for the purpose of
                                    # building an augmented grammar

        self.Prodnames    = { }     # A dictionary mapping the names of nonterminals to a list of all
                                    # productions of that nonterminal.

        self.Prodmap      = { }     # A dictionary that is only used to detect duplicate
                                    # productions.

        self.Terminals    = { }     # A dictionary mapping the names of terminal symbols to a
                                    # list of the rules where they are used.

        for term in terminals:
            self.Terminals[term] = []

        self.Terminals['error'] = []

        self.Nonterminals = { }     # A dictionary mapping names of nonterminals to a list
                                    # of rule numbers where they are used.

        self.First        = { }     # A dictionary of precomputed FIRST(x) symbols

        self.Follow       = { }     # A dictionary of precomputed FOLLOW(x) symbols

        self.Precedence   = { }     # Precedence rules for each terminal. Contains tuples of the
                                    # form ('right',level) or ('nonassoc', level) or ('left',level)

        self.UsedPrecedence = { }   # Precedence rules that were actually used by the grammer.
                                    # This is only used to provide error checking and to generate
                                    # a warning about unused precedence rules.

        self.Start = None           # Starting symbol for the grammar


    def __len__(self):
        return len(self.Productions)

    def __getitem__(self,index):
        return self.Productions[index]

    # -----------------------------------------------------------------------------
    # set_precedence()
    #
    # Sets the precedence for a given terminal. assoc is the associativity such as
    # 'left','right', or 'nonassoc'.  level is a numeric level.
    #
    # -----------------------------------------------------------------------------

    def set_precedence(self,term,assoc,level):
        assert self.Productions == [None],"Must call set_precedence() before add_production()"
        if term in self.Precedence:
            raise GrammarError("Precedence already specified for terminal '%s'" % term)
        if assoc not in ['left','right','nonassoc']:
            raise GrammarError("Associativity must be one of 'left','right', or 'nonassoc'")
        self.Precedence[term] = (assoc,level)
 
    # -----------------------------------------------------------------------------
    # add_production()
    #
    # Given an action function, this function assembles a production rule and
    # computes its precedence level.
    #
    # The production rule is supplied as a list of symbols.   For example,
    # a rule such as 'expr : expr PLUS term' has a production name of 'expr' and
    # symbols ['expr','PLUS','term'].
    #
    # Precedence is determined by the precedence of the right-most non-terminal
    # or the precedence of a terminal specified by %prec.
    #
    # A variety of error checks are performed to make sure production symbols
    # are valid and that %prec is used correctly.
    # -----------------------------------------------------------------------------

    def add_production(self,prodname,syms,func=None,file='',line=0):

        if prodname in self.Terminals:
            raise GrammarError("%s:%d: Illegal rule name '%s'. Already defined as a token" % (file,line,prodname))
        if prodname == 'error':
            raise GrammarError("%s:%d: Illegal rule name '%s'. error is a reserved word" % (file,line,prodname))
        if not _is_identifier.match(prodname):
            raise GrammarError("%s:%d: Illegal rule name '%s'" % (file,line,prodname))

        # Look for literal tokens 
        for n,s in enumerate(syms):
            if s[0] in "'\"":
                 try:
                     c = eval(s)
                     if (len(c) > 1):
                          raise GrammarError("%s:%d: Literal token %s in rule '%s' may only be a single character" % (file,line,s, prodname))
                     if not c in self.Terminals:
                          self.Terminals[c] = []
                     syms[n] = c
                     continue
                 except SyntaxError:
                     pass
            if not _is_identifier.match(s) and s != '%prec':
                raise GrammarError("%s:%d: Illegal name '%s' in rule '%s'" % (file,line,s, prodname))
        
        # Determine the precedence level
        if '%prec' in syms:
            if syms[-1] == '%prec':
                raise GrammarError("%s:%d: Syntax error. Nothing follows %%prec" % (file,line))
            if syms[-2] != '%prec':
                raise GrammarError("%s:%d: Syntax error. %%prec can only appear at the end of a grammar rule" % (file,line))
            precname = syms[-1]
            prodprec = self.Precedence.get(precname,None)
            if not prodprec:
                raise GrammarError("%s:%d: Nothing known about the precedence of '%s'" % (file,line,precname))
            else:
                self.UsedPrecedence[precname] = 1
            del syms[-2:]     # Drop %prec from the rule
        else:
            # If no %prec, precedence is determined by the rightmost terminal symbol
            precname = rightmost_terminal(syms,self.Terminals)
            prodprec = self.Precedence.get(precname,('right',0)) 
            
        # See if the rule is already in the rulemap
        map = "%s -> %s" % (prodname,syms)
        if map in self.Prodmap:
            m = self.Prodmap[map]
            raise GrammarError("%s:%d: Duplicate rule %s. " % (file,line, m) +
                               "Previous definition at %s:%d" % (m.file, m.line))

        # From this point on, everything is valid.  Create a new Production instance
        pnumber  = len(self.Productions)
        if not prodname in self.Nonterminals:
            self.Nonterminals[prodname] = [ ]

        # Add the production number to Terminals and Nonterminals
        for t in syms:
            if t in self.Terminals:
                self.Terminals[t].append(pnumber)
            else:
                if not t in self.Nonterminals:
                    self.Nonterminals[t] = [ ]
                self.Nonterminals[t].append(pnumber)

        # Create a production and add it to the list of productions
        p = Production(pnumber,prodname,syms,prodprec,func,file,line)
        self.Productions.append(p)
        self.Prodmap[map] = p

        # Add to the global productions list
        try:
            self.Prodnames[prodname].append(p)
        except KeyError:
            self.Prodnames[prodname] = [ p ]
        return 0

    # -----------------------------------------------------------------------------
    # set_start()
    #
    # Sets the starting symbol and creates the augmented grammar.  Production 
    # rule 0 is S' -> start where start is the start symbol.
    # -----------------------------------------------------------------------------

    def set_start(self,start=None):
        if not start:
            start = self.Productions[1].name
        if start not in self.Nonterminals:
            raise GrammarError("start symbol %s undefined" % start)
        self.Productions[0] = Production(0,"S'",[start])
        self.Nonterminals[start].append(0)
        self.Start = start

    # -----------------------------------------------------------------------------
    # find_unreachable()
    #
    # Find all of the nonterminal symbols that can't be reached from the starting
    # symbol.  Returns a list of nonterminals that can't be reached.
    # -----------------------------------------------------------------------------

    def find_unreachable(self):
        
        # Mark all symbols that are reachable from a symbol s
        def mark_reachable_from(s):
            if reachable[s]:
                # We've already reached symbol s.
                return
            reachable[s] = 1
            for p in self.Prodnames.get(s,[]):
                for r in p.prod:
                    mark_reachable_from(r)

        reachable   = { }
        for s in list(self.Terminals) + list(self.Nonterminals):
            reachable[s] = 0

        mark_reachable_from( self.Productions[0].prod[0] )

        return [s for s in list(self.Nonterminals)
                        if not reachable[s]]
    
    # -----------------------------------------------------------------------------
    # infinite_cycles()
    #
    # This function looks at the various parsing rules and tries to detect
    # infinite recursion cycles (grammar rules where there is no possible way
    # to derive a string of only terminals).
    # -----------------------------------------------------------------------------

    def infinite_cycles(self):
        terminates = {}

        # Terminals:
        for t in self.Terminals:
            terminates[t] = 1

        terminates['$end'] = 1

        # Nonterminals:

        # Initialize to false:
        for n in self.Nonterminals:
            terminates[n] = 0

        # Then propagate termination until no change:
        while 1:
            some_change = 0
            for (n,pl) in self.Prodnames.items():
                # Nonterminal n terminates iff any of its productions terminates.
                for p in pl:
                    # Production p terminates iff all of its rhs symbols terminate.
                    for s in p.prod:
                        if not terminates[s]:
                            # The symbol s does not terminate,
                            # so production p does not terminate.
                            p_terminates = 0
                            break
                    else:
                        # didn't break from the loop,
                        # so every symbol s terminates
                        # so production p terminates.
                        p_terminates = 1

                    if p_terminates:
                        # symbol n terminates!
                        if not terminates[n]:
                            terminates[n] = 1
                            some_change = 1
                        # Don't need to consider any more productions for this n.
                        break

            if not some_change:
                break

        infinite = []
        for (s,term) in terminates.items():
            if not term:
                if not s in self.Prodnames and not s in self.Terminals and s != 'error':
                    # s is used-but-not-defined, and we've already warned of that,
                    # so it would be overkill to say that it's also non-terminating.
                    pass
                else:
                    infinite.append(s)

        return infinite


    # -----------------------------------------------------------------------------
    # undefined_symbols()
    #
    # Find all symbols that were used the grammar, but not defined as tokens or
    # grammar rules.  Returns a list of tuples (sym, prod) where sym in the symbol
    # and prod is the production where the symbol was used. 
    # -----------------------------------------------------------------------------
    def undefined_symbols(self):
        result = []
        for p in self.Productions:
            if not p: continue

            for s in p.prod:
                if not s in self.Prodnames and not s in self.Terminals and s != 'error':
                    result.append((s,p))
        return result

    # -----------------------------------------------------------------------------
    # unused_terminals()
    #
    # Find all terminals that were defined, but not used by the grammar.  Returns
    # a list of all symbols.
    # -----------------------------------------------------------------------------
    def unused_terminals(self):
        unused_tok = []
        for s,v in self.Terminals.items():
            if s != 'error' and not v:
                unused_tok.append(s)

        return unused_tok

    # ------------------------------------------------------------------------------
    # unused_rules()
    #
    # Find all grammar rules that were defined,  but not used (maybe not reachable)
    # Returns a list of productions.
    # ------------------------------------------------------------------------------

    def unused_rules(self):
        unused_prod = []
        for s,v in self.Nonterminals.items():
            if not v:
                p = self.Prodnames[s][0]
                unused_prod.append(p)
        return unused_prod

    # -----------------------------------------------------------------------------
    # unused_precedence()
    #
    # Returns a list of tuples (term,precedence) corresponding to precedence
    # rules that were never used by the grammar.  term is the name of the terminal
    # on which precedence was applied and precedence is a string such as 'left' or
    # 'right' corresponding to the type of precedence. 
    # -----------------------------------------------------------------------------

    def unused_precedence(self):
        unused = []
        for termname in self.Precedence:
            if not (termname in self.Terminals or termname in self.UsedPrecedence):
                unused.append((termname,self.Precedence[termname][0]))
                
        return unused

    # -------------------------------------------------------------------------
    # _first()
    #
    # Compute the value of FIRST1(beta) where beta is a tuple of symbols.
    #
    # During execution of compute_first1, the result may be incomplete.
    # Afterward (e.g., when called from compute_follow()), it will be complete.
    # -------------------------------------------------------------------------
    def _first(self,beta):

        # We are computing First(x1,x2,x3,...,xn)
        result = [ ]
        for x in beta:
            x_produces_empty = 0

            # Add all the non-<empty> symbols of First[x] to the result.
            for f in self.First[x]:
                if f == '<empty>':
                    x_produces_empty = 1
                else:
                    if f not in result: result.append(f)

            if x_produces_empty:
                # We have to consider the next x in beta,
                # i.e. stay in the loop.
                pass
            else:
                # We don't have to consider any further symbols in beta.
                break
        else:
            # There was no 'break' from the loop,
            # so x_produces_empty was true for all x in beta,
            # so beta produces empty as well.
            result.append('<empty>')

        return result

    # -------------------------------------------------------------------------
    # compute_first()
    #
    # Compute the value of FIRST1(X) for all symbols
    # -------------------------------------------------------------------------
    def compute_first(self):
        if self.First:
            return self.First

        # Terminals:
        for t in self.Terminals:
            self.First[t] = [t]

        self.First['$end'] = ['$end']

        # Nonterminals:

        # Initialize to the empty set:
        for n in self.Nonterminals:
            self.First[n] = []

        # Then propagate symbols until no change:
        while 1:
            some_change = 0
            for n in self.Nonterminals:
                for p in self.Prodnames[n]:
                    for f in self._first(p.prod):
                        if f not in self.First[n]:
                            self.First[n].append( f )
                            some_change = 1
            if not some_change:
                break
        
        return self.First

    # ---------------------------------------------------------------------
    # compute_follow()
    #
    # Computes all of the follow sets for every non-terminal symbol.  The
    # follow set is the set of all symbols that might follow a given
    # non-terminal.  See the Dragon book, 2nd Ed. p. 189.
    # ---------------------------------------------------------------------
    def compute_follow(self,start=None):
        # If already computed, return the result
        if self.Follow:
            return self.Follow

        # If first sets not computed yet, do that first.
        if not self.First:
            self.compute_first()

        # Add '$end' to the follow list of the start symbol
        for k in self.Nonterminals:
            self.Follow[k] = [ ]

        if not start:
            start = self.Productions[1].name

        self.Follow[start] = [ '$end' ]

        while 1:
            didadd = 0
            for p in self.Productions[1:]:
                # Here is the production set
                for i in range(len(p.prod)):
                    B = p.prod[i]
                    if B in self.Nonterminals:
                        # Okay. We got a non-terminal in a production
                        fst = self._first(p.prod[i+1:])
                        hasempty = 0
                        for f in fst:
                            if f != '<empty>' and f not in self.Follow[B]:
                                self.Follow[B].append(f)
                                didadd = 1
                            if f == '<empty>':
                                hasempty = 1
                        if hasempty or i == (len(p.prod)-1):
                            # Add elements of follow(a) to follow(b)
                            for f in self.Follow[p.name]:
                                if f not in self.Follow[B]:
                                    self.Follow[B].append(f)
                                    didadd = 1
            if not didadd: break
        return self.Follow


    # -----------------------------------------------------------------------------
    # build_lritems()
    #
    # This function walks the list of productions and builds a complete set of the
    # LR items.  The LR items are stored in two ways:  First, they are uniquely
    # numbered and placed in the list _lritems.  Second, a linked list of LR items
    # is built for each production.  For example:
    #
    #   E -> E PLUS E
    #
    # Creates the list
    #
    #  [E -> . E PLUS E, E -> E . PLUS E, E -> E PLUS . E, E -> E PLUS E . ]
    # -----------------------------------------------------------------------------

    def build_lritems(self):
        for p in self.Productions:
            lastlri = p
            i = 0
            lr_items = []
            while 1:
                if i > len(p):
                    lri = None
                else:
                    lri = LRItem(p,i)
                    # Precompute the list of productions immediately following
                    try:
                        lri.lr_after = self.Prodnames[lri.prod[i+1]]
                    except (IndexError,KeyError):
                        lri.lr_after = []
                    try:
                        lri.lr_before = lri.prod[i-1]
                    except IndexError:
                        lri.lr_before = None

                lastlri.lr_next = lri
                if not lri: break
                lr_items.append(lri)
                lastlri = lri
                i += 1
            p.lr_items = lr_items

# -----------------------------------------------------------------------------
#                            == Class LRTable ==
#
# This basic class represents a basic table of LR parsing information.  
# Methods for generating the tables are not defined here.  They are defined
# in the derived class LRGeneratedTable.
# -----------------------------------------------------------------------------

class VersionError(YaccError): pass

class LRTable(object):
    def __init__(self):
        self.lr_action = None
        self.lr_goto = None
        self.lr_productions = None
        self.lr_method = None

    def read_table(self,module):
        if isinstance(module,types.ModuleType):
            parsetab = module
        else:
            if sys.version_info[0] < 3:
                exec("import %s as parsetab" % module)
            else:
                env = { }
                exec("import %s as parsetab" % module, env, env)
                parsetab = env['parsetab']

        if parsetab._tabversion != __tabversion__:
            raise VersionError("yacc table file version is out of date")

        self.lr_action = parsetab._lr_action
        self.lr_goto = parsetab._lr_goto

        self.lr_productions = []
        for p in parsetab._lr_productions:
            self.lr_productions.append(MiniProduction(*p))

        self.lr_method = parsetab._lr_method
        return parsetab._lr_signature

    def read_pickle(self,filename):
        try:
            import cPickle as pickle
        except ImportError:
            import pickle

        in_f = open(filename,"rb")

        tabversion = pickle.load(in_f)
        if tabversion != __tabversion__:
            raise VersionError("yacc table file version is out of date")
        self.lr_method = pickle.load(in_f)
        signature      = pickle.load(in_f)
        self.lr_action = pickle.load(in_f)
        self.lr_goto   = pickle.load(in_f)
        productions    = pickle.load(in_f)

        self.lr_productions = []
        for p in productions:
            self.lr_productions.append(MiniProduction(*p))

        in_f.close()
        return signature

    # Bind all production function names to callable objects in pdict
    def bind_callables(self,pdict):
        for p in self.lr_productions:
            p.bind(pdict)
    
# -----------------------------------------------------------------------------
#                           === LR Generator ===
#
# The following classes and functions are used to generate LR parsing tables on 
# a grammar.
# -----------------------------------------------------------------------------

# -----------------------------------------------------------------------------
# digraph()
# traverse()
#
# The following two functions are used to compute set valued functions
# of the form:
#
#     F(x) = F'(x) U U{F(y) | x R y}
#
# This is used to compute the values of Read() sets as well as FOLLOW sets
# in LALR(1) generation.
#
# Inputs:  X    - An input set
#          R    - A relation
#          FP   - Set-valued function
# ------------------------------------------------------------------------------

def digraph(X,R,FP):
    N = { }
    for x in X:
       N[x] = 0
    stack = []
    F = { }
    for x in X:
        if N[x] == 0: traverse(x,N,stack,F,X,R,FP)
    return F

def traverse(x,N,stack,F,X,R,FP):
    stack.append(x)
    d = len(stack)
    N[x] = d
    F[x] = FP(x)             # F(X) <- F'(x)

    rel = R(x)               # Get y's related to x
    for y in rel:
        if N[y] == 0:
             traverse(y,N,stack,F,X,R,FP)
        N[x] = min(N[x],N[y])
        for a in F.get(y,[]):
            if a not in F[x]: F[x].append(a)
    if N[x] == d:
       N[stack[-1]] = MAXINT
       F[stack[-1]] = F[x]
       element = stack.pop()
       while element != x:
           N[stack[-1]] = MAXINT
           F[stack[-1]] = F[x]
           element = stack.pop()

class LALRError(YaccError): pass

# -----------------------------------------------------------------------------
#                             == LRGeneratedTable ==
#
# This class implements the LR table generation algorithm.  There are no
# public methods except for write()
# -----------------------------------------------------------------------------

class LRGeneratedTable(LRTable):
    def __init__(self,grammar,method='LALR',log=None):
        if method not in ['SLR','LALR']:
            raise LALRError("Unsupported method %s" % method)

        self.grammar = grammar
        self.lr_method = method

        # Set up the logger
        if not log:
            log = NullLogger()
        self.log = log

        # Internal attributes
        self.lr_action     = {}        # Action table
        self.lr_goto       = {}        # Goto table
        self.lr_productions  = grammar.Productions    # Copy of grammar Production array
        self.lr_goto_cache = {}        # Cache of computed gotos
        self.lr0_cidhash   = {}        # Cache of closures

        self._add_count    = 0         # Internal counter used to detect cycles

        # Diagonistic information filled in by the table generator
        self.sr_conflict   = 0
        self.rr_conflict   = 0
        self.conflicts     = []        # List of conflicts

        self.sr_conflicts  = []
        self.rr_conflicts  = []

        # Build the tables
        self.grammar.build_lritems()
        self.grammar.compute_first()
        self.grammar.compute_follow()
        self.lr_parse_table()

    # Compute the LR(0) closure operation on I, where I is a set of LR(0) items.

    def lr0_closure(self,I):
        self._add_count += 1

        # Add everything in I to J
        J = I[:]
        didadd = 1
        while didadd:
            didadd = 0
            for j in J:
                for x in j.lr_after:
                    if getattr(x,"lr0_added",0) == self._add_count: continue
                    # Add B --> .G to J
                    J.append(x.lr_next)
                    x.lr0_added = self._add_count
                    didadd = 1

        return J

    # Compute the LR(0) goto function goto(I,X) where I is a set
    # of LR(0) items and X is a grammar symbol.   This function is written
    # in a way that guarantees uniqueness of the generated goto sets
    # (i.e. the same goto set will never be returned as two different Python
    # objects).  With uniqueness, we can later do fast set comparisons using
    # id(obj) instead of element-wise comparison.

    def lr0_goto(self,I,x):
        # First we look for a previously cached entry
        g = self.lr_goto_cache.get((id(I),x),None)
        if g: return g

        # Now we generate the goto set in a way that guarantees uniqueness
        # of the result

        s = self.lr_goto_cache.get(x,None)
        if not s:
            s = { }
            self.lr_goto_cache[x] = s

        gs = [ ]
        for p in I:
            n = p.lr_next
            if n and n.lr_before == x:
                s1 = s.get(id(n),None)
                if not s1:
                    s1 = { }
                    s[id(n)] = s1
                gs.append(n)
                s = s1
        g = s.get('$end',None)
        if not g:
            if gs:
                g = self.lr0_closure(gs)
                s['$end'] = g
            else:
                s['$end'] = gs
        self.lr_goto_cache[(id(I),x)] = g
        return g

    # Compute the LR(0) sets of item function
    def lr0_items(self):

        C = [ self.lr0_closure([self.grammar.Productions[0].lr_next]) ]
        i = 0
        for I in C:
            self.lr0_cidhash[id(I)] = i
            i += 1

        # Loop over the items in C and each grammar symbols
        i = 0
        while i < len(C):
            I = C[i]
            i += 1

            # Collect all of the symbols that could possibly be in the goto(I,X) sets
            asyms = { }
            for ii in I:
                for s in ii.usyms:
                    asyms[s] = None

            for x in asyms:
                g = self.lr0_goto(I,x)
                if not g:  continue
                if id(g) in self.lr0_cidhash: continue
                self.lr0_cidhash[id(g)] = len(C)
                C.append(g)

        return C

    # -----------------------------------------------------------------------------
    #                       ==== LALR(1) Parsing ====
    #
    # LALR(1) parsing is almost exactly the same as SLR except that instead of
    # relying upon Follow() sets when performing reductions, a more selective
    # lookahead set that incorporates the state of the LR(0) machine is utilized.
    # Thus, we mainly just have to focus on calculating the lookahead sets.
    #
    # The method used here is due to DeRemer and Pennelo (1982).
    #
    # DeRemer, F. L., and T. J. Pennelo: "Efficient Computation of LALR(1)
    #     Lookahead Sets", ACM Transactions on Programming Languages and Systems,
    #     Vol. 4, No. 4, Oct. 1982, pp. 615-649
    #
    # Further details can also be found in:
    #
    #  J. Tremblay and P. Sorenson, "The Theory and Practice of Compiler Writing",
    #      McGraw-Hill Book Company, (1985).
    #
    # -----------------------------------------------------------------------------

    # -----------------------------------------------------------------------------
    # compute_nullable_nonterminals()
    #
    # Creates a dictionary containing all of the non-terminals that might produce
    # an empty production.
    # -----------------------------------------------------------------------------

    def compute_nullable_nonterminals(self):
        nullable = {}
        num_nullable = 0
        while 1:
           for p in self.grammar.Productions[1:]:
               if p.len == 0:
                    nullable[p.name] = 1
                    continue
               for t in p.prod:
                    if not t in nullable: break
               else:
                    nullable[p.name] = 1
           if len(nullable) == num_nullable: break
           num_nullable = len(nullable)
        return nullable

    # -----------------------------------------------------------------------------
    # find_nonterminal_trans(C)
    #
    # Given a set of LR(0) items, this functions finds all of the non-terminal
    # transitions.    These are transitions in which a dot appears immediately before
    # a non-terminal.   Returns a list of tuples of the form (state,N) where state
    # is the state number and N is the nonterminal symbol.
    #
    # The input C is the set of LR(0) items.
    # -----------------------------------------------------------------------------

    def find_nonterminal_transitions(self,C):
         trans = []
         for state in range(len(C)):
             for p in C[state]:
                 if p.lr_index < p.len - 1:
                      t = (state,p.prod[p.lr_index+1])
                      if t[1] in self.grammar.Nonterminals:
                            if t not in trans: trans.append(t)
             state = state + 1
         return trans

    # -----------------------------------------------------------------------------
    # dr_relation()
    #
    # Computes the DR(p,A) relationships for non-terminal transitions.  The input
    # is a tuple (state,N) where state is a number and N is a nonterminal symbol.
    #
    # Returns a list of terminals.
    # -----------------------------------------------------------------------------

    def dr_relation(self,C,trans,nullable):
        dr_set = { }
        state,N = trans
        terms = []

        g = self.lr0_goto(C[state],N)
        for p in g:
           if p.lr_index < p.len - 1:
               a = p.prod[p.lr_index+1]
               if a in self.grammar.Terminals:
                   if a not in terms: terms.append(a)

        # This extra bit is to handle the start state
        if state == 0 and N == self.grammar.Productions[0].prod[0]:
           terms.append('$end')

        return terms

    # -----------------------------------------------------------------------------
    # reads_relation()
    #
    # Computes the READS() relation (p,A) READS (t,C).
    # -----------------------------------------------------------------------------

    def reads_relation(self,C, trans, empty):
        # Look for empty transitions
        rel = []
        state, N = trans

        g = self.lr0_goto(C[state],N)
        j = self.lr0_cidhash.get(id(g),-1)
        for p in g:
            if p.lr_index < p.len - 1:
                 a = p.prod[p.lr_index + 1]
                 if a in empty:
                      rel.append((j,a))

        return rel

    # -----------------------------------------------------------------------------
    # compute_lookback_includes()
    #
    # Determines the lookback and includes relations
    #
    # LOOKBACK:
    #
    # This relation is determined by running the LR(0) state machine forward.
    # For example, starting with a production "N : . A B C", we run it forward
    # to obtain "N : A B C ."   We then build a relationship between this final
    # state and the starting state.   These relationships are stored in a dictionary
    # lookdict.
    #
    # INCLUDES:
    #
    # Computes the INCLUDE() relation (p,A) INCLUDES (p',B).
    #
    # This relation is used to determine non-terminal transitions that occur
    # inside of other non-terminal transition states.   (p,A) INCLUDES (p', B)
    # if the following holds:
    #
    #       B -> LAT, where T -> epsilon and p' -L-> p
    #
    # L is essentially a prefix (which may be empty), T is a suffix that must be
    # able to derive an empty string.  State p' must lead to state p with the string L.
    #
    # -----------------------------------------------------------------------------

    def compute_lookback_includes(self,C,trans,nullable):

        lookdict = {}          # Dictionary of lookback relations
        includedict = {}       # Dictionary of include relations

        # Make a dictionary of non-terminal transitions
        dtrans = {}
        for t in trans:
            dtrans[t] = 1

        # Loop over all transitions and compute lookbacks and includes
        for state,N in trans:
            lookb = []
            includes = []
            for p in C[state]:
                if p.name != N: continue

                # Okay, we have a name match.  We now follow the production all the way
                # through the state machine until we get the . on the right hand side

                lr_index = p.lr_index
                j = state
                while lr_index < p.len - 1:
                     lr_index = lr_index + 1
                     t = p.prod[lr_index]

                     # Check to see if this symbol and state are a non-terminal transition
                     if (j,t) in dtrans:
                           # Yes.  Okay, there is some chance that this is an includes relation
                           # the only way to know for certain is whether the rest of the
                           # production derives empty

                           li = lr_index + 1
                           while li < p.len:
                                if p.prod[li] in self.grammar.Terminals: break      # No forget it
                                if not p.prod[li] in nullable: break
                                li = li + 1
                           else:
                                # Appears to be a relation between (j,t) and (state,N)
                                includes.append((j,t))

                     g = self.lr0_goto(C[j],t)               # Go to next set
                     j = self.lr0_cidhash.get(id(g),-1)     # Go to next state

                # When we get here, j is the final state, now we have to locate the production
                for r in C[j]:
                     if r.name != p.name: continue
                     if r.len != p.len:   continue
                     i = 0
                     # This look is comparing a production ". A B C" with "A B C ."
                     while i < r.lr_index:
                          if r.prod[i] != p.prod[i+1]: break
                          i = i + 1
                     else:
                          lookb.append((j,r))
            for i in includes:
                 if not i in includedict: includedict[i] = []
                 includedict[i].append((state,N))
            lookdict[(state,N)] = lookb

        return lookdict,includedict

    # -----------------------------------------------------------------------------
    # compute_read_sets()
    #
    # Given a set of LR(0) items, this function computes the read sets.
    #
    # Inputs:  C        =  Set of LR(0) items
    #          ntrans   = Set of nonterminal transitions
    #          nullable = Set of empty transitions
    #
    # Returns a set containing the read sets
    # -----------------------------------------------------------------------------

    def compute_read_sets(self,C, ntrans, nullable):
        FP = lambda x: self.dr_relation(C,x,nullable)
        R =  lambda x: self.reads_relation(C,x,nullable)
        F = digraph(ntrans,R,FP)
        return F

    # -----------------------------------------------------------------------------
    # compute_follow_sets()
    #
    # Given a set of LR(0) items, a set of non-terminal transitions, a readset,
    # and an include set, this function computes the follow sets
    #
    # Follow(p,A) = Read(p,A) U U {Follow(p',B) | (p,A) INCLUDES (p',B)}
    #
    # Inputs:
    #            ntrans     = Set of nonterminal transitions
    #            readsets   = Readset (previously computed)
    #            inclsets   = Include sets (previously computed)
    #
    # Returns a set containing the follow sets
    # -----------------------------------------------------------------------------

    def compute_follow_sets(self,ntrans,readsets,inclsets):
         FP = lambda x: readsets[x]
         R  = lambda x: inclsets.get(x,[])
         F = digraph(ntrans,R,FP)
         return F

    # -----------------------------------------------------------------------------
    # add_lookaheads()
    #
    # Attaches the lookahead symbols to grammar rules.
    #
    # Inputs:    lookbacks         -  Set of lookback relations
    #            followset         -  Computed follow set
    #
    # This function directly attaches the lookaheads to productions contained
    # in the lookbacks set
    # -----------------------------------------------------------------------------

    def add_lookaheads(self,lookbacks,followset):
        for trans,lb in lookbacks.items():
            # Loop over productions in lookback
            for state,p in lb:
                 if not state in p.lookaheads:
                      p.lookaheads[state] = []
                 f = followset.get(trans,[])
                 for a in f:
                      if a not in p.lookaheads[state]: p.lookaheads[state].append(a)

    # -----------------------------------------------------------------------------
    # add_lalr_lookaheads()
    #
    # This function does all of the work of adding lookahead information for use
    # with LALR parsing
    # -----------------------------------------------------------------------------

    def add_lalr_lookaheads(self,C):
        # Determine all of the nullable nonterminals
        nullable = self.compute_nullable_nonterminals()

        # Find all non-terminal transitions
        trans = self.find_nonterminal_transitions(C)

        # Compute read sets
        readsets = self.compute_read_sets(C,trans,nullable)

        # Compute lookback/includes relations
        lookd, included = self.compute_lookback_includes(C,trans,nullable)

        # Compute LALR FOLLOW sets
        followsets = self.compute_follow_sets(trans,readsets,included)

        # Add all of the lookaheads
        self.add_lookaheads(lookd,followsets)

    # -----------------------------------------------------------------------------
    # lr_parse_table()
    #
    # This function constructs the parse tables for SLR or LALR
    # -----------------------------------------------------------------------------
    def lr_parse_table(self):
        Productions = self.grammar.Productions
        Precedence  = self.grammar.Precedence
        goto   = self.lr_goto         # Goto array
        action = self.lr_action       # Action array
        log    = self.log             # Logger for output

        actionp = { }                 # Action production array (temporary)
        
        log.info("Parsing method: %s", self.lr_method)

        # Step 1: Construct C = { I0, I1, ... IN}, collection of LR(0) items
        # This determines the number of states

        C = self.lr0_items()

        if self.lr_method == 'LALR':
            self.add_lalr_lookaheads(C)

        # Build the parser table, state by state
        st = 0
        for I in C:
            # Loop over each production in I
            actlist = [ ]              # List of actions
            st_action  = { }
            st_actionp = { }
            st_goto    = { }
            log.info("")
            log.info("state %d", st)
            log.info("")
            for p in I:
                log.info("    (%d) %s", p.number, str(p))
            log.info("")

            for p in I:
                    if p.len == p.lr_index + 1:
                        if p.name == "S'":
                            # Start symbol. Accept!
                            st_action["$end"] = 0
                            st_actionp["$end"] = p
                        else:
                            # We are at the end of a production.  Reduce!
                            if self.lr_method == 'LALR':
                                laheads = p.lookaheads[st]
                            else:
                                laheads = self.grammar.Follow[p.name]
                            for a in laheads:
                                actlist.append((a,p,"reduce using rule %d (%s)" % (p.number,p)))
                                r = st_action.get(a,None)
                                if r is not None:
                                    # Whoa. Have a shift/reduce or reduce/reduce conflict
                                    if r > 0:
                                        # Need to decide on shift or reduce here
                                        # By default we favor shifting. Need to add
                                        # some precedence rules here.
                                        sprec,slevel = Productions[st_actionp[a].number].prec
                                        rprec,rlevel = Precedence.get(a,('right',0))
                                        if (slevel < rlevel) or ((slevel == rlevel) and (rprec == 'left')):
                                            # We really need to reduce here.
                                            st_action[a] = -p.number
                                            st_actionp[a] = p
                                            if not slevel and not rlevel:
                                                log.info("  ! shift/reduce conflict for %s resolved as reduce",a)
                                                self.sr_conflicts.append((st,a,'reduce'))
                                            Productions[p.number].reduced += 1
                                        elif (slevel == rlevel) and (rprec == 'nonassoc'):
                                            st_action[a] = None
                                        else:
                                            # Hmmm. Guess we'll keep the shift
                                            if not rlevel:
                                                log.info("  ! shift/reduce conflict for %s resolved as shift",a)
                                                self.sr_conflicts.append((st,a,'shift'))
                                    elif r < 0:
                                        # Reduce/reduce conflict.   In this case, we favor the rule
                                        # that was defined first in the grammar file
                                        oldp = Productions[-r]
                                        pp = Productions[p.number]
                                        if oldp.line > pp.line:
                                            st_action[a] = -p.number
                                            st_actionp[a] = p
                                            chosenp,rejectp = pp,oldp
                                            Productions[p.number].reduced += 1
                                            Productions[oldp.number].reduced -= 1
                                        else:
                                            chosenp,rejectp = oldp,pp
                                        self.rr_conflicts.append((st,chosenp,rejectp))
                                        log.info("  ! reduce/reduce conflict for %s resolved using rule %d (%s)", a,st_actionp[a].number, st_actionp[a])
                                    else:
                                        raise LALRError("Unknown conflict in state %d" % st)
                                else:
                                    st_action[a] = -p.number
                                    st_actionp[a] = p
                                    Productions[p.number].reduced += 1
                    else:
                        i = p.lr_index
                        a = p.prod[i+1]       # Get symbol right after the "."
                        if a in self.grammar.Terminals:
                            g = self.lr0_goto(I,a)
                            j = self.lr0_cidhash.get(id(g),-1)
                            if j >= 0:
                                # We are in a shift state
                                actlist.append((a,p,"shift and go to state %d" % j))
                                r = st_action.get(a,None)
                                if r is not None:
                                    # Whoa have a shift/reduce or shift/shift conflict
                                    if r > 0:
                                        if r != j:
                                            raise LALRError("Shift/shift conflict in state %d" % st)
                                    elif r < 0:
                                        # Do a precedence check.
                                        #   -  if precedence of reduce rule is higher, we reduce.
                                        #   -  if precedence of reduce is same and left assoc, we reduce.
                                        #   -  otherwise we shift
                                        rprec,rlevel = Productions[st_actionp[a].number].prec
                                        sprec,slevel = Precedence.get(a,('right',0))
                                        if (slevel > rlevel) or ((slevel == rlevel) and (rprec == 'right')):
                                            # We decide to shift here... highest precedence to shift
                                            Productions[st_actionp[a].number].reduced -= 1
                                            st_action[a] = j
                                            st_actionp[a] = p
                                            if not rlevel:
                                                log.info("  ! shift/reduce conflict for %s resolved as shift",a)
                                                self.sr_conflicts.append((st,a,'shift'))
                                        elif (slevel == rlevel) and (rprec == 'nonassoc'):
                                            st_action[a] = None
                                        else:
                                            # Hmmm. Guess we'll keep the reduce
                                            if not slevel and not rlevel:
                                                log.info("  ! shift/reduce conflict for %s resolved as reduce",a)
                                                self.sr_conflicts.append((st,a,'reduce'))

                                    else:
                                        raise LALRError("Unknown conflict in state %d" % st)
                                else:
                                    st_action[a] = j
                                    st_actionp[a] = p

            # Print the actions associated with each terminal
            _actprint = { }
            for a,p,m in actlist:
                if a in st_action:
                    if p is st_actionp[a]:
                        log.info("    %-15s %s",a,m)
                        _actprint[(a,m)] = 1
            log.info("")
            # Print the actions that were not used. (debugging)
            not_used = 0
            for a,p,m in actlist:
                if a in st_action:
                    if p is not st_actionp[a]:
                        if not (a,m) in _actprint:
                            log.debug("  ! %-15s [ %s ]",a,m)
                            not_used = 1
                            _actprint[(a,m)] = 1
            if not_used:
                log.debug("")

            # Construct the goto table for this state

            nkeys = { }
            for ii in I:
                for s in ii.usyms:
                    if s in self.grammar.Nonterminals:
                        nkeys[s] = None
            for n in nkeys:
                g = self.lr0_goto(I,n)
                j = self.lr0_cidhash.get(id(g),-1)
                if j >= 0:
                    st_goto[n] = j
                    log.info("    %-30s shift and go to state %d",n,j)

            action[st] = st_action
            actionp[st] = st_actionp
            goto[st] = st_goto
            st += 1


    # -----------------------------------------------------------------------------
    # write()
    #
    # This function writes the LR parsing tables to a file
    # -----------------------------------------------------------------------------

    def write_table(self,modulename,outputdir='',signature=""):
        basemodulename = modulename.split(".")[-1]
        filename = os.path.join(outputdir,basemodulename) + ".py"
        try:
            f = open(filename,"w")

            f.write("""
# %s
# This file is automatically generated. Do not edit.
_tabversion = %r

_lr_method = %r

_lr_signature = %r
    """ % (filename, __tabversion__, self.lr_method, signature))

            # Change smaller to 0 to go back to original tables
            smaller = 1

            # Factor out names to try and make smaller
            if smaller:
                items = { }

                for s,nd in self.lr_action.items():
                   for name,v in nd.items():
                      i = items.get(name)
                      if not i:
                         i = ([],[])
                         items[name] = i
                      i[0].append(s)
                      i[1].append(v)

                f.write("\n_lr_action_items = {")
                for k,v in items.items():
                    f.write("%r:([" % k)
                    for i in v[0]:
                        f.write("%r," % i)
                    f.write("],[")
                    for i in v[1]:
                        f.write("%r," % i)

                    f.write("]),")
                f.write("}\n")

                f.write("""
_lr_action = { }
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = { }
      _lr_action[_x][_k] = _y
del _lr_action_items
""")

            else:
                f.write("\n_lr_action = { ");
                for k,v in self.lr_action.items():
                    f.write("(%r,%r):%r," % (k[0],k[1],v))
                f.write("}\n");

            if smaller:
                # Factor out names to try and make smaller
                items = { }

                for s,nd in self.lr_goto.items():
                   for name,v in nd.items():
                      i = items.get(name)
                      if not i:
                         i = ([],[])
                         items[name] = i
                      i[0].append(s)
                      i[1].append(v)

                f.write("\n_lr_goto_items = {")
                for k,v in items.items():
                    f.write("%r:([" % k)
                    for i in v[0]:
                        f.write("%r," % i)
                    f.write("],[")
                    for i in v[1]:
                        f.write("%r," % i)

                    f.write("]),")
                f.write("}\n")

                f.write("""
_lr_goto = { }
for _k, _v in _lr_goto_items.items():
   for _x,_y in zip(_v[0],_v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = { }
       _lr_goto[_x][_k] = _y
del _lr_goto_items
""")
            else:
                f.write("\n_lr_goto = { ");
                for k,v in self.lr_goto.items():
                    f.write("(%r,%r):%r," % (k[0],k[1],v))
                f.write("}\n");

            # Write production table
            f.write("_lr_productions = [\n")
            for p in self.lr_productions:
                if p.func:
                    f.write("  (%r,%r,%d,%r,%r,%d),\n" % (p.str,p.name, p.len, p.func,p.file,p.line))
                else:
                    f.write("  (%r,%r,%d,None,None,None),\n" % (str(p),p.name, p.len))
            f.write("]\n")
            f.close()

        except IOError:
            e = sys.exc_info()[1]
            sys.stderr.write("Unable to create '%s'\n" % filename)
            sys.stderr.write(str(e)+"\n")
            return


    # -----------------------------------------------------------------------------
    # pickle_table()
    #
    # This function pickles the LR parsing tables to a supplied file object
    # -----------------------------------------------------------------------------

    def pickle_table(self,filename,signature=""):
        try:
            import cPickle as pickle
        except ImportError:
            import pickle
        outf = open(filename,"wb")
        pickle.dump(__tabversion__,outf,pickle_protocol)
        pickle.dump(self.lr_method,outf,pickle_protocol)
        pickle.dump(signature,outf,pickle_protocol)
        pickle.dump(self.lr_action,outf,pickle_protocol)
        pickle.dump(self.lr_goto,outf,pickle_protocol)

        outp = []
        for p in self.lr_productions:
            if p.func:
                outp.append((p.str,p.name, p.len, p.func,p.file,p.line))
            else:
                outp.append((str(p),p.name,p.len,None,None,None))
        pickle.dump(outp,outf,pickle_protocol)
        outf.close()

# -----------------------------------------------------------------------------
#                            === INTROSPECTION ===
#
# The following functions and classes are used to implement the PLY
# introspection features followed by the yacc() function itself.
# -----------------------------------------------------------------------------

# -----------------------------------------------------------------------------
# get_caller_module_dict()
#
# This function returns a dictionary containing all of the symbols defined within
# a caller further down the call stack.  This is used to get the environment
# associated with the yacc() call if none was provided.
# -----------------------------------------------------------------------------

def get_caller_module_dict(levels):
    try:
        raise RuntimeError
    except RuntimeError:
        e,b,t = sys.exc_info()
        f = t.tb_frame
        while levels > 0:
            f = f.f_back                   
            levels -= 1
        ldict = f.f_globals.copy()
        if f.f_globals != f.f_locals:
            ldict.update(f.f_locals)

        return ldict

# -----------------------------------------------------------------------------
# parse_grammar()
#
# This takes a raw grammar rule string and parses it into production data
# -----------------------------------------------------------------------------
def parse_grammar(doc,file,line):
    grammar = []
    # Split the doc string into lines
    pstrings = doc.splitlines()
    lastp = None
    dline = line
    for ps in pstrings:
        dline += 1
        p = ps.split()
        if not p: continue
        try:
            if p[0] == '|':
                # This is a continuation of a previous rule
                if not lastp:
                    raise SyntaxError("%s:%d: Misplaced '|'" % (file,dline))
                prodname = lastp
                syms = p[1:]
            else:
                prodname = p[0]
                lastp = prodname
                syms   = p[2:]
                assign = p[1]
                if assign != ':' and assign != '::=':
                    raise SyntaxError("%s:%d: Syntax error. Expected ':'" % (file,dline))

            grammar.append((file,dline,prodname,syms))
        except SyntaxError:
            raise
        except Exception:
            raise SyntaxError("%s:%d: Syntax error in rule '%s'" % (file,dline,ps.strip()))

    return grammar

# -----------------------------------------------------------------------------
# ParserReflect()
#
# This class represents information extracted for building a parser including
# start symbol, error function, tokens, precedence list, action functions,
# etc.
# -----------------------------------------------------------------------------
class ParserReflect(object):
    def __init__(self,pdict,log=None):
        self.pdict      = pdict
        self.start      = None
        self.error_func = None
        self.tokens     = None
        self.files      = {}
        self.grammar    = []
        self.error      = 0

        if log is None:
            self.log = PlyLogger(sys.stderr)
        else:
            self.log = log

    # Get all of the basic information
    def get_all(self):
        self.get_start()
        self.get_error_func()
        self.get_tokens()
        self.get_precedence()
        self.get_pfunctions()
        
    # Validate all of the information
    def validate_all(self):
        self.validate_start()
        self.validate_error_func()
        self.validate_tokens()
        self.validate_precedence()
        self.validate_pfunctions()
        self.validate_files()
        return self.error

    # Compute a signature over the grammar
    def signature(self):
        try:
            from hashlib import md5
        except ImportError:
            from md5 import md5
        try:
            sig = md5()
            if self.start:
                sig.update(self.start.encode('latin-1'))
            if self.prec:
                sig.update("".join(["".join(p) for p in self.prec]).encode('latin-1'))
            if self.tokens:
                sig.update(" ".join(self.tokens).encode('latin-1'))
            for f in self.pfuncs:
                if f[3]:
                    sig.update(f[3].encode('latin-1'))
        except (TypeError,ValueError):
            pass
        return sig.digest()

    # -----------------------------------------------------------------------------
    # validate_file()
    #
    # This method checks to see if there are duplicated p_rulename() functions
    # in the parser module file.  Without this function, it is really easy for
    # users to make mistakes by cutting and pasting code fragments (and it's a real
    # bugger to try and figure out why the resulting parser doesn't work).  Therefore,
    # we just do a little regular expression pattern matching of def statements
    # to try and detect duplicates.
    # -----------------------------------------------------------------------------

    def validate_files(self):
        # Match def p_funcname(
        fre = re.compile(r'\s*def\s+(p_[a-zA-Z_0-9]*)\(')

        for filename in self.files.keys():
            base,ext = os.path.splitext(filename)
            if ext != '.py': return 1          # No idea. Assume it's okay.

            try:
                f = open(filename)
                lines = f.readlines()
                f.close()
            except IOError:
                continue

            counthash = { }
            for linen,l in enumerate(lines):
                linen += 1
                m = fre.match(l)
                if m:
                    name = m.group(1)
                    prev = counthash.get(name)
                    if not prev:
                        counthash[name] = linen
                    else:
                        self.log.warning("%s:%d: Function %s redefined. Previously defined on line %d", filename,linen,name,prev)

    # Get the start symbol
    def get_start(self):
        self.start = self.pdict.get('start')

    # Validate the start symbol
    def validate_start(self):
        if self.start is not None:
            if not isinstance(self.start,str):
                self.log.error("'start' must be a string")

    # Look for error handler
    def get_error_func(self):
        self.error_func = self.pdict.get('p_error')

    # Validate the error function
    def validate_error_func(self):
        if self.error_func:
            if isinstance(self.error_func,types.FunctionType):
                ismethod = 0
            elif isinstance(self.error_func, types.MethodType):
                ismethod = 1
            else:
                self.log.error("'p_error' defined, but is not a function or method")
                self.error = 1
                return

            eline = func_code(self.error_func).co_firstlineno
            efile = func_code(self.error_func).co_filename
            self.files[efile] = 1

            if (func_code(self.error_func).co_argcount != 1+ismethod):
                self.log.error("%s:%d: p_error() requires 1 argument",efile,eline)
                self.error = 1

    # Get the tokens map
    def get_tokens(self):
        tokens = self.pdict.get("tokens",None)
        if not tokens:
            self.log.error("No token list is defined")
            self.error = 1
            return

        if not isinstance(tokens,(list, tuple)):
            self.log.error("tokens must be a list or tuple")
            self.error = 1
            return
        
        if not tokens:
            self.log.error("tokens is empty")
            self.error = 1
            return

        self.tokens = tokens

    # Validate the tokens
    def validate_tokens(self):
        # Validate the tokens.
        if 'error' in self.tokens:
            self.log.error("Illegal token name 'error'. Is a reserved word")
            self.error = 1
            return

        terminals = {}
        for n in self.tokens:
            if n in terminals:
                self.log.warning("Token '%s' multiply defined", n)
            terminals[n] = 1

    # Get the precedence map (if any)
    def get_precedence(self):
        self.prec = self.pdict.get("precedence",None)

    # Validate and parse the precedence map
    def validate_precedence(self):
        preclist = []
        if self.prec:
            if not isinstance(self.prec,(list,tuple)):
                self.log.error("precedence must be a list or tuple")
                self.error = 1
                return
            for level,p in enumerate(self.prec):
                if not isinstance(p,(list,tuple)):
                    self.log.error("Bad precedence table")
                    self.error = 1
                    return

                if len(p) < 2:
                    self.log.error("Malformed precedence entry %s. Must be (assoc, term, ..., term)",p)
                    self.error = 1
                    return
                assoc = p[0]
                if not isinstance(assoc,str):
                    self.log.error("precedence associativity must be a string")
                    self.error = 1
                    return
                for term in p[1:]:
                    if not isinstance(term,str):
                        self.log.error("precedence items must be strings")
                        self.error = 1
                        return
                    preclist.append((term,assoc,level+1))
        self.preclist = preclist

    # Get all p_functions from the grammar
    def get_pfunctions(self):
        p_functions = []
        for name, item in self.pdict.items():
            if name[:2] != 'p_': continue
            if name == 'p_error': continue
            if isinstance(item,(types.FunctionType,types.MethodType)):
                line = func_code(item).co_firstlineno
                file = func_code(item).co_filename
                p_functions.append((line,file,name,item.__doc__))

        # Sort all of the actions by line number
        p_functions.sort()
        self.pfuncs = p_functions


    # Validate all of the p_functions
    def validate_pfunctions(self):
        grammar = []
        # Check for non-empty symbols
        if len(self.pfuncs) == 0:
            self.log.error("no rules of the form p_rulename are defined")
            self.error = 1
            return 
        
        for line, file, name, doc in self.pfuncs:
            func = self.pdict[name]
            if isinstance(func, types.MethodType):
                reqargs = 2
            else:
                reqargs = 1
            if func_code(func).co_argcount > reqargs:
                self.log.error("%s:%d: Rule '%s' has too many arguments",file,line,func.__name__)
                self.error = 1
            elif func_code(func).co_argcount < reqargs:
                self.log.error("%s:%d: Rule '%s' requires an argument",file,line,func.__name__)
                self.error = 1
            elif not func.__doc__:
                self.log.warning("%s:%d: No documentation string specified in function '%s' (ignored)",file,line,func.__name__)
            else:
                try:
                    parsed_g = parse_grammar(doc,file,line)
                    for g in parsed_g:
                        grammar.append((name, g))
                except SyntaxError:
                    e = sys.exc_info()[1]
                    self.log.error(str(e))
                    self.error = 1

                # Looks like a valid grammar rule
                # Mark the file in which defined.
                self.files[file] = 1

        # Secondary validation step that looks for p_ definitions that are not functions
        # or functions that look like they might be grammar rules.

        for n,v in self.pdict.items():
            if n[0:2] == 'p_' and isinstance(v, (types.FunctionType, types.MethodType)): continue
            if n[0:2] == 't_': continue
            if n[0:2] == 'p_' and n != 'p_error':
                self.log.warning("'%s' not defined as a function", n)
            if ((isinstance(v,types.FunctionType) and func_code(v).co_argcount == 1) or
                (isinstance(v,types.MethodType) and func_code(v).co_argcount == 2)):
                try:
                    doc = v.__doc__.split(" ")
                    if doc[1] == ':':
                        self.log.warning("%s:%d: Possible grammar rule '%s' defined without p_ prefix",
                                         func_code(v).co_filename, func_code(v).co_firstlineno,n)
                except Exception:
                    pass

        self.grammar = grammar

# -----------------------------------------------------------------------------
# yacc(module)
#
# Build a parser
# -----------------------------------------------------------------------------

def yacc(method='LALR', debug=yaccdebug, module=None, tabmodule=tab_module, start=None, 
         check_recursion=1, optimize=0, write_tables=1, debugfile=debug_file,outputdir='',
         debuglog=None, errorlog = None, picklefile=None):

    global parse                 # Reference to the parsing method of the last built parser

    # If pickling is enabled, table files are not created

    if picklefile:
        write_tables = 0

    if errorlog is None:
        errorlog = PlyLogger(sys.stderr)

    # Get the module dictionary used for the parser
    if module:
        _items = [(k,getattr(module,k)) for k in dir(module)]
        pdict = dict(_items)
    else:
        pdict = get_caller_module_dict(2)

    # Collect parser information from the dictionary
    pinfo = ParserReflect(pdict,log=errorlog)
    pinfo.get_all()

    if pinfo.error:
        raise YaccError("Unable to build parser")

    # Check signature against table files (if any)
    signature = pinfo.signature()

    # Read the tables
    try:
        lr = LRTable()
        if picklefile:
            read_signature = lr.read_pickle(picklefile)
        else:
            read_signature = lr.read_table(tabmodule)
        if optimize or (read_signature == signature):
            try:
                lr.bind_callables(pinfo.pdict)
                parser = LRParser(lr,pinfo.error_func)
                parse = parser.parse
                return parser
            except Exception:
                e = sys.exc_info()[1]
                errorlog.warning("There was a problem loading the table file: %s", repr(e))
    except VersionError:
        e = sys.exc_info()
        errorlog.warning(str(e))
    except Exception:
        pass

    if debuglog is None:
        if debug:
            debuglog = PlyLogger(open(debugfile,"w"))
        else:
            debuglog = NullLogger()

    debuglog.info("Created by PLY version %s (http://www.dabeaz.com/ply)", __version__)


    errors = 0

    # Validate the parser information
    if pinfo.validate_all():
        raise YaccError("Unable to build parser")
    
    if not pinfo.error_func:
        errorlog.warning("no p_error() function is defined")

    # Create a grammar object
    grammar = Grammar(pinfo.tokens)

    # Set precedence level for terminals
    for term, assoc, level in pinfo.preclist:
        try:
            grammar.set_precedence(term,assoc,level)
        except GrammarError:
            e = sys.exc_info()[1]
            errorlog.warning("%s",str(e))

    # Add productions to the grammar
    for funcname, gram in pinfo.grammar:
        file, line, prodname, syms = gram
        try:
            grammar.add_production(prodname,syms,funcname,file,line)
        except GrammarError:
            e = sys.exc_info()[1]
            errorlog.error("%s",str(e))
            errors = 1

    # Set the grammar start symbols
    try:
        if start is None:
            grammar.set_start(pinfo.start)
        else:
            grammar.set_start(start)
    except GrammarError:
        e = sys.exc_info()[1]
        errorlog.error(str(e))
        errors = 1

    if errors:
        raise YaccError("Unable to build parser")

    # Verify the grammar structure
    undefined_symbols = grammar.undefined_symbols()
    for sym, prod in undefined_symbols:
        errorlog.error("%s:%d: Symbol '%s' used, but not defined as a token or a rule",prod.file,prod.line,sym)
        errors = 1

    unused_terminals = grammar.unused_terminals()
    if unused_terminals:
        debuglog.info("")
        debuglog.info("Unused terminals:")
        debuglog.info("")
        for term in unused_terminals:
            errorlog.warning("Token '%s' defined, but not used", term)
            debuglog.info("    %s", term)

    # Print out all productions to the debug log
    if debug:
        debuglog.info("")
        debuglog.info("Grammar")
        debuglog.info("")
        for n,p in enumerate(grammar.Productions):
            debuglog.info("Rule %-5d %s", n, p)

    # Find unused non-terminals
    unused_rules = grammar.unused_rules()
    for prod in unused_rules:
        errorlog.warning("%s:%d: Rule '%s' defined, but not used", prod.file, prod.line, prod.name)

    if len(unused_terminals) == 1:
        errorlog.warning("There is 1 unused token")
    if len(unused_terminals) > 1:
        errorlog.warning("There are %d unused tokens", len(unused_terminals))

    if len(unused_rules) == 1:
        errorlog.warning("There is 1 unused rule")
    if len(unused_rules) > 1:
        errorlog.warning("There are %d unused rules", len(unused_rules))

    if debug:
        debuglog.info("")
        debuglog.info("Terminals, with rules where they appear")
        debuglog.info("")
        terms = list(grammar.Terminals)
        terms.sort()
        for term in terms:
            debuglog.info("%-20s : %s", term, " ".join([str(s) for s in grammar.Terminals[term]]))
        
        debuglog.info("")
        debuglog.info("Nonterminals, with rules where they appear")
        debuglog.info("")
        nonterms = list(grammar.Nonterminals)
        nonterms.sort()
        for nonterm in nonterms:
            debuglog.info("%-20s : %s", nonterm, " ".join([str(s) for s in grammar.Nonterminals[nonterm]]))
        debuglog.info("")

    if check_recursion:
        unreachable = grammar.find_unreachable()
        for u in unreachable:
            errorlog.warning("Symbol '%s' is unreachable",u)

        infinite = grammar.infinite_cycles()
        for inf in infinite:
            errorlog.error("Infinite recursion detected for symbol '%s'", inf)
            errors = 1
        
    unused_prec = grammar.unused_precedence()
    for term, assoc in unused_prec:
        errorlog.error("Precedence rule '%s' defined for unknown symbol '%s'", assoc, term)
        errors = 1

    if errors:
        raise YaccError("Unable to build parser")
    
    # Run the LRGeneratedTable on the grammar
    if debug:
        errorlog.debug("Generating %s tables", method)
            
    lr = LRGeneratedTable(grammar,method,debuglog)

    if debug:
        num_sr = len(lr.sr_conflicts)

        # Report shift/reduce and reduce/reduce conflicts
        if num_sr == 1:
            errorlog.warning("1 shift/reduce conflict")
        elif num_sr > 1:
            errorlog.warning("%d shift/reduce conflicts", num_sr)

        num_rr = len(lr.rr_conflicts)
        if num_rr == 1:
            errorlog.warning("1 reduce/reduce conflict")
        elif num_rr > 1:
            errorlog.warning("%d reduce/reduce conflicts", num_rr)

    # Write out conflicts to the output file
    if debug and (lr.sr_conflicts or lr.rr_conflicts):
        debuglog.warning("")
        debuglog.warning("Conflicts:")
        debuglog.warning("")

        for state, tok, resolution in lr.sr_conflicts:
            debuglog.warning("shift/reduce conflict for %s in state %d resolved as %s",  tok, state, resolution)
        
        already_reported = {}
        for state, rule, rejected in lr.rr_conflicts:
            if (state,id(rule),id(rejected)) in already_reported:
                continue
            debuglog.warning("reduce/reduce conflict in state %d resolved using rule (%s)", state, rule)
            debuglog.warning("rejected rule (%s) in state %d", rejected,state)
            errorlog.warning("reduce/reduce conflict in state %d resolved using rule (%s)", state, rule)
            errorlog.warning("rejected rule (%s) in state %d", rejected, state)
            already_reported[state,id(rule),id(rejected)] = 1
        
        warned_never = []
        for state, rule, rejected in lr.rr_conflicts:
            if not rejected.reduced and (rejected not in warned_never):
                debuglog.warning("Rule (%s) is never reduced", rejected)
                errorlog.warning("Rule (%s) is never reduced", rejected)
                warned_never.append(rejected)

    # Write the table file if requested
    if write_tables:
        lr.write_table(tabmodule,outputdir,signature)

    # Write a pickled version of the tables
    if picklefile:
        lr.pickle_table(picklefile,signature)

    # Build the parser
    lr.bind_callables(pinfo.pdict)
    parser = LRParser(lr,pinfo.error_func)

    parse = parser.parse
    return parser


### BEGIN expr2latex

t_PLUS = r'\+'
t_MINUS = r'-'
t_NEG = r'~'
t_EQUALS = r'='
# either * or .* (element-wise multiply)
t_TIMES  = r'(\*)|(\.\*)'
# either / or ./ (element-wise divide)
t_DIVIDE = r'(/)|(\./)'
# either \ or .\ (element-wise LEFT divide - backwards divide)
t_LDIVIDE = r'(\\)|(\.\\)'
# either ^ or .^ (element-wise exponentiation)
t_EXPONENT = r'(\^)|(\.\^)'
# matrix transpose:
t_TRANSPOSE = r"\.'"
# complex conjugate transpose:
t_CCTRANSPOSE = r"'"

t_COLON = r':'
t_COMMA = r','

t_LT  = r'<'
t_LTE = r'<='
t_GT  = r'>'
t_GTE = r'>='
t_EQ  = r'=='
# MATLAB-style: '~=', C-style: '!='
t_NEQ = r'(~|!)='

t_OR     = r'\|'
t_OROR   = r'\|\|'
t_AND    = r'&'
t_ANDAND = r'&&'

t_LPAREN = r'\('
t_RPAREN = r'\)'

t_LBRACE = r'\{'
t_RBRACE = r'\}'

t_LBRACKET = r'\['
t_RBRACKET = r'\]'

# Ignored characters (very tricky - also ignore \r for newlines in HTML
# forms)
t_ignore = " \t\n\r"

# These token definitions were stolen from pycparser:
#   http://code.google.com/p/pycparser/

# valid C identifiers (K&R2: A.2.3)
c_identifier = r'[a-zA-Z_][0-9a-zA-Z_]*'

# add a twist where you can access arbitrary struct elements
# like foo.bar or foo.bar.baz or foo$bar (R syntax)
identifier = c_identifier + '(([.]|[$])' + c_identifier + ')*'

# integer constants (K&R2: A.2.5.1)
integer_suffix_opt = r'(([uU][lL])|([lL][uU])|[uU]|[lL])?'
decimal_constant = '(0'+integer_suffix_opt+')|([1-9][0-9]*'+integer_suffix_opt+')'
 
# floating constants (K&R2: A.2.5.3)
exponent_part = r"""([eE][-+]?[0-9]+)"""

# dis-allow floats like 1. or 0. ...
#fractional_constant = r"""([0-9]*\.[0-9]+)|([0-9]+\.)"""
fractional_constant = r"""[0-9]*\.[0-9]+"""

floating_constant = '(((('+fractional_constant+')'+exponent_part+'?)|([0-9]+'+exponent_part+'))[FfLl]?)'


# The following floating and integer constants are defined as 
# functions to impose a strict order (otherwise, decimal
# is placed before the others because its regex is longer,
# and this is bad)
@TOKEN(floating_constant)
def t_FLOAT_CONST(t):
  return t

@TOKEN(decimal_constant)
def t_INT_CONST(t):
  return t

@TOKEN(identifier)
def t_ID(t):
  return t


tokens = ('FLOAT_CONST', 'INT_CONST', 
          'ID', 'LPAREN', 'RPAREN', 
          'LBRACE', 'RBRACE',
          'LBRACKET', 'RBRACKET',
          'PLUS', 'MINUS', 'TIMES', 'DIVIDE', 'LDIVIDE',
          'TRANSPOSE', 'CCTRANSPOSE',
          'EXPONENT',
          'LT', 'LTE', 'GT', 'GTE', 'EQ', 'NEQ',
          'NEG',
          'COMMA', 'COLON',
          'OR', 'OROR', 'AND', 'ANDAND',
          'EQUALS')

# MATLAB operators reference (for precedence rules):
# http://www.mathworks.com/access/helpdesk/help/techdoc/index.html?/access/helpdesk/help/techdoc/matlab_prog/f0-40063.html

# later in the list means higher precedence, according to MATLAB rules
precedence = ( ('left', 'COMMA'),
               ('left', 'OROR'),
               ('left', 'ANDAND'),
               ('left', 'OR'),
               ('left', 'AND'),
               ('left', 'LT', 'LTE', 'GT', 'GTE', 'EQ', 'NEQ'),
               ('left', 'COLON'),
               ('left','PLUS', 'MINUS'),
               # divide comes before ldivide ...
               ('left', 'TIMES', 'DIVIDE', 'LDIVIDE'),
               ('right', 'UMINUS', 'NEG'),
               ('left', 'TRANSPOSE', 'CCTRANSPOSE', 'EXPONENT'),
             )

def t_error(t):
  print >> sys.stderr, "Illegal character '%s'" % t.value[0]
  raise Exception() # fail fast
  #t.lexer.skip(1)


# Build the lexer 
#inlined_ply.lex.lex() 
lex() 


# Also some code stolen from this example:
#   http://www.dabeaz.com/ply/example.html

def p_expression_binop(t): 
  '''expression : expression PLUS expression 
                | expression MINUS expression 
                | expression TIMES expression 
                | expression DIVIDE expression
                | expression LDIVIDE expression
                | expression EXPONENT expression
                | expression COLON expression
                | expression EQUALS expression
                | expression LT  expression
                | expression LTE expression
                | expression GT  expression
                | expression GTE expression
                | expression EQ  expression
                | expression NEQ expression
                | expression OR expression
                | expression OROR expression
                | expression AND expression
                | expression ANDAND expression
                ''' 
  op = t[2]
  # treat element-wise multiply, divide, and exponent like regular ones:
  if op == '.*':
    op = '*'
  elif op == './':
    op = '/'
  elif op == '.^':
    op = '^'

  # treat left divide like regular divide except that the terms are
  # REVERSED: (\ a b) <--> (/ b a)
  if op in ('.\\', '\\'):
    t[0] = ['/', t[3], t[1]]
  # for everything else, treat using the terms in the proper order:
  else:
    t[0] = [op, t[1], t[3]]

def p_expression_transpose(t):
  '''expression : expression TRANSPOSE
                | expression CCTRANSPOSE'''
  if t[2] == ".'":
    t[0] = ['transpose', t[1]]
  else:
    assert t[2] == "'"
    t[0] = ['cctranspose', t[1]]

def p_expression_uminus(t): 
  '''expression : MINUS expression %prec UMINUS'''
  t[0] = ['uminus', t[2]]

def p_expression_negation(t): 
  '''expression : NEG expression'''
  t[0] = ['negation', t[2]]

# stand-alone brackets expression
#
# From Kevin's email:
#
#   Technically you can do [3:5] in matlab and then it just makes an array
#   [3 4 5].
#   [x+y : z] makes an array from round(x+y) to round(z) of integers. If
#   it's easy to support it then support it -- it is valid matlab and it
#   gets used occasionally but not that often.
#
def p_standalone_brackets_arr(t):
  '''expression : LBRACKET arr_expression RBRACKET'''
  # hack by making the first half of brackets_arr an empty string:
  t[0] = ['brackets_arr', '', t[2]]

# function call or special array access like var{5}
def p_expression_arr(t):
  '''expression : ID LPAREN arr_expression RPAREN
                | ID LBRACE arr_expression RBRACE
                | ID LBRACKET arr_expression RBRACKET'''
  if t[2] == '(':
    assert t[4] == ')'
    # special-case rendering for sqrt
    if t[1] == 'sqrt':
      t[0] = ['sqrt', t[3]]
    else:
      t[0] = ['call', t[1], t[3]]
  elif t[2] == '{':
    assert t[4] == '}'
    t[0] = ['braces_arr', t[1], t[3]]
  else:
    assert t[2] == '[' and t[4] == ']'
    t[0] = ['brackets_arr', t[1], t[3]]

def p_expression_group(t):
  'expression : LPAREN expression RPAREN' 
  t[0] = ['group',  t[2]]

# special expressions allowed inside of array accesses - 
# e.g., arr(2:5), arr{3:10}, arr(3,5)

def p_arr_expression(t):
  '''arr_expression : commacolon_exp
                    | expression'''
  t[0] = t[1]

def p_commacolon_exp(t):
  '''commacolon_exp : COMMA
               | COLON
               | arr_expression COMMA arr_expression
               | arr_expression COLON arr_expression'''
  if len(t) == 2:
    t[0] = [t[1]] 
  else:
    assert len(t) == 4
    t[0] = [t[2], t[1], t[3]]


def p_expression_terminal(t):
  '''expression : FLOAT_CONST
                | INT_CONST
                | ID'''
  t[0] = t[1]

def p_error(p):
  print >> sys.stderr, "Syntax error at '%s'" % p.value
  raise Exception() # fail fast


LATEX_LPAREN = r' \left( '
LATEX_RPAREN = r' \right)'

LATEX_LBRACE = r' \left \{ '
LATEX_RBRACE = r' \right \}'

LATEX_LBRACKET = r' \left[ '
LATEX_RBRACKET = r' \right]'

LATEX_UNDERSCORE = r'\_'
LATEX_DOLLAR = r'\$'

# converts an s-expression s into a string in LaTeX syntax
def sexpr_to_latex(s):
  if type(s) is list:
    if s[0] in ('+', '-', '='):
      assert len(s) == 3
      return sexpr_to_latex(s[1]) + ' ' + s[0] + ' ' + sexpr_to_latex(s[2])
    # for simplicity, always render a \cdot
    elif s[0] == '*':
      assert len(s) == 3
      return sexpr_to_latex(s[1]) + ' \cdot ' + sexpr_to_latex(s[2])
    elif s[0] in ('<', '>', '==', '|', '||'):
      return sexpr_to_latex(s[1]) + ' ' + s[0] + ' ' + sexpr_to_latex(s[2])
    elif s[0] == '&':
      return sexpr_to_latex(s[1]) + ' \\& ' + sexpr_to_latex(s[2])
    elif s[0] == '&&':
      return sexpr_to_latex(s[1]) + ' \\&\\& ' + sexpr_to_latex(s[2])
    elif s[0] == '<=':
      return sexpr_to_latex(s[1]) + r' \leq ' + sexpr_to_latex(s[2])
    elif s[0] == '>=':
      return sexpr_to_latex(s[1]) + r' \geq ' + sexpr_to_latex(s[2])
    elif s[0] in ('~=', '!='):
      return sexpr_to_latex(s[1]) + r' \neq ' + sexpr_to_latex(s[2])
    elif s[0] in (',', ':'):
      if len(s) == 1:
        return s[0]
      else:
        assert len(s) == 3
        return sexpr_to_latex(s[1]) + ' ' + s[0] + ' ' + sexpr_to_latex(s[2])
    elif s[0] == '^':
      assert len(s) == 3
      return sexpr_to_latex(s[1]) + '^{ ' + sexpr_to_latex(s[2]) + ' }'
    elif s[0] == '/':
      assert len(s) == 3
      return r'\frac{' + sexpr_to_latex(s[1]) + '}{' + sexpr_to_latex(s[2]) + '}'
    elif is_group(s):
      assert len(s) == 2
      return LATEX_LPAREN + sexpr_to_latex(s[1]) + LATEX_RPAREN
    elif s[0] == 'call':
      assert len(s) == 3
      return sexpr_to_latex(s[1]) + LATEX_LPAREN + sexpr_to_latex(s[2]) + LATEX_RPAREN
    elif s[0] == 'sqrt':
      assert len(s) == 2
      return r'\sqrt{' + sexpr_to_latex(s[1]) + '}'
    elif s[0] == 'braces_arr':
      assert len(s) == 3
      return sexpr_to_latex(s[1]) + LATEX_LBRACE + sexpr_to_latex(s[2]) + LATEX_RBRACE
    elif s[0] == 'brackets_arr':
      assert len(s) == 3
      return sexpr_to_latex(s[1]) + LATEX_LBRACKET + sexpr_to_latex(s[2]) + LATEX_RBRACKET
    elif s[0] == 'uminus':
      assert len(s) == 2
      return r'\text{-}' + sexpr_to_latex(s[1])
    elif s[0] == 'negation':
      assert len(s) == 2
      return r'\sim' + sexpr_to_latex(s[1])
    elif s[0] == 'transpose':
      assert len(s) == 2
      return sexpr_to_latex(s[1]) + '^{T}'
    elif s[0] == 'cctranspose':
      assert len(s) == 2
      return sexpr_to_latex(s[1]) + '^{H}'
    else:
      assert False, "should never get here!"
  else:
    # base case:
    assert type(s) is str
    s_isnum = False
    try:
      f = float(s)
      s_isnum = True
    except ValueError:
      s_isnum = False

    # render numbers in math notation:
    if s_isnum:
      return s
    # and letters in \text{} notation to prevent italics:
    else:
      # don't do anything for empty string ...
      if not s:
        return ''
      # pi is special:
      elif s == 'pi':
        return r'\pi'
      else:
        return r'\text{' + s.replace('_', LATEX_UNDERSCORE).replace('$', LATEX_DOLLAR) + '}'


#yacc.yacc() 
yacc()


'''
Our goal is to minimize the number of nested fractions:

There are only five possible forms for 3 expressions a, b, c, which are
connected by multiplications and divisions:

1. (/ (* a b) c)
2. (* (/ a c) b)
3. (* a (/ b c))

4. (/ (/ a b) c)
5. (/ a (* b c))

Forms 1, 2, and 3 are isomorphic.  Forms 4 and 5 are isomorphic.

If you are in form 1:
  Form 2 should be preferred over form 1 only if b contains more nested
  fractions than a OR if a and b both have an identical but non-zero
  number of fractions
    e.g., a = (x / y), b = (q / p)
          a = x, b = (q / p)

  Form 3 should be preferred over form 1 only if a contains more nested
  fractions than b
    e.g., a = (x / y), b = q

If you are in forms 2 or 3:
  Always transform to form 1, because it will provide better
  opportunities for optimizing later ... in essence, you want to push
  ('bubble') the division upwards so that hopefully it will eventually
  meet another division and result in form 4, which can then be
  optimized to form 5.

  ERRATA: When you are in form 2, DON'T transform to form 1 if 'b'
          is actually a GROUP (a sub-expression enclosed in parens),
          since Kevin says that it looks aesthetically better that way
          e.g., leave this alone: (* (/ a c) [GROUP ...])

Note that in forms 1, 2, and 3, if c has nested fractions, we can't ever
get rid of them since it must remain in the denominator

If you are in form 4:
  Form 5 should always be preferred over form 4, since it always
  contains fewer nested fractions

If you are in form 5:
  You don't need to do anything
'''

# 1. (/ (* a b) c)
def is_form_1(s):
  return type(s) is list and \
         len(s) == 3 and \
         s[0] == '/' and \
         len(s[1]) == 3 and \
         s[1][0] == '*'

# returns a, b, c in a tuple
def form_1_components(s):
  assert is_form_1(s)
  a = s[1][1]
  b = s[1][2]
  c = s[2]
  return (a, b, c)


# 2. (* (/ a c) b)
def is_form_2(s):
  return type(s) is list and \
         len(s) == 3 and \
         s[0] == '*' and \
         len(s[1]) == 3 and \
         s[1][0] == '/'

# 3. (* a (/ b c))
def is_form_3(s):
  return type(s) is list and \
         len(s) == 3 and \
         s[0] == '*' and \
         len(s[2]) == 3 and \
         s[2][0] == '/'

# 4. (/ (/ a b) c)
def is_form_4(s):
  return type(s) is list and \
         len(s) == 3 and \
         s[0] == '/' and \
         len(s[1]) == 3 and \
         s[1][0] == '/'

# 5. (/ a (* b c))
def is_form_5(s):
  return type(s) is list and \
         len(s) == 3 and \
         s[0] == '/' and \
         len(s[2]) == 3 and \
         s[2][0] == '*'


# transform trees from one form into another:

# (/ (* a b) c) --> (* (/ a c) b)
def transform_1_to_2(s):
  assert is_form_1(s)
  a = s[1][1]
  b = s[1][2]
  c = s[2]
  ret = ['*', ['/', a, c], b]
  assert is_form_2(ret)
  return ret

#  (* (/ a c) b) --> (/ (* a b) c)
def transform_2_to_1(s):
  assert is_form_2(s)
  a = s[1][1]
  c = s[1][2]
  b = s[2]
  ret = ['/', ['*', a, b], c]
  assert is_form_1(ret)
  return ret

# (/ (* a b) c) --> (* a (/ b c))
def transform_1_to_3(s):
  assert is_form_1(s)
  a = s[1][1]
  b = s[1][2]
  c = s[2]
  ret = ['*', a, ['/', b, c]]
  assert is_form_3(ret)
  return ret

# (* a (/ b c)) --> (/ (* a b) c)
def transform_3_to_1(s):
  assert is_form_3(s)
  a = s[1]
  b = s[2][1]
  c = s[2][2]
  ret = ['/', ['*', a, b], c]
  assert is_form_1(ret)
  return ret

# (/ (/ a b) c) --> (/ a (* b c))
def transform_4_to_5(s):
  assert is_form_4(s)
  a = s[1][1]
  b = s[1][2]
  c = s[2]
  ret = ['/', a, ['*', b, c]]
  assert is_form_5(ret)
  return ret

# get the number of fractions (even within nested parens) in the
# s-expression s:
def num_fractions(s):
  if type(s) is list:
    if s[0] == '/':
      assert len(s) == 3
      return 1 + num_fractions(s[1]) + num_fractions(s[2])
    elif s[0] in ('+', '-', '*', '=', '^'):
      assert len(s) == 3
      return num_fractions(s[1]) + num_fractions(s[2])
    elif s[0] in (',', ':'):
      if len(s) == 1:
        return 0
      else:
        assert len(s) == 3
        return num_fractions(s[1]) + num_fractions(s[2])
    elif s[0] in ('group', 'sqrt'):
      assert len(s) == 2
      return num_fractions(s[1])
    elif s[0] in ('call', 'braces_arr', 'brackets_arr'):
      assert len(s) == 3
      assert type(s[1]) is str
      return num_fractions(s[2])
    elif s[0] == 'uminus':
      assert len(s) == 2
      return num_fractions(s[1])
    else:
      assert False, "should never get here!"
  else:
    # base case
    return 0


# transform to flatten divisions as much as possible ...
def tree_transform(s):
  if type(s) is list:
    if s[0] in ('*', '/'):
      assert len(s) == 3
      # make the recursive call first ...
      new_s = [s[0], tree_transform(s[1]), tree_transform(s[2])]

      if is_form_1(new_s):
        (a, b, c) = form_1_components(new_s)
        na = num_fractions(a)
        nb = num_fractions(b)

        #Form 2 should be preferred over form 1 only if b contains
        #more nested fractions than a OR if a and b both have an
        #identical but non-zero number of fractions
        if (nb > na) or ((nb == na) and na > 0):
          return transform_1_to_2(new_s)
        # Form 3 should be preferred over form 1 only if a contains 
        # more nested fractions than b
        elif na > nb:
          return transform_1_to_3(new_s)
        else:
          return new_s

      # If you start on forms 2 or 3, try to transform to form 1, because
      # it will provide better opportunities for optimizing later ... in
      # essence, you want to push ('bubble') the division upwards so that
      # hopefully it will eventually meet another division and result in
      # form 4, which can be optimized to form 5.
      elif is_form_2(new_s):
        # however, make an exception when you encounter a GROUP
        # (don't switch to form 1), because Kevin says that 
        # this looks aesthetically better
        if is_group(new_s[2]):
          return new_s
        else:
          return transform_2_to_1(new_s)
      elif is_form_3(new_s):
        return transform_3_to_1(new_s)
      elif is_form_4(new_s):
        # remember to recursively transform your children
        # before applying transform_4_to_5()
        new_s = [s[0], tree_transform(s[1]), tree_transform(s[2])]
        return transform_4_to_5(new_s)
      else:
        return new_s

    # TODO: ugh, this list is getting long ...
    elif s[0] in ('+', '-', '=', '^', '<', '<=', '>', '>=', '==', '~=', '!=', '|', '||', '&', '&&'):
      assert len(s) == 3
      return [s[0], tree_transform(s[1]), tree_transform(s[2])]

    elif s[0] in (',', ':'):
      if len(s) == 1:
        return s # return verbatim
      else:
        assert len(s) == 3
        return [s[0], tree_transform(s[1]), tree_transform(s[2])]
    elif s[0] in ('group', 'sqrt', 'uminus', 'negation', 'transpose', 'cctranspose'):
      assert len(s) == 2
      return [s[0], tree_transform(s[1])]
    elif s[0] in ('call', 'braces_arr', 'brackets_arr'):
      assert len(s) == 3
      assert type(s[1]) is str
      return [s[0], s[1], tree_transform(s[2])]
    else:
      assert False, "should never get here!"
  else:
    # base case - return verbatim:
    assert type(s) is str
    return s


def is_group(s):
  if type(s) is list and s[0] == 'group':
    assert len(s) == 2
    return True
  else:
    return False

# transform tree to eliminate unnecessary parentheses:
def eliminate_parens(s, force_eliminate_group=False):
  if type(s) is list:
    if s[0] == '/':
      # we can only eliminate parentheses if we have something of the
      # form (/ a b) where either a and b are of type 'group'
      return [s[0], 
              # force_eliminate_group on LHS and RHS:
              eliminate_parens(s[1], True),
              eliminate_parens(s[2], True)]

    elif s[0] == '^':
      assert len(s) == 3
      # we can eliminate parens in anything on the RHS of a ^ operator
      # since it will be rended in a LaTeX ^{ ... } block
      # e.g., a^(b/c) can eliminate parens around b/c
      return [s[0], 
              # don't eliminate parens on LHS for readability reasons
              s[1],
              # force_eliminate_group on RHS:
              eliminate_parens(s[2], True)]

    elif s[0] in ('+', '-', '*', '=', '<', '<=', '>', '>=', '==', '~=', '!=', '|', '||', '&', '&&'):
      assert len(s) == 3
      return [s[0], 
              eliminate_parens(s[1]),
              eliminate_parens(s[2])]

    elif s[0] in (',', ':'):
      if len(s) == 1:
        return s # return verbatim
      else:
        assert len(s) == 3
        return [s[0], 
                eliminate_parens(s[1]),
                eliminate_parens(s[2])]

    elif is_group(s):
      # we can eliminate parentheses if we have nested groups:
      # (group (group ...))
      if is_group(s[1]):
        # strip off the outer 'group' and KEEP PROPAGATING
        # force_eliminate_group (rather than using default False val)
        return eliminate_parens(s[1], force_eliminate_group)
      # (group (/ x y)) --> (/ x y)
      # since division creates a \frac, which doesn't need parens
      #
      # (group (^ x y)) --> (^ x y)
      # since ^ creates a ^{ ... }, which doesn't need parens
      elif type(s[1]) is list and s[1][0] in ('/', '^'):
        return eliminate_parens(s[1])
      # if some node from above commanded us to strip off all groups,
      # then do so :)
      elif force_eliminate_group:
        return eliminate_parens(s[1])
      else:
        return [s[0], eliminate_parens(s[1])]
    elif s[0] in ('sqrt', 'uminus', 'negation', 'transpose', 'cctranspose'):
      assert len(s) == 2
      return [s[0], eliminate_parens(s[1])]
    elif s[0] in ('call', 'braces_arr', 'brackets_arr'):
      assert len(s) == 3
      assert type(s[1]) is str
      return [s[0], s[1], eliminate_parens(s[2])]
    else:
      assert False, "should never get here!"
  else:
    # base case - return verbatim:
    assert type(s) is str
    return s


def expr2latex(s):
  # pre-process to eliminate trailing semi-colon in case people copy and
  # paste their entire line of code, which ends in semi-colon
  s = s.rstrip()
  while s[-1] == ';':
    s = s[:-1]

  # also pre-process to eliminate '...', which stands for a line
  # continuation in MATLAB
  s = s.replace('...', ' ')

  # do eliminate_parens AFTER tree_transform
  return sexpr_to_latex(
           #eliminate_parens(tree_transform(yacc.parse(s))))
           eliminate_parens(tree_transform(parse(s))))


### BEGIN tests.py

# pairs of (input, expected output) or a single string 'SECTION NAME'
tests = [ 'Simple fractions',
  ('a = b/c', '\\text{a} = \\frac{\\text{b}}{\\text{c}}'),
  'Nested fractions',
  ('a / b / c', '\\frac{\\text{a}}{\\text{b} \\cdot \\text{c}}'),
  ( 'a / b / c / d',
    '\\frac{\\text{a}}{\\text{b} \\cdot \\text{c} \\cdot \\text{d}}'),
  ( 'a*b/c/d',
    '\\frac{\\text{a} \\cdot \\text{b}}{\\text{c} \\cdot \\text{d}}'),
  ( 'a*b/c*d/e',
    '\\frac{\\text{a} \\cdot \\text{b} \\cdot \\text{d}}{\\text{c} \\cdot \\text{e}}'),
  ( 'a*b/(c*d)',
    '\\frac{\\text{a} \\cdot \\text{b}}{\\text{c} \\cdot \\text{d}}'),
  ( '(a + b*c + d/e)/(g/h)',
    '\\frac{\\text{a} + \\text{b} \\cdot \\text{c} + \\frac{\\text{d}}{\\text{e}}}{\\frac{\\text{g}}{\\text{h}}}'),
  ( 'a + b/c + d/e/g*h',
    '\\text{a} + \\frac{\\text{b}}{\\text{c}} + \\frac{\\text{d} \\cdot \\text{h}}{\\text{e} \\cdot \\text{g}}'),
  'Element-wise (dot) notation',
  ( 'a.*b/c./d',
    '\\frac{\\text{a} \\cdot \\text{b}}{\\text{c} \\cdot \\text{d}}'),
  'Function calls',
  ( 'brHeight(a + b/c) + b/c + d/e/g*h',
    '\\text{brHeight} \\left( \\text{a} + \\frac{\\text{b}}{\\text{c}} \\right) + \\frac{\\text{b}}{\\text{c}} + \\frac{\\text{d} \\cdot \\text{h}}{\\text{e} \\cdot \\text{g}}'),
  'Unary minus',
  ('-a*b', '\\text{-}\\text{a} \\cdot \\text{b}'),
  ('-(a*b)', '\\text{-} \\left( \\text{a} \\cdot \\text{b} \\right)'),
  ('-a/b', '\\frac{\\text{-}\\text{a}}{\\text{b}}'),
  ( '-a*-(b/c+d)',
    '\\text{-}\\text{a} \\cdot \\text{-} \\left( \\frac{\\text{b}}{\\text{c}} + \\text{d} \\right)'),
  'Unary negation',
  ('~x', '\\sim\\text{x}'),
  ('~~~x/y', '\\frac{\\sim\\sim\\sim\\text{x}}{\\text{y}}'),
  ('~~~(x/y)', '\\sim\\sim\\sim\\frac{\\text{x}}{\\text{y}}'),
  'Special array access',
  ('arr{5/3}', '\\text{arr} \\left \\{ \\frac{5}{3} \\right \\}'),
  ( 'hello{world/3}',
    '\\text{hello} \\left \\{ \\frac{\\text{world}}{3} \\right \\}'),
  ('arr[5/3]', '\\text{arr} \\left[ \\frac{5}{3} \\right]'),
  ( 'arr[x{y}]',
    '\\text{arr} \\left[ \\text{x} \\left \\{ \\text{y} \\right \\} \\right]'),
  'Struct access',
  ('foo.bar / 4', '\\frac{\\text{foo.bar}}{4}'),
  'R data frame access',
  ('foo$bar / 4', '\\frac{\\text{foo\\$bar}}{4}'),
  'Underscores',
  ('my_big_variable_name', '\\text{my\\_big\\_variable\\_name}'),
  'Colons and commas inside of array operations',
  ('matrix1(3,4)/8', '\\frac{\\text{matrix1} \\left( 3 , 4 \\right)}{8}'),
  ('arr(3:5)', '\\text{arr} \\left( 3 : 5 \\right)'),
  ('arr(3:5:xyz)', '\\text{arr} \\left( 3 : 5 : \\text{xyz} \\right)'),
  ( 'arr(3:5/23:xyz)',
    '\\text{arr} \\left( 3 : \\frac{5}{23} : \\text{xyz} \\right)'),
  ('arr(:)', '\\text{arr} \\left( : \\right)'),
  ('4*a(3,:)', '4 \\cdot \\text{a} \\left( 3 , : \\right)'),
  ('4*a(6/2,:)', '4 \\cdot \\text{a} \\left( \\frac{6}{2} , : \\right)'),
  ( 'A(i,j,k,:)',
    '\\text{A} \\left( \\text{i} , \\text{j} , \\text{k} , : \\right)'),
  ('A(:,:)', '\\text{A} \\left( : , : \\right)'),
  ('A{:,:}', '\\text{A} \\left \\{ : , : \\right \\}'),
  ('a(-2,:)', '\\text{a} \\left( \\text{-}2 , : \\right)'),
  'Exponents',
  ('5^kevin', '5^{ \\text{kevin} }'),
  ('5.^kevin', '5^{ \\text{kevin} }'),
  ('2^3*5', '2^{ 3 } \\cdot 5'),
  ('3/5^y', '\\frac{3}{5^{ \\text{y} }}'),
  ('3./5^y', '\\frac{3}{5^{ \\text{y} }}'),
  ('a*b^(4/7)', '\\text{a} \\cdot \\text{b}^{ \\frac{4}{7} }'),
  ( 'sqrt((w/c)^2 - (n*pi/d)^2)',
    '\\sqrt{ \\left( \\frac{\\text{w}}{\\text{c}} \\right)^{ 2 } -  \\left( \\frac{\\text{n} \\cdot \\pi}{\\text{d}} \\right)^{ 2 }}'),
  'Square roots',
  ('sqrt(3/5)', '\\sqrt{\\frac{3}{5}}'),
  ( 'sqrt(a + 3/(x+y))',
    '\\sqrt{\\text{a} + \\frac{3}{\\text{x} + \\text{y}}}'),
  "Kevin's real-world examples",
  ( 'mu_h*((1-phi)/(1+2/3*phi))',
    '\\text{mu\\_h} \\cdot \\frac{1 - \\text{phi}}{1 + \\frac{2 \\cdot \\text{phi}}{3}}'),
  ( '(1./(sqrt(-1)*2*pi*freqs(k)*rhos)).*dpdr(:,k)',
    '\\frac{1}{\\sqrt{\\text{-}1} \\cdot 2 \\cdot \\pi \\cdot \\text{freqs} \\left( \\text{k} \\right) \\cdot \\text{rhos}} \\cdot \\text{dpdr} \\left( : , \\text{k} \\right)'),
  ( 'trapz(int_recreated_long{i_freq}, z_pos_long{i_freq})',
    '\\text{trapz} \\left( \\text{int\\_recreated\\_long} \\left \\{ \\text{i\\_freq} \\right \\} , \\text{z\\_pos\\_long} \\left \\{ \\text{i\\_freq} \\right \\} \\right)'),
  ( '(-1./(sqrt(-1)*2*pi*freqs(i_freq)*env_rhos{i_freq})).*(TmpP2(:,i_freq) - TmpP(:,i_freq))/dr_1;',
    '\\frac{\\text{-}1}{\\sqrt{\\text{-}1} \\cdot 2 \\cdot \\pi \\cdot \\text{freqs} \\left( \\text{i\\_freq} \\right) \\cdot \\text{env\\_rhos} \\left \\{ \\text{i\\_freq} \\right \\}} \\cdot \\frac{\\text{TmpP2} \\left( : , \\text{i\\_freq} \\right) - \\text{TmpP} \\left( : , \\text{i\\_freq} \\right)}{\\text{dr\\_1}}'),
  ( 'beta = 1 / (sqrt(1-(v/c)^2))',
    '\\text{beta} = \\frac{1}{\\sqrt{1 -  \\left( \\frac{\\text{v}}{\\text{c}} \\right)^{ 2 }}}'),
  'Butt-kickers for nested fractions',
  ( 'a*b/c*d*e/f/g/h',
    '\\frac{\\text{a} \\cdot \\text{b} \\cdot \\text{d} \\cdot \\text{e}}{\\text{c} \\cdot \\text{f} \\cdot \\text{g} \\cdot \\text{h}}'),
  'Redundant parens',
  ('(((a + b)))', ' \\left( \\text{a} + \\text{b} \\right)'),
  ('x / (y * z)', '\\frac{\\text{x}}{\\text{y} \\cdot \\text{z}}'),
  ('x + (y / z)', '\\text{x} + \\frac{\\text{y}}{\\text{z}}'),
  ('x ^ (y / z)', '\\text{x}^{ \\frac{\\text{y}}{\\text{z}} }'),
  ('(x ^ y) + z', '\\text{x}^{ \\text{y} } + \\text{z}'),
  ( '((x + y)) ^ (((z + w)))',
    ' \\left(  \\left( \\text{x} + \\text{y} \\right) \\right)^{ \\text{z} + \\text{w} }'),
  ( '((x + y)) / (((z + w)))',
    '\\frac{\\text{x} + \\text{y}}{\\text{z} + \\text{w}}'),
  ( '(1 + 2) / 3 ^ ((((((4 + 5)) * 6))))',
    '\\frac{1 + 2}{3^{  \\left( 4 + 5 \\right) \\cdot 6 }}'),
  'Multiplications',
  ('4 * x', '4 \\cdot \\text{x}'),
  ('x * 4', '\\text{x} \\cdot 4'),
  'Left divide',
  ('6 \\ 5', '\\frac{5}{6}'),
  ('a \\ (b / c)', '\\frac{\\frac{\\text{b}}{\\text{c}}}{\\text{a}}'),
  'Transpose',
  ("A'", '\\text{A}^{H}'),
  ("A.'", '\\text{A}^{T}'),
  'Ignoring trailing semi-colons',
  ('x = y + z;', '\\text{x} = \\text{y} + \\text{z}'),
  ('x + 5; \n\n', '\\text{x} + 5'),
  'Pi',
  ('pi * r ^2', '\\pi \\cdot \\text{r}^{ 2 }'),
  ('pi / 2', '\\frac{\\pi}{2}'),
  'Comparisons',
  ('a < b / c', '\\text{a} < \\frac{\\text{b}}{\\text{c}}'),
  ('a <= b / c', '\\text{a} \\leq \\frac{\\text{b}}{\\text{c}}'),
  ('a > b / c', '\\text{a} > \\frac{\\text{b}}{\\text{c}}'),
  ('a >= b / c', '\\text{a} \\geq \\frac{\\text{b}}{\\text{c}}'),
  ('a == b / c', '\\text{a} == \\frac{\\text{b}}{\\text{c}}'),
  ('a ~= b / c', '\\text{a} \\neq \\frac{\\text{b}}{\\text{c}}'),
  ('a != b / c', '\\text{a} \\neq \\frac{\\text{b}}{\\text{c}}'),
  'AndOr',
  ('a & b', '\\text{a} \\& \\text{b}'),
  ('a | b', '\\text{a} | \\text{b}'),
  ('a && b', '\\text{a} \\&\\& \\text{b}'),
  ('a || b', '\\text{a} || \\text{b}'),
  ( 'a & b / (c || d)',
    '\\text{a} \\& \\frac{\\text{b}}{\\text{c} || \\text{d}}'),
  'Stand-alone colon',
  ('a:b', '\\text{a} : \\text{b}'),
  ('1+2:3/4', '1 + 2 : \\frac{3}{4}'),
  'Render fractions as siblings',
  ( '(a + b)/(c + d)/(f*g)*(h + i)',
    '\\frac{\\text{a} + \\text{b}}{ \\left( \\text{c} + \\text{d} \\right) \\cdot  \\left( \\text{f} \\cdot \\text{g} \\right)} \\cdot  \\left( \\text{h} + \\text{i} \\right)'),
  ( '2*a/b*c*(sin(pi*c/2)/(pi*c)/2 )',
    '\\frac{2 \\cdot \\text{a} \\cdot \\text{c}}{\\text{b}} \\cdot \\frac{\\text{sin} \\left( \\frac{\\pi \\cdot \\text{c}}{2} \\right)}{ \\left( \\pi \\cdot \\text{c} \\right) \\cdot 2}'),
  ( '1/2*(real(pressure_recreated1{i_freq}.*conj(vr_recreated{i_freq})))',
    '\\frac{1}{2} \\cdot  \\left( \\text{real} \\left( \\text{pressure\\_recreated1} \\left \\{ \\text{i\\_freq} \\right \\} \\cdot \\text{conj} \\left( \\text{vr\\_recreated} \\left \\{ \\text{i\\_freq} \\right \\} \\right) \\right) \\right)'),
  'stand-alone brackets',
  ('[3:5]', ' \\left[ 3 : 5 \\right]'),
  ('[x+y : z]', ' \\left[ \\text{x} + \\text{y} : \\text{z} \\right]'),
  ( '[x+y : z/w]',
    ' \\left[ \\text{x} + \\text{y} : \\frac{\\text{z}}{\\text{w}} \\right]')]


def runTests(verbose=False):
  newTestSuite = []

  for e in tests:
    if type(e) is str:
      if verbose:
        print("=== " + e + " ===")
      newTestSuite.append(e)
    else:
      (i, expected) = e

      actual = expr2latex(i) 
      if verbose:
        print('Input:    ' + i)
        print('Output:   ' + actual)
      if actual != expected:
        if verbose:
          print('FAILED!')
          print('Expected: ' + expected)
        else:
          print('FAILED TEST')
          print('  Input:    ' + i)
          print('  Output:   ' + actual)
          print('  Expected: ' + expected)
      if verbose:
        print()
      # note that we append *actual* and NOT expected
      newTestSuite.append((i, actual))

print('Running all tests ...')
runTests(verbose=False)
print('DONE')
