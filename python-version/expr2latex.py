# expr2latex
#   converts a math formula written in MATLAB-like syntax into LaTeX syntax
#
# Created on 2009-08-04 by Philip Guo

import re, sys, os

# to get ply to work on MIT CSAIL ...
sys.path.insert(0, '/afs/csail.mit.edu/u/p/pgbovine/lib/python/')

import ply.lex
from ply.lex import TOKEN
import ply.yacc as yacc

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
ply.lex.lex() 


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


yacc.yacc() 



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
           eliminate_parens(tree_transform(yacc.parse(s))))


# if clobberTestSuite is True, then replaces tests.py with a new version
# consisting of actual observed values and backs up old version as
# tests.py.backup:
def runTests(verbose=False, clobberTestSuite=False):
  import tests # only import on demand

  newTestSuite = []

  for e in tests.tests:
    if type(e) is str:
      if verbose:
        print "===", e, "==="
      newTestSuite.append(e)
    else:
      (i, expected) = e

      actual = expr2latex(i) 
      if verbose:
        print 'Input:   ', i
        print 'Output:  ', actual
      if actual != expected:
        if verbose:
          print 'FAILED!'
          print 'Expected:', expected
        else:
          print 'FAILED TEST'
          print '  Input:   ', i
          print '  Output:  ', actual
          print '  Expected:', expected
      if verbose:
        print
      # note that we append *actual* and NOT expected
      newTestSuite.append((i, actual))

  if clobberTestSuite:
    of = open('tests.py.new', 'w')
    of.write("# pairs of (input, expected output) or a single string 'SECTION NAME'\n")
    of.write("tests = ")
    import pprint
    pp = pprint.PrettyPrinter(indent=2, stream=of)
    pp.pprint(newTestSuite)
    of.close()
    os.rename('tests.py', 'tests.py.backup')
    os.rename('tests.py.new', 'tests.py')

if __name__ == "__main__":
  if len(sys.argv) < 2:
    print 'Running all tests ...'
    runTests(verbose=False, clobberTestSuite=False)
    print 'DONE'
  else:
    #print expr2latex(sys.argv[1])

    # for debugging only:
    s = yacc.parse(sys.argv[1])
    print s
    s2 = tree_transform(s)
    print s2
    s3 = eliminate_parens(s2, False)
    print s3
    print sexpr_to_latex(s3)

