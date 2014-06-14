#!/usr/bin/python
import cgi

from urllib import quote

# to get ply to work on MIT CSAIL ...
import sys
sys.path.insert(0, '/afs/csail.mit.edu/u/p/pgbovine/lib/python/')

from expr2latex import expr2latex


print "Content-type: text/html\n"
print '''
<html>
  <head>
    <title>MathViz: Math expression code visualizer</title>

    <style>
body {
  font-family: verdana;
  margin-top: 30px;
  margin-left: 40px;
  margin-right: 40px;
}
    </style>

    <script language="JavaScript">
function visualize(form, val) {
  form.expr.value = val
  form.submit()
}
    </script>

  </head>
  <body>
'''


DEFAULT_EXPR = 'x = (-b + sqrt(b^2 - 4*a*c)) / (2*a)'

form = cgi.FieldStorage()

if form.has_key('expr'):
  expr = form['expr'].value
else:
  expr = DEFAULT_EXPR

success = True
try:
  latexOutput = expr2latex(expr)
except Exception:
  success = False

print '<center>'

print '''
<form method="POST" action="index.py">

<p><small>This tool helps you understand and debug math code written in
the syntax of popular computer programming languages like MATLAB, C,
Java, Python, and R.  It comes in handy when you're reading other
people's code, especially when it contains nested parentheses,
fractions, and exponents.</small></p>

<p/><b>Paste a line of code that represents a math expression:</b>

<p><textarea style="font-size: 12pt; text-align: center;" name="expr" rows=4 cols=60>%s</textarea></p>

<p><input style="font-size: 12pt" type="submit" value="Visualize code in mathematical form"/></p>

</form>
''' % expr

print '<p style="margin-top: 50px; margin-bottom: 20px"></p>'


# debug only:
#print '<p style="margin-top: 40px">Input:<pre>' + `expr` + '</pre></p>'

if success:
  print '<img src="http://www.codecogs.com/eq.latex?%s"/>' % quote(latexOutput)
  #print '<p style="margin-top: 60px">Output LaTeX source code:</p><textarea rows=4 cols=40>' + latexOutput + '</textarea></p>'
  print '<p style="margin-top:30px"/>'
else:
  print '''
<p/>
  <font color="#cc0000">
  
    <b>Uh oh, unable to render your input :(</b>
    
    <p/><b>Please check that it's valid MATLAB or C-style syntax (with
    balanced parentheses), or email your input to me at
    philip@pgbovine.net so that I can see what's up with it.</b>

    <p/><b>Check those parentheses ;)</b>

  </font>
'''

print '</center>'

print '<hr style="margin-top: 60px;"/>'

## nix the visualize button ...
#def create_entry_OLD(expr):
#  return '<tt>%s</tt> <input style="font-size: 8pt" type="button" value="Visualize" onClick="visualize(this.form, \'%s\');"/>' % (expr, expr)

def create_entry(expr, i):
  return '<tt>%s</tt><p/><div style="margin-left: 20px; margin-bottom: 30px;"><img src="eq%d.png" border="1"/></div>' % (expr, i)

print '''
<b>Example equations:</b>

<p>These equations were taken directly from real MATLAB code.  As you can see, they are much easier to understand and debug when visualized using MathViz.</p>

<form method="POST" action="index.py">

<input type="hidden" name="expr"/>

<ul>
  <li/>%s
  <li/>%s
  <li/>%s
  <li/>%s
  <li/>%s
  <li/>%s
</ul>

This pair shows how one tiny change in MATLAB code can totally alter
the expression's meaning, something that is very easy to see in MathViz:

<ul>
  <li/>%s
  <li/>%s
</ul>


Here's a nasty-looking MATLAB expression that MathViz helped Kevin to
understand.  He told me over email: <small><i>"Like, there's no way you
could parse that in your head without spending a good 30 seconds looking
at it even though it's a small equation. But mathviz makes it easy to
understand in quicker than you can say 'latex'!"</i></small>

<ul>
  <li/>%s
</ul>

</form>

''' % (
  create_entry('1/(4*pi*(2*pi*f))*pr', 1),
  create_entry('2*a/b*c*(sin(pi*c/2)/(pi*c)/2)', 2),
  create_entry('(-1./(sqrt(-1)*2*pi*freq(k)*rho)).*(p1(:,k) - p2(:,k));', 3),
  create_entry('3/(2*pi*(numel(krs)-1)*log10(exp(1)))*(krs(end) - krs(1))', 4),
  create_entry('1/2*(real(pressure_recreated1{i_freq}.*conj(vr_recreated{i_freq})))', 5),
  create_entry('max(ceil( (2*pi*oasp_input.f/oasp_input.wi_cmin - 2*pi*oasp_input.f/oasp_input.wi_cmax)/  (pi/4/(Rmax*1000)) ), 10);', 6),

  create_entry('finite_diff = (func(x+delta)-func(x-delta))/(delta*2)', 7),
  create_entry('finite_diff = (func(x+delta)-func(x-delta))/delta*2', 8),
  create_entry('((ws./c).*(1-1/2*(2./((ws./c)*d)).^2))', 9),
)


print '''
<b>Currently supports:</b>
<ul>
  <li/>MATLAB and C-style variable names: <tt>my_var_1</tt>
  <li/>struct variables: <tt>record.field.sub_field</tt>
  <li/>R data frame variables: <tt>frame$field</tt>
  <li/>flattening of fractions: <tt>x / y / z / w</tt>
  <li/>exponents: <tt>a^b</tt>
  <li/>square root: <tt>sqrt(x/y)</tt>
  <li/>unary minus: <tt>-x</tt>
  <li/>parentheses: <tt>2*(3*4)</tt>
  <li/>comparisons: <tt>x <= 3 / y</tt>
  <li/>array accesses using parens and braces (MATLAB) and brackets (C-style): <tt>A(5)</tt>, <tt>A{5}</tt>, <tt>A[5]</tt>
  <li/>function calls: <tt>fib(n-1) + fib(n-2)</tt>
  <li/>elimination of redundant parentheses: <tt>((x + y)) ^ (((z + w)))</tt>
  <li/>MATLAB array accesses using colons and commas: <tt>A(i,j,k,:)</tt>
  <li/>Python array accesses and slicing: <tt>A[3:-2]</tt>
  <li/>MATLAB left divide: <tt>y \ x</tt>
  <li/>MATLAB dot operators: <tt>x.*y</tt>, <tt>A.^b</tt>
  <li/>MATLAB transpose: <tt>A.'</tt>
  <li/>MATLAB Hermitian transpose: <tt>A'</tt> (same as <tt>A.'</tt> for real matrices)
</ul>

<b>Possible new features (if there is a demand):</b>
<ul>
  <li/>One-click feedback mechanism for queries that are rendered incorrectly
  <li/>Multi-dimensional arrays: <tt>A[3][5]</tt>
  <li/>Selective rendering of an entire source file, not just of one line of code
</ul>

<hr/>

<small>MathViz was created by <a
href="http://www.stanford.edu/~pgbovine/">Philip Guo</a>.  If you have
questions, bug reports, or suggestions, please contact me at
philip@pgbovine.net</small>

<p/> <small>Special thanks to Kevin Cockrell for creating an early
prototype, inspiring the creation of MathViz, doing beta testing, making
feature requests, and providing example MATLAB code.</small>

'''

print '''
  </body>
</html>
'''


