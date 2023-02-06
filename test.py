
import string
import random
 
# initializing size of string

 
# using random.choices()
# generating random strings
def gen_string(N=5):
  res = ''.join(random.choices(string.ascii_lowercase +
                             string.digits, k=N))
  return res
 

def ssample(l):
  return random.sample(l,1)[0]
def generate_test(num_vars,num_funcs,num_equalities,num_inequalities):
  vars=[]
  funcs=[]
  for i in range(num_vars):
    vars.append('v_'+str(i))
  for i in range(num_funcs):
    func=['f_'+str(i)]
    num_args=20*(len(vars)+len(funcs))#random.randint(num_vars * (3/4),num_vars)
    for j in range(num_args):
      next_arg=ssample(vars+funcs)
      func.append(next_arg)
    funcs.append(tuple(func))
  equalities=[]
  inequalities=[]
  for i in range(num_equalities):
    equalities.append(  (ssample(vars+funcs),ssample(vars+funcs))   )
  for i in range(num_inequalities):
    inequalities.append(  (ssample(vars+funcs),ssample(vars+funcs))   )

  #print(vars,'\n',funcs,'\n',equalities,'\n',inequalities)
  return vars,funcs,equalities,inequalities
#generate_test(10,5,3,0)
#print(random.sample([1,2,3],1)[0])