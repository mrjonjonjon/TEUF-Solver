import string
from collections import defaultdict
from unionfind import UnionFind
from test import generate_test
import time
from statistics import mean
import matplotlib.pyplot as plt
import numpy as np
int_to_term=dict([])
int_to_vert=dict([])
term_to_int=dict([])
term_to_vert=dict([])
vert_to_int=dict([])
all_terms=set([])
all_vars=set([])
all_funcs=set([])
term_counter=0
vertex_counter=0
uf=0
graph=defaultdict(list)
transformed_graph = defaultdict(list)
predecessors=defaultdict(list)
p1=defaultdict(list)
eq_class_to_pred_list=defaultdict(list)
eqp=defaultdict(list)
equalities=[]
disequalities=[]
all_vertices=set([])
sig_table = defaultdict(set)
def merge(l,r):
    global eq_class_to_pred_list
    if(len(uf.component(l)) < len(uf.component(r))):
        eq_class_to_pred_list[uf.find(r)].extend(eq_class_to_pred_list[uf.find(l)])
        del eq_class_to_pred_list[uf.find(l)]
    else:
        eq_class_to_pred_list[uf.find(l)].extend(eq_class_to_pred_list[uf.find(r)])
        del eq_class_to_pred_list[uf.find(r)]
def print_graph(g):
    
    print("PRINTING GRAPH")
    for v in g:
        print(v," successors: ")
        if g[v] is not None:
            for n in g[v]:
                print(n)
            print('\n')
def print_predecessors():
    global predecessors
    print("PRINTING PREDECESSORS")
    for v in predecessors:
        print(v," : ")
        if predecessors[v] is not None:
            for p in predecessors[v]:
                print(p)
class Vertex:
  def __init__(self, id, label,term):
    self.id = id
    self.label = label
    self.term=term

  def __str__(self):
    return "V["+str(self.term)+"]"


  def __repr__(self):
    return "V["+str(self.term)+"]"
dummy=Vertex(-1,'d','d')


def build_var_graph(v):
    global vertex_counter
    global graph
    global all_vars
    if v in term_to_vert:
        return v
    #all_vars.append(v)
    vert = Vertex(vertex_counter,v,v)

    term_to_int[v]=vertex_counter
    int_to_term[vertex_counter]=v
    int_to_vert[vertex_counter]=vert
    vert_to_int[vert]=vertex_counter
    term_to_vert[v]=vert
    vertex_counter+=1
    graph[vert]=None
    return vert

def build_func_graph(f):
    global vertex_counter
    global graph
    global all_vars
    if f in term_to_vert:
        return f
    global vertex_counter
    global graph
    vert = Vertex(vertex_counter,f[0],f)
    term_to_int[f]=vertex_counter
    int_to_term[vertex_counter]=f

    int_to_vert[vertex_counter]=vert
    vert_to_int[vert]=vertex_counter
    term_to_vert[f]=vert
    vertex_counter+=1
    term_to_vert[f]=vert
    #print(f,len(f))
    for i in range(1,len(f)):
        if f[i] in term_to_vert:
            #print(f[i],"yes")
            #note:have built all vertices by this pint
            graph[vert].append(term_to_vert[f[i]])
            p1[term_to_vert[f[i]]].append(vert)
        else:
            if type(f[i]) is tuple:
                fvert = build_func_graph(f[i])
                graph[vert].append(fvert)
            else:
                fvert = build_var_graph(f[i])
                graph[vert].append(fvert)
            p1[fvert].append(vert)

    return vert

def build_graph():
    for (a,b) in equalities:
        if type(a) is tuple:
            build_func_graph(a)
        else:
            build_var_graph(a)

        if type(b) is tuple:
            build_func_graph(b)
        else:
            build_var_graph(b)
    

def transform_graph():
    global graph
    global vertex_counter
    
    vertex_counter=0
    for v in graph:

        w=v
        if graph[v] is not None and len(graph[v])>0:#add first successor

            transformed_graph[v].append(graph[v][0])
            predecessors[graph[v][0]].append(v)

            if(graph[v] is not None and len(graph[v])>=2):
                
                for d in range(1,len(graph[v])):# 2 to deg v -1
                    w2=Vertex(vertex_counter,'dummy','dummy')
                    #all_vertices.add(w2)
                    vertex_counter+=1

                    transformed_graph[w].append(w2)
                    predecessors[w2].append(w)


                    transformed_graph[w2].append(graph[v][d])
                    predecessors[graph[v][d]].append(w2)
                    w=w2
                
                #x=Vertex(vertex_counter,'dummy','dummy')
                x=dummy
                #all_vertices.add(x)
                vertex_counter+=1
            
                transformed_graph[w2].append(x)
                predecessors[x].append(w2)

                transformed_graph[x]=None
                
        else:
             transformed_graph[v]=None
    for v in transformed_graph:
        if transformed_graph[v] is not None:
            transformed_graph[v]=tuple(transformed_graph[v])
def naive_congruence_closure():
    for (a,b) in equalities:
        naive_merge(term_to_vert[a],term_to_vert[b])
def naive_merge(u,v):
    if uf.connected(u,v):
        return
    Pu=eq_class_to_pred_list[uf.find(u)]
    Pv=eq_class_to_pred_list[uf.find(v)]
    merge(u,v)
    uf.union(u,v)
    
    for x in Pu:
        for y in Pv:
            
            if not uf.connected(x,y) and is_congruent(x,y):
                naive_merge(x,y)

def fast_congruence_closure():
    global uf
    global eq_class_to_pred_list
    pending=[]
    for v in transformed_graph:
        if transformed_graph[v] is not None and len(transformed_graph[v])>=1:
            pending.append(v)
    while len(pending)>0:
        combine=[]
        for v in pending:
            #print("TEST: ",v," --- ",query(v),' ---\n')
            if query(v)=='lamda':
                enter(v)
            else:
                #print("COMBINING ", v,query(v))
                combine.append((v,query(v)))
                
        pending=[]
        #print("COMBINE IS: ",combine)
        for (v,w) in combine:
            #print(uf.component(v),uf.component(w))
            if not uf.connected(v,w):
                if len(eq_class_to_pred_list[uf.find(v)])<len(eq_class_to_pred_list[uf.find(w)]):
                    for u in eq_class_to_pred_list[uf.find(v)]:
                        delete(u)
                        pending.append(u)
                    merge(v,w)
                    uf.union(v,w)
                    #print('niuhnbuhbiuyb',uf.components())
                    
                else:
                    for u in eq_class_to_pred_list[uf.find(w)]:
                        delete(u)
                        pending.append(u)
                    merge(v,w)
                    uf.union(v,w)
                    #print('inipjnpiujnihn',uf.components())
        #print("\nNEW EQS ARE: ",uf.components(),'\n NEW SIGTABLE IS: ',sig_table,'\n PENDING IS: ',pending,'\nPREDLIST IS: ',eq_class_to_pred_list)
                       




def enter(v):
    global sig_table
    sig=0
    if len(transformed_graph[v])==1:
        sig=uf.find(transformed_graph[v][0])
    else:
        sig=(uf.find(transformed_graph[v][0]),uf.find(transformed_graph[v][1]))
    #print("ADDING  ",v," WITH SIGNATURE ",sig," CURSTATE ",sig_table[sig])
    sig_table[sig].add(v)
def delete(v):
    global sig_table
    sig=0
    if len(transformed_graph[v])==1:
        sig=uf.find(transformed_graph[v][0])
    else:
        sig=(uf.find(transformed_graph[v][0]),uf.find(transformed_graph[v][1]))
    #print("REMOVING  ",v," WITH SIGNATURE ",sig," CURSTATE ",sig_table[sig])
    if v in sig_table[sig]:
        sig_table[sig].remove(v)
def query(v):
    global sig_table
    sig=0
    if len(transformed_graph[v])==1:
        sig=uf.find(transformed_graph[v][0])
    else:
        sig=(uf.find(transformed_graph[v][0]),uf.find(transformed_graph[v][1]))
    #print("QUERYING  ",v," WITH SIGNATURE ",sig," CURSTATE ",sig_table[sig])

    for e in sig_table[sig]:
            if e!=v:
                return e
    else:
        return 'lamda'

def verify_term(t):
    pass

def query_term():
    global term_counter
    fv = input("function or variable? (f/v)")
    ans=0
    if fv=='v':
        ans=query_variable()
    elif fv=='f':
        ans=query_function()
    all_terms.add(ans)
    term_counter+=1
    return ans
def query_variable():
    global vertex_counter
    var_name= input("input name of variable")
    all_vars.add(var_name)
    #v=Vertex(vertex_counter,var_name,var_name)
    #graph[v]=None
    #vertex_counter+=1
    return var_name
def query_function():

    ans=[]
    fun_name=input("input name of function")
    ans.append(fun_name)
    num_args= input("input num args")
    #v=Vertex(vertex_counter,fun_name)
    while not num_args.isnumeric():
        print("invalid. must be number. try again")
        num_args=input("input num args")
    for i in range(0,int(num_args)):
        print("input "+ str(i) +"th argument")
        next_arg=query_term()
        ans.append(next_arg)
    all_funcs.add(tuple(ans))
        #graph[fun_name].append(next_arg)
    return tuple(ans)
def is_congruent(v1,v2):
    global transformed_graph
    graph=transformed_graph
    if len(graph[v1])!=len(graph[v2]):
        return False
    for i in range(len(graph[v1])):
        if not uf.connected(graph[v1][i],graph[v2][i]):
            return False
    return True


def naive_build_uf_structure():
      #uf = unionfind(vertex_counter)
    uf = UnionFind(graph.keys())
    for v in graph:
        eq_class_to_pred_list[uf.find(v)]=predecessors[v]

def build_uf_structure():
    global uf
    #uf = unionfind(vertex_counter)
    uf = UnionFind(transformed_graph.keys())
    for v in transformed_graph:
        eq_class_to_pred_list[uf.find(v)]=predecessors[v]

def add_rest(t):
    global all_funcs
    global all_vars
    if type(t) is tuple:
        all_funcs.add(t)
        for i in range(1,len(t)):
            add_rest(t[i])
    else:
        all_vars.add(t)

def begin():   
    while True:
        #ask the user for a pair
        ed=input("equality or disequality? (e/d)")
        if ed=='t':
            _,_,equalities,disequalities = generate_test(10,10,5,0)
            for (a,b) in equalities:
                add_rest(a)
                add_rest(b)

            
            
            break
        char=0
        if ed=='e':
            char="="
        else:
            char="!="
        print("enter lhs")
        lhs=query_term()
        print("entered lhs: ",lhs)
        print("enter rhs")
        rhs=query_term()
        print("enetered rhs: ",rhs)

        print("pair is: ",lhs,char,rhs)
        if ed=='e':
            equalities.append((lhs,rhs))
        again = input("Do you want to continue? (y/n) ")
        if again == "n":
            break
x=[(('f',('f',('f','a'))),'a')    ,     (('f',('f',('f',('f',('f','a'))))),'a')]
y=[[('f','a','b'),'a']  , [('f',('f','a','b'),'b'),'c']]
_,_,equalities,disequalities = generate_test(num_vars=100,num_funcs=10,num_equalities= 1000000,num_inequalities=0)






#for (a,b) in equalities:
           # pass
            #add_rest(a)
           # add_rest(b)

build_graph()
#print_graph(graph)
transform_graph()
#print_graph(transformed_graph)
#print_predecessors()
#print(graph.keys())
t0 = time.time()

build_uf_structure()
#print('\n before: ',uf.components(),'\n')
print('equalities are: \n')
#for eq in equalities:
    #print(eq,'\n')
for (l,r) in equalities:
    merge(term_to_vert[l],term_to_vert[r])
    uf.union(term_to_vert[l],term_to_vert[r])





fast_congruence_closure()
#naive_congruence_closure()
for (a,b) in disequalities:
    if a in term_to_vert and b in term_to_vert and uf.connected(term_to_vert[a],term_to_vert[b]):
        print("UNSAT")
        t1 = time.time()


print("SAT")
for c in uf.components():
    print(c,'\n')
t1 = time.time()
print('time was: ',t1-t0,' seconds')
num_conjunctions=[100,200,300,500,1000]
the_time=         []

average_100=[]#with 100 vars, 10 funcs
average_200=[]
average_300=[]
average_500=[]
average_1000=[]
average_1500=mean([0.3066439628601074,0.2642180919647217,0.1623690128326416])
average_2000=[]
average_5000=mean([0.6593132019042969,0.7252397537231445,0.7108378410339355])
average_10000=mean([1.4072790145874023,1.3463706970214844,0.8127477169036865])
average_20000=mean([2.4409821033477783,2.5140931606292725,2.3244760036468506])
average_50000=mean([4.667107105255127,6.51757025718689,7.288363933563232])
average_100000=mean([10.610958099365234,11.290279865264893,12.4786958694458])
average_150000=mean([18.707698106765747,18.037336826324463,17.652232885360718])
average_200000=mean([20.126737117767334,21.806681156158447,24.128961086273193])
average_500000=mean([63.028456926345825,38.07115435600281,48.65704703330994])
average_1000000=mean([131.58413410186768,116.76077485084534,117.83148503303528])
ypoints = [average_1500,average_5000,average_10000,average_20000,average_50000,average_100000,average_150000,average_200000,average_500000,average_1000000]
xpoints = [1500,        5000,           10000,      20000,      50000,          100000,         150000,         200000,     500000,         1000000]
rat=[y for x,y in zip(xpoints,ypoints)]
plt.plot(xpoints, rat)
x = np.linspace(1.1, 150000, 100)
y = x*np.log(x)* 2.4/20000
#plt.plot(xpoints,xpoints)
#plt.show()