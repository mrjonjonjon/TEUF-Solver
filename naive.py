import string
from collections import defaultdict
from unionfind import UnionFind
from test import generate_test
import time
from statistics import mean
import matplotlib.pyplot as plt
import numpy as np

term_to_vert=dict([])
graph=defaultdict(list)
predecessors=defaultdict(list)
eq_class_to_pred_list=defaultdict(list)
sig_table = defaultdict(set)
equalities=[]
disequalities=[]
uf=0
vertex_counter=0

all_terms=set([])
all_vars=set([])
all_funcs=set([])
term_counter=0



all_vertices=set([])




def merge(l,r):
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    
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
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    
    if v in term_to_vert:
        return v
    #all_vars.append(v)
    vert = Vertex(vertex_counter,v,v)


    term_to_vert[v]=vert
    vertex_counter+=1
    graph[vert]=None
    return vert

def build_func_graph(f):
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    if f in term_to_vert:
        return f
    global vertex_counter
    global graph
    vert = Vertex(vertex_counter,f[0],f)
    term_to_vert[f]=vert
    vertex_counter+=1
    term_to_vert[f]=vert
    #print(f,len(f))
    for i in range(1,len(f)):
        if f[i] in term_to_vert:
            #print(f[i],"yes")
            #note:have built all vertices by this pint
            graph[vert].append(term_to_vert[f[i]])
            predecessors[term_to_vert[f[i]]].append(vert)
        else:
            if type(f[i]) is tuple:
                fvert = build_func_graph(f[i])
                graph[vert].append(fvert)
            else:
                fvert = build_var_graph(f[i])
                graph[vert].append(fvert)
            predecessors[fvert].append(vert)

    return vert

def build_graph():
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert

    for (a,b) in equalities:
        if type(a) is tuple:
            build_func_graph(a)
        else:
            build_var_graph(a)

        if type(b) is tuple:
            build_func_graph(b)
        else:
            build_var_graph(b)
    


def naive_congruence_closure():
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    for (a,b) in equalities:
        naive_merge(term_to_vert[a],term_to_vert[b])
        
def naive_merge(u,v):
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    if uf.connected(u,v):
        return
    Pu=eq_class_to_pred_list[uf.find(u)]
    Pv=eq_class_to_pred_list[uf.find(v)]
    merge(u,v)
    uf.union(u,v)
    
    for x in Pu:
        for y in Pv:
            #print(x,y,is_congruent(x,y))
            if not uf.connected(x,y) and is_congruent(x,y):
                naive_merge(x,y)
def enter(v):
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    
 
    sig = tuple([uf.find(i) for i in graph[v]] + [v.label])
    #print("ADDING  ",v," WITH SIGNATURE ",sig," CURSTATE ",sig_table[sig])
    sig_table[sig].add(v)
def delete(v):
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    sig = tuple([uf.find(i) for i in graph[v]] + [v.label])

    #print("REMOVING  ",v," WITH SIGNATURE ",sig," CURSTATE ",sig_table[sig])
    if v in sig_table[sig]:
        sig_table[sig].remove(v)
def query(v):
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    sig = tuple([uf.find(i) for i in graph[v]] + [v.label])

    #print("QUERYING  ",v," WITH SIGNATURE ",sig," CURSTATE ",sig_table[sig])

    for e in sig_table[sig]:
            if e!=v:
                return e
    else:
        return 'lamda'

def fast_merge(u,v):
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    if uf.connected(u,v):
        return
    Pu=eq_class_to_pred_list[uf.find(u)]
    Pv=eq_class_to_pred_list[uf.find(v)]
    merge(u,v)
    uf.union(u,v)
    
    for x in Pu:
        if query(x)=='lamda':
            enter(x)
        else:
            merge(x,query(x))
            uf.union(x,query(x))
            





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
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    if len(graph[v1])!=len(graph[v2]):
        return False
    if v1.label!=v2.label:
        return False
    for i in range(len(graph[v1])):
        if not uf.connected(graph[v1][i],graph[v2][i]):
            return False
    return True


def build_uf_structure():
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    #uf = unionfind(vertex_counter)
    uf = UnionFind(graph.keys())
    for v in graph:
        eq_class_to_pred_list[uf.find(v)]=predecessors[v]



def naiverun():
    global equalities,disequalities,graph,predecessors,eq_class_to_pred_list,sig_table,uf,vertex_counter,term_to_vert
    xpoints=np.linspace(0,100,100)
    ypoints=[]
    for x in xpoints:
        print(x)
        term_to_vert=dict([])
        graph=defaultdict(list)
        predecessors=defaultdict(list)
        eq_class_to_pred_list=defaultdict(list)
        sig_table = defaultdict(set)
        equalities=[]
        disequalities=[]
        uf=0
        vertex_counter=0
        _,_,equalities,disequalities = generate_test(num_vars=100,num_funcs=10,num_equalities = int(x),num_inequalities=0)

        build_graph()
        build_uf_structure()
        t0=time.time()
        naive_congruence_closure()
        for (a,b) in disequalities:
            if a in term_to_vert and b in term_to_vert and uf.connected(term_to_vert[a],term_to_vert[b]):
                #print("UNSAT")
                t1 = time.time()
        #print("SAT")
        t1=time.time()
        ypoints.append(t1-t0)
    plt.plot(xpoints,ypoints,label='naive')
    #plt.show()


#naiverun()
#plt.show()