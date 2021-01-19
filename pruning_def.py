"""
"""


from exh import *
from exh.utils import entails
from exh.alternatives import find_maximal_sets
from itertools import chain, combinations
import functools



def exhf(f):
    prop_set=[f.prejacent]+[i for i in f.e.innocently_incl]+[~i for i in f.e.innocently_excl]
    conj=GrandConj(MaxStrong(prop_set))
    return conj

def neg(Alt): # generates all negations of propositions in Alt
    neg=[~p for p in Alt]
    return neg

def GrandConj(Alt): # generates the grand conjunction of propositions in Alt
    conj=functools.reduce(lambda x,y: x&y,Alt)
    return conj

def MaxStrong(Alt): # outputs a list of the maxially strong propositions in Alt
    univ=Universe(fs=Alt)
    strong=[]
    for i in Alt:
        if not any (univ.equivalent(i,p) for p in strong):
            if not any(univ.entails(p,i) and not univ.entails(i,p) for p in Alt):
                strong.append(i)
    return strong

def ps(iterable): # outputs a powerset of the set of altenatives in Alt 
    s = list(iterable)
    ch=chain.from_iterable(combinations(s, r) for r in range(1,len(s)+1))
    return [list(i) for i in ch]    


# def Rel(Alt):
#     univ=Universe(fs=Alt)
#     relevant=Alt.copy()
# #     jprint("Input Alt set: ",relevant)
#     while True:
#         oldrelevant=relevant.copy()
#         relevant=relevant+[i for i in neg(relevant) if not any (univ.equivalent(i,p) for p in relevant)]
#     #     jprint("Closure under negation: ",relevant)
#         maxsetsbool=find_maximal_sets(univ,relevant)
#         arcells=np.array(relevant)
#         maxsets=[list(arcells[i]) for i in maxsetsbool]
#         cells=[]
#         [cells.append(GrandConj(MaxStrong(i))) for i in maxsets]
#         #     jprint("Cells in partition: ",cells)
#         relevant=relevant+[i for i in cells if not any(univ.equivalent(i,j) for j in relevant)]
#         if relevant==oldrelevant:
#             break
#     #     relevant=DisjClose(relevant,univ)
#     #     jprint("All unions of cells:",relevant)
#     return relevant

def GrandDisj(Alt):
    disj=functools.reduce(lambda x,y: x|y,Alt)
    return disj

def DisjClose(Alt):
    pow_set=ps(Alt)
    disj_close=[]
    [disj_close.append(GrandDisj(i)) for i in pow_set]
    return disj_close

def Cells(Alt):
    univ=Universe(fs=Alt)
    laterals=Alt+neg(Alt)
    maxsetsbool=find_maximal_sets(univ,laterals)
    arcells=np.array(laterals)
    maxsets=[list(arcells[i]) for i in maxsetsbool]
    cells=[]
    [cells.append(GrandConj(MaxStrong(i))) for i in maxsets]
    return cells

def Rel(Alt):
    relevant=[i for i in DisjClose(Cells(Alt))]
    return relevant    

def PrunRelevance(prej,Alt,subAlt):
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return not any(univ.equivalent(i,j) for i in Rel(subAlt) for j in pruned_alt)

def PrunExhaustiveRelevance(prej,Alt,subAlt):
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return not any(univ.equivalent(i,Exh(j,subAlt)) for i in Rel(subAlt) for j in pruned_alt)

def Prun1000ExhaustiveRelevance(prej,Alt,subAlt):
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
    exh_pruned=[Exh(j,subAlt) for j in pruned_alt]
    if not exh_pruned:
        rel_exh_pruned=[]
    else:
        rel_exh_pruned=Rel(exh_pruned)
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return not any(univ.equivalent(i,j) for i in Rel(pruned_alt) for j in rel_exh_pruned)

def PrunSettling(prej,Alt,subAlt):
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return not any(univ.entails(Exh(prej,subAlt),i) or univ.entails(Exh(prej,subAlt),~i) for i in pruned_alt)

def PrunWeakening(prej,Alt,subAlt):
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return univ.entails(Exh(prej,Alt),Exh(prej,subAlt))

def PrunIEII(prej,Alt,subAlt):
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return all(x in Exh(prej,Alt).e.innocently_incl or x in Exh(prej,Alt).e.innocently_incl for x in pruned_alt)

def PossiblePrunings(prej,Alt,constraint):
    pow_alt=[i for i in ps(Alt) if prej in i]
    possible_prunings=[]
    [possible_prunings.append(i) for i in pow_alt if constraint(prej,Alt,i)]
    return possible_prunings


