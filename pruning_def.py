"""
"""

from exh import *
from exh.utils import entails
from exh.alternatives import find_maximal_sets
from itertools import chain, combinations
import functools



def exhf(f): # outputs a formula equivalent to an exh expression
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

def GrandDisj(Alt): # takes a set and returns its grand disjunction
    disj=functools.reduce(lambda x,y: x|y,Alt)
    return disj

def DisjClose(Alt): # closes a set under disjunction
    pow_set=ps(Alt)
    disj_close=[]
    [disj_close.append(GrandDisj(i)) for i in pow_set]
    return disj_close

def Cells(Alt): # finds all the cells in the partition induced by a set of alternatives
    univ=Universe(fs=Alt)
    laterals=Alt+neg(Alt) # begin with a set of all alternatives an their negations
    maxsetsbool=find_maximal_sets(univ,laterals) # find maximal consistent sets of (negations of) alternatives
    arcells=np.array(laterals)
    maxsets=[list(arcells[i]) for i in maxsetsbool]
    cells=[]
    [cells.append(GrandConj(MaxStrong(i))) for i in maxsets] # each cell is a grand conjunction of a maximal consistent set of (negations of) alternatives  
    return cells

def Rel(Alt): # finds all the unions of cells in the partition induced by a set of alternatives
    relevant=[i for i in DisjClose(Cells(Alt))]
    return relevant    

def PrunRelevance(prej,Alt,subAlt): # returns true only if subAlt is a licit choice of pruning given prej and Alt assuming Pruning by Relevance 
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return not any(univ.equivalent(i,j) for i in Rel(subAlt) for j in pruned_alt)

def PrunExhaustiveRelevance(prej,Alt,subAlt): # returns true only if subAlt is a licit choice of pruning given prej and Alt assuming Pruning by Exhaustive Relevance 
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return not any(univ.equivalent(i,Exh(j,subAlt)) for i in Rel(subAlt) for j in pruned_alt)

def PrunSettling(prej,Alt,subAlt): # returns true only if subAlt is a licit choice of pruning given prej and Alt assuming Pruning by Non-settling 
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return not any(univ.entails(Exh(prej,subAlt),i) or univ.entails(Exh(prej,subAlt),~i) for i in pruned_alt)

def PrunWeakening(prej,Alt,subAlt): # returns true only if subAlt is a licit choice of pruning given prej and Alt assuming Pruning by weakening 
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return univ.entails(Exh(prej,Alt),Exh(prej,subAlt))

def PrunIEII(prej,Alt,subAlt): # returns true only if subAlt is a licit choice of pruning given prej and Alt assuming Pruning of exclufdable or includable alternatives 
    univ=Universe(fs=Alt)
    pruned_alt=[i for i in Alt if i not in subAlt]
#     jprint("Formal alternatives: ",Alt)
#     jprint("Chosen subset: ",subAlt)
#     jprint("Pruned alternatives: ",pruned_alt)
    return all(x in Exh(prej,Alt).e.innocently_incl or x in Exh(prej,Alt).e.innocently_incl for x in pruned_alt)

def PossiblePrunings(prej,Alt,constraint): # returns a list of all possible prunings given a prejacent, a set of alternatives, and a constraint on pruning 
    pow_alt=[i for i in ps(Alt) if prej in i]
    possible_prunings=[]
    [possible_prunings.append(i) for i in pow_alt if constraint(prej,Alt,i)]
    return possible_prunings


