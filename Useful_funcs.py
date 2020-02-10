import networkx as nx
import itertools
import heapq as hq
import timeit

def calc_bfs(G,start):
    '''
    This is the BFS which assigns vertices their level and counts number of vertices per level
    '''
    starttime = timeit.default_timer()
    nx.set_node_attributes(G,False,'seen')
    q = [start]
    nodeLevel = {0:[start]}
    nx.set_node_attributes(G,{start:True},'seen')
    nx.set_node_attributes(G,{start:0},'level')
    while q:
        curr = q.pop(0)
        y = G.nodes[curr]['level']
        try:
            nodeLevel[y+1]
        except:
            nodeLevel[y+1] = []
        for n in G.neighbors(curr):
            if G.nodes()[n]['seen']==False:
                q.append(n)
                nodeLevel[y+1].append(n)
                nx.set_node_attributes(G,{n:True},'seen')
                nx.set_node_attributes(G,{n:y+1},'level')
    del nodeLevel[max(nodeLevel, key=int)]
#     print(f"BFS time (V={len(G)},E={G.size()}): ",timeit.default_timer()-starttime)
    return nodeLevel,timeit.default_timer()-starttime


def calc_level_bound(nlvl,k):
    starttime = timeit.default_timer()
    '''
    diam^k calc of level-based lower bound for all combinations of levels
    '''
    fortesting = []
    def rec_level_bound(fortesting,nlvl,bound,lcount,S,memo,Q,k=1):
        if type(S[k]) is int:
            if lcount[S[k-1]]>0: #cannot have more sources than nodes per level
                S[k]=S[k-1]
            else:
                S[k] = S[k-1]+1
            lcount[S[k]] -= 1
            while S[k]<len(nlvl):
                newBound = bound           ## S needs a dud at the end and a static 0 to at the start
                if S[k] != S[k-1]:
                    if (S[k-1],S[k]) in memo:
                        newBound += memo[(S[k-1],S[k])]
                    else:
                        m = (S[k]+S[k-1])//2 #m is the midpoint between two levels
                        count = 0
                        for x in range(S[k-1]+1,m+1):
                            count+=len(nlvl[x])*(x-S[k-1])
                        for x in range(m+1,S[k]):
                            count+=len(nlvl[x])*(S[k]-x)
                        count += len(nlvl[S[k]])
                        memo[(S[k-1],S[k])] = count
                        newBound += count
                rec_level_bound(fortesting,nlvl,newBound,lcount,S,memo,Q,k+1)
                lcount[S[k]] +=1
                S[k]+=1
                lcount[S[k]] -= 1
        else:
                count = 0
                if (S[k-1],-1) in memo:
                    bound += memo[(S[k-1],-1)]
                else:
                    count = 0
                    for i in range(S[k-1],len(nlvl)):  #not adding one to start of range because using S[k-1] old position
                        count += len(nlvl[i])*(i-S[k-1])
                    memo[(S[k-1],-1)] = count
                    bound += count
                bound -= (len(S)-1)   #counted source nodes as 1 when should be 0, excluding 'F' entry for final segment
                Q.add_task(tuple(S[:-1]+[0]),bound)  #add zero to denote level bound
                fortesting.append((tuple(S[:-1]),bound))

    S = [0 for i in range(k)]+['F']
    Q = PQ()
    memo = {}
    lcount = [len(nlvl[lvl]) for lvl in nlvl.keys()]+[k] #keep track of how many source nodes there can be per level
    for i in range(len(nlvl)):  #all possible starting positions
        lcount[i] -= 1
        bound = 0
        for j in range(0,i):
            bound += len(nlvl[j])*(i-j)
        bound += len(nlvl[i])
        rec_level_bound(fortesting,nlvl,bound,lcount,S,memo,Q)
        lcount[i]+=1
        S[0]+=1
#     print(f"LevelBound time (nlvl={nlvl},k={k}): ",timeit.default_timer()-starttime)
    return Q,timeit.default_timer()-starttime,fortesting

def brute_force_bound_3(G):
    '''
    brute force calculation of level bound for verification of accuracy.
    '''
    bound={}
    for i in G.nodes():
        I = G.nodes()[i]['level']
        for j in G.nodes():
            if i == j:
                continue
            J = G.nodes()[j]['level']
            for k in G.nodes():
                if k == i or k==j:
                    continue
                b = 0
                K = G.nodes()[k]['level']
                for n in G.nodes():
                    if n == i or n == j or n == k:
                        continue
                    N = G.nodes()[n]['level']
                    mini =  min(abs(I-N),abs(J-N),abs(K-N))
                    b += max(mini,1)
                if (I,J,K) in bound:
                    if bound[(I,J,K)] != b:
                        print("FUCK!! ")
                        print("lvls: ",I,J,K)
                else:
                    bound[(I,J,K)] = b
    return bound

def validate_level_bound_kis3(G):
    '''
    Function to compare efficient bound implementation vs brute force for accuracy validation.
    Prints out mismatches.
    '''
    nlvl = calc_bfs(G,0)
    Q = calc_level_bound(nlvl,3)
    test = brute_force_bound_3(G)
    while 1:
        try:
            task,priority = Q.pop_task()
        except:
            break
        if test[task[:-1]] != priority:
            print("ERROR: ",task,priority,test[task[:-1]])
    print("Done")

def degreeBound(S,Q,lvln,G,lvlBound, drop_val):
    '''
    lvlbound is the level-based bound of this level combination
    S is the levels in the combination
    lvln is the dictionary of level to nodes

        1) this works off the assumption that nodes arent next to each other, but some will be so we take the tighter bound..we
        should check for the case where degree bound is lower than lvlBound and return to lower bound.
       it would be better if we could catch it in the level that it happens and continue with the calc.
       this will be particularly prominent when we have multiple nodes in the same level.
    '''
    starttime = timeit.default_timer()
    bound = lvlBound - len(S)
    m = (S[0]+S[1])//2 +1
    for lvl in range(max(0,S[0]-1),min(S[0]+2,m)): #includes m
        bound += len(lvln[lvl])
    superQ = [[[node],bound] for node in lvln[S[0]]]
    for supr in superQ:
        supr[1] -= G.degree[supr[0][0]]
    for i in range(len(S[1:-1])):      #can definitely improve on this i+1 shit
        mNext = (S[i+1]+S[i+2])//2 + 1  #we use m as a way to prevent calculating the same level more than once.
        bound = 0
        for lvl in range(max(m,S[i+1]-1),min(S[i+1]+2,mNext)):
            bound += len(lvln[lvl])
        m = mNext
        for j in range(len(superQ)): # basically incrementally iterating through all possiblecombinations for given levels
            supr = superQ.pop(0)
            for node in lvln[S[i+1]]:
                if node not in supr[0]:
                    superQ.append([supr[0]+[node],supr[1]+bound - G.degree[node]]) #node combo, updated bound
    bound = 0
    for lvl in range(max(m,S[-1]),min(S[-1]+2,len(lvln))):
        bound += len(lvln[lvl])
    cnt = 0
    for j in range(len(superQ)):
        supr = superQ.pop(0)
        for node in lvln[S[-1]]:
            if node in supr[0]:
                continue
            task = tuple(supr[0]+[node,1])
            degreeBound = max(lvlBound,supr[1]+bound - G.degree[node])
            if degreeBound>=drop_val: #this is just to try save some ram
                continue
            Q.add_task(task, degreeBound)
    return timeit.default_timer() - starttime 
            if degreeBound>=drop_val: #this is just to try save some ram
                continue
            Q.add_task(task, degreeBound)
    return timeit.default_timer() - starttime

def old_optimal_centrality(G,S,Q,drop_val):
    '''
    Exact calculation of supernode total distance
    '''
    starttime = timeit.default_timer()
    S = tuple(set(S))
    if len(S)==1:
        superG = G
    else:
        superG = nx.contracted_nodes(G,S[0],S[1],self_loops = False)
    for s in S[2:]:
        superG = nx.contracted_nodes(superG,S[0],s,self_loops=False)
    nx.set_node_attributes(superG,False,'seen')      
    q = [S[0]]
    nx.set_node_attributes(superG,{S[0]:True},'seen')
    nx.set_node_attributes(superG,{S[0]:0},'level')
    centrality = 0
    while q:         
        curr = q.pop(0)
        y = superG.nodes[curr]['level']
        for n in superG.neighbors(curr):
            if superG.nodes()[n]['seen']==False:
                q.append(n)
                centrality += y+1
                if centrality>=drop_val:
                    return drop_val,timeit.default_timer()-starttime 
                nx.set_node_attributes(superG,{n:True},'seen')
                nx.set_node_attributes(superG,{n:y+1},'level')
    Q.add_task(S+(2,),centrality)
    return centrality,timeit.default_timer()-starttime

def distance_centrality(G,S,Q,drop_val):
    '''
    Exact calculation of supernode total distance
    '''
    starttime = timeit.default_timer() #for testing purposes
    nx.set_node_attributes(G,False,'seen')
    q = {}
    for i in range(len(S)):
        q[i]=[S[i]]             #one queue for each source node
        nx.set_node_attributes(G,{S[i]:True},'seen')
        nx.set_node_attributes(G,{S[i]:0},'level')
    centrality = 0
    i = 0
    while any(len(value)!=0 for value in q.values()): #while any queue still contains elements
        nex = []     #queue of nodes in next level which will be processed in next turn.
        while q[i]:  #standard BFS.
            curr = q[i].pop(0)
            y = G.nodes[curr]['level']
            for n in G.neighbors(curr):    
                if G.nodes()[n]['seen']==False:
                    nex.append(n)
                    centrality += y+1
                    if centrality>=drop_val:
                        return drop_val,timeit.default_timer()-starttime 
                    nx.set_node_attributes(G,{n:True},'seen')
                    nx.set_node_attributes(G,{n:y+1},'level')
        q[i]=nex
        i=(i+1)%len(S)      #queues take turns
        Q.add_task(S+(2,),centrality) #enqueue tuple with 2 at the end to show that the priority is of type optimal
    return centrality, timeit.default_timer()-starttime

    
def find_central_supernode(G,k):
    starttime = timeit.default_timer()
    nlvl,bfs_time = calc_bfs(G,0)
    Q,lbound_time,lbounds = calc_level_bound(nlvl,k)
    dbound_time = 0
    dbound_runs = 0
    opt_time = 0
    opt_runs = 0
    lowest_centrality = G.size()*len(G) #N*E
    while 1:
        supr,bound = Q.pop_task()
        if supr[-1] == 0:
            dbound_runs +=1
            dbound_time+=degreeBound(supr[:-1],Q,nlvl,G,bound, lowest_centrality)
        elif supr[-1] == 1:
            opt_runs+=1
            opt = distance_centrality(G,supr[:-1],Q,lowest_centrality)
            opt_time+= opt[1]
            lowest_centrality = opt[0]
        else:
#             print(f"Total algo (V={len(G)},E={G.size()},k={k}): ",timeit.default_timer()-starttime)
            return supr,bound,{'levelBounds':lbounds,'k':k,'V':len(G),'E':G.size(),'nlvls':{dist:len(nodes) for dist,nodes in nlvl.items()},'bfs':bfs_time,'lbound':lbound_time,'dbound':dbound_time,'opt':opt_time,'total':timeit.default_timer()-starttime},{'dbound':dbound_runs,'opt runs':opt_runs}

def test(G,k):
    ans = find_central_supernode(G,k)
    times = ans[2]
    times['overall'] = times['total'] - (times['lbound'] + times['dbound'] + times['bfs'] + times['opt'])
    ans[3]['nodes'] = len(G)
    ans[3]['edges'] = G.size()
    return ans[0],ans[1],times,ans[3]

class PQ:
    def __init__(self, ls=[]):
        self.pq = []                         # list of entries arranged in a heap
        self.entry_finder = {}               # mapping of tasks to entries
        self.REMOVED = '<removed-task>'      # placeholder for a removed task
        self.counter = itertools.count()     # unique sequence count
        if ls:
            for i in ls:
                self.add_task(i[0],i[1])

    def add_task(self,task, priority=0):
        'Add a new task or update the priority of an existing task'
        if task in self.entry_finder:
            self.remove_task(task)
        count = next(self.counter)
        entry = [priority, count, task]
        self.entry_finder[task] = entry
        hq.heappush(self.pq, entry)

    def remove_task(self,task):
        'Mark an existing task as REMOVED.  Raise KeyError if not found.'
        entry = self.entry_finder.pop(task)
        entry[-1] = self.REMOVED

    def pop_task(self):
        'Remove and return the lowest priority task. Raise KeyError if empty.'
        while self.pq:
            priority, count, task = hq.heappop(self.pq)
            if task is not self.REMOVED:
                del self.entry_finder[task]
                return task,priority
        raise KeyError('pop from an empty priority queue')

    def costly_print(self):
        tasks = []
        while self.pq:
            task,priority = self.pop_task()
            print(task," ",priority)
            tasks.append((task,priority))
        for i in tasks:
            self.add_task(i[0],i[1])
