# Thomas Gwozdz, tgwozdz
# path_finder.py
# 
# purpose: to create random graphs and agents and 
# use a SAT solver to find optimal path of agents,
# checking the solution with other solvers


# I apologize for not separating the functions into classes!
# I built it at staggered times and didn't want to create
# a difficult-to-find bug when moving things around.

import random
import pycosat as sat
from collections import defaultdict
import sys
import itertools
import time
import math
import copy


# ---------------------
# HELPER FUNCTIONS
# ---------------------

# find adjacent vertices to v, given edges
def adjVerts(v, edges):
    adj = []
    for e in edges:
        l = edges[e]
        if l[0] == v:
            adj.append(l[1])
        elif l[1] == v:
            adj.append(l[0])
    adj.append(v)
    return adj


# find edge ID for edge between two vertices
def edge_between_verts(v1, v2, edges):
    for e in edges:
        l = edges[e]
        if l[0] == v1 and l[1] == v2:
            return e
        elif l[1] == v1 and l[0] == v2:
            return e
    return -1


# find lists of all possible positions list of agent
def poss_positions(goal, edges, T, currposes):
    if T <= 0:
        # only take poss positions where last vertex is goal
        validposes = []
        for pos in currposes:
            if pos[len(pos) - 1] == goal:
                validposes.append(pos)
        return validposes

    newcurrposes = []
    for pos in currposes:
        v = pos[len(pos) - 1]
        adjvs = adjVerts(v, edges)
        for nv in adjvs:
            newlist = copy.deepcopy(pos)
            newlist.append(nv)
            newcurrposes.append(newlist)

    return poss_positions(goal, edges, (T-1), newcurrposes)


# rotate the posses graph to make lists of where
# agent could be at each time step
def rotate_poss(posses):
    if len(posses) == 0:
        return []

    rotated = {}
    bigt = len(posses[0])
    for t in range(bigt):
        rotated[t] = []

    for i in range(len(posses)):
        for t in range(bigt):
            rotated[t].append(posses[i][t])

    rlist = []
    for t in rotated:
        rlist.append(rotated[t])
    return rlist


# ---------------------
# CONVERSION TO SAT
# ---------------------

# convert a graph problem to a set of literal clauses, a SAT input
def convert_to_sat(capV, capE, agents, edges, nt):
    # nt = # of time steps (3 if there are 3 time steps) so nt begins at 1

    #print("encoding to sat")

    def getNumEdge(agentID, edgeID, time):
        prevnum = len(agents) * len(capV) * nt + 1
        return (len(capE) * (nt-1) * agentID) + (len(capE) * time) + edgeID + prevnum


    largest = 0

    def getNum(agentID, vertexID, time):
        num = (len(capV) * nt * agentID) + (len(capV) * time) + (vertexID) + 1
        nonlocal largest
        if (largest < num):
            largest = num
        return num

    # have a variable for whether agent is at vertex at time step
    # N = # of variables = |agents| x |capV| x t
    clauses = []
    tt = nt - 1
    numA = len(agents)
    numV = len(capV)

    # agent must start at first position
    firstpos = []
    for i in range(len(agents)):
        x = getNum(i, agents[i][0], 0)
        firstpos.append([x])
    clauses.extend(firstpos)

    # agent must end on goal position
    lastpos = []
    for i in range(len(agents)):
        x = getNum(i, agents[i][1], tt)
        lastpos.append([x])
    clauses.extend(lastpos)

    # agent is at at most one vertex per time step
    single = []
    for time in range(nt):
        for a in range(len(agents)):
            for v1 in range(len(capV)):
                for v2 in range((v1+1), len(capV)):
                    x1 = getNum(a, v1, time)
                    x2 = getNum(a, v2, time)
                    single.append([-x1, -x2])
    clauses.extend(single)

    # agent is at at least one vertex per time step
    single = []
    for time in range(nt):
        for a in range(len(agents)):
            allVertices = []
            for v in range(len(capV)):
                x = getNum(a, v, time)
                allVertices.append(x)
            single.append(allVertices)
    clauses.extend(single)

    # agent moves to adjacent vertex or stays put
    move = []
    for time in range(tt-1):
        for a in range(len(agents)):
            for v in range(len(capV)):
                x = getNum(a, v , time)
                forward = [-x]
                x = getNum(a, v, time+1)
                forward.append(x)
                for nv in adjVerts(v, edges):
                    x = getNum(a, nv, time+1)
                    forward.append(x)
                move.append(forward)
    clauses.extend(move)

    # agent moves to adjacent vertex or stays put
    move = []
    for time in range(1, nt):
        for a in range(len(agents)):
            for v in range(len(capV)):
                x = getNum(a, v , time)
                forward = [-x]
                x = getNum(a, v, time-1)
                forward.append(x)
                for nv in adjVerts(v, edges):
                    x = getNum(a, nv, time-1)
                    forward.append(x)
                move.append(forward)
    clauses.extend(move)

    # ---------------------
    # OLD IMPLEMENTATION START
    # ---------------------
    # at most capV(v) agents per vertex per time step
    # I decided to leave this as-is (without optimization) for
    # at-most-1 because I believe it could (possibly) decrease
    # runtime less than optimization of capE(e) constraints
    # OLD
    # N = []
    # for time in range(nt):
    #     for v in range(len(capV)):
    #         cap = capV[v]
    #         if cap >= len(agents):
    #             continue
    #         else:
    #             agentComb = itertools.combinations(range(len(agents)), cap + 1)
    #             for c in agentComb:
    #                 Vert = []
    #                 for a in c:
    #                     x = getNum(a, v, time)
    #                     Vert.append(-x)
    #                 N.append(Vert)
    # clauses.extend(N)

    # # MIGHT BE ABLE to be made easier using itertools.product
    # # at most capE(e) agents per edge per time step
    # E = []
    # for time in range(0, tt):
    #     for e in edges:
    #         v1 = edges[e][0]
    #         v2 = edges[e][1]
    #         k = capE[e]
    #         # if no way the edge could be filled, continue
    #         if k >= len(agents):
    #             continue
    #         # for every k+1 agent sets
    #         agentComb = itertools.combinations(range(len(agents)), k + 1)
    #         # combo is a set of k+1 agent IDs
    #         for combo in agentComb:
    #             agentSpots = []
    #             for a in combo:
    #                 fvf = getNum(a, v1, time)
    #                 svs = getNum(a, v2, time+1)
    #                 svf = getNum(a, v2, time)
    #                 fvs = getNum(a, v1, time+1)
    #                 len4 = [fvf, svs, svf, fvs]
    #                 agentSpots.append(len4)

    #             # generate all binary numbers from 0 to 2^{k+1}-1
    #             for i in range(0, (k+1)+1):
    #                 binagents = itertools.combinations(combo, i)
    #                 for sa in binagents:
    #                     cl = []
    #                     count = 0
    #                     for agent in combo:
    #                         if agent in sa:
    #                             x1 = agentSpots[count][0]
    #                             x2 = agentSpots[count][1]
    #                             cl.append(-x1)
    #                             cl.append(-x2)
    #                         else:
    #                             x1 = agentSpots[count][2]
    #                             x2 = agentSpots[count][3]
    #                             cl.append(-x1)
    #                             cl.append(-x2)
    #                         count += 1
    #                     E.append(cl)

    # clauses.extend(E)
    # ---------------------
    # OLD IMPLEMENTATION END
    # ---------------------


    # ---------------------
    # NEW IMPLEMENTATION START
    # ---------------------
    # encoding extra edge variables
    # last number to be used
    # increment and then use
    lastnum = len(agents) * len(capV) * nt
    lastnum += 1

    def newNum():
        nonlocal lastnum
        lastnum += 1
        return lastnum

    edgesnums = {} # key: a, e, t (t = 0 if first time step)

    # these are the same
    # print("largest = %d" % largest)
    # print("lastnum = %d" % lastnum)

    # Tseytin transformation
    for a in range(numA):
        for e in range(len(edges)):
            v1 = edges[e][0]
            v2 = edges[e][1]
            for t in range(tt):
                w1 = newNum()
                w2 = newNum()
                w3 = newNum()
                edgesnums[(a, e, t)] = w3

                # agents at vertices at times
                x1 = getNum(a, v1, t)
                x2 = getNum(a, v2, t+1)
                x3 = getNum(a, v2, t)
                x4 = getNum(a, v1, t+1)

                f = [[-x1, -x2, w1], [x1, -w1], [x2, -w1]]
                s = [[-x3, -x4, w2], [x3, -w2], [x4, -w2]]
                t = [[w1, w2, -w3], [-w1, w3], [-w2, w3]]

                clauses.extend(f)
                clauses.extend(s)
                clauses.extend(t)

    # for hashing variable number
    log2n = int(math.ceil(math.log(numA)/math.log(2)))

    # edge capacity constraint
    for e in range(len(edges)):
        k = capE[e] # capacity
        n = numA
        if k >= n:
            continue
        for t in range(tt):
            bs = {}
            ts = {}
            bitstr = []

            for i in range(1, k+1):
                for g in range(1, log2n+1):
                    bs[(i, g)] = newNum()

            for g in range(1, k+1):
                for i in range(1, n+1):
                    ts[(g, i)] = newNum()

            # unique bitstring
            for a in range(numA):
                bins = bin(a)[2:].zfill(log2n)
                bitstr.append(bins[::-1])

            # actual clause development
            for a in range(numA):
                w3 = edgesnums[(a, e, t)]
                firstcl = [-w3]
                for i in range(max(1, (k - n + a + 1)), (min((a+1), k)+1)):
                    firstcl.append(ts[(i, (a+1))])
                clauses.append(firstcl)

                bits = bitstr[a]
                newcls = []
                for g in range(max(1, (k - n + a + 1)), (min((a+1), k)+1)):
                    for j in range(1, log2n+1):
                        newcl = []
                        if bits[j-1:j] == '1':
                            newcl = [-ts[(g, (a+1))], bs[(g, j)]]
                        else:
                            newcl = [-ts[(g, (a+1))], -bs[(g, j)]]
                        newcls.append(newcl)
                clauses.extend(newcls)

    # vertex capacity constraint
    for v in range(len(capV)):
        k = capV[v] # capacity
        n = numA
        if k >= n:
            continue
        for time in range(nt):
            bs = {}
            ts = {}
            bitstr = []

            for i in range(1, k+1):
                for g in range(1, log2n+1):
                    bs[(i, g)] = newNum()

            for g in range(1, k+1):
                for i in range(1, n+1):
                    ts[(g, i)] = newNum()

            # unique bitstring
            for a in range(numA):
                bins = bin(a)[2:].zfill(log2n)
                bitstr.append(bins[::-1])

            # actual clause development
            for a in range(numA):
                w3 = getNum(a, v, time)
                firstcl = [-w3]
                for i in range(max(1, (k - n + a + 1)), (min((a+1), k)+1)):
                    firstcl.append(ts[(i, (a+1))])
                clauses.append(firstcl)

                bits = bitstr[a]
                newcls = []
                for g in range(max(1, (k - n + a + 1)), (min((a+1), k)+1)):
                    for j in range(1, log2n+1):
                        newcl = []
                        if bits[j-1:j] == '1':
                            newcl = [-ts[(g, (a+1))], bs[(g, j)]]
                        else:
                            newcl = [-ts[(g, (a+1))], -bs[(g, j)]]
                        newcls.append(newcl)
                clauses.extend(newcls)
    # ---------------------
    # NEW IMPLEMENTATION END
    # ---------------------

    # smarter way to remove unreachable vertices
    for a in range(numA):
        # current reachable starts at start vertex
        curr = set([agents[a][0]])
        for t in range(0, nt):
            def_false = [v for v in range(numV) if v not in curr]
            def_false_nums = [[-getNum(a, v, t)] for v in def_false]
            clauses.extend(def_false_nums)

            newcurr = []
            for v in curr:
                newcurr.extend(adjVerts(v, edges))
            curr = set(newcurr)

    # newlastnum = newNum()
    # print("newlastnum = %d" % newlastnum)
    # print(len(clauses))

    return clauses


# convert to a list of lists where each inner list is a list of 
# positions (list) for each agent at every time step
def convert_to_movements(solved, capV, agents, t):
    positions = {}
    count = 0

    for i in range(len(agents)):
        for k in range(t):
            for v in range(len(capV)):
                if solved[count] > 0:
                    pos = []
                    if i in positions:
                        pos = positions[i]
                    pos.append(v)
                    positions[i] = pos
                count += 1

    moves = []
    for a in positions:
        moves.append(positions[a])

    return moves


# ---------------------
# SOLUTION VERIFICATION
# ---------------------

# check solution {of SAT, of naive solvers} 
# to see if it is a valid solution to graph
def check_sol(positions, edges, agents, capV, capE, t):
    for a in range(len(agents)):
        moves = positions[a]
        # check that agent starts and ends at correct vertices
        if moves[0] != agents[a][0]:
            #print("Agent doesn't start at \"start\" vertex.")
            #print("first %d, start %d, agent %d" % (moves[0], agents[a][0], a))
            return False
        if moves[-1] != agents[a][1]:
            #print("Agent doesn't end at \"end\" vertex.")
            return False

        # check that agent moves to adjacent vertices only
        for i in range(1, len(moves)):
            if moves[i] not in adjVerts(moves[i-1], edges):
                #print("Agent moved to non-adjacent vertex!")
                return False

        # check that an agent has a position at each time
        if len(positions[a]) != t:
            #print("Agent doesn't have a position for every time step")
            #print("len %d, t %d" % (len(positions[a]),t))
            return False

    # check that capacity of each vertex not exceeded
    for i in range(t):
        vertCaps = {}
        for a in range(len(agents)):
            currv = positions[a][i]
            if currv not in vertCaps:
                vertCaps[currv] = 1
            else:
                vertCaps[currv] += 1
        for v in vertCaps:
            if vertCaps[v] > capV[v]:
                #print("Vertex over capacity.")
                return False

    # check that capacity of each edge not exceeded
    for i in range(1, t):
        edgeCaps = {}
        for a in range(len(agents)):
            currv = positions[a][i]
            prevv = positions[a][i-1]
            if currv == prevv:
                continue
            e = edge_between_verts(currv, prevv, edges)
            if e == -1:
                #print("Edge cannot be found between %d and %d." % (currv, prevv))
                return False
            else:
                if e not in edgeCaps:
                    edgeCaps[e] = 1
                else:
                    edgeCaps[e] += 1
        for e  in edgeCaps:
            if edgeCaps[e] > capE[e]:
                #print("Edge %d over capacity. (%d > %d)" % (e, edgeCaps[e], capE[e]))
                return False

    return True


# ---------------------
# GRAPH GENERATION
# ---------------------

# generate a random graph with various bounds
def generate_graph(numV, numE, numA, lowC, highC):
    capV = {}        # vertex ID -> capacity
    capE = {}        # edge ID -> capacity
    agents = {}      # agent ID -> start vertex, goal vertex
    alledges = []    # all possible start, end vertices for edges
    someedges = []   # edges chosen randomly
    somepaths = []   # paths chosen randomly
    edges = {}       # edge ID -> start vertex, end vertex

    for i in range(numV):
        capV[i] = random.randint(lowC, highC)

    for i in range(numE):
        capE[i] = random.randint(lowC, highC)

    for i in range(numV):
        for j in range(i+1, numV):
            alledges.append([i, j])

    someedges = random.sample(alledges, numE)
    somepaths = random.sample(alledges, numE)

    for i in range(numE):
        edges[i] = someedges[i]

    for i in range(min(numA, len(somepaths))):
        agents[i] = somepaths[i]

    return capV, capE, agents, edges


# generate graph from bounds and print graph
def make_graph(numV, numE, numA, lowC, highC):
    capV, capE, agents, edges = generate_graph(numV, numE, numA, lowC, highC)
    #print_graph_abr(capV, capE, agents, edges)
    return capV, capE, agents, edges


# generate random numbers and make graph from them
def generate_random_graph():
    numV = random.randint(3, 10)
    numE = random.randint(3, numV)
    numA = random.randint(5, 5)
    lowC = random.randint(1, 1)
    highC = random.randint(lowC, 1)
    capV, capE, agents, edges = make_graph(numV, numE, numA, lowC, highC)
    return capV, capE, agents, edges


# generate random numbers and make graph from them
def generate_random_graph_specific(numa, numv, nume):
    numV = numv
    numE = nume
    numA = numa
    lowC = random.randint(2, 10)
    highC = random.randint(lowC, 15)
    capV, capE, agents, edges = make_graph(numV, numE, numA, lowC, highC)
    return capV, capE, agents, edges


# generate random graph in the shape of a grid;
# every vertex is connected to its adjacent neighbors in the cardinal directions
def generate_random_graph_grid(width, height, numA, lowC, highC):

    # check if an edge exists between v1 and v2
    def edge_exists(v1, v2, edges):
        for edge in edges:
            s = edges[edge][0]
            t = edges[edge][1]

            if v1 == s and v2 == t:
                return True
            elif v2 == s and v1 == t:
                return True

        return False

    capV = {}     # vertex ID -> capacity
    capE = {}     # edge ID -> capacity
    agents = {}   # agent ID -> start vertex, goal vertex
    edges = {}    # edge ID -> start vertex, end vertex

    edgecount = 0

    for i in range(width):
        for j in range(height):
            vert = (j * width) + i

            capV[vert] = random.randint(lowC, highC)

            # if at an inner vertex
            vertl = (j * width) + (i-1)
            vertr = (j * width) + (i+1)
            vertu = ((j-1) * width) + i
            vertd = ((j+1) * width) + i

            if not edge_exists(vert, vertl, edges) and (i-1) >= 0:
                edges[edgecount] = [vert, vertl]
                capE[edgecount] = random.randint(lowC, highC)
                edgecount += 1

            if not edge_exists(vert, vertr, edges) and (i+1) <= width - 1:
                edges[edgecount] = [vert, vertr]
                capE[edgecount] = random.randint(lowC, highC)
                edgecount += 1

            if not edge_exists(vert, vertu, edges) and (j-1) >= 0:
                edges[edgecount] = [vert, vertu]
                capE[edgecount] = random.randint(lowC, highC)
                edgecount += 1

            if not edge_exists(vert, vertd, edges) and (j+1) <= height - 1:
                edges[edgecount] = [vert, vertd]
                capE[edgecount] = random.randint(lowC, highC)
                edgecount += 1

    for i in range(numA):
        s = random.randint(0, width*height - 1)
        t = random.randint(0, width*height - 1)
        agents[i] = [s, t]

    return capV, capE, agents, edges


# generate random graph
# for each possible edge, form edge with probability p
def generate_random_graph_prob(numV, numA, lowC, highC, p):
    capV = {}     # vertex ID -> capacity
    capE = {}     # edge ID -> capacity
    agents = {}   # agent ID -> start vertex, goal vertex
    edges = {}    # edge ID -> start vertex, end vertex

    edgec = 0

    for i in range(numV):
        capV[i] = random.randint(lowC, highC)

    for i in range(numV):
        for j in range(i+1, numV):
            if random.random() < p:
                edges[edgec] = [i, j]
                capE[edgec] = random.randint(lowC, highC)
                edgec += 1

    for i in range(numA):
        s = random.randint(0, numV-1)
        t = random.randint(0, numV-1)
        agents[i] = [s, t]

    return capV, capE, agents, edges


# ---------------------
# PRINTER FUNCTIONS
# ---------------------

# pretty graph printing
def print_graph(capV, capE, agents, edges):
    print("------GRAPH------")
    print("VERTICES")
    for i in range(len(capV)):
        print("vertex %d has capacity %d" % (i, capV[i]))
    print("EDGES")
    for i in range(len(capE)):
        sv, ev = edges[i]
        print("edge %d has capacity %d and connects %d and %d" % (i, capE[i], sv, ev))
    print("AGENTS")
    for i in range(len(agents)):
        sv, ev = agents[i]
        print("agent %d is traveling from %d to %d" % (i, sv, ev))
    print("-----------------")
    return


# abbreviated pretty graph printing
def print_graph_abr(capV, capE, agents, edges):
    print("------GRAPH------")
    print("VERTICES")
    print("There are %d vertices" % (len(capV)))
    print("EDGES")
    print("There are %d edges" % (len(capE)))
    print("AGENTS")
    print("There are %d agents" % (len(agents)))
    return


# pretty printing of agent movements
def print_movements(positions):
    if len(positions) == 0:
        return
    if len(positions[0]) == 0:
        return

    for a in range(len(positions)):
        print("Agent %d: " % a, end='')

        for i in range(len(positions[a])):
            v = positions[a][i]
            print("%d" % v, end='')
            if i < len(positions[a])-1:
                print(" -> ", end='')

        print("")

    return


# call pretty printing of solutions list
def print_sol(correctpos, solvetime, solver, numsol=-1):
    print("------------------")
    print("%s SOLUTION" % solver)
    if numsol == -1:
        numsol = len(correctpos)
    i = len(correctpos[0][0])

    if (numsol <= 0):
        print("There are no solutions.")
    elif (numsol < 2):
        print("This is a unique solution in %d time steps." % i)
        print_movements(correctpos[0])
    else:
        print("There are %d solution(s) in %d time steps." % (numsol, i))

    print("------------------")
    print("Solve:  \t%.2f s" % (solvetime))
    print("------------------")
    return


# ---------------------
# SOLVER FUNCTIONS
# ---------------------

# solves MAPF-CG instance using brute force, naive 
# searching of entire solution space
def solve_graph_iter(capV, capE, agents, edges, T):
    solvestart = time.time()
    numv = len(capV)
    numa = len(agents)

    for i in range(1, T+1):
        vertiter = itertools.product(range(numv), repeat=i)
        posspos = [list(pos) for pos in vertiter]

        positer = itertools.product(posspos, repeat=numa)
        possmoves = [list(pos) for pos in positer]

        correctpos = []
        for positions in possmoves:
            if (check_sol(positions, edges, agents, capV, capE, i)):
                correctpos.append(positions)

        if len(correctpos) > 0:
            solveend = time.time()
            solvetime = solveend - solvestart

            return correctpos, solvetime, "ITER"

    return [[[]]], 0, "ITER"


# less-naive brute force solution that searches through
# all reachable solution space
def solve_graph_smart(capV, capE, agents, edges, T):
    solvestart = time.time()
    numv = len(capV)
    numa = len(agents)

    for i in range(1, T+1):
        args = []
        lenzero = False
        for a in range(numa):
            posspos = poss_positions(agents[a][1], copy.deepcopy(edges), (i-1), [[agents[a][0]]])
            if len(posspos) <= 0:
                lenzero = True
            args.append(posspos)

        if lenzero:
            continue

        positer = itertools.product(*args)
        possmoves = [list(pos) for pos in positer]

        correctpos = []
        for positions in possmoves:
            if (check_sol(positions, edges, agents, capV, capE, i)):
                # CHANGED TO TEST
                # solveend = time.time()
                # solvetime = solveend - solvestart
                # return [positions], solvetime, "SMART"
                # COMMENT OUT ABOVE LINES TO PREVIOUS COMMENT AND
                # UNCOMMENT LINE BELOW TO SEE ORIGINAL FUNCTION

                correctpos.append(positions)
                

        if len(correctpos) > 0:
            solveend = time.time()
            solvetime = solveend - solvestart

            return correctpos, solvetime, "SMART"

    return [[[]]], 0, "SMART"


# SAT SOLVER function
# for a max of T time steps, see if graph is solvable
def solve_graph_sat(capV, capE, agents, edges, T):
    totalstart = time.time()
    for i in range(1, T+1):
        clausestart = time.time()
        clauses = convert_to_sat(capV, capE, agents, edges, i)
        clauseend = time.time()

        solvestart = time.time()
        solved = sat.solve(clauses)
        solveend = time.time()

        clausetime = clauseend - clausestart
        solvetime = solveend - solvestart

        if not isinstance(solved, str):
            totalend = time.time()
            movements = convert_to_movements(solved, capV, agents, i)

            # to get complete time
            #return [movements], totalend - totalstart, "SAT", 1

            # to get clause time
            return [movements], clauseend - clausestart, "SAT", 1

    return [[[]]], 0, "SAT", 0


# ---------------------
# TESTING
# ---------------------

# a small test case
def make_medium_test_graph():
    #  0 - - 3 - - 6
    #  | \       / |
    #  |   \   /   |
    #  1     4     7
    #  |   /   \   |
    #  | /       \ |
    #  2 - - 5 - - 8
    capV = {0: 1, 1: 1, 2: 1, 3: 2, 4: 1, 5: 1, 6: 2, 7: 1, 8: 1}
    capE = {0: 1, 1: 1, 2: 1, 3: 1, 4: 1, 5: 1, 6: 2, 7: 1, 8: 1, 9: 1, 10: 1, 11: 1}
    edges = {0: [0, 1], 1: [1, 2], 2: [2, 5], 3: [5, 8], 4: [8, 7], 5: [7, 6], 6: [6, 3], 7: [3, 0], 8: [0, 4], 9: [4, 6], 10: [2, 4], 11: [4, 8]}
    agents = {0: [7, 3], 1: [4, 3]}

    correctpos, time, solver, numsols = solve_graph_sat(capV, capE, agents, edges, 3)
    print_sol(correctpos, time, solver, numsols)

    correctpos, time, solver = solve_graph_iter(capV, capE, agents, edges, 3)
    print_sol(correctpos, time, solver)

    correctpos, time, solver = solve_graph_smart(capV, capE, agents, edges, 3)
    print_sol(correctpos, time, solver)
    return

# an even smaller test case
def make_small_test_graph():
    # 0 - - 1 - - 2
    capV = {0: 2, 1: 1, 2: 2}
    capE = {0: 2, 1: 2}
    edges = {0: [0, 1], 1: [1, 2]}
    agents = {0: [0, 2], 1: [0, 2]}
    
    correctpos, time, solver, numsols = solve_graph_sat(capV, capE, agents, edges, 3)
    print_sol(correctpos, time, solver, numsols)

    correctpos, time, solver = solve_graph_iter(capV, capE, agents, edges, 3)
    print_sol(correctpos, time, solver)
    return


# test solutions against each other to 
# verify optimality
def test_sols():
    print("TESTING SOLUTIONS")
    n = 200
    numpassed = 0
    i = 0

    # test on n graphs
    while(i < n):
        #print("TEST %d" % (i+1))

        #capV, capE, agents, edges = generate_random_graph()
        capV, capE, agents, edges = generate_random_graph_prob(5, 3, 1, 2, 0.1)
        if (i % 2 == 0):
            capV, capE, agents, edges = generate_random_graph_grid(4, 4, 4, 1, 2)


        scorrectpos, _, _, numsols = solve_graph_sat(capV, capE, agents, edges, 3)
        # icorrectpos, _, _ = solve_graph_iter(capV, capE, agents, edges, 3)
        smcorrectpos, _, _ = solve_graph_smart(capV, capE, agents, edges, 3)

        satsort = sorted(scorrectpos, key=lambda t: t[0])
        # itersort = sorted(icorrectpos, key=lambda t: t[0])
        smartsort = sorted(smcorrectpos, key=lambda t: t[0])

        match = False
        for smartsol in smartsort:
            if satsort[0] == smartsol:
                if satsort[0] != [[]]:
                    i += 1
                    numpassed += 1
                match = True
                break
        if not match:
            print("FAILED")
            print("agents")
            print(agents)
            print('edges')
            print(edges)
            print("capE")
            print(capE)
            print("capV")
            print(capV)
            print("sat")
            print(satsort[0])
            print('smart')
            for smartsol in smartsort:
                print(smartsol)


    print("PASSED: %d / %d" % (numpassed, n))


# testing a solver (averaged over itern iterations)
# for a specified number of vertices, edges and agents
def test_sol_specific(numa, itern, n):
    i = 0
    total = 0
    
    while (i < itern):
        # generate_random_graph_grid(width, height, numA, lowC, highC)
        # generate_random_graph_prob(numV, numA, lowC, highC, p):
        capV, capE, agents, edges = generate_random_graph_prob(n, numa, max(1, int(numa/8)), int(numa/2), (math.log(n)/n)*1.01)

        # check that graph is fully connected
        conn = set([])
        for e in edges:
            v1 = edges[e][0]
            v2 = edges[e][1]
            conn.add(v1)
            conn.add(v2)

        numV = len(capV)
        missing = False
        for v in capV:
            if not v in conn:
                missing = True

        if missing:
            continue

        print("found a connected graph!")

        satsort, time, kind, numsols = solve_graph_sat(capV, capE, agents, edges, 10)

        # satsort, time, kind = solve_graph_smart(capV, capE, agents, edges, 7)

        print_movements(satsort[0])

        if (satsort != [[[]]]):
            total += time
            #print("round %d" % i)
            i += 1

    print("Averaged over %d iterations and %d vertices: %.2f" % (itern, n, total/itern))


def timing():
    #x = [50, 100, 150, 200, 250, 300]
    # x = [350, 400, 450, 500]
    x = [550, 600, 650, 700, 750, 800]
    for a in x:
        test_sol_specific(5, 10, a)


def test_connectedness():
    n = 100
    avg = 0
    numV = 50
    for i in range(n):
        capV, capE, agents, edges = generate_random_graph_prob(100, 1, 1, 1, 0.05)
        conn = set([])
        for e in edges:
            v1 = edges[e][0]
            v2 = edges[e][1]
            conn.add(v1)
            conn.add(v2)

        numV = len(capV)
        numconn = 0.0
        for v in capV:
            if v in conn:
                numconn += 1
        avg += float(numconn/numV)
    print("%.2f avg connected" % (avg/n))




# generate_random_graph()
# make_medium_test_graph()
# make_small_test_graph()
# pycosat()
# test_sols()
# capV, capE, agents, edges = generate_random_graph_grid(2, 2, 0, 5, 10)
# print_graph(capV, capE, agents, edges)
# test_connectedness()
# timing()
# test_sol_specific(5, 10)
test_sol_specific(100, 2, 100)




