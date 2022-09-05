#!/usr/bin/env python3

'''
    Kód k bakalářské práci v jazyce Python 3.
    Autor: Ondřej Polanský
    FIT VUT
    Brno 24.04.2020
    Obsah:
        datové struktury - třídy a jejich metody
        parsování automatů ze vstupu
        jednotlivé implementace algoritmů
        funkce main a měření
'''

import copy                             # deepcopy
from queue import Queue                 # for most algorithms
from collections import defaultdict, Counter     # transit_states
import sys                              # argument parsing and stdin
import time

determinization_fail_switch = False     # true -> determinization will add fail state, false -> determinization will not add false state

# ---------------------------------------------------------------------------------------------------------------
#                                               CLASS DEFINITIONS
# ---------------------------------------------------------------------------------------------------------------

# state of the automaton - elements of the class will not change
class State:
    __slots__ = ["name","transit_states","reversed_transit_states","final_st","start_st","visited","flag","index","card"]
    def __init__(self,name="",transit_states=None,reversed_transit_states=None,final_st=False,start_st=False,visited=False,flag=0,index=-1,card=None):
        self.name = name                                            # name of the state
        if transit_states == None:
            self.transit_states = defaultdict(list)                 # dict of transitions {letter_alphabet,[state,...]}  list/set .append/.add
        else:
            self.transit_states = copy.deepcopy(transit_states)
        if reversed_transit_states == None:
            self.reversed_transit_states = defaultdict(list)        # dict of reversed transitions {letter_alphabet,[state,...]}
        else:
            self.reversed_transit_states = copy.deepcopy(reversed_transit_states)
        self.final_st = final_st                                    # bool value: true if state is final
        self.start_st = start_st                                    # bool value: true if state is starting
        self.visited = visited                                      # bool value - used by some algorithms
        self.flag = flag                                            # int number - used by some algorithms
        self.index = index                                          # "self" index into the list of states
        if card == None:
            self.card = {}                                          # used by the NFA reduction algorithm {letter:number_of_transitions}
        else:
            self.card = copy.deepcopy(card)

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    # next functions are getters and setters of variables
    def add_transit_state(self, letter, state):
        self.transit_states[letter].append(state)

    def add_reversed_transit_state(self, letter, state):
        self.reversed_transit_states[letter].append(state)

    def remove_transit_state(self, letter, state):
        temp_list = self.transit_states[letter]
        for ind, st in enumerate(temp_list):
            if st.name == state.name:
                temp_list[ind] = temp_list[-1]
                break
        temp_list.pop()

    def remove_reversed_transit_state(self, letter, state):
        temp_list = self.reversed_transit_states[letter]
        for ind, st in enumerate(temp_list):
            if st.name == state.name:
                temp_list[ind] = temp_list[-1]
                break
        temp_list.pop()

    # returns a list of [state, ...] accessible from self state in transit dictionaries
    def get_transit_states_values(self):
        return self.transit_states.values()

    def get_reversed_transit_states_values(self):
        return self.reversed_transit_states.values()

    # returns a list of pairs [(letter, [state, ...]), ...]
    def get_transit_states_items(self):
        return self.transit_states.items()

    def get_reversed_transit_states_items(self):
        return self.reversed_transit_states.items()

    # returns a list of states accessible from self state
    def get_transit_states(self, letter):
        return self.transit_states[letter]

    def get_reversed_transit_states(self, letter):
        return self.reversed_transit_states[letter]

    # swaps transit_states and reversed_transit_states, helps to construct a reversed automaton
    def swap_transitions(self):
        self.transit_states, self.reversed_transit_states = self.reversed_transit_states, self.transit_states

    # clears transit state dictionaries
    def clear_transit_states(self):
        self.transit_states = defaultdict(list)

    def clear_reversed_transit_states(self):
        self.reversed_transit_states = defaultdict(list)

# finite automaton
class FA:
    __slots__ = ["name","states","alphabet","start_states","final_states"]
    def __init__(self,name="",states=None,alphabet=None,start_states=None,final_states=None):
        self.name = name                                            # name of the automaton
        if states == None:
            self.states = []                                        # list of states
        else:
            self.states = copy.deepcopy(states)
        if alphabet == None:
            self.alphabet = []                                      # list of alphabet - sorted during parsing
        else:
            self.alphabet = copy.deepcopy(alphabet)
        if start_states == None:
            self.start_states = set()                               # set of start states
        else:
            self.start_states = copy.deepcopy(start_states)
        if final_states == None:
            self.final_states = set()                               # ?ordered? set of final states
        else:
            self.final_states = copy.deepcopy(final_states)

    # constructs a reversed automaton
    def reverse_automaton(self):
        for state in self.states:
            state.swap_transitions()
            state.card = {}
            state.start_st, state.final_st = state.final_st, state.start_st
        self.start_states, self.final_states = self.final_states, self.start_states

    # creates a shallow copy of automaton and returns it
    def copy_FA(self):
        result_automaton = FA(name=self.name,alphabet=self.alphabet)
        relations = {}
        for state in self.states:
            relations[state.name] = []

        for s in self.states:
            st = State(s.name)
            st.start_st = s.start_st
            st.final_st = s.final_st
            st.flag = 0
            st.visited = False
            result_automaton.states.append(st)

            for a in self.alphabet:
                for targ_state in s.get_transit_states(a):
                    relations[targ_state.name].append((a, st))
            if st.start_st: result_automaton.start_states.add(st)
            if st.final_st: result_automaton.final_states.add(st)

        for s in result_automaton.states:
            for fst, snd in relations[s.name]:
                snd.add_transit_state(fst, s)
                s.add_reversed_transit_state(fst, snd)
        return result_automaton

    # print function, used for printing results
    def __str__(self):
        ret_str = ""
        for st in self.states:
            for lt, tr in st.get_transit_states_items():
                for targ in tr:
                    ret_str += st.name + "(" + lt + ")->" + targ.name + ", "
        return "Printing automaton " + self.name + "\n"                                             \
             + "Q = " + str([st.name for st in self.states]) + "\n"                                 \
             + "A = " + str(self.alphabet) + "\n"                                                   \
             + "r = {" +  ret_str[:-2] + "}\n"                                                      \
             + "s = {" + str(", ".join([st.name for st in self.start_states])) + "}\n" \
             + "F = {" + str(", ".join([st.name for st in self.final_states])) + "}\n"

    # print function, used for debugging purposes
    def debug_print(self):
        ret_str = ""
        for st in self.states:
            if st.flag == -1:
                continue
            ret_str += "\t" + st.name + " (final: " + str(st.final_st) + ", start: " + str(st.start_st) + ", visited: " + str(st.visited) + ", flag: " + str(st.flag) + "):\n"
            for lt, tr in st.get_transit_states_items():
                for targ in tr:
                    ret_str += "\t\tNext state: (" + lt + ", " + targ.name + ")\n"
            for lt, tr in st.get_reversed_transit_states_items():
                for targ in tr:
                    ret_str += "\t\tPrev state: (" + lt + ", " + targ.name + ")\n"
        return "Printing automaton " + self.name + "\n" \
             + "Q = {\n" + ret_str + "}\n"\
             + "A = " + str(self.alphabet) + "\n" \
             + "s = {" + str(", ".join([st.name for st in self.start_states])) + "}\n" \
             + "F = {" + str(", ".join([st.name for st in self.final_states])) + "}\n"



# custom exception raised when error occurs during FA parse
class ParseError(Exception):
    pass
# custom exception raised when error occurs during argument parse
class ArgumentError(Exception):
    pass
# custom exception raised when alphabets of two automatons are incompatible
class AlphabetsIncompatibleError(Exception):
    pass

# ---------------------------------------------------------------------------------------------------------------
#                                               AUTOMATON PARSE
# ---------------------------------------------------------------------------------------------------------------

def ParseFA():
    '''
        Parses automaton from stdin and saves them into corresponding structures. Expects correct format.
        Input: No input.
        Returns: List of automatons.
    '''

    state = 0           # state of parsing
    Automatons = []     # list of automatons
    alphabet = []       # list of letters of FA alphabet
    counter = 0         # used in transition parse
    start_state = False # used in transition parse

    for line in sys.stdin:
        line = line.rstrip()        # remove endline symbol from the back of the string
        if line == "":              # remove endline symbol from the back of the string
            continue
        line = line.split()         # split to words

        if not __debug__:           # __debug__ set to True when run without -O (inverts that)
            print(line)

        for word in line:           # main parsing - command center
            if not __debug__:           # __debug__ set to True when run without -O (inverts that)
                print(word)
            # state changes
            if word == "Ops" and state == 6:    # init alphabet and start again
                state = 1
                alphabet = []
                continue
            elif word == "Ops" and state == 0:   # alphabet
                state = 1
                continue
            elif word == "Automaton" and (state == 1 or state == 6):
                state = 2                       # automaton name
                continue
            elif word == "States" and state == 2:
                state = 3                       # states
                continue
            elif word == "Final" and state == 3:
                state = 4
                continue
            elif word == "States" and state == 4:
                state = 5                       # final states
                continue
            elif word == "Transitions" and state == 5:
                state = 6                       # transitions
                continue

            # main parsing - build automaton
            if state == 1:      # reads alphabet
                if word[word.find(":")+1] != '1':              # automaton accepts only unary symbols (a:1)
                    continue
                alphabet.append(word[0:word.find(":")]);       # alphabet symbol is the first one
            elif state == 2:    # reads name of the automaton and assigns the alphabet
                automaton = FA()
                automaton.name = word
                alphabet.sort()
                automaton.alphabet = alphabet
                Automatons.append(automaton)
            elif state == 3:    # reads a list of states
                Automatons[-1].states.append(State(name=word))
            elif state == 5:    # reads a list of final states
                # finds state in the vector of states and pushes pointer to the state
                for st in Automatons[-1].states:
                    if st.name == word:
                        st.final_st = True
                        Automatons[-1].final_states.add(st)
                        break
            elif state == 6:    # parses transitions
                if counter == 0:                                # left side of a(p)->q
                    if(word.find("(") == -1):                           # start state
                        start_state = True
                    else:                                               # normal transition
                        bracket_start = word.find("(")
                        bracket_end = word.find(")")
                        transit_letter = word[0:bracket_start]          # word = "a(p)"
                        source_state = word[bracket_start+1:bracket_end]

                        if not __debug__:
                            print("TRANSIT: ", transit_letter, " SOURCE STATE: ", source_state)
                    counter += 1
                elif counter == 1:                              # arrow in a(p)->q
                    counter += 1
                    continue
                else:                                           # right side of a(p)->q
                    target_state = word
                    if not __debug__:
                        print("TARGET: ", target_state)

                    if not start_state:     # is not a start state
                        for state_source in Automatons[-1].states:     # fill the optimalised transition tree
                            if state_source.name == source_state:
                                for state_target in Automatons[-1].states:
                                    if state_target.name == target_state:
                                        state_source.add_transit_state(transit_letter, state_target)
                                        state_target.add_reversed_transit_state(transit_letter, state_source)
                    else:                   # is a start state
                        for st in Automatons[-1].states:                   # fill the start_states vector
                            if st.name == target_state:
                                st.start_st = True
                                Automatons[-1].start_states.add(st)
                        start_state = False

                    counter = 0;    # reset the counter for another relation

    if state != 6:
        raise ParseError        # parsing must end with transitions

    return Automatons


# ---------------------------------------------------------------------------------------------------------------
#                                               AUTOMATON ALGORITHMS
# ---------------------------------------------------------------------------------------------------------------

# --------------------------------------------- EMPTINESS ALGORITHM ---------------------------------------------

def Emptiness_test(automaton):
    '''
        Function checks if automaton is empty. It is basically a Depth-first search (DFS) in a tree of states.
        Input: automaton - FA class
        Returns:
            true  -> automaton is empty
            false -> automaton si not empty (final state reached)
    '''
    W = []      # stack
    visited_htab = {}

    for state in automaton.start_states:                # push all start states to stack
        visited_htab[state.name] = None
        W.append(state)

    while W:
        state = W.pop()         # pop state from stack
        if not __debug__:
            print(state.name + ", list: ", W)

        if state.final_st:
            return False        # final state reached -> automaton is not empty
        for st in state.get_transit_states_values():    # go through all transitions
            for s in st:                                # go through the set of states reachable by a certain letter
                if not s.name in visited_htab:          # do not visit states twice
                    visited_htab[s.name] = None         # set the visited flag
                    W.append(s)                         # push state to stack

    return True     # final state not found -> automaton is empty

# --------------------------------------- USELESS STATES REMOVAL ALGORITHM --------------------------------------

def Remove_relations(state):
    '''
        Function removes relations with states that should be removed.
        Input: state - state whose relations should be removed
        Returns: void
    '''
    for letter, st in state.get_transit_states_items():             # update reversed_transit_states of all next states
        for s in st:
            s.remove_reversed_transit_state(letter, state)

    for letter, st in state.get_reversed_transit_states_items():    # update transit_states of all previous states
        for s in st:
            s.remove_transit_state(letter, state)

def Restore_FA(automaton, alg, visited_htab, flag_htab):
    '''
        Function takes automaton with states that need to be removed and removes those states.
        Input:
            automaton - FA class
            alg - id of algorithm calling this function (0 - useless, 1 - reduction)
            visited_htab - hash table of state names (from start states)
            flag_htab - hash table of state names (from final states)
        Returns: void
    '''
    st_ind = 0
    end_ind = len(automaton.states) - 1

    while st_ind < end_ind:         # first index must be smaller than second - it swaps states with 0 flag to the end
        st_state = automaton.states[st_ind]
        if (alg == 0 and not (st_state.name in flag_htab and st_state.name in visited_htab)) or (alg == 1 and st_state.flag == 0):     # element will be swapped and removed
            Remove_relations(st_state)  # remove all relations with other states
            while (automaton.states[end_ind].name not in flag_htab or automaton.states[end_ind].name not in visited_htab) and st_ind != end_ind:   # find the first valid state from the end
                Remove_relations(automaton.states[end_ind])     # remove relations of all encountered states that should be removed
                end_ind -= 1
            if st_ind < end_ind:    # if a valid state was found
                temp = automaton.states[st_ind]
                automaton.states[st_ind] = automaton.states[end_ind]    # "swap" elements
                automaton.states[end_ind] = temp
                end_ind -= 1
        st_ind += 1

    # remove states that should be removed (they should all be in the back of the list)
    while len(automaton.states) > 0 and (automaton.states[-1].name not in flag_htab or automaton.states[-1].name not in visited_htab):
        if automaton.states[-1].start_st:
            temp = list(automaton.start_states)
            idx = temp.index(automaton.states[-1])
            temp[idx] = temp[-1]
            temp.pop()
            automaton.start_states = set(temp)

        if automaton.states[-1].final_st:
            temp = list(automaton.final_states)
            idx = temp.index(automaton.states[-1])
            temp[idx] = temp[-1]
            temp.pop()
            automaton.final_states = set(temp)

        automaton.states.pop()


def Remove_useless_states(automaton):
    '''
        Function implements the Remove useless states algorithm. Removes all non-ending and non-reachable states.
        Has three parts - breadth-first search from start states (saves into visited_htab), breadth-first search
        from final states andreversed automaton (saves into flag_htab), remove states that are not in both tables.
        Input: automaton - FA class
        Returns: void
    '''
    W = Queue()
    visited_htab = {}
    flag_htab = {}

    # ----------------------------------------- Removing non-reachable states -------------------------------------
    for state in automaton.start_states:        # push all start states to queue
        visited_htab[state.name] = None
        W.put(state)

    while not W.empty():
        state = W.get()         # pop state from queue

        for st in state.get_transit_states_values():    # go through all transitions
            for s in st:                                # go through the set of states reachable by a certain letter
                if not s.name in visited_htab:          # do not visit states twice
                    visited_htab[s.name] = None
                    W.put(s)                            # push state to queue

    # ----------------------------------------- Removing non-ending states -------------------------------------
    for state in automaton.final_states:        # push all final states to queue
        flag_htab[state.name] = None
        W.put(state)

    while not W.empty():
        state = W.get()         # pop state from queue

        for st in state.get_reversed_transit_states_values():   # go through all reversed transitions
            for s in st:                            # go through the set of states reachable by a certain letter
                if not s.name in flag_htab:                      # do not visit states twice
                    flag_htab[s.name] = None
                    W.put(s)                        # push state to queue

    # ------------------------------ Setting flag and modifying automaton -----------------------------------
    Restore_FA(automaton, 0, visited_htab, flag_htab)       # modify automaton

# --------------------------------------- INTERSECTION ------------------------------------------------------

def Intersection_FA(automaton1, automaton2):
    '''
        Function implements the Intersection algorithm. Computes intersection of two automatons by making pairs of states.
        Input:
            automaton1 - first automaton, used to compute intersection
            automaton2 - second automaton, used to compute intersection
            result_automaton - result automaton, used to store result automaton
        Returns: result automaton FA
    '''
    if not __debug__:
        print(automaton1)
        print(automaton2)

    W = Queue()     # queue of lists [state1, state2, merged_state]
    opt_Q = {}      # optimalize searching Q

    result_automaton = FA(name=automaton1.name+"&"+automaton2.name)     # create a new automaton that will be returned

    # checking if alphabets are the same - they are sorted
    #if automaton1.alphabet != automaton2.alphabet:
    #    raise AlphabetsIncompatibleError
    if len(automaton1.alphabet) < len(automaton2.alphabet):
        result_automaton.alphabet = copy.copy(automaton1.alphabet)
    else:
        result_automaton.alphabet = copy.copy(automaton2.alphabet)

    # carthesian product of start states of automaton1 and automaton2
    for state1 in automaton1.start_states:
        for state2 in automaton2.start_states:
            st = State(name=state1.name+state2.name, start_st=True)     # create a new state by merging two states from automaton1 and automaton2
            result_automaton.states.append(st)                          # push to states
            opt_Q[st.name] = st
            result_automaton.start_states.add(st)                       # push to start_states

            if state1.final_st and state2.final_st:                     # if both states are final, merged state is final too
                result_automaton.final_states.add(st)                   # push to final_states
                st.final_st = True
            W.put([state1,state2,st])                                  # push the list to queue

    if not __debug__:
        print(result_automaton)

    while not W.empty():
        s_list = W.get()
        if not __debug__:
            print("Intersection: state list [",str(s_list[0]),", ",str(s_list[1]),", ",str(s_list[2]),"]")

        for a in result_automaton.alphabet:                           # for every letter of the alphabet
            for state1 in s_list[0].get_transit_states(a):                  # find all states reachable from state1 by that letter
                for state2 in s_list[1].get_transit_states(a):              # find all states reachable from state2 by that letter
                    new_state = State(name=state1.name+state2.name)     # create new state
                    if new_state.name not in opt_Q:                         # insert new state into result_automaton only if it is not yet there
                        result_automaton.states.append(new_state)
                        opt_Q[new_state.name] = new_state
                        if state1.final_st and state2.final_st:         # if both states are final, new_state is also final
                            new_state.final_st = True
                            result_automaton.final_states.add(new_state)
                        W.put([state1,state2,new_state])                # push state list into queue
                        # always push relations
                        s_list[2].add_transit_state(a, new_state)
                        new_state.add_reversed_transit_state(a, s_list[2])
                    else:
                        # always push relations
                        s_list[2].add_transit_state(a, opt_Q[new_state.name])
                        opt_Q[new_state.name].add_reversed_transit_state(a, s_list[2])

    return result_automaton

# --------------------------------------- DETERMINIZATION ------------------------------------------------------

def Determinization_FA(automaton1):
    '''
        Function implements the Determinization algorithm. Computes deterministic version of input automaton.
        Input:
            automaton1 - source automaton, used to compute determinization
        Returns: result automaton FA
    '''

    if not __debug__:
        print(automaton1.debug_print())

    W = Queue()     # queue of [[vector_of_states_to_be_merged], merged_state]
    opt_Q = {}      # optimalize searching Q
    fail = None     # fail state

    result_automaton = FA(name="det"+automaton1.name,alphabet=automaton1.alphabet)  # building a new automaton that will be returned
    st = State(name="|", start_st = True)                                           # create a new start state by merging all start states
    # optimalization - find all state names and push them into a list
    opt_name = []                           # optimizes dealing with S1S2S3, S2S1S3, S3S2S1, ... states - it is the same state
    for state in automaton1.start_states:
        opt_name.append(state.name)         # push all state names into list
        if state.final_st == True:          # if atleast one start state is also final, the result state is final too
            st.final_st = True
    opt_name.sort()                         # sort the list of state names
    for name in opt_name:
        st.name = st.name + name + "|"      # create name for the new state

    result_automaton.states.append(st)          # push the new state to result_automaton
    opt_Q[st.name] = st                         # push the new state to optimalization list
    result_automaton.start_states.add(st)       # add start state
    if st.final_st:
        result_automaton.final_states.add(st)   # add final state
    W.put([list(automaton1.start_states), st])  # push structure to queue

    if not __debug__:
        print(result_automaton)

    # main loop - until queue is empty
    while not W.empty():
        st_list = W.get()
        if not __debug__:
            print("Determinization: state list [",[s.name for s in st_list[0]],", ",st_list[1].name,"]")

        for a in automaton1.alphabet:                   # for every letter of the alphabet
            st = State(name="|")                        # create a new state
            opt_storage = {}                            # optimizes searching in storage - prevents states like S1S1S1S2S3 or S1S1S2S3S3
            storage = []                                # stores states reachable by a letter that will be merged
            for state in st_list[0]:                    # for every source state
                for s in state.get_transit_states(a):   # get transit states by letter a
                    if s.name not in opt_storage:       # if state is not elrady in storage, put it in there
                        opt_storage[s.name] = s
                        if s.final_st:
                            st.final_st = True          # if the state is final, merged state is also final
                        storage.append(s)
            for name in sorted(list(opt_storage.keys())):      # sort state names and create a new name
                st.name = st.name + name + "|"

            if determinization_fail_switch:
                if not storage:                                         # if storage is empty - add or connect a fail state
                    if fail == None:                                    # if fail state does not exist yet
                        fail = State(name="fail")                       # create it
                        result_automaton.states.append(fail)            # push it to automaton
                        for alph in automaton1.alphabet:                # add relations from fail to fail for every letter
                            fail.add_transit_state(alph, fail)
                            fail.add_reversed_transit_state(alph, fail)
                    st_list[1].add_transit_state(a, fail)               # add transitions between source state and fail state
                    fail.add_reversed_transit_state(a, st_list[1])
                    continue
            else:
                if not storage:                         # if no state can be reached by letter a (storage empty) -> continue to the next letter
                    continue

            if st.name not in opt_Q:                            # if state is not yet in Q
                result_automaton.states.append(st)                     # add it
                opt_Q[st.name] = st
                if st.final_st:
                    result_automaton.final_states.add(st)       # push the state to final states
                W.put([storage, st])                            # push structure to queue
                st_list[1].add_transit_state(a, st)             # add relations between source state and the new state
                st.add_reversed_transit_state(a, st_list[1])
            else:
                st_list[1].add_transit_state(a, opt_Q[st.name]) # always add relations between source state and the new state
                opt_Q[st.name].add_reversed_transit_state(a, st_list[1])

    return result_automaton     # return result automaton

# --------------------------------------- MINIMALIZATION ------------------------------------------------------

def Hopcroft(automaton1):
    '''
        Function implements the Hopcroft algorithm. Computes the language partition, which is a list of blocks of states.
        Input:
            automaton1 - source automaton, used to compute language partition
        Returns: result language partition
    '''

    partition_lan = []          # vector of vectors of states [[a,b,c,...],[x,y,z,...],...]
    W = []                      # list of splitters [(a,B), ...]

    # first condition of the algorithm - initializing partition
    if len(automaton1.final_states) == 0 or len(automaton1.final_states) == len(automaton1.states):
        return [copy.copy(list(automaton1.states))]     # Q
    else:
        partition_lan = [copy.copy(list(automaton1.final_states)), copy.copy(list(set(automaton1.states) - set(automaton1.final_states)))]  # [F,Q/F]

    #if not __debug__:
    #    print("Printing partition_lan: ", partition_lan)

    if len(partition_lan[0]) < len(partition_lan[1]):       # push [a,min(Q,Q/F)] into W
        for a in automaton1.alphabet:
            W.append([a,partition_lan[0]])
    else:
        for a in automaton1.alphabet:
            W.append([a,partition_lan[1]])

    # main loop - while there are splitters
    while W:
        splitter = W.pop()
        if not __debug__:
            print("Printing partition_lan: ", partition_lan)
            print("Printing splitters (W): ", splitter, " - ", W)

        new_partition_lan = []              # do all alterations of partition_lan here and then assign it to patition_lan (avoid slow removing)
        for bl in partition_lan:            # go through all blocks in partition
            splits_in = False
            splits_out = False
            block1 = []
            block2 = []

            for st in bl:                   # for every state of the block check where do its transitions lead
                try:
                    transit = st.get_transit_states(splitter[0])[0]
                except IndexError:            # if there is no transition, it splits out
                    splits_out = True
                    block2.append(st)
                else:                       # if there is a transition, check if it splits in or out
                    if not __debug__:
                        print(transit.name)
                    if transit.name in [st.name for st in splitter[1]]:
                        splits_in = True
                        block1.append(st)
                    else:
                        splits_out = True
                        block2.append(st)

            if not __debug__:
                print("Active block: ", bl)
                print("Two blocks print: ", block1, block2)

            if splits_in and splits_out:                        # if a block is being split by current splitter - insert two subblocks into new partition
                new_partition_lan.append(block1)
                new_partition_lan.append(block2)

                # final modifications to W (list of splitters) - for every letter of the alphabet
                for a in automaton1.alphabet:
                    for ind, split in enumerate(W):             # go through the list of splitters
                        # if a splitters block is being deleted, erase it and insert splitters for two subblocks
                        if Counter(bl) == Counter(split[1]) and split[0] == a:
                            W[ind] = W[-1]                      # efficient erasing...
                            W[-1] = [a,block1]                  # insert first subblock
                            W.append([a,block2])                # insert second subblock
                            break
                        if ind == len(W)-1:                     # if a splitter for deleted block was not found
                            if len(block1) < len(block2):       # insert [a,min(block1,block2)]
                                W.append([a,block1])
                            else:
                                W.append([a,block2])
                            break
            else:
                new_partition_lan.append(bl)                    # if a block is not being split by current splitter - insert it to new partition
        partition_lan = new_partition_lan
    return partition_lan


def Minimalization_FA(automaton1):
    '''
        Function implements the Minimalization algorithm. Computes minimal automaton from source automaton.
        Input:
            automaton1 - source automaton, used to compute its minimal version
        Returns: result automaton FA
    '''

    partition_lan = Hopcroft(automaton1)
    if not __debug__:
        print("Minimalization - language partition print: ", partition_lan)

    relations = defaultdict(list)       # name_of_requested_state:[letter,partition_source_state]
    result_automaton = FA(name="min-"+automaton1.name,alphabet=automaton1.alphabet)     # building a new minimal automaton
    # goes through all partitions, creates corresponding state in result_automaton and inserts requests for relations
    for block in partition_lan:
        st = State(name="")
        result_automaton.states.append(st)

        it = block[0]       # for speed
        # for every letter check where the first state points and save (name_of_the_state,{letter,partition_state}) into relations
        for a in automaton1.alphabet:
            try:
                relations[it.get_transit_states(a)[0].name].append([a,st])  # if there is relation for letter a, save the target_state:[letter,requesting state] into relations
            except IndexError:     # if there is no relation for letter a, save nothing
                pass

        for state in block:                         # build the partition state
            st.name = st.name + state.name          # set name and final/start flags
            if state.final_st:
                st.final_st = True
            if state.start_st:
                st.start_st = True
        if st.final_st:
            result_automaton.final_states.add(st)
        if st.start_st:
            result_automaton.start_states.add(st)

    # goes through all states again and connects name_of_the_state with letter and partition_state
    # partitions correspond to states in result_automaton
    for block, part_st in zip(partition_lan, result_automaton.states):
        for state in block:                                                     # for every state in the block checks if some other state requests relation with it
            if state.name in relations:
                for request in relations[state.name]:                           # for every state that requests relation - add it
                    request[1].add_transit_state(request[0],part_st)
                    part_st.add_reversed_transit_state(request[0],request[1])

    return result_automaton

# --------------------------------------- REDUCTION ILIE ------------------------------------------------------

def Preorder(automaton1):
    '''
        Function implements the Simulation relation algorithm. Computes simulation relation of an automaton.
        Input:
            automaton1 - source automaton, used to compute its minimal version
        Returns: The simulation relation (dictionary {(state_name,state_name):None}).
    '''

    # basically: int N[alphabet][state][state] = {0}
    N = [[[0]*len(automaton1.states) for x in range(len(automaton1.states))] for y in range(len(automaton1.alphabet))]
    W = Queue()     # queue of lists [state1,state2]
    preord = {}     # dict of tuples (state_name,state_name)

    # initializing preord and W
    for ind, st in enumerate(automaton1.states):
        for a in automaton1.alphabet:                       # preprocessing
            # reversed relations are already computed inside reversed_transit_states_p (multimap)
            st.card[a] = len(st.get_transit_states(a))      # compute cardinality(rel(state,a))
        st.flag = ind       # set state index into N

        # W initialization
        for st2 in automaton1.states:
            if st.final_st:                             # add all pairs Fx(Q-F)
                if not st2.final_st:                    # st=F, st2=(Q-F)
                    preord[(st.name,st2.name)] = None
                    W.put([st,st2])
                    continue

            # {(q,r)| Ea in alphabet: d(q,a)!=0 and d(r,a)==0}
            for a in automaton1.alphabet:
                if len(st.get_transit_states(a)) > 0 and len(st2.get_transit_states(a)) == 0 and (st.name,st2.name) not in preord:
                    preord[(st.name,st2.name)] = None
                    W.put([st,st2])

    if not __debug__:
        print("Preorder - printing preord after init: ", list(preord.keys()))

    # main loop
    while not W.empty():
        st_pair = list(W.get())
        if not __debug__:
            print("Preorder - printing pair: ", st_pair)

        for ind, a in enumerate(automaton1.alphabet):
            for k in st_pair[1].get_reversed_transit_states(a):     # get rd(j,a)
                N[ind][st_pair[0].flag][k.flag] = N[ind][st_pair[0].flag][k.flag] + 1   # N(a)ik <- N(a)ik + 1
                if N[ind][st_pair[0].flag][k.flag] == k.card[a]:
                    for l in st_pair[0].get_reversed_transit_states(a):
                        if (l.name,k.name) not in preord:
                            preord[(l.name,k.name)] = None
                            W.put([l,k])
                            if not __debug__:
                                print("Preorder - pushing pair into preorder: ", (l.name,k.name))

    return {(st1.name,st2.name):None for st1 in automaton1.states for st2 in automaton1.states if (st1.name,st2.name) not in preord}

def Reduction_NFA(automaton1):
    ''' Ilie NFA reduction '''
    # optim:
    #       neprochazet vsechny stavy, ale jen preorder, uprava prvni faze spojovani stavu p a q
    #       neni treba odstranovat (p,q) a (q,p) zvlast, proste odstranit vsechny dvojice, ve kterych je stav p     c++
    #       spojit to do jednoho cyklu?
    #       presun nastavovani flagu na -1 do mista find_in_states(i->first)        c++
    #       osetreni startovnicha finalnich stavu!!     c++

    preorder_r = Preorder(automaton1)
    automaton1.reverse_automaton()          # construct a reverse automaton
    preorder_l = Preorder(automaton1)
    automaton1.reverse_automaton()

    if not __debug__:
        print("Reduction - preorder_r: ", list(preorder_r.keys()))
        print("Reduction - preorder_l: ", list(preorder_l.keys()))

    # 1) p-q, q-p v preorder_r
    # 2) p-q, q-p v preorder_l
    # 3) p-q, p-q v rozdilnych preorderech
    for i, val in preorder_r.items():
        if val != None:         # pair is marked for removal
            continue
        i = list(i)
        if i[0] == i[1]:        # (p,p)
            continue
        if (i[1],i[0]) in preorder_r:       # found (p,q) (q,p) duo
            # merging states p and q - transfering relations from p to q
            st = next(s for s in automaton1.states if s.name == i[0])       # find the state p
            st2 = next(s for s in automaton1.states if s.name == i[1])      # find the state q
            print(st.name, st2.name)
            st.flag = 0
            st2.final_st = st2.final_st or st.final_st
            st2.start_st = st2.start_st or st.start_st
            if st.start_st:
                automaton1.start_states.discard(st)
                automaton1.start_states.add(st2)
            if st.final_st:
                automaton1.final_states.discard(st)
                automaton1.final_states.add(st2)
            for j_lists in st.get_reversed_transit_states_values():               # for all previous relations of p
                for j in j_lists:
                    for k_first, k_second_lists in j.get_transit_states_items():  # find their forward relations pointing back to p
                        for ind, k_second in enumerate(k_second_lists):
                            if k_second.name == i[0]:
                                if [r for r in j.get_transit_states(k_first) if r.name == i[1]] == []:    # if relations point only to p and not q (with same letter)
                                    j.get_transit_states(k_first)[ind] = st2   # redirect the relation to q
                                else:                                               # if relations also point to q with same letter, just erase the redundant relation
                                    temp = j.get_transit_states(k_first)
                                    temp[ind] = temp[-1]
                                    temp.pop()

            for j_first, j_second_lists in st.get_transit_states_items():         # find all forward relations between p and j
                for j_second in j_second_lists:
                    if [r for r in st2.get_transit_states(j_first) if r.name == j_second.name] == []:     # if there is no same transition between q and j
                        st2.get_transit_states(j_first).append(j_second)                                   # add the relation to q
                    for ind, r in enumerate(j_second.get_reversed_transit_states(j_first)):                    # find all backward transition
                        if r.name == st.name:
                            j_second.get_reversed_transit_states(j_first)[ind] = st2                           # redirect them to q
            st.clear_transit_states()
            st.clear_reversed_transit_states()

            # removing pairs from both preorders according to Ilie algorithm
            for state in automaton1.states:
                if (i[1],state.name) in preorder_r and (i[0],state.name) not in preorder_r:
                    preorder_r.pop((i[1],state.name), None)
                if (i[1],state.name) in preorder_l and (i[0],state.name) not in preorder_l:
                    preorder_l.pop((i[1],state.name), None)
            # erasing all pairs that contain deleted state p from both preorders

            for pair_first, pair_second in preorder_r:
                if pair_first == i[0] or pair_second == i[0]:
                    preorder_r[(pair_first,pair_second)] = -1

            for pair_first, pair_second in preorder_l:
                if pair_first == i[0] or pair_second == i[0]:
                    preorder_l[(pair_first,pair_second)] = -1
    # ---------------------------------------------------------------------------------------------------------------------------
    for i, val in preorder_l.items():
        if val != None:         # pair is marked for removal
            continue
        i = list(i)
        if i[0] == i[1]:        # (p,p)
            continue
        if (i[1],i[0]) in preorder_l:       # found (p,q) (q,p) duo
            # merging states p and q - transfering relations from p to q
            st = next(s for s in automaton1.states if s.name == i[0])       # find the state p
            st2 = next(s for s in automaton1.states if s.name == i[1])      # find the state q
            print(st.name, st2.name)
            st.flag = 0
            st2.final_st = st2.final_st or st.final_st
            st2.start_st = st2.start_st or st.start_st
            if st.start_st:
                automaton1.start_states.discard(st)
                automaton1.start_states.add(st2)
            if st.final_st:
                automaton1.final_states.discard(st)
                automaton1.final_states.add(st2)
            for j_lists in st.get_reversed_transit_states_values():               # for all previous relations of p
                for j in j_lists:
                    for k_first, k_second_lists in j.get_transit_states_items():  # find their forward relations pointing back to p
                        for ind, k_second in enumerate(k_second_lists):
                            if k_second.name == i[0]:
                                if [r for r in j.get_transit_states(k_first) if r.name == i[1]] == []:    # if relations point only to p and not q (with same letter)
                                    j.get_transit_states(k_first)[ind] = st2   # redirect the relation to q
                                else:                                               # if relations also point to q with same letter, just erase the redundant relation
                                    temp = j.get_transit_states(k_first)
                                    temp[ind] = temp[-1]
                                    temp.pop()

            for j_first, j_second_lists in st.get_transit_states_items():         # find all forward relations between p and j
                for j_second in j_second_lists:
                    if [r for r in st2.get_transit_states(j_first) if r.name == j_second.name] == []:     # if there is no same transition between q and j
                        st2.get_transit_states(j_first).append(j_second)                                   # add the relation to q
                    for ind, r in enumerate(j_second.get_reversed_transit_states(j_first)):                    # find all backward transition
                        if r.name == st.name:
                            j_second.get_reversed_transit_states(j_first)[ind] = st2                           # redirect them to q
            st.clear_transit_states()
            st.clear_reversed_transit_states()

            # removing pairs from both preorders according to Ilie algorithm
            for state in automaton1.states:
                if (i[1],state.name) in preorder_l and (i[0],state.name) not in preorder_l:
                    preorder_l.pop((i[1],state.name), None)
                if (i[1],state.name) in preorder_r and (i[0],state.name) not in preorder_r:
                    preorder_r.pop((i[1],state.name), None)
            # erasing all pairs that contain deleted state p from both preorders

            for pair_first, pair_second in preorder_l:
                if pair_first == i[0] or pair_second == i[0]:
                    preorder_l[(pair_first,pair_second)] = -1

            for pair_first, pair_second in preorder_r:
                if pair_first == i[0] or pair_second == i[0]:
                    preorder_r[(pair_first,pair_second)] = -1
    # ---------------------------------------------------------------------------------------------------------------------------
    print("---------: ", preorder_r)
    print("---------: ", preorder_l)
    print(automaton1.debug_print())
    for i, val in preorder_r.items():
        if val != None:         # pair is marked for removal
            continue
        i = list(i)
        if i[0] == i[1]:        # (p,p)
            continue
        if (i[0],i[1]) in preorder_l:       # found (p,q) (p,q) duo
            # merging states p and q - transfering relations from p to q
            st = next(s for s in automaton1.states if s.name == i[0])       # find the state p
            st2 = next(s for s in automaton1.states if s.name == i[1])      # find the state q
            print(st.name, st2.name)
            st.flag = 0
            st2.final_st = st2.final_st or st.final_st
            st2.start_st = st2.start_st or st.start_st
            if st.start_st:
                automaton1.start_states.discard(st)
                automaton1.start_states.add(st2)
            if st.final_st:
                automaton1.final_states.discard(st)
                automaton1.final_states.add(st2)
            for j_lists in st.get_reversed_transit_states_values():               # for all previous relations of p
                for j in j_lists:
                    for k_first, k_second_lists in j.get_transit_states_items():  # find their forward relations pointing back to p
                        for ind, k_second in enumerate(k_second_lists):
                            if k_second.name == i[0]:
                                if [r for r in j.get_transit_states(k_first) if r.name == i[1]] == []:    # if relations point only to p and not q (with same letter)
                                    j.get_transit_states(k_first)[ind] = st2   # redirect the relation to q
                                else:                                               # if relations also point to q with same letter, just erase the redundant relation
                                    temp = j.get_transit_states(k_first)
                                    temp[ind] = temp[-1]
                                    temp.pop()

            for j_first, j_second_lists in st.get_transit_states_items():         # find all forward relations between p and j
                for j_second in j_second_lists:
                    if [r for r in st2.get_transit_states(j_first) if r.name == j_second.name] == []:     # if there is no same transition between q and j
                        st2.get_transit_states(j_first).append(j_second)                                   # add the relation to q
                    for ind, r in enumerate(j_second.get_reversed_transit_states(j_first)):                    # find all backward transition
                        if r.name == st.name:
                            j_second.get_reversed_transit_states(j_first)[ind] = st2                           # redirect them to q
            st.clear_transit_states()
            st.clear_reversed_transit_states()

            # erasing all pairs that contain deleted state p from both preorders
            for pair_first, pair_second in preorder_r:
                if pair_first == i[0] or pair_second == i[0]:
                    preorder_r[(pair_first,pair_second)] = -1

            for pair_first, pair_second in preorder_l:
                if pair_first == i[0] or pair_second == i[0]:
                    preorder_l[(pair_first,pair_second)] = -1

    #erase = [(pair_first,pair_second) for pair_first, pair_second in preorder_r.keys() if pair_first == i[0] or pair_second == i[0]]
    #for e in erase: preorder_r.pop(e)
    #Restore_FA(automaton1, 1)
    return automaton1

# --------------------------------------- UNIVERSALITY AND INCLUSION --------------------------------------------------------

# class that represents macro state
class Macro_state:
    __slots__ = ["states","rejecting"]
    def __init__(self,states=None,rejecting=None):
        if states == None:                      # list of states in a macro state
            self.states = []
        else:
            self.states = copy.copy(states)
        self.rejecting = rejecting              # bool value - rejecting/accepting macro state

    def __repr__(self):
        return str(self.states) + str(self.rejecting)


# class that represents product state
class Product_state:
    __slots__ = ["a1_st","macro_st","rejecting"]
    def __init__(self,a1_st=None,macro_st=None,rejecting=None):
        self.a1_st = State()                    # state from first automaton
        self.macro_st = Macro_state()           # macro state of second automaton
        self.rejecting = rejecting              # bool value - rejecting/accepting product state

    def __repr__(self):
        return str(self.a1_st) + str(self.macro_st.states) + str(self.rejecting)



def Minimize(macro_R, preorder):
    '''
        Function iterates (i,j are iterators) through macro state and if there is (i,j) pair in preorder, it deletes i from macro state. Implements second optimization.
        Input:
            macro_R - source macro state
            preorder - simulation relation
        Returns: minimized macro state
    '''
    del_macro_R_states = {}                     # deleted states from macro_R_states
    for st1 in macro_R.states:                  # go through macro_R states
        for st2 in [state for state in macro_R.states if state not in del_macro_R_states]:  # go through macro_R states again
            if st1 == st2: continue;            # identity cannot remove state
            if (st1.name,st2.name) in preorder: # if there is a pair (st1,st2) in preorder
                del_macro_R_states[st1] = None  # remove i (because i is simulated by j)
                break
    macro_R.states = [state for state in macro_R.states if state not in del_macro_R_states]
    return macro_R

def Is_subset(macroSubs, macroSuper, preorder):
    '''
        Function checks if first macro state (macroSubs) is subset of second macro state (macroSuper).
        For every state sub_st in first macro state there must be state super_st in second macro state such that (sub_st, super_st) are in preorder.
        Input:
            macroSubs - first macro state
            macroSuper - second macro state
            preorder - simulation relation
        Returns: True if macroSubs is subset of macroSuper, false otherwise.
    '''
    for sub_st in macroSubs.states:                     # for every state of subset
        found = False
        for super_st in macroSuper.states:              # there must be a state in superset
            if (sub_st.name,super_st.name) in preorder: # such that sub_st <= super_st in preorder
                found = True
                break
        if not found:
            return False
    return True

def Universality_NFA(automaton1, preorder):
    '''
        Function implements the Universality algorithm.
        Input:
            automaton1 - source automaton
            preorder - simulation relation
        Returns: True if automaton is universal, false if automaton is not universal
    '''
    processed = []      # processed and next vectors
    next = []
    # if a macro state of start states is rejecting -> automaton does not recognise empty string (epsilon) as a part of the language
    # -> language is not universal
    macro_R = Macro_state(states=list(automaton1.start_states),rejecting=True)
    for state in macro_R.states:
        if state.final_st:
            macro_R.rejecting = False
            break
    if macro_R.rejecting:
        return False
    macro_R = Minimize(macro_R, preorder)       # next = {Minimize(I)};
    next.append(macro_R)

    while next:         # main loop
        macro_R = next.pop()
        processed.append(macro_R)

        if not __debug__:
            print("Universality - current macro state: ", macro_R)

        # get adjacent macro states
        for a in automaton1.alphabet:
            # getting Post(R) for specific letter *a
            redundant = {}
            macro_P = Macro_state(states=[],rejecting=True)
            for state in macro_R.states:
                for next_st in state.get_transit_states(a):
                    if next_st.name not in redundant:
                        redundant[next_st.name] = None
                        macro_P.states.append(next_st)
                        if next_st.final_st:
                            macro_P.rejecting = False

            if not __debug__:
                print("Universality - new macro state before minim: ", macro_P)
            macro_P = Minimize(macro_P, preorder)
            if not __debug__:
                print("Universality - new macro state after minim: ", macro_P)

            if macro_P.rejecting:
                return False

            # search in processed for S such that S <= P
            exists_S = False
            new_processed = []
            for macro_S in processed:
                if Is_subset(macro_S, macro_P, preorder):
                    exists_S = True
                    break

                # remove all S from processed such that P <= S
                if not Is_subset(macro_P, macro_S, preorder):           # if is subset -> delete from processed -> do not insert into new_processed
                    new_processed.append(macro_S)

            if not exists_S:                # if not found yet
                processed = new_processed   # update processed - only changes, if S was not found
                new_next = []
                for macro_S in next:
                    if Is_subset(macro_S, macro_P, preorder):
                        exists_S = True
                        break

                    # remove all S from next such that P <= S
                    if not Is_subset(macro_P, macro_S, preorder):       # if is subset -> delete from next -> do not insert into new_next
                        new_next.append(macro_S)
                if not exists_S:
                    next = new_next         # update next - only changes, if S was not found

            # if no such S was found
            if not exists_S:
                next.append(macro_P)        # add P to next
                if not __debug__:
                    print("Universality - pushing (into next) macro state: ", macro_P)

    return True

def Inclusion_NFA(automaton1, automaton2, preorder):
    '''
        Function implements the Inclusion algorithm. Checks if L(automaton1) is subset of L(automaton2).
        Input:
            automaton1 - first automaton
            automaton2 - second automaton
            preorder - simulation relation of (automaton1 union automaton2)
        Returns: True if L(automaton1) is subset of L(automaton2), false otherwise.
    '''
    processed = []      # processed and next vectors
    next = []

    # checking if alphabets are the same - they are sorted
    alphabet = set()
    if len(automaton1.alphabet) < len(automaton2.alphabet):
        alphabet = copy.copy(automaton1.alphabet)
    else:
        alphabet = copy.copy(automaton2.alphabet)

    # if a product state of p and start states is accepting -> automaton1 overlaps with complement of automaton2
    # -> L(automaton1) (not)<= L(automaton2)
    prod_st1 = Product_state()
    prod_st1.macro_st.states = copy.copy(automaton2.start_states)
    prod_st1.macro_st.rejecting = True
    for state in prod_st1.macro_st.states:
        if state.final_st:
            prod_st1.macro_st.rejecting = False         # compute if macro state is rejecting
            break

    prod_st1.rejecting = True                                   # if program does not end, product state must be rejecting for every start state from automaton1
    prod_st1.macro_st = Minimize(prod_st1.macro_st, preorder)   # minimize the macro state for initialization

    for state in automaton1.start_states:
        if state.final_st and prod_st1.macro_st.rejecting:      # if q from (q,I) is accepting and I is not accepting, return false
            return False
        prod_st1.a1_st = state
        next.append(prod_st1)                                   # push product_state to next, later apply initialization

    new_next = []
    for p_state in next:        # initialize(next) part
        cont = False
        # initialize(): condition (2)
        for m_state in p_state.macro_st.states:
            if (p_state.a1_st.name,m_state.name) in preorder:   # pair p<=q from (p,Q), q in Q, was found in preorder
                cont = True
                break                                           # delete product state from next (do not add it to new_next)
        if cont: continue

        # initialize(): condition (1)
        for p_state_2 in next:
            if id(p_state) == id(p_state_2):                            # do not compare same elements (add it to new_next)
                continue
            # (p,P),(q,Q) from next:          p <= q                 &&                         Q <= P
            if (p_state.a1_st.name,p_state_2.a1_st.name) in preorder and Is_subset(p_state_2.macro_st, p_state.macro_st, preorder):
                cont = True
                break                                           # delete product state from next (do not add it to new_next)
        if not cont:
            new_next.append(p_state)
    next = new_next

    if not __debug__:
        print(next)

    while next:         # main loop
        prod_st1 = next.pop()
        processed.append(prod_st1)

        if not __debug__:
            print("Inclusion - current product state: ", prod_st1)

        # get adjacent product states - for all a in alphabet
        for a in alphabet:
            # getting Post(R) for specific letter *a
            redundant = {}
            mc_state = Macro_state()
            mc_state.rejecting = True
            for state in prod_st1.macro_st.states:
                for next_st in state.get_transit_states(a):
                    if next_st.name not in redundant:
                        redundant[next_st.name] = None
                        mc_state.states.append(next_st)
                        if next_st.final_st:
                            mc_state.rejecting = False

            if not __debug__:
                print("Inclusion - new macro state before minim: ", mc_state)
            mc_state = Minimize(mc_state, preorder)
            if not __debug__:
                print("Inclusion - new macro state after minim: ", mc_state)

            # for all Post(r) for specific letter *a and macro state Post(R)
            for next_a1_st in prod_st1.a1_st.get_transit_states(a):
                prod_st2 = Product_state()
                prod_st2.rejecting = False
                prod_st2.macro_st = mc_state
                prod_st2.a1_st = next_a1_st
                if next_a1_st.final_st and prod_st2.macro_st.rejecting:
                    return False

                # optimization 1(b)
                found = False
                for p in prod_st2.macro_st.states:
                    if (prod_st2.a1_st.name,p.name) in preorder:
                        found = True
                        break

                # optimization 2
                if not found:
                    # search in processed for (s,S) such that p <= s && S <= P
                    exists_S = False
                    for prod_S in processed:
                        if (prod_st2.a1_st.name,prod_S.a1_st.name) in preorder and Is_subset(prod_S.macro_st, prod_st2.macro_st, preorder):
                            exists_S = True
                            break
                    if not exists_S:        # if not found yet
                        # search in next for (s,S) such that p <= s && S <= P
                        for prod_S in next:
                            if (prod_st2.a1_st.name,prod_S.a1_st.name) in preorder and Is_subset(prod_S.macro_st, prod_st2.macro_st, preorder):
                                exists_S = True
                                break

                    # if no such (s,S) was found
                    if not exists_S:
                        # remove all (s,S) from processed such that s <= p && P <= S
                        new_processed = []
                        for prod_S in processed:
                            if (prod_S.a1_st.name,prod_st2.a1_st.name) in preorder and Is_subset(prod_st2.macro_st, prod_S.macro_st, preorder):
                                pass
                            else:
                                new_processed.append(prod_S)
                        processed = new_processed

                        # remove all (s,S) from next such that s <= p && P <= S
                        new_next = []
                        for prod_S in next:
                            if (prod_S.a1_st.name,prod_st2.a1_st.name) in preorder and Is_subset(prod_st2.macro_st, prod_S.macro_st, preorder):
                                pass
                            else:
                                new_next.append(prod_S)
                        next = new_next

                        # add (p,P) to next
                        next.append(prod_st2)
                        if not __debug__:
                            print("Inclusion - pushing (into next) product state ", prod_st2)
    return True

# ---------------------------------------------------------------------------------------------------------------
#                                               ADDITIONAL FUNCTIONS
# ---------------------------------------------------------------------------------------------------------------

def Get_identity_relation(automaton1):
    '''
        Function generates the identity relation from states of automaton. It can be used for special versions of universality and inclusion checking.
        Input:
            automaton - source automaton
        Returns: result identity relation
    '''
    preorder = {}
    for state in automaton1.states:
        preorder[(state.name,state.name)] = None
    return preorder

def Union_FA(automaton1, automaton2):
    '''
        Function implements the Union algorithm. Computes automaton1 union automaton2.
        Input:
            automaton1 - first automaton
            automaton2 - second automaton
        Returns: result automaton FA
    '''
    result_automaton = FA()
    if len(automaton1.alphabet) > len(automaton2.alphabet):
        result_automaton.alphabet = set(list(automaton1.alphabet)[:])
    else:
        result_automaton.alphabet = set(list(automaton2.alphabet)[:])
    result_automaton.name = automaton1.name + "+" + automaton2.name
    opt_s = {}
    for state in automaton1.states:
        result_automaton.states.append(state)
        opt_s[state.name] = None
    for state in automaton2.states:
        result_automaton.states.append(state)
        if state.name in opt_s:
            state.name = state.name + "_copy"
    result_automaton.final_states = set(list(automaton1.final_states)[:] + list(automaton2.final_states)[:])
    result_automaton.start_states = set(list(automaton1.start_states)[:] + list(automaton2.start_states)[:])
    return result_automaton

def Complement_FA(automaton1):
    '''
        Function creates a complement of a source automaton. It does not create a new automaton.
        Input:
            automaton1 - source automaton
        Returns: Result automaton.
    '''
    automaton1.final_states = set()
    for state in automaton1.states:
        state.final_st = not state.final_st
        if state.final_st:
            automaton1.final_states.add(state)
    return automaton1

# ---------------------------------------------------------------------------------------------------------------
#                                               MAIN FUNCTION
# ---------------------------------------------------------------------------------------------------------------

def main():
    ''' Main function. Used to parse arguments and call corresponding functions. '''

    # wrong arguments -> help message
    if len(sys.argv) != 2:
        print("Wrong arguments (use: -e | -n | -p | -d | -m | -s | -u | -ui | -i | -ii | -o | -x)\n")
        raise ArgumentError

    automatons = ParseFA()                  # parse automatons
    if not __debug__:
        for automaton in automatons:
            print(automaton.debug_print())  # print automaton

    number_of_states = 0
    number_of_transitions = 0
    for automaton in automatons:
        number_of_states += len(automaton.states)
        for st in automaton.states:
            for lt, tr in st.get_transit_states_items():
                for targ in tr:
                    number_of_transitions += 1

    counter = 0
    length_ms = 500

    # parse arguments and
    if sys.argv[1] == '-e':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- EMPTINESS -------------------------\n")

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Emptiness_test(automatons[0])
            counter += 1
        result_variable = Emptiness_test(automatons[0])
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        if result_variable:
            print("Automaton is empty!\n")
        else:
            print("Automaton is not empty!\n")
    elif sys.argv[1] == '-n':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- REMOVE USELESS STATES -------------------------\n")
        temp = automatons[0].copy_FA()

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Remove_useless_states(automatons[0])
            automatons[0] = temp.copy_FA()
            counter += 1
        Remove_useless_states(automatons[0])
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        print(automatons[0])
    elif sys.argv[1] == '-p':
        if len(automatons) < 2:
            print("The algorithm requires two automatons from stdin!\n")
            raise ArgumentError
        print("------------------------- PRODUCT (INTERSECTION) -------------------------\n")

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Intersection_FA(automatons[0], automatons[1])
            counter += 1
        result_automaton = Intersection_FA(automatons[0], automatons[1])
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        print(result_automaton)
        try:
            pass
        except:
            sys.exit(2)
    elif sys.argv[1] == '-d':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- DETERMINIZATION -------------------------\n")

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Determinization_FA(automatons[0])
            counter += 1
        result_automaton = Determinization_FA(automatons[0])
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        print(result_automaton)
    elif sys.argv[1] == '-m':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- MINIMALIZATION -------------------------\n")
        result_automaton2 = Determinization_FA(automatons[0])

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Minimalization_FA(result_automaton2)
            counter += 1
        result_automaton = Minimalization_FA(result_automaton2)
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        print(result_automaton)
    elif sys.argv[1] == '-s':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- SIMULATION RELATION -------------------------\n")

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Preorder(automatons[0])
            counter += 1
        result_variable = Preorder(automatons[0])
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        print(list(result_variable.keys()))
    elif sys.argv[1] == '-r':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- REDUCTION -------------------------\n")

        swstart = time.time()
        startCPUtime = time.process_time()
        result_variable = Reduction_NFA(automatons[0])
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0) ) + "\n")

        print(result_variable)
        # reduction
    elif sys.argv[1] == '-u':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- UNIVERSALITY -------------------------\n")
        preorder = Preorder(automatons[0])
        # print("Universality - preorder: ", list(preorder.keys()))

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Universality_NFA(automatons[0], preorder)
            counter += 1
        result_variable = Universality_NFA(automatons[0], preorder)
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        if result_variable:
            print("Automaton is universal!")
        else:
            print("Automaton is not universal!")
    elif sys.argv[1] == '-ui':
        if len(automatons) < 1:
            print("The algorithm requires one automaton from stdin!\n")
            raise ArgumentError
        print("------------------------- UNIVERSALITY IDENTITY -------------------------\n")
        preorder = Get_identity_relation(automatons[0])
        # print("Universality identity - preorder: ", list(preorder.keys()))

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Universality_NFA(automatons[0], preorder)
            counter += 1
        result_variable = Universality_NFA(automatons[0], preorder)
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        if result_variable:
            print("Automaton is universal!")
        else:
            print("Automaton is not universal!")
    elif sys.argv[1] == '-i':
        if len(automatons) < 2:
            print("The algorithm requires two automatons from stdin!\n")
            raise ArgumentError
        print("------------------------- INCLUSION -------------------------\n")
        try:
            preorder = Preorder(Union_FA(automatons[0], automatons[1]))
            # print("Inclusion - preorder: ", list(preorder.keys()))

            swstart = time.time()
            startCPUtime = time.process_time()
            whenEnd = startCPUtime + (length_ms/1000.0)
            while time.process_time() < whenEnd:
                Inclusion_NFA(automatons[0], automatons[1], preorder)
                counter += 1
            result_variable = Inclusion_NFA(automatons[0], automatons[1], preorder)
            endCPUtime = time.process_time()
            swend = time.time()

            print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

            if result_variable:
                print("Automaton inclusion A <= B is true!")
            else:
                print("Automaton inclusion A <= B is not true!")
        except AlphabetsIncompatibleError:
            print("Alphabets are incompatible!")
            sys.exit(2)
    elif sys.argv[1] == '-ii':
        if len(automatons) < 2:
            print("The algorithm requires two automatons from stdin!\n")
            raise ArgumentError
        print("------------------------- INCLUSION IDENTITY -------------------------\n")
        try:
            preorder = Get_identity_relation(Union_FA(automatons[0], automatons[1]))
            # print("Inclusion identity - preorder: ", list(preorder.keys()))

            swstart = time.time()
            startCPUtime = time.process_time()
            whenEnd = startCPUtime + (length_ms/1000.0)
            while time.process_time() < whenEnd:
                Inclusion_NFA(automatons[0], automatons[1], preorder)
                counter += 1
            result_variable = Inclusion_NFA(automatons[0], automatons[1], preorder)
            endCPUtime = time.process_time()
            swend = time.time()

            print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

            if result_variable:
                print("Automaton inclusion A <= B is true!")
            else:
                print("Automaton inclusion A <= B is not true!")
        except AlphabetsIncompatibleError:
            print("Alphabets are incompatible!")
            sys.exit(2)
    elif sys.argv[1] == '-o':
        if len(automatons) < 2:
            print("The algorithm requires two automatons from stdin!\n")
            raise ArgumentError
        print("------------------------- UNION -------------------------\n")

        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Union_FA(automatons[0], automatons[1])
            counter += 1
        result_automaton = Union_FA(automatons[0], automatons[1])
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        print(result_automaton)
    elif sys.argv[1] == '-x':
        if len(automatons) < 3:
            print("The algorithm requires three automatons from stdin!\n")
            raise ArgumentError
        print("------------------------- SEQUENCE -------------------------\n")
        swstart = time.time()
        startCPUtime = time.process_time()
        whenEnd = startCPUtime + (length_ms/1000.0)
        while time.process_time() < whenEnd:
            Complement_FA(Determinization_FA(Union_FA(Intersection_FA(automatons[0], automatons[1]), automatons[2])))
            counter += 1
        result_automaton = Complement_FA(Determinization_FA(Union_FA(Intersection_FA(automatons[0], automatons[1]), automatons[2])))
        endCPUtime = time.process_time()
        swend = time.time()

        print("states: " + str(number_of_states) + " transitions: " + str(number_of_transitions) + " cpu: " + "{:.9f}".format( ((endCPUtime-startCPUtime)*1000.0)/(counter+1) ) + " wall: " + "{:.9f}".format( ((swend-swstart)*1000.0)/(counter+1) ) + "\n")

        print(result_automaton)
    else:
        print("Wrong arguments (use: -e | -n | -p | -d | -m | -s | -u | -ui | -i | -ii | -o | -x)")
        raise ArgumentError



# ---------------------------------------- MAIN INVOCATION ----------------------------------------
main()



