/*
 * Kód k bakalářské práci v jazyce C++.
 * Autor: Ondřej Polanský
 * FIT VUT
 * Brno 24.04.2020
 * Obsah:
        datové struktury
        parsování automatů ze vstupu
        výpisové funkce
        jednotlivé implementace algoritmů
        funkce main a měření
*/

#include <iostream>
#include <vector>
#include <list>
#include <queue>
#include <stack>
#include <map>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <utility>
#include <string>
#include <algorithm>
#include <chrono>
#include <ctime>
#include <iomanip>

//#define MAIN_DEBUG
//#define PARSE_DEBUG
//#define EMPTINESS_DEBUG
//#define USELESS_DEBUG
//#define INTERSECTION_DEBUG
//#define DETERMINIZATION_DEBUG
//#define MINIMALIZATION_DEBUG
//#define REDUCTION_DEBUG
//#define UNIVERSALITY_DEBUG
//#define INCLUSION_DEBUG

//#define DETERMINIZATION_FAIL_SWITCH


// --------------------------------------------------------------------------------
//                              DATA STRUCTURES
// --------------------------------------------------------------------------------

// structure containing information about state
typedef struct st{
    std::string name;                                               // name of the state
    std::multimap<std::string, struct st *> transit_states_p;              // map of following states and transition rules - (alphabet letter,pointer)
    std::multimap<std::string, struct st *> reversed_transit_states_p;     // map of reversed transit. states and transition rules - (alphabet letter,pointer)
    bool final_st = false;                                          // true -> state is final, else -> false
    bool start_st = false;                                          // true -> state is start, else -> false
    bool visited = false;                                           // true -> state was visited, else -> false
    short int flag = 0;                                             // flag for multiple purposes
    std::map<std::string, int> card;                                // compute cardinality (NFA reduction - Ilie)
} State;

// structure containing information about finite automaton
typedef struct {
    std::string name;                                       // name of the automaton
    std::list<State> states;
    std::vector<std::string> alphabet;                      // vector of alphabet
    std::multimap<std::pair<std::string, std::string>, std::string> transitions;   // table of transitions - not used
    std::multimap<std::pair<std::string, std::string>, std::string> reversed_transitions;   // table of reversed transitions - not used
    std::vector<State *> start_states;                      // vector of starting states - pointers
    std::set<State *> final_states;                         // set of final states - pointers
} FA;

// structure used in Intersection algorithm
typedef struct {
    State * first;                  // state from FA A
    State * second;                 // state from FA B
    State * source;                 // already pushed state from FA A&B
} Inters_help;

// structure used in Determinization algorithm
typedef struct {
    std::vector<State *> states;    // states to merge
    State * source;                 // already pushed merged state
} Determin_help;

// structure used in Minimalization algorithm
typedef struct {
    State * source;
    std::string letter;
    State * target;
} Minimal_help;

// structure used in Universality and Inclusion algorithm
typedef struct {
    std::vector<State *> states;    // states of a macro state
    bool rejecting;                 // indicates if macro state is accepting or rejecting
} Macro_state;

// structure used in Inclusion algorithm
typedef struct {
    State *a1_st;                   // state from first automaton
    Macro_state macro_st;           // macro state in second automaton
    bool rejecting;                 // indicates if product state is accepting or rejecting
} Product_state;

// rule for computing hash in unordered_set
struct pair_hash
{
    std::size_t operator () (std::pair<std::string,std::string> const &p) const
    {
        std::size_t h1 = std::hash<std::string>()(p.first);
        std::size_t h2 = std::hash<std::string>()(p.second);

        return h1^h2;
    }
};

// --------------------------------------------------------------------------------
//                              AUTOMATON PARSER
// --------------------------------------------------------------------------------

// Parses automaton from stdin and saves them into corresponding structures. Saves automatons into Automatons. Expects correct format.
// input: Automatons - reference to vector<FA>
// returns: void
void parse_FA_stdin(std::vector<FA> &Automatons)
{
    std::vector<std::string> alphabet;  // vector of alphabet
    std::string word;                   // word received from stdin
    int state = 0;                      // state of the parsing automaton
    short int counter = 0;              // variable for transition parsing
    bool start_state = false;           // variable for start state parsing
    std::string transit_letter;         // variable for transition parsing
    std::string source_state;           // variable for transition parsing
    std::string target_state;           // variable for transition parsing

    // reads words from stdin and parses them
    while(std::cin >> word)
    {
        #ifdef PARSE_DEBUG
            std::cout << word << std::endl;
        #endif

        // states of the automaton
        if(word == "Ops" && state == 6) {alphabet.clear();state = 1;continue;}              // idle
        else if(word == "Ops" && state == 0) {state = 1;continue;}                          // alphabet
        else if(word == "Automaton" && (state == 1 || state == 6)) {state = 2;continue;}    // automaton name
        else if(word == "States" && state == 2) {state = 3;continue;}                       // states
        else if(word == "Final" && state == 3) {state = 4;continue;}
        else if(word == "States" && state == 4) {state = 5;continue;}                       // final states
        else if(word == "Transitions" && state == 5) {state = 6;continue;}                  // transitions

        if(state == 1) // reads alphabet
        {
            if(word[word.find(":")+1] != '1') continue;    // automaton accepts only unary symbols (a:1)
            alphabet.push_back(word.substr(0, word.find(":")));    // alphabet symbol is the first one
        }
        else if(state == 2) // reads name of the automaton and assigns the alphabet
        {
            FA automaton;
            Automatons.push_back(automaton);
            Automatons.back().name = word;
            std::sort(alphabet.begin(), alphabet.end());
            Automatons.back().alphabet = alphabet;
        }
        else if(state == 3) // reads a list of states
        {
            State st;
            st.name = word;
            st.visited = false;
            st.start_st = false;
            st.final_st = false;
            st.flag = 0;
            Automatons.back().states.push_back(st);
        }
        else if(state == 5) // reads a list of final states
        {
            // finds state in the vector of states and pushes pointer to the state
            for(auto i = Automatons.back().states.begin(); i != Automatons.back().states.end();++i)
                if(i->name == word)
                {
                    i->final_st = true;
                    Automatons.back().final_states.insert(&(*i));
                    break;
                }
        }
        else if(state == 6) // parses transitions
        {
            if(counter == 0)                                        // left side of a(p)->q
            {
                if(word.find("(") == std::string::npos)             // start state
                {
                    start_state = true;
                }
                else                                                // normal transition
                {
                    std::size_t bracket_start = word.find("(");
                    std::size_t bracket_end = word.find(")");
                    transit_letter = word.substr(0, bracket_start);// word = "a01(p)"
                    source_state = word.substr(bracket_start+1, bracket_end-bracket_start-1);
                    #ifdef PARSE_DEBUG
                        std::cout << "TRANSIT: " << transit_letter << " SOURCE STATE: " + source_state << std::endl;
                    #endif
                }
                counter++;
            }
            else if(counter == 1)                                   // arrow in a(p)->q
            {
                counter++;
                continue;
            }
            else                                                    // right side of a(p)->q
            {
                target_state = word;
                #ifdef PARSE_DEBUG
                    std::cout << "TARGET: " + target_state << std::endl;
                #endif

                if(!start_state)    // is not a start state
                {
                    Automatons.back().transitions.insert({{source_state,transit_letter},target_state}); // fill the transition multimap
                    Automatons.back().reversed_transitions.insert({{target_state,transit_letter},source_state}); // fill the reversed transition multimap

                    for(auto i = Automatons.back().states.begin(); i != Automatons.back().states.end(); ++i)                    // fill the optimalised transition tree
                        if(i->name == source_state)
                        {
                            for(auto j = Automatons.back().states.begin(); j != Automatons.back().states.end(); ++j)
                                if(j->name == target_state)
                                {
                                    i->transit_states_p.insert({transit_letter, &(*j)});
                                    j->reversed_transit_states_p.insert({transit_letter, &(*i)});
                                }
                        }
                }
                else                // is a start state
                {
                    for(auto i = Automatons.back().states.begin(); i != Automatons.back().states.end(); ++i)                    // fill the start_states vector
                        if(i->name == target_state)
                        {
                            i->start_st = true;
                            Automatons.back().start_states.push_back(&(*i));
                        }
                    start_state = false;
                }
                counter = 0;
            }
        }
    }

    if(state != 6) {throw "Parsing error!";}    // parsing must end with transitions
}

// --------------------------------------------------------------------------------
//                         OUTPUT AND PRINT FUNCTIONS
// --------------------------------------------------------------------------------

// Function prints all automatons to stdout. It is meant for debug purposes - prints more information.
// input: automatons - vector<FA>
// returns: void
void print_FA(std::vector<FA> automatons)
{
    for(auto i = automatons.begin();i != automatons.end();++i)
    {
        std::cout << "Printing automaton " + i->name << std::endl;

        std::cout << "Q = {" << std::endl;
        for(auto j = i->states.begin(); j != i->states.end(); ++j)
        {
            if(j->flag == -1) continue; // deleted state
            std::cout << std::boolalpha << "\t" << j->name << " (final: " << j->final_st << ", start: " << j->start_st << ", visited: " << j->visited << ", flag: " << j->flag << "):" << std::endl;
            for(auto const& x : j->transit_states_p)
                std::cout << "\t\tNext state: (" << x.first << ", " << x.second->name << ")" << std::endl;
            for(auto const& x : j->reversed_transit_states_p)
                std::cout << "\t\tPrev state: (" << x.first << ", " << x.second->name << ")" << std::endl;
        }
        std::cout << "}" << std::endl;

        std::cout << "A = {";
        for(auto j = i->alphabet.begin(); j != i->alphabet.end(); ++j)
            std::cout << *j << ", ";
        std::cout << "}" << std::endl;

        std::cout << "r = {";
        for(auto j = i->transitions.begin(); j != i->transitions.end(); ++j)
            std::cout << j->first.first << "(" << j->first.second << ")" << "->" << j->second << ", ";
        std::cout << "}" << std::endl;

        std::cout << "rr = {";
        for(auto j = i->reversed_transitions.begin(); j != i->reversed_transitions.end(); ++j)
            std::cout << j->first.first << "(" << j->first.second << ")" << "->" << j->second << ", ";
        std::cout << "}" << std::endl;

        std::cout << "s = {";
        for(auto j = i->start_states.begin(); j != i->start_states.end(); ++j)
            std::cout << (*j)->name << ", ";
        std::cout << "}" << std::endl;

        std::cout << "F = {";
        for(auto j = i->final_states.begin(); j != i->final_states.end(); ++j)
            std::cout << (*j)->name << ", ";
        std::cout << "}" << std::endl;

        std::cout << std::endl << std::endl;
    }
}

// Function prints automaton to stdout. Main printing function meant for printing results.
// input: automaton - FA
// input: alg_flag - bool - if true, does not print states with flag = -1
// returns: void
void Print_result_FA(FA &automaton, bool alg_flag = false)
{
    std::cout << "Printing automaton " + automaton.name << std::endl;

    std::cout << "Q = {";
    for(auto j = automaton.states.begin(); j != automaton.states.end(); ++j)
    {
        if(j->flag == -1) continue; // deleted state
        std::cout << j->name << ", ";
    }
    std::cout << "}" << std::endl;

    std::cout << "A = {";
    for(auto j = automaton.alphabet.begin(); j != automaton.alphabet.end(); ++j)
        std::cout << *j << ", ";
    std::cout << "}" << std::endl;

    std::cout << "r = {";
    for(auto j = automaton.states.begin(); j != automaton.states.end(); ++j)
    {
        if(j->flag == -1) continue; // deleted state
        for(auto const& x : j->transit_states_p)
            if(alg_flag)
                { if(x.second->flag != -1) std::cout << j->name << "(" << x.first << ")" << "->" << x.second->name << ", "; } // transition to deleted state
            else std::cout << j->name << "(" << x.first << ")" << "->" << x.second->name << ", "; // transition to deleted state

    }
    std::cout << "}" << std::endl;

    std::cout << "s = {";
    for(auto j = automaton.start_states.begin(); j != automaton.start_states.end(); ++j)
        if((*j)->flag != -1) std::cout << (*j)->name << ", ";
    std::cout << "}" << std::endl;

    std::cout << "F = {";
    for(auto j = automaton.final_states.begin(); j != automaton.final_states.end(); ++j)
        if((*j)->flag != -1) std::cout << (*j)->name << ", ";
    std::cout << "}" << std::endl;

    std::cout << std::endl << std::endl;
}

// Function prints state queue to stdout. It is meant for debug purposes.
// input: q - queue<State *>
// returns: void
void Print_state_queue(std::queue<State *> q)
{
    std::cout << "Printing queue: {";
    while(!q.empty())
    {
        std::cout << q.front()->name << ", ";
        q.pop();
    }
    std::cout << "}" << std::endl;
}

// Function prints state stack to stdout. It is meant for debug purposes.
// input: q - stack<State *>
// returns: void
void Print_state_stack(std::stack<State *> q)
{
    std::cout << "Printing queue: {";
    while(!q.empty())
    {
        std::cout << q.top()->name << ", ";
        q.pop();
    }
    std::cout << "}" << std::endl;
}

// Function prints language partition to stdout (minimalization). It is meant for debug purposes.
// input: Partition_lan - reference to list<vector<State *>>
// returns: void
void Partition_print(std::list<std::vector<State *>> &Partition_lan)
{
    std::cout << "Partition print:\n";
    for(auto x  = Partition_lan.begin(); x != Partition_lan.end(); ++x)
    {
        std::cout << "\t{";
        for(auto y = x->begin(); y != x->end(); ++y)
        {
            std::cout << (*y)->name << ", ";
        }
        std::cout << "}" << std::endl;
    }
}

// Function prints minimalization queue to stdout. It is meant for debug purposes.
// input: W - reference to list<pair<string, vector<State *> *>>
// returns: void
void Minim_queue_print(std::list<std::pair<std::string, std::vector<State *> *>> &W)
{
    std::cout << "Queue print:\n\t{";
    for(auto i = W.begin(); i != W.end(); ++i)
    {
        std::cout << "(" << i->first << ",[";
        for(auto j = i->second->begin(); j != i->second->end(); ++j)
        {
            std::cout << (*j)->name << ", ";
        }
        std::cout << "]), ";
    }
    std::cout << "}" << std::endl;
}

// Function prints list or vector of states to stdout. It is meant for debug purposes.
// input: data_struct - reference to T
// returns: void
template <class T>
void Print_iter(T &data_struct)
{
    std::cout << "{";
    for(auto i = data_struct.begin(); i != data_struct.end(); ++i)
        std::cout << (*i)->name << ", ";
    std::cout << "}";
}

// Function prints <st_name,st_name> container in preorder to stdout. It is meant for debug purposes.
// input: data_struct - reference to Tmpl
// returns: void
template <class Tmpl>
void Print_reduct(Tmpl &data_struct)
{
    std::cout << "{";
    for(auto i = data_struct.begin(); i != data_struct.end(); ++i)
        std::cout << "(" << i->first << "," << i->second << "), ";
        //if(i->first != nullptr && i->second != nullptr) std::cout << "(" << i->first->name << "," << i->second->name << "), ";
    std::cout << "}" << std::endl;
}

// Function prints macro state to stdout. It is meant for debug purposes.
// input: m - reference to Macro_state
// returns: void
void Print_MacroState(Macro_state &m)
{
    std::cout << "[";
    for(auto i = m.states.begin(); i != m.states.end(); ++i)
    {
        std::cout << (*i)->name << ", ";
    }
    std::cout << "] " << m.rejecting << std::endl;
}

// -------------------------------------------------------------------------------------------------
//                                       AUTOMATON ALGORITHMS
// -------------------------------------------------------------------------------------------------

// ---------------------------------------- EMPTINESS -----------------------------------------

// Function checks if automaton is empty. It is basically a Depth-first search (DFS) in a tree of states.
// input: automaton - reference to FA
// returns: true - automaton language is empty, false - automaton language is not empty
bool Emptiness_test(FA &automaton)
{
    std::stack<State *>state_q;
    State * st;
    std::unordered_set<std::string> visited_htab;

    // pushes all start states to the state stack (pointers)
    for(auto i = automaton.start_states.begin(); i != automaton.start_states.end();++i)
    {
        visited_htab.insert((*i)->name);
        state_q.push(*i);
    }

    // takes states from stack and looks if they are final
    // if yes -> return false
    // if no  -> push all forward states onto the stack and keep checking
    while(!state_q.empty())
    {
        #ifdef EMPTINESS_DEBUG
            Print_state_stack(state_q);
        #endif

        st = state_q.top();
        state_q.pop();
        if(st->final_st) return false;
        for(auto const& transition : st->transit_states_p)
        {
            if(visited_htab.find(transition.second->name) == visited_htab.end()) // do not push an already visited state again
            {
                visited_htab.insert(transition.second->name);
                state_q.push(transition.second);
            }
        }
    }
    return true;
}
// ---------------------------------------- USELESS STATES -----------------------------------------

// Function returns iterator pointing to a state with a specific name.
// input: start_states - reference to vector<State *>
// input: name - string - name of the state
// returns: iterator to a vector of states
inline std::vector<State *>::iterator find_in_start_states(std::vector<State *> &start_states, std::string name)
{
    auto st = start_states.begin();
    for(; st != start_states.end(); ++st)
        if((*st)->name == name) break;
    return st;
}
// Function removes relations with states that should be removed.
// input: state - iterator into list of states
// returns: void
inline void Remove_relations(std::list<State>::iterator state)
{
    std::pair<std::multimap<std::string, State *>::iterator,std::multimap<std::string, State *>::iterator> range1;

    for(auto rel = state->transit_states_p.begin(); rel != state->transit_states_p.end(); ++rel)
    {
        range1 = rel->second->reversed_transit_states_p.equal_range(rel->first);    // update reversed relations of all next states
        for(auto i = range1.first; i != range1.second; ++i)
            if(i->second->name == state->name) { rel->second->reversed_transit_states_p.erase(i); break; }
    }
    for(auto rel = state->reversed_transit_states_p.begin(); rel != state->reversed_transit_states_p.end(); ++rel)
    {
        range1 = rel->second->transit_states_p.equal_range(rel->first);    // update outgoing relations of all previous states
        for(auto i = range1.first; i != range1.second; ++i)
            if(i->second->name == state->name) { rel->second->transit_states_p.erase(i); break; }
    }
    state->transit_states_p.clear();            // clear relations of a useless state
    state->reversed_transit_states_p.clear();
}

// Function takes automaton with states that need to be removed and removes those states.
// input: automaton - reference to automaton
// input: alg - id of algorithm calling this function (0 - useless, 1 - reduction)
// input: visited_htab - reference to hash table of state names (from start states)
// input: flag_htab - reference to hash table of state names (from final states)
// returns: void
void Restore_FA(FA &automaton, short int alg, std::unordered_set<std::string> &visited_htab, std::unordered_set<std::string> &flag_htab)
{
    // remove states that should be removed
    for(auto state = automaton.states.begin(); state != automaton.states.end();)
    {
        // if state was not visited both from beginning (visited_htab) and end (flag_htab)
        // it is complicated because it is being used from two functions
        if( (alg == 0 && !(flag_htab.find(state->name) != flag_htab.end() && visited_htab.find(state->name) != visited_htab.end())) || (alg == 1 && state->flag == -1) )
        {
            if(state->start_st)     // remove the state from start states
            {
                for(auto st = automaton.start_states.begin(); st != automaton.start_states.end(); ++st)
                {
                    if((*st)->name == state->name)
                    {
                        *st = *(automaton.start_states.rbegin());
                        automaton.start_states.pop_back();
                        break;
                    }
                }
            }
            if(state->final_st)     // remove the state from final states
            {
                automaton.final_states.erase(&(*state));
            }
            Remove_relations(state);
            state = automaton.states.erase(state);
        }
        else ++state;
    }
}

// Function implements the Remove useless states algorithm. Removes all non-ending and non-reachable states.
// Has three parts - breadth-first search from start states (saves into visited_htab), breadth-first search
// from final states andreversed automaton (saves into flag_htab), remove states that are not in both tables.
// input: automaton - reference to automaton
// returns: void
void Remove_useless_states(FA &automaton)
{
    std::queue<State *>state_q;
    State * st;
    std::unordered_set<std::string> visited_htab;
    std::unordered_set<std::string> flag_htab;

    // -------------- finding non-reachable states ------------------

    // pushes all start states to the state queue (pointers)
    for(auto i = automaton.start_states.begin(); i != automaton.start_states.end();++i)
    {
        visited_htab.insert((*i)->name);     // start states are reachable from start
        state_q.push(*i);
    }

    // goes through all transitions from start and marks visited states
    // not visited states are non-reachable and will be removed
    while(!state_q.empty())
    {
        #ifdef USELESS_DEBUG
            std::cout << "start: ";
            Print_state_queue(state_q);
            print_FA({automaton});
        #endif

        st = state_q.front();
        for(auto const& transition : st->transit_states_p)
        {
            if(visited_htab.find(transition.second->name) == visited_htab.end()) // do not push an already visited state again
            {
                visited_htab.insert(transition.second->name);
                state_q.push(transition.second);
            }
        }
        state_q.pop();
    }

    // -------------- finding non-ending states ------------------

    // pushes all final states to the state queue (pointers)
    for(auto i = automaton.final_states.begin(); i != automaton.final_states.end();++i)
    {
        flag_htab.insert((*i)->name);       // final states are reachable from end
        state_q.push(*i);
    }

    // goes through all transitions from final states and marks visited states
    // not visited states are non-ending and will be removed
    while(!state_q.empty())
    {
        #ifdef USELESS_DEBUG
            std::cout << "final: ";
            Print_state_queue(state_q);
            print_FA({automaton});
        #endif

        st = state_q.front();
        for(auto const& transition : st->reversed_transit_states_p)
        {
            if(flag_htab.find(transition.second->name) == flag_htab.end()) // do not push an already visited state again
            {
                flag_htab.insert(transition.second->name);
                state_q.push(transition.second);
            }
        }
        state_q.pop();
    }

    // ------------------------------ setting flag and modifying automaton -----------------------------------
    Restore_FA(automaton, 0, visited_htab, flag_htab);  // modify automaton
}

// ---------------------------------------- INTERSECTION -----------------------------------------

// Function implements the Intersection algorithm. Computes intersection of two automatons by making pairs of states.
// input: automaton1 - reference to first automaton, used to compute intersection
// input: automaton2 - reference to second automaton, used to compute intersection
// input: result_automaton - reference to result automaton, used to store result automaton
// returns: void
void Intersection_FA(FA &automaton1, FA &automaton2, FA &result_automaton)
{
    std::queue<Inters_help> W;      // queue W from algorithm
    Inters_help st_pair;            // structure pushed to the queue
    State st;                       // the state structure
    std::string a;                  // alphabet letter - main loop
    std::unordered_map<std::string,State *> optim_Q;  // optimalization of finding state in Q - hash table of state names
    std::pair<std::multimap<std::string,State *>::iterator, std::multimap<std::string,State *>::iterator> range1, range2; // iterator pairs for equal_range

    #ifdef INTERSECTION_DEBUG
        std::cout << "\nIntersection: printing input automatons..." << std::endl;
        Print_result_FA(automaton1);
        Print_result_FA(automaton2);
    #endif // INTERSECTION_DEBUG

    // checking if alphabets are the same - they are sorted
    //if(automaton1.alphabet != automaton2.alphabet) {throw "Intersection: alphabets are different!";}
    if(automaton1.alphabet.size() < automaton2.alphabet.size())
        result_automaton.alphabet = automaton1.alphabet;
    else
        result_automaton.alphabet = automaton2.alphabet;

    // building a new automaton that will be returned
    result_automaton.name = automaton1.name + "&" + automaton2.name;

    // cartesian product of starting states - push them to Q, S, F and W
    for(auto i = automaton1.start_states.begin(); i != automaton1.start_states.end(); ++i)
    {
        for(auto j = automaton2.start_states.begin(); j != automaton2.start_states.end(); ++j)
        {
            st.name = (*i)->name + (*j)->name;      // create a name for a new state
            st.start_st = true;
            result_automaton.states.push_back(st);  // push the state to Q
            optim_Q.insert({st.name,&result_automaton.states.back()});                    // push the state name and pointer to hash table
            result_automaton.start_states.push_back(&(result_automaton.states.back()));     // push the state to S
            if((*i)->final_st && (*j)->final_st)    // set the final state variable
            {
                result_automaton.final_states.insert(&(result_automaton.states.back()));    // mozna to neni potreba
                result_automaton.states.back().final_st = true;
            }
            else
                result_automaton.states.back().final_st = false;
            W.push({*i,*j,&(result_automaton.states.back())});    // push the state to W
        }
    }

    #ifdef INTERSECTION_DEBUG
        Print_result_FA(result_automaton);
    #endif // INTERSECTION_DEBUG

    // main loop - until queue is empty
    while(!W.empty())
    {
        st_pair = W.front();
        #ifdef INTERSECTION_DEBUG
            std::cout << "\nIntersection - st_pair: " << st_pair.first->name << ", " << st_pair.second->name << ", " << st_pair.source->name << std::endl;
        #endif // INTERSECTION_DEBUG

        // it looks only at the alphabet of the first state instead of running through the entire alphabet of the automaton
        for(auto it = st_pair.first->transit_states_p.begin(); it != st_pair.first->transit_states_p.end(); it = range1.second)
        {
            a = it->first;
            #ifdef INTERSECTION_DEBUG
                std::cout << "\nIntersection - main loop: " << "letter: " << a << "\n";
            #endif // INTERSECTION_DEBUG

            // find all states accessible from the current pair
            range1 = st_pair.first->transit_states_p.equal_range(a);
            range2 = st_pair.second->transit_states_p.equal_range(a);

            // cartesian product of accessible states
            for(auto i = range1.first; i != range1.second; ++i)
            {
                #ifdef INTERSECTION_DEBUG
                    std::cout << "\t" << i->first << ", " << i->second->name << "\n";
                #endif // INTERSECTION_DEBUG
                for(auto j = range2.first; j != range2.second; ++j)
                {
                    #ifdef INTERSECTION_DEBUG
                        std::cout << "\t\t" << j->first << ", " << j->second->name << std::endl;
                    #endif // INTERSECTION_DEBUG

                    st.name = i->second->name + j->second->name;
                    st.start_st = false;

                    // add state only if it is not already in Q (new automaton)
                    //if(k == result_automaton.states.rend())
                    auto seek = optim_Q.find(st.name);
                    if(seek == optim_Q.end())
                    {
                        result_automaton.states.push_back(st);          // insert the new state
                        optim_Q.insert({st.name,&result_automaton.states.back()});   // push the state name and pointer to hash table
                        if(i->second->final_st && j->second->final_st)  // insert state into final state set
                        {
                            result_automaton.states.back().final_st = true;
                            result_automaton.final_states.insert(&result_automaton.states.back());
                        }
                        else
                            result_automaton.states.back().final_st = false;
                        W.push({i->second,j->second,&result_automaton.states.back()});    // push the state to W

                        // always push relations
                        st_pair.source->transit_states_p.insert({a,&result_automaton.states.back()});
                        result_automaton.states.back().reversed_transit_states_p.insert({a,st_pair.source});    // reversed mozna neni potreba
                    }
                    else
                    {
                        // always push relations
                        st_pair.source->transit_states_p.insert({a,seek->second});
                        seek->second->reversed_transit_states_p.insert({a,st_pair.source});    // reversed mozna neni potreba
                    }
                }
            }
        }
        W.pop();
        #ifdef INTERSECTION_DEBUG
            std::cout << "\nIntersection - endloop: \n";
            Print_result_FA(result_automaton);
        #endif // INTERSECTION_DEBUG
    }
}

// ---------------------------------------- DETERMINIZATION -----------------------------------------

// Function implements the Determinization algorithm. Computes deterministic version of input automaton.
// input: automaton1 - reference to source automaton, used to compute determinization
// input: result_automaton - reference to result automaton, used to store result automaton
// returns: void
void Determinization_FA(FA &automaton1, FA &result_automaton)
{
    std::queue<Determin_help> W;    // queue W from algorithm
    Determin_help st_vect;          // structure pushed to the queue - contains vector of source states and a pointer to a new state created from source states
    State st;                       // the state structure
    std::vector<State *> storage;
    std::pair<std::multimap<std::string,State *>::iterator, std::multimap<std::string,State *>::iterator> range1; // iterator pair for equal_range
    #ifdef DETERMINIZATION_FAIL_SWITCH
    State * fail = nullptr;         // pointer to a fail state
    #endif
    std::vector<std::string> opt_name;              // optimizes dealing with S1S2S3, S2S1S3, S3S2S1, ... states - it is the same state
    std::unordered_set<std::string> opt_storage;    // optimizes searching in storage - prevents states like S1S1S1S2S3 or S1S1S2S3S3
    std::unordered_map<std::string,State *> opt_Q;  // optimizes searching in Q

    #ifdef DETERMINIZATION_DEBUG
        std::cout << "\nDeterminization: printing input automaton..." << std::endl;
        Print_result_FA(automaton1);
        print_FA({automaton1});
    #endif

    // building a new automaton that will be returned
    result_automaton.name = "det" + automaton1.name;
    result_automaton.alphabet = automaton1.alphabet;

    // create the new start state by merging all start states
    st.name = "|";
    st.start_st = true;
    st.final_st = false;
    // optimalization - find all state names and push them into a vector
    for(auto i = automaton1.start_states.begin(); i != automaton1.start_states.end(); ++i)
    {
        opt_name.push_back((*i)->name);
        if((*i)->final_st) st.final_st = true;  // if atleast one state is final, the new state is final too
    }
    std::sort(opt_name.begin(), opt_name.end());    // sort the vector of state names
    for(auto i = opt_name.begin(); i != opt_name.end(); ++i)
        st.name = st.name + *i + "|";         // create a name for the new state by merging names

    result_automaton.states.push_back(st);  // push the state to Q
    opt_Q.insert({st.name,&result_automaton.states.back()});
    result_automaton.start_states.push_back(&result_automaton.states.back());    // push the state to S
    if(st.final_st) result_automaton.final_states.insert(&result_automaton.states.back());   // mozna to neni potreba
    W.push({automaton1.start_states,&result_automaton.states.back()});   // push the state to W

    #ifdef DETERMINIZATION_DEBUG
        Print_result_FA(result_automaton);
    #endif

    // main loop - until queue is empty
    while(!W.empty())
    {
        st_vect = W.front();
        #ifdef DETERMINIZATION_DEBUG
            std::cout << "\nDeterminization - st_vect: ";
            for(auto i = st_vect.states.begin(); i != st_vect.states.end(); ++i)
                std::cout << (*i)->name << ", ";
            std::cout << "|| " << st_vect.source->name << std::endl;
        #endif

        // for every letter of the alphabet
        for(auto a = result_automaton.alphabet.begin(); a != result_automaton.alphabet.end(); ++a)
        {
            #ifdef DETERMINIZATION_DEBUG
                std::cout << "\nDeterminization - main loop: letter: " << *a << "\n";
            #endif

            st.name = "|";           // create and initialize a new state
            st.final_st = false;
            opt_name.clear();
            opt_storage.clear();
            // goes through all source states
            for(auto i = st_vect.states.begin(); i != st_vect.states.end(); ++i)
            {
                // for every state finds states reachable by the letter
                range1 = (*i)->transit_states_p.equal_range(*a);
                for(auto j = range1.first; j != range1.second; ++j)
                {
                    // insert the same state only once
                    if(opt_storage.insert(j->second->name).second)
                    {
                        opt_name.push_back(j->second->name);    // push name of the state to optimalizing vector
                        if(j->second->final_st) st.final_st = true;     // if atleast one state is final, the new state is final too
                        storage.push_back(j->second);           // push to W later
                    }
                }
            }
            std::sort(opt_name.begin(), opt_name.end());        // sort names
            for(auto i = opt_name.begin(); i != opt_name.end(); ++i)
                st.name = st.name + *i + "|";            // create a name for the new state by merging names

            // NEBO PRIDAT FAIL STAV? MUSI MIT DFA  PRO KAZDY STAV VSECHNY PRECHODY?
            #ifndef DETERMINIZATION_FAIL_SWITCH
            if(storage.empty()) continue;   // if no state can be reached by chosen letter -> continue to the next letter
            #else
            if(storage.empty())
            {
                if(fail == nullptr)     // adds a fail state if it does not exist
                {
                    st.name = "fail";
                    st.start_st = false;
                    st.final_st = false;
                    result_automaton.states.push_back(st);
                    fail = &result_automaton.states.back();

                    // add transitions from fail to fail for every letter
                    for(auto alph = automaton1.alphabet.begin(); alph != automaton1.alphabet.end(); ++alph)
                    {
                        fail->transit_states_p.insert({*alph,fail});
                        fail->reversed_transit_states_p.insert({*alph,fail});
                    }
                }
                st_vect.source->transit_states_p.insert({*a,fail});
                fail->reversed_transit_states_p.insert({*a,st_vect.source});
                continue;
            }
            #endif // DETERMINIZATION_FAIL_SWITCH

            // add state only if it is not already in Q (new automaton)
            auto seek = opt_Q.find(st.name);
            if(seek == opt_Q.end())
            {
                st.start_st = false;
                result_automaton.states.push_back(st);  // push the state to Q
                opt_Q.insert({st.name,&result_automaton.states.back()});
                if(st.final_st) result_automaton.final_states.insert(&result_automaton.states.back());   // mozna to neni potreba
                W.push({storage,&result_automaton.states.back()});   // push the state to W

                // always push relations
                st_vect.source->transit_states_p.insert({*a,&result_automaton.states.back()});
                result_automaton.states.back().reversed_transit_states_p.insert({*a,st_vect.source});    // reversed mozna neni potreba
            }
            else
            {
                // always push relations
                st_vect.source->transit_states_p.insert({*a,seek->second});
                seek->second->reversed_transit_states_p.insert({*a,st_vect.source});    // reversed mozna neni potreba
            }
            storage.clear();
        }
        W.pop();
        #ifdef DETERMINIZATION_DEBUG
            std::cout << "\nDeterminization - endloop: \n";
            Print_result_FA(result_automaton);
        #endif
    }
}

// ---------------------------------------- MINIMALIZATION -----------------------------------------

// Function implements the Hopcroft algorithm. Computes the language partition, which is a list of blocks of states.
// input: automaton1 - reference to source automaton, used to compute language partition
// input: Partition_lan - result language partition
// returns: void
void Hopcroft(FA &automaton1, std::list<std::vector<State *>> &Partition_lan)
{
    std::vector<State *> block1, block2;                    // block of the partition
    std::pair<std::string, std::vector<State *> *> splitter;         // (a,B) splitter
    std::list<std::pair<std::string, std::vector<State *> *>> W;     // list of (a,B) splitters
    std::vector<State *> *bl1, *bl2;                        // pointers to blocks in the partition
    bool splits_in, splits_out;                             // if both are true -> splitter splits a block
    std::vector<State *> missing_block;

    std::multimap<std::string, State *>::iterator iter;

    // first condition of the algorithm - initializing partition
    if(automaton1.final_states.empty() || automaton1.final_states.size() == automaton1.states.size())
    {
        for(auto i = automaton1.states.begin(); i != automaton1.states.end(); ++i)
            block1.push_back(&(*i));
        Partition_lan.push_back(block1);    // Q
        #ifdef MINIMALIZATION_DEBUG
            std::cout << "Minimalization: F=={} or Q-F=={}" << std::endl;
        #endif // MINIMALIZATION_DEBUG
        return;
    }
    else
    {
        Partition_lan.push_back({});        // F
        Partition_lan.push_back({});        // Q-F
        for(auto i = automaton1.states.begin(); i != automaton1.states.end(); ++i)
        {
            if(i->final_st) Partition_lan.front().push_back(&(*i));
            else Partition_lan.back().push_back(&(*i));
        }
    }
    #ifdef MINIMALIZATION_DEBUG
        std::cout << "Partition print - first condition:\n";
        Partition_print(Partition_lan);
    #endif // MINIMALIZATION_DEBUG

    // fill W queue - (a,min{F,Q-F})
    if(Partition_lan.front().size() < Partition_lan.back().size())
    {
        for(auto a = automaton1.alphabet.begin(); a != automaton1.alphabet.end(); ++a)
            W.push_back({*a,&Partition_lan.front()});
    }
    else
    {
        for(auto a = automaton1.alphabet.begin(); a != automaton1.alphabet.end(); ++a)
            W.push_back({*a,&Partition_lan.back()});
    }

    // main loop - while there are splitters
    while(!W.empty())
    {
        splitter = W.front();           // splitter zmenen: misto pointeru na vektor nyni obsahuje hodnotovou kopii vektoru (mazani bloku pozdeji)
        #ifdef MINIMALIZATION_DEBUG
            std::cout << "Splitter print: (" << splitter.first << ", ";
            Print_iter(*splitter.second);
            std::cout << ")" << std::endl;
        #endif // MINIMALIZATION_DEBUG

        // go through all blocks in partition
        for(auto i = Partition_lan.begin(); i != Partition_lan.end(); ++i)
        {
            splits_in = false;
            splits_out = false;
            block1.clear();
            block2.clear();
            // for every state of the block check where do its transitions lead
            // i - block vector, j - state pointer
            for(auto j = i->begin(); j != i->end(); ++j)
            {
                iter = (*j)->transit_states_p.find(splitter.first); // it is DFA so there can be only one transition using one letter
                if(iter != (*j)->transit_states_p.end())            // mozna zbytecne, v DFA musi byt prechod pro kazde pismeno?
                {
                    // check if found transit state is in splitter block
                    // creates blocks B0 and B1 that might split B
                    auto k = splitter.second->begin();
                    for(; k != splitter.second->end(); ++k)
                    {
                        if(iter->second->name == (*k)->name)    // it is in splitter block
                        {
                            splits_in = true;
                            block1.push_back(*j);
                            break;
                        }
                    }
                    if(k == splitter.second->end())             // it is out of splitter block
                    {
                        splits_out = true;
                        block2.push_back(*j);
                    }
                }
                else    // if there is no transition for a letter, split the block (???)
                {
                    splits_out = true;
                    block2.push_back(*j);
                }
            }
            #ifdef MINIMALIZATION_DEBUG
                std::cout << "Two blocks print: " << "(splits_in: " << splits_in << ", splits_out: " << splits_out << ")\n";
                Print_iter(block1);
                Print_iter(block2);
                std::cout << std::endl;
            #endif // MINIMALIZATION_DEBUG

            // if there are transitions to both outside and inside of the splitter (if it actually splits B)
            // -> erase B from partition list -> add B0 and B1
            // pozor pointery!
            if(splits_in && splits_out)
            {
                i = Partition_lan.insert(i, block1);        // insert new block before the old one, i points to the new block
                bl1 = &(*i);                                // remember the pointer to the block
                i = Partition_lan.insert(i, block2);        // insert second new block
                bl2 = &(*i);                                // remember the pointer to the block
                ++i;    // added two elements -> incrementing iterator by two to get back to the old block
                ++i;

                // posledni faze - upravy W
                // for every letter of the alphabet
                for(auto a = automaton1.alphabet.begin(); a != automaton1.alphabet.end(); ++a)
                {
                    // goes through split queue
                    auto split = ++W.begin();       // ignores first element (the already picked one)
                    for(; split != W.end(); ++split)
                    {
                        // if splitter (a,B) exists -> replace it with (a,B0) and (a,B1)
                        if(split->second == &(*i) && *a == split->first)
                        {
                            W.erase(split);     // pro jistotu
                            W.insert(W.end(), {*a,bl1});
                            split = W.insert(W.end(), {*a,bl2});
                            break;
                        }
                    }
                    // if splitter (a,B) does not exist -> insert (a,min{B0,B1})
                    if(split == W.end())
                    {
                        if(bl1->size() < bl2->size()) W.push_back({*a,bl1});
                        else W.push_back({*a,bl2});
                    }
                }
                if(splitter.second == &(*i))    // if a block wants to split itself, it needs to temporarily save itself and redirect pointer
                {
                    missing_block = *i;              // temporary vector of deleted elements (function might delete block that will still be used in the future)
                    splitter.second = &missing_block;// redirect pointer to this variable for the rest of the loop (alphabet)
                }
                i = Partition_lan.erase(i);     // returns iterator pointing to the next element but the for loop will increment again
                --i;                            // therefore i decrement it here
            }
            #ifdef MINIMALIZATION_DEBUG
                std::cout << "Partition print - end:\n";
                Partition_print(Partition_lan);
            #endif // MINIMALIZATION_DEBUG
        }
        W.pop_front();
        #ifdef MINIMALIZATION_DEBUG
            Minim_queue_print(W);
        #endif // MINIMALIZATION_DEBUG
    }
}

// Function implements the Minimalization algorithm. Computes minimal automaton from source automaton.
// input: automaton1 - reference to source automaton, used to compute its minimal version
// input: result_automaton - reference to result automaton, used to store result automaton
// returns: void
void Minimalization_FA(FA &automaton1, FA &result_automaton)
{
    std::list<std::vector<State *>> Partition_lan;
    std::multimap<std::string, std::pair<std::string,State *>> relations;  // UNORDERED?
    State st;
    State * st_p;

    std::vector<State *>::iterator it;
    std::pair<std::multimap<std::string, std::pair<std::string,State *>>::iterator,std::multimap<std::string, std::pair<std::string,State *>>::iterator> it_range;
    std::multimap<std::string, std::pair<std::string,State *>>::iterator range;
    std::multimap<std::string, State *>::iterator seek;

    Hopcroft(automaton1, Partition_lan);
    #ifdef MINIMALIZATION_DEBUG
        std::cout << "\nMINIMALIZATION:-------------------------------------\n";
        Partition_print(Partition_lan);
    #endif // MINIMALIZATION_DEBUG

    // building a new minimal automaton
    result_automaton.alphabet = automaton1.alphabet;
    result_automaton.name = "min-" + automaton1.name;

    // goes through all partitions, creates corresponding state in result_automaton and inserts requests for relations
    for(auto block = Partition_lan.begin(); block != Partition_lan.end(); ++block)
    {
        st.name = "";
        st.start_st = false;
        st.final_st = false;
        result_automaton.states.push_back(st);

        // filling relations
        st_p = &result_automaton.states.back();
        it = block->begin();    // use just the first element in each block since all elements in the same block must have similar relations with blocks

        // for every letter check where the first state points and save (name_of_the_state,{letter,pointer_to_partition_state}) into relations
        for(auto a = result_automaton.alphabet.begin(); a != result_automaton.alphabet.end(); ++a)
        {
            seek = (*it)->transit_states_p.find(*a);
            if(seek != (*it)->transit_states_p.end())
                relations.insert({seek->second->name,{*a,st_p}});
        }

        // setting up the state
        for(auto state = block->begin(); state != block->end(); ++state)
        {
            st_p->name = st_p->name + (*state)->name;
            if((*state)->final_st) st_p->final_st = true;
            if((*state)->start_st) st_p->start_st = true;
        }
        if(st_p->start_st) result_automaton.start_states.push_back(&result_automaton.states.back());
        if(st_p->final_st) result_automaton.final_states.insert(&result_automaton.states.back());
    }

    // goes through all states again and connects name_of_the_state with letter and pointer_to_partition_state
    // partitions correspond to states in result_automaton
    std::list<State>::iterator iter;// = result_automaton.states.begin();
    std::list<std::vector<State *>>::iterator block;// = Partition_lan.begin();
    for(block = Partition_lan.begin(), iter = result_automaton.states.begin(); block != Partition_lan.end() && iter != result_automaton.states.end(); ++block, ++iter)
    {
        for(auto state = block->begin(); state != block->end(); ++state)
        {
            it_range = relations.equal_range((*state)->name);
            for(range = it_range.first; range != it_range.second; ++range)
            {
                // create relations
                range->second.second->transit_states_p.insert({range->second.first,&(*iter)});
                iter->reversed_transit_states_p.insert({range->second.first,range->second.second});
            }
        }
    }
}

// ---------------------------------------- REDUCTION ILIE -----------------------------------------

// Function implements the Simulation relation algorithm. Computes simulation relation of an automaton.
// input: automaton1 - reference to source automaton, used to compute its minimal version
// input: preorder - reference to result preorder, used to store simulation relation
// returns: void
void Preorder(FA &automaton1, std::unordered_set<std::pair<std::string,std::string>, pair_hash> &preorder)
{
    // sim, N(a)ik = card()

    size_t counter = 0;                                     // counts indexes for states
    // basically: int N[alphabet][state][state] = {0}
    std::vector<std::vector<std::vector<int>>> N(automaton1.alphabet.size(),std::vector<std::vector<int>>
                                                (automaton1.states.size(),std::vector<int>
                                                (automaton1.states.size(),0)));
    std::queue<std::pair<State *,State *>> W;               // queue of state pairs
    std::pair<State *,State *> st_pair, st_pair2;           // inserting or removing pairs from W and preord
    std::unordered_set<std::pair<std::string,std::string>, pair_hash> preord;

    std::vector<std::string>::iterator a;      // iterates through alphabet
    std::pair<std::multimap<std::string, State *>::iterator,std::multimap<std::string, State *>::iterator> range1, range2; // for .equal_range()

    // initializing preord and W
    for(auto i = automaton1.states.begin(); i != automaton1.states.end(); ++i)
    {
        // preprocessing --------------------------
        for(a = automaton1.alphabet.begin(); a != automaton1.alphabet.end(); ++a)
        {
            // reversed relations are already computed inside reversed_transit_states_p (multimap)
            // compute cardinality(rel(state,a))
            i->card.insert({*a,i->transit_states_p.count(*a)});     // mozna zbytecne, toto muzu vypocitat i na miste
        }
        i->flag = counter;  // flag contains an index to N array
        ++counter;

        // W initialization -----------------------
        for(auto j = automaton1.states.begin(); j != automaton1.states.end(); ++j)
        {
            if(i->final_st)     // add all pairs Fx(Q-F)
            {
                if(!j->final_st)// i=F, j=(Q-F)
                {
                    st_pair.first = &(*i);
                    st_pair.second = &(*j);
                    preord.insert({st_pair.first->name,st_pair.second->name});
                    W.push(st_pair);
                    continue;
                }
            }
            // {(q,r)| Ea in alphabet: d(q,a)!=0 and d(r,a)==0}
            for(auto a = automaton1.alphabet.begin(); a != automaton1.alphabet.end(); ++a)
            {
                if((i->transit_states_p.count(*a) > 0) && (j->transit_states_p.count(*a) == 0) && preord.find({i->name,j->name}) == preord.end())
                {
                    st_pair.first = &(*i);
                    st_pair.second = &(*j);
                    preord.insert({st_pair.first->name,st_pair.second->name});
                    W.push(st_pair);
                }
            }
        }
    }

    #ifdef REDUCTION_DEBUG
        std::cout << "Reduction - printing preord: ";
        Print_reduct(preord);
    #endif // REDUCTION_DEBUG

    // main loop
    while(!W.empty())
    {
        st_pair = W.front();    // (i,j)

        #ifdef REDUCTION_DEBUG
            std::cout << "Reduction - printing W pair: (" << st_pair.first->name << "," << st_pair.second->name << ")" << std::endl;
        #endif // REDUCTION_DEBUG

        for(a = automaton1.alphabet.begin(); a != automaton1.alphabet.end(); ++a)
        {
            // get rd(j,a)
            range1 = st_pair.second->reversed_transit_states_p.equal_range(*a);
            for(auto k = range1.first; k != range1.second; ++k)
            {
                // N(a)ik <- N(a)ik + 1
                N[a - automaton1.alphabet.begin()][st_pair.first->flag][k->second->flag]++;
                if(N[a - automaton1.alphabet.begin()][st_pair.first->flag][k->second->flag] == k->second->card.find(*a)->second)
                {
                    // get rd(i,a)
                    range2 = st_pair.first->reversed_transit_states_p.equal_range(*a);
                    for(auto l = range2.first; l != range2.second; ++l)
                    {
                        st_pair2.first = l->second;
                        st_pair2.second = k->second;
                        if(preord.find({st_pair2.first->name,st_pair2.second->name}) == preord.end())   // if (l,k) not in preord
                        {
                            preord.insert({st_pair2.first->name,st_pair2.second->name});                // insert (l,k) into preord
                            W.push(st_pair2);                       // insert (l,k) into queue

                            #ifdef REDUCTION_DEBUG
                                std::cout << "Reduction - pushing pair into preord and W: (" << st_pair2.first->name << "," << st_pair2.second->name << ")" << std::endl;
                            #endif // REDUCTION_DEBUG
                        }
                    }
                }
            }
        }
        W.pop();
    }

    preorder.clear(); // clear preorder set
    // converting complement preorder (preord) to preorder (preorder)
    for(auto i = automaton1.states.begin(); i != automaton1.states.end(); ++i)
    {
        for(auto j = automaton1.states.begin(); j != automaton1.states.end(); ++j)
        {
            st_pair.first = &(*i);
            st_pair.second = &(*j);
            if(preord.find({st_pair.first->name,st_pair.second->name}) == preord.end()) preorder.insert({st_pair.first->name,st_pair.second->name});
        }
    }
}

// find a state with specific name in a list of states - help function
State * find_in_states(std::list<State> &states, std::string name)
{
    for(auto temp = states.begin(); temp != states.end(); ++temp)
        if(temp->name == name) return &(*temp);
    return nullptr;
}

// Ilie - NFA reduction
void Reduction_NFA(FA &automaton1)
{
    std::unordered_set<std::pair<std::string,std::string>, pair_hash> preorder_r, preorder_l;
    std::multimap<std::string, State *> swap_tr;
    std::pair<State *,State *> st_pair;
    State *st, *st2;
    std::string st_p1, st_p2;

    std::unordered_set<std::pair<std::string,std::string>, pair_hash>::iterator seek, seek2;
    std::pair<std::multimap<std::string, State *>::iterator,std::multimap<std::string, State *>::iterator> range1;

    // get preorder R
    Preorder(automaton1, preorder_r);

    #ifdef REDUCTION_DEBUG
        std::cout << "Reduction NFA - final r-preord: ";
        Print_reduct(preorder_r);
    #endif // REDUCTION_DEBUG


    // construct a reverse automaton
    for(auto state = automaton1.states.begin(); state != automaton1.states.end(); ++state)
    {
        swap_tr = state->transit_states_p;
        state->transit_states_p = state->reversed_transit_states_p;
        state->reversed_transit_states_p = swap_tr;
        state->card.clear();

        if(state->final_st)
        {
            state->final_st = state->start_st;
            state->start_st = true;
        }
        else if(state->start_st)
        {
            state->start_st = state->final_st;
            state->final_st = true;
        }
    }
    auto help = automaton1.final_states;
    automaton1.final_states.clear();
    for(auto i = automaton1.start_states.begin(); i != automaton1.start_states.end(); ++i)
        automaton1.final_states.insert(*i);

    // get preorder L
    Preorder(automaton1, preorder_l);

    #ifdef REDUCTION_DEBUG
        std::cout << "Reduction NFA - final l-preord: ";
        Print_reduct(preorder_l);
    #endif // REDUCTION_DEBUG

    // construct a reverse automaton
    for(auto state = automaton1.states.begin(); state != automaton1.states.end(); ++state)
    {
        swap_tr = state->transit_states_p;
        state->transit_states_p = state->reversed_transit_states_p;
        state->reversed_transit_states_p = swap_tr;

        if(state->final_st)
        {
            state->final_st = state->start_st;
            state->start_st = true;
        }
        else if(state->start_st)
        {
            state->start_st = state->final_st;
            state->final_st = true;
        }
    }
    automaton1.final_states = help;

    /*
    // converting complement preorder (preord) to preorder (preorder)
    for(auto i = automaton1.states.begin(); i != automaton1.states.end(); ++i)
    {
        for(auto j = automaton1.states.begin(); j != automaton1.states.end(); ++j)
        {
            st_pair.first = &(*i);
            st_pair.second = &(*j);
            if(preord_r.find({st_pair.first->name,st_pair.second->name}) == preord_r.end()) preorder_r.insert({st_pair.first->name,st_pair.second->name});
            if(preord_l.find({st_pair.first->name,st_pair.second->name}) == preord_l.end()) preorder_l.insert({st_pair.first->name,st_pair.second->name});
        }
    }*/
    #ifdef REDUCTION_DEBUG
        std::cout << "Reduction NFA - final r-preorder: ";
        Print_reduct(preorder_r);
        std::cout << "Reduction NFA - final l-preorder: ";
        Print_reduct(preorder_l);
    #endif // REDUCTION_DEBUG

    // 1) p-q, q-p ve stejnem preorderu
    // 2) p-q, p-q v rozdilnych preorderech
    for(auto i = preorder_r.begin(); i != preorder_r.end(); ++i)
    {
        if(i->first == i->second) continue; // (p,p)
        seek = preorder_r.find({i->second,i->first});
        if(seek != preorder_r.end())    // found (p,q) (q,p) duo
        {
            // merging states p and q - transfering relations from p to q
            st = find_in_states(automaton1.states, i->first);
            for(auto j = st->reversed_transit_states_p.begin(); j != st->reversed_transit_states_p.end(); ++j)
            {
                for(auto k = j->second->transit_states_p.begin(); k != j->second->transit_states_p.end(); ++k)
                {
                    if(k->second->name == i->first)
                    {
                        range1 = j->second->transit_states_p.equal_range(k->first);
                        auto r = range1.first;
                        for(; r != range1.second; ++r)
                        {
                            if(r->second->name == i->second) break;
                        }
                        if(r == range1.second) k->second = find_in_states(automaton1.states, i->second);
                        else
                        {
                            k = j->second->transit_states_p.erase(k);
                            --k;
                        }
                    }
                }
            }
            st2 = find_in_states(automaton1.states, i->second);
            for(auto j = st->transit_states_p.begin(); j != st->transit_states_p.end(); ++j)
            {
                range1 = st2->transit_states_p.equal_range(j->first);
                auto r = range1.first;
                for(; r != range1.second; ++r)
                {
                    if(r->second == j->second) break;
                }
                if(r == range1.second) st2->transit_states_p.insert(*j);

                range1 = j->second->reversed_transit_states_p.equal_range(j->first);
                for(auto r = range1.first; r != range1.second; ++r)
                {
                    if(r->second == st) r->second = st2;
                }
            }
            st->transit_states_p.clear();

            // removing pairs from both preorders according to Ilie algorithm
            st_p1 = i->first;
            st_p2 = i->second;
            for(auto j = automaton1.states.begin(); j != automaton1.states.end(); ++j)
            {
                seek2 = preorder_r.find({st_p2,j->name});
                if(seek2 != preorder_r.end())
                {
                    if(preorder_r.find({st_p1,j->name}) == preorder_r.end())
                        preorder_r.erase(seek2);
                }
                seek2 = preorder_l.find({st_p2,j->name});
                if(seek2 != preorder_l.end())
                {
                    if(preorder_l.find({st_p1,j->name}) == preorder_l.end())
                        preorder_l.erase(seek2);
                }
            }
            // erasing (p,q) and (q,p) pairs from preorder_r
            seek2 = preorder_r.find({st_p1,st_p2});
            if(seek2 != preorder_r.end()) preorder_r.erase(seek2);
            seek2 = preorder_r.find({st_p2,st_p1});
            if(seek2 != preorder_r.end()) preorder_r.erase(seek2);

            // erasing all pairs that contain deleted state p from both preorders
            for(auto x = preorder_r.begin();x != preorder_r.end();)
            {
                if(x->first == st_p1 || x->second == st_p1)
                {
                    x = preorder_r.erase(x);
                }
                else ++x;
            }
            for(auto x = preorder_l.begin();x != preorder_l.end();)
            {
                if(x->first == st_p1 || x->second == st_p1)
                {
                    x = preorder_l.erase(x);
                }
                else ++x;
            }

            //Print_reduct(preorder_r);
            for(auto temp = automaton1.states.begin(); temp != automaton1.states.end(); ++temp)
                if(temp->name == st_p1) { temp->flag = -1; break; }     // mark the state for removal
        }
    }
    // --------------------------------------------------
    for(auto i = preorder_l.begin(); i != preorder_l.end(); ++i)
    {
        if(i->first == i->second) continue; // (p,p)
        seek = preorder_l.find({i->second,i->first});
        if(seek != preorder_l.end())    // found (p,q) (q,p) duo
        {
            // merging states p and q - transfering relations from p to q
            st = find_in_states(automaton1.states, i->first);
            for(auto j = st->reversed_transit_states_p.begin(); j != st->reversed_transit_states_p.end(); ++j)
            {
                for(auto k = j->second->transit_states_p.begin(); k != j->second->transit_states_p.end(); ++k)
                {
                    if(k->second->name == i->first)
                    {
                        range1 = j->second->transit_states_p.equal_range(k->first);
                        auto r = range1.first;
                        for(; r != range1.second; ++r)
                        {
                            if(r->second->name == i->second) break;
                        }
                        if(r == range1.second) k->second = find_in_states(automaton1.states, i->second);
                        else
                        {
                            k = j->second->transit_states_p.erase(k);
                            --k;
                        }
                    }
                }
            }
            st2 = find_in_states(automaton1.states, i->second);
            for(auto j = st->transit_states_p.begin(); j != st->transit_states_p.end(); ++j)
            {
                range1 = st2->transit_states_p.equal_range(j->first);
                auto r = range1.first;
                for(; r != range1.second; ++r)
                {
                    if(r->second == j->second) break;
                }
                if(r == range1.second) st2->transit_states_p.insert(*j);

                range1 = j->second->reversed_transit_states_p.equal_range(j->first);
                for(auto r = range1.first; r != range1.second; ++r)
                {
                    if(r->second == st) r->second = st2;
                }
            }
            st->transit_states_p.clear();

            // removing pairs from both preorders according to Ilie algorithm
            st_p1 = i->first;
            st_p2 = i->second;
            for(auto j = automaton1.states.begin(); j != automaton1.states.end(); ++j)
            {
                seek2 = preorder_l.find({st_p2,j->name});
                if(seek2 != preorder_l.end())
                {
                    if(preorder_l.find({st_p1,j->name}) == preorder_l.end())
                        preorder_l.erase(seek2);
                }
                seek2 = preorder_r.find({st_p2,j->name});
                if(seek2 != preorder_r.end())
                {
                    if(preorder_r.find({st_p1,j->name}) == preorder_r.end())
                        preorder_r.erase(seek2);
                }
            }
            // erasing (p,q) and (q,p) pairs from preorder_l
            seek2 = preorder_l.find({st_p1,st_p2});
            if(seek2 != preorder_l.end()) preorder_l.erase(seek2);
            seek2 = preorder_l.find({st_p2,st_p1});
            if(seek2 != preorder_l.end()) preorder_l.erase(seek2);

            // erasing all pairs that contain deleted state p from both preorders
            for(auto x = preorder_l.begin();x != preorder_l.end();)
            {
                if(x->first == st_p1 || x->second == st_p1)
                {
                    x = preorder_l.erase(x);
                }
                else ++x;
            }
            for(auto x = preorder_r.begin();x != preorder_r.end();)
            {
                if(x->first == st_p1 || x->second == st_p1)
                {
                    x = preorder_r.erase(x);
                }
                else ++x;
            }

            //Print_reduct(preorder_l);
            for(auto temp = automaton1.states.begin(); temp != automaton1.states.end(); ++temp)
                if(temp->name == st_p1) { temp->flag = -1; break; }     // mark the state for removal
        }
    }
    // ----------------------------------------------
    for(auto i = preorder_r.begin(); i != preorder_r.end(); ++i)
    {
        if(i->first == i->second) continue; // (p,p)
        seek = preorder_l.find({i->first,i->second});
        if(seek != preorder_l.end())    // found (p,q) (p,q) duo
        {
            // merging states p and q - transfering relations from p to q
            st = find_in_states(automaton1.states, i->first);
            for(auto j = st->reversed_transit_states_p.begin(); j != st->reversed_transit_states_p.end(); ++j)
            {
                for(auto k = j->second->transit_states_p.begin(); k != j->second->transit_states_p.end(); ++k)
                {
                    if(k->second->name == i->first)
                    {
                        range1 = j->second->transit_states_p.equal_range(k->first);
                        auto r = range1.first;
                        for(; r != range1.second; ++r)
                        {
                            if(r->second->name == i->second) break;
                        }
                        if(r == range1.second) k->second = find_in_states(automaton1.states, i->second);
                        else
                        {
                            k = j->second->transit_states_p.erase(k);
                            --k;
                        }
                    }
                }
            }
            st2 = find_in_states(automaton1.states, i->second);
            for(auto j = st->transit_states_p.begin(); j != st->transit_states_p.end(); ++j)
            {
                range1 = st2->transit_states_p.equal_range(j->first);
                auto r = range1.first;
                for(; r != range1.second; ++r)
                {
                    if(r->second == j->second) break;
                }
                if(r == range1.second) st2->transit_states_p.insert(*j);

                range1 = j->second->reversed_transit_states_p.equal_range(j->first);
                for(auto r = range1.first; r != range1.second; ++r)
                {
                    if(r->second == st) r->second = st2;
                }
            }
            st->transit_states_p.clear();

            st_p1 = i->first;
            st_p2 = i->second;

            // erasing (p,q) from preorder_r and preorder_l
            preorder_r.erase(preorder_r.find({st_p1,st_p2}));
            preorder_l.erase(preorder_l.find({st_p1,st_p2}));

            for(auto temp = automaton1.states.begin(); temp != automaton1.states.end(); ++temp)
                if(temp->name == st_p1) { temp->flag = -1; break; }     // mark the state for removal
        }
    }
    // remove states - preorder function sets flag to some positive number, only states set to -1 by this function can have flag -1
    //Restore_FA(automaton1, 1);
}

// --------------------------- UNIVERSALITY AND INCLUSION ----------------------

// Function iterates (i,j are iterators) through macro state and if there is (i,j) pair in preorder, it deletes i from macro state. Implements second optimization.
// input: macro_R - reference to source macro state
// input: preorder - reference to simulation relation
// returns: void
void Minimize(Macro_state &macro_R, std::unordered_set<std::pair<std::string,std::string>, pair_hash> &preorder)
{
    for(auto i = macro_R.states.begin(); i != macro_R.states.end(); ++i)
    {
        for(auto j = macro_R.states.begin(); j != macro_R.states.end(); ++j)
        {
            if(i == j) continue;        // identity cannot remove state
            if(preorder.find({(*i)->name,(*j)->name}) != preorder.end())  // if there is a pair (i,j) in preorder
            {
                i = --macro_R.states.erase(i); // remove i (because i is simulated by j)
                break;
            }
        }
    }
}

// Function checks if first macro state (macroSubs) is subset of second macro state (macroSuper).
// For every state sub_st in first macro state there must be state super_st in second macro state such that (sub_st, super_st) are in preorder.
// input: macroSubs - reference to first macro state
// input: macroSuper - reference to second macro state
// input: preorder - reference to simulation relation
// returns: True if macroSubs is subset of macroSuper, false otherwise.
bool Is_subset(Macro_state &macroSubs, Macro_state &macroSuper, std::unordered_set<std::pair<std::string,std::string>, pair_hash> &preorder)
{
    // for every state of subset
    for(auto sub_st = macroSubs.states.begin(); sub_st != macroSubs.states.end(); ++sub_st)
    {
        // there must be a state in superset
        auto super_st = macroSuper.states.begin();
        for(; super_st != macroSuper.states.end(); ++super_st)
        {
            // such that sub_st <= super_st in preorder
            if(preorder.find({(*sub_st)->name,(*super_st)->name}) != preorder.end()) break;
        }
        if(super_st == macroSuper.states.end()) return false;
    }
    return true;
}

// Function implements the Universality algorithm.
// input: automaton1 - reference to source automaton
// input: preorder - reference to simulation relation
// returns: True if automaton is universal, false if automaton is not universal
bool Universality_NFA(FA &automaton1, std::unordered_set<std::pair<std::string,std::string>, pair_hash> &preorder)
{
    Macro_state macro_R, macro_P;               // macro states R and P
    std::vector<Macro_state> processed, next;   // processed and next vectors
    std::unordered_set<std::string> redundant;  // used to prevent redundancy of states when creating new macro states
    bool exists_S;                              // used to check if S exists

    std::vector<Macro_state>::iterator macro_S; // macro state S
    std::pair<std::multimap<std::string, State *>::iterator,std::multimap<std::string, State *>::iterator> range1;    // .equal_range()

    // if a macro state of start states is rejecting -> automaton does not recognise empty string (epsilon) as a part of the language
    // -> language is not universal
    macro_R.states = automaton1.start_states;
    macro_R.rejecting = true;
    for(auto state = macro_R.states.begin(); state != macro_R.states.end(); ++state)
    {
        if((*state)->final_st) { macro_R.rejecting = false; break; }
    }
    if(macro_R.rejecting) return false;

    // next = {Minimize(I)};
    Minimize(macro_R, preorder);
    next.push_back(macro_R);

    // main loop
    while(!next.empty())
    {
        macro_R = next.back();
        next.pop_back();
        processed.push_back(macro_R);

        #ifdef UNIVERSALITY_DEBUG
            std::cout << "Universality - printing current macro state: ";
            Print_MacroState(macro_R);
        #endif // UNIVERSALITY_DEBUG

        // get adjacent macro states
        for(auto a = automaton1.alphabet.begin(); a != automaton1.alphabet.end(); ++a)
        {
            // getting Post(R) for specific letter *a
            redundant.clear();
            macro_P.states.clear();
            macro_P.rejecting = true;
            for(auto state = macro_R.states.begin(); state != macro_R.states.end(); ++state)
            {
                range1 = (*state)->transit_states_p.equal_range(*a);
                for(auto next_st = range1.first; next_st != range1.second; ++next_st)
                {
                    if(redundant.insert(next_st->second->name).second)  // does not push redundant states - fast searching
                    {
                        macro_P.states.push_back(next_st->second);
                        if(next_st->second->final_st) macro_P.rejecting = false;    // sets the rejecting flag
                    }
                }
            }
            #ifdef UNIVERSALITY_DEBUG
                std::cout << "\tUniversality - printing new macro state (" << *a << ") before minimalization:\n\t\t";
                Print_MacroState(macro_P);
            #endif // UNIVERSALITY_DEBUG

            Minimize(macro_P, preorder);

            #ifdef UNIVERSALITY_DEBUG
                std::cout << "\tUniversality - printing new macro state (" << *a << ") after minimalization:\n\t\t";
                Print_MacroState(macro_P);
            #endif // UNIVERSALITY_DEBUG

            if(macro_P.rejecting) return false;

            // search in processed for S such that S <= P
            exists_S = false;
            for(macro_S = processed.begin(); macro_S != processed.end();)
            {
                if(Is_subset(*macro_S, macro_P, preorder)) { exists_S = true; break; }

                // remove all S from processed such that P <= S
                if(Is_subset(macro_P, *macro_S, preorder))
                    macro_S = processed.erase(macro_S);
                else ++macro_S;
            }
            if(!exists_S)   // if not found yet
            {
                // search in next for S such that S <= P
                for(macro_S = next.begin(); macro_S != next.end();)
                {
                    if(Is_subset(*macro_S, macro_P, preorder)) { exists_S = true; break; }

                    // remove all S from next such that P <= S
                    if(Is_subset(macro_P, *macro_S, preorder))
                        macro_S = next.erase(macro_S);
                    else ++macro_S;
                }
            }
            // if no such S was found
            if(!exists_S)
            {
                // add P to next
                next.push_back(macro_P);
                #ifdef UNIVERSALITY_DEBUG
                    std::cout << "\tUniversality - pushing (into next) macro state ";
                    Print_MacroState(macro_P);
                #endif // UNIVERSALITY_DEBUG
            }
        }
    }
    return true;
}

// Function implements the Inclusion algorithm. Checks if L(automaton1) is subset of L(automaton2).
// input: automaton1 - reference to first automaton
// input: automaton2 - reference to second automaton
// input: preorder - reference to simulation relation of (automaton1 union automaton2)
// returns: True if L(automaton1) is subset of L(automaton2), false otherwise.
bool Inclusion_NFA(FA &automaton1, FA &automaton2, std::unordered_set<std::pair<std::string,std::string>, pair_hash> &preorder)
{
    Product_state prod_st1, prod_st2;
    Macro_state macro_R, macro_P;               // macro states R and P
    std::vector<Product_state> processed, next; // processed and next vectors
    std::unordered_set<std::string> redundant;  // used to prevent redundancy of states when creating new macro states
    bool exists_S;                              // used to check if S exists

    std::vector<Product_state>::iterator prod_S; // product state S
    std::pair<std::multimap<std::string, State *>::iterator,std::multimap<std::string, State *>::iterator> range1, range2;    // .equal_range()

    // algorithm is meant for automatons with same alphabets!!!
    // following code picks a smaller alphabet (that will be used for computation) - error prevention
    std::vector<std::string> alphabet;
    if(automaton1.alphabet.size() < automaton2.alphabet.size())
        alphabet = automaton1.alphabet;
    else
        alphabet = automaton2.alphabet;
    //if(automaton1.alphabet != automaton2.alphabet) {throw "Inclusion: alphabets are different!";}

    // if a product state of p and start states is accepting -> automaton1 overlaps with complement of automaton2
    // -> L(automaton1) (not)<= L(automaton2)
    prod_st1.macro_st.states = automaton2.start_states;
    prod_st1.macro_st.rejecting = true;
    for(auto state = prod_st1.macro_st.states.begin(); state != prod_st1.macro_st.states.end(); ++state)
    {
        if((*state)->final_st) { prod_st1.macro_st.rejecting = false; break; }  // compute if macro state is rejecting
    }

    prod_st1.rejecting = true;              // if program does not end, product state must be rejecting for every start state from automaton1
    Minimize(prod_st1.macro_st, preorder);  // minimize the macro state for initialization

    for(auto a1_state = automaton1.start_states.begin(); a1_state != automaton1.start_states.end(); ++a1_state)
    {
        if((*a1_state)->final_st && prod_st1.macro_st.rejecting) return false;  // if q from (q,I) is accepting and I is not accepting, return false
        prod_st1.a1_st = *a1_state;
        next.push_back(prod_st1);   // push product_state to next, later apply initialization
    }

    // initialize(next) part
    for(auto p_state = next.begin(); p_state != next.end();)
    {
        // initialize(): condition (2)
        auto m_state = p_state->macro_st.states.begin();
        for(; m_state != p_state->macro_st.states.end(); ++m_state)
            if(preorder.find({p_state->a1_st->name,(*m_state)->name}) != preorder.end()) break;   // found

        if(m_state != p_state->macro_st.states.end())   // pair p<=q from (p,Q), q in Q, was found in preorder
        {
            p_state = next.erase(p_state);  // delete product state from next
            continue;
        }

        // initialize(): condition (1)
        for(auto p_state_2 = next.begin(); p_state_2 != next.end(); ++p_state_2)
        {
            if(p_state == p_state_2) continue;  // do not compare same elements
            // (p,P),(q,Q) from next:               p <= q                           &&                         Q <= P
            if( (preorder.find({p_state->a1_st->name,p_state_2->a1_st->name}) != preorder.end()) && Is_subset(p_state_2->macro_st, p_state->macro_st, preorder) )
            {
                p_state = next.erase(p_state);  // delete product state from next
                --p_state;
                break;
            }
        }
        ++p_state;
    }

    // main loop
    while(!next.empty())
    {
        prod_st1 = next.back();
        next.pop_back();
        processed.push_back(prod_st1);

        #ifdef INCLUSION_DEBUG
            std::cout << "Inclusion - printing current product state: " << prod_st1.a1_st->name << ",";
            Print_MacroState(prod_st1.macro_st);
        #endif // INCLUSION_DEBUG

        // get adjacent product states - for all a in alphabet
        for(auto a = alphabet.begin(); a != alphabet.end(); ++a)
        {
            // getting Post(R) for specific letter *a
            redundant.clear();
            prod_st2.macro_st.states.clear();
            prod_st2.macro_st.rejecting = true;
            for(auto state = prod_st1.macro_st.states.begin(); state != prod_st1.macro_st.states.end(); ++state)
            {
                range1 = (*state)->transit_states_p.equal_range(*a);
                for(auto next_st = range1.first; next_st != range1.second; ++next_st)
                {
                    if(redundant.insert(next_st->second->name).second)  // does not push redundant states - fast searching
                    {
                        prod_st2.macro_st.states.push_back(next_st->second);
                        if(next_st->second->final_st) prod_st2.macro_st.rejecting = false;    // sets the rejecting flag
                    }
                }
            }

            #ifdef INCLUSION_DEBUG
                std::cout << "\tInclusion - printing new macro state (" << *a << ") before minimalization:\n\t\t";
                Print_MacroState(prod_st2.macro_st);
            #endif // INCLUSION_DEBUG

            Minimize(prod_st2.macro_st, preorder);  // optimization 1(a), mozny problem - rejecting kontroluju pred minimalizaci a ne az po

            #ifdef INCLUSION_DEBUG
                std::cout << "\tInclusion - printing new macro state (" << *a << ") after minimalization:\n\t\t";
                Print_MacroState(prod_st2.macro_st);
            #endif // INCLUSION_DEBUG

            // for all Post(r) for specific letter *a and macro state Post(R)
            range2 = prod_st1.a1_st->transit_states_p.equal_range(*a);
            for(auto next_a1_st = range2.first; next_a1_st != range2.second; ++next_a1_st)
            {
                prod_st2.a1_st = next_a1_st->second;
                if(next_a1_st->second->final_st && prod_st2.macro_st.rejecting) return false;
                //else prod_st2.rejecting = true;
                // optimization 1(b)
                auto p = prod_st2.macro_st.states.begin();
                for(; p != prod_st2.macro_st.states.end(); ++p)
                {
                    if(preorder.find({prod_st2.a1_st->name,(*p)->name}) != preorder.end()) break;
                }
                if(p == prod_st2.macro_st.states.end())    // optimization 2
                {
                    // search in processed for (s,S) such that p <= s && S <= P
                    exists_S = false;
                    for(prod_S = processed.begin(); prod_S != processed.end(); ++prod_S)
                    {
                        if( (preorder.find({prod_st2.a1_st->name,prod_S->a1_st->name}) != preorder.end()) &&
                            Is_subset(prod_S->macro_st, prod_st2.macro_st, preorder) )
                        { exists_S = true; break; }
                    }
                    if(!exists_S)   // if not found yet
                    {
                        // search in next for (s,S) such that p <= s && S <= P
                        for(prod_S = next.begin(); prod_S != next.end(); ++prod_S)
                        {
                            if( (preorder.find({prod_st2.a1_st->name,prod_S->a1_st->name}) != preorder.end()) &&
                                 Is_subset(prod_S->macro_st, prod_st2.macro_st, preorder) )
                            { exists_S = true; break; }
                        }
                    }
                    // if no such (s,S) was found
                    if(!exists_S)
                    {
                        // remove all (s,S) from processed such that s <= p && P <= S
                        for(prod_S = processed.begin(); prod_S != processed.end();)
                        {
                            if( (preorder.find({prod_S->a1_st->name,prod_st2.a1_st->name}) != preorder.end()) &&
                                 Is_subset(prod_st2.macro_st, prod_S->macro_st, preorder))
                                prod_S = processed.erase(prod_S);
                            else ++prod_S;
                        }
                        // remove all (s,S) from next such that s <= p && P <= S
                        for(prod_S = next.begin(); prod_S != next.end();)
                        {
                            if( (preorder.find({prod_S->a1_st->name,prod_st2.a1_st->name}) != preorder.end()) &&
                                 Is_subset(prod_st2.macro_st, prod_S->macro_st, preorder))
                                prod_S = next.erase(prod_S);
                            else ++prod_S;
                        }
                        // add (p,P) to next
                        next.push_back(prod_st2);
                        #ifdef INCLUSION_DEBUG
                            std::cout << "\tInclusion - pushing (into next) product state " << prod_st2.a1_st->name << ",";
                            Print_MacroState(prod_st2.macro_st);
                        #endif // INCLUSION_DEBUG
                    }
                }
            }
        }
    }
    return true;
}

// ---------------------------------------- ADDITIONAL FUNCTIONS -----------------------------------------

// Function generates the identity relation from states of automaton. It can be used for special versions of universality and inclusion checking.
// input: automaton - reference to source automaton
// input: preorder - reference to result identity relation
// returns: void
void Get_identity_relation(FA &automaton, std::unordered_set<std::pair<std::string,std::string>, pair_hash> &preorder)
{
    for(auto state = automaton.states.begin(); state != automaton.states.end(); ++state)
        preorder.insert({state->name,state->name});
}

// Function implements the Union algorithm. Computes automaton1 union automaton2.
// input: automaton1 - reference to first automaton
// input: automaton2 - reference to second automaton
// input: result_automaton - reference to result automaton, used to save result
// returns: void
void Union_FA(FA &automaton1, FA &automaton2, FA &result_automaton)
{
    std::multimap<std::string, std::pair<std::string,State *>> relations;
    std::unordered_set<std::string> opt_s;
    State st;
    State * st_p;

    //std::vector<State *>::iterator it;
    std::pair<std::multimap<std::string, std::pair<std::string,State *>>::iterator,std::multimap<std::string, std::pair<std::string,State *>>::iterator> it_range;
    std::multimap<std::string, std::pair<std::string,State *>>::iterator range;
    std::pair<std::multimap<std::string, State *>::iterator, std::multimap<std::string, State *>::iterator> seek;

    //if(automaton1.alphabet != automaton2.alphabet) {throw "Union: alphabets are different!";}
    if(automaton1.alphabet.size() > automaton2.alphabet.size())
        result_automaton.alphabet = automaton1.alphabet;
    else
        result_automaton.alphabet = automaton2.alphabet;

    // building a new automaton that will be returned
    result_automaton.name = automaton1.name + "+" + automaton2.name;

    // goes through all states of first automaton, creates corresponding state in result_automaton and inserts requests for relations
    for(auto s = automaton1.states.begin(); s != automaton1.states.end(); ++s)
    {
        st.name = s->name;
        opt_s.insert(st.name);
        st.start_st = s->start_st;
        st.final_st = s->final_st;
        st.flag = 0;
        st.visited = false;
        result_automaton.states.push_back(st);

        // filling relations
        st_p = &result_automaton.states.back();

        // for every letter check where the state points and save (name_of_the_state,{letter,pointer_to_state}) into relations
        for(auto a = result_automaton.alphabet.begin(); a != result_automaton.alphabet.end(); ++a)
        {
            seek = s->transit_states_p.equal_range(*a);
            for(auto targ_state = seek.first; targ_state != seek.second; ++targ_state)
            {
                relations.insert({targ_state->second->name,{*a,st_p}});
            }
        }
        if(st_p->start_st) result_automaton.start_states.push_back(&result_automaton.states.back());
        if(st_p->final_st) result_automaton.final_states.insert(&result_automaton.states.back());
    }
    // goes through all states of second automaton, creates corresponding state in result_automaton and inserts requests for relations
    for(auto s = automaton2.states.begin(); s != automaton2.states.end(); ++s)
    {
        if(opt_s.find(s->name) == opt_s.end())
            st.name = s->name;
        else
        {
            st.name = s->name + "_copy";
        }
        st.start_st = s->start_st;
        st.final_st = s->final_st;
        result_automaton.states.push_back(st);

        // filling relations
        st_p = &result_automaton.states.back();

        // for every letter check where the state points and save (name_of_the_state,{letter,pointer_to_state}) into relations
        for(auto a = result_automaton.alphabet.begin(); a != result_automaton.alphabet.end(); ++a)
        {
            seek = s->transit_states_p.equal_range(*a);
            for(auto targ_state = seek.first; targ_state != seek.second; ++targ_state)
            {
                if(opt_s.find(targ_state->second->name) == opt_s.end())
                    relations.insert({targ_state->second->name,{*a,st_p}});
                else
                    relations.insert({targ_state->second->name + "_copy",{*a,st_p}});
            }
        }
        if(st_p->start_st) result_automaton.start_states.push_back(&result_automaton.states.back());
        if(st_p->final_st) result_automaton.final_states.insert(&result_automaton.states.back());
    }

    // goes through all states again and connects name_of_the_state with letter and pointer_to_state
    for(auto s = result_automaton.states.begin(); s != result_automaton.states.end(); ++s)
    {
        it_range = relations.equal_range(s->name);
        for(range = it_range.first; range != it_range.second; ++range)
        {
            // create relations
            range->second.second->transit_states_p.insert({range->second.first,&(*s)});
            s->reversed_transit_states_p.insert({range->second.first,range->second.second});
        }
    }
    for(auto s = automaton2.states.begin(); s != automaton2.states.end(); ++s)
    {
        if(opt_s.find(s->name) != opt_s.end()) s->name = s->name + "_copy";
    }
}

// Function implements Copy algorithm. Creates a copy of source automaton.
// input: automaton1 - reference to source automaton
// returns: A copy of a source automaton.
FA Copy_FA(FA &automaton1)
{
    FA result_automaton;
    std::multimap<std::string, std::pair<std::string,State *>> relations;
    State st;
    State * st_p;

    std::pair<std::multimap<std::string, std::pair<std::string,State *>>::iterator,std::multimap<std::string, std::pair<std::string,State *>>::iterator> it_range;
    std::multimap<std::string, std::pair<std::string,State *>>::iterator range;
    std::pair<std::multimap<std::string, State *>::iterator, std::multimap<std::string, State *>::iterator> seek;

    // building a new automaton that will be returned
    result_automaton.name = automaton1.name;
    result_automaton.alphabet = automaton1.alphabet;

    // goes through all states of first automaton, creates corresponding state in result_automaton and inserts requests for relations
    for(auto s = automaton1.states.begin(); s != automaton1.states.end(); ++s)
    {
        st.name = s->name;
        st.start_st = s->start_st;
        st.final_st = s->final_st;
        st.flag = 0;
        st.visited = false;
        result_automaton.states.push_back(st);

        // filling relations
        st_p = &result_automaton.states.back();

        // for every letter check where the state points and save (name_of_the_state,{letter,pointer_to_state}) into relations
        for(auto a = result_automaton.alphabet.begin(); a != result_automaton.alphabet.end(); ++a)
        {
            seek = s->transit_states_p.equal_range(*a);
            for(auto targ_state = seek.first; targ_state != seek.second; ++targ_state)
            {
                relations.insert({targ_state->second->name,{*a,st_p}});
            }
        }
        if(st_p->start_st) result_automaton.start_states.push_back(&result_automaton.states.back());
        if(st_p->final_st) result_automaton.final_states.insert(&result_automaton.states.back());
    }

    // goes through all states again and connects name_of_the_state with letter and pointer_to_state
    for(auto s = result_automaton.states.begin(); s != result_automaton.states.end(); ++s)
    {
        it_range = relations.equal_range(s->name);
        for(range = it_range.first; range != it_range.second; ++range)
        {
            // create relations
            range->second.second->transit_states_p.insert({range->second.first,&(*s)});
            s->reversed_transit_states_p.insert({range->second.first,range->second.second});
        }
    }
    return result_automaton;
}

// Function creates a complement of a source automaton. It does not create a new automaton.
// input: automaton1 - reference to source automaton
// returns: void
void Complement_FA(FA &automaton1)
{
    automaton1.final_states.clear();
    for(auto state = automaton1.states.begin(); state != automaton1.states.end(); ++state)
    {
        state->final_st = !state->final_st;
        if(state->final_st) automaton1.final_states.insert(&(*state));
    }
}

// ---------------------------------------- MAIN FUNCTION -----------------------------------------

// main function - used to parse arguments and call appropriate algorithms
int main(int argc, char *argv[])
{
    // program wants one argument
    if(argc != 2) { std::cout << "Wrong arguments (use: -e | -n | -p | -d | -m | -s | -u | -ui | -i | -ii | -o | -x)" << std::endl; return 3; }

    std::vector<FA> automatons;
    FA result_automaton;
    FA result_automaton2;
    std::unordered_set<std::pair<std::string,std::string>, pair_hash> preorder;

    // parse and print automatons -------------------------
    try
    {
        parse_FA_stdin(automatons);
    }
    catch(const char *msg)
    {
        std::cerr << msg << std::endl;
        return 1;
    }
    #ifdef MAIN_DEBUG
        print_FA(automatons);
    #endif

    long number_of_states = 0;
    long number_of_transitions = 0;
    for(auto autom = automatons.begin(); autom != automatons.end(); ++autom)
    {
        number_of_states += autom->states.size();
        for(auto j = autom->states.begin(); j != autom->states.end(); ++j)
        {
            number_of_transitions += j->transit_states_p.size();
        }
    }
    //int measurement_const = 49;       // number of measurements - 1
    long counter = 0;       // counts the number of algorithm completions performed during measuring
    int length_ms = 500;    // how long should the measurement last

    // parse arguments ------------------------------------
    std::string str;
    str = argv[1];
    if(str == "-e")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- EMPTINESS -------------------------\n";

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            Emptiness_test(automatons[0]);
            ++counter;
        }
        bool return_value = Emptiness_test(automatons[0]);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        if(return_value) std::cout << "Automaton is empty!" << std::endl;
        else std::cout << "Automaton is not empty!" << std::endl;
    }
    else if(str == "-n")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- REMOVE USELESS STATES -------------------------\n";
        FA result_automaton2;
        result_automaton2 = Copy_FA(automatons[0]);

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            Remove_useless_states(automatons[0]);
            automatons[0] = Copy_FA(result_automaton2);
            ++counter;
        }
        Remove_useless_states(automatons[0]);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        Print_result_FA(automatons[0]);
    }
    else if(str == "-p")
    {
        if(automatons.size() < 2) { std::cout << "The algorithm requires two automatons from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- PRODUCT (INTERSECTION) -------------------------\n";
        try
        {
            auto startsw = std::chrono::high_resolution_clock::now();
            std::clock_t startCPUtime = std::clock();
            std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
            while(std::clock() < whenEnd)
            {
                FA result_automaton;
                Intersection_FA(automatons[0], automatons[1], result_automaton);
                ++counter;
            }
            Intersection_FA(automatons[0], automatons[1], result_automaton);
            std::clock_t endCPUtime = std::clock();
            auto endsw = std::chrono::high_resolution_clock::now();
            long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
            long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

            std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

            Print_result_FA(result_automaton);
        }
        catch(const char *msg)
        {
            std::cerr << msg << std::endl;
            return 2;
        }
    }
    else if(str == "-d")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- DETERMINIZATION -------------------------\n";

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            FA result_automaton;
            Determinization_FA(automatons[0], result_automaton);
            ++counter;
        }
        Determinization_FA(automatons[0], result_automaton);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        Print_result_FA(result_automaton);
    }
    else if(str == "-m")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- MINIMALIZATION -------------------------\n";
        Determinization_FA(automatons[0], result_automaton2);

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            FA result_automaton;
            Minimalization_FA(result_automaton2, result_automaton);
            ++counter;
        }
        Minimalization_FA(result_automaton2, result_automaton);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        Print_result_FA(result_automaton);
    }
    else if(str == "-s")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- SIMULATION RELATION -------------------------\n";

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            std::unordered_set<std::pair<std::string,std::string>, pair_hash> preorder;
            Preorder(automatons[0], preorder);
            ++counter;
        }
        Preorder(automatons[0], preorder);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        Print_reduct(preorder);
    }
    else if(str == "-r")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- REDUCTION -------------------------\n";

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        Reduction_NFA(automatons[0]);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " cpu: " << std::fixed << std::setprecision(6) << CPUduration << " wall: " << duration << std::endl << std::endl;

        Print_result_FA(automatons[0]);
    }
    else if(str == "-u")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- UNIVERSALITY -------------------------\n";
        Preorder(automatons[0], preorder);

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            Universality_NFA(automatons[0], preorder);
            ++counter;
        }
        bool result_variable = Universality_NFA(automatons[0], preorder);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        if(result_variable) std::cout << "Automaton is universal!" << std::endl;
        else std::cout << "Automaton is not universal!" << std::endl;
    }
    else if(str == "-ui")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- UNIVERSALITY IDENTITY -------------------------\n";
        Get_identity_relation(automatons[0], preorder);
        //Print_reduct(preorder);

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            Universality_NFA(automatons[0], preorder);
            ++counter;
        }
        bool result_variable = Universality_NFA(automatons[0], preorder);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        if(result_variable) std::cout << "Automaton is universal!" << std::endl;
        else std::cout << "Automaton is not universal!" << std::endl;
    }
    else if(str == "-uc")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- UNIVERSALITY COMPLEMENT -------------------------\n";
        Complement_FA(automatons[0]);
        Preorder(automatons[0], preorder);

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            Universality_NFA(automatons[0], preorder);
            ++counter;
        }
        bool result_variable = Universality_NFA(automatons[0], preorder);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        if(result_variable) std::cout << "Automaton is universal!" << std::endl;
        else std::cout << "Automaton is not universal!" << std::endl;
    }
    else if(str == "-uic")
    {
        if(automatons.size() < 1) { std::cout << "The algorithm requires one automaton from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- UNIVERSALITY IDENTITY COMPLEMENT -------------------------\n";
        Complement_FA(automatons[0]);
        Get_identity_relation(automatons[0], preorder);
        //Print_reduct(preorder);

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            Universality_NFA(automatons[0], preorder);
            ++counter;
        }
        bool result_variable = Universality_NFA(automatons[0], preorder);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        if(result_variable) std::cout << "Automaton is universal!" << std::endl;
        else std::cout << "Automaton is not universal!" << std::endl;
    }
    else if(str == "-i")
    {
        if(automatons.size() < 2) { std::cout << "The algorithm requires two automatons from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- INCLUSION -------------------------\n";
        try
        {
            Union_FA(automatons[0], automatons[1], result_automaton);
            Preorder(result_automaton, preorder);

            auto startsw = std::chrono::high_resolution_clock::now();
            std::clock_t startCPUtime = std::clock();
            std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
            while(std::clock() < whenEnd)
            {
                Inclusion_NFA(automatons[0], automatons[1], preorder);
                ++counter;
            }
            bool result_variable = Inclusion_NFA(automatons[0], automatons[1], preorder);
            std::clock_t endCPUtime = std::clock();
            auto endsw = std::chrono::high_resolution_clock::now();
            long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
            long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

            std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

            if(result_variable) std::cout << "Automaton inclusion A <= B is true! (A - first, B - second automaton)" << std::endl;
            else std::cout << "Automaton inclusion A <= B is not true! (A - first, B - second automaton)" << std::endl;
        }
        catch(const char *msg)
        {
            std::cerr << msg << std::endl;
            return 2;
        }
    }
    else if(str == "-ii")
    {
        if(automatons.size() < 2) { std::cout << "The algorithm requires two automatons from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- INCLUSION IDENTITY -------------------------\n";
        try
        {
            Union_FA(automatons[0], automatons[1], result_automaton);
            Get_identity_relation(result_automaton, preorder);

            auto startsw = std::chrono::high_resolution_clock::now();
            std::clock_t startCPUtime = std::clock();
            std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
            while(std::clock() < whenEnd)
            {
                Inclusion_NFA(automatons[0], automatons[1], preorder);
                ++counter;
            }
            bool result_variable = Inclusion_NFA(automatons[0], automatons[1], preorder);
            std::clock_t endCPUtime = std::clock();
            auto endsw = std::chrono::high_resolution_clock::now();
            long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
            long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

            std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

            if(result_variable) std::cout << "Automaton inclusion A <= B is true! (A - first, B - second automaton)" << std::endl;
            else std::cout << "Automaton inclusion A <= B is not true! (A - first, B - second automaton)" << std::endl;
        }
        catch(const char *msg)
        {
            std::cerr << msg << std::endl;
            return 2;
        }
    }
    else if(str == "-o")
    {
        if(automatons.size() < 2) { std::cout << "The algorithm requires two automatons from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- UNION -------------------------\n";

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            FA result_automaton;
            Union_FA(automatons[0], automatons[1], result_automaton);
            ++counter;
        }
        Union_FA(automatons[0], automatons[1], result_automaton);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        Print_result_FA(result_automaton);
    }
    else if(str == "-x")
    {
        if(automatons.size() < 3) { std::cout << "The algorithm requires three automatons from stdin!" << std::endl; return 4; }
        std::cout << "------------------------- SEQUENCE -------------------------\n";
        //int measurement_modif = measurement_const/4;
        FA result_automaton_p, result_automaton_o, result_automaton;

        auto startsw = std::chrono::high_resolution_clock::now();
        std::clock_t startCPUtime = std::clock();
        std::clock_t whenEnd = startCPUtime + (length_ms/1000.0) * CLOCKS_PER_SEC;
        while(std::clock() < whenEnd)
        {
            FA result_automaton_p, result_automaton_o, result_automaton;
            Intersection_FA(automatons[0], automatons[1], result_automaton_p);
            Union_FA(result_automaton_p, automatons[2], result_automaton_o);
            Determinization_FA(result_automaton_o, result_automaton);
            Complement_FA(result_automaton);
            ++counter;
        }
        Intersection_FA(automatons[0], automatons[1], result_automaton_p);
        Union_FA(result_automaton_p, automatons[2], result_automaton_o);
        Determinization_FA(result_automaton_o, result_automaton);
        Complement_FA(result_automaton);
        std::clock_t endCPUtime = std::clock();
        auto endsw = std::chrono::high_resolution_clock::now();
        long double duration = std::chrono::duration_cast<std::chrono::nanoseconds>(endsw - startsw).count() * 0.000001;
        long double CPUduration = 1000.0 * ((long double)(endCPUtime - startCPUtime) / CLOCKS_PER_SEC);

        std::cout << "states: " << number_of_states << " transitions: " << number_of_transitions << " cpu: " << std::fixed << std::setprecision(6) << CPUduration/(counter+1) << " wall: " << duration/(counter+1) << std::endl << std::endl;

        Print_result_FA(result_automaton);
    }
    else { std::cout << "Wrong arguments (use: -e | -n | -p | -d | -m | -s | -u | -ui | -i | -ii | -o | -x)" << std::endl; return 3; }

    return 0;
}
