// Peterson

byte victim;
bool flags[2];

// For verification
bool in_crit[2];

active [2] proctype a_process()
{
  tryagain:
  do :: goto tryagain;

     :: flags[_pid] = true;
        victim = _pid;

        flags[1 - _pid] == false || victim != _pid;

        in_crit[_pid] = 1;
        printf("In crit: %d\n", _pid);
        assert(in_crit[1 - _pid] == 0);
        in_crit[_pid] = 0;
        flags[_pid] = 0;
  od;
}


// No starvation: a process that asks always gets to the critical section.
ltl no_starvation { always (flags[0] -> (eventually in_crit[0])) }
// ^ This fails. Talk through why. When is flags[0] true? :-)
//  A: In the critical section! So finishing final request leads to obligation to sat a future one

// Better property: the process eventually lowers its flag.
ltl no_starvation2 { always (flags[0] -> (eventually !flags[0])) }
// Fails! Why? Fairness... one proc never gets a /chance/ to move forward (even though it can)

///////////
// Comments from *last year*

// WEDNESDAY is until/weakuntil, + LTL translation + perspective on TL

// FRIDAY w/ spin misc. + partial order reduction
//   + process variables
// Alternative property: the process eventually returns to the start of the loop.
ltl no_starvation3 { always (flags[0] -> (eventually (a_process[0]@tryagain))) }

// By default, Spin allows the scheduler to be unfair. So the property fails.
// If we assume fairness (./pan -a -f -N no_starvation2) it passes.

