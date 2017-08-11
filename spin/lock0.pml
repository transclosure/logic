/*
  Lecture outline:
    motivate locking
    ask for properties. expect: mutex, no deadlock
    sketch some example counterexamples (traces) on board. 
    idea of flags; produce lock0. ugh! [active]
    check /after/ raise my flag: produce lock1. ugh!
    flags not enough. what about politeness: lock2. ugh!
    Peterson: combine the two ideas. yay! 
    demo select
*/

// Lock #0
// Check before setting flag:
//   operations out of order. Does not guarantee mutex!

bool flags[2];
byte counter;

// For verification
bool in_crit[2];

active [2] proctype a_process()
{
  restart:
    flags[1 - _pid] == 0;
    flags[_pid] = 1;

    in_crit[_pid] = 1;
    assert(in_crit[1 - _pid] == 0);
    in_crit[_pid] = 0;

    flags[_pid] = 0;
  goto restart;
}

// Result: failed assertion w/ counterexample