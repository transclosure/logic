// Lock #2
// Problem: If 1st thread goes and 2nd thread never does, 1st thread never gets to go (waiting for victim != self)

byte victim = 255;

// For verification
bool in_crit[2];

active [2] proctype a_process()
{

  tryagain:
  do
    // Allow processes to be dis-interested in the critical section.
    // Without this, the failure case can never happen: both processes *must* seek the CS.
    :: goto tryagain;

    :: victim = _pid; // defer to other process
       victim != _pid; // block until other process defers

       in_crit[_pid] = 1;
       assert(in_crit[1 - _pid] == 0);
       in_crit[_pid] = 0;
  od;
}

// In a true deadlock, all processes are stuck. The problem here isn't a deadlock, it's an infinite
// wait. Instead of running ./pan as in lock 1, we state a more subtle property:

// "It's always true that: if process 0 tries to get the CS, eventually someone will get the CS"
ltl strong_no_deadlocks { always (victim==0 -> (eventually (in_crit[0] || in_crit[1]))) }

// Compile to C verifier as in lock1.
// To check an LTL property, you need to do ./pan -a
// -a is short for "accepting cycle", which is a technical term meaning the property is violated.
// spin -t -p lock2.pml to see the trace.

