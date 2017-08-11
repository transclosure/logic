// Lock 2 w/o option of disinterest.

byte victim = 255;

// For verification
bool in_crit[2];

active [2] proctype a_process()
{
  tryagain:
    victim = _pid; // defer to other process
    victim != _pid; // block until other process defers

    in_crit[_pid] = 1;
    assert(in_crit[1 - _pid] == 0);
    in_crit[_pid] = 0;  
  goto tryagain;
}

ltl zero_eats { always (victim==0 -> (eventually in_crit[0])) }

// Compile to C verifier as in lock1.
// To check an LTL property, you need to do ./pan -a
// -a is short for "accepting cycle", which is a technical term meaning the property is violated.

