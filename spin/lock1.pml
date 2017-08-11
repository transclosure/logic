// Lock #1
// Problem: flag1 -> flag2 -> both block

bool flags[2];

// For verification
bool in_crit[2];

active [2] proctype a_process()
{
  restart:
    flags[_pid] = 1; // raise flag
    flags[1 - _pid] == 0; // block until other flag is down

    in_crit[_pid] = 1;
    assert(in_crit[1 - _pid] == 0); // check mutex property
    in_crit[_pid] = 0;

    flags[_pid] = 0; // lower flag
  goto restart;
}

// If you just run "spin lock1.pml", Spin executes the program non-deterministically.
// That's not enough to do an exhaustive search for possible violations. Instead,
// compile to a C program that searches all possible executions. That's *not* the same
// as "compiling the program to C".

// Promela to C verifier: spin -a lock1.pml
// Compile the verifier: gcc -o pan pan.c
// Run the search for deadlocks and assert violations: ./pan
// Spin will detect the deadlock (nobody can move; contrast lock2).
// To see the full trace leading to deadlock: spin -t -p lock1.pml