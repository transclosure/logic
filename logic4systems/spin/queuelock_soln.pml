// Anderson's queue lock (basic version)
// Assume processes are always contending 

// Adjust this to change the number of threads (N=2 default)
#define NTHREADS 3

// Try with NTHREADS = 3. Assertion fails. Why?

/////////////////////////////////////////////////////////////////////

// Promela has C-macro like inlines. These are not helper functions;
// they can't return anything. Invocations get replaced with the
// code inside at compile time. Use these macros to simulate atomic
// Test-And-Set (TAS) and Get-And-Increment (GAI) actions.

// Simulate hardware TAS
inline test_and_set(VAR, VAL, RESULT) {
  d_step {
    if :: VAR != VAL -> VAR = VAL; RESULT = true;
       :: VAR == VAL -> RESULT = false;
    fi;
  }
}

// Simulate hardware GAI 
inline get_and_increment(VAR, RESULT) {
  d_step {
    RESULT = VAR;
    VAR = (VAR + 1) % NTHREADS; // *** CHANGE for (2) *** 
  }
}

/////////////////////////////////////////////////////////////////////

// sets all to false; init process gives flags[0] = true.
bool flags[NTHREADS] = {true, false}; 

// the thread that gets slot 0 goes first
byte next = 0; 

// Variables for verification. Note that these are also hints re: how to verify...
byte in_crit; // *number* of processes in critical section
byte expectNextSlotInCS = 0; // next slot expected to be used

/////////////////////////////////////////////////////////////////////

// A process contending for the lock. Start with N of them
active [NTHREADS] proctype a_process()
{
  // Allocate a different mySlot for each a_process instance.
  // Doing this, instead of making a global array of length
  // NTHREADS tells Spin that each mySlot can only be
  // accessed by its local thread, which speeds up verification.
  
  byte mySlot;  

  do
     ::
        get_and_increment(next,mySlot);   // grab a slot    
        printf("my slot: %d. flag = %d\n", mySlot, flags[mySlot % NTHREADS]);
        flags[mySlot % NTHREADS];         // block until my slot is true 
        printf("progressing. my slot: %d. flag = %d\n", mySlot, flags[mySlot % NTHREADS]);
        flags[mySlot % NTHREADS] = false; // reset this flag for re-use later

        //////////////////////////////////////////////////////////////////
        in_crit++; // in CS

        // verify (b): slots are used in order (implies FIFO)
        assert(expectNextSlotInCS == mySlot % NTHREADS);
        
        // set helper verification variable: which slot is expected next?
        expectNextSlotInCS = (mySlot +1) % NTHREADS; 

        // Verify (a): mutual exclusion 
        label_cs: assert(in_crit <= 1);

        in_crit--; // out of CS
        //////////////////////////////////////////////////////////////////

        flags[(mySlot+1) % NTHREADS] = true; // next thread can continue
  od;
}

// ./pan -N no_starvation -a -f -m2000000
ltl no_starvation {
  always eventually a_process[0]@label_cs
}