// Constants
#define TRUE 1
#define FALSE 0
// Is there newly produced data?
bool flag = FALSE;
// Which processes are in the critical section? 
bool in_cs[2];
// Is there newly consumed data?
bool data = TRUE;

// ASSUME: neither process stops producing/consuming

active proctype Producer() {
	start:
		data == TRUE;
		in_cs[1 - _pid] == FALSE;
		in_cs[_pid] = TRUE;
		in_cs[1 - _pid] == FALSE;
		// ASSERT: mutual exclusion of critical section
		assert(in_cs[1 - _pid] == FALSE);
		// ASSERT: never overwrite data unless read
		assert(data == TRUE);
		data = FALSE;
		flag = TRUE;
		in_cs[_pid] = FALSE;
	goto start;
}

active proctype Consumer() {
	start:
		flag == TRUE;
		in_cs[1 - _pid] == FALSE;
		in_cs[_pid] = TRUE;
		in_cs[1 - _pid] == FALSE;
		// ASSERT: mutual exclusion of critical section
		assert(in_cs[1 - _pid] == FALSE);
		// ASSERT: never read data unless unread
		assert(flag == TRUE);
		flag = FALSE;
		data = TRUE;
		in_cs[_pid] = FALSE;
	goto start;
}

// ASSERT: non-starvation / no deadlocks
// is this strong enough???????
ltl { always (eventually (in_cs[0])) &
			 (eventually (in_cs[1]))}