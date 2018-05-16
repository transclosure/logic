// Constants
#define TRU 1
#define FLS 0
// Is there newly produced data?
bool flag = FLS;
// Which processes are in the critical section? 
bool in_cs[2];
// Is there newly consumed data?
bool data = TRU;

// ASSUME: neither process stops producing/consuming

active proctype Producer() {
	start:
		data == TRU;
		in_cs[1 - _pid] == FLS;
		in_cs[_pid] = TRU;
		in_cs[1 - _pid] == FLS;
		// ASSERT: mutual exclusion of critical section
		assert(in_cs[1 - _pid] == FLS);
		// ASSERT: never overwrite data unless read
		assert(data == TRU);
		data = FLS;
		flag = TRU;
		in_cs[_pid] = FLS;
	goto start;
}

active proctype Consumer() {
	start:
		flag == TRU;
		in_cs[1 - _pid] == FLS;
		in_cs[_pid] = TRU;
		in_cs[1 - _pid] == FLS;
		// ASSERT: mutual exclusion of critical section
		assert(in_cs[1 - _pid] == FLS);
		// ASSERT: never read data unless unread
		assert(flag == TRU);
		flag = FLS;
		data = TRU;
		in_cs[_pid] = FLS;
	goto start;
}

// ASSERT: non-starvation / no deadlocks
ltl { always (eventually (in_cs[0])) & (eventually (in_cs[1])) }
