// Real bits in the algorithm:
// (1) The Boolean flag, indicating that there is data to be read.
bool flag = 0;

// For verification only
// (1) Who is in the "Critical Section", which is the parts of the program that can access
// the shared data
bool in_cs[2];
// (2) A Boolean that indicates whether the data in the buffer is unread.
//    NOTE: you are not required to model the buffer itself, only whether its data is fresh!
bool data = 0;

// Two processes ("active" means to load on startup). Recall that _pid is the unique process
// id assigned by Spin, starting at 0.
active proctype Producer() {

}

active proctype Consumer() {

}