  THE SPEC:

  Theo G's example: we're no longer interested in actual ambient temp.
  Instead, we're looking at the thermostat setting and whether or not it's
  set to something that everyone is comfortable with. 

  We have two people: Nice and Selfish. Selfish is comfortable at more 
  temperatures than Nice. The model has people setting the thermostat
  to temps they are comfortable at, so Selfish can potentially make Nice
  uncomfy. (The names aren't well chosen, of course; it's not Selfish's fault
  that they are easier to make happy than Nice. Both people are "selfish!")

  Since we're keeping track of who is changing the thermostat, I originally
  used the event idiom. But in order to avoid slowdown as much as possible,
  I've switched to a Moore-machine style where the event leading to the next
  state is baked into the state itself. This is far, far more efficient than events
  but increases the number of platonic states/initial-states, which means it's
  imperative we're looking for a counterexample and not trying to do
  brute-force verification.

------------------------------------

  THE ANALYSIS:

  Split into 2 specs: one that drives synthesis (step 1) and one that drives verification (step 2).
  
  We start assuming the first config synthesized is just the maximum permissions possible, so
    there's no "synthesis_0" predicate. 

  Note the optimization in the synthesis spec: we don't actually need a state predicate there.