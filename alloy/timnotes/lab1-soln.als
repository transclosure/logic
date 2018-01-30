/*
  Solution to Lab 1 by Tim
  -- comments are "student" comments, // comments are template

  TODO: make sure students are in "arbitrary model" mode
  TODO: are we re-using settings from normal Alloy, like core granularity?
  TODO: connectionsOf made into a field in writeup
*/

sig Cat {
  friends : set Cat
}

run {}

fact NoLonelyKittens {
  -- filling this in
  -- all cats have at least one friend
  all c: Cat | some c.friends
}

fact OutsideFriends {
  -- filling this in
  -- no self-friendship		
  no iden & friends
}

fact TwoWayStreet {
  -- filling this in
  -- friendship is symmetric
  friends = ~friends
}

one sig KittyBacon extends Cat {
  connectionsOf: set Cat
} 

fact connectionsOfKittyBacon {
  -- TODO: writeup change!
  -- filling this in
  connectionsOf[KittyBacon] = 
  friendsOf[KittyBacon] + friendsOfFriendsOf[KittyBacon]
  -- adding another stage. TODO: specify do it in a /function/?
  + (KittyBacon.friends.friends.friends - KittyBacon)
}

// `friendsOf` consumes a `Cat` and returns a set of `Cat`s.
fun friendsOf[cat : Cat] : set Cat {
  cat.friends
}

// `isFriend` consumes two cats and is true iff the two cats
// disjoint (they aren't the same cat) and the second cat is
// a friend of the first cat.
pred isFriend[disj cat, kitty : one Cat] {
  kitty in friendsOf[cat]
}

pred isFriendOfFriend[disj cat, kitty : one Cat] {
  kitty in friendsOfFriendsOf[cat]
}

fun friendsOfFriendsOf[cat : Cat] : set Cat {
  -- filling this in
  -- TODO writeup around this, and don't include - cat.friends
  cat.friends.friends - cat
}

pred ConnectedKittyBacon {
  Cat - KittyBacon = connectionsOf[KittyBacon]
}

run ConnectedKittyBacon

pred SuperConnected {
  Cat - KittyBacon in KittyBacon.^friends
}

-- TODO: explain "assert" as opposite of run, or else make it a pred
assert ConnectedKittyBacon_equals_SuperConnected {
  -- filling this in
 ConnectedKittyBacon iff SuperConnected
}
check ConnectedKittyBacon_equals_SuperConnected for exactly 3 Cat
check ConnectedKittyBacon_equals_SuperConnected for exactly 4 Cat
check ConnectedKittyBacon_equals_SuperConnected for exactly 5 Cat

----------------------------------------------------------------------
-- Strategy A 
----------------------------------------------------------------------

-- TODO: pictures?

-- Why is the _equals_ assert failing at size 5?
-- TODO: may want to rename some of these predicates, explain

-- TODO not ConnectedKittyBacon_equals_SuperConnected in localProperty, but was assert

/*
-- local = in /some/ satisfying instances, this holds
pred localProperty {not (ConnectedKittyBacon iff SuperConnected) }
run localFailsGlobally { 
  localProperty 
  -- TODO: consistent function call stx
  -- TODO: is this saying something like only one dir of the bi-imp fails?
  --    SuperConnected -> CKB fails. Just getting confused by the negation.
  all c:Cat-KittyBacon | c in connectionsOf[KittyBacon]
} for exactly 5 Cat
pred reasonA { 
  -- my reason: characterize when localProperty holds
  -- what is it about these instances that MAKES the property hold?
  some c: Cat | {
    c not in KittyBacon.friends +
             KittyBacon.friends.friends +
             KittyBacon.friends.friends.friends
    c in KittyBacon.friends.friends.friends.friends
  }
}
-- TODO: bounds should all be 5, right?
check validateReasonA { localProperty iff reasonA } for exactly 5 Cat

-- global = in every satisfying instance, this holds: 
pred globalProperty {KittyBacon not in connectionsOf[KittyBacon]}
-- so try to find an instance of its negation and look at core:
run globalFailsGlobally {not globalProperty} for exactly 5 Cat
pred reasonB {
  -- my reason: "the spec says that..."
  KittyBacon not in KittyBacon.friends
}
check validateReasonB { globalProperty iff reasonB } for exactly 5 Cat
*/

----------------------------------------------------------------------
-- Strategy B 
----------------------------------------------------------------------

-- What would an implies reason rather than a characterize reason?
-- IFF: some cat in 4th degree
-- IMPLIES: friends 4 times


-- TODO: again, was assert not pred
pred localProperty {not (ConnectedKittyBacon iff SuperConnected)}
run localFailsLocally {localProperty} for exactly 5 Cat -- get any surprising model 
-- ASK: @whynot KittyBacon->Cat$? in connectionsOf
pred reasonA { 

-- *QQQ*: TWO provenances! which one is the useful one?

 some c: Cat | {
    c not in KittyBacon.friends +
             KittyBacon.friends.friends +
             KittyBacon.friends.friends.friends
    c in KittyBacon.friends.friends.friends.friends
}
check validateReasonA { localProperty iff reasonA } for exactly 4 Cat

-- TODO: change writeup to use connectionsOf field

-- Note different globalProperty. Artifact?
-- True in all instances
pred globalProperty {KittyBacon not in KittyBacon.connectionsOf}
run globalFailsLocally {globalProperty} for exactly 4 Cat
-- ASK: @whynot KittyBacon->KittyBacon in connectionsOf
pred reasonB {
  -- my answer
 -- worth noting provenance is limited; shows the constraint but 
  -- not /why/ the below doesn't happen. 
  KittyBacon not in KittyBacon.friends 
}
check validateReasonB { globalProperty iff reasonB } for exactly 4 Cat


