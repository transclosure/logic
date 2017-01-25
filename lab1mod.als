// Natasha Danas - Lab 1
//

// Cat friendships
sig Cat {
  friends : set Cat
}

fact NoLonelyKittens {
  no c : Cat | no c.friends
}

fact OutsideFriends {
  no c : Cat | c in c.friends
}

fact TwoWayStreet {
  all c : Cat | all f : c.friends | c in f.friends
}

// Kitty Bacon
one sig KittyBacon extends Cat {}

fun friendsOf[cat : Cat] : set Cat {
  cat.friends
}

pred isFriend[disj cat, kitty : one Cat] {
  kitty in friendsOf[cat]
}

pred isFriendOfFriend[disj cat, kitty : one Cat] {
  kitty in friendsOfFriendsOf[cat]
}

fun friendsOfFriendsOf[cat : Cat] : set Cat {
  friendsOf[friendsOf[cat]] - friendsOf[cat] - cat
}

run {}

// Degrees of Kitty Bacon
pred ConnectedKittyBacon {
  Cat - KittyBacon = connectionsOf[KittyBacon]
}

fun connectionsOf[cat : Cat] : set Cat {
  friendsOf[cat] + friendsOfFriendsOf[cat] + friendsOfFriendsOfFriendsOf[cat]
}

run ConnectedKittyBacon

pred SuperConnected {
  Cat - KittyBacon in KittyBacon.^friends
}

assert ConnectedKittyBacon_equals_SuperConnected {
  ConnectedKittyBacon iff SuperConnected
}

check ConnectedKittyBacon_equals_SuperConnected for exactly 3 Cat

check ConnectedKittyBacon_equals_SuperConnected for exactly 4 Cat

fun friendsOfFriendsOfFriendsOf[cat : Cat] : set Cat {
  friendsOf[friendsOf[friendsOf[cat]]] - friendsOf[friendsOf[cat]] - friendsOf[cat] - cat
}

check ConnectedKittyBacon_equals_SuperConnected for exactly 5 Cat
// No. Transitive closure cannot be expressed as predicates since it
// is a higher order function. Trying to make connectionsOf recursive would
// only work if the friends relation was not symmetric.


// Kitty Bacon and the cool cat club
one sig CoolCatClub {
  members : set Cat
}

fact CoolKittyBaconConnections {
  CoolCatClub.members = connectionsOf[KittyBacon]
}

pred KittyBaconIsCool {
  KittyBacon in CoolCatClub.members
}

run KittyBaconIsCool


