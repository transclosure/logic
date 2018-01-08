sig Cat {friends : set Cat}
fact NoFriendlessCats {no c:Cat | no c.friends}
fact NoSelfFriendship {no c:Cat | c in c.friends}
fact SymmetricFriendship {friends = ~friends}
one sig KittyBacon extends Cat {
	connectionsOf : set Cat
}
fact { 
	// definitely need function desugaring in provenance
	KittyBacon.connectionsOf = 
	KittyBacon.friends + 
	(KittyBacon.friends.friends - KittyBacon.friends - KittyBacon) + 
	(KittyBacon.friends.friends.friends - KittyBacon.friends.friends - KittyBacon.friends - KittyBacon)
}
assert IsSuperConnected {
	// transitive closure desugaring in provenance?
	// we should study how looking at provenance (none, highlighting, proof tree) affects the students understanding of transitive closure
	// what's the rubric here? what understanding goals are there for TC?
	// if that's too complex / abstract, maybe there's a sweep style alternative we can do instead?
	KittyBacon.connectionsOf = KittyBacon.^friends - KittyBacon
}
check IsSuperConnected for exactly 3 Cat
check IsSuperConnected for exactly 4 Cat
check IsSuperConnected for exactly 5 Cat
