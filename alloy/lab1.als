// universe
sig Cat { friends : set Cat }
one sig KittyBacon extends Cat { connectionsOf : set Cat }
// constraints
fact { Cat in friends.Cat }
fact { no iden & friends }
fact { ~friends = friends }
fact { KittyBacon.connectionsOf = 
	KittyBacon.friends + 
	(KittyBacon.friends.friends - KittyBacon.friends - KittyBacon) + 
	(KittyBacon.friends.friends.friends - KittyBacon.friends.friends - KittyBacon.friends - KittyBacon)
}
// properties
pred IsSuperConnected { KittyBacon.connectionsOf = KittyBacon.^friends - KittyBacon }
check {IsSuperConnected} for exactly 3 Cat
check {IsSuperConnected} for exactly 4 Cat
check {IsSuperConnected} for exactly 5 Cat
// study
pred problem { some KittyBacon.friends.friends.friends.friends }
check fixUC { not problem implies IsSuperConnected } for exactly 5 Cat
run fixOC { not problem implies IsSuperConnected } for exactly 5 Cat
