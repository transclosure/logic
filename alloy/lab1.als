// Part 1
sig Cat { friends : set Cat }
one sig KittyBacon extends Cat { connectionsOf : set Cat }
fact NoFriendlessCats { Cat in friends.Cat }
fact NoSelfFriendship { no iden & friends }
fact SymmetricFriendship { ~friends = friends }
fact { KittyBacon.connectionsOf = 
	(KittyBacon.friends + 
	KittyBacon.friends.friends + 
	KittyBacon.friends.friends.friends) - KittyBacon
}
pred ConnectedKittyBacon { Cat - KittyBacon = KittyBacon.connectionsOf }
pred SuperConnected { Cat - KittyBacon in KittyBacon.^friends }
pred ConnectedKittyBacon_equals_SuperConnected {ConnectedKittyBacon iff SuperConnected}
check {ConnectedKittyBacon_equals_SuperConnected} for exactly 3 Cat
check {ConnectedKittyBacon_equals_SuperConnected} for exactly 4 Cat
check {ConnectedKittyBacon_equals_SuperConnected} for exactly 5 Cat 

// Part 2 A
pred failurePropertyA {not ConnectedKittyBacon_equals_SuperConnected}
-- strategy A
pred inexactReason { some c:Cat-KittyBacon | c not in KittyBacon.connectionsOf }
run AFailsGlobally { failurePropertyA and not inexactReason } for exactly 5 Cat
-- strategy B
run AFailsLocally {failurePropertyA} for exactly 5 Cat -- why c not in KittyBacon.connectionsOf?
-- task / validation
pred reasonA { some c: Cat | {
	c not in KittyBacon.friends +
             KittyBacon.friends.friends +
             KittyBacon.friends.friends.friends
    c in KittyBacon.friends.friends.friends.friends
}}
check validateReasonA { failurePropertyA iff reasonA } for exactly 5 Cat

// Part 2 B
pred failurePropertyB {KittyBacon not in KittyBacon.connectionsOf}
-- strategy A
run BFailsGlobally {not failurePropertyB} for exactly 4 Cat
-- strategy B
run BFailsLocally {failurePropertyB} for exactly 4 Cat -- why KittyBacon not in KittyBacon.connectionsOf?
-- task / validation
pred reasonB { KittyBacon not in KittyBacon.friends }
check validateReasonB { failurePropertyB iff reasonB } for exactly 4 Cat
