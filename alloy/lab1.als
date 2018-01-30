// Part 1
sig Cat { friends : set Cat }
one sig KittyBacon extends Cat { connectionsOf : set Cat }

fact NoFriendlessCats { Cat in friends.Cat }
fact NoSelfFriendship { no iden & friends }
fact SymmetricFriendship { ~friends = friends }
fun F[c:Cat]:set Cat {c.friends-c}
fun FF[c:Cat]:set Cat {F[F[c]]-F[c]-c}
fun FFF[c:Cat]:set Cat {F[F[F[c]]]-F[F[c]]-F[c]-c}
fun FFFF[c:Cat]:set Cat {F[F[F[F[c]]]]-F[F[F[c]]]-F[F[c]]-F[c]-c}
fact { KittyBacon.connectionsOf = F[KittyBacon]+FF[KittyBacon]+FFF[KittyBacon] }

pred ConnectedKittyBacon { Cat - KittyBacon = KittyBacon.connectionsOf }
pred SuperConnected { Cat - KittyBacon in KittyBacon.^friends }
pred ConnectedKittyBacon_equals_SuperConnected {ConnectedKittyBacon iff SuperConnected}
check {ConnectedKittyBacon_equals_SuperConnected} for exactly 3 Cat
check {ConnectedKittyBacon_equals_SuperConnected} for exactly 4 Cat
check {ConnectedKittyBacon_equals_SuperConnected} for exactly 5 Cat 

// Part 2 A
pred localProperty {not ConnectedKittyBacon_equals_SuperConnected}
run localFailsLocally {localProperty} for exactly 5 Cat -- why c not in KittyBacon.connectionsOf?
run localFailsGlobally {
	localProperty
	all c:Cat-KittyBacon | c in KittyBacon.connectionsOf
} for exactly 5 Cat
pred reasonA { some c:Cat | c in FFFF[KittyBacon] }
check validateReasonA { localProperty iff reasonA } for exactly 4 Cat

// Part 2 B
pred globalProperty {KittyBacon not in KittyBacon.connectionsOf}
run globalFailsLocally {globalProperty} for exactly 4 Cat -- why KittyBacon not in KittyBacon.connectionsOf?
run globalFailsGlobally {not globalProperty} for exactly 4 Cat
pred reasonB { KittyBacon not in KittyBacon.friends }
check validateReasonB { globalProperty iff reasonB } for exactly 4 Cat
