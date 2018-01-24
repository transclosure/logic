// Foundations
-- universe
sig Cat { friends : set Cat }
one sig KittyBacon extends Cat { connectionsOf : set Cat }
-- constraints
fact NoFriendlessCats { Cat in friends.Cat }
fact NoSelfFriendship { no iden & friends }
fact SymmetricFriendship { ~friends = friends }
fun F[c:Cat]:set Cat {c.friends-c}
fun FF[c:Cat]:set Cat {F[F[c]]-F[c]-c}
fun FFF[c:Cat]:set Cat {F[F[F[c]]]-F[F[c]]-F[c]-c}
fun FFFF[c:Cat]:set Cat {F[F[F[F[c]]]]-F[F[F[c]]]-F[F[c]]-F[c]-c}
fact { KittyBacon.connectionsOf = F[KittyBacon]+FF[KittyBacon]+FFF[KittyBacon] }
-- properties
pred SuperConnected {KittyBacon.connectionsOf - KittyBacon = KittyBacon.^friends - KittyBacon}
check {SuperConnected} for exactly 3 Cat
check {SuperConnected} for exactly 4 Cat
check {SuperConnected} for exactly 5 Cat 

// Investigation A
-- exploration
run LocalNotSuperConnected {not SuperConnected} for exactly 5 Cat -- why c not in KittyBacon.connectionsOf?
run GlobalNotSuperConnected {
	no c:Cat | c not in KittyBacon.connectionsOf and c in KittyBacon.^friends - KittyBacon
	not SuperConnected
} for exactly 5 Cat
-- explanation
pred reasonA { some c:Cat | c in FFFF[KittyBacon] }
-- validation
run noUnexplainedNotSuperConnectedModels { not reasonA and not SuperConnected } for exactly 5 Cat
run someExplainedSuperConnectedModels { not reasonA and SuperConnected } for exactly 5 Cat
-- local problems are under-constraint only, fine just not what we expected at first

// Investigation B
-- exploration
run LocalKittyBaconLeftOut {} for exactly 4 Cat -- why KittyBacon not in KittyBacon.connectionsOf?
run GlobalKittyBaconLeftOut {KittyBacon in KittyBacon.connectionsOf} for exactly 4 Cat
-- explanation
pred reasonB { KittyBacon not in KittyBacon.friends }
-- validation
run findsOverconstraint { not reasonB } for exactly 5 Cat
-- since this is a global problem being investigated, we can't do the under-constraint validation check
-- this is alloy telling you to remove your self friendship over-constraint

