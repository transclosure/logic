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

pred SuperConnected {KittyBacon.connectionsOf - KittyBacon = KittyBacon.^friends - KittyBacon}
check {SuperConnected} for exactly 3 Cat
check {SuperConnected} for exactly 4 Cat
check {SuperConnected} for exactly 5 Cat 

// Part 2
-- Property A
pred localFailure {not SuperConnected}
run localFailsLocally {localFailure} for exactly 5 Cat -- why c not in KittyBacon.connectionsOf?
run localFailsGlobally {
	no c:Cat | c not in KittyBacon.connectionsOf and c in KittyBacon.^friends - KittyBacon
	localFailure
} for exactly 5 Cat
pred reasonA { some c:Cat | c in FFFF[KittyBacon] }
run validateReasonA { localFailure and not reasonA } for exactly 5 Cat
run sanitycheckReasonA { not localFailure and not reasonA } for exactly 5 Cat
-- Property B
pred globalFailure {KittyBacon not in KittyBacon.connectionsOf}
run globalFailsLocally {} for exactly 4 Cat -- why KittyBacon not in KittyBacon.connectionsOf?
run globalFailsGlobally {not globalFailure} for exactly 4 Cat
pred reasonB { KittyBacon not in KittyBacon.friends }
run validateReasonB { globalFailure and not reasonB } for exactly 5 Cat
run sanitycheckReasonB { not globalFailure and not reasonB } for exactly 5 Cat
