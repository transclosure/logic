abstract sig Need {}
one sig EnoughSleep extends Need {}
one sig GoodGrades extends Need {}
one sig SocialLife extends Need {}
sig Person { choose : set Need }

fact { #Need = 3 and all p:Person | {
	#(p.choose) > 0
	#(p.choose) < 3 
}}

run {} for 1 Person // trivial base
run {some Person} for 1 Person // non-trivial base
run {some p: Person | #(p.choose) > 1 } for 1 Person // one augment
run {some p: Person | #(p.choose) > 2 } for 1 Person // two augments

