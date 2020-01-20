/*
	*
		*
			Object/Action Factored MDP
		*
	*
*/
-- GENERAL
open util/boolean
-- RDDL: types { ... }
abstract sig Agent {}
abstract sig GlassBlock {}
abstract sig Apple {}
abstract sig Potato {}
abstract sig RawRabbit {}
abstract sig CookedRabbit {}
abstract sig DiamondAxe {}
abstract sig OrchidFlower {}
abstract sig DirtBlock {}
abstract sig DaisyFlower {}
abstract sig RedstoneBlock {}
abstract sig Lava {}
-- RDDL: pvariables { ... }
abstract sig Time {
	-- state fluents
	agentx: Agent -> Int,
	agenty: Agent -> Int,
	agentz: Agent -> Int,
	agentalive: Agent -> Bool,
	agenthaspickaxe: Agent -> Bool,
	agentnumapples: Agent -> Int,
	agentnumpotatoes: Agent -> Int,
	agentnumorchids: Agent -> Int,
	agentnumdaisyflowers: Agent -> Int,
	agentnumrawrabbits: Agent -> Int,
	agentnumcookedrabbits: Agent -> Int,
	glassblockx: GlassBlock -> Int,
	glassblocky: GlassBlock -> Int,
	glassblockz: GlassBlock -> Int,
	glassblockhits: GlassBlock -> Int,
	glassblockpresent: GlassBlock -> Bool,
	dirtblockx: DirtBlock -> Int,
	dirtblocky: DirtBlock -> Int,
	dirtblockz: DirtBlock -> Int,
	dirtblockhits: DirtBlock -> Int,
	dirtblockpresent: DirtBlock -> Bool,
	applex: Apple -> Int,
	appley: Apple -> Int,
	applez: Apple -> Int,
	applepresent: Apple -> Bool,
	daisyflowerx: DaisyFlower -> Int,
	daisyflowery: DaisyFlower -> Int,
	daisyflowerz: DaisyFlower -> Int,
	daisyflowerpresent: DaisyFlower -> Bool,
	rawrabbitx: RawRabbit -> Int,
	rawrabbity: RawRabbit -> Int,
	rawrabbitz: RawRabbit -> Int,
	rawrabbitpresent: RawRabbit -> Bool,
	orchidx: OrchidFlower -> Int,
	orchidy: OrchidFlower -> Int,
	orchidz: OrchidFlower -> Int,
	orchidpresent: OrchidFlower -> Bool,
	potatox: Potato -> Int,
	potatoy: Potato -> Int,
	potatoz: Potato -> Int,
	potatopresent: Potato -> Bool,
	-- non-fluents
	lavax: Lava -> Int,
	lavay: Lava -> Int,
	lavaz: Lava -> Int
}
one sig Initial,Goal extends Time {}
/*
-- RDDL: cdf { taxix } 
pred taxix_movee[s:Time,ss:Time,t:Taxi,tx:Int] {
	Int in ss.taxix[t]
}
pred taxix_movew[s:Time,ss:Time,t:Taxi,tx:Int] {
	--True in s.movew[t]
	Int in ss.taxix[t]
}
pred taxix_else[s:Time,ss:Time,t:Taxi,tx:Int] {
	tx in ss.taxix[t]
}
-- RDDL: cdf { taxiy } 
pred taxiy_moven[s:Time,ss:Time,t:Taxi,ty:Int] {
	Int in ss.taxiy[t]
}
pred taxiy_moves[s:Time,ss:Time,t:Taxi,ty:Int] {
	Int in ss.taxiy[t]
}
pred taxiy_else[s:Time,ss:Time,t:Taxi,ty:Int] {
	ty in ss.taxiy[t]
}
-- RDDL: cdf { passx } 
pred passx_movee[s:Time,ss:Time,p:Pass,px:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
	}
	Int in ss.passx[p]
}
pred passx_movew[s:Time,ss:Time,p:Pass,px:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
	}
	Int in ss.passx[p]
}
pred passx_else[s:Time,ss:Time,p:Pass,px:Int] {
	px in ss.passx[p]
}
-- RDDL: cdf { passy } 
pred passy_moven[s:Time,ss:Time,p:Pass,py:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
	}
	Int in ss.passy[p]
}
pred passy_moves[s:Time,ss:Time,p:Pass,py:Int] {
	some t:Taxi | {
		True in s.pint[p,t]
	}
	Int in ss.passy[p]
}
pred passy_else[s:Time,ss:Time,p:Pass,py:Int] {
	py in ss.passy[p]
}
-- RDDL: cdf { pint }
pred pint_pickup[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	some (s.taxix[t]&s.passx[p])
	some (s.taxiy[t]&s.passy[p])
	False in s.pint[p,t]
	False in pnt
	Bool in ss.pint[p,t]
}
pred pint_dropoff[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	True in s.pint[p,t]
	True in pnt
	Bool in ss.pint[p,t]
}
pred pint_else[s:Time,ss:Time,p:Pass,t:Taxi,pnt:Bool] {
	pnt in ss.pint[p,t]
}
*/
/*
	*
		*
			MDP Problem Instance
		*
	*
*/
one sig Steve extends Agent {}
one sig 
	GB1,GB2,GB3,GB4,GB5,GB6,GB7,GB8,GB9,GB10,
	GB11,GB12,GB13,GB14,GB15,GB16,GB17,GB18,GB19,GB20,
	GB21,GB22 
extends GlassBlock {}
one sig A1,A2,A3,A4 extends Apple {}
one sig P1 extends Potato {}
one sig RR1 extends RawRabbit {}
one sig CR1 extends CookedRabbit {}
one sig DA1 extends DiamondAxe {}
one sig 
	DRB1,DRB2,DRB3,DRB4,DRB5,DRB6,DRB7,DRB8,DRB9,DRB10,
	DRB11,DRB12,DRB13,DRB14,DRB15,DRB16,DRB17,DRB18,DRB19,DRB20,
	DRB21,DRB22
extends DirtBlock {}
one sig
	DAF1,DAF2,DAF3,DAF4,DAF5,DAF6,DAF7,DAF8,DAF9,DAF10,
	DAF11,DAF12,DAF13,DAF14,DAF15,DAF16,DAF17,DAF18,DAF19,DAF20,
	DAF21,DAF22
extends DaisyFlower {}
one sig 
	ORF1,ORF2,ORF3,ORF4,ORF5,ORF6,ORF7,ORF8,ORF9,ORF10,
	ORF11,ORF12,ORF13,ORF14,ORF15,ORF16,ORF17,ORF18,ORF19,ORF20,
	ORF21,ORF22,ORF23,ORF24,ORF25,ORF26,ORF27,ORF28,ORF29 
extends OrchidFlower {}
one sig RB1 extends RedstoneBlock {}
one sig
	LA1,LA2,LA3,LA4,LA5,LA6,LA7,LA8,LA9,LA10,
	LA11,LA12,LA13,LA14,LA15,LA16,LA17,LA18,LA19,LA20,
	LA21,LA22,LA23,LA24,LA25,LA26,LA27,LA28,LA29,LA30,
	LA31,LA32,LA33,LA34,LA35,LA36,LA37,LA38,LA39,LA40,
	LA41,LA42,LA43
extends Lava {}
pred initial[s:Time] {
	-- state-fluents
	6 in s.agentx[Steve] and 2 in s.agenty[Steve] 0 in s.agentz[Steve]
	True in s.agentalive[Steve] and True in s.agenthaspickaxe[Steve]
	0 in s.agentnumapples[Steve] and 0 in s.agentnumpotatoes[Steve]
	1 in s.agentnumorchids[Steve] and 0 in s.agentnumdaisyflowers[Steve]
	0 in s.agentnumrawrabbits[Steve] and 0 in s.agentnumcookedrabbits[Steve]
    1 in s.glassblockx[GB1]   	and 4 in s.glassblocky[GB1]     		and 0 in s.glassblockz[GB1]
    0 in s.glassblockhits[GB1] 	and True in s.glassblockpresent[GB1] 
    2 in s.glassblockx[GB2]   	and 4 in s.glassblocky[GB2]     		and 0 in s.glassblockz[GB2]
    0 in s.glassblockhits[GB2] 	and True in s.glassblockpresent[GB2] 
    3 in s.glassblockx[GB3]   	and 4 in s.glassblocky[GB3]     		and 0 in s.glassblockz[GB3]
    0 in s.glassblockhits[GB3] 	and True in s.glassblockpresent[GB3] 
    4 in s.glassblockx[GB4]   	and 4 in s.glassblocky[GB4]     		and 0 in s.glassblockz[GB4]
    0 in s.glassblockhits[GB4] 	and True in s.glassblockpresent[GB4] 
    5 in s.glassblockx[GB5]   	and 4 in s.glassblocky[GB5]     		and 0 in s.glassblockz[GB5]
    0 in s.glassblockhits[GB5] 	and True in s.glassblockpresent[GB5] 
    6 in s.glassblockx[GB6]   	and 4 in s.glassblocky[GB6]     		and 0 in s.glassblockz[GB6]
    0 in s.glassblockhits[GB6] 	and True in s.glassblockpresent[GB6] 
    7 in s.glassblockx[GB7]   	and 4 in s.glassblocky[GB7]     		and 0 in s.glassblockz[GB7]
    0 in s.glassblockhits[GB7] 	and True in s.glassblockpresent[GB7] 
    8 in s.glassblockx[GB8]   	and 4 in s.glassblocky[GB8]     		and 0 in s.glassblockz[GB8]
    0 in s.glassblockhits[GB8] 	and True in s.glassblockpresent[GB8] 
    9 in s.glassblockx[GB9]   	and 4 in s.glassblocky[GB9]     		and 0 in s.glassblockz[GB9]
    0 in s.glassblockhits[GB9] 	and True in s.glassblockpresent[GB9] 
    10 in s.glassblockx[GB10]   and 4 in s.glassblocky[GB10]     		and 0 in s.glassblockz[GB10]
    0 in s.glassblockhits[GB10] and True in s.glassblockpresent[GB10] 
    11 in s.glassblockx[GB11]   and 4 in s.glassblocky[GB11]     		and 0 in s.glassblockz[GB11]
    0 in s.glassblockhits[GB11] and True in s.glassblockpresent[GB11] 
    1 in s.glassblockx[GB12]   	and 4 in s.glassblocky[GB12]     		and 1 in s.glassblockz[GB12]
    0 in s.glassblockhits[GB12] and True in s.glassblockpresent[GB12] 
    2 in s.glassblockx[GB13]   	and 4 in s.glassblocky[GB13]     		and 1 in s.glassblockz[GB13]
    0 in s.glassblockhits[GB13] and True in s.glassblockpresent[GB13] 
    3 in s.glassblockx[GB14]   	and 4 in s.glassblocky[GB14]     		and 1 in s.glassblockz[GB14]
    0 in s.glassblockhits[GB14] and True in s.glassblockpresent[GB14] 
    4 in s.glassblockx[GB15]   	and 4 in s.glassblocky[GB15]     		and 1 in s.glassblockz[GB15]
    0 in s.glassblockhits[GB15] and True in s.glassblockpresent[GB15] 
    5 in s.glassblockx[GB16]   	and 4 in s.glassblocky[GB16]     		and 1 in s.glassblockz[GB16]
    0 in s.glassblockhits[GB16] and True in s.glassblockpresent[GB16] 
    6 in s.glassblockx[GB17]   	and 4 in s.glassblocky[GB17]     		and 1 in s.glassblockz[GB17]
    0 in s.glassblockhits[GB17] and True in s.glassblockpresent[GB17] 
    7 in s.glassblockx[GB18]   	and 4 in s.glassblocky[GB18]     		and 1 in s.glassblockz[GB18]
    0 in s.glassblockhits[GB18] and True in s.glassblockpresent[GB18] 
    8 in s.glassblockx[GB19]   	and 4 in s.glassblocky[GB19]     		and 1 in s.glassblockz[GB19]
    0 in s.glassblockhits[GB19] and True in s.glassblockpresent[GB19] 
    9 in s.glassblockx[GB20]   	and 4 in s.glassblocky[GB20]     		and 1 in s.glassblockz[GB20]
    0 in s.glassblockhits[GB20] and True in s.glassblockpresent[GB20] 
    10 in s.glassblockx[GB21]   and 4 in s.glassblocky[GB21]     		and 1 in s.glassblockz[GB21]
    0 in s.glassblockhits[GB21] and True in s.glassblockpresent[GB21] 
    11 in s.glassblockx[GB22]   and 4 in s.glassblocky[GB22]     		and 1 in s.glassblockz[GB22]
    0 in s.glassblockhits[GB22] and True in s.glassblockpresent[GB22] 
    3 in s.applex[A1]	and 2 in s.appley[A1]	and 0 in s.applez[A1] 	and 	True in s.applepresent[A1]
    4 in s.applex[A2]	and 3 in s.appley[A2]	and 0 in s.applez[A2] 	and 	True in s.applepresent[A2]
    8 in s.applex[A3]	and 2 in s.appley[A3]	and 0 in s.applez[A3] 	and 	True in s.applepresent[A3]
    5 in s.applex[A4]	and 9 in s.appley[A4]	and 0 in s.applez[A4] 	and 	True in s.applepresent[A4]
    10 in s.potatox[P1] and 1 in s.potatoy[P1] and 0 in s.potatoz[P1] and True in s.potatopresent[P1]
    1 in s.rawrabbitx[RR1] and 1 in s.rawrabbity[RR1] and 0 in s.rawrabbitz[RR1] and True in s.rawrabbitpresent[RR1]	
    0 in s.dirtblockx[DRB1] and 10 in s.dirtblocky[DRB1] and 3 in s.dirtblockz[DRB1]
    0 in s.dirtblockhits[DRB1] and True in s.dirtblockpresent[DRB1] 
    1 in s.dirtblockx[DRB2] and 10 in s.dirtblocky[DRB2] and 3 in s.dirtblockz[DRB2]
    0 in s.dirtblockhits[DRB2] and True in s.dirtblockpresent[DRB2] 
    2 in s.dirtblockx[DRB3] and 10 in s.dirtblocky[DRB3] and 3 in s.dirtblockz[DRB3]
    0 in s.dirtblockhits[DRB3] and True in s.dirtblockpresent[DRB3] 
    3 in s.dirtblockx[DRB4] and 10 in s.dirtblocky[DRB4] and 3 in s.dirtblockz[DRB4]
    0 in s.dirtblockhits[DRB4] and True in s.dirtblockpresent[DRB4] 
    4 in s.dirtblockx[DRB5] and 10 in s.dirtblocky[DRB5] and 3 in s.dirtblockz[DRB5]
    0 in s.dirtblockhits[DRB5] and True in s.dirtblockpresent[DRB5] 
    5 in s.dirtblockx[DRB6] and 10 in s.dirtblocky[DRB6] and 3 in s.dirtblockz[DRB6]
    0 in s.dirtblockhits[DRB6] and True in s.dirtblockpresent[DRB6] 
    6 in s.dirtblockx[DRB7] and 10 in s.dirtblocky[DRB7] and 3 in s.dirtblockz[DRB7]
    0 in s.dirtblockhits[DRB7] and True in s.dirtblockpresent[DRB7] 
    7 in s.dirtblockx[DRB8] and 10 in s.dirtblocky[DRB8] and 3 in s.dirtblockz[DRB8]
    0 in s.dirtblockhits[DRB8] and True in s.dirtblockpresent[DRB8] 
    8 in s.dirtblockx[DRB9] and 10 in s.dirtblocky[DRB9] and 3 in s.dirtblockz[DRB9]
    0 in s.dirtblockhits[DRB9] and True in s.dirtblockpresent[DRB9] 
    9 in s.dirtblockx[DRB10] and 10 in s.dirtblocky[DRB10] and 3 in s.dirtblockz[DRB10]
    0 in s.dirtblockhits[DRB10] and True in s.dirtblockpresent[DRB10] 
    10 in s.dirtblockx[DRB11] and 10 in s.dirtblocky[DRB11] and 3 in s.dirtblockz[DRB11]
    0 in s.dirtblockhits[DRB11] and True in s.dirtblockpresent[DRB11] 
    10 in s.dirtblockx[DRB12] and 11 in s.dirtblocky[DRB12] and 3 in s.dirtblockz[DRB12]
    0 in s.dirtblockhits[DRB12] and True in s.dirtblockpresent[DRB12] 
    0 in s.dirtblockx[DRB13] and 11 in s.dirtblocky[DRB13] and 3 in s.dirtblockz[DRB13]
    0 in s.dirtblockhits[DRB13] and True in s.dirtblockpresent[DRB13] 
    1 in s.dirtblockx[DRB14] and 11 in s.dirtblocky[DRB14] and 3 in s.dirtblockz[DRB14]
    0 in s.dirtblockhits[DRB14] and True in s.dirtblockpresent[DRB14] 
   	2 in s.dirtblockx[DRB15] and 11 in s.dirtblocky[DRB15] and 3 in s.dirtblockz[DRB15]
    0 in s.dirtblockhits[DRB15] and True in s.dirtblockpresent[DRB15] 
    3 in s.dirtblockx[DRB16] and 11 in s.dirtblocky[DRB16] and 3 in s.dirtblockz[DRB16]
    0 in s.dirtblockhits[DRB16] and True in s.dirtblockpresent[DRB16] 
    4 in s.dirtblockx[DRB17] and 11 in s.dirtblocky[DRB17] and 3 in s.dirtblockz[DRB17]
    0 in s.dirtblockhits[DRB17] and True in s.dirtblockpresent[DRB17]
    5 in s.dirtblockx[DRB18] and 11 in s.dirtblocky[DRB18] and 3 in s.dirtblockz[DRB18]
    0 in s.dirtblockhits[DRB18] and True in s.dirtblockpresent[DRB18] 
    6 in s.dirtblockx[DRB19] and 11 in s.dirtblocky[DRB19] and 3 in s.dirtblockz[DRB19]
    0 in s.dirtblockhits[DRB19] and True in s.dirtblockpresent[DRB19] 
    7 in s.dirtblockx[DRB20] and 11 in s.dirtblocky[DRB20] and 3 in s.dirtblockz[DRB20]
    0 in s.dirtblockhits[DRB20] and True in s.dirtblockpresent[DRB20] 
    8 in s.dirtblockx[DRB21] and 11 in s.dirtblocky[DRB21] and 3 in s.dirtblockz[DRB21]
    0 in s.dirtblockhits[DRB21] and True in s.dirtblockpresent[DRB21] 
    9 in s.dirtblockx[DRB22] and 11 in s.dirtblocky[DRB22] and 3 in s.dirtblockz[DRB22]
    0 in s.dirtblockhits[DRB22] and True in s.dirtblockpresent[DRB22] 
    0 in s.daisyflowerx[DAF1]	and 10 in s.daisyflowery[DAF1] 	and 4 in s.daisyflowerz[DAF1]	 and True in s.daisyflowerpresent[DAF1]
    1 in s.daisyflowerx[DAF2]	and 10 in s.daisyflowery[DAF2] 	and 4 in s.daisyflowerz[DAF2]	 and True in s.daisyflowerpresent[DAF2]
    2 in s.daisyflowerx[DAF3]	and 10 in s.daisyflowery[DAF3] 	and 4 in s.daisyflowerz[DAF3]	 and True in s.daisyflowerpresent[DAF3]
    3 in s.daisyflowerx[DAF4]	and 10 in s.daisyflowery[DAF4] 	and 4 in s.daisyflowerz[DAF4]	 and True in s.daisyflowerpresent[DAF4]
    4 in s.daisyflowerx[DAF5]	and 10 in s.daisyflowery[DAF5] 	and 4 in s.daisyflowerz[DAF5]	 and True in s.daisyflowerpresent[DAF5]
    5 in s.daisyflowerx[DAF6]	and 10 in s.daisyflowery[DAF6] 	and 4 in s.daisyflowerz[DAF6]	 and True in s.daisyflowerpresent[DAF6]
    6 in s.daisyflowerx[DAF7]	and 10 in s.daisyflowery[DAF7] 	and 4 in s.daisyflowerz[DAF7]	 and True in s.daisyflowerpresent[DAF7]
    7 in s.daisyflowerx[DAF8]	and 10 in s.daisyflowery[DAF8] 	and 4 in s.daisyflowerz[DAF8]	 and True in s.daisyflowerpresent[DAF8]
    8 in s.daisyflowerx[DAF9]	and 10 in s.daisyflowery[DAF9] 	and 4 in s.daisyflowerz[DAF9]	 and True in s.daisyflowerpresent[DAF9]
    9 in s.daisyflowerx[DAF10]	and 10 in s.daisyflowery[DAF10] and 4 in s.daisyflowerz[DAF10]	 and True in s.daisyflowerpresent[DAF10]
    10 in s.daisyflowerx[DAF11] and 11 in s.daisyflowery[DAF11] and 4 in s.daisyflowerz[DAF11]	 and True in s.daisyflowerpresent[DAF11]
    10 in s.daisyflowerx[DAF12] and 11 in s.daisyflowery[DAF12] and 4 in s.daisyflowerz[DAF12]	 and True in s.daisyflowerpresent[DAF12]
    0 in s.daisyflowerx[DAF13]	and 11 in s.daisyflowery[DAF13] and 4 in s.daisyflowerz[DAF13]	 and True in s.daisyflowerpresent[DAF13]
    1 in s.daisyflowerx[DAF14]	and 11 in s.daisyflowery[DAF14] and 4 in s.daisyflowerz[DAF14]	 and True in s.daisyflowerpresent[DAF14]
    2 in s.daisyflowerx[DAF15]	and 11 in s.daisyflowery[DAF15] and 4 in s.daisyflowerz[DAF15]	 and True in s.daisyflowerpresent[DAF15]
    3 in s.daisyflowerx[DAF16]	and 11 in s.daisyflowery[DAF16] and 4 in s.daisyflowerz[DAF16]	 and True in s.daisyflowerpresent[DAF16]
    4 in s.daisyflowerx[DAF17]	and 11 in s.daisyflowery[DAF17] and 4 in s.daisyflowerz[DAF17]	 and True in s.daisyflowerpresent[DAF17]
    5 in s.daisyflowerx[DAF18]	and 11 in s.daisyflowery[DAF18] and 4 in s.daisyflowerz[DAF18]	 and True in s.daisyflowerpresent[DAF18]
    6 in s.daisyflowerx[DAF19]	and 11 in s.daisyflowery[DAF19] and 4 in s.daisyflowerz[DAF19]	 and True in s.daisyflowerpresent[DAF19]
    7 in s.daisyflowerx[DAF20]	and 11 in s.daisyflowery[DAF20] and 4 in s.daisyflowerz[DAF20]	 and True in s.daisyflowerpresent[DAF20]
    8 in s.daisyflowerx[DAF21]	and 11 in s.daisyflowery[DAF21] and 4 in s.daisyflowerz[DAF21]	 and True in s.daisyflowerpresent[DAF21]
    9 in s.daisyflowerx[DAF22]	and 11 in s.daisyflowery[DAF22] and 4 in s.daisyflowerz[DAF22]	 and True in s.daisyflowerpresent[DAF22] 
    1 in s.orchidx[ORF1]	and 1 in s.orchidy[ORF1] 	and 0 in s.orchidz[ORF1]  	and True in s.orchidpresent[ORF1]
    2 in s.orchidx[ORF2]	and 1 in s.orchidy[ORF2] 	and 0 in s.orchidz[ORF2]  	and True in s.orchidpresent[ORF2]
    3 in s.orchidx[ORF3]	and 1 in s.orchidy[ORF3] 	and 0 in s.orchidz[ORF3]  	and True in s.orchidpresent[ORF3]
    4 in s.orchidx[ORF4]	and 1 in s.orchidy[ORF4] 	and 0 in s.orchidz[ORF4]  	and True in s.orchidpresent[ORF4]
    5 in s.orchidx[ORF5]	and 1 in s.orchidy[ORF5] 	and 0 in s.orchidz[ORF5]  	and True in s.orchidpresent[ORF5]
    6 in s.orchidx[ORF6]	and 1 in s.orchidy[ORF6] 	and 0 in s.orchidz[ORF6]  	and True in s.orchidpresent[ORF6]
    7 in s.orchidx[ORF7]	and 1 in s.orchidy[ORF7] 	and 0 in s.orchidz[ORF7]  	and True in s.orchidpresent[ORF7]
    8 in s.orchidx[ORF8]	and 1 in s.orchidy[ORF8] 	and 0 in s.orchidz[ORF8]  	and True in s.orchidpresent[ORF8]
    9 in s.orchidx[ORF9]	and 1 in s.orchidy[ORF9] 	and 0 in s.orchidz[ORF9]  	and True in s.orchidpresent[ORF9]
    10 in s.orchidx[ORF10] 	and 1 in s.orchidy[ORF10] 	and 0 in s.orchidz[ORF10]  	and True in s.orchidpresent[ORF10]
    11 in s.orchidx[ORF11] 	and 1 in s.orchidy[ORF11] 	and 0 in s.orchidz[ORF11]  	and True in s.orchidpresent[ORF11]
    1 in s.orchidx[ORF12]	and 2 in s.orchidy[ORF12] 	and 0 in s.orchidz[ORF12]  	and True in s.orchidpresent[ORF12]
    1 in s.orchidx[ORF13]	and 2 in s.orchidy[ORF13] 	and 0 in s.orchidz[ORF13]  	and True in s.orchidpresent[ORF13]
    1 in s.orchidx[ORF14]	and 2 in s.orchidy[ORF14] 	and 0 in s.orchidz[ORF14]  	and True in s.orchidpresent[ORF14]
    1 in s.orchidx[ORF15]	and 2 in s.orchidy[ORF15] 	and 0 in s.orchidz[ORF15]  	and True in s.orchidpresent[ORF15]
    1 in s.orchidx[ORF16]	and 2 in s.orchidy[ORF16] 	and 0 in s.orchidz[ORF16]  	and True in s.orchidpresent[ORF16]
    1 in s.orchidx[ORF17]	and 2 in s.orchidy[ORF17] 	and 0 in s.orchidz[ORF17]  	and True in s.orchidpresent[ORF17]
    1 in s.orchidx[ORF18]	and 2 in s.orchidy[ORF18] 	and 0 in s.orchidz[ORF18]  	and True in s.orchidpresent[ORF18]
    1 in s.orchidx[ORF19]	and 2 in s.orchidy[ORF19] 	and 0 in s.orchidz[ORF19]  	and True in s.orchidpresent[ORF19]
    1 in s.orchidx[ORF20]	and 2 in s.orchidy[ORF20] 	and 0 in s.orchidz[ORF20]  	and True in s.orchidpresent[ORF20]
    1 in s.orchidx[ORF21]	and 2 in s.orchidy[ORF21] 	and 0 in s.orchidz[ORF21]  	and True in s.orchidpresent[ORF21]
    1 in s.orchidx[ORF22]	and 2 in s.orchidy[ORF22] 	and 0 in s.orchidz[ORF22]  	and True in s.orchidpresent[ORF22]
	1 in s.orchidx[ORF23]	and 2 in s.orchidy[ORF23] 	and 0 in s.orchidz[ORF23]  	and True in s.orchidpresent[ORF23]
	1 in s.orchidx[ORF24]	and 2 in s.orchidy[ORF24] 	and 0 in s.orchidz[ORF24]  	and True in s.orchidpresent[ORF24]
	1 in s.orchidx[ORF25]	and 2 in s.orchidy[ORF25] 	and 0 in s.orchidz[ORF25]  	and True in s.orchidpresent[ORF25]
	1 in s.orchidx[ORF26]	and 2 in s.orchidy[ORF26] 	and 0 in s.orchidz[ORF26]  	and True in s.orchidpresent[ORF26]
	1 in s.orchidx[ORF27]	and 2 in s.orchidy[ORF27] 	and 0 in s.orchidz[ORF27]  	and True in s.orchidpresent[ORF27]
	1 in s.orchidx[ORF28]	and 2 in s.orchidy[ORF28] 	and 0 in s.orchidz[ORF28]  	and True in s.orchidpresent[ORF28]
	1 in s.orchidx[ORF29]	and 2 in s.orchidy[ORF29] 	and 0 in s.orchidz[ORF29]  	and True in s.orchidpresent[ORF29]
	-- non-fluents
	1 in s.lavax[LA1]  		and 10 in s.lavay[LA1]  	and 0 in s.lavaz[LA1] 
    2 in s.lavax[LA2]  		and 10 in s.lavay[LA2]  	and 0 in s.lavaz[LA2] 
    3 in s.lavax[LA3]  		and 10 in s.lavay[LA3]  	and 0 in s.lavaz[LA3] 
    4 in s.lavax[LA4]  		and 10 in s.lavay[LA4]  	and 0 in s.lavaz[LA4] 
    5 in s.lavax[LA5]  		and 10 in s.lavay[LA5]  	and 0 in s.lavaz[LA5] 
    6 in s.lavax[LA6]  		and 10 in s.lavay[LA6]  	and 0 in s.lavaz[LA6] 
    7 in s.lavax[LA7]  		and 10 in s.lavay[LA7]  	and 0 in s.lavaz[LA7] 
    8 in s.lavax[LA8]  		and 10 in s.lavay[LA8]  	and 0 in s.lavaz[LA8] 
    9 in s.lavax[LA9]  		and 10 in s.lavay[LA9]  	and 0 in s.lavaz[LA9] 
    10 in s.lavax[LA10]  	and 10 in s.lavay[LA10]  	and 0 in s.lavaz[LA10]
    11 in s.lavax[LA11]  	and 10 in s.lavay[LA11]  	and 0 in s.lavaz[LA11] 
    1 in s.lavax[LA12]  	and 11 in s.lavay[LA12]  	and 0 in s.lavaz[LA12] 
    2 in s.lavax[LA13]  	and 11 in s.lavay[LA13]  	and 0 in s.lavaz[LA13] 
    3 in s.lavax[LA14]  	and 11 in s.lavay[LA14]  	and 0 in s.lavaz[LA14] 
    4 in s.lavax[LA15]  	and 11 in s.lavay[LA15]  	and 0 in s.lavaz[LA15] 
    5 in s.lavax[LA16]  	and 11 in s.lavay[LA16]  	and 0 in s.lavaz[LA16] 
    6 in s.lavax[LA17]  	and 11 in s.lavay[LA17]  	and 0 in s.lavaz[LA17] 
    7 in s.lavax[LA18]  	and 11 in s.lavay[LA18]  	and 0 in s.lavaz[LA18] 
    8 in s.lavax[LA19]  	and 11 in s.lavay[LA19]  	and 0 in s.lavaz[LA19] 
    9 in s.lavax[LA20]  	and 11 in s.lavay[LA20]  	and 0 in s.lavaz[LA20] 
    10 in s.lavax[LA21]  	and 11 in s.lavay[LA21]  	and 0 in s.lavaz[LA21] 
    11 in s.lavax[LA22]  	and 11 in s.lavay[LA22]  	and 0 in s.lavaz[LA22]
    11 in s.lavax[LA23]  	and 11 in s.lavay[LA23]  	and 0 in s.lavaz[LA23] 
    8 in s.lavax[LA24]  	and 5 in s.lavay[LA24]  	and 0 in s.lavaz[LA24] 
    8 in s.lavax[LA25]  	and 6 in s.lavay[LA25]  	and 0 in s.lavaz[LA25] 
    8 in s.lavax[LA26]  	and 7 in s.lavay[LA26]  	and 0 in s.lavaz[LA26] 
    8 in s.lavax[LA27]  	and 8 in s.lavay[LA27]  	and 0 in s.lavaz[LA27] 
    8 in s.lavax[LA28]  	and 9 in s.lavay[LA28]  	and 0 in s.lavaz[LA28] 
    9 in s.lavax[LA29]  	and 5 in s.lavay[LA29]  	and 0 in s.lavaz[LA29] 
    9 in s.lavax[LA30]  	and 6 in s.lavay[LA30]  	and 0 in s.lavaz[LA30] 
    9 in s.lavax[LA31]  	and 7 in s.lavay[LA31]  	and 0 in s.lavaz[LA31] 
    9 in s.lavax[LA32]  	and 8 in s.lavay[LA32]  	and 0 in s.lavaz[LA32] 
    9 in s.lavax[LA33]  	and 9 in s.lavay[LA33]  	and 0 in s.lavaz[LA33] 
    10 in s.lavax[LA34]  	and 5 in s.lavay[LA34]  	and 0 in s.lavaz[LA34] 
    10 in s.lavax[LA35]  	and 6 in s.lavay[LA35]  	and 0 in s.lavaz[LA35] 
    10 in s.lavax[LA36]  	and 7 in s.lavay[LA36]  	and 0 in s.lavaz[LA36] 
    10 in s.lavax[LA37]  	and 8 in s.lavay[LA37]  	and 0 in s.lavaz[LA37] 
    10 in s.lavax[LA38]  	and 9 in s.lavay[LA38]  	and 0 in s.lavaz[LA38] 
    11 in s.lavax[LA39]  	and 5 in s.lavay[LA39]  	and 0 in s.lavaz[LA39] 
    11 in s.lavax[LA40]  	and 6 in s.lavay[LA40]  	and 0 in s.lavaz[LA40] 
    11 in s.lavax[LA41]  	and 7 in s.lavay[LA41]  	and 0 in s.lavaz[LA41] 
    11 in s.lavax[LA42]  	and 8 in s.lavay[LA42]  	and 0 in s.lavaz[LA42] 
    11 in s.lavax[LA43]  	and 9 in s.lavay[LA43]  	and 0 in s.lavaz[LA43]
}
pred goal[s:Time] {
	-- state-fluents
	5 in s.agentx[Steve] and 9 in s.agenty[Steve] 0 in s.agentz[Steve]
	-- non-fluents
	1 in s.lavax[LA1]  		and 10 in s.lavay[LA1]  	and 0 in s.lavaz[LA1] 
    2 in s.lavax[LA2]  		and 10 in s.lavay[LA2]  	and 0 in s.lavaz[LA2] 
    3 in s.lavax[LA3]  		and 10 in s.lavay[LA3]  	and 0 in s.lavaz[LA3] 
    4 in s.lavax[LA4]  		and 10 in s.lavay[LA4]  	and 0 in s.lavaz[LA4] 
    5 in s.lavax[LA5]  		and 10 in s.lavay[LA5]  	and 0 in s.lavaz[LA5] 
    6 in s.lavax[LA6]  		and 10 in s.lavay[LA6]  	and 0 in s.lavaz[LA6] 
    7 in s.lavax[LA7]  		and 10 in s.lavay[LA7]  	and 0 in s.lavaz[LA7] 
    8 in s.lavax[LA8]  		and 10 in s.lavay[LA8]  	and 0 in s.lavaz[LA8] 
    9 in s.lavax[LA9]  		and 10 in s.lavay[LA9]  	and 0 in s.lavaz[LA9] 
    10 in s.lavax[LA10]  	and 10 in s.lavay[LA10]  	and 0 in s.lavaz[LA10]
    11 in s.lavax[LA11]  	and 10 in s.lavay[LA11]  	and 0 in s.lavaz[LA11] 
    1 in s.lavax[LA12]  	and 11 in s.lavay[LA12]  	and 0 in s.lavaz[LA12] 
    2 in s.lavax[LA13]  	and 11 in s.lavay[LA13]  	and 0 in s.lavaz[LA13] 
    3 in s.lavax[LA14]  	and 11 in s.lavay[LA14]  	and 0 in s.lavaz[LA14] 
    4 in s.lavax[LA15]  	and 11 in s.lavay[LA15]  	and 0 in s.lavaz[LA15] 
    5 in s.lavax[LA16]  	and 11 in s.lavay[LA16]  	and 0 in s.lavaz[LA16] 
    6 in s.lavax[LA17]  	and 11 in s.lavay[LA17]  	and 0 in s.lavaz[LA17] 
    7 in s.lavax[LA18]  	and 11 in s.lavay[LA18]  	and 0 in s.lavaz[LA18] 
    8 in s.lavax[LA19]  	and 11 in s.lavay[LA19]  	and 0 in s.lavaz[LA19] 
    9 in s.lavax[LA20]  	and 11 in s.lavay[LA20]  	and 0 in s.lavaz[LA20] 
    10 in s.lavax[LA21]  	and 11 in s.lavay[LA21]  	and 0 in s.lavaz[LA21] 
    11 in s.lavax[LA22]  	and 11 in s.lavay[LA22]  	and 0 in s.lavaz[LA22] 
    8 in s.lavax[LA24]  	and 5 in s.lavay[LA24]  	and 0 in s.lavaz[LA24] 
    8 in s.lavax[LA25]  	and 6 in s.lavay[LA25]  	and 0 in s.lavaz[LA25] 
    8 in s.lavax[LA26]  	and 7 in s.lavay[LA26]  	and 0 in s.lavaz[LA26] 
    8 in s.lavax[LA27]  	and 8 in s.lavay[LA27]  	and 0 in s.lavaz[LA27] 
    8 in s.lavax[LA28]  	and 9 in s.lavay[LA28]  	and 0 in s.lavaz[LA28] 
    9 in s.lavax[LA29]  	and 5 in s.lavay[LA29]  	and 0 in s.lavaz[LA29] 
    9 in s.lavax[LA30]  	and 6 in s.lavay[LA30]  	and 0 in s.lavaz[LA30] 
    9 in s.lavax[LA31]  	and 7 in s.lavay[LA31]  	and 0 in s.lavaz[LA31] 
    9 in s.lavax[LA32]  	and 8 in s.lavay[LA32]  	and 0 in s.lavaz[LA32] 
    9 in s.lavax[LA33]  	and 9 in s.lavay[LA33]  	and 0 in s.lavaz[LA33] 
    10 in s.lavax[LA34]  	and 5 in s.lavay[LA34]  	and 0 in s.lavaz[LA34] 
    10 in s.lavax[LA35]  	and 6 in s.lavay[LA35]  	and 0 in s.lavaz[LA35] 
    10 in s.lavax[LA36]  	and 7 in s.lavay[LA36]  	and 0 in s.lavaz[LA36] 
    10 in s.lavax[LA37]  	and 8 in s.lavay[LA37]  	and 0 in s.lavaz[LA37] 
    10 in s.lavax[LA38]  	and 9 in s.lavay[LA38]  	and 0 in s.lavaz[LA38] 
    11 in s.lavax[LA39]  	and 5 in s.lavay[LA39]  	and 0 in s.lavaz[LA39] 
    11 in s.lavax[LA40]  	and 6 in s.lavay[LA40]  	and 0 in s.lavaz[LA40] 
    11 in s.lavax[LA41]  	and 7 in s.lavay[LA41]  	and 0 in s.lavaz[LA41] 
    11 in s.lavax[LA42]  	and 8 in s.lavay[LA42]  	and 0 in s.lavaz[LA42] 
    11 in s.lavax[LA43]  	and 9 in s.lavay[LA43]  	and 0 in s.lavaz[LA43]
}
/*
pred in_taxix[s:Time,t:Taxi,i:Int] {
	s.taxix[t] in i
}
pred in_taxiy[s:Time,t:Taxi,i:Int] {
	s.taxiy[t] in i
}
pred in_passx[s:Time,p:Pass,i:Int] {
	s.passx[p] in i
}
pred in_passy[s:Time,p:Pass,i:Int] {
	s.passy[p] in i
}
pred in_pint[s:Time,p:Pass,t:Taxi,b:Bool] {
	s.pint[p][t] in b
}
*/
/*
	*
		*
			Planning Sequence/Space/Scope Algorithm
		*
	*
*/
fun relevant : univ {
	{a:Agent | #Initial.agentx[a]!=1}+
	{a:Agent | #Initial.agenty[a]!=1}+
	{a:Agent | #Initial.agentalive[a]!=1}+
	{a:Agent | #Initial.agenthaspickaxe[a]!=1}+
	{a:Agent | #Initial.agentnumapples[a]!=1}+
	{a:Agent | #Initial.agentnumpotatoes[a]!=1}+
	{a:Agent | #Initial.agentnumorchids[a]!=1}+
	{a:Agent | #Initial.agentnumdaisyflowers[a]!=1}+
	{a:Agent | #Initial.agentnumrawrabbits[a]!=1}+
	{a:Agent | #Initial.agentnumcookedrabbits[a]!=1}+
	{g:GlassBlock | #Initial.glassblockx[g]!=1}+
	{g:GlassBlock | #Initial.glassblocky[g]!=1}+
	{g:GlassBlock | #Initial.glassblockz[g]!=1}+
	{g:GlassBlock | #Initial.glassblockhits[g]!=1}+
	{g:GlassBlock | #Initial.glassblockpresent[g]!=1}+
	{g:DirtBlock | #Initial.dirtblockx[g]!=1}+
	{g:DirtBlock | #Initial.dirtblocky[g]!=1}+
	{g:DirtBlock | #Initial.dirtblockz[g]!=1}+
	{g:DirtBlock | #Initial.dirtblockhits[g]!=1}+
	{g:DirtBlock | #Initial.dirtblockpresent[g]!=1}+
	{g:Apple | #Initial.applex[g]!=1}+
	{g:Apple | #Initial.appley[g]!=1}+
	{g:Apple | #Initial.applez[g]!=1}+
	{g:Apple | #Initial.applepresent[g]!=1}+
	{g:DaisyFlower | #Initial.daisyflowerx[g]!=1}+
	{g:DaisyFlower | #Initial.daisyflowery[g]!=1}+
	{g:DaisyFlower | #Initial.daisyflowerz[g]!=1}+
	{g:DaisyFlower | #Initial.daisyflowerpresent[g]!=1}+
	{g:RawRabbit | #Initial.rawrabbitx[g]!=1}+
	{g:RawRabbit | #Initial.rawrabbity[g]!=1}+
	{g:RawRabbit | #Initial.rawrabbitz[g]!=1}+
	{g:RawRabbit | #Initial.rawrabbitpresent[g]!=1}+
	{g:OrchidFlower | #Initial.orchidx[g]!=1}+
	{g:OrchidFlower | #Initial.orchidy[g]!=1}+
	{g:OrchidFlower | #Initial.orchidz[g]!=1}+
	{g:OrchidFlower | #Initial.orchidpresent[g]!=1}+
	{g:Potato | #Initial.potatox[g]!=1}+
	{g:Potato | #Initial.potatoy[g]!=1}+
	{g:Potato | #Initial.potatoz[g]!=1}+
	{g:Potato | #Initial.potatopresent[g]!=1}+
	{g:Lava | #Initial.lavax[g]!=1}+
	{g:Lava | #Initial.lavay[g]!=1}+
	{g:Lava | #Initial.lavaz[g]!=1}
}
run scope {
	initial[Initial]
	goal[Goal]
	/*
	all t:Taxi | {
		all tx:Initial.taxix[t] | {
			!in_taxix[Goal,t,tx] implies (taxix_movee[Goal,Initial,t,tx] or taxix_movew[Goal,Initial,t,tx])
		}
		all ty:Initial.taxiy[t] | {
			!in_taxiy[Goal,t,ty] implies (taxiy_moven[Goal,Initial,t,ty] or taxiy_moves[Goal,Initial,t,ty])
		}
	}
	all p:Pass | {
		all px:Initial.passx[p] | {
			!in_passx[Goal,p,px] implies (passx_movee[Goal,Initial,p,px] or passx_movew[Goal,Initial,p,px])
		}
		all py:Initial.passy[p] | {
			!in_passy[Goal,p,py] implies (passy_moven[Goal,Initial,p,py] or passy_moves[Goal,Initial,p,py])
		}
	}
	all t:Taxi,p:Pass | {
		all pnt:Initial.pint[p,t] | {
			!in_pint[Goal,p,t,pnt] implies (pint_pickup[Goal,Initial,p,t,pnt] or pint_dropoff[Goal,Initial,p,t,pnt])
		}
	}
	*/
} for 4 Int
