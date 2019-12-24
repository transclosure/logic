sig Sex {}
one sig Female,Male extends Sex {}
sig DOW {}
one sig Sun,Mon,Tue,Wed,Thur,Fri,Sat extends DOW {}
sig Whale {
	sex : one Sex,
	born : one DOW
}
one sig Eldest extends Whale {}
one sig Youngest extends Whale {}

pred AtLeastOneMaleBornWed {some w:Whale | w.sex = Male and w.born = Wed}
pred BothMale {Eldest.sex = Male and Youngest.sex = Male}
-- what is P(BothMale|Priors)?
run NoPriors {} for exactly 2 Whale, 2 Sex, 7 DOW
run GivenEldestMale {Eldest.sex = Male} for exactly 2 Whale, 2 Sex, 7 DOW
run GivenAtLeastOneMale {some w:Whale | w.sex = Male} for exactly 2 Whale, 2 Sex, 7 DOW
-- 14 / 28 (should be 13 / 27, i think oak's stuff is still enabled...)
run LikelihoodAndPrior {(BothMale implies AtLeastOneMaleBornWed) and BothMale} for exactly 2 Whale, 2 Sex, 7 DOW
run Evidence {AtLeastOneMaleBornWed} for exactly 2 Whale, 2 Sex, 7 DOW

/* Thoughts */
-- T = event (sig) ontology and relationships between events (facts)
-- Mod(T) (w/ eval, or two commands) = classical probability calculation via enumeration 
-- Thy(Mod(T))? = probability approximation?
-- only minimal models = discrete math
-- approximate probability = approximate discrete cone size?
-- sex and born are independent, how to ignore if independent of probability calculation? (fragment spec?)
-- if they are independent, models in cone of born Monday should be the same as ones in born Tuesday, etc (best way to derive?)
-- there has to be a way to do these things apriori, we have things likes Bayes' rule
