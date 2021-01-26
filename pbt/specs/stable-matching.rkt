#lang forge

--option verbose 10
--option solver MiniSatProver
--option logtranslation 2
--option coregranularity 0
--option solver MiniSat -- TODO: this seems to produce duplicate solns sometimes??
option sb 2000
--option skolemization 0

pred isSeqOf[r1: set Int -> univ, d: set univ] {
    r1 in Int -> univ
    r1[Int] in d
    all i1: r1.univ | sum[i1] >= 0
    all i1: r1.univ | {
        sum[i1] >= 0 =>
        lone r1[i1]
    }
    all e: r1[Int] | some r1.e
    all i1: (r1.univ - sing[0]) | { some r1[sing[subtract[sum[i1], 1]]] }
}

fun first[r: set Int -> univ]: univ {
    r[sing[0]]
}

fun last[r: set Int -> univ]: univ {
    r[sing[subtract[#r, 1]]]
}

fun indsOf[r: set Int -> univ, e: set univ]: set Int {
    r.e
}

fun idxOf[r: set Int -> univ, e: set univ]: Int {
    min[r.e]
}

fun lastIdxOf[r: set Int -> univ, e: set univ]: Int {
    max[r.e]
}

fun elems[r: set Int -> univ]: set r[Int] {
    r[Int]
}

fun inds[r: set Int -> univ]: set Int {
    r.univ
}

pred isEmpty[r: set Int -> univ] {
    no r
}

pred hasDups[r: set Int -> univ] {
    some e: elems[r] | {
        #(indsOf[r, e]) > 1
    }
}

// stable matching spec

// Person/Company are ListOf Ints that refer to index
/*
abstract sig Ind {}
one sig n0 extends Ind {}
one sig n1 extends Ind {}
one sig n2 extends Ind {}
one sig n3 extends Ind {}
*/

sig seqPerson {
    r1: set Int -> Person
}

sig seqCompany {
    r2: set Int -> Company
}

-- 5 people, 5 companies
-- person1 : '(3 4 2 1 5)
-- company1 : '(4 3 2 1 5)
-- InputPair : '(person1 person2 ...) x '(company1 ...)
-- Hires     : '((p1 . c1) (p3 . c5) ...)

sig Person {
    cprefs: one seqCompany --set Int -> Ind
}

sig Company {
    pprefs: one seqPerson --set Int -> Ind
}

sig InputPair {    
    seqP: one seqPerson,
    seqC: one seqCompany
}

-- output
sig Hires {
    m: set Person -> Company
}

one sig In extends InputPair {}
one sig Out extends Hires {}

fun pdomain[input: InputPair]: set Person { elems[input.seqP.r1] }
fun cdomain[input: InputPair]: set Company { elems[input.seqC.r2] }

-- error for checking highlighting
--pred cdomain[input: InputPair] { elems[input.seqC.r2] } -- wrong

pred interesting[input: InputPair, output: Hires] {
    let interestingSize = 0 | { -- changed for differing sizes
        #(input.seqP).r1 > interestingSize
        #(input.seqC).r2 > interestingSize
        #((((input.seqP).r1)[Int]).cprefs).r2 > interestingSize
        #((((input.seqC).r2)[Int]).pprefs).r1 > interestingSize
    }
}

pred constrain[input: InputPair, output: Hires] {
    -- NOTE WELL: do not put constraints on output here, just input assumptions

    -- require same number of people requesting matches as companies requesting matches
    -- constrain number of participants
    #pdomain[input] = #cdomain[input]
    -- constrain preferences per participant to be exactly the other group of participants
    all p: pdomain[input] | elems[p.cprefs.r2] = cdomain[input]
    all c: cdomain[input] | elems[c.pprefs.r1] = pdomain[input]

    all seqP: seqPerson | {
        isSeqOf[seqP.r1, Person]
        -- disallows outputs with previously unseen people
        --   (side effect of not using integer indices directly)
        -- elems[seqP.r1] = Person
        
        -- too weak, allows duplicates
        -- #(seqP.r1) = #Person

        -- no duplicate entries
        all p: Person | lone seqP.r1.p 
    }

    all seqC: seqCompany | {
        isSeqOf[seqC.r2, Company]
       -- disallows outputs with previously unseen companies
       --   (side effect of not using integer indices directly)
       -- elems[seqC.r2] = Company
       
       -- too weak, allows duplicates
       -- #(seqC.r2) = #Company

        -- no duplicate entries
        all c: Company | lone seqC.r2.c
    }
}

-- TOTALITY (every input person/company gets matched if they are in input)
--  Was these, but too strong
    --all p: pdomain[input] | some c: cdomain[input] | c in output.m[p]
    --all c: cdomain[input] | some p: pdomain[input] | p in (output.m).c

-- ***** NOTE:
-- If we divide these up, there's interference!
--   because the nature of the other properties implies if one P isn't matched, some C isn't matched either
pred p1[input: InputPair, output: Hires] {       
    all p: pdomain[input] | some output.m[p]
}
pred p2[input: InputPair, output: Hires] {       
    all c: cdomain[input] | some (output.m).c   
}

-- STABILITY (weakened slightly; see notes)
pred negp3[input: InputPair, output: Hires] {    
    some cheaterPerson: pdomain[input], cheaterCompany: cdomain[input] | {
        -- "I'm not matched with the other cheater"
        cheaterPerson -> cheaterCompany not in output.m
        -- Without these weakening antecedents, p2+p3 implies p1, since then if a person
        --  is unmatched a company must also be unmatched. Here we release unmatched people
        --  from the obligation.
        some cheaterPerson.(output.m) implies {
            all c2: cheaterPerson.(output.m) | {
                -- "I prefer the other cheater to everyone I'm matched with"
                idxOf[(cheaterPerson.cprefs.r2), cheaterCompany]
                <
                idxOf[(cheaterPerson.cprefs.r2), c2]
            }
        }
        some (output.m).cheaterCompany implies {
            all p2: (output.m).cheaterCompany | {
                -- "I prefer the other cheater to everyone I'm matched with"
                idxOf[(cheaterCompany.pprefs.r1), cheaterPerson]
                <
                idxOf[(cheaterCompany.pprefs.r1), p2]
            }
        }
    }
}
pred p3[input: InputPair, output: Hires] {
    not negp3[input, output]
}

------------------------------------------------------------
-- FUNCTIONALITY: nobody has >1 match
pred negp4[input: InputPair, output: Hires] {
    some p: pdomain[input], c: cdomain[input] | {
        #(p.(output.m)) > 1 
        or
        #((output.m).c) > 1
    }
}
pred p4[input: InputPair, output: Hires] {
    not negp4[input, output]
}

------------------------------------------------------------
-- DOMAIN RESPECTED: everything matched is present in the input
pred p5[input: InputPair, output: Hires] {
    -- output.m is in Person -> Company
    all c : (output.m)[Person]  | c in elems[input.seqC.r2]    
}
pred p6[input: InputPair, output: Hires] {    
    all p : (output.m).Company | p in elems[input.seqP.r1]  
}

-- to enable, add "test" to start of line
expect {
    nonexhaustive_allprop: {
        interesting[In, Out]
        constrain[In, Out]
        p1[In, Out]
        p2[In, Out]
        p3[In, Out]
        p4[In, Out]
        p5[In, Out]
        p6[In, Out]
        some p: Person  | p not in pdomain[In]
        some c: Company | c not in cdomain[In]
    } for 6 Int, exactly 1 InputPair, exactly 1 Hires,
      exactly 5 Person, exactly 5 Company
      is sat
}

/*
foo: run {
    interesting[In, Out]
    constrain[In, Out]
    p1[In, Out]
    p2[In, Out]
    p3[In, Out]
    p4[In, Out]
    p5[In, Out]
    p6[In, Out] 
} for 6 Int, exactly 1 InputPair, exactly 1 Hires,
    exactly 5 Person, exactly 5 Company -- identifiers, not necessarily used
*/
--(evaluate  foo (stream-first (forge:Run-result foo)) (join cprefs r2))

