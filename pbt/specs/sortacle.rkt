#lang forge

/*
  Properties for Sortacle
    Adapted from properties from Toposortacle
    Use Ints instead of Chars to benefit from automatic ordering
*/

option verbosity 0
option sb 200000
option solver MiniSatProver -- was SAT4J -- minisat isn't avail on Windows
option logtranslation 2
option coregranularity 2
option core_minimization rce

-----------------------------
-- DO NOT CHANGE
-----------------------------

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


/*
run { 
    some t: seqPerson | {
        isSeqOf[t.r, Char]
        #t.r > 3
        one c: Char | { #indsOf[t.r, c] > 1 }
        idxOf[t.r, A] = 2
        #elems[t.r] = 5
        first[t.r] = B
    }
} for 6 Int, exactly 1 seqPerson
*/
// not working with Int as codomain

// unique spec
// using chars


-----------------------------
-- END DO NOT CHANGE
-----------------------------

sig Person {
  name: one Int,
  age: one Int
}

abstract sig seqPerson {
    sq: set Int -> Person
}

one sig OutSeq extends seqPerson {}
one sig InSeq extends seqPerson {}

-- to get interesting examples:

-- Note unlike toposort, in and out have same type, so just one indirection relation: sq

pred interesting[input: seqPerson, output: seqPerson] {
    #(input.sq) > 3
    #(output.sq) > 2    
    -- we want duplicates to be permitted
   -- not hasDups[input.sq]
}

-- to make sure in/out are seqs:

pred constrain[input: seqPerson, output: seqPerson] {
    isSeqOf[input.sq, Person]
    isSeqOf[output.sq, Person]
    input != output -- because disj isn't constraining yet TODO

    -- canonicity (prevent duplicate tests extracted from 'different' instances
    all p1, p2: Person | {p1 != p2 implies not equalPerson[p1, p2]}
    -- and full use (same reason)
    all p: Person | some sp : seqPerson | p in elems[sp.sq]
}

/*
  Properties (sort by /age/)
  Unless canonical, be careful not to use identity of Person atoms, use fields instead
*/

pred equalPerson[p1, p2: Person] {
  p1.age  = p2.age
  p1.name = p2.name
}

-- (1) if an element is in output, it must be mentioned in input
pred p1[input: seqPerson, output: seqPerson] {
    all e: elems[output.sq] | {
        some i2: inds[input.sq] | e = input.sq[i2] --equalPerson[e, input.sq[i2]]            
    }    
}

-- (2) if an element is in an input tuple, it must be mentioned in output
pred p2[input: seqPerson, output: seqPerson] {
    all e: elems[input.sq] | {
        some i2: inds[output.sq] | e = output.sq[i2] -- equalPerson[e, output.sq[i2]]            
    }  
}

-- (3) SORTED: for all output x, adjacencies <= by age
pred p3[input: seqPerson, output: seqPerson] {
    all disj i1, i2: inds[output.sq] | {
        sum[i1] <= sum[i2] implies sum[(output.sq[i1]).age] <= sum[(output.sq[i2]).age]
    }   
}

-- (4--5) Stronger (1+2): output is permutation of input
-- this is the "correct" version
-- note: count indexes, NOT elements (or dupes won't be counted)
pred p4[input: seqPerson, output: seqPerson] {
    all e: elems[output.sq] | {
        #{i: inds[output.sq] | output.sq[i] = e} --let p = output.sq[i] | equalPerson[p, e]}
        = #{i: inds[input.sq]  | input.sq[i] = e} -- let p = input.sq[i] | equalPerson[p, e]}
    }    
}
pred p5[input: seqPerson, output: seqPerson] {
    all e: elems[input.sq] | { -- don't forget input too
          #{i: inds[output.sq] | output.sq[i] = e} --let p = output.sq[i] | equalPerson[p, e]}
        = #{i: inds[input.sq]  | input.sq[i] = e} -- let p = input.sq[i] | equalPerson[p, e]}
    }    
}

-- (6) A misconception of the permutation property: lose nothing in count
pred p6[input: seqPerson, output: seqPerson] {
     #input.sq = #output.sq  
}


-- Cardinality is expensive in Forge, especially when dealing with large upper bounds.
-- So force a limit on the sequence relations' upper bounds
inst optimizerInstance {
  -- these are SEMANTIC; no in/out quantifier in pred
  InSeq = InSeq0
  OutSeq = OutSeq0
  -- Exactly 5 people in the world to pick from
  --Person = Person0 + Person1 + Person2 + Person3 + Person4
  Person in Person0 + Person1 + Person2 + Person3 + Person4
  -- Sequences cannot be longer than 5 elements
  -- Sequences contain only subsets of these 7 people
  sq in (InSeq0 + OutSeq0) -> (0+1+2+3) -> (Person0 + Person1 + Person2 + Person3 + Person4)
  -- ages are non-negative (and don't need more than 5 distinct ages; room for 1 new age)
  --age in Person -> (0+1+2+3+4) 
  age in (Person0 + Person1 + Person2 + Person3 + Person4) -> (0+1+2+3+4)
  -- name options are luring solver into same-age, different-name variations
  -- and yet name is never used in any properties
  name in (Person0 + Person1 + Person2 + Person3 + Person4) -> (0 + 1)
  
}


/*
  It is imperative that we have a handle that DEFINITELY is the input and
    another that DEFINITELY is the output. Allowing in/out types to be the same
    is therefore ill-advised. This particular script trusts that InSeq0 and OutSeq0
    are unique atoms in their appropriate subsigs.
*/
/*
run {    
    some inseq: InSeq, outseq: OutSeq | {        
        interesting[inseq, outseq]
        constrain[inseq, outseq]
       
        p1[inseq, outseq]
        p2[inseq, outseq]
        p3[inseq, outseq]
        p4[inseq, outseq]
        p5[inseq, outseq]
        p6[inseq, outseq]
    }
} for 4 Int, 5 Person, exactly 2 seqPerson for optimizerInstance
*/
-- 4 Int gives us [-8, 7] by default
-- this is unsat, but script is sat