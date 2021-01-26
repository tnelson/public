#lang forge

/*
  Properties for LfS toposortacle
  Tim and Sam
*/

--option verbosity 10

abstract sig Char {}

one sig n1 extends Char {}
one sig n2 extends Char {}
one sig n3 extends Char {}
one sig n4 extends Char {}
one sig n5 extends Char {}
one sig n6 extends Char {}
one sig n7 extends Char {}
one sig n8 extends Char {}
one sig n9 extends Char {}
one sig n0 extends Char {}

-----------------------------
-- DO NOT CHANGE
-----------------------------
-- Cheating a bit: bound on PairChar must be large enough...
-- Ideally we'd nest sequences here with constraints (TODO)

sig PairChar {
  f: one Char,
  s: one Char
}

sig seqPairChar {
  inR: set Int -> PairChar 
}

sig seqChar {
    outR: set Int -> Char
}

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
    some t: seqChar | {
        isSeqOf[t.r, Char]
        #t.r > 3
        one c: Char | { #indsOf[t.r, c] > 1 }
        idxOf[t.r, A] = 2
        #elems[t.r] = 5
        first[t.r] = B
    }
} for 6 Int, exactly 1 seqChar
*/
// not working with Int as codomain

// unique spec
// using chars


-----------------------------
-- END DO NOT CHANGE
-----------------------------

-- to get interesting examples:

pred interesting[input: seqPairChar, output: seqChar] {
    #(input.inR) > 3
    #output.outR > 2
    not hasDups[input.inR]
}

pred isDAG[pairs: set PairChar] {
    -- Build the relation the pairs embody and take its transitive closure
    no iden & ^{node1, node2: Char | some apair : pairs | apair.f = node1 and apair.s = node2}
}

pred constrain[input: seqPairChar, output: seqChar] {
    isSeqOf[input.inR, PairChar]
    isSeqOf[output.outR, Char]

    -- canonicity: disallow 2 PairChars to have the same values
    --   (this is an effort to prevent isomorphic instances that Kodkod doesn't catch
    all pc1, pc2: PairChar | {
        pc1 != pc2 implies {pc1.f != pc2.f or pc1.s != pc2.s}
    }

    -- forbid unused PairChars (same reason as above)
    all pc: PairChar | {
        some spc: seqPairChar | pc in elems[spc.inR]
    }
    
    -- Must satisfy precondition
    --   Not only is it unfair to omit this, but student implementations may have undefined behavior
    --   like looping forever...
    isDAG[elems[input.inR]]
}

/*
  Properties (these do not exactly echo the Programming '21 paper's):

*/
-- (1) if an element is in output, it must be mentioned in an input tuple
pred p1[input: seqPairChar, output: seqChar] {
    all e: elems[output.outR] | {
        some i2: inds[input.inR] | {
            (input.inR[i2]).f = e or (input.inR[i2]).s = e
        }
    }
    
}

-- (2) if an element is in an input tuple, it must be mentioned in output
pred p2[input: seqPairChar, output: seqChar] {
    all e: (elems[input.inR].f + elems[input.inR].s) | {
        some i: (output.outR).univ | {output.outR[i] = e }
    }
}

-- (3) output elements unique in output
pred p3[input: seqPairChar, output: seqChar] {
    --all i1,j: inds[output.r] | sum[i1] < sum[j] => {
     --   idxOf[input.r, output.r[i1]] <= idxOf[input.r, output.r[j]]
    --}
    -- TODO disj support in expander
    all i1, i2: inds[output.outR] | i1 != i2 implies output.outR[i1] != output.outR[i2]
}

-- (4) for all input tuples (x,y), idx[x] <= idx[y] in output
pred p4[input: seqPairChar, output: seqChar] {
    all inpair: elems[input.inR] | {
        idxOf[output.outR, inpair.f] < idxOf[output.outR, inpair.s]
    }
   --idxOf[output.r, e] = lastIdxOf[output.r, e]
}

-- (5) misconception subproperty:
--    same output size as unique entries in input
pred p5[input: seqPairChar, output: seqChar] {
    #(output.outR) = #{c: Char | c in elems[input.inR].f + elems[input.inR].s}
   
}

/*
pred goodinput[input: seqChar] {
    #input.r >= 7
    all e: elems[input.r] | #(indsOf[input.r, e]) <= 3
}
*/

inst optimizerInstance {
  seqChar = OutSeq
  seqPairChar = InSeq
  -- "in" to avoid exact-bounding and forcing unused PairChars
  PairChar in PairChar0 + PairChar1 + PairChar2 + PairChar3 + PairChar4 + PairChar5
  --Char = n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9
  -- Sequences cannot be longer than 4 elements     
  inR in seqPairChar -> (0+1+2+3) -> (PairChar0 + PairChar1 + PairChar2 + PairChar3 + PairChar4 + PairChar5)
  outR in seqChar -> (0+1+2+3) -> (n00 + n10 + n20 + n30 + n40 + n50 + n60 + n70 + n80 + n90)
}

--option solver MiniSatProver
--option core_minimization rce
--option logtranslation 1
--option verbose 1

/*
run {
    some i: seqPairChar, o: seqChar | {
      
        interesting[i, o]
        constrain[i, o]
       
        p1[i, o]
        p2[i, o]
        p3[i, o]
        p4[i, o]
        p5[i, o]
    }
} for 10 Char, 6 PairChar, 5 Int for optimizerInstance
-- ^ MUST provide PairChar bound
*/

