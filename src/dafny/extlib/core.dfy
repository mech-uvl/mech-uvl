// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

module ExtLib {

  module Option {

    datatype option<T> =
      | Some(value: T)
      | None

  }

  module Algebra {

    ghost predicate LeftIdentity<T(!new)>(f: (T,T)-> T, neutral: T){
      forall x: T :: f(neutral, x) == x
    }

    ghost predicate RightIdentity<T(!new)>(f: (T,T)-> T, neutral: T){
      forall x: T :: f(x, neutral) == x
    }

    ghost predicate Assoc<T(!new)>(f: (T,T)-> T){
      forall x, y, z: T :: f(x, (f(y, z))) == f(f(x, y), z)
    }

  }


  /*
    module SeqFoldRight {
  
      function FoldR<T, U>(f: (T, U) -> U, init: U, s: seq<T>): U
        decreases |s|
      {
        if |s| == 0 then
          init
        else
          f(s[0], FoldR(f, init, s[1..]))
      }
  
      lemma FoldApp<T,U>(f: (T, U) -> U, init: U, s1: seq<T>, s2: seq<T>)
        ensures FoldR(f, init, s1+s2) == FoldR(f, FoldR(f, init, s2), s1)
      {
        if |s1| == 0 {
          assert s1+s2 == s2;
        } else {
          assert (s1+s2)[0] == s1[0];
          assert (s1+s2)[1..] == s1[1..] + s2;
          calc {
            FoldR(f, init, s1+s2);
          == { }
            f(s1[0], FoldR(f, init, s1[1..]+s2));
          == { FoldApp(f, init, s1[1..], s2); }
            f(s1[0], FoldR(f, FoldR(f, init, s2), s1[1..]));
          }
        }
      }
  */

  module SeqProperties {
    import opened S = Std.Collections.Seq
    import opened Algebra

    lemma FoldAppAssoc<T(!new)> (s1: seq<T>, s2: seq<T>, init: T, f: (T, T) -> T)
      requires LeftIdentity(f, init)
      requires Assoc(f)
      ensures FoldRight(f, s1+s2, init) == f(FoldRight(f, s1, init), FoldRight(f, s2, init))
    {
      if |s1| == 0 {
        calc {
          FoldRight(f, s1+s2, init);
        == { assert [] + s2 == s2; }
          FoldRight(f, s2, init);
        == { }
          f(init, FoldRight(f, s2, init));
        == {}
          f(FoldRight(f, s1, init), FoldRight(f, s2, init));
        }
      } else {
        FoldAppAssoc(s1[1..], s2, init, f);
        assert (s1+s2)[0] == s1[0];
        assert (s1+s2)[1..] == s1[1..]+s2;
        calc {
          FoldRight(f, s1+s2, init);
        == {}
          f(s1[0], FoldRight(f, s1[1..]+s2, init));
        == {}
          f(s1[0], f(FoldRight(f, s1[1..], init), FoldRight(f, s2, init)));
        == {}
          f(FoldRight(f, s1, init), FoldRight(f, s2, init));
        }
      }
    }

  }



  module SeqMap {
    import opened Std.Collections.Seq
    import opened SeqProperties

    function FMap<A,B>(f: A->B, s: seq<A>): seq<B>{
      if |s| == 0
      then []
      else [f(s[0])] + FMap(f, s[1..])
    }

    lemma FMapApp<A,B>(f: A->B, s1: seq<A>, s2:seq<A>)
      ensures FMap(f, s1+s2) == FMap(f, s1) + FMap(f, s2)
    {
      if |s1| == 0 {
        assert s1+s2 == s2;
      } else {
        assert (s1+s2)[0] == s1[0];
        assert (s1+s2)[1..] == s1[1..]+s2;
        FMapApp(f, s1[1..], s2);
      }
    }

    lemma FMapExt<A,B>(s: seq<A>, f1: A->B, f2: A->B)
      requires forall x :: x in s ==> f1(x) == f2(x)
      ensures FMap(f1, s) == FMap(f2, s)
    {
      if |s| == 0 {
      } else {
        FMapExt(s[1..], f1, f2);
      }
    }

    lemma FMapFMap<A,B,C>(f: A->B, g: B->C, s: seq<A>)
      ensures FMap(g, FMap(f, s)) == FMap((x: A) => g(f(x)), s)
    {
      if |s| == 0 {
      } else {
        FMapFMap(f, g, s[1..]);
      }
    }

    lemma FoldMapLeft<A,B,C>(f: (A, B)->A, g:C->B, s: seq<C>, init: A)
      ensures FoldLeft(f, init, FMap(g, s)) == FoldLeft((a, c) => f(a, g(c)), init, s)
    {
      if |s| == 0 {
      } else {
        FoldMapLeft(f, g, s[1..], f(init, g(s[0])));
      }
    }

  }

  module Sum {

    module EInt {
      import opened Std.Collections.Seq
      import opened Algebra

      // Sum on integers
      function sum(numbers: seq<int>): int {
        FoldRight((x,y)=>(x+y), numbers, 0)
      }

      lemma sumHd(xs: seq<int>)
        requires (|xs| > 0)
        ensures sum(xs) == xs[0] + sum(xs[1..])
      {}

      lemma LeftIdentityAdd0()
        ensures LeftIdentity((x,y)=>(x+y), 0)
      {}

      lemma AssocAdd()
        ensures Assoc<int>((x,y)=>(x+y))
      {}
    }

    module Float {
      import opened Std.Collections.Seq
      import opened Algebra

      // Sum on real numbers
      function sum(numbers: seq<real>): real {
        FoldRight((x,y)=>(x+y), numbers, 0.)
      }

      lemma sumHd(xs: seq<real>)
        requires (|xs| > 0)
        ensures sum(xs) == xs[0] + sum(xs[1..])
      {}

      lemma LeftIdentityAdd0()
        ensures LeftIdentity((x,y)=>(x+y), 0.0)
      {}

      lemma AssocAdd()
        ensures Assoc<real>((x,y)=>(x+y))
      {}

    }

    module Nat {
      import opened Std.Collections.Seq
      import opened Algebra

      // Sum on natural numbers
      function sum(numbers: seq<nat>): nat {
        FoldRight((x,y)=>(x+y), numbers, 0)
      }

      lemma sumHd(xs: seq<nat>)
        requires (|xs| > 0)
        ensures sum(xs) == xs[0] + sum(xs[1..])
      {}

      lemma LeftIdentityAdd0()
        ensures LeftIdentity((x,y)=>(x+y), 0)
      {}

      lemma AssocAdd()
        ensures Assoc<nat>((x,y)=>(x+y))
      {}
    }

  }

  module SeqNoDup {

    function HasNoDup<T(==)>(xs: seq<T>): bool
      decreases |xs|
    {
      if |xs| == 0 then true
      else xs[0] !in xs[1..] && HasNoDup(xs[1..])
    }

  }

  module SetToSeq {

    ghost function Set2Seq<T(!new)>(s: set<T>): seq<T>
      ensures forall x :: x in s <==> x in Set2Seq(s)
      ensures |Set2Seq(s)| == |s|
      decreases |s|
    {
      if s == {} then
        []
      else
        var x :| x in s;
        [x] + Set2Seq(s - {x})
    }

  }

  module SeqMapMerge {
    import opened Std.Collections.Seq

    function Merge<A,B>(chunks: seq<map<A, B>>): map<A, B>
    {
      FoldRight((chunk, acc) => chunk + acc, chunks, map[])
    }

  }

  module SeqSetUnion {
    import opened Std.Collections.Seq

    function Union<A>(sets: seq<set<A>>): set<A>
    {
      FoldRight((s1,s2)=>s1+s2, sets, {})
    }

  }

}
