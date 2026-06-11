// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

module ExtLib {

  module Option {

    datatype option<T> =
      | Some(value: T)
      | None

  }

  module SeqFold {

    function sfold<T, U>(f: (T, U) -> U, init: U, s: seq<T>): U
      decreases |s|
    {
      if |s| == 0 then
        init
      else
        f(s[0], sfold(f, init, s[1..]))
    }

    lemma FoldApp<T,U>(f: (T, U) -> U, init: U, s1: seq<T>, s2: seq<T>)
      ensures sfold(f, init, s1+s2) == sfold(f, sfold(f, init, s2), s1)
    {
      if |s1| == 0 {
        assert s1+s2 == s2;
      } else {
        assert (s1+s2)[0] == s1[0];
        assert (s1+s2)[1..] == s1[1..] + s2;
        calc {
          sfold(f, init, s1+s2);
        == { }
          f(s1[0], sfold(f, init, s1[1..]+s2));
        == { FoldApp(f, init, s1[1..], s2); }
          f(s1[0], sfold(f, sfold(f, init, s2), s1[1..]));
        }
      }
    }

    // Algebraic properties needed for lemmas on sfold
    ghost predicate LeftIdentity<T(!new)>(f: (T,T)-> T, neutral: T){
      forall x: T :: f(neutral, x) == x
    }

    ghost predicate RightIdentity<T(!new)>(f: (T,T)-> T, neutral: T){
      forall x: T :: f(x, neutral) == x
    }

    ghost predicate Assoc<T(!new)>(f: (T,T)-> T){
      forall x, y, z: T :: f(x, (f(y, z))) == f(f(x, y), z)
    }

    lemma FoldAppAssoc<T(!new)> (s1: seq<T>, s2: seq<T>, init: T, f: (T, T) -> T)
      requires LeftIdentity(f, init)
      requires Assoc(f)
      ensures sfold(f, init, s1+s2) == f(sfold(f, init, s1), sfold(f, init, s2))
    {
      if |s1| == 0 {
        calc {
          sfold(f, init, s1+s2);
        == { assert [] + s2 == s2; }
          sfold(f, init, s2);
        == { }
          f(init, sfold(f, init, s2));
        == {}
          f(sfold(f, init, s1), sfold(f, init, s2));
        }
      } else {
        FoldAppAssoc(s1[1..], s2, init, f);
        assert (s1+s2)[0] == s1[0];
        assert (s1+s2)[1..] == s1[1..]+s2;
        calc {
          sfold(f, init, s1+s2);
        == {}
          f(s1[0], sfold(f, init, s1[1..]+s2));
        == {}
          f(s1[0], f(sfold(f, init, s1[1..]), sfold(f, init, s2)));
        == {}
          f(sfold(f, init, s1), sfold(f, init, s2));
        }
      }
    }
  }

  module SeqFoldLeft {

    function sfoldl<T, U>(f: (U, T) -> U, init: U, s: seq<T>): U
      decreases |s|
    {
      if |s| == 0 then
        init
      else
        sfoldl(f, f(init, s[0]), s[1..])
    }

    lemma FoldApp<T,U>(f: (U, T) -> U, init: U, s1: seq<T>, s2: seq<T>)
      ensures sfoldl(f, init, s1+s2) == sfoldl(f, sfoldl(f, init, s1), s2)
    {
      if |s1| == 0 {
        assert s1+s2 == s2;
      } else {
        assert (s1+s2)[0] == s1[0];
        assert (s1+s2)[1..] == s1[1..] + s2;
        FoldApp(f, f(init, s1[0]), s1[1..], s2);
      }
    }
  }

  module SeqMap {
    import opened SeqFoldLeft

    function smap<A,B>(f: A->B, s: seq<A>): seq<B>{
      if |s| == 0
      then []
      else [f(s[0])] + smap(f, s[1..])
    }

    lemma MapApp<A,B>(f: A->B, s1: seq<A>, s2:seq<A>)
      ensures smap(f, s1+s2) == smap(f, s1) + smap(f, s2)
    {
      if |s1| == 0 {
        assert s1+s2 == s2;
      } else {
        assert (s1+s2)[0] == s1[0];
        assert (s1+s2)[1..] == s1[1..]+s2;
        MapApp(f, s1[1..], s2);
      }
    }

    lemma MapExt<A,B>(s: seq<A>, f1: A->B, f2: A->B)
      requires forall x :: x in s ==> f1(x) == f2(x)
      ensures smap(f1, s) == smap(f2, s)
    {
      if |s| == 0 {
      } else {
        MapExt(s[1..], f1, f2);
      }
    }

    lemma MapMap<A,B,C>(f: A->B, g: B->C, s: seq<A>)
      ensures smap(g, smap(f, s)) == smap((x: A) => g(f(x)), s)
    {
      if |s| == 0 {
      } else {
        MapMap(f, g, s[1..]);
      }
    }

    lemma FoldMapLeft<A,B,C>(f: (A, B)->A, g:C->B, s: seq<C>, init: A)
      ensures sfoldl(f, init, smap(g, s)) == sfoldl((a, c) => f(a, g(c)), init, s)
    {
      if |s| == 0 {
      } else {
        FoldMapLeft(f, g, s[1..], f(init, g(s[0])));
      }
    }

  }

  module ForAll {
    import opened SeqFold

    // A computable forall on sequences
    function ForAll<T>(p: T->bool, s: seq<T>) : bool
    {
      sfold((e, t)=> p(e) && t, true, s)
    }

    lemma ForAll_forall<T>(s: seq<T>, p: T->bool)
      ensures (forall i :: 0 <= i < |s| ==>p(s[i])) <==> ForAll(p, s)
    {
      if |s| == 0 {
      } else {
        ForAll_forall(s[1..], p);
      }
    }
  }

  module Sum {

    module EInt {
      import opened SeqFold

      // Sum on integers
      function sum(numbers: seq<int>): int {
        sfold((x,y)=>(x+y), 0, numbers)
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
      import opened SeqFold

      // Sum on real numbers
      function sum(numbers: seq<real>): real {
        sfold((x,y)=>(x+y), 0., numbers)
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
      import opened SeqFold

      // Sum on natural numbers
      function sum(numbers: seq<nat>): nat {
        sfold((x,y)=>(x+y), 0, numbers)
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

    ghost function set2seq<T(!new)>(s: set<T>): seq<T>
      ensures forall x :: x in s <==> x in set2seq(s)
      ensures |set2seq(s)| == |s|
      decreases |s|
    {
      if s == {} then
        []
      else
        var x :| x in s;
        [x] + set2seq(s - {x})
    }

  }

  module SeqMapMerge {
    import opened SeqFold

    function Merge<A,B>(chunks: seq<map<A, B>>): map<A, B>
    {
      sfold((chunk, acc) => chunk + acc, map[], chunks)
    }

  }

  module SeqSetUnion {
    import opened SeqFoldLeft

    function Union<A>(sets: seq<set<A>>): set<A>
    {
      sfoldl((s1,s2)=>s1+s2, {}, sets)
    }
  }

}
