// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module solves the finite domain type constraints generated for typing
// introduced attributes. The solver returns either a contradiction, an
// underconstrained domain map, or a solved assignment.

module UVL_TypeConstraintSolver {
  import opened Std.Collections.Seq
  import opened ExtLib.Option
  import opened ExtLib.SetToSeq
  import opened ExtLib.SeqMap
  import opened ExtLib.SeqSetUnion
  import opened UVL_Syntax
  import opened UVL_ModelsLevels

  // Small constraint language for introduced attribute typing. It captures
  // type equality between references and finite domain restrictions.
  datatype TypeConstraint =
    | TypeIn(reference: Reference, allowed: set<FeatureType>)
    | SameType(left: Reference, right: Reference)

  // Solver outcomes distinguish contradiction, underconstrained problem,
  // and a fully determined typing.
  datatype SolverResult =
    | Contradiction(domains: map<Reference, set<FeatureType>>)
    | Underconstrained(domains: map<Reference, set<FeatureType>>)
    | Solved(solution: map<Reference, FeatureType>)

  // Finite type universe used by the constraint solver.
  function AllTypes(): set<FeatureType>
  {
    {FTBoolean, FTInteger, FTReal, FTString}
  }

  function GetReferences(constraint: TypeConstraint): set<Reference>
  {
    match constraint
    case TypeIn(reference, _) => {reference}
    case SameType(left, right) => {left, right}
  }

  function ConstraintVariables(constraints: seq<TypeConstraint>): set<Reference>
  {
    Union(FMap(GetReferences, constraints))
  }

  // The solver starts every constrained reference with the full finite type
  // universe, then narrows those domains by propagation.
  function InitialDomains(constraints: seq<TypeConstraint>): map<Reference, set<FeatureType>>
    ensures forall reference :: reference in InitialDomains(constraints) <==> reference in ConstraintVariables(constraints)
    ensures forall reference :: reference in ConstraintVariables(constraints) ==> InitialDomains(constraints)[reference] == AllTypes()
  {
    map reference | reference in ConstraintVariables(constraints) :: AllTypes()
  }

  ghost predicate SameDomain<V1, V2>(left: map<Reference, V1>, right: map<Reference, V2>)
  {
    forall reference :: reference in left <==> reference in right
  }

  ghost predicate SatisfiesTypeConstraint(
    solution: map<Reference, FeatureType>,
    constraint: TypeConstraint
  )
  {
    match constraint
    case TypeIn(reference, allowed) =>
      reference in solution &&
      solution[reference] in allowed
    case SameType(left, right) =>
      left in solution &&
      right in solution &&
      solution[left] == solution[right]
  }

  ghost predicate SatisfiesTypeConstraints(
    solution: map<Reference, FeatureType>,
    constraints: seq<TypeConstraint>
  )
  {
    forall i :: 0 <= i < |constraints| ==> SatisfiesTypeConstraint(solution, constraints[i])
  }

  ghost predicate RespectsDomains(
    solution: map<Reference, FeatureType>,
    domains: map<Reference, set<FeatureType>>
  )
  {
    forall reference :: reference in solution && reference in domains ==> solution[reference] in domains[reference]
  }

  ghost predicate ChangeOn(
    references: seq<Reference>,
    before: map<Reference, set<FeatureType>>,
    after: map<Reference, set<FeatureType>>
  )
  {
    exists reference ::
      reference in references &&
      reference in before &&
      reference in after &&
      after[reference] != before[reference]
  }

  ghost predicate StableSingletonDomains(
    domains: map<Reference, set<FeatureType>>,
    constraint: TypeConstraint
  )
  {
    (forall reference :: reference in GetReferences(constraint) ==>
                           reference in domains) &&
    (forall reference :: reference in domains ==>
                           UniqueTypeIn(domains[reference]).Some?) &&
    ApplyConstraint(domains, constraint) == domains
  }

  // Returns the unique type in a singleton domain, and None otherwise.
  function UniqueTypeIn(domain: set<FeatureType>): option<FeatureType>
  {
    if domain == {FTBoolean} then
      Some(FTBoolean)
    else if domain == {FTInteger} then
      Some(FTInteger)
    else if domain == {FTReal} then
      Some(FTReal)
    else if domain == {FTString} then
      Some(FTString)
    else
      None
  }

  // UVL concretisation policy for residual solver domains. The only non
  // singleton domain accepted here is the numeric ambiguity between Integer
  // and Real.
  function ConcretiseDomain(domain: set<FeatureType>): option<FeatureType>
    ensures ConcretiseDomain(domain).Some? ==> ConcretiseDomain(domain).value in domain
  {
    if domain == {FTInteger, FTReal} then
      Some(FTReal)
    else
      UniqueTypeIn(domain)
  }

  method ConcretiseDomains(
    domains: map<Reference, set<FeatureType>>
  ) returns (result: option<map<Reference, FeatureType>>)
    ensures result.Some? ==> SameDomain(result.value, domains)
    ensures result.Some? ==> RespectsDomains(result.value, domains)
  {
    var solution: map<Reference, FeatureType> := map[];
    var unchecked: set<Reference> := set reference | reference in domains :: reference;
    while unchecked != {}
      invariant unchecked <= set reference | reference in domains :: reference
      invariant forall reference :: reference in solution <==> reference in domains && reference !in unchecked
      invariant forall reference :: reference in solution ==> solution[reference] in domains[reference]
      decreases |unchecked|
    {
      var reference: Reference :| reference in unchecked;
      var concreteType := ConcretiseDomain(domains[reference]);
      if concreteType.None? {
        result := None;
        return;
      }
      solution := solution[reference := concreteType.value];
      unchecked := unchecked - {reference};
    }
    result := Some(solution);
  }

  // Applies one local domain refinement step induced by a single constraint.
  function ApplyConstraint(
    domains: map<Reference, set<FeatureType>>,
    constraint: TypeConstraint
  ): map<Reference, set<FeatureType>>
    ensures SameDomain(domains, ApplyConstraint(domains, constraint))
    ensures forall reference :: reference in domains ==> ApplyConstraint(domains, constraint)[reference] <= domains[reference]
    ensures forall solution ::
              SatisfiesTypeConstraint(solution, constraint) &&
              RespectsDomains(solution, domains) ==>
                RespectsDomains(solution, ApplyConstraint(domains, constraint))
  {
    match constraint
    case TypeIn(reference, allowed) =>
      if reference in domains then
        domains[reference := domains[reference] * allowed]
      else
        domains
    case SameType(left, right) =>
      if left in domains && right in domains then
        var common := domains[left] * domains[right];
        domains[left := common][right := common]
      else
        domains
  }

  function PropagationRound(
    domains: map<Reference, set<FeatureType>>,
    constraints: seq<TypeConstraint>
  ): map<Reference, set<FeatureType>>
    ensures SameDomain(domains, PropagationRound(domains, constraints))
    ensures forall reference :: reference in domains ==> PropagationRound(domains, constraints)[reference] <= domains[reference]
    ensures forall solution ::
              SatisfiesTypeConstraints(solution, constraints) &&
              RespectsDomains(solution, domains) ==>
                RespectsDomains(solution, PropagationRound(domains, constraints))
    decreases |constraints|
  {
    if |constraints| == 0 then
      domains
    else
      PropagationRound(ApplyConstraint(domains, constraints[0]), constraints[1..])
  }

  function TheUniqueType(domain: set<FeatureType>): FeatureType
    requires UniqueTypeIn(domain).Some?
    ensures TheUniqueType(domain) in domain
  {
    UniqueTypeIn(domain).value
  }

  function SingletonSolution(domains: map<Reference, set<FeatureType>>): map<Reference, FeatureType>
    requires forall reference :: reference in domains ==> UniqueTypeIn(domains[reference]).Some?
    ensures SameDomain(domains, SingletonSolution(domains))
    ensures RespectsDomains(SingletonSolution(domains), domains)
    ensures forall reference :: reference in domains ==> SingletonSolution(domains)[reference] == TheUniqueType(domains[reference])
  {
    map reference | reference in domains :: TheUniqueType(domains[reference])
  }

  // Any satisfying assignment must define every reference mentioned by the
  // constraint sequence.
  lemma SatisfiesConstraintsDefineVars(
    solution: map<Reference, FeatureType>,
    constraints: seq<TypeConstraint>
  )
    requires SatisfiesTypeConstraints(solution, constraints)
    ensures forall reference :: reference in ConstraintVariables(constraints) ==>
                                  reference in solution
    decreases |constraints|
  {
    if |constraints| != 0 {
      SatisfiesConstraintsDefineVars(solution, constraints[1..]);
      forall reference | reference in ConstraintVariables(constraints)
        ensures reference in solution
      {
        if reference in GetReferences(constraints[0]) {
          match constraints[0]
          case TypeIn(head, _) =>
            assert reference == head;
            assert head in solution;
          case SameType(left, right) =>
            if reference == left {
              assert left in solution;
            } else {
              assert reference == right;
              assert right in solution;
            }
        }
      }
    }
  }

  // The following weight functions justify termination of propagation: every
  // strict narrowing removes at least one possible primitive type.
  ghost function DomainWeightOver(
    references: seq<Reference>,
    domains: map<Reference, set<FeatureType>>
  ): nat
    requires forall reference :: reference in references ==> reference in domains
    decreases |references|
  {
    if |references| == 0 then
      0
    else
      |domains[references[0]]| + DomainWeightOver(references[1..], domains)
  }

  ghost function DomainWeight(domains: map<Reference, set<FeatureType>>): nat
  {
    DomainWeightOver(Set2Seq(set reference | reference in domains :: reference), domains)
  }

  lemma StrictSubsetHasWitness(small: set<FeatureType>, large: set<FeatureType>)
    ensures small < large ==> exists featureType :: featureType in large - small
  {
    if small < large {
      if !(exists featureType :: featureType in large - small) {
        assert {:contradiction} forall featureType :: featureType in large ==> featureType in small by {
          forall featureType | featureType in large
            ensures featureType in small
          {
            if featureType !in small {
              assert {:contradiction} featureType in large - small;
            }
          }
        }
        assert {:contradiction} large <= small;
        assert {:contradiction} large == small;
      }
    }
  }

  lemma TypeSetWeightMonotone(small: set<FeatureType>, large: set<FeatureType>)
    ensures small <= large ==> |small| <= |large|
    decreases |large - small|
  {
    if small <= large {
      if small != large {
        StrictSubsetHasWitness(small, large);
        var featureType :| featureType in large - small;
        assert small + {featureType} <= large;
        assert |large - (small + {featureType})| < |large - small|;
        TypeSetWeightMonotone(small + {featureType}, large);
        assert featureType !in small;
        assert |small + {featureType}| == |small| + 1;
      }
    }
  }

  lemma TypeSetWeightStrictDecrease(small: set<FeatureType>, large: set<FeatureType>)
    ensures small < large ==> |small| < |large|
  {
    if small < large {
      StrictSubsetHasWitness(small, large);
      var featureType :| featureType in large - small;
      TypeSetWeightMonotone(small + {featureType}, large);
      assert featureType !in small;
      assert |small + {featureType}| == |small| + 1;
    }
  }

  lemma DomainWeightOverMonotone(
    references: seq<Reference>,
    before: map<Reference, set<FeatureType>>,
    after: map<Reference, set<FeatureType>>
  )
    requires forall reference :: reference in references ==> reference in before && reference in after
    requires forall reference :: reference in references ==> after[reference] <= before[reference]
    ensures DomainWeightOver(references, after) <= DomainWeightOver(references, before)
    decreases |references|
  {
    if |references| != 0 {
      TypeSetWeightMonotone(after[references[0]], before[references[0]]);
      DomainWeightOverMonotone(references[1..], before, after);
    }
  }

  lemma DomainWeightOverStrictDecrease(
    references: seq<Reference>,
    before: map<Reference, set<FeatureType>>,
    after: map<Reference, set<FeatureType>>
  )
    requires forall reference :: reference in references ==> reference in before && reference in after
    requires forall reference :: reference in references ==> after[reference] <= before[reference]
    ensures ChangeOn(references, before, after) ==> DomainWeightOver(references, after) < DomainWeightOver(references, before)
    decreases |references|
  {
    if ChangeOn(references, before, after) {
      assert |references| != 0;
      if after[references[0]] == before[references[0]] {
        DomainWeightOverStrictDecrease(references[1..], before, after);
      } else {
        TypeSetWeightStrictDecrease(after[references[0]], before[references[0]]);
        DomainWeightOverMonotone(references[1..], before, after);
      }
    }
  }

  lemma DomainWeightStrictDecrease(
    before: map<Reference, set<FeatureType>>,
    after: map<Reference, set<FeatureType>>
  )
    ensures
      SameDomain(before, after) &&
      (forall reference :: reference in before ==> after[reference] <= before[reference]) &&
      before != after ==>
        DomainWeight(after) < DomainWeight(before)
  {
    if SameDomain(before, after) &&
       (forall reference :: reference in before ==> after[reference] <= before[reference]) &&
       before != after
    {
      var references := Set2Seq(set reference | reference in before :: reference);
      assert forall reference :: reference in references ==> reference in before && reference in after;
      DomainWeightOverStrictDecrease(references, before, after);
      assert (set reference | reference in before :: reference) == (set reference | reference in after :: reference);
    }
  }

  lemma DomainWeightMonotone(
    before: map<Reference, set<FeatureType>>,
    after: map<Reference, set<FeatureType>>
  )
    ensures
      SameDomain(before, after) &&
      (forall reference :: reference in before ==> after[reference] <= before[reference]) ==>
        DomainWeight(after) <= DomainWeight(before)
  {
    if SameDomain(before, after) &&
       (forall reference :: reference in before ==> after[reference] <= before[reference])
    {
      var references := Set2Seq(set reference | reference in before :: reference);
      assert forall reference :: reference in references ==> reference in before && reference in after;
      DomainWeightOverMonotone(references, before, after);
      assert (set reference | reference in before :: reference) == (set reference | reference in after :: reference);
    }
  }

  // Repeatedly applies local refinements until a fixed point is reached.
  method PropagateConstraints(
    constraints: seq<TypeConstraint>,
    initialDomains: map<Reference, set<FeatureType>>
  ) returns (domains: map<Reference, set<FeatureType>>)
    ensures SameDomain(initialDomains, domains)
    ensures forall reference :: reference in initialDomains ==> domains[reference] <= initialDomains[reference]
    ensures PropagationRound(domains, constraints) == domains
    ensures forall solution ::
              SatisfiesTypeConstraints(solution, constraints) &&
              RespectsDomains(solution, initialDomains) ==>
                RespectsDomains(solution, domains)
  {
    domains := initialDomains;
    while true
      invariant SameDomain(initialDomains, domains)
      invariant forall reference :: reference in initialDomains ==> domains[reference] <= initialDomains[reference]
      invariant forall solution ::
                  SatisfiesTypeConstraints(solution, constraints) &&
                  RespectsDomains(solution, initialDomains) ==>
                    RespectsDomains(solution, domains)
      decreases DomainWeight(domains)
    {
      var nextDomains := PropagationRound(domains, constraints);
      assert forall reference :: reference in initialDomains ==> nextDomains[reference] <= domains[reference];
      assert forall reference :: reference in initialDomains ==> nextDomains[reference] <= initialDomains[reference];
      assert forall solution ::
          SatisfiesTypeConstraints(solution, constraints) &&
          RespectsDomains(solution, initialDomains) ==>
            RespectsDomains(solution, nextDomains);
      if nextDomains == domains {
        break;
      }
      DomainWeightStrictDecrease(domains, nextDomains);
      domains := nextDomains;
    }
  }

  // If a full propagation round is already a fixed point, the first constraint
  // in that round cannot change the domains either.
  lemma HeadConstraintFixedInFixedRound(
    domains: map<Reference, set<FeatureType>>,
    constraints: seq<TypeConstraint>
  )
    ensures
      |constraints| != 0 ==>
        PropagationRound(domains, constraints) == domains ==>
          ApplyConstraint(domains, constraints[0]) == domains
  {
    if |constraints| != 0 {
      if PropagationRound(domains, constraints) == domains {
        var headDomains := ApplyConstraint(domains, constraints[0]);
        if headDomains != domains {
          DomainWeightStrictDecrease(domains, headDomains);
          DomainWeightMonotone(headDomains, PropagationRound(headDomains, constraints[1..]));
          assert {:contradiction} false;
        }
      }
    }
  }

  // Once every domain is a singleton and one constraint no longer changes the
  // domains, the induced singleton assignment satisfies that constraint.
  lemma SingletonSolutionSatisfiesConstraint(
    domains: map<Reference, set<FeatureType>>,
    constraint: TypeConstraint
  )
    ensures StableSingletonDomains(domains, constraint) ==> SatisfiesTypeConstraint(SingletonSolution(domains), constraint)
  {
    if StableSingletonDomains(domains, constraint) {
      match constraint
      case TypeIn(reference, allowed) =>
        assert ApplyConstraint(domains, constraint)[reference] == domains[reference] * allowed;
        assert domains[reference] == domains[reference] * allowed;
        assert SingletonSolution(domains)[reference] in allowed;
      case SameType(left, right) =>
        assert ApplyConstraint(domains, constraint)[left] == domains[left] * domains[right];
        assert ApplyConstraint(domains, constraint)[right] == domains[left] * domains[right];
        assert domains[left] == domains[left] * domains[right];
        assert domains[right] == domains[left] * domains[right];
        assert domains[left] == domains[right];
    }
  }

  lemma SingletonSolutionSatisfiesConstraints(
    domains: map<Reference, set<FeatureType>>,
    constraints: seq<TypeConstraint>
  )
    requires PropagationRound(domains, constraints) == domains
    requires forall reference :: reference in ConstraintVariables(constraints) ==> reference in domains
    requires forall reference :: reference in domains ==> UniqueTypeIn(domains[reference]).Some?
    ensures SatisfiesTypeConstraints(SingletonSolution(domains), constraints)
    decreases |constraints|
  {
    if |constraints| != 0 {
      HeadConstraintFixedInFixedRound(domains, constraints);
      SingletonSolutionSatisfiesConstraint(domains, constraints[0]);
      SingletonSolutionSatisfiesConstraints(domains, constraints[1..]);
    }
  }

  // Solves constraints by iterating domain refinement to a fixed point. The
  // result is either a contradiction, a fully determined solution, or the
  // remaining domains when the problem is underconstrained.
  method SolveTypeConstraints(
    constraints: seq<TypeConstraint>
  ) returns (result: SolverResult)
    ensures result.Contradiction? ==> SameDomain(InitialDomains(constraints), result.domains)
    ensures result.Contradiction? ==> PropagationRound(result.domains, constraints) == result.domains
    ensures result.Contradiction? ==> exists reference :: reference in result.domains && result.domains[reference] == {}
    ensures result.Contradiction? ==> forall solution ::
                RespectsDomains(solution, InitialDomains(constraints)) ==>
                  !SatisfiesTypeConstraints(solution, constraints)
    ensures result.Solved? ==> RespectsDomains(result.solution, InitialDomains(constraints))
    ensures result.Solved? ==> SatisfiesTypeConstraints(result.solution, constraints)
    ensures result.Underconstrained? ==> SameDomain(InitialDomains(constraints), result.domains)
    ensures result.Underconstrained? ==> PropagationRound(result.domains, constraints) == result.domains
    ensures result.Underconstrained? ==> forall reference :: reference in result.domains ==> result.domains[reference] != {}
    ensures result.Underconstrained? ==> exists reference :: reference in result.domains && !UniqueTypeIn(result.domains[reference]).Some?
    ensures result.Underconstrained? ==> forall solution ::
                SatisfiesTypeConstraints(solution, constraints) &&
                RespectsDomains(solution, InitialDomains(constraints)) ==>
                  RespectsDomains(solution, result.domains)
  {
    var domains := InitialDomains(constraints);
    domains := PropagateConstraints(constraints, domains);

    if exists reference :: reference in domains && domains[reference] == {} {
      var badRef :| badRef in domains && domains[badRef] == {};
      assert forall solution :: RespectsDomains(solution, InitialDomains(constraints)) ==> !SatisfiesTypeConstraints(solution, constraints) by {
        forall solution | RespectsDomains(solution, InitialDomains(constraints))
          ensures !SatisfiesTypeConstraints(solution, constraints)
        {
          if SatisfiesTypeConstraints(solution, constraints) {
            SatisfiesConstraintsDefineVars(solution, constraints);
            assert {:contradiction} badRef in solution;
            assert {:contradiction} false;
          }
        }
      }
      result := Contradiction(domains);
    } else if forall reference :: reference in domains ==> UniqueTypeIn(domains[reference]).Some? {
      var solution := SingletonSolution(domains);
      SingletonSolutionSatisfiesConstraints(domains, constraints);
      result := Solved(solution);
    } else {
      result := Underconstrained(domains);
    }
  }
}
