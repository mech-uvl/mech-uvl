// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines the ordering and constructors for UVL language levels.
// It covers major levels, minor levels, declared-level projections, and
// joins of required levels. Other modules use these definitions to state
// level requirements and to compute explicit `includes` declarations.

module UVL_Levels {
  import opened ExtLib.Option
  import opened ExtLib.SeqFoldLeft
  import opened ExtLib.SeqMap
  import opened UVL_Syntax


  // Order on major levels
  function Le(lvl_l: MajorLevel, lvl_r: MajorLevel): bool
  {
    match (lvl_l, lvl_r)
    case (BooleanLevel, _) => true
    case (ArithmeticLevel, BooleanLevel) => false
    case (ArithmeticLevel, _) => true
    case (TypeLevel, TypeLevel) => true
    case (TypeLevel, _) => false
  }

  function MaxLevel(lvl_l: MajorLevel, lvl_r: MajorLevel): MajorLevel
  {
    if Le(lvl_l, lvl_r) then lvl_r else lvl_l
  }

  function MinorMajor(minor: MinorLevel): MajorLevel
  {
    match minor
    case GroupCardinalityLevel => BooleanLevel
    case AggregateFunctionLevel => ArithmeticLevel
    case FeatureCardinalityLevel => ArithmeticLevel
    case StringConstraintsLevel => TypeLevel
  }

  function Minors(major: MajorLevel): set<MinorLevel>
  {
    match major
    case BooleanLevel => {GroupCardinalityLevel}
    case ArithmeticLevel => {AggregateFunctionLevel, FeatureCardinalityLevel}
    case TypeLevel => {StringConstraintsLevel}
  }

  function AllMinors(): set<MinorLevel>
  {
    {GroupCardinalityLevel, AggregateFunctionLevel, FeatureCardinalityLevel, StringConstraintsLevel}
  }

  function MaxMajor(levels: seq<MajorLevel>): MajorLevel
  {
    sfoldl(MaxLevel, BooleanLevel, levels)
  }

  predicate ValidLevel(level: LanguageLevel)
  {
    match level.minor
    case None => true
    case Some(AnyMinorLevel) => true
    case Some(ExactMinorLevel(minor)) => level.major == MinorMajor(minor)
  }

  predicate ValidLevels(levels: seq<LanguageLevel>)
  {
    forall i :: 0 <= i < |levels| ==> ValidLevel(levels[i])
  }

  function DeclaredMajor(levels: seq<LanguageLevel>): MajorLevel
  {
    if |levels| == 0 then
      TypeLevel
    else
      MaxMajor(smap((ll: LanguageLevel)=>ll.major, levels))
  }

  function MinorsOfDecl(level: LanguageLevel): set<MinorLevel>
  {
    match level.minor
    case None => {}
    case Some(AnyMinorLevel) => Minors(level.major)
    case Some(ExactMinorLevel(minor)) =>
      if level.major == MinorMajor(minor) then {minor} else {}
  }

  function DeclaredMinors(levels: seq<LanguageLevel>): set<MinorLevel>
    decreases |levels|
  {
    if |levels| == 0 then
      AllMinors()
    else sfoldl((acc, ll)=>MinorsOfDecl(ll)+acc, {}, levels)
  }

  // One analysis result records both the required major level and the set of
  // required minor levels.
  datatype RequiredLevels =
    | MkRequiredLevels(
        major: MajorLevel,
        minors: set<MinorLevel>
      )

  // Merges two independent level requirements.
  function MergeRequiredLevels(left: RequiredLevels, right: RequiredLevels): RequiredLevels
  {
    MkRequiredLevels(
      MaxLevel(left.major, right.major),
      left.minors + right.minors
    )
  }

  function JoinRequiredLevels(chunks: seq<RequiredLevels>): RequiredLevels
  {
    if |chunks| == 0 then
      MkRequiredLevels(BooleanLevel, {})
    else
      sfoldl(MergeRequiredLevels, chunks[0], chunks[1..])
  }

  // Normalisation of levels specifications: if all minor levels of a major
  // level are required, use * instead.
  function ExplicitMinorLevelsForMajor(
    major: MajorLevel,
    minors: set<MinorLevel>
  ): seq<LanguageLevel>
  {
    match major
    case BooleanLevel =>
      if GroupCardinalityLevel in minors then
        [MkLanguageLevel(BooleanLevel, Some(ExactMinorLevel(GroupCardinalityLevel)))]
      else
        []
    case ArithmeticLevel =>
      if AggregateFunctionLevel in minors && FeatureCardinalityLevel in minors then
        [MkLanguageLevel(ArithmeticLevel, Some(AnyMinorLevel))]
      else
        (if AggregateFunctionLevel in minors then
           [MkLanguageLevel(ArithmeticLevel, Some(ExactMinorLevel(AggregateFunctionLevel)))]
         else
           []) +
        (if FeatureCardinalityLevel in minors then
           [MkLanguageLevel(ArithmeticLevel, Some(ExactMinorLevel(FeatureCardinalityLevel)))]
         else
           [])
    case TypeLevel =>
      if StringConstraintsLevel in minors then
        [MkLanguageLevel(TypeLevel, Some(ExactMinorLevel(StringConstraintsLevel)))]
      else
        []
  }


  function ExplicitLevelsOf(required: RequiredLevels): seq<LanguageLevel>
  {
    [MkLanguageLevel(required.major, None)] +
    ExplicitMinorLevelsForMajor(BooleanLevel, required.minors) +
    ExplicitMinorLevelsForMajor(ArithmeticLevel, required.minors) +
    ExplicitMinorLevelsForMajor(TypeLevel, required.minors)
  }
}
