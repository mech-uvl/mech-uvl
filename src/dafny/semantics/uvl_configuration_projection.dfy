// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines configuration projections used when interpreting an
// imported model through one of its root occurrences. The projection keeps the
// subtree rooted at that occurrence and removes the prefix that precedes the
// imported root, so the imported root occurrence becomes a root occurrence in
// the projected configuration.

module UVL_ConfigurationProjection {
  import opened UVL_Syntax
  import opened UVL_Configuration

  type OccurrencePrefix = seq<OccurrenceId>

  // Checks whether an occurrence starts with a possibly empty occurrence
  // prefix.
  predicate HasOccurrencePrefix(occurrence: OccRef, prefix: OccurrencePrefix)
  {
    |prefix| <= |occurrence| &&
    occurrence[..|prefix|] == prefix
  }

  // Checks whether the end of an occurrence projects to the given UVL
  // reference.
  predicate EndsWithReference(occurrence: OccRef, reference: Reference)
  {
    |reference| <= |occurrence| &&
    ToRef(occurrence[|occurrence| - |reference|..]) == reference
  }

  // Returns the prefix that appears before the given reference suffix.
  ghost function PrefixBeforeReferenceSuffix(occurrence: OccRef, reference: Reference): OccurrencePrefix
    requires EndsWithReference(occurrence, reference)
  {
    occurrence[..|occurrence| - |reference|]
  }

  // Removes a prefix from a concrete occurrence.
  ghost function ProjectOccurrence(prefix: OccurrencePrefix, occurrence: OccRef): OccRef
    requires HasOccurrencePrefix(occurrence, prefix)
    requires |prefix| < |occurrence|
    ensures prefix + ProjectOccurrence(prefix, occurrence) == occurrence
  {
    occurrence[|prefix|..]
  }

  // Removes a prefix from the owner of an attribute value.
  ghost function ProjectAttributeRef(prefix: OccurrencePrefix, attribute: AttributeRef): AttributeRef
    requires HasOccurrencePrefix(attribute.owner, prefix)
    requires |prefix| < |attribute.owner|
    ensures prefix + ProjectAttributeRef(prefix, attribute).owner == attribute.owner
    ensures ProjectAttributeRef(prefix, attribute).key == attribute.key
  {
    AttributeRef(ProjectOccurrence(prefix, attribute.owner), attribute.key)
  }

  // Keeps the selected subtree rooted at `scopeRoot` and removes `prefix` from
  // each retained occurrence. The intended imported-model use is:
  //
  //   prefix    = PrefixBeforeReferenceSuffix(scopeRoot, importedRoot.name)
  //   scopeRoot = the concrete occurrence of that imported root
  ghost function ProjectConfiguration(
    prefix: OccurrencePrefix,
    scopeRoot: OccRef,
    cfg: Configuration
  ): Configuration
  {
    Configuration(
      set occurrence: OccRef |
        occurrence in cfg.selected &&
        DescendantOf(occurrence, scopeRoot) &&
        HasOccurrencePrefix(occurrence, prefix) &&
        |prefix| < |occurrence| ::
        ProjectOccurrence(prefix, occurrence),
      map occurrence: OccRef |
        occurrence in cfg.featureValues &&
        DescendantOf(occurrence, scopeRoot) &&
        HasOccurrencePrefix(occurrence, prefix) &&
        |prefix| < |occurrence| ::
        ProjectOccurrence(prefix, occurrence) := cfg.featureValues[occurrence],
      map attribute: AttributeRef |
        attribute in cfg.attributeValues &&
        DescendantOf(attribute.owner, scopeRoot) &&
        HasOccurrencePrefix(attribute.owner, prefix) &&
        |prefix| < |attribute.owner| ::
        ProjectAttributeRef(prefix, attribute) := cfg.attributeValues[attribute]
    )
  }
}
