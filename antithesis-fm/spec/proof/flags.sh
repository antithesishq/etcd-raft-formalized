#!/bin/bash
# usage: flags.sh Module  -- extra tlapm flags a module needs (none for most).
# EtcdChange: tlapm's SMT encoding crashes (Invalid_argument "List.combine") on set extensionality
# axioms for ConfChanges, a set constructor with three bound variables; the lemma does not need them.
case "$1" in
  EtcdChange) echo "--debug no_smt_set_extensionality" ;;
esac
