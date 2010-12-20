(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Standard Collections} *}
theory Collections
imports
  "common/Misc"
(* Interfaces *)
  SetSpec
  OrderedSet
  MapSpec
  OrderedMap
  ListSpec
  AnnotatedListSpec
  PrioSpec
  PrioUniqueSpec
(* Implementations *)
  SetStdImpl
  MapStdImpl
  StdInst
  RecordSetImpl
  RecordMapImpl
  Fifo
  BinoPrioImpl
  SkewPrioImpl
  FTAnnotatedListImpl
  FTPrioImpl
  FTPrioUniqueImpl

(* Miscellanneous*)
  DatRef

begin
  text {*
    This theory summarizes the components of the Isabelle Collection Framework.
    *}
end
