Require Import VST.floyd.proofauto VST.floyd.VSU.
From CertiGraph.CertiGC Require Import verif_gc verif_boxing.


Definition linked := ltac:(linkVSUs GCVSU BoxingVSU).
