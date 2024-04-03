From CertiGraph.CertiGC Require Import env_graph_gc spec_gc.

Lemma body_is_ptr: semax_body Vprog Gprog f_is_ptr is_ptr_spec.
Proof.
  start_function.
  forward_call x.
  forward.
  red in H0.
  destruct Archi.ptr64 eqn:H1; try solve [inversion H1].
  destruct x; simpl in *; entailer!!.
Qed.
