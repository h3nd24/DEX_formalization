(** * cdr.v: Control Dependence Region (interface) *)
(* Hendra : Removed exception related SOAP *)
Set Implicit Arguments.
Section GRAPH.

  Variable PC Tag: Set.
  Variable step : PC -> option PC -> Prop.
  Definition result p := step p None.

  Record CDR : Type := make_CDR {
     region : PC -> PC -> Prop;
     junc : PC -> PC -> Prop;
     junc_func: forall i j1 j2,
       junc i j1 -> junc i j2 -> j1=j2;
     soap1: forall i j k,
       step i (Some j) ->
       step i (Some k) ->
       j <> k ->
       region i k \/ junc i k;
     soap2:forall i j k,
       region i j-> 
       step j (Some k) ->
       region i k \/ junc i k;
     soap3 : forall i j k, 
       region i j -> 
       result j -> 
       ~ junc i k
  }.

End GRAPH.