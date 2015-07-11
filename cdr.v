(** * cdr.v: Control Dependence Region (interface) *)
(* Hendra : Removed exception related SOAP *)
Set Implicit Arguments.
Section GRAPH.

  Variable PC Tag: Set.
  Variable step : PC -> Tag -> option PC -> Prop.
  Definition result p := exists k, step p k None.

  Record CDR : Type := make_CDR {
     region : PC -> Tag -> PC -> Prop;
     junc : PC -> Tag -> PC -> Prop;
     junc_func: forall i j1 j2 kd,
       junc i kd j1 -> junc i kd j2 -> j1=j2;
     soap1: forall i j kd,
       step i kd (Some j) -> 
       region i kd j \/ junc i kd j;
     soap2:forall i j k kd kd0,
       region i kd0 j-> 
       step j kd (Some k) ->
       region i kd0 k \/ junc i kd0 k;
     soap3 : forall i j k kd, 
       region i kd j -> 
       result j -> 
       ~ junc i kd k
(* DEX Exception
     soap4 : forall i j1 j2 kd1 kd2,
       junc i kd1 j1 -> 
       junc i kd2 j2 -> 
       j1=j2 \/ region i kd1 j2 \/ region i kd2 j1;
     soap5 : forall i j k kd kd', 
       region i kd j -> 
       result j -> 
       junc i kd' k ->
       region i kd k;
     soap5' : forall i k kd kd', 
       step i kd None ->
       (region i kd' k \/ junc i kd' k) ->
       region i kd k
*)
  }.

End GRAPH.


