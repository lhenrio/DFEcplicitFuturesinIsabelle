theory TypeTheorems imports gASPFuturesTypeSystem begin

section{* Induction lemmas *}
lemma TypeExpression_induct_Config:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C v T. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Av:T \<Longrightarrow> Prop P aos futs \<Gamma> C (At v) T) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C e e'. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ae:BType Integer \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ae':BType Integer \<Longrightarrow> Prop P aos futs \<Gamma> C (e+\<^sub>Ae') (BType Integer)) \<Longrightarrow> 
    (\<And>P T T' aos futs \<Gamma> C e.  P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow> Prop P aos futs \<Gamma> C e T \<Longrightarrow>Prop P  aos futs \<Gamma> C e T') 
          \<Longrightarrow> Prop P aos futs  \<Gamma> C e T"
apply (insert gASPFuturesTypeSystem.TypeExpression.induct [of  P "Cn aos futs" \<Gamma> C e T  "\<lambda> x conf y z t. (Prop x (Conf_AOs conf) (Conf_futs conf) y z t)" ])
apply clarsimp
 apply (drule meta_impE,auto,case_tac Config,auto)+
done

lemma TypeAtom_induct_Config:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ae:T \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C v T. P,Cn aos futs\<turnstile>\<^sub>Vv:T \<Longrightarrow> Prop P aos futs \<Gamma> C (Val v) T) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C. Prop P aos futs \<Gamma> C (Var This) (BType (TObj C))) \<Longrightarrow> 
    (\<And>P T T' aos futs \<Gamma> C x.   \<Gamma> x = Some T  \<Longrightarrow> Prop P  aos futs \<Gamma> C (Var (VarOrThis.Id x)) T) \<Longrightarrow>
     (\<And>P T T' aos futs \<Gamma> C e.  P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ae:T \<Longrightarrow> Prop P aos futs \<Gamma> C e T \<Longrightarrow>Prop P  aos futs \<Gamma> C e T')
          \<Longrightarrow> Prop P aos futs  \<Gamma> C e T"
apply (insert gASPFuturesTypeSystem.TypeAtom.induct [of  P "Cn aos futs" \<Gamma> C e T  "\<lambda> x conf y z t. (Prop x (Conf_AOs conf) (Conf_futs conf) y z t)" ])
apply clarsimp
 apply (drule meta_impE,auto,case_tac Config,auto)+
done

lemma TypeStatement_TypeStatementList_induct_Config:
"  (\<And>P aos futs \<Gamma> C a T x T'. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T \<Longrightarrow> \<Gamma> x = Some T' \<Longrightarrow>  P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow> P1 P aos futs \<Gamma> C (x =\<^sub>A a)) \<Longrightarrow>
    (\<And>P C Class m Meth T' aos futs \<Gamma> e T x. fetchClass P C = Some Class \<Longrightarrow> fetchMethodInClass Class m = Some Meth \<Longrightarrow> MRType Meth = T' \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow> \<Gamma> x = Some T' \<Longrightarrow>  P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow> P1 P aos futs \<Gamma> C (return e)) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C z  sl sl'. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Az:BType Boolean \<Longrightarrow> (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>L sl)  \<Longrightarrow> P2 P aos futs \<Gamma> C sl \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>L sl'  \<Longrightarrow> P2 P aos futs \<Gamma> C sl' \<Longrightarrow> P1 P aos futs \<Gamma> C (IF z THEN sl ELSE sl' )) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C. P2 P aos futs \<Gamma> C []) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C s sl. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>S s  \<Longrightarrow> P1 P aos futs \<Gamma> C s \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>L sl  \<Longrightarrow> P2 P aos futs \<Gamma> C sl \<Longrightarrow> P2 P aos futs \<Gamma> C (s ;; sl)) \<Longrightarrow>
    ((P,Cn aos futs,\<Gamma> in x4\<turnstile>\<^sub>S x5)  \<longrightarrow> P1 P aos futs \<Gamma> x4 x5) \<and> ((P',Cn aos' futs',\<Gamma>' in x9\<turnstile>\<^sub>L x10)  \<longrightarrow> P2 P' aos' futs' \<Gamma>'  x9 x10)"
apply (insert gASPFuturesTypeSystem.TypeStatement_TypeStatementList.induct [of "\<lambda> x conf y z t. (P1 x (Conf_AOs conf) (Conf_futs conf) y z t)" "\<lambda> x conf y z t. (P2 x (Conf_AOs conf) (Conf_futs conf) y z t)" P "Cn aos futs" \<Gamma> x4 x5 P' "Cn aos' futs'" \<Gamma>' x9 x10])
apply rule
 apply (drule meta_impE,auto,case_tac Config,auto)+
done

lemma TypeRhs_induct_Config:
"(P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>RR: T)\<Longrightarrow>
    (\<And>P aos futs \<Gamma> C e T. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T) \<Longrightarrow> P1 P aos futs \<Gamma> C (Expr e) T) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C z C' Class m Meth param_types el.
        (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Az:BType (TObj C')) \<Longrightarrow>
        fetchClass P C' = Some Class \<Longrightarrow> fetchMethodInClass Class m = Some Meth \<Longrightarrow> param_types = map fst (MParams Meth) \<Longrightarrow> length param_types = length el \<Longrightarrow> \<forall>i<length el. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Eel ! i:param_types ! i) 
                  \<Longrightarrow> P1 P  aos futs \<Gamma> C (z.\<^sub>Am(el)) (MakeFutureType (MRType Meth))) \<Longrightarrow>
    (\<And>P C' Class Class_param_types el aos futs \<Gamma> C. fetchClass P C' = Some Class \<Longrightarrow> Class_param_types = map fst (ClassParameters Class) \<Longrightarrow> length Class_param_types = length el 
                  \<Longrightarrow> \<forall>i<length el. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>E(el ! i):(Class_param_types ! i)) \<Longrightarrow> P1 P  aos futs \<Gamma> C (newActive C'(el)) (BType (TObj C'))) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C z T. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Az:FutType T) \<Longrightarrow> P1 P  aos futs \<Gamma> C (Get z) (BType T)) \<Longrightarrow> (\<And>P T T'  aos futs \<Gamma> C e.  P\<turnstile>T\<sqsubseteq>T' 
                  \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Re:T \<Longrightarrow> P1 P  aos futs \<Gamma> C e T \<Longrightarrow> P1 P aos futs \<Gamma> C e T') 
\<Longrightarrow> P1 P aos futs \<Gamma> C R T"
apply (insert TypeRhs.induct [of  P "Cn aos futs" \<Gamma> C R T "\<lambda> x conf y z t. (P1 x (Conf_AOs conf) (Conf_futs conf) y z t)"])
apply auto
apply (drule meta_impE,auto,case_tac Config,auto)+
done

section{* Basic Lemmas *}

lemma TypeStatementList_TypeStatement[rule_format]: 
"(P,Config,\<Gamma> in C \<turnstile>\<^sub>L Stl)  \<longrightarrow> (S \<in> set Stl\<longrightarrow> (P,Config,\<Gamma> in C \<turnstile>\<^sub>S S))"
apply (induct_tac Stl)
 apply clarsimp+
apply (drule TypeStatementList.cases,auto)
done

lemma fetchClass_Some_In[rule_format]:
 "fetchClass (Prog CL Vars Stl) C = Some CLa \<Longrightarrow> CLa\<in>set CL"
by (unfold fetchClass_def, rule find_Some,auto)

lemma fetchClass_Some_Name[rule_format]:
 "fetchClass (Prog CL Vars Stl) C = Some CLa \<Longrightarrow> Name CLa=C"
by (unfold fetchClass_def,simp,drule find_Some_P,simp)

lemma fetchMethodInClass_Some:
 "fetchMethodInClass C m = Some M \<Longrightarrow> M \<in> set (Methods C)"
by (unfold fetchMethodInClass_def, rule find_Some,auto)
section{* extending set of AOs in config *}

lemma TypeValue_extendconfiguration_AO[rule_format]:
"P,Cn AOs Futures\<turnstile>\<^sub>Vv:T \<Longrightarrow> (case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C=C' | None \<Rightarrow> True) 
    \<Longrightarrow>(P,Cn  (AOs(\<alpha>\<mapsto> (AO C state R Ec Rq))) Futures\<turnstile>\<^sub>Vv:T)"
apply (erule TypeValue.cases,auto)
    apply (rule TypeValue.intros)
   apply (rule TypeValue.intros)
  apply (rule TypeValue.intros)
 apply (case_tac "\<alpha>=\<alpha>'")
  apply (rule TypeValue.intros,force)
 apply (rule TypeValue.intros,force)
apply (rule TypeValue.intros,simp)
done

lemma TypeValue_extendconfiguration_AO_lambda[rule_format]:
"P,Cn AOs Futures\<turnstile>\<^sub>Vv:T \<Longrightarrow> (case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C=C' | None \<Rightarrow> True) 
    \<Longrightarrow>(P,Cn ( (\<lambda>a. if a = \<alpha> then Some (AO C state R Ec Rq) else AOs a) ) Futures\<turnstile>\<^sub>Vv:T)"
by (insert TypeValue_extendconfiguration_AO,simp add: fun_upd_def)

lemma TypeAtom_extendconfiguration_AO[rule_format]:
"P,Cn AOs futs,\<Gamma> in C\<turnstile>\<^sub>Az:T \<Longrightarrow> ((case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True) \<longrightarrow> 
          ( P,Cn (\<lambda>a. if a = \<alpha> then Some (AO C'' state R Ec Rq) else AOs a)  futs ,\<Gamma> in C\<turnstile>\<^sub>Az:T))"
apply (erule  "TypeAtom_induct_Config",auto)
    apply (rule  "TypeValue.cases",auto)
        apply (rule  "TypeAtom.intros",(rule  TypeValue_extendconfiguration_AO_lambda)?,(auto)?)+
done


lemma TypeExpression_extendconfiguration_AO[rule_format]:
"P,Cn AOs futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow> ((case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True) \<longrightarrow> 
          ( P,Cn (\<lambda>a. if a = \<alpha> then Some (AO C'' state R Ec Rq) else AOs a)  futs ,\<Gamma> in C\<turnstile>\<^sub>Ee:T))"
apply (erule  "TypeExpression_induct_Config",auto)
  apply (rule  "TypeExpression.intros",(auto)?)+
  apply (rule  "TypeAtom_extendconfiguration_AO",auto)
 apply (rule  "TypeExpression.intros",(auto)?)+
  apply (rule  "TypeAtom_extendconfiguration_AO",auto)
 apply (rule  "TypeAtom_extendconfiguration_AO",auto)
apply (rule  "TypeExpression.intros",auto)
done

lemma TypeRhs_extendconfiguration_AO[rule_format]:
"P,Cn AOs futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T \<Longrightarrow> ((case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True)
  \<longrightarrow>(P,Cn (\<lambda>a. if a = \<alpha> then Some (AO C'' state R Ec Rq) else AOs a) futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T))"
apply (erule  "TypeRhs_induct_Config",auto)
(*5*)
    apply (rule  "TypeRhs.intros",(auto)?)
    apply (erule TypeExpression_extendconfiguration_AO,auto)
   apply (rule  "TypeRhs.intros",(auto)?)
    apply (erule TypeAtom_extendconfiguration_AO,auto)
   apply (rule_tac AOs=aos in TypeExpression_extendconfiguration_AO)
     apply (drule_tac x=i in spec,auto)
(*3*)
  apply (rule  "TypeRhs.intros",(auto)?)
  apply (rule_tac AOs=aos in TypeExpression_extendconfiguration_AO)
    apply (drule_tac x=i in spec,auto)
 apply (rule  "TypeRhs.intros",(auto)?)
 apply (erule TypeAtom_extendconfiguration_AO,force)
apply (rule  "TypeRhs.intros",(auto)?)
done


lemma TypeStatement_extendconfiguration_AO_Pre[rule_format]:
" ((P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<longrightarrow> (\<forall> \<alpha> X. (case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True)
                    \<longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>(AO C'' state R Ec Rq))) futs,\<Gamma> in C \<turnstile>\<^sub>S S))) \<and> 
  ((P, Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<longrightarrow> (\<forall> \<alpha> X. (case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True)
                    \<longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>(AO C'' state R Ec Rq))) futs,\<Gamma> in C \<turnstile>\<^sub>L Stl)))"
apply (rule TypeStatement_TypeStatementList_induct_Config,auto)
(*5*)
    apply (rule  "TypeStatement_TypeStatementList.intros",auto)
    apply (erule_tac AOs=aos in TypeRhs_extendconfiguration_AO,auto)
   apply (rule "TypeStatement_TypeStatementList.intros",force,auto)
   apply (erule_tac AOs=aos in TypeExpression_extendconfiguration_AO,auto)
  apply (rule  "TypeStatement_TypeStatementList.intros")
(*5*)
    apply (erule_tac AOs=aos in TypeAtom_extendconfiguration_AO,auto)
 apply (rule  "TypeStatement_TypeStatementList.intros")
apply (rule  "TypeStatement_TypeStatementList.intros")
 apply auto
done

lemma TypeRequest_extendconfiguration_AO[rule_format]:
"P,Cn AOs futs in C\<turnstile>\<^sub>Q (f,m,vl) \<Longrightarrow> ((case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True)
  \<longrightarrow>(P,Cn (\<lambda>a. if a = \<alpha> then Some (AO C'' state R Ec Rq) else AOs a) futs in C\<turnstile>\<^sub>Q (f,m,vl)))"
apply (erule TypeRequest.cases,auto)
apply (rule TypeRequest.intros,auto)
apply (drule_tac x=i in spec)
apply clarsimp
apply (rule_tac TypeValue_extendconfiguration_AO_lambda)
apply auto
done

(* GLOBAL LEMMAS *)
lemma TypeStatement_extendconfiguration_AO:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<Longrightarrow>(case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True) 
          \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>(AO C'' state R Ec Rq))) futs,\<Gamma> in C \<turnstile>\<^sub>S S"
by (insert TypeStatement_extendconfiguration_AO_Pre, auto)

lemma TypeStatementList_extendconfiguration_AO:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow>(case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True) 
          \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>(AO C'' state R Ec Rq))) futs,\<Gamma> in C \<turnstile>\<^sub>L Stl"
by (insert TypeStatement_extendconfiguration_AO_Pre, auto)

section{* extending set of futs in config *}

lemma TypeValue_extendconfiguration_futs[rule_format]:
"P,Cn AOs futs\<turnstile>\<^sub>Vv:T \<Longrightarrow>futs f = None\<Longrightarrow>(P,Cn  AOs  (futs(f\<mapsto>a))\<turnstile>\<^sub>Vv:T)"
apply (erule TypeValue.cases,auto)
    apply (rule TypeValue.intros,force?)+
done
lemma TypeValue_extendconfiguration_futs_lambda[rule_format]:
"P,Cn AOs futs\<turnstile>\<^sub>Vv:T \<Longrightarrow>futs f = None\<Longrightarrow>(P,Cn  AOs  (\<lambda>a. if a = f then Some Y else futs a)\<turnstile>\<^sub>Vv:T)"
by (insert TypeValue_extendconfiguration_futs,simp add: fun_upd_def)


lemma TypeAtom_extendconfiguration_futs[rule_format]:
"P,Cn AOs futs,\<Gamma> in C\<turnstile>\<^sub>Az:T \<Longrightarrow> futs f = None\<longrightarrow>( P,Cn AOs (\<lambda>a. if a = f then Some Y else futs a),\<Gamma> in C\<turnstile>\<^sub>Az:T)"
apply (erule  "TypeAtom_induct_Config",auto)
    apply (rule  "TypeValue.cases",auto)
        apply (rule  "TypeAtom.intros",(rule  TypeValue_extendconfiguration_futs_lambda)?,(auto)?)+
done

lemma TypeExpression_extendconfiguration_futs[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow> futs f = None\<longrightarrow>( P,Cn aos (\<lambda>a. if a = f then Some Y else futs a),\<Gamma> in C\<turnstile>\<^sub>Ee:T)"
apply (erule  "TypeExpression_induct_Config",auto)
  apply (rule  "TypeExpression.intros",(auto)?)+
  apply (rule  "TypeAtom_extendconfiguration_futs",auto)
 apply (rule  "TypeExpression.intros",(auto)?)+
  apply (rule  "TypeAtom_extendconfiguration_futs",auto)
 apply (rule  "TypeAtom_extendconfiguration_futs",auto)
apply (rule  "TypeExpression.intros",auto)
done


lemma TypeRhs_extendconfiguration_futs[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T \<Longrightarrow> (futs f = None\<longrightarrow>(P,Cn aos (\<lambda>a. if a = f then Some Y else futs a),\<Gamma> in C\<turnstile>\<^sub>Ra:T))"
apply (erule  "TypeRhs_induct_Config",auto)
(*5*)
    apply (rule  "TypeRhs.intros",(auto)?)
    apply (erule TypeExpression_extendconfiguration_futs,auto)
   apply (rule  "TypeRhs.intros",(auto)?)
    apply (erule TypeAtom_extendconfiguration_futs,auto)
   apply (rule_tac aos=aos in TypeExpression_extendconfiguration_futs)
     apply (drule_tac x=i in spec,auto)
(*3*)
  apply (rule  "TypeRhs.intros",(auto)?)
  apply (rule_tac aos=aos in TypeExpression_extendconfiguration_futs)
    apply (drule_tac x=i in spec,auto)
 apply (rule  "TypeRhs.intros",(auto)?)
 apply (erule TypeAtom_extendconfiguration_futs,force)
apply (rule  "TypeRhs.intros",(auto)?)
done

lemma TypeStatement_extendconfiguration_futs_Pre[rule_format]:
" ((P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<longrightarrow> (\<forall> f Y. f\<notin>(dom futs)\<longrightarrow> (P, Cn AOs (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>S S))) \<and> 
  ((P, Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<longrightarrow> (\<forall> f Y. f\<notin>(dom futs)\<longrightarrow> (P, Cn AOs (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>L Stl)))"
apply (rule TypeStatement_TypeStatementList_induct_Config,auto)
(*5*)
    apply (rule  "TypeStatement_TypeStatementList.intros",auto)
    apply (erule TypeRhs_extendconfiguration_futs,auto)
    apply (rotate_tac -1,erule contrapos_pp,force)  
   apply (rule  "TypeStatement_TypeStatementList.intros",auto)
   apply (erule TypeExpression_extendconfiguration_futs,auto)
    apply (rotate_tac -1,erule contrapos_pp,force)  
  apply (rule  "TypeStatement_TypeStatementList.intros")
(*5*)
    apply (erule TypeAtom_extendconfiguration_futs,auto)
    apply (rotate_tac -1,erule contrapos_pp,force)
   apply (drule_tac x=f in spec,auto)+
 apply (rule  "TypeStatement_TypeStatementList.intros")
apply (rule  "TypeStatement_TypeStatementList.intros")
 apply (drule_tac x=f in spec,auto)+
done

lemma TypeRequest_extendconfiguration_futs[rule_format]:
"P,Cn AOs futs in C\<turnstile>\<^sub>Q (f,m,vl) \<Longrightarrow> (futs f = None
  \<longrightarrow>(P,Cn AOs (\<lambda>a. if a = f then Some Y else futs a) in C\<turnstile>\<^sub>Q (f,m,vl)))"
by (erule TypeRequest.cases,auto)


(* GLOBAL LEMMAS *)
lemma TypeStatement_extendconfiguration_futs:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<Longrightarrow>f\<notin>(dom futs) \<Longrightarrow>P, Cn AOs (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>S S"
by (insert TypeStatement_extendconfiguration_futs_Pre,case_tac Y, simp)

lemma TypeStatementList_extendconfiguration_futs:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow>f\<notin>(dom futs) \<Longrightarrow>P, Cn AOs (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>L Stl"
by (insert TypeStatement_extendconfiguration_futs_Pre,case_tac Y, simp)


section {* extend AOs and futs *}
lemma TypeStatement_extendconfiguration:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<Longrightarrow>(case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True) \<Longrightarrow>f\<notin>(dom futs) 
                \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>(AO C'' state R Ec Rq))) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>S S"
by (insert TypeStatement_extendconfiguration_futs,insert TypeStatement_extendconfiguration_AO, auto)

lemma TypeStatementList_extendconfiguration:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow>(case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C''=C' | None \<Rightarrow> True) 
                 \<Longrightarrow>f\<notin>(dom futs) \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>(AO C'' state R Ec Rq))) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>L Stl"
by (insert TypeStatementList_extendconfiguration_futs,insert TypeStatementList_extendconfiguration_AO, auto)

section {* compositional lemmas for WT *}

lemma TypeUpdate_AO:  "P \<turnstile> Cn AOs Futures  \<Longrightarrow>
  (case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C=C' | None \<Rightarrow> True) \<Longrightarrow>
   (\<exists> CL . (fetchClass P C = Some CL \<and>
    (
     (* check state *)
     ( (  \<forall> x v. (state(x) =Some  v \<longrightarrow> (\<exists> T . (T,x)\<in> set (ClassParameters CL) \<and> (P,Cn (AOs(\<alpha> \<mapsto> AO C state R Ec Rq)) Futures\<turnstile>\<^sub>V v: T))) ) )
     (* check request queue*)
     \<and> (\<forall> R'\<in>set Rq. (P, (Cn (AOs(\<alpha> \<mapsto> AO C state R Ec Rq)) Futures) in C \<turnstile>\<^sub>Q R' ) )
     (* check current request*)
     \<and> 
     (case R of Some  (f,m,vl) \<Rightarrow>
         (\<exists> Meth. fetchMethodInClass CL m = Some Meth \<and>
           (P, Cn (AOs(\<alpha> \<mapsto> AO C state R Ec Rq)) Futures in C \<turnstile>\<^sub>Q (f,m,vl)) 
           \<and> (case Ec of (locs,Stl) \<Rightarrow> ( \<forall> s\<in>set Stl. 
             (P,Cn (AOs(\<alpha> \<mapsto> AO C state R Ec Rq)) Futures,(BuildTypeEnv (ClassParameters CL))++(BuildTypeEnv (LocalVariables Meth))++(BuildTypeEnv (MParams Meth)) in C \<turnstile>\<^sub>S s)
        )) ) ) )))
\<Longrightarrow> P \<turnstile> Cn (AOs(\<alpha> \<mapsto> AO C state R Ec Rq)) Futures "
apply (clarsimp,auto)
 apply (clarsimp simp: ran_def)
 apply (case_tac "a = \<alpha>",simp,force)
(*activity not alpha *)
 apply clarsimp
 apply (case_tac Act,clarsimp)
 apply (drule_tac x= "(AO x1 x2 x3 (aa, b) x5)" in spec)
 apply clarsimp
 apply (erule impE,force)
 apply clarsimp
 apply (intro allI conjI)
(*4*)
   apply clarsimp
   apply (drule_tac x=x in spec)+
   apply (drule_tac x=v in spec)+
   apply clarsimp
   apply (rule_tac x=T in exI)
   apply clarsimp
   apply (erule TypeValue_extendconfiguration_AO)
   apply clarsimp

(*3 Q*)
  apply clarsimp
  apply (rename_tac a)
(* one of the pending request *)
  apply (drule_tac x="(ab, ac, a)" in bspec,simp)
  apply (erule TypeRequest.cases)
  apply (rule_tac Meth=Meth in TypeRequest.intros)
         apply auto
  apply (drule_tac x=i in spec,clarsimp)
  apply (rule TypeValue_extendconfiguration_AO)
   apply clarsimp+

(*2 the current req*)
 apply (case_tac x3,auto) 
  apply (simp add: Fun.fun_upd_def)
  apply (erule TypeRequest_extendconfiguration_AO)
  apply auto
 apply (drule_tac x=x in bspec,auto)
 apply (erule_tac \<alpha>=\<alpha> in TypeStatement_extendconfiguration_AO)
 apply simp

(*1 Finally: futures *)
apply (drule_tac x="(a,b)" in bspec)
 apply simp
apply(case_tac b)
 apply auto
apply (erule TypeValue_extendconfiguration_AO)
apply clarsimp
done

section{*Type-empty-config*}

lemma  TypeValue_EmptyConfig_pre: 
  "(P,Cnf\<turnstile>\<^sub>Vv:T) \<Longrightarrow>(Cnf=EmptyConfig  \<longrightarrow>(P,Config\<turnstile>\<^sub>Vv:T))"
apply (erule TypeValue.induct,auto)
apply (rule TypeValue.intros)+
done
lemma  TypeValue_EmptyConfig: 
  "(P,EmptyConfig\<turnstile>\<^sub>Vv:T) \<Longrightarrow>(P,Config\<turnstile>\<^sub>Vv:T)"
by (drule TypeValue_EmptyConfig_pre,auto)

lemma  TypeAtom_EmptyConfig_pre: 
  "(P,Cnf,\<Gamma> in C\<turnstile>\<^sub>Av:T) \<Longrightarrow>(Cnf=EmptyConfig  \<longrightarrow>(P,Config,\<Gamma> in C\<turnstile>\<^sub>Av:T))"
apply (erule TypeAtom.induct,auto)
apply (rule TypeAtom.intros)
apply (erule TypeValue_EmptyConfig)
apply (rule TypeAtom.intros)
apply (erule TypeAtom.intros)
apply (erule TypeAtom.intros,simp)
done
lemma  TypeAtom_EmptyConfig: 
"(P,EmptyConfig,\<Gamma> in C\<turnstile>\<^sub>Av:T) \<Longrightarrow>(P,Config,\<Gamma> in C\<turnstile>\<^sub>Av:T)"
by (drule TypeAtom_EmptyConfig_pre,auto)

lemma  TypeExpression_EmptyConfig_pre: 
  "(P,Cnf,\<Gamma> in C\<turnstile>\<^sub>Ee:T) \<Longrightarrow>(Cnf=EmptyConfig  \<longrightarrow>(P,Config,\<Gamma> in C\<turnstile>\<^sub>Ee:T))"
apply (erule TypeExpression.induct,auto)
apply (rule TypeExpression.intros)
apply (erule TypeAtom_EmptyConfig)
apply (rule TypeExpression.intros)
apply (erule TypeAtom_EmptyConfig)
apply (erule TypeAtom_EmptyConfig)
apply (erule TypeExpression.intros,simp)
done
lemma  TypeExpression_EmptyConfig: 
"(P,EmptyConfig,\<Gamma> in C\<turnstile>\<^sub>Ee:T) \<Longrightarrow>(P,Config,\<Gamma> in C\<turnstile>\<^sub>Ee:T)"
by (drule TypeExpression_EmptyConfig_pre,auto)

lemma TypeRhs_EmptyConfig_pre:
"(P,Cnf,\<Gamma> in C\<turnstile>\<^sub>RR:T) \<Longrightarrow>(Cnf=EmptyConfig  \<longrightarrow>(P,Config,\<Gamma> in C\<turnstile>\<^sub>RR:T))"
apply (drule TypeRhs.induct,auto)
apply (rule TypeRhs.intros)
apply (erule TypeExpression_EmptyConfig)
apply (rule TypeRhs.intros,auto)
apply (erule TypeAtom_EmptyConfig)
apply (drule_tac x=i in spec,simp)
apply (erule TypeExpression_EmptyConfig)
apply (rule TypeRhs.intros,auto)
apply (drule_tac x=i in spec,simp)
apply (erule TypeExpression_EmptyConfig)
apply (rule TypeRhs.intros)
apply (erule TypeAtom_EmptyConfig)
apply (rule TypeRhs.intros,auto)
done
lemma  TypeRhs_EmptyConfig: 
"(P,EmptyConfig,\<Gamma> in C\<turnstile>\<^sub>RR:T) \<Longrightarrow>(P,Config,\<Gamma> in C\<turnstile>\<^sub>RR:T)"
by (drule TypeRhs_EmptyConfig_pre,auto)

lemma Type_EmptyConfig_Stl_pre: "((P,Cnf,\<Gamma> in C \<turnstile>\<^sub>S S) \<longrightarrow>(Cnf=EmptyConfig \<longrightarrow>(P,Config,\<Gamma> in C \<turnstile>\<^sub>S S))) \<and>
                             ((P,Cnf,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<longrightarrow> (Cnf=EmptyConfig \<longrightarrow>(P,Config,\<Gamma> in C \<turnstile>\<^sub>L Stl)))"
apply (rule TypeStatement_TypeStatementList.induct,auto)
apply (rule TypeStatement_TypeStatementList.intros,auto)
apply (erule TypeRhs_EmptyConfig)
apply (rule TypeStatement_TypeStatementList.intros,auto)
apply (erule TypeExpression_EmptyConfig)
apply (rule TypeStatement_TypeStatementList.intros,auto)
apply (erule TypeAtom_EmptyConfig)
apply (rule TypeStatement_TypeStatementList.intros)
apply (rule TypeStatement_TypeStatementList.intros,auto)
done
lemma  TypeStl_EmptyConfig: 
"(P,EmptyConfig,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow>(P,Config,\<Gamma> in C \<turnstile>\<^sub>L Stl)"
by (insert Type_EmptyConfig_Stl_pre,auto)

section{* Well-typed initial configuraiton *}

theorem WTinitialconfiguration: "\<turnstile>\<^sub>P Prog  CL Vars Stl \<Longrightarrow> Prog  ((MainObjClass Vars)#CL) Vars Stl \<turnstile> InitialConfiguration (Prog  CL Vars Stl)"
apply (unfold InitialConfiguration_def BuildInitialConfigurationfromVarsStl_def)
apply (auto,unfold Let_def fetchClass_def fetchMethodInClass_def MainObjClass_def MainMethodEmptyBody_def,auto)
 apply (intro gASPFuturesTypeSystem.TypeRequest.intros, auto simp: fetchClass_def fetchMethodInClass_def GetBasicType_def)
apply (rule TypeStatementList_TypeStatement,auto)
apply (unfold BuildTypeEnv_def)
apply (rule_tac AOs="empty"  in TypeStatementList_extendconfiguration)
  apply (auto)
done

section {* Subject Reduction *}



theorem SubjectReduction: 
"Prog CL Vars Stl \<turnstile> Cn aos futs   \<leadsto> Cn aos' futs' \<Longrightarrow> \<turnstile>\<^sub>P Prog  CL Vars Stl
    \<longrightarrow> ((Prog CL Vars Stl \<turnstile> Cn aos futs)  \<longrightarrow> (Prog CL Vars Stl \<turnstile> Cn aos' futs'))"
apply (erule gASPFutures.reduction.induct)
(* 11 SERVE *)
apply (case_tac P, rename_tac CL Vars Stl, simp only: Let_def)
apply (intro impI)
apply (rule TypeUpdate_AO)
apply clarsimp+
apply (drule_tac x="AO C state None (a, b) ((f, m, vl) # Rq)" in bspec,force simp: ran_def)
apply simp
apply clarify
apply (rule_tac x=CLa in exI)
apply clarsimp
apply (intro conjI,clarsimp)
apply (drule_tac x=x in spec, drule_tac x=v in spec)
apply clarsimp
apply (rule_tac x=T in exI)
apply clarsimp
apply (erule TypeValue_extendconfiguration_AO,clarsimp)
(*12*)
apply clarsimp
apply (rename_tac a b c)
apply (drule_tac x="(a,b,c)" in bspec,simp)
apply (simp add: fun_upd_def)
apply (erule TypeRequest_extendconfiguration_AO)
apply force
(*11*)
apply (simp add: Bind_def )
apply (case_tac "fetchMethodInClass CLa m",clarsimp)
apply clarsimp
apply (intro conjI)
apply (simp add: fun_upd_def,erule TypeRequest_extendconfiguration_AO,force)
apply clarsimp
(* well typed new body! *)
apply (clarsimp simp: Let_def)
apply (case_tac "length (MParams aa) = length vl")  
apply clarsimp
apply (drule_tac x=CLa in bspec)
apply (erule fetchClass_Some_In)
apply (rule_tac Stl="Body aa" in TypeStatementList_TypeStatement)
apply (drule_tac x=aa in bspec)
apply (erule fetchMethodInClass_Some)
apply (rule TypeStl_EmptyConfig)
apply (simp add: BuildTypeEnv_def)
apply (drule fetchClass_Some_Name,simp,simp,simp)

(*10 AssignLocal *)
apply (case_tac P, rename_tac CL Vars Stl, simp only: Let_def)
apply (intro impI)
apply (rule TypeUpdate_AO)
apply clarsimp+
apply (drule_tac x="(AO C state (Some (a, aa, b)) (locs, x =\<^sub>A Expr e ;; Stla) Rq)" in bspec,force simp: ran_def)
apply simp
apply clarify
apply (rule_tac x=CLa in exI)
apply clarsimp
apply (intro conjI,clarsimp)
apply (drule_tac x=xa in spec, drule_tac x=va in spec)
apply clarsimp
apply (rule_tac x=T in exI)
apply clarsimp
apply (erule TypeValue_extendconfiguration_AO,clarsimp)
(*12*)
apply clarsimp
apply (rename_tac a b c)
apply (drule_tac x="(a,b,c)" in bspec,simp)
apply (simp add: fun_upd_def)
apply (erule TypeRequest_extendconfiguration_AO)
apply force
(*11*)
apply (simp add: fun_upd_def)
apply (erule TypeRequest_extendconfiguration_AO)
apply force
(*10*)
apply clarsimp
apply (drule_tac x=xa in bspec,simp)
apply (erule TypeStatement_extendconfiguration_AO)
apply force

(*9 AssignField*)
apply (case_tac P, rename_tac CL Vars Stl, simp only: Let_def)
apply (intro impI)
apply (thin_tac "x \<notin> dom locs")
apply (rule TypeUpdate_AO)
apply clarsimp+
apply (drule_tac x="(AO C state (Some (a, aa, b)) (locs, x =\<^sub>A Expr e ;; Stla) Rq)" in bspec,force simp: ran_def)
apply simp
apply clarify
apply (rule_tac x=CLa in exI)
apply clarsimp
apply (intro conjI,clarsimp)
apply (intro conjI,clarsimp)
apply (drule_tac x=x in spec, drule_tac x=y in spec)
apply clarsimp
apply (rule_tac x=T in exI)
apply clarsimp
apply (erule TypeValue_extendconfiguration_AO,clarsimp)
(*12*)
apply clarsimp
apply (rename_tac a b c)
apply (drule_tac x="(a,b,c)" in bspec,simp)
apply (simp add: fun_upd_def)
apply (erule TypeRequest_extendconfiguration_AO)
apply force
(*11*)
apply (simp add: fun_upd_def)
apply (erule TypeRequest_extendconfiguration_AO)
apply force
(*10*)
apply clarsimp
apply (drule_tac x=xa in bspec,simp)
apply (erule TypeStatement_extendconfiguration_AO)
apply force
