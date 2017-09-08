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


section{* extending set of AOs in config *}

lemma TypeValue_extendconfiguration_AO[rule_format]:
"P,Cn AOs Futures\<turnstile>\<^sub>Vv:T \<Longrightarrow> (case AOs \<alpha> of Some (AO C' st' R' Ec' Rq') \<Rightarrow> C=C' | None \<Rightarrow> True) \<Longrightarrow>(P,Cn (AOs(\<alpha> \<mapsto> AO C state R Ec Rq)) Futures\<turnstile>\<^sub>Vv:T)"
apply (erule TypeValue.cases,auto)
    apply (rule TypeValue.intros)
   apply (rule TypeValue.intros)
  apply (rule TypeValue.intros)
 apply (case_tac "\<alpha>=\<alpha>'")
  apply (rule TypeValue.intros,force)
 apply (rule TypeValue.intros,force)
apply (rule TypeValue.intros,force)
done

lemma TypeAtom_extendconfiguration_AO[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Az:T \<Longrightarrow> (aos \<alpha> = None \<longrightarrow> ( P,Cn (\<lambda>a. if a = \<alpha> then Some X else aos a)  futs ,\<Gamma> in C\<turnstile>\<^sub>Az:T))"
apply (erule  "TypeAtom.induct",auto)
    apply (rule  "TypeValue.cases",auto)
        apply (rule  "TypeAtom.intros",(auto)?)+
done
lemma TypeExpression_extendconfiguration_AO[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow> (aos \<alpha> = None \<longrightarrow> ( P,Cn (\<lambda>a. if a = \<alpha> then Some X else aos a)  futs ,\<Gamma> in C\<turnstile>\<^sub>Ee:T))"
apply (erule  "TypeExpression_induct_Config",auto)
  apply (rule  "TypeExpression.intros",(auto)?)+
  apply (rule  "TypeAtom_extendconfiguration_AO",auto)
 apply (rule  "TypeExpression.intros",(auto)?)+
  apply (rule  "TypeAtom_extendconfiguration_AO",auto)
 apply (rule  "TypeAtom_extendconfiguration_AO",auto)
apply (rule  "TypeExpression.intros",auto)
done

lemma TypeRhs_extendconfiguration_AO[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T \<Longrightarrow> (aos \<alpha> = None \<longrightarrow>(P,Cn (\<lambda>a. if a = \<alpha> then Some X else aos a) futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T))"
apply (erule  "TypeRhs_induct_Config",auto)
(*5*)
    apply (rule  "TypeRhs.intros",(auto)?)
    apply (erule TypeExpression_extendconfiguration_AO,auto)
   apply (rule  "TypeRhs.intros",(auto)?)
    apply (erule TypeAtom_extendconfiguration_AO,auto)
   apply (rule_tac aos=aos in TypeExpression_extendconfiguration_AO)
     apply (drule_tac x=i in spec,auto)
(*3*)
  apply (rule  "TypeRhs.intros",(auto)?)
  apply (rule_tac aos=aos in TypeExpression_extendconfiguration_AO)
    apply (drule_tac x=i in spec,auto)
 apply (rule  "TypeRhs.intros",(auto)?)
 apply (erule TypeAtom_extendconfiguration_AO,force)
apply (rule  "TypeRhs.intros",(auto)?)
done


lemma TypeStatement_extendconfiguration_AO_Pre[rule_format]:
" ((P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<longrightarrow> (\<forall> \<alpha> X. \<alpha>\<notin>(dom AOs)\<longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>X)) futs,\<Gamma> in C \<turnstile>\<^sub>S S))) \<and> 
  ((P, Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<longrightarrow> (\<forall> \<alpha> X. \<alpha>\<notin>(dom AOs)\<longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>X)) futs,\<Gamma> in C \<turnstile>\<^sub>L Stl)))"
apply (rule TypeStatement_TypeStatementList_induct_Config,auto)
(*5*)
    apply (rule  "TypeStatement_TypeStatementList.intros",auto)
    apply (erule TypeRhs_extendconfiguration_AO,auto)
   apply (rule  "TypeStatement_TypeStatementList.intros",auto)
   apply (erule TypeExpression_extendconfiguration_AO,auto)
  apply (rule  "TypeStatement_TypeStatementList.intros")
(*5*)
    apply (erule TypeAtom_extendconfiguration_AO,auto)
 apply (rule  "TypeStatement_TypeStatementList.intros")
apply (rule  "TypeStatement_TypeStatementList.intros")
 apply auto
done

(* GLOBAL LEMMAS *)
lemma TypeStatement_extendconfiguration_AO:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<Longrightarrow>\<alpha>\<notin>(dom AOs) \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>X)) futs,\<Gamma> in C \<turnstile>\<^sub>S S"
by (insert TypeStatement_extendconfiguration_AO_Pre, auto)

lemma TypeStatementList_extendconfiguration_AO:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow>\<alpha>\<notin>(dom AOs) \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>X)) futs,\<Gamma> in C \<turnstile>\<^sub>L Stl"
by (insert TypeStatement_extendconfiguration_AO_Pre, auto)

section{* extending set of futs in config *}

lemma TypeAtom_extendconfiguration_futs[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Az:T \<Longrightarrow> futs f = None\<longrightarrow>( P,Cn aos (\<lambda>a. if a = f then Some Y else futs a),\<Gamma> in C\<turnstile>\<^sub>Az:T)"
apply (erule  "TypeAtom.induct",auto)
    apply (rule  "TypeValue.cases",auto)
        apply (rule  "TypeAtom.intros",(auto)?)+
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

(* GLOBAL LEMMAS *)
lemma TypeStatement_extendconfiguration_futs:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<Longrightarrow>f\<notin>(dom futs) \<Longrightarrow>P, Cn AOs (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>S S"
by (insert TypeStatement_extendconfiguration_futs_Pre,case_tac Y, simp)

lemma TypeStatementList_extendconfiguration_futs:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow>f\<notin>(dom futs) \<Longrightarrow>P, Cn AOs (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>L Stl"
by (insert TypeStatement_extendconfiguration_futs_Pre,case_tac Y, simp)


section {* extend AOs and futs *}
lemma TypeStatement_extendconfiguration:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<Longrightarrow>\<alpha>\<notin>dom AOs \<Longrightarrow>f\<notin>(dom futs) \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>X)) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>S S"
by (insert TypeStatement_extendconfiguration_futs,insert TypeStatement_extendconfiguration_AO, auto)

lemma TypeStatementList_extendconfiguration:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow>\<alpha>\<notin>dom AOs \<Longrightarrow>f\<notin>(dom futs) \<Longrightarrow>P, Cn (AOs(\<alpha>\<mapsto>X)) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>L Stl"
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
apply clarsimp
 apply (case_tac Act,clarsimp)

apply (drule_tac x= "(AO x1 x2 x3 (aa, b) x5)" in spec)
apply clarsimp
apply (erule impE,force)
apply clarsimp
 apply (intro allI conjI)
apply clarsimp
apply (drule_tac x=x in spec)+
apply (drule_tac x=v in spec)+
apply clarsimp
apply (rule_tac x=T in exI)
apply clarsimp
apply (erule TypeValue_extendconfiguration_AO)
apply clarsimp

(*Q*)
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

(* the current req*)
apply (case_tac x3,auto)
apply (erule TypeRequest.cases)
apply (rule_tac Meth=Meth in TypeRequest.intros)
apply auto
apply (drule_tac x=i in spec,clarsimp)
apply (rule TypeValue_extendconfiguration_AO)
apply auto
apply (drule_tac x=x in bspec,auto)
apply (rule TypeStatement_extendconfiguration_AO)

section{* Well-typed initial configuraiton *}

theorem WTinitialconfiguration: "\<turnstile>\<^sub>P Prog  CL Vars Stl \<Longrightarrow> Prog  ((MainObjClass Vars)#CL) Vars Stl \<turnstile> InitialConfiguration (Prog  CL Vars Stl)"
apply (unfold InitialConfiguration_def BuildInitialConfigurationfromVarsStl_def)
apply (auto,unfold Let_def fetchClass_def fetchMethodInClass_def MainObjClass_def MainMethodEmptyBody_def,auto)
 apply (intro gASPFuturesTypeSystem.TypeRequest.intros, auto simp: fetchClass_def fetchMethodInClass_def )
apply (rule TypeStatementList_TypeStatement,auto)
apply (unfold BuildTypeEnv_def)
apply (rule_tac AOs="empty"  in TypeStatementList_extendconfiguration_AO)
  apply (auto)
done

section {* Subject Reduction *}



theorem SubjectReduction: 
"Prog CL Vars Stl \<turnstile> Cn aos futs   \<leadsto> Cn aos' futs' 
    \<Longrightarrow> (Prog CL Vars Stl \<turnstile> Cn aos futs)  \<longrightarrow> (Prog CL Vars Stl \<turnstile> Cn aos' futs')"
apply (erule gASPFutures.reduction.induct)
(* 11 SERVE *)
apply clarsimp