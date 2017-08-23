theory TypeTheorems imports gASPFuturesTypeSystem begin

section{* Basic Lemmas *}

lemma TypeStatementList_TypeStatement[rule_format]: 
"(P,Config,\<Gamma> in C \<turnstile>\<^sub>L Stl)  \<longrightarrow> (S \<in> set Stl\<longrightarrow> (P,Config,\<Gamma> in C \<turnstile>\<^sub>S S))"
apply (induct_tac Stl)
apply simp
apply clarsimp
apply (drule TypeStatementList.cases,auto)
done

lemma TypeStatement_TypeStatementList_induct_Config:
"  (\<And>P aos futs \<Gamma> C a T x T'. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T \<Longrightarrow> \<Gamma> x = Some T' \<Longrightarrow>  P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow> P1 P aos futs \<Gamma> C (x =\<^sub>A a)) \<Longrightarrow>
    (\<And>P C Class m Meth T' aos futs \<Gamma> e T x. fetchClass P C = Some Class \<Longrightarrow> fetchMethodInClass Class m = Some Meth \<Longrightarrow> MRType Meth = T' \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow> \<Gamma> x = Some T' \<Longrightarrow>  P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow> P1 P aos futs \<Gamma> C (return e)) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C e  sl sl'. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:BType Boolean \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>L sl  \<Longrightarrow> P2 P aos futs \<Gamma> C sl \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>L sl'  \<Longrightarrow> P2 P aos futs \<Gamma> C sl' \<Longrightarrow> P1 P aos futs \<Gamma> C (IF e THEN sl ELSE sl' )) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C. P2 P aos futs \<Gamma> C []) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C s sl. P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>S s  \<Longrightarrow> P1 P aos futs \<Gamma> C s \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>L sl  \<Longrightarrow> P2 P aos futs \<Gamma> C sl \<Longrightarrow> P2 P aos futs \<Gamma> C (s ;; sl)) \<Longrightarrow>
    (P,Cn aos futs,\<Gamma> in x4\<turnstile>\<^sub>S x5  \<longrightarrow> P1 P aos futs \<Gamma> x4 x5) \<and> (P',Cn aos' futs',\<Gamma>' in x9\<turnstile>\<^sub>L x10  \<longrightarrow> P2 P' aos' futs' \<Gamma>'  x9 x10)"
apply (insert gASPFuturesTypeSystem.TypeStatement_TypeStatementList.induct [of "\<lambda> x conf y z t. (P1 x (Conf_AOs conf) (Conf_futs conf) y z t)" "\<lambda> x conf y z t. (P2 x (Conf_AOs conf) (Conf_futs conf) y z t)" P "Cn aos futs" \<Gamma> x4 x5 P' "Cn aos' futs'" \<Gamma>' x9 x10])
apply rule
apply (drule meta_impE,auto,case_tac Config,auto)+
done

lemma TypeRhs_induct_Config:
"(P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>RR: T)\<Longrightarrow>
    (\<And>P aos futs \<Gamma> C e T. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T) \<Longrightarrow> P1 P aos futs \<Gamma> C (Expr e) T) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C e C' Class m Meth param_types el.
        (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:BType (TObj C')) \<Longrightarrow>
        fetchClass P C' = Some Class \<Longrightarrow> fetchMethodInClass Class m = Some Meth \<Longrightarrow> param_types = map fst (MParams Meth) \<Longrightarrow> length param_types = length el \<Longrightarrow> \<forall>i<length el. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Eel ! i:param_types ! i) \<Longrightarrow> P1 P  aos futs \<Gamma> C (e.\<^sub>Am(el)) (MakeFutureType (MRType Meth))) \<Longrightarrow>
    (\<And>P C' Class Class_param_types el aos futs \<Gamma> C. fetchClass P C' = Some Class \<Longrightarrow> Class_param_types = map fst (ClassParameters Class) \<Longrightarrow> length Class_param_types = length el \<Longrightarrow> \<forall>i<length el. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>E(el ! i):(Class_param_types ! i)) \<Longrightarrow> P1 P  aos futs \<Gamma> C (newActive C'(el)) (BType (TObj C'))) \<Longrightarrow>
    (\<And>P aos futs \<Gamma> C e T. (P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:FutType T) \<Longrightarrow> P1 P  aos futs \<Gamma> C (Get e) (BType T)) \<Longrightarrow> (\<And>P T T'  aos futs \<Gamma> C e.  P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow> P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Re:T \<Longrightarrow> P1 P  aos futs \<Gamma> C e T \<Longrightarrow> P1 P aos futs \<Gamma> C e T') 
\<Longrightarrow> P1 P aos futs \<Gamma> C R T"
apply (insert TypeRhs.induct [of  P "Cn aos futs" \<Gamma> C R T "\<lambda> x conf y z t. (P1 x (Conf_AOs conf) (Conf_futs conf) y z t)"])
apply auto
apply (drule meta_impE,auto,case_tac Config,auto)+
done

lemma TypeExpression_extendconfiguration_AO[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ee:T \<Longrightarrow> (aos \<alpha> = None \<longrightarrow> (futs f = None\<longrightarrow>( P,Cn (\<lambda>a. if a = \<alpha> then Some X else AOs a) (\<lambda>a. if a = f then Some Y else futs a),\<Gamma> in C\<turnstile>\<^sub>Ee:T)))"
apply (erule  "TypeExpression.induct",auto)
apply (rule  "TypeValue.cases",auto)
apply (rule  "TypeExpression.intros",(auto)?)+
done

lemma TypeRhs_extendconfiguration_AO[rule_format]:
"P,Cn aos futs,\<Gamma> in C\<turnstile>\<^sub>Ra:T \<Longrightarrow> (aos \<alpha> = None \<longrightarrow> (futs f = None\<longrightarrow>(P,Cn (\<lambda>a. if a = \<alpha> then Some X else AOs a) (\<lambda>a. if a = f then Some Y else futs a),\<Gamma> in C\<turnstile>\<^sub>Ra:T)))"
apply (erule  "TypeRhs_induct_Config",auto)
apply (rule  "TypeRhs.intros",(auto)?)
apply (erule TypeExpression_extendconfiguration_AO,auto)
apply (rule  "TypeRhs.intros",(auto)?)
apply (erule TypeExpression_extendconfiguration_AO,auto)
apply (rule_tac aos=aos in TypeExpression_extendconfiguration_AO)
apply (drule_tac x=i in spec,auto)
apply (rule  "TypeRhs.intros",(auto)?)
apply (rule_tac aos=aos in TypeExpression_extendconfiguration_AO)
apply (drule_tac x=i in spec,auto)
apply (rule  "TypeRhs.intros",(auto)?)
apply (erule TypeExpression_extendconfiguration_AO,force,force)
apply (rule  "TypeRhs.intros",(auto)?)
done

lemma TypeStatement_extendconfiguration_AO_Pre[rule_format]:
" ((P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<longrightarrow> (\<forall> \<alpha> X. \<alpha>\<notin>(dom AOs)\<longrightarrow>(\<forall> f Y. f\<notin>(dom futs)\<longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>X)) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>S S)))) \<and> 
  ((P, Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<longrightarrow> (\<forall> \<alpha> X. \<alpha>\<notin>(dom AOs)\<longrightarrow>(\<forall> f Y. f\<notin>(dom futs)\<longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>X)) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>L Stl))))"
apply (rule TypeStatement_TypeStatementList_induct_Config,auto)
apply (rule  "TypeStatement_TypeStatementList.intros",auto)
apply (erule TypeRhs_extendconfiguration_AO,auto)
apply (rotate_tac -1,erule contrapos_pp,force)
apply (rule  "TypeStatement_TypeStatementList.intros",auto)
apply (erule TypeExpression_extendconfiguration_AO,auto)
apply (rotate_tac -1,erule contrapos_pp,force)
apply (rule  "TypeStatement_TypeStatementList.intros")
apply (erule TypeExpression_extendconfiguration_AO,auto)
apply (rotate_tac -1,erule contrapos_pp,force)
apply (drule_tac x=\<alpha> in spec)+
apply force
apply (drule_tac x=\<alpha> in spec)+
apply force
apply (rule  "TypeStatement_TypeStatementList.intros")
apply (rule  "TypeStatement_TypeStatementList.intros")
apply (drule_tac x=\<alpha> in spec)+
apply force
apply (drule_tac x=\<alpha> in spec)+
apply force
done

lemma TypeStatement_extendconfiguration_AO:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>S S) \<Longrightarrow> \<alpha>\<notin>dom AOs \<Longrightarrow>f\<notin> dom futs \<Longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>X)) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>S S) "
by (case_tac Y,insert TypeStatement_extendconfiguration_AO_Pre,auto)

lemma TypeStatementList_extendconfiguration_AO:
" (P,Cn AOs futs,\<Gamma> in C \<turnstile>\<^sub>L Stl) \<Longrightarrow> \<alpha>\<notin>(dom AOs) \<Longrightarrow>f\<notin> dom futs \<Longrightarrow> (P, Cn (AOs(\<alpha>\<mapsto>X)) (futs(f\<mapsto>Y)),\<Gamma> in C \<turnstile>\<^sub>L Stl) "
by (case_tac Y,insert TypeStatement_extendconfiguration_AO_Pre,auto)

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
