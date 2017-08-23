theory gASPFuturesTypeSystem imports gASPFutures begin

definition BuildTypeEnv ::"(ASPType * VarName) list \<Rightarrow> VarName \<Rightarrow>ASPType option"
where
"BuildTypeEnv VarDeclList =  (map_of (map prod.swap (VarDeclList)))"

inductive Subtype :: "Program\<Rightarrow>ASPType \<Rightarrow>ASPType \<Rightarrow>bool "  (" _\<turnstile>_\<sqsubseteq>_" 50)
 where
 "P\<turnstile>T\<sqsubseteq>T"
|
 "P\<turnstile>BType T\<sqsubseteq>FutType T"
|
 "P\<turnstile>BType (TObj C)\<sqsubseteq>BType AnyObject"
|
 "P\<turnstile>FutType (TObj C)\<sqsubseteq>FutType AnyObject"

inductive TypeValue :: "Program\<Rightarrow>Configuration\<Rightarrow>Value \<Rightarrow> ASPType \<Rightarrow> bool"  ("_,_\<turnstile>\<^sub>V_:_" 50)
where
 "P,Conf \<turnstile>\<^sub>V ASPInt n: BType Integer"
|
 "P,Conf \<turnstile>\<^sub>V ASPBool b: BType Boolean"
|
 "P,Conf \<turnstile>\<^sub>V null :  BType (AnyObject)"
|
 "Acts \<alpha>= Some(AO C' state R Ec Rq)
\<Longrightarrow> P,Cn Acts Futs \<turnstile>\<^sub>V ActRef \<alpha>:  BType (TObj C')"  (*dynamic obj*)
|
 "Futs f = Some(T,V)
\<Longrightarrow> P,Cn Acts Futs \<turnstile>\<^sub>V FutRef f: FutType T"  (*dynamic fut*)

inductive TypeExpression :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Expression \<Rightarrow>ASPType \<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>E_:_" 50)
 where
 " P,Config \<turnstile>\<^sub>V v:T \<Longrightarrow> P,config,\<Gamma> in C \<turnstile>\<^sub>E Val v:T"
|
" P,Cn Acts Futs,\<Gamma> in C \<turnstile>\<^sub>E Var This:  BType (TObj C)  (*This*)
  " 
|
" \<Gamma> x = Some T \<Longrightarrow>P,Cn Acts Futs,\<Gamma>  in C\<turnstile>\<^sub>E Var (Id x) : T (* Var or field reference *)
  "
|
"\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:BType Integer; P,Config,\<Gamma> in C \<turnstile>\<^sub>E e':BType Integer
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>Ee+\<^sub>Ae':BType Integer"
|
"P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow>  P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T' " (* subtype*)


inductive TypeRhs  :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow> Rhs \<Rightarrow>ASPType \<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>R_:_" 50)
 where
  (* Expression *)
 " P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (Expr e):T"
|  (* method call*)
 "\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:BType (TObj C') ; fetchClass P C' = Some Class;
   fetchMethodInClass Class m = Some Meth;
   param_types= map fst (MParams Meth) ; length param_types = length el ; \<forall> i<length el. (P,Config,\<Gamma> in C \<turnstile>\<^sub>E el!i:(param_types!i)) \<rbrakk>
\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (e.\<^sub>Am(el)):MakeFutureType (MRType Meth)"
|  (* new active *)
"\<lbrakk>  fetchClass P C' = Some Class;
   Class_param_types = map fst (ClassParameters Class);
   length Class_param_types = length el ; \<forall> i<length el. (P,Config,\<Gamma> in C \<turnstile>\<^sub>E el!i:(Class_param_types!i)) \<rbrakk>
\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (newActive C'(el)):BType (TObj C')"
| (* Get *)
" P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:(FutType T)    \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (Get e):BType (T)"
|
"P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow>  P,Config,\<Gamma> in C \<turnstile>\<^sub>R e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R e:T' "   (* subtype*)

inductive TypeStatement  :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Statement\<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>S _ " 50)
and TypeStatementList ::"Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Statement list\<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>L _ " 50)
 where
 "\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>R a:T; 
    \<Gamma> x = Some T' ; P\<turnstile>T\<sqsubseteq>T'
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>S (x=\<^sub>A a) "
|
 "\<lbrakk> fetchClass P C = Some Class;
   fetchMethodInClass Class m = Some Meth;
   MRType Meth = T';
   P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T; 
    \<Gamma> x = Some T' ; P\<turnstile>T\<sqsubseteq>T'
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>S return e "
|
 "\<lbrakk>
   P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:BType Boolean; 
   P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl;  P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl'
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>S IF e THEN sl ELSE sl' "
|
"P,Config,\<Gamma> in C \<turnstile>\<^sub>L [] "
|
"P,Config,\<Gamma> in C \<turnstile>\<^sub>S s\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl\<Longrightarrow>P,Config,\<Gamma> in C \<turnstile>\<^sub>L s;;sl "


fun TypeClass :: "Program \<Rightarrow> Class \<Rightarrow>bool" ("_ \<turnstile>\<^sub>C _ " 50)
where
" (P\<turnstile>\<^sub>CClass) = (let C_param_env = (map_of (map prod.swap (ClassParameters Class))) in
               (\<forall> M\<in> set (Methods Class). 
               let \<Gamma> = C_param_env ++ (map_of (map prod.swap (LocalVariables M))) ++ (map_of (map prod.swap (MParams M))) in
               (P,EmptyConfig,\<Gamma> in (Name Class) \<turnstile>\<^sub>L (Body M) ) ) ) "

primrec TypeProgram :: "Program \<Rightarrow>bool" ("\<turnstile>\<^sub>P _ " 50)
where
" (\<turnstile>\<^sub>PProg CL MainVars MainBody) = (let P = Prog ((MainObjClass MainVars)#CL) MainVars MainBody in
                          ( (\<forall> C\<in>set CL. (P\<turnstile>\<^sub>CC)) \<and>
                            (let \<Gamma> = (map_of (map prod.swap (MainVars))) in
                              (P,EmptyConfig,\<Gamma> in (''MainClass'') \<turnstile>\<^sub>L MainBody )  ) ) )
"

inductive TypeRequest :: "Program \<Rightarrow> Configuration\<Rightarrow> ClassName \<Rightarrow>Request \<Rightarrow> bool"  ("_,_ in _ \<turnstile>\<^sub>Q _" 50)
where 
" \<lbrakk> fetchClass P C =   Some Class ;
    fetchMethodInClass Class m = Some Meth; 
    param_types= map fst (MParams Meth);
    length vl = length param_types ;  \<forall> i <length vl . (P, Cn Acts Futs\<turnstile>\<^sub>V(vl!i):(param_types!i));
    Futs f = Some (T, Undefined); T=GetBasicType (MRType Meth)
\<rbrakk>
\<Longrightarrow>P,Cn Acts Fut in C\<turnstile>\<^sub>Q(f,m,vl)"

primrec TypeConfig :: "Program \<Rightarrow>Configuration \<Rightarrow>bool" ("_ \<turnstile> _ " 50)
where
" (P\<turnstile>Cn AOs Futures) =
((\<forall> Act\<in> ran AOs. case Act of (AO C state R Ec Rq) \<Rightarrow>
   (\<exists> CL . (fetchClass P C = Some CL \<and>
    (
     (* check state *)
     ( (  \<forall> x v. (state(x) =Some  v \<longrightarrow> (\<exists> T . (T,x)\<in> set (ClassParameters CL) \<and> (P,Cn AOs Futures\<turnstile>\<^sub>V v: T))) ) )
     (* check request queue*)
     \<and> (\<forall> R'\<in>set Rq. (P, (Cn AOs Futures) in C \<turnstile>\<^sub>Q R' ) )
     (* check current request*)
     \<and> 
     (case R of Some  (f,m,vl) \<Rightarrow>
         (\<exists> Meth. fetchMethodInClass CL m = Some Meth \<and>
           (P, Cn AOs Futures in C \<turnstile>\<^sub>Q (f,m,vl)) 
           \<and> (case Ec of (locs,Stl) \<Rightarrow> ( \<forall> s\<in>set Stl. 
             (P,Cn AOs Futures,(BuildTypeEnv (ClassParameters CL))++(BuildTypeEnv (LocalVariables Meth))++(BuildTypeEnv (MParams Meth)) in C \<turnstile>\<^sub>S s)
        )) ) ) )))) \<and>
   (* Futures *)
(\<forall> futs\<in> ran Futures. case futs of
      (T,Undefined) \<Rightarrow> True |
      (T,FutVal v) \<Rightarrow> (P,Cn AOs Futures \<turnstile>\<^sub>V v: (FutType T))))
"


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


lemma WTinitialconfiguration: "\<turnstile>\<^sub>P Prog  CL Vars Stl \<Longrightarrow> Prog  ((MainObjClass Vars)#CL) Vars Stl \<turnstile> InitialConfiguration (Prog  CL Vars Stl)"
apply (unfold InitialConfiguration_def BuildInitialConfigurationfromVarsStl_def)
apply (auto,unfold Let_def fetchClass_def fetchMethodInClass_def MainObjClass_def MainMethodEmptyBody_def,auto)
apply (intro gASPFuturesTypeSystem.TypeRequest.intros, auto simp: fetchClass_def fetchMethodInClass_def )
apply (rule TypeStatementList_TypeStatement,auto)
apply (unfold BuildTypeEnv_def)
apply (rule_tac AOs="empty"  in TypeStatementList_extendconfiguration_AO)
apply (auto)
done
