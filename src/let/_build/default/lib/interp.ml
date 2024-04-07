(*Lukas Mikulenas and Gabby Sokolik
   I plege my honor that I have abided by the Stevens Honor System.*)
   open Parser_plaf.Ast
   open Parser_plaf.Parser
   open Ds
     
   (** [eval_expr e] evaluates expression [e] *)
   let rec eval_expr : expr -> exp_val ea_result =
     fun e ->
     match e with
     | Int(n) ->
       return (NumVal n)
     | Var(id) ->
       apply_env id
     | Add(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       return (NumVal (n1+n2))
     | Sub(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       return (NumVal (n1-n2))
     | Mul(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       return (NumVal (n1*n2))
     | Div(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       if n2==0
       then error "Division by zero"
       else return (NumVal (n1/n2))
     | Let(id,def,body) ->
       eval_expr def >>= 
       extend_env id >>+
       eval_expr body 
     | ITE(e1,e2,e3) ->
       eval_expr e1 >>=
       bool_of_boolVal >>= fun b ->
       if b 
       then eval_expr e2
       else eval_expr e3
     | IsZero(e) ->
       eval_expr e >>=
       int_of_numVal >>= fun n ->
       return (BoolVal (n = 0))
     | Pair(e1,e2) ->
       eval_expr e1 >>= fun ev1 ->
       eval_expr e2 >>= fun ev2 ->
       return (PairVal(ev1,ev2))
     | Fst(e) ->
       eval_expr e >>=
       pair_of_pairVal >>= fun (l,_) ->
       return l
     | Snd(e) ->
       eval_expr e >>=
       pair_of_pairVal >>= fun (_,r) ->
       return r
     | Debug(_e) ->
       string_of_env >>= fun str ->
       print_endline str; 
       error "Debug called"
     | IsEmpty(e) ->
       (eval_expr e >>= fun ev ->
       match ev with
       | TreeVal tree ->
           (match tree with
           | Empty -> return (BoolVal true)
           | _ -> return (BoolVal false))
       | _ -> error "Expected a binary tree")
     | EmptyTree(_t)-> 
        return (TreeVal Empty)
     | Node(e1, e2, e3) -> 
     (eval_expr e1 >>= fun ev1 ->
       eval_expr e2 >>= fun ev2 ->
       eval_expr e3 >>= fun ev3 ->
       match (ev2, ev3) with
       | (TreeVal t2, TreeVal t3) -> 
           return (TreeVal (Node((ev1, t2, t3))))
       | _ -> error "Node: Second or third argument is not a tree")
     | CaseT(e1, e2, id1, id2, id3, e3) ->
       (eval_expr e1 >>= function
       | TreeVal t ->
           (match t with
           | Empty -> eval_expr e2
           | Node(a, l, r) ->
               extend_env id1 a >>+
               extend_env id2 (TreeVal (l)) >>+ 
               extend_env id3 (TreeVal (r)) >>+
               eval_expr e3)
       | _ -> error "CaseT: Expected a tree value")
   
     | Proj(e, id) ->
       (eval_expr e >>= record_of_exp_val) >>= fun lst ->
         find_in_list lst id
     
     | Record(fs) ->
       if find_duplicates fs then
         (fun (_:env) -> Error "Record: duplicate fields")
       else
         eval_exprs (expr_fs fs) >>= fun res ->
           (fun (_:env) -> Ok (RecordVal (join_string (string_fs fs) res)))
     and
       eval_exprs : expr list -> (exp_val list) ea_result = 
       fun es -> 
         match es with 
         | [] -> return []
         | h::t -> eval_expr h >>= fun i ->
           eval_exprs t >>= fun l ->
           return (i::l)
   
   
   (** [eval_prog e] evaluates program [e] *)
   let eval_prog (AProg(_,e)) =
     eval_expr e
   
   
   (** [interp s] parses [s] and then evaluates it *)
   let interp (e:string) : exp_val result =
     let c = e |> parse |> eval_prog
     in run c