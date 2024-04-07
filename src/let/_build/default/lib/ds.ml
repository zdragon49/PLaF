(*Lukas Mikulenas and Gabby Sokolik
   I plege my honor that I have abided by the Stevens Honor System.*)
   open Parser_plaf.Ast

   type 'a tree = Empty | Node of 'a * 'a tree * 'a tree
   type exp_val =
     | NumVal of int
     | BoolVal of bool
     | PairVal of exp_val*exp_val
     | TupleVal of exp_val list
     | TreeVal of exp_val tree
     | RecordVal of ((string*exp_val) list)
   type env =
     | EmptyEnv
     | ExtendEnv of string*exp_val*env
   
   
   (* Environment Abstracted Result *)
   
   type 'a result = Ok of 'a | Error of string
   
   type 'a ea_result = env -> 'a result
     
   let return : 'a -> 'a ea_result =
     fun v ->
     fun _env ->
     Ok v
   
   let error : string -> 'a ea_result = fun s ->
     fun _env -> 
     Error s
   
   let (>>=) : 'a ea_result -> ('a -> 'b ea_result) -> 'b ea_result = fun c f ->
     fun env ->
     match c env with
     | Error err -> Error err
     | Ok v -> f v env
   
   let (>>+) : env ea_result -> 'a ea_result -> 'a ea_result =
     fun c d ->
     fun env ->
     match c env with
     | Error err -> Error err
     | Ok newenv -> d newenv
   
   let run : 'a ea_result -> 'a result =
     fun c ->
     c EmptyEnv
   
   let lookup : env ea_result = fun env ->
     Ok env
   
   let rec sequence : 'a ea_result list -> 'a list ea_result =
     fun l ->
     match l with
     | [] -> return []
     | h::t ->
       h >>= fun ev ->
       sequence t >>= fun evs ->
       return (ev::evs)
         
   (* Operations on environments *)
   
   let empty_env : unit -> env ea_result = fun () ->
     return EmptyEnv
   
   let extend_env : string -> exp_val -> env ea_result = fun id v env ->
     Ok (ExtendEnv(id,v,env))
   
   let rec extend_env_list_helper =
     fun ids evs en ->
     match ids,evs with
     | [],[] -> en
     | id::idt,ev::evt ->
       ExtendEnv(id,ev,extend_env_list_helper idt evt en)
     | _,_ -> failwith
                "extend_env_list_helper: ids and evs have different sizes"
     
   let extend_env_list =
     fun ids evs ->
     fun en ->
     Ok (extend_env_list_helper ids evs en)
       
   let rec apply_env : string -> exp_val ea_result = fun id env ->
     match env with
     | EmptyEnv -> Error (id^" not found!")
     | ExtendEnv(v,ev,tail) ->
       if id=v
       then Ok ev
       else apply_env id tail
   
   
   
   (* operations on expressed values *)
   
   let int_of_numVal : exp_val -> int ea_result =  function
     |  NumVal n -> return n
     | _ -> error "Expected a number!"
   
   let bool_of_boolVal : exp_val -> bool ea_result =  function
     |  BoolVal b -> return b
     | _ -> error "Expected a boolean!"
   
   let list_of_tupleVal : exp_val -> (exp_val list)  ea_result =  function
     |  TupleVal l -> return l
     | _ -> error "Expected a tuple!"
              
   let pair_of_pairVal : exp_val -> (exp_val*exp_val) ea_result =  function
     |  PairVal(ev1,ev2) -> return (ev1,ev2)
     | _ -> error "Expected a pair!"
   let tree_of_treeval : exp_val -> exp_val tree ea_result = function
     |  TreeVal t -> return t
     | _ -> error "Expected a tree!"
   
   let record_of_exp_val a = 
     fun _ -> 
       match a with 
       | RecordVal lst -> Ok lst 
       | _ -> Error " Expected a record "
   
   let rec find_in_list (a:(string*exp_val) list) (b:string) : (exp_val ea_result) = 
       fun (c:env) -> 
       (
         match a with 
         | [] -> Error "Proj : field does not exist "
         | (id,expr)::t -> if (id = b) then (Ok(expr)) else (find_in_list t b c) 
       )  
   
   let rec string_fs a =
     match a with 
     | [] -> []
     | (str, _)::t -> str :: string_fs t
       
   let rec expr_fs a =
       match a with 
       | [] -> []
       | (_, (_, ex))::t -> ex :: expr_fs t
     
   let rec join_string a b =
     match a, b with
     | [], [] -> []
     | h1::t1, h2::t2 -> (h1, h2) :: join_string t1 t2
   
   let rec find_duplicates a =
       match a with 
     | [] -> false
     | (s, _)::t -> if List.exists (fun (d, _) -> s = d) t then true else find_duplicates t 
   
   let rec string_of_expval = function
     | NumVal n -> "NumVal " ^ string_of_int n
     | BoolVal b -> "BoolVal " ^ string_of_bool b
     | PairVal (ev1,ev2) -> "PairVal("^string_of_expval ev1
                            ^","^ string_of_expval ev2^")"
     | TupleVal evs -> "TupleVal("^String.concat "," (List.map string_of_expval evs)^")"
    
   
   let rec string_of_env' ac = function
     | EmptyEnv ->  "["^String.concat ",\n" ac^"]"
     | ExtendEnv(id,v,env) -> string_of_env' ((id^":="^string_of_expval v)::ac) env
   
   let string_of_env : string ea_result =
     fun env ->
     match env with
     | EmptyEnv -> Ok ">>Environment:\nEmpty"
     | _ -> Ok (">>Environment:\n"^ string_of_env' [] env)