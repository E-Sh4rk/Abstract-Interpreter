
(* AI.ml : Abstract Interpretation *)
(* 2016 - Mickaël Laurent *)

open AST;;

module Env = Environment.Make (Value.Mixed)

let rec widen_until_fixed_point env cond body =
  let new_env = execute (Env.assume env cond) body
  in let wide_env = Env.widen env new_env
  in match wide_env with
    | wide_env when Env.equal env wide_env -> wide_env
    | wide_env -> widen_until_fixed_point wide_env cond body

and execute env statements = List.fold_left exec env statements
and exec env statement = match statement with
  | Assign (var, expr) -> Env.assign env var expr
  | Echo args -> List.fold_left Env.echo env args
  | Unset args -> List.fold_left Env.unset env args
  | Function (name, args) -> env

  | If (cond, if_block, else_block) ->
      let path1 = execute (Env.assume env cond) if_block
      and path2 = execute (Env.assume env (Not cond)) else_block
      in Env.join path1 path2

  | While (cond, body) ->
      let path1 = Env.assume env (Not cond) (* Sort en 0 tour *)
      in let env = execute (Env.assume env cond) body (* Valeurs possibles après 1 tour *)
      in let path2 = Env.assume env (Not cond) (* Sort en 1 tour *)
      (* Valeurs possibles après au moins 2 tours *)
      in let env = execute (Env.assume (widen_until_fixed_point env cond body) cond) body
      in let path3 = Env.assume env (Not cond) (* Sort en 2+ tours *)
      in Env.join (Env.join path1 path2) path3
;;

let () = let env = execute (Env.init ()) (AST.parseFile "file.xml")
  in print_string (Env.print env);;
