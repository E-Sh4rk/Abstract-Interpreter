
(* AST.ml : Parse xml file to AST using xml-light *)
(* Input : XML from nikic/PHP-Parser v1.x (v2.x not tested) *)
(* This AST is not exhaustive and is only relevant for this project needs *)
(* 2016 - Mickaël Laurent *)

(* #load "xml-light.cma";; *)
open Xml;;

(* ---------------------------------- *)

type identifier =
    | Name of string
    | Group of string * identifier (* For example : _POST, _GET, _SESSION... *)
;;

type variable =
    | Var of identifier
    | Case of variable
    (* NOTE : Case should be variable * expression,
       but it's not needed for this project *)
;;

type expression =
    | Bool of bool
    | Int of int
    | Float of float
    | String of string
    | Array of int
    (* NOTE : Array should be expression list,
       but it's not needed for this project *)
    | Value

    | Variable of variable

    | Identical of expression * expression
    | NotIdentical of expression * expression
    | Equal of expression * expression
    | Different of expression * expression
    | Leq of expression * expression
    | Geq of expression * expression
    | Lower of expression * expression
    | Greater of expression * expression

    | Not of expression
    | And of expression * expression
    | Or of expression * expression

    | Multiplied of expression * expression
    | Divided of expression * expression
    | Plus of expression * expression
    | Minus of expression * expression
    | Modulo of expression * expression
    | Concat of expression * expression

    | ToBool of expression
    | ToInt of expression
    | ToFloat of expression
    | ToString of expression
    | ToArray of expression

    | Isset of variable list
    | Sanitize of expression
    | StringInput
    | IntInput of expression * expression
    | FloatInput of expression * expression
    | ExprFunction of string * expression list
;;

type statement =
    | Assign of variable * expression
    | Echo of expression list
    | Unset of variable list
    | Function of string * expression list

    | If of expression * statement list * statement list
    | While of expression * statement list
;;

type program = statement list;;

(* ---------------------------------- *)

let expr_function f = match f with
  | ExprFunction ("str_input", []) -> StringInput
  | ExprFunction ("int_input", [expr1; expr2]) -> IntInput (expr1, expr2)
  | ExprFunction ("flt_input", [expr1; expr2]) -> FloatInput (expr1, expr2)
  | ExprFunction ("sanitize", [expr]) -> Sanitize expr
  | ExprFunction ("array", args) -> Array (List.length args)
  | ExprFunction _ -> f
  | _ -> Utils.error "Not a function !"

let expr_const str = match str with
  | "null" | "NULL" | "Null" -> Value
  | "true" | "TRUE" | "True" -> Bool true
  | "false" | "FALSE" | "False" -> Bool false
  | str -> Utils.error ("Unknow const value "^str^" !")

(* ---------------------------------- *)

let listContains lst e =
  List.exists (fun x -> x = e) lst;;

let findChildren children names =
  let rec _findChildren children = match children with
    | [] -> []
    | Element (name, _, children)::lst when listContains names name -> children
    | a::lst -> _findChildren lst
  in let c = _findChildren children
  in if c = [] then children else c
;;

let rec nextChildren children = match children with
  | [] -> []
  | [Element ("scalar:array", _, children)] -> nextChildren children
  | [Element ("scalar:null", _, _)] -> []
  | children -> children
;;

let enterChildren children names =
  nextChildren (findChildren (nextChildren children) names);;

(* ---------------------------------- *)

let rec parseName children  = match children with
  | [Element ("node:Name", _, children)] -> (
      match enterChildren children ["subNode:parts"] with
        | [] -> ""
        | [PCData(msg)] -> msg
        | [Element (_, _, [])] -> ""
        | [Element (_, _, [PCData(msg)])] -> msg
        | _ -> Utils.error ("Invalid name parts !")
    )
  | _ -> Utils.error ("Invalid or unknow value/name !")
;;

let rec parseValueName children =
  match enterChildren children ["subNode:value"; "subNode:name"] with
    | [] -> ""
    | [PCData(msg)] -> msg
    | [Element (_, _, [])] -> ""
    | [Element (_, _, [PCData(msg)])] -> msg
    | children -> parseName children
;;

let rec countItems children =
  List.length (enterChildren children ["subNode:items"])
;;

let rec parseExpression children = match children with
  | [Element ("node:Expr_ConstFetch", _, children)] ->
      expr_const (parseValueName children)
  | [Element ("node:Scalar_String", _, children)] ->
      String(parseValueName children)
  | [Element ("node:Scalar_LNumber", _, children)] ->
      Int(int_of_string (parseValueName children))
  | [Element ("node:Scalar_DNumber", _, children)] ->
      Float(float_of_string (parseValueName children))
  | [Element ("node:Expr_Array", _, children)] ->
      Array(countItems children)
  | [Element ("node:Expr_Variable", _, children)] ->
      Variable (Var (Name (parseValueName children)))
  | [Element ("node:Expr_ArrayDimFetch", _, children)] -> (
      let var = parseVar children and dim = parseDim children
      in match dim with
        | String (str) -> (
            match var with 
              | Var (identifier) ->
                  Variable (Var (Group (str, identifier)))
              | Case _ ->
                  Variable (Case (var))
          )
        | _ -> Variable (Case (var))
    )
  | [Element ("node:Expr_UnaryPlus", _, children)] ->
      Plus (Int 0, parseExpr children)
  | [Element ("node:Expr_UnaryMinus", _, children)] ->
      Minus (Int 0, parseExpr children)
  | [Element ("node:Expr_BinaryOp_Plus", _, children)] ->
      Plus (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Minus", _, children)] ->
      Minus (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Mul", _, children)] ->
      Multiplied (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Div", _, children)] ->
      Divided (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Mod", _, children)] ->
      Modulo (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Concat", _, children)] ->
      Concat (parseLeft children, parseRight children)
  | [Element ("node:Expr_BooleanNot", _, children)] ->
      Not (parseExpr children)
  | [Element ("node:Expr_BinaryOp_BooleanAnd", _, children)] ->
      And (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_BooleanOr", _, children)] ->
      Or (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Equal", _, children)] ->
      Equal (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_NotEqual", _, children)] ->
      Different (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Identical", _, children)] ->
      Identical (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_NotIdentical", _, children)] ->
      NotIdentical (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Smaller", _, children)] ->
      Lower (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_SmallerOrEqual", _, children)] ->
      Leq (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_Greater", _, children)] ->
      Greater (parseLeft children, parseRight children)
  | [Element ("node:Expr_BinaryOp_GreaterOrEqual", _, children)] ->
      Geq (parseLeft children, parseRight children)
  | [Element ("node:Expr_FuncCall", _, children)] ->
      expr_function (ExprFunction (parseValueName children, parseArgs children))
  | [Element ("node:Expr_Cast_Bool", _, children)] ->
      ToBool (parseExpr children)
  | [Element ("node:Expr_Cast_Int", _, children)] ->
      ToInt (parseExpr children)
  | [Element ("node:Expr_Cast_Double", _, children)] ->
      ToFloat (parseExpr children)
  | [Element ("node:Expr_Cast_String", _, children)] ->
      ToString (parseExpr children)
  | [Element ("node:Expr_Cast_Array", _, children)] ->
      ToArray (parseExpr children)
  | [Element ("node:Expr_Isset", _, children)] ->
      Isset (parseVars children)
  | [Element (name, attr, children)] ->
      Utils.error ("Unknow expression type : " ^ name)
  | _ -> Utils.error ("Invalid expression !")

and parseExpr children =
  parseExpression (enterChildren children ["subNode:expr"])

and parseExprs children =
  let children = enterChildren children ["subNode:exprs"]
  in List.map (fun x -> parseExpression [x]) children

and parseArgs children = 
  let rec _parseArgs children = match children with
    | [] -> []
    | Element("node:Arg", _, children)::lst
      -> (parseExpression (enterChildren children ["subNode:value"]))::(_parseArgs lst)
    | _ -> Utils.error ("Invalid args structure !")
  in _parseArgs (enterChildren children ["subNode:args"])

and parseLeft children =
  parseExpression (enterChildren children ["subNode:left"])

and parseRight children =
  parseExpression (enterChildren children ["subNode:right"])

and parseDim children =
  parseExpression (enterChildren children ["subNode:dim"])

and parseVar children =
  match parseExpression (enterChildren children ["subNode:var"]) with
    | Variable (variable) -> variable
    | _ -> Utils.error ("Invalid or unknow variable !")

and parseVars children =
  let children = enterChildren children ["subNode:vars"]
  in List.map (fun x -> parseVar [x]) children

;;

(* ---------------------------------- *)

let rec parseStatements children =
  let rec parseStatement child = match child with
    | Element("node:Stmt_Echo", _, children) ->
        [Echo(parseExprs children)]
    | Element("node:Expr_Assign", _, children) ->
        [Assign(parseVar children, parseExpr children)]
    | Element("node:Expr_AssignOp_Plus", _, children) -> (
        let var = parseVar children in
          [Assign(var, Plus(Variable (var), parseExpr children))]
      )
    | Element("node:Expr_AssignOp_Minus", _, children) -> (
        let var = parseVar children in
          [Assign(var, Minus(Variable (var), parseExpr children))]
      )
    | Element("node:Stmt_Unset", _, children) ->
        [Unset(parseVars children)]
    | Element("node:Stmt_If", _, children) -> 
        [If (parseCond children, parseStmts children, parseElseifs children (parseElse children))]
    | Element("node:Stmt_While", _, children) -> 
        [While (parseCond children, parseStmts children)]
    | Element("node:Expr_FuncCall", _, children) -> 
        [Function (parseValueName children, parseArgs children)]
    | Element("node:Stmt_For", _, children) -> 
        (parseInit children)@[While (parseCond children, (parseStmts children)@(parseLoop children))]
    | Element("node:Stmt_InlineHTML", _, children) -> 
        []
    | Element (name, attr, children) ->
        Utils.error ("Unknow statement type : " ^ name)
    | _ -> Utils.error ("Invalid statement !")
  in List.fold_right (fun e acc -> (parseStatement e)@acc) (enterChildren children []) []

and parseCond children =
  parseExpression (enterChildren children ["subNode:cond"])

and parseInit children =
  parseStatements (enterChildren children ["subNode:init"])

and parseLoop children =
  parseStatements (enterChildren children ["subNode:loop"])

and parseStmts children =
  parseStatements (enterChildren children ["subNode:stmts"])

and parseElse children = match enterChildren children ["subNode:else"] with
  | [] -> []
  | [Element("node:Stmt_Else", _, children)] -> parseStmts children
  | _ -> Utils.error ("Invalid else structure !")

and parseElseifs children elseStatements =
  let rec _parseEI lst = match lst with
    | [] -> elseStatements
    | Element("node:Stmt_ElseIf", _, children)::lst -> (
        [If (parseCond children, parseStmts children, _parseEI lst)]
      )
    | _ -> Utils.error ("Invalid elseif structure !")
  in _parseEI (enterChildren children ["subNode:elseifs"])
;;

let parseToAST xml = parseStatements (enterChildren xml ["AST"]);;

let parseFile file = parseToAST [Xml.parse_file file];;
