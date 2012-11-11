datatype exp     = Ident of string
                 | Const of int
                 | Plus of exp * exp
                 | Minus of exp * exp
                 | Mult of exp * exp;
datatype boolExp = LessThan of exp * exp
                 | MoreThan of exp * exp
                 | Equal of exp * exp;


 (* incomplete *)
datatype decl      = Var of string * exp;
datatype direction = N | S | E | W;
datatype move      = Forward | Backward | Left | Right;
datatype stmt      = Start of exp*exp*direction
                   | Stop
  (* Pen *)        | PenUp | PenDown
  (* Move *)       | Forward of exp | Backward of exp | Right of exp | Left of exp
  (* Assignment *) | Assignment of string * exp
  (* If *)         | IfThenElse of boolExp * stmt list * stmt list
  (* While *)      | While of boolExp * stmt list;

datatype grid    = Size of int * int;
datatype robot   = R of decl list * stmt list;
datatype program = P of grid * robot;

(*val p1 = [Stop];*)

(*val p2 = [Start (Const 0, Const 0, N), Stop];*)

val decls1 = [Var ("x", Const 5)
             ,Var ("y", Ident "x")
             ,Var ("z", Ident "a")];

(*
- val State (_,_,_,_,bs) = initialState decls1 (State ((), Up, (0,0), N, fn _ => NONE));
val bs = fn : bindings
- bs "x";
val it = SOME 5 : int option
- bs "y";

uncaught exception Fail [Fail: not implemented yet]
  raised at: m.sml:47.36-47.62
*)

(*
val p = [Start (Const 23, Const 30, S)
        ,Forward (Const 15)
        ,PenUp
        ,Left (Const 15)
        , Right (Add (Const 2) (Const 3))
        , PenDown
        , Backward (Add (Const 10) (Const 27))
        , Stop];
*)

datatype pen  = Up | Down;
type position = int*int;
type board    = unit; (* ... *)
type bindings = string -> int option;

datatype state = State of board * pen * position * direction * bindings;

fun eval binding (Const i) = i 
  | eval binding (Ident var) = valOf (binding var)
  | eval binding (Plus (a,b)) = (eval binding a) + (eval binding b)
  | eval binding (Minus (a,b)) = (eval binding a) - (eval binding b)
  | eval binding (Mult (a,b)) = (eval binding a) * (eval binding b);
  (*| eval binding _ = raise Fail "not implemented yet"; *)


fun evalBoolExp bindings (LessThan (a,b)) = (eval bindings a) < (eval bindings b)
  | evalBoolExp bindings (Equal (a,b))    = (eval bindings a) = (eval bindings b)
  | evalBoolExp bindings (MoreThan (a,b)) = (eval bindings a) > (eval bindings b);
  
(* Could use `fold` here *)
fun initialState nil acc = acc
  | initialState ((Var (v,e))::vs) (State (b,p,pos,dir,find)) = initialState vs (State (b,p,pos,dir, fn var => if (var = v) then SOME (eval (find) e)
                                                                                                                            else find var));

(* TODO: take direction into account *)
fun calculatePos (x,y) N i "R" = (x+i,y)
  | calculatePos (x,y) S i "R" = (x-i,y)
  | calculatePos (x,y) E i "R" = (x,y-i)
  | calculatePos (x,y) W i "R" = (x,y+i)
  | calculatePos (x,y) N i "L" = (x-i,y)
  | calculatePos (x,y) S i "L" = (x+i,y)
  | calculatePos (x,y) E i "L" = (x,y+i)
  | calculatePos (x,y) W i "L" = (x,y-i)
  | calculatePos (x,y) N i "F" = (x,y+i)
  | calculatePos (x,y) S i "F" = (x,y-i)
  | calculatePos (x,y) E i "F" = (x+i,y)
  | calculatePos (x,y) W i "F" = (x-i,y)
  | calculatePos (x,y) N i "B" = (x,y-i)
  | calculatePos (x,y) S i "B" = (x,y+i)
  | calculatePos (x,y) E i "B" = (x-i,y)
  | calculatePos (x,y) W i "B" = (x+i,y);

fun calculateDir dir "F" = dir
  | calculateDir  N  "R" = E
  | calculateDir  N  "L" = W
  | calculateDir  N  "B" = S
  | calculateDir  S  "R" = W
  | calculateDir  S  "L" = E
  | calculateDir  S  "B" = N
  | calculateDir  E  "R" = S
  | calculateDir  E  "L" = N
  | calculateDir  E  "B" = W
  | calculateDir  W  "R" = N
  | calculateDir  W  "L" = S
  | calculateDir  W  "B" = E;

(* Step takes a state and a list of statements. Execute the first statement, and obtain an intermediate state.
   If we need to continue (i.e. not STOP), then use intermediate state to interpret remaining statements.
   Interpret runs the whole program. TODO: when and how do we stop?
*)
fun interpret (P (gr,R (decls,stmts))) = step (initialState decls (State ((), Up, (0,0), N, fn _ => NONE))) stmts
and step state (Stop::_) = state

  (* START *)
  | step (State (b,p,pos,dir,bs)) (Start(ex1, ex2, d)::ss) =  let
                                                                val dir = d;
                                                                val e1 = eval bs ex1;
                                                                val e2 = eval bs ex2;
                                                              in
                                                                step (State (b,Up,(e1, e2),dir,bs)) ss
                                                              end

  (* RIGHT *)
  | step (State (b,p,pos,dir,bs)) (Right e::ss)            =  let
                                                                val v = eval bs e;
                                                                val s = State (b,p, calculatePos pos dir v "R", calculateDir dir "R", bs);
                                                              in step s ss end

  (* LEFT *)
  | step (State (b,p,pos,dir,bs)) (Left e::ss)             =  let
                                                                val v = eval bs e
                                                                val s = State (b,p, calculatePos pos dir v "L", calculateDir dir "L", bs);
                                                              in step s ss end

  (* FORWARD *)
  | step (State (b,p,pos,dir,bs)) (Forward e::ss)          =  let
                                                                val v = eval bs e
                                                                val s = State (b,p, calculatePos pos dir v "F", calculateDir dir "F", bs);
                                                              in step s ss end

  (* BACKWARD *)
  | step (State (b,p,pos,dir,bs)) (Backward e::ss)         =  let
                                                                val v = eval bs e
                                                                val s = State (b,p, calculatePos pos dir v "B", calculateDir dir "B", bs);
                                                              in step s ss end

  (* IF *)
  | step (State (b,p,pos,dir,bs)) (IfThenElse(e, sl1, sl2)::ss) = let val doIt = evalBoolExp bs e
                                                                  in
                                                                    if doIt then
                                                                      let val new = step (State (b,p,pos,dir,bs)) sl1
                                                                      in step new ss end
                                                                    else
                                                                      let val new = step (State (b,p,pos,dir,bs)) sl2
                                                                      in step new ss end
                                                                  end

  (* PENUP *)
  | step (State (b,_,pos,dir,bs)) (PenUp::ss)              =  let in step (State (b,Up,pos,dir,bs)) ss end

  (* PENDOWN *)
  | step (State (b,_,pos,dir,bs)) (PenDown::ss)            =  let in step (State (b,Down,pos,dir,bs)) ss end

  (* ASSIGNMENT *)
  | step (State (b,p,pos,dir,bs)) (Assignment (varName, exp):: ss) =  let val newVal = fn var => if (var = varName) then SOME (eval (bs) exp)
                                                                                                                    else bs var
                                                                      in step (State (b,p,pos,dir,newVal)) ss end

  (* WHILE*)
  | step (State (b,p,pos,dir,bs)) (While (conditional, stmtlist)::ss) = let val conditionalVal = evalBoolExp bs conditional
                                                                        in
                                                                          if conditionalVal then
                                                                            let val currentState = step (State (b,p,pos,dir,bs)) stmtlist
                                                                            in step currentState (While(conditional,stmtlist)::ss) end
                                                                          else
                                                                            step (State (b,p,pos,dir,bs)) ss
                                                                        end

  | step state [] = state;



(* Example:

- interpret (P (nil,[Move (Const 1)]));

uncaught exception Match [nonexhaustive match failure]
  raised at: m.sml:67.82

*)

fun prettyPrintSpace 0 = " "
| prettyPrintSpace indent = " " ^ prettyPrintSpace (indent - 1)

fun prettyPrintExp (Const i) = Int.toString (i)
| prettyPrintExp (Ident var) = var
| prettyPrintExp (Plus (a,b)) = (prettyPrintExp a) ^ " + " ^ (prettyPrintExp b)
| prettyPrintExp (Minus (a,b)) = (prettyPrintExp a) ^ " - " ^ (prettyPrintExp b)
| prettyPrintExp (Mult (a,b)) = (prettyPrintExp a) ^ " * " ^ (prettyPrintExp b)


fun prettyPrintBoolExp (LessThan (a,b)) = (prettyPrintExp a) ^ " < " ^ (prettyPrintExp b)
| prettyPrintBoolExp (Equal (a,b)) = (prettyPrintExp a) ^ " = " ^ (prettyPrintExp b)
| prettyPrintBoolExp (MoreThan (a,b)) = (prettyPrintExp a) ^ " > " ^ (prettyPrintExp b)

fun prettyPrintDirection N = "N"
| prettyPrintDirection S = "S"
| prettyPrintDirection E = "E"
| prettyPrintDirection W = "W"


fun prettyPrint indent (Start (x,y,direction) :: ss) = prettyPrintSpace indent ^ "start("
^ (prettyPrintExp x) ^ "," ^ (prettyPrintExp y) ^ "," ^ (prettyPrintDirection direction)
^ ")\n" ^ prettyPrint indent ss

(* Pen *)
| prettyPrint indent (PenUp :: ss) = prettyPrintSpace indent ^ "Up()\n" ^ prettyPrint indent ss
| prettyPrint indent (PenDown :: ss) = prettyPrintSpace indent ^ "Down()\n" ^ prettyPrint indent ss

(* Move *)
| prettyPrint indent (Forward (distance) :: ss) = prettyPrintSpace indent ^ "Forward (" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrint indent ss
| prettyPrint indent (Backward (distance) :: ss) = prettyPrintSpace indent ^ "Backward (" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrint indent ss
| prettyPrint indent (Right (distance) :: ss) = prettyPrintSpace indent ^ "Right  (" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrint indent ss
| prettyPrint indent (Left (distance) :: ss) = prettyPrintSpace indent ^ "Left (" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrint indent ss

(* Assignment *)
| prettyPrint indent (Assignment(var,e) :: ss) = prettyPrintSpace indent ^ "var "^ var ^ " = " ^ (prettyPrintExp e)  ^ "\n" ^ prettyPrint indent ss

(* While *)
| prettyPrint indent (While (boolex, stmtlist)::ss) = prettyPrintSpace indent ^ "while (" ^ prettyPrintBoolExp boolex ^ ") {\n" 
^ prettyPrint (indent + 4) stmtlist
^ prettyPrintSpace indent ^ "}\n" ^ prettyPrint indent ss

(* If-Else *)
| prettyPrint indent (IfThenElse (boolex, ifPart, elsePart)::ss) = 
prettyPrintSpace indent ^ "if (" ^ prettyPrintBoolExp boolex ^ ") {\n" 
^ prettyPrint (indent + 4) ifPart 
^ prettyPrintSpace indent ^ "} " 
^ prettyPrintSpace indent ^ "else {\n" 
^ prettyPrint (indent + 4) elsePart
^ prettyPrintSpace indent ^ "}\n" ^prettyPrint indent ss

(* Stop *)
| prettyPrint indent (Stop :: ss) = prettyPrintSpace indent ^ "stop\n" ^ prettyPrint indent ss

(* End of recursion *)
| prettyPrint indent _ = "";


(* old testing code
let
	val decl1 = [Var ("x", Const 5) 
	,Var ("y", Ident "x")];
	val test1 = [Start (Const 0, Const 0, E)
				, PenDown
				, PenUp
	            , Forward(Const 3) 
				, Left(Const 2)
				, Right(Const 5)
				, Backward (Const 10)
				, Assignment ("x", Const 39)
				, While ((LessThan (Ident "x", Const 42)),[PenDown, PenUp, Assignment("x", Const 100)]) 
				, IfThenElse((LessThan (Ident "x", Const 42)), [PenDown], [PenUp, Forward (Plus (Ident "x", Const 2))])
				, Stop]
in
	print "\n-Testprogram number 1-\n";
	print (prettyPrint 0 test1);
	interpret(P(Size(10,10), R([], test1)))
end;*)



(* Menu *)
fun showtests () = 
  print ("----------------\n"
    ^    "Tests available:\n"
    ^    "* t1()\n"
    ^    "* t2()\n"
    ^    "* t4()\n"
    ^    "----------------\n");



(* Testing code 1 *)
fun t1 ():state =
  let
    val stmts = [
      Start(Const 23, Const 30, W),
      Forward(Const 15),
      PenDown,
      Left(Const 15),
      Right(Plus(Const 2, Const 3)),
      PenUp,
      Backward(Plus(Const 10, Const 27)),
      Stop
    ]
  in
    (* run test *)
    print "\n** Testprogram number 1 **\n";
    print (prettyPrint 0 stmts);
    interpret(P(Size(64, 64), R([], stmts)))
  end;

(* Testing code 2 *)
fun t2 ():state =
  let
    val decl = [
      Var("i", Const 5),
      Var("j", Const 3)
    ];
    val stmts = [
      Start(Const 23, Const 6, W),
      Forward(Mult(Const 3, Ident "i")),
      PenDown,
      Right(Const 15),
      Left(Const 4),
      PenUp,
      Backward(Plus(Plus(Mult(Const 2, Ident "i"), Mult(Const 3, Ident "j")), Const 5)),
      Stop
    ]
  in
    (* run test *)
    print "\n** Testprogram number 2 **\n";
    print (prettyPrint 0 stmts);
    interpret(P(Size(64, 64), R(decl, stmts)))
  end;

(* Testing code 3 skipped *)

(* Testing code 4 *)
fun t4 ():state =
  let
    val decl = [
      Var("i", Const 5),
      Var("j", Const 3)
    ];
    val stmts = [
      Start(Const 23, Const 6, W),
      Forward(Mult(Const 3, Ident "i")),
      PenDown,
      Right(Const 15),
      Left(Const 4),
      PenUp,
      Backward(Plus(Plus(Mult(Const 2, Ident "i"), Mult(Const 3, Ident "j")), Const 5)),
      While(MoreThan(Ident "j", Const 0), [
        Right(Ident "j"),
        Assignment("j", Minus(Ident "j", Const 1))]),
      IfThenElse(MoreThan(Ident "i", Const 3), [
        Forward(Const 14)], [
        (* else *)
        Backward(Const 14)]),
      Stop
    ]
  in
    (* run test *)
    print "\n** Testprogram number 4 **\n";
    print (prettyPrint 0 stmts);
    interpret(P(Size(64, 64), R(decl, stmts)))
  end;

showtests();