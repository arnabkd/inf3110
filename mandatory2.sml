datatype exp = Ident of string | Const of int | Plus of exp * exp | Minus of exp * exp | Mult of exp * exp;
datatype boolExp = LessThan of exp * exp | MoreThan of exp * exp | Equal of exp * exp;


 (* incomplete *)
datatype decl = Var of string * exp;
datatype direction = N | S | E | W;
datatype move = Forward | Backward | Left | Right;
datatype stmt = Start of exp*exp*direction
              	| Stop
              	(* Pen: *)
	      	  	| PenUp | PenDown
              	(* Move: *)
              	| Forward of exp | Backward of exp | Right of exp | Left of exp
				(* While *)
				| While of boolExp * stmt list;

datatype grid = Size of int * int;
datatype robot = R of decl list * stmt list;
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

datatype pen = Up | Down;
type position = int*int;
type board = unit; (* ... *)
type bindings = string -> int option;

datatype state = State of board * pen * position * direction * bindings;

fun eval binding (Const i) = i 
  | eval binding (Ident var) = valOf (binding var)
  | eval binding (Plus (a,b)) = (eval binding a) + (eval binding b)
  | eval binding (Minus (a,b)) = (eval binding a) - (eval binding b)
  | eval binding (Mult (a,b)) = (eval binding a) * (eval binding b);
  (*| eval binding _ = raise Fail "not implemented yet"; *)


fun evalBoolExp bindings (LessThan (a,b)) = (eval bindings a) < (eval bindings b)
  | evalBoolExp bindings (Equal (a,b)) = (eval bindings a) = (eval bindings b)
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
	| calculateDir N "R" = E
	| calculateDir N "L" = W
	| calculateDir N "B" = S
	| calculateDir S "R" = W
	| calculateDir S "L" = E
	| calculateDir S "B" = N
	| calculateDir E "R" = S
	| calculateDir E "L" = N
	| calculateDir E "B" = W
	| calculateDir W "R" = N
	| calculateDir W "L" = S
	| calculateDir W "B" = E;

(* Step takes a state and a list of statements. Execute the first statement, and obtain an intermediate state.
   If we need to continue (i.e. not STOP), then use intermediate state to interpret remaining statements.
   Interpret runs the whole program. TODO: when and how do we stop?
*)
fun interpret (P (gr,R (decls,stmts))) = step (initialState decls (State ((), Up, (0,0), N, fn _ => NONE))) stmts
and step state (Stop::_) = state
  (* START *)
  | step (State (b,p,pos,dir,bs)) (Start(ex1, ex2, d)::ss) = let val dir = d;
														   	val e1 = eval bs ex1;
														   	val e2 = eval bs ex2;
														   	val pr = "Start(" ^ Int.toString (e1) ^ ", "^Int.toString (e2) ^ ")\n"
														   	in print pr;
														   	step (State (b,Up,(e1, e2),dir,bs)) ss end
  (* RIGHT *)
  | step (State (b,p,pos,dir,bs)) (Right e::ss) = let val v = eval bs e
                                                  val s = State (b,p, calculatePos pos dir v "R", calculateDir dir "R", bs); 
												  val pr = "Right(" ^ Int.toString (v) ^ ")\n"
                                                  in print pr; step s ss end
  (* LEFT *)
  | step (State (b,p,pos,dir,bs)) (Left e::ss) = let val v = eval bs e
                                                  val s = State (b,p, calculatePos pos dir v "L", calculateDir dir "L", bs);
												  val pr = "Left(" ^ Int.toString (v) ^ ")\n"
                                                  in print pr; step s ss end
  (* FORWARD *)
  | step (State (b,p,pos,dir,bs)) (Forward e::ss) = let val v = eval bs e
                                                  val s = State (b,p, calculatePos pos dir v "F", calculateDir dir "F", bs);
												  val pr = "Forward(" ^ Int.toString (v) ^ ")\n"
                                                  in print pr; step s ss end
  (* BACKWARD *)
  | step (State (b,p,pos,dir,bs)) (Backward e::ss) = let val v = eval bs e
                                                  val s = State (b,p, calculatePos pos dir v "B", calculateDir dir "B", bs);
												  val pr = "Backward(" ^ Int.toString (v) ^ ")\n"
                                                  in print pr; step s ss end
  (* PENUP *)
  | step (State (b,_,pos,dir,bs)) (PenUp::ss) = let in print "PenDown()\n"; step (State (b,Down,pos,dir,bs)) ss end

  (* PENDOWN *)
  | step (State (b,_,pos,dir,bs)) (PenDown::ss) = let in print "PenUp()\n"; step (State (b,Up,pos,dir,bs)) ss end
  
  (* WHILE*)
  ;



(* Example:

- interpret (P (nil,[Move (Const 1)]));

uncaught exception Match [nonexhaustive match failure]
  raised at: m.sml:67.82

*)

let
	val decl1 = [Var ("x", Const 5) 
	,Var ("y", Ident "x")
	,Var("x", Const 42)];
	val test1 = [Start (Const 0, Const 0, E)
	            , Forward(Const 3)
				, PenDown
				, Left(Const 2)
				, Stop]
in
	print "\n-Testprogram number 1-\n";
	interpret(P(Size(10,10), R([], test1)))
end;
