datatype exp     = Ident of string
                 | Const of int
                 | Plus of exp * exp
                 | Minus of exp * exp
                 | Mult of exp * exp;
datatype boolExp = LessThan of exp * exp
                 | MoreThan of exp * exp
                 | Equal of exp * exp;


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

datatype pen  = Up | Down;

type position = int*int;
type board    = bool list list;
type bindings = string -> int option;

datatype state = State of board * pen * position * direction * bindings;

exception OutOfGrid;

fun eval binding (Const i) = i 
  | eval binding (Ident var) = valOf (binding var)
  | eval binding (Plus (a,b)) = (eval binding a) + (eval binding b)
  | eval binding (Minus (a,b)) = (eval binding a) - (eval binding b)
  | eval binding (Mult (a,b)) = (eval binding a) * (eval binding b);


fun evalBoolExp bindings (LessThan (a,b)) = (eval bindings a) < (eval bindings b)
  | evalBoolExp bindings (Equal (a,b))    = (eval bindings a) = (eval bindings b)
  | evalBoolExp bindings (MoreThan (a,b)) = (eval bindings a) > (eval bindings b);
  
(* Could use `fold` here *)
fun initialState nil acc = acc
  | initialState ((Var (v,e))::vs) (State (b,p,pos,dir,find)) = initialState vs (State (b,p,pos,dir, fn var => if (var = v) then SOME (eval (find) e)
                                                                                                                               else find var));

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

fun getNewPos (x,y) f i t board =
  let
    val np = calculatePos (x,y) f i t
    val gx = List.length(board)
    val gy = List.length(hd(board))
  in
    (* check if outside grid *)
    if (#1 np) <= 0 orelse (#1 np) > gx then
      raise OutOfGrid
    else if (#2 np) <= 0 orelse (#2 np) > gy then
      raise OutOfGrid
    else
      np
  end

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


fun prettyPrintSpace 0 = " "
  | prettyPrintSpace indent = " " ^ prettyPrintSpace (indent - 1)

fun prettyPrintExp (Const i)      = Int.toString (i)
  | prettyPrintExp (Ident var)    = var
  | prettyPrintExp (Plus (a,b))   = (prettyPrintExp a) ^ " + " ^ (prettyPrintExp b)
  | prettyPrintExp (Minus (a,b))  = (prettyPrintExp a) ^ " - " ^ (prettyPrintExp b)
  | prettyPrintExp (Mult (a,b))   = let (* adds extra parentheses if needed *)
                                      val x = prettyPrintExp(a)
                                      val y = prettyPrintExp(b)
                                    in
                                     (case a of
                                          Plus a => "(" ^ x ^ ")"
                                        | Minus a => "(" ^ x ^ ")"
                                        | _  => x)
                                    ^ "*"
                                    ^ (case b of
                                          Plus b => "(" ^ y ^ ")"
                                        | Minus b => "(" ^ y ^ ")"
                                        | _  => y)
                                    end

fun prettyPrintBoolExp (LessThan (a,b)) = (prettyPrintExp a) ^ " < " ^ (prettyPrintExp b)
  | prettyPrintBoolExp (Equal (a,b))    = (prettyPrintExp a) ^ " = " ^ (prettyPrintExp b)
  | prettyPrintBoolExp (MoreThan (a,b)) = (prettyPrintExp a) ^ " > " ^ (prettyPrintExp b)

fun prettyPrintDirection N = "N"
  | prettyPrintDirection S = "S"
  | prettyPrintDirection E = "E"
  | prettyPrintDirection W = "W"

fun prettyPrintDecls (Var (id,x) :: ss) =
    prettyPrintSpace 0 ^ "var " ^ id ^ " = " ^ (prettyPrintExp x) ^ ";\n" ^ prettyPrintDecls ss
  | prettyPrintDecls _ = ""

fun prettyPrintStmts indent
  (* Start *)
                       (Start (x,y,direction) :: ss) =
      prettyPrintSpace indent ^ "start("
    ^ (prettyPrintExp x) ^ "," ^ (prettyPrintExp y) ^ "," ^ (prettyPrintDirection direction)
    ^ ")\n" ^ prettyPrintStmts indent ss

  (* Pen *)
  | prettyPrintStmts indent (PenUp :: ss) = prettyPrintSpace indent ^ "Up()\n" ^ prettyPrintStmts indent ss
  | prettyPrintStmts indent (PenDown :: ss) = prettyPrintSpace indent ^ "Down()\n" ^ prettyPrintStmts indent ss

  (* Move *)
  | prettyPrintStmts indent (Forward (distance) :: ss) =
      prettyPrintSpace indent ^ "Forward(" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrintStmts indent ss
  | prettyPrintStmts indent (Backward (distance) :: ss) =
      prettyPrintSpace indent ^ "Backward(" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrintStmts indent ss
  | prettyPrintStmts indent (Right (distance) :: ss) =
      prettyPrintSpace indent ^ "Right(" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrintStmts indent ss
  | prettyPrintStmts indent (Left (distance) :: ss) =
      prettyPrintSpace indent ^ "Left(" ^ prettyPrintExp distance ^ ")\n" ^ prettyPrintStmts indent ss
  
  (* Assignment *)
  | prettyPrintStmts indent (Assignment(var,e) :: ss) =
      prettyPrintSpace indent ^ "var "^ var ^ " = " ^ (prettyPrintExp e)  ^ "\n" ^ prettyPrintStmts indent ss
  
  (* While *)
  | prettyPrintStmts indent (While (boolex, stmtlist)::ss) =
      prettyPrintSpace indent ^ "While (" ^ prettyPrintBoolExp boolex ^ ") {\n" 
    ^ prettyPrintStmts (indent + 4) stmtlist
    ^ prettyPrintSpace indent ^ "}\n" ^ prettyPrintStmts indent ss
  
  (* If-Else *)
  | prettyPrintStmts indent (IfThenElse (boolex, ifPart, elsePart)::ss) = 
      prettyPrintSpace indent ^ "if (" ^ prettyPrintBoolExp boolex ^ ") {\n" 
    ^ prettyPrintStmts (indent + 4) ifPart 
    ^ prettyPrintSpace indent ^ "} " 
    ^ prettyPrintSpace indent ^ "else {\n" 
    ^ prettyPrintStmts (indent + 4) elsePart
    ^ prettyPrintSpace indent ^ "}\n" ^prettyPrintStmts indent ss
  
  (* Stop *)
  (*| prettyPrintStmts indent (Stop :: ss) =
      prettyPrintSpace indent ^ "stop\n" ^ prettyPrintStmts indent ss*)
  
  (* End of recursion *)
  | prettyPrintStmts indent _ = "";


(* for printing out the board *)
fun getBoardBox cols (x,y)  = case cols of
                                []    => ""
                              | a::ab => (if x = 1 andalso y = 1 then "#"
                                        else if a = true then "X"
                                        else "·") ^ (getBoardBox ab (x-1, y))
fun getBoardLine rows (x,y) = case rows of
                                []    => ""
                              | a::ab => (getBoardLine ab (x, y-1)) ^ (getBoardBox a (x, y)) ^ "\n" (* reverse listing, x0 at bottom *)
fun getBoardText b (x,y) =  let in
                              "\nBoard layout:\n"
                            ^ (getBoardLine b (x,y))
                            ^ "# = current position, X = pen drawed, · = blank area\n\n"
                            end


(* drawing on board *)
fun drawfieldhlp b cy y x = if cy = y then List.take(b, x-1) @ [true] @ List.drop(b, x)
                            else b
fun drawfield b (x,y) cy  = case b of
                              []     => []
                            | ba::bb => (drawfieldhlp ba cy y x) :: (drawfield bb (x,y) (cy+1))
fun drawfields b (x,y) (rx,ry) bx = case bx of
                                      []    => b
                                    | _::ab => drawfields (drawfield b (x,y) 1) (x+rx,y+ry) (rx,ry) ab

fun getDir N = ( 0, 1)
  | getDir S = ( 0,~1)
  | getDir E = ( 1, 0)
  | getDir W = (~1, 0)

(* do the move and draw if pen is down *)
fun move (State (b,p,pos,dir,bs)) newdir n =  let
                                                val v = eval bs n;
                                                val newpos = getNewPos pos dir v newdir b;
                                                val nd = calculateDir dir newdir
                                                val s = State (b, p, newpos, nd, bs)
                                              in
                                                case p of
                                                  Down => (State ((drawfields b pos (getDir nd) (List.tabulate(v, fn i => []))),p,newpos,nd,bs))
                                                  | _  => s
                                              end


(* creating board *)
fun getBoardHelper y i = List.tabulate(y, fn i => false)
fun getBoard (Size(x,y)) = List.tabulate(x, (getBoardHelper y));


(* Step takes a state and a list of statements. Execute the first statement, and obtain an intermediate state.
   If we need to continue (i.e. not STOP), then use intermediate state to interpret remaining statements.
   Interpret runs the whole program.
*)
fun interpret (P (gr,R (decls,stmts))) =  let
                                            val b = getBoard gr
                                          in
                                            print (prettyPrintDecls decls);
                                            print (prettyPrintStmts 0 stmts);
                                            step (initialState decls (State (b, Up, (0,0), N, fn _ => NONE))) stmts;
                                            "interpret finished"
                                          end
and step
  (* STOP *)
    (State (b,p,(x,y),dir,bs)) (Stop::_) =  let in
                                              print ((prettyPrintSpace 0) ^ "stop (x:" ^ Int.toString(x) ^ " y:" ^ Int.toString(y) ^ " direction:" ^ (prettyPrintDirection dir) ^ ")\n");
                                              print (getBoardText b (x,y));
                                              (State (b,p,(x,y),dir,bs))
                                            end

  (* START *)
  | step (State (b,p,pos,dir,bs)) (Start(ex1, ex2, d)::ss) =  let
                                                                val dir = d;
                                                                val e1 = eval bs ex1;
                                                                val e2 = eval bs ex2;
                                                              in
                                                                step (State (b,Up,(e1, e2),dir,bs)) ss
                                                              end

  (* RIGHT *)
  | step state (Right e::ss)            =  step (move state "R" e) ss
  (* LEFT *)
  | step state (Left e::ss)             =  step (move state "L" e) ss
  (* FORWARD *)
  | step state (Forward e::ss)          =  step (move state "F" e) ss
  (* BACKWARD *)
  | step state (Backward e::ss)         =  step (move state "B" e) ss
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
  | step (State (b,_,pos,dir,bs)) (PenDown::ss)            =  let val nb = drawfield b pos 1
                                                              in step (State (nb,Down,pos,dir,bs)) ss end

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


(* Menu *)
fun showtests () = 
  print ("----------------\n"
    ^    "Tests available:\n"
    ^    "* t1()\n"
    ^    "* t2()\n"
    ^    "* t4()\n"
    ^    "----------------\n");



(* Testing code 1 *)
fun t1 () =
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
    interpret(P(Size(64, 64), R([], stmts)))
  end;

(* Testing code 2 *)
fun t2 () =
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
    interpret(P(Size(64, 64), R(decl, stmts)))
  end;

(* Testing code 3 skipped *)

(* Testing code 4 *)
fun t4 () =
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
    interpret(P(Size(64, 64), R(decl, stmts)))
  end;

showtests();