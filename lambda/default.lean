import lambda.parsing lambda.types
import system.io data.buffer.parser

open parsing types parser

def mk_env (env : list (string × term)) (t : term) : term :=
match list.unzip env with
| (names, terms) := multi_app (multi_lam names t) terms
end

def env : list (string × term) :=
[("I", term.lam "x" (term.var "x")),
 ("K", multi_lam ["x", "y"] (term.var "x")),
 ("S", multi_lam ["f", "g", "x"]
   (term.app (term.app (term.var "f") (term.var "x"))
             (term.app (term.var "g") (term.var "x"))))]

def help : string := "
:help             print this summary or command-specific help
:quit             exit the interpreter
:env              show variables in the scope
let name := body  creates a new variable “name” with value “body”"

structure repl_configuration :=
(env : list (string × term))
(recursion_depth : nat)

def loop : repl_configuration → io (option repl_configuration)
| conf :=
  let repl_eval := eval conf.recursion_depth ∘ mk_env conf.env in do
  io.put_str "λ> ",
  line ← io.get_line,
  match (run_string Term line, run_string Let line, line) with
  | (_, _, "") := pure conf
  | (_, _, ":quit") := pure none
  | (_, _, ":help") := io.put_str_ln help >> pure conf
  | (_, _, ":env") := do
    list.foldl (>>) (pure ()) $
      list.map (λ (var : string × term),
        io.put_str_ln $ sformat! "{var.1} := {var.2}")
        conf.env,
    pure conf
  | (_, sum.inr (name, t), _) :=
    pure $ some { conf with env :=
      conf.env ++ pure (name, (repl_eval t).1) }
  | (sum.inr t, _) :=
    let res := repl_eval t in
    do io.put_str_ln $ sformat! "{res.1} : {res.2}", pure conf
  | (sum.inl er, _) := do io.put_str_ln er, pure conf
  end

def initial_conf : repl_configuration :=
{ recursion_depth := 1000, env := env }
def main : io unit := io.iterate initial_conf loop >> pure ()
