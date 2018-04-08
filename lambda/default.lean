import lambda.parsing lambda.types lambda.unicode
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
:show_depth       show current recursion depth
:depth [nat]      set recursion depth
:clear_env        clear environment
:load [filename]  load file “filename”
let name := body  creates a new variable “name” with value “body”"

structure repl_configuration :=
(env : list (string × term))
(recursion_depth : nat)

def read_from_file (conf : repl_configuration) (filename : string) :
  io repl_configuration := do
  filehandle ← io.mk_file_handle filename io.mode.read,
  lines ← io.iterate [] (λ (readed : list string),
    do eof ← io.fs.is_eof filehandle,
      if eof then pure none
      else do line ← (flip option.get_or_else "") <$>
                     unicode.utf8_to_string <$>
                     io.fs.get_line filehandle,
              pure $ some (readed ++ [line])),
  io.fs.close filehandle,
  let (new_conf, for_print) := list.foldl
    (λ (pair : repl_configuration × list string) line,
      let file_eval := eval pair.1.recursion_depth ∘ mk_env pair.1.env in
      match run_string Command line with
        | (sum.inr $ repl_command.term t) :=
          (pair.1, pair.2 ++ [to_string (file_eval t).1])
        | (sum.inr $ repl_command.bind name t) :=
          ({ pair.1 with env := pair.1.env ++ [(name, (file_eval t).1)] },
          pair.2)
        | (sum.inl er) := (pair.1, pair.2 ++ [er])
        | _ := pair
      end)
    (conf, []) lines,
  list.foldr (>>) (pure ()) $
    list.map (io.put_str_ln) for_print,
  pure new_conf

def loop : repl_configuration → io (option repl_configuration)
| conf :=
  let repl_eval := eval conf.recursion_depth ∘ mk_env conf.env in do
  io.put_str "λ> ",
  line ← io.get_line,
  match run_string Command line with
  | (sum.inr repl_command.quit) := pure none
  | (sum.inr repl_command.help) := io.put_str_ln help >> pure conf
  | (sum.inr repl_command.env) := do
    list.foldl (>>) (pure ()) $
      list.map (λ (var : string × term),
        io.put_str_ln $ sformat! "{var.1} := {var.2}")
        conf.env,
    pure conf
  | (sum.inr repl_command.clear_env) := pure $ some { conf with env := [] }
  | (sum.inr $ repl_command.load filename) :=
    some <$> read_from_file conf filename
  | (sum.inr $ repl_command.depth depth) :=
    pure $ some { conf with recursion_depth := depth }
  | (sum.inr repl_command.show_depth) := do
    io.put_str_ln $ to_string conf.recursion_depth,
    pure conf
  | (sum.inr $ repl_command.bind name t) :=
    pure $ some { conf with env :=
      conf.env ++ pure (name, (repl_eval t).1) }
  | (sum.inr $ repl_command.term t) :=
    let res := repl_eval t in
    do io.put_str_ln $ sformat! "{res.1} : {res.2}", pure conf
  | (sum.inr repl_command.nothing) := pure conf
  | (sum.inl er) := do io.put_str_ln er, pure conf
  end

def initial_conf : repl_configuration :=
{ recursion_depth := 1000, env := env }

def main : io unit := io.iterate initial_conf loop >> pure ()
