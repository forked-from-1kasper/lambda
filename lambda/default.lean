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
:help                print this summary or command-specific help
:quit                exit the interpreter
:env                 show variables in the scope
:show_depth          show current recursion depth
:depth [nat]         set recursion depth
:show_import_depth   show current import depth
:import_depth [nat]  set import depth
:clear_env           clear environment
:load [filename]     load file “filename”
let name := body     creates a new variable “name” with value “body”"

structure repl_configuration :=
(env : list (string × term))
(recursion_depth : nat)
(import_depth : nat)

def read_from_file : nat → repl_configuration → string → io repl_configuration
| 0 conf _ :=
  pure conf
| (nat.succ n) conf filename := do
  filehandle ← io.mk_file_handle filename io.mode.read,
  new_conf ← io.iterate conf
    (λ (conf : repl_configuration),
      do eof ← io.fs.is_eof filehandle,
        if eof then pure none
        else do
          line ← (flip option.get_or_else "") <$>
                 unicode.utf8_to_string <$>
                 io.fs.get_line filehandle,
          let file_eval := eval conf.recursion_depth ∘ mk_env conf.env,
          match run_string Command line with
            | (sum.inr $ repl_command.term t) := do
              io.put_str_ln $ to_string (file_eval t).1,
              pure conf
            | (sum.inr $ repl_command.bind name t) :=
              pure $ some { conf with
                env := conf.env ++ [(name, (file_eval t).1)] }
            | (sum.inr $ repl_command.load filename) :=
              some <$> (read_from_file n conf filename)
            | (sum.inl er) := do io.put_str_ln er, pure none
            | _ := pure $ some conf
          end),
  io.fs.close filehandle,
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
    some <$> read_from_file conf.import_depth conf filename
  | (sum.inr $ repl_command.depth depth) :=
    pure $ some { conf with recursion_depth := depth }
  | (sum.inr $ repl_command.import_depth depth) :=
    pure $ some { conf with import_depth := depth }
  | (sum.inr repl_command.show_depth) := do
    io.put_str_ln $ to_string conf.recursion_depth,
    pure conf
  | (sum.inr repl_command.show_import_depth) := do
    io.put_str_ln $ to_string conf.import_depth,
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
{ import_depth := 1000, recursion_depth := 1000, env := env }

def main : io unit := io.iterate initial_conf loop >> pure ()
