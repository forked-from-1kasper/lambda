namespace types

inductive term : Type
| var : string → term
| app : term → term → term
| lam : string → term → term
open term

def multi_lam (names : list string) (body : term) : term :=
list.foldr lam body names

def multi_app (t : term) (b : list term) : term :=
list.foldl app t b

def term_to_string : term → string
| (var n) := sformat! "{n}"
| (app (var e₁) (var e₂)) := sformat! "{e₁} {e₂}"
| (app e₁ (var e₂)) := sformat! "({term_to_string e₁}) {e₂}"
| (app (var e₁) e₂) := sformat! "{e₁} ({term_to_string e₂})"
| (app e₁ e₂) := sformat! "({term_to_string e₁}) ({term_to_string e₂})"
| (lam n t) := sformat! "λ{n}, {term_to_string t}"

instance term_has_to_string : has_to_string term :=
⟨term_to_string⟩

instance term_has_repr : has_repr term :=
⟨term_to_string⟩

def subst : string → term → term → term
| x newVal (lam y body) :=
  if x ≠ y then lam y (subst x newVal body)
  else lam y body
| x newVal (app e₁ e₂) :=
  app (subst x newVal e₁) (subst x newVal e₂)
| x newVal (var y) :=
  if x = y then newVal
  else var y

inductive eval_result
| limit | normal
def result_to_string : eval_result → string
| eval_result.limit := "maximum recursion depth exceeded"
| eval_result.normal := "normal form"

instance result_has_to_string : has_to_string eval_result :=
⟨result_to_string⟩

instance result_has_repr : has_repr eval_result :=
⟨result_to_string⟩

def eval : nat → term → term × eval_result
| 0 r := (r, eval_result.limit)
| _ (lam x e) := (lam x e, eval_result.normal)
| _ (var n) := (var n, eval_result.normal)
| (nat.succ n) (app e₁ e₂) :=
match eval n e₁ with
  | (lam x body, _) := eval n (subst x e₂ body)
  | (res, r) := (app res e₂, r)
end

inductive repl_command : Type
| term : term → repl_command
| quit | help | env | show_depth | clear_env
| depth : nat → repl_command
| bind : string → term → repl_command

end types
