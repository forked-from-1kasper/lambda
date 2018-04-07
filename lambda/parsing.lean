import data.buffer.parser
import lambda.types
open parser types

namespace parsing

def WordChar : parser char :=
sat (λ c, c ≠ ' ' ∧ c ≠ ',' ∧ c ≠ 'λ' ∧ c ≠ '(' ∧ c ≠ ')')

def Ws : parser unit :=
decorate_error "<whitespace>" $
many' $ one_of' " \t\x0d".to_list

def Word : parser string := many_char1 WordChar

def tok (s : string) := str s >> Ws

def Var : parser term := do
  name ← Word,
  pure $ term.var name

def Lam (Term_recur : parser term) : parser term := do
  ch 'λ', many Ws,
  names ← sep_by1 Ws (many_char1 WordChar),
  ch ',', many Ws,
  body ← Term_recur,
  pure $ multi_lam names body

def App (Term : parser term) : parser term := do
  head ← Term, many1 Ws,
  body ← sep_by Ws Term,
  pure $ multi_app head body

def Term_core : parser term → parser term
| Term_recur := let term := App Term_recur <|> Var <|> Lam Term_recur in do
  t ← (do ch '(', t ← term, ch ')', pure t) <|> term,
  pure t
def Term := fix Term_core

def Let : parser (string × term) := do
  tok "let",
  name ← Word, many1 Ws,
  tok ":=", body ← Term,
  pure (name, body)

def Numeral : parser char :=
sat $ λ c, list.any "0123456789".to_list (= c)
def Number := many_char1 Numeral

def Command : parser repl_command :=
str ":quit" >> pure repl_command.quit <|>
str ":help" >> pure repl_command.help <|>
str ":env" >> pure repl_command.env <|>
str ":depth" >> Ws >> Number >>=
  (pure ∘ repl_command.depth ∘ string.to_nat) <|>
str ":show_depth" >> pure repl_command.show_depth <|>
Let >>= (pure ∘ function.uncurry repl_command.bind) <|>
Term >>= (pure ∘ repl_command.term)

end parsing
