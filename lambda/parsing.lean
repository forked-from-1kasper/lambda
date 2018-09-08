import data.buffer.parser
import lambda.types
open parser types

namespace parsing

def whitespaces := " \t\n\x0d".to_list

def reserved_chars :=
[' ', ',', 'λ', '(', ')', ':', '-']
def WordChar : parser char :=
sat (λ c, list.all (reserved_chars ++ whitespaces) (≠ c))

def LF := ch $ char.of_nat 10
def CR := ch $ char.of_nat 13

def Nl := CR >> LF <|> LF <|> CR

def Ws : parser unit :=
decorate_error "<whitespace>" $
many' $ one_of' whitespaces

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

def parens (term : parser term) :=
term <|> (ch '(' >> term <* ch ')')

def Term_core : parser term → parser term
| Term_recur :=
  parens $
    Lam (parens Term_recur) <|>
    App (parens Term_recur) <|>
    Var
def Term := fix Term_core

def Let : parser (string × term) := do
  tok "let",
  name ← Word, many1 Ws,
  tok ":=", body ← Term,
  pure (name, body)

def Numeral : parser char :=
sat $ λ c, list.any "0123456789".to_list (= c)
def Number := many_char1 Numeral

def Command_line : parser repl_command :=
str ":quit" >> pure repl_command.quit <|>
str ":help" >> pure repl_command.help <|>
str ":env" >> pure repl_command.env <|>
str ":depth" >> Ws >> Number >>=
  (pure ∘ repl_command.depth ∘ string.to_nat) <|>
str ":import_depth" >> Ws >> Number >>=
  (pure ∘ repl_command.import_depth ∘ string.to_nat) <|>
str ":show_depth" >> pure repl_command.show_depth <|>
str ":show_import_depth" >> pure repl_command.show_import_depth <|>
str ":clear_env" >> pure repl_command.clear_env <|>
str ":load" >> Ws >> Word >>= (pure ∘ repl_command.load) <|>
Let >>= (pure ∘ function.uncurry repl_command.bind) <|>
Term >>= (pure ∘ repl_command.term) <|>
many Ws >> pure repl_command.nothing

def Command : parser repl_command := do
  cmd ← Command_line,
  optional (str "--" >> optional Ws >> many (sat (λ _, tt))),
  optional $ many Ws,
  pure cmd

end parsing
