%default total

data Term: Type where
  App: Term -> Term -> Term
  Abs: (Term -> Term) -> Term
  
partial
uhOh: Term -> Term
uhOh (Abs f) = f (Abs f)
uhOh t = t

-- What happens if you try:
--   uhOh (Abs uhOh)
-- ?
