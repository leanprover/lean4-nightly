def map : (α → β) → List α → List β
  | f, []    => []
  | f, a::as => f a :: map f as
