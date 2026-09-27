@[inline] private def maybe {α β : Type} (d : β) (f : α → β) (o : Option α) : β := Option.elim o d f

@[inline] private def maybe' {α β : Type} (d : Unit → β) (f : α → β) : Option α → β
  | some a => f a
  | none => d ()

-- Terms are purposefully eta-reduced in PureScript, but Lean's defs usually have arguments.
-- To mimic eta-reduction, we can use (fun x => ...) or just leave them as they are.

def test1 (f : Unit → Int) : Option Int → Int := maybe (f ()) (fun x => x + 1)

def test2 {α β : Type} (f : Unit → β) (g : Int → α → β) : Option α → β := maybe (f ()) (g 1)

def test3 (f : Unit → Int) : Option Int → Int := maybe' f (fun x => x + 1)

def test4 {α β : Type} (f : Unit → β) (g : Int → α → β) : Option α → β := maybe' f (g 1)

def test5 {α : Type} (a : Int) (g : Int → α → Int) : Option α → Int := maybe' (fun _ => a + 1) (g 1)
