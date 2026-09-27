-- @js_export: test1, test2, test3, test4
def preview_left {α β : Type} : Except α β → Option α
  | Except.error a => some a
  | Except.ok _ => none

def preview_left_right {α β γ : Type} : Except (Except α β) γ → Option β
  | Except.error (Except.ok b) => some b
  | _ => none

def test1 : Except Int Int → Option Int := preview_left
def test2 (a : Except Int Int) := preview_left a
def test3 : Except (Except Int Int) Int → Option Int := preview_left_right
def test4 (a : Except (Except Int Int) Int) := preview_left_right a
