-- @js_export: test2, wat
def wat : Int := 42

def test1 {α β : Type} (wat : α → β) (a : α) : β := wat a

def test2 {α β : Type} (f : α → β) (a : α) : β := test1 f a
