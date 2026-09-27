def test1 {α : Type} (a : Array α) : Int := (a.size : Int)

def test2 {α : Type} [Inhabited α] (a : Array α) : α := a[2]!

def test3 {α : Type} (a : { a : Array α // a.size > 0 }) : Int := (a.val.size : Int)

def test4 {α : Type} [Inhabited α] (a : { a : Array α // a.size > 0 }) : α := a.val[2]!
