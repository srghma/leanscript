def test1 (fn : Unit → Int) : Array Int :=
  let array := #[ 1, 2, fn () ]
  if array.size == 3 then array else #[]

def test2 (fn : Unit → Int) : Array (Array Int) :=
  let array1 := #[ 1, 2, fn () ]
  let array2 := #[ array1, #[ 3, 4 ], #[ fn () ] ]
  if some 3 == (array2[0]? |>.map (fun a => a.size)) then array2 else #[array1] ++ array2

@[noinline] def fn' (_ : Unit) : Int := 0

def extern1 : Array Int := #[ 1, 2, fn' () ]
def extern2 : Array (Array Int) := #[ extern1, #[ 3 ], #[ fn' () ] ]

def test3 : Array Int :=
  if extern1.size == 3 then extern1 else #[]

def test4 : Array (Array Int) :=
  if some 3 == (extern2[0]? |>.map (fun a => a.size)) then extern2 else #[]
