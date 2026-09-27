def test1 {α β : Type} (f : α → β) (as : Array α) : Array β := Id.run do
  let mut bs := #[]
  for a in as do
    bs := bs.push (f a)
  pure bs

def test2 {α β : Type} (f : α → Array β) (as : Array α) : Array β := Id.run do
  let mut bs := #[]
  for a in as do
    let as' := f a
    for a' in as' do
      bs := bs.push a'
  pure bs
