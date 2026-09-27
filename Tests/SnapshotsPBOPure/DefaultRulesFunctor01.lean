open Option

-- 1. PureScript's `<#>` (map flipped)
infixl:100 " <#> " => fun x f => Functor.map f x

-- 2. PureScript's `<$` (mapConst)
infixr:100 " <$ "  => Functor.mapConst

-- 3. PureScript's `$>` (mapConst flipped)
infixl:100 " $> "  => fun x a => Functor.mapConst a x

-- 4. PureScript's `<@>` (flap)
infixl:100 " <@> " => fun ff x => (fun g => g x) <$> ff

-- test1: mb <#> \i -> show i
def test1 (mb : Option Int) : Option String :=
  mb <#> fun (i : Int) => toString i

-- test2: void mb (mapping to Unit)
def test2 {α : Type} (mb : Option α) : Option Unit :=
  Functor.mapConst () mb

-- test3: mb $> 42
def test3 {α : Type} (mb : Option α) : Option Int :=
  mb $> 42

-- test4: 42 <$ mb
def test4 {α : Type} (mb : Option α) : Option Int :=
  42 <$ mb

-- test5: const <$> mb <@> 12
def test5 {α : Type} (mb : Option α) : Option α :=
  (Function.const Nat <$> mb) <@> 12
