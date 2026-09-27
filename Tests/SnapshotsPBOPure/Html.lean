private inductive Html where
  | elem (tag : String) (children : List Html) -- the constructors of enums are always like =<F12>
  | text (content : String)
deriving Repr

private def render : Html → String
  | .text content => s!"Html.text {repr content}" -- repr on string + Format.pretty => just wrap string in "" and escape "" if have inside => JSON.stringify
  | .elem tag children =>
      let childrenStr := String.intercalate ", " (children.map render)
      s!"Html.elem {repr tag} [{childrenStr}]"

def test (user : String) : Html :=
  Html.elem "section"
    [ Html.elem "h1" [Html.text ("Posts for " ++ user)]
    , Html.elem "article"
        [ Html.elem "h2" [Html.text "The first post"]
        , Html.elem "p"
            [ Html.text "This is the first post."
            , Html.text "Not much else to say."
            ]
        ]
    ]
