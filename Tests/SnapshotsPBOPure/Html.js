const render = (v) => {
  if (v.tag === "text") {
    return "Html.text " + JSON.stringify(v._content);
  }
  if (v.tag === "elem") {
    const childrenStr = $String$intercalate(", ")($List$map(render)(v._children));
    return "Html.elem " + JSON.stringify(v._tag) + " [" + childrenStr + "]";
  }
  throw new Error("UNREACHABLE");
};
const test = (user) => ({
  tag: "elem",
  _tag: "section",
  _children: {
    tag: "cons",
    _head: {
      tag: "elem",
      _tag: "h1",
      _children: {
        tag: "cons",
        _head: { tag: "text", _content: "Posts for " + user },
        _tail: { tag: "nil" },
      },
    },
    _tail: {
      tag: "cons",
      _head: {
        tag: "elem",
        _tag: "article",
        _children: {
          tag: "cons",
          _head: {
            tag: "elem",
            _tag: "h2",
            _children: {
              tag: "cons",
              _head: { tag: "text", _content: "The first post" },
              _tail: { tag: "nil" },
            },
          },
          _tail: {
            tag: "cons",
            _head: {
              tag: "elem",
              _tag: "p",
              _children: {
                tag: "cons",
                _head: { tag: "text", _content: "This is the first post." },
                _tail: {
                  tag: "cons",
                  _head: { tag: "text", _content: "Not much else to say." },
                  _tail: { tag: "nil" },
                },
              },
            },
            _tail: { tag: "nil" },
          },
        },
      },
      _tail: { tag: "nil" },
    },
  },
});
export { test };
