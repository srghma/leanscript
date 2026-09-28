const $Noinline$appendR = /* #__PURE__ */ (a_bar, a_foo) => /* #__PURE__ */(b_bar, b_foo) => ({
  bar: [...a_bar, ...b_bar],
  foo: a_foo + b_foo,
});
const $Noinline$test1 = $Noinline$appendR;
const $Noinline$test2 = $Noinline$appendR;
const $Noinline$test3 = /* #__PURE__ */ $Noinline$appendR(["hello"], "hello");
const $Noinline$test4 = /* #__PURE__ */ $Noinline$appendR(["hello"], "hello")(["World!"], ", World!");
const $Inline$appendR = /* #__PURE__ */ (a_bar, a_foo) => /* #__PURE__ */(b_bar, b_foo) => ({
  bar: [...a_bar, ...b_bar],
  foo: a_foo + b_foo,
});
const $Inline$test1 = $Inline$appendR;
const $Inline$test2 = $Inline$appendR;
const $Inline$test3 = /* #__PURE__ */ $Inline$appendR(["hello"], "hello");
const $Inline$test4 = {
  bar: ["hello", "World!"],
  foo: "hello, World!",
};
const $AlwaysInline$appendR = /* #__PURE__ */ (a_bar, a_foo) => /* #__PURE__ */(b_bar, b_foo) => ({
  bar: [...a_bar, ...b_bar],
  foo: a_foo + b_foo,
});
const $AlwaysInline$test1 = $AlwaysInline$appendR;
const $AlwaysInline$test2 = $AlwaysInline$appendR;
const $AlwaysInline$test3 = /* #__PURE__ */ (b_bar, b_foo) => ({
  bar: ["hello", ...b_bar],
  foo: "hello" + b_foo,
});
const $AlwaysInline$test4 = {
  bar: ["hello", "World!"],
  foo: "hello, World!",
};
const $InlineIfReduceInline$appendR = /* #__PURE__ */ (a_bar, a_foo) => /* #__PURE__ */(b_bar, b_foo) => ({
  bar: [...a_bar, ...b_bar],
  foo: a_foo + b_foo,
});
const $InlineIfReduceInline$test1 = $InlineIfReduceInline$appendR;
const $InlineIfReduceInline$test2 = $InlineIfReduceInline$appendR;
const $InlineIfReduceInline$test3 = /* #__PURE__ */ $InlineIfReduceInline$appendR(["hello"], "hello");
const $InlineIfReduceInline$test4 = {
  bar: ["hello", "World!"],
  foo: "hello, World!",
};
