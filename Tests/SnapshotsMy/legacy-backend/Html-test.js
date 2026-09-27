const _private_SnapshotsMy_Html_0_p = (v0) => ({ tag: 0, _1: "p", _2: v0([]) });
const _private_SnapshotsMy_Html_0_h2 = (
  v0,
) => ({ tag: 0, _1: "h2", _2: v0([]) });
const _private_SnapshotsMy_Html_0_article = (
  v0,
) => ({ tag: 0, _1: "article", _2: v0([]) });
const _private_SnapshotsMy_Html_0_section_ = (
  v0,
) => ({ tag: 0, _1: "section", _2: v0([]) });
const _private_SnapshotsMy_Html_0_h1 = (
  v0,
) => ({ tag: 0, _1: "h1", _2: v0([]) });
export const test = (
  v0,
) => _private_SnapshotsMy_Html_0_section_(
  (
    v1,
  ) => [
    ...[
      ...v1,
      _private_SnapshotsMy_Html_0_h1(
        (v2) => [...v2, { tag: 1, _1: "Posts for " + v0 }],
      ),
    ],
    _private_SnapshotsMy_Html_0_article(
      (
        v2,
      ) => [
        ...[
          ...v2,
          _private_SnapshotsMy_Html_0_h2(
            (v3) => [...v3, { tag: 1, _1: "The first post" }],
          ),
        ],
        _private_SnapshotsMy_Html_0_p(
          (
            v3,
          ) => [
            ...[...v3, { tag: 1, _1: "This is the first post." }],
            { tag: 1, _1: "Not much else to say." },
          ],
        ),
      ],
    ),
  ],
);
