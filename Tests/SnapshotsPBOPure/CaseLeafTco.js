import {
  Array_append,
  Array_back_,
  Int_instDecidableEq,
} from "../runtime/lean_runtime_non_configurable.mjs";
export const test1Fuel = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 === 0) {
      return v5;
    } else {
      const v6 = v3 - 1;
      if (0 < v5.length) {
        const v7 = v5[0];
        if (Int_instDecidableEq(v7, 1)) {
          const v8 = Array_back_(v5);
          if (v8.tag === 0) {
            return [...v5, 1];
          } else {
            const v9 = v8._1;
            if (Int_instDecidableEq(v9, 2)) {
              return v5;
            } else {
              if (v4) {
                return [];
              } else {
                v3 = v6;
                v5 = Array_append(
                  [
                    ...[
                      ...[
                        ...[
                          ...[
                            ...[
                              ...[
                                ...[
                                  ...[
                                    ...[
                                      ...[
                                        ...[
                                          ...[
                                            ...[
                                              ...[...[...[...[], v9], 1], 3],
                                              v9,
                                            ],
                                            5,
                                          ],
                                          6,
                                        ],
                                        7,
                                      ],
                                      8,
                                    ],
                                    9,
                                  ],
                                  10,
                                ],
                                1,
                              ],
                              12,
                            ],
                            13,
                          ],
                          14,
                        ],
                        15,
                      ],
                      16,
                    ],
                    17,
                  ],
                  v5,
                );
                continue;
              }
            }
          }
        } else {
          const v8 = Array_back_(v5);
          if (v8.tag === 0) {
            return [...v5, v7];
          } else {
            const v9 = v8._1;
            if (v4) {
              return [];
            } else {
              v3 = v6;
              v5 = Array_append(
                [
                  ...[
                    ...[
                      ...[
                        ...[
                          ...[
                            ...[
                              ...[
                                ...[
                                  ...[
                                    ...[
                                      ...[
                                        ...[
                                          ...[
                                            ...[...[...[...[], v9], v7], 3],
                                            v9,
                                          ],
                                          5,
                                        ],
                                        6,
                                      ],
                                      7,
                                    ],
                                    8,
                                  ],
                                  9,
                                ],
                                10,
                              ],
                              v7,
                            ],
                            12,
                          ],
                          13,
                        ],
                        14,
                      ],
                      15,
                    ],
                    16,
                  ],
                  17,
                ],
                v5,
              );
              continue;
            }
          }
        }
      } else {
        const v7 = Array_back_(v5);
        if (v7.tag === 0) {
          return v5;
        } else {
          return [...v5, v7._1];
        }
      }
    }
  }
};
export const test1FuelCalled = (v0, v1) => test1Fuel(1000000, v0, v1);
