window.BENCHMARK_DATA = {
  "lastUpdate": 1769284845001,
  "repoUrl": "https://github.com/talagrand/parpl",
  "entries": {
    "Parpl Benchmark": [
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "733fa8450270ff18f3ef308ac48238278e045cb8",
          "message": "Fix build failure",
          "timestamp": "2026-01-17T13:17:25-08:00",
          "tree_id": "39878ee2ed233d43eda2c58b8ec2241062370bab",
          "url": "https://github.com/talagrand/parpl/commit/733fa8450270ff18f3ef308ac48238278e045cb8"
        },
        "date": 1768684865705,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2399,
            "range": "± 26",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8306,
            "range": "± 123",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8774,
            "range": "± 390",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11419,
            "range": "± 132",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8640,
            "range": "± 205",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 21951,
            "range": "± 385",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1527,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 5716,
            "range": "± 37",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 6412,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Define",
            "value": 8960,
            "range": "± 60",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 6237,
            "range": "± 37",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 12913,
            "range": "± 118",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "351c885b4400a67c59cfa50f14f0c152dbc1327f",
          "message": "deps(deps): bump string-interner from 0.17.0 to 0.19.0\n\nBumps [string-interner](https://github.com/robbepop/string-interner) from 0.17.0 to 0.19.0.\n- [Release notes](https://github.com/robbepop/string-interner/releases)\n- [Changelog](https://github.com/Robbepop/string-interner/blob/master/RELEASE_NOTES.md)\n- [Commits](https://github.com/robbepop/string-interner/commits/v0.19.0)\n\n---\nupdated-dependencies:\n- dependency-name: string-interner\n  dependency-version: 0.19.0\n  dependency-type: direct:production\n  update-type: version-update:semver-minor\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>",
          "timestamp": "2026-01-17T13:39:30-08:00",
          "tree_id": "52894110a51a5ce6cc8c094d8147974b03ef581f",
          "url": "https://github.com/talagrand/parpl/commit/351c885b4400a67c59cfa50f14f0c152dbc1327f"
        },
        "date": 1768686147791,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2353,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8222,
            "range": "± 31",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8832,
            "range": "± 49",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11152,
            "range": "± 119",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8524,
            "range": "± 225",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 21443,
            "range": "± 56",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1573,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 5636,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 6337,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Define",
            "value": 8811,
            "range": "± 57",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 6137,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 12994,
            "range": "± 107",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "c858a36e6e1e8d308889026ee96694659522e039",
          "message": "Fix permissions on fuzzing workflow",
          "timestamp": "2026-01-19T14:27:19-08:00",
          "tree_id": "7792e7c43c7ce9909e77d755bff4668bb7f184df",
          "url": "https://github.com/talagrand/parpl/commit/c858a36e6e1e8d308889026ee96694659522e039"
        },
        "date": 1768861865550,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2227,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 7921,
            "range": "± 33",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8367,
            "range": "± 111",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 10940,
            "range": "± 62",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8133,
            "range": "± 223",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 21291,
            "range": "± 75",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1567,
            "range": "± 1222",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 5366,
            "range": "± 1678",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 13364,
            "range": "± 4422",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 6087,
            "range": "± 2141",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 5917,
            "range": "± 2484",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 12155,
            "range": "± 3657",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 1264,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 4691,
            "range": "± 74",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 11438,
            "range": "± 132",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 11486,
            "range": "± 134",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "3dcef904a05a2b6b319b542c67b74293e93dd63b",
          "message": "Miscellaneous small [inline] annotations",
          "timestamp": "2026-01-19T14:41:06-08:00",
          "tree_id": "956c12630e3348ac3c75dcadb98644083514a7f5",
          "url": "https://github.com/talagrand/parpl/commit/3dcef904a05a2b6b319b542c67b74293e93dd63b"
        },
        "date": 1768862684525,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2346,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8267,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8606,
            "range": "± 147",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11141,
            "range": "± 37",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8356,
            "range": "± 35",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 21672,
            "range": "± 55",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1573,
            "range": "± 620",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 5512,
            "range": "± 888",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 13500,
            "range": "± 1396",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 6077,
            "range": "± 875",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 5974,
            "range": "± 1317",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 12350,
            "range": "± 1465",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 1219,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 4527,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 10981,
            "range": "± 116",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 11113,
            "range": "± 105",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "c0c096e32f4f6668c649fc08a1fc47214909882e",
          "message": "First-character-based dispatch in Scheme tokenizer for 40% performance gain",
          "timestamp": "2026-01-19T15:07:28-08:00",
          "tree_id": "8455c13efd2b2964f9f271444ec56868f1659dbb",
          "url": "https://github.com/talagrand/parpl/commit/c0c096e32f4f6668c649fc08a1fc47214909882e"
        },
        "date": 1768864272281,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2305,
            "range": "± 95",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8264,
            "range": "± 159",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8675,
            "range": "± 234",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11271,
            "range": "± 74",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8410,
            "range": "± 334",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 21584,
            "range": "± 63",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1161,
            "range": "± 1459",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 3787,
            "range": "± 1798",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 9545,
            "range": "± 6879",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 4371,
            "range": "± 3724",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 4391,
            "range": "± 2817",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 8828,
            "range": "± 4712",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 818,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2993,
            "range": "± 65",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 7498,
            "range": "± 125",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7509,
            "range": "± 130",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "0e445c35e4dcf6d1d31f9a762c2413b4f9348633",
          "message": "Fast path for simple decimal integers saves 5%",
          "timestamp": "2026-01-19T15:16:55-08:00",
          "tree_id": "089352d04cad231a6f365be42be2316aeb1ad3c1",
          "url": "https://github.com/talagrand/parpl/commit/0e445c35e4dcf6d1d31f9a762c2413b4f9348633"
        },
        "date": 1768864839855,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2314,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8360,
            "range": "± 295",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8727,
            "range": "± 106",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11361,
            "range": "± 62",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8614,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 22028,
            "range": "± 62",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1133,
            "range": "± 1986",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 3647,
            "range": "± 2569",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 9671,
            "range": "± 3407",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 4498,
            "range": "± 3579",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 4487,
            "range": "± 3514",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 9007,
            "range": "± 7351",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 805,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2898,
            "range": "± 119",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 7496,
            "range": "± 75",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7648,
            "range": "± 70",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "3367aab64c5ef52bbb8c4d5d5626c62d3de5a697",
          "message": "Consolidate take_subsequent pattern for 12% perf improvement in identifier-heavy code",
          "timestamp": "2026-01-19T17:44:49-08:00",
          "tree_id": "dc8a58ee86c6e50dac8e7ea20b714304ee9a3003",
          "url": "https://github.com/talagrand/parpl/commit/3367aab64c5ef52bbb8c4d5d5626c62d3de5a697"
        },
        "date": 1768873709688,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2220,
            "range": "± 26",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 7935,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8155,
            "range": "± 105",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 10929,
            "range": "± 68",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8199,
            "range": "± 154",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 20980,
            "range": "± 112",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1139,
            "range": "± 2015",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 3555,
            "range": "± 3600",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 9130,
            "range": "± 7609",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 4293,
            "range": "± 5083",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 4303,
            "range": "± 4529",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 8533,
            "range": "± 6890",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 751,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2708,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 7031,
            "range": "± 142",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7153,
            "range": "± 108",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "24734daadc48b9f7d47d39cfb27ffae36ec3e110",
          "message": "deps(deps): bump thiserror from 1.0.69 to 2.0.17\n\nBumps [thiserror](https://github.com/dtolnay/thiserror) from 1.0.69 to 2.0.17.\n- [Release notes](https://github.com/dtolnay/thiserror/releases)\n- [Commits](https://github.com/dtolnay/thiserror/compare/1.0.69...2.0.17)\n\n---\nupdated-dependencies:\n- dependency-name: thiserror\n  dependency-version: 2.0.17\n  dependency-type: direct:production\n  update-type: version-update:semver-major\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>",
          "timestamp": "2026-01-20T13:20:43-08:00",
          "tree_id": "be8fdfb375056afbd572142d4f4f3771c300204b",
          "url": "https://github.com/talagrand/parpl/commit/24734daadc48b9f7d47d39cfb27ffae36ec3e110"
        },
        "date": 1768944262160,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2301,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8113,
            "range": "± 37",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8464,
            "range": "± 92",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11209,
            "range": "± 42",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8166,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 21365,
            "range": "± 54",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 1151,
            "range": "± 1959",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 3705,
            "range": "± 2991",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 9679,
            "range": "± 4679",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 4532,
            "range": "± 2848",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 4469,
            "range": "± 3529",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 8947,
            "range": "± 3587",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 820,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2939,
            "range": "± 55",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 7580,
            "range": "± 95",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7739,
            "range": "± 94",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "6fc93583f772958aad48141af5c99dc7e71bbbc8",
          "message": "Address permissions issues in Dev Container setup",
          "timestamp": "2026-01-20T23:16:00-08:00",
          "tree_id": "21552068f8ec0fcfa54d6c509edbef16df62a9cb",
          "url": "https://github.com/talagrand/parpl/commit/6fc93583f772958aad48141af5c99dc7e71bbbc8"
        },
        "date": 1768980201848,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2356,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8468,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8769,
            "range": "± 92",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11509,
            "range": "± 348",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8629,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 22130,
            "range": "± 98",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 942,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 3314,
            "range": "± 102",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 8150,
            "range": "± 110",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 3805,
            "range": "± 68",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 3712,
            "range": "± 48",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 7780,
            "range": "± 146",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 771,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2720,
            "range": "± 37",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 7155,
            "range": "± 60",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7268,
            "range": "± 80",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "866e8a1afbaea0fb3f7ac9e66c78a9a59df1f524",
          "message": "Fix cargo fmt",
          "timestamp": "2026-01-20T23:21:39-08:00",
          "tree_id": "74b6826f05fa3c165752ffa8905054835f0e6961",
          "url": "https://github.com/talagrand/parpl/commit/866e8a1afbaea0fb3f7ac9e66c78a9a59df1f524"
        },
        "date": 1768980320831,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2336,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8375,
            "range": "± 180",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8764,
            "range": "± 204",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11361,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8589,
            "range": "± 55",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 22191,
            "range": "± 977",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 936,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 3249,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 8115,
            "range": "± 161",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 3770,
            "range": "± 41",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 3639,
            "range": "± 21",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 7722,
            "range": "± 46",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 780,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2755,
            "range": "± 21",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 7190,
            "range": "± 54",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7346,
            "range": "± 97",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "21f5c07302ad57bffc9ccb68afc88a3d69808c4f",
          "message": "Scheme/CEL WriterError now carries the original error (boxed).\nCopy method on Scheme writer is also fixed.\nPeek is simplified to not require cloneable errors.",
          "timestamp": "2026-01-24T10:07:00-08:00",
          "tree_id": "554963204eb6b74f9cbc1107ebd06a840d675b1c",
          "url": "https://github.com/talagrand/parpl/commit/21f5c07302ad57bffc9ccb68afc88a3d69808c4f"
        },
        "date": 1769281052265,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2282,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 8147,
            "range": "± 135",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8571,
            "range": "± 294",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 11174,
            "range": "± 65",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8324,
            "range": "± 31",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 21481,
            "range": "± 76",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 845,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 2989,
            "range": "± 77",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 7658,
            "range": "± 109",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 3505,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 3398,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 7034,
            "range": "± 99",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 738,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2672,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 6944,
            "range": "± 34",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7111,
            "range": "± 39",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "80ce04ffbfd5d0706c4fca9cc636513e4bfb5494",
          "message": "Fix Fuzzing project and update dependencies",
          "timestamp": "2026-01-24T11:49:04-08:00",
          "tree_id": "5200cb66d6ca92a05bb8bc8e5169bafe1aff4a94",
          "url": "https://github.com/talagrand/parpl/commit/80ce04ffbfd5d0706c4fca9cc636513e4bfb5494"
        },
        "date": 1769284374108,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2230,
            "range": "± 30",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 7796,
            "range": "± 40",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 7975,
            "range": "± 151",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 10734,
            "range": "± 62",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 7863,
            "range": "± 58",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 20591,
            "range": "± 72",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 849,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 3013,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 7710,
            "range": "± 54",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 3538,
            "range": "± 25",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 3437,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 7133,
            "range": "± 61",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 737,
            "range": "± 90",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2753,
            "range": "± 248",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 7070,
            "range": "± 635",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7165,
            "range": "± 653",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "b11012d2dde935c4310bcd3025d3811390dd4c19",
          "message": "Fix Fuzzing project and update dependencies",
          "timestamp": "2026-01-24T11:57:05-08:00",
          "tree_id": "7a9e5c6aecb537b9ab442f6b17e2a43f650e554c",
          "url": "https://github.com/talagrand/parpl/commit/b11012d2dde935c4310bcd3025d3811390dd4c19"
        },
        "date": 1769284844705,
        "tool": "cargo",
        "benches": [
          {
            "name": "CEL Parsing/Simple (1 + 2)",
            "value": 2196,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Arithmetic",
            "value": 7828,
            "range": "± 108",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Comparison",
            "value": 8098,
            "range": "± 148",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Function Call",
            "value": 10517,
            "range": "± 49",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Ternary",
            "value": 8024,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "CEL Parsing/Complex",
            "value": 20678,
            "range": "± 156",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Simple (+ 1 2)",
            "value": 869,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Nested",
            "value": 2997,
            "range": "± 69",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Factorial",
            "value": 7671,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Lambda",
            "value": 3560,
            "range": "± 37",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Quote",
            "value": 3438,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "Scheme Parsing/Complex",
            "value": 7068,
            "range": "± 76",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Simple (+ 1 2)",
            "value": 747,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Nested",
            "value": 2684,
            "range": "± 177",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/Factorial",
            "value": 6987,
            "range": "± 25",
            "unit": "ns/iter"
          },
          {
            "name": "MiniScheme Parsing/1K Sample",
            "value": 7077,
            "range": "± 43",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}