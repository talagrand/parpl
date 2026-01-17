window.BENCHMARK_DATA = {
  "lastUpdate": 1768686148172,
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
      }
    ]
  }
}