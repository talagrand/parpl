window.BENCHMARK_DATA = {
  "lastUpdate": 1768684866076,
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
      }
    ]
  }
}