# lean-perf-proofs

Lean 4 proofs for performance fixes I have sent upstream. Each fix makes code
faster without changing its output, and each folder proves that the new code
returns exactly what the old code returned.

All proofs use Lean core only (no Mathlib), toolchain in `lean-toolchain`.
Check them all from the repo root:

```sh
./check.sh
```

None uses `sorry`; `#print axioms` shows only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

| Folder | Project | Change | Speedup | PR |
|---|---|---|---|---|
| [pyannote-core-sweep](pyannote-core-sweep) | pyannote.core | `Timeline.co_iter` / `segmentation` nested loops → sweep line | DER ~26x at 8k segments | [pyannote/pyannote-core#116](https://github.com/pyannote/pyannote-core/pull/116) |
| [torchao-da8w4-vnni](torchao-da8w4-vnni) | torchao | DA8W4 linear: scalar CPU fallback → AVX512-VNNI kernel | 32-176x | [pytorch/ao#5045](https://github.com/pytorch/ao/pull/5045) |
| [onnxruntime-subbyte-dequant](onnxruntime-subbyte-dequant) | ONNX Runtime | int4/int2 `DequantizeLinear` CPU loops | 4-24x | [microsoft/onnxruntime#33784](https://github.com/microsoft/onnxruntime/pull/33784) |
| [wfdb-xqrs-backsearch](wfdb-xqrs-backsearch) | wfdb-python | XQRS backsearch quadratic rescan → skip checked peaks | 40-min gap 23s → 1.3s | [MIT-LCP/wfdb-python#596](https://github.com/MIT-LCP/wfdb-python/pull/596) (merged) |
| [biopython-nexus-charbuffer](biopython-nexus-charbuffer) | Biopython | NEXUS `CharBuffer` list `pop(0)` → string + cursor | ~100x on long commands | [biopython/biopython#5397](https://github.com/biopython/biopython/pull/5397) |
| [clickhouse-posix-class-scan](clickhouse-posix-class-scan) | ClickHouse | regexp analyzer `[:` lookup rescans pattern → find last `:]` once | 34 s → 0.0002 s analysis | PR_PLACEHOLDER |

Each folder's README says what is proved and what is modelled by hand. The
models are transcribed from the real code, so the tests in each PR are what tie
a proof to the compiled implementation.
