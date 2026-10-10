import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# ML-KEM on x86-64: verified compressions and decompressions, as values

What a verified implementation of `ByteEncode_d ∘ Compress_d` or
`Decompress_d ∘ ByteDecode_d` provides (`CEImpl`, `DDImpl`): the callers in
`FragPrim.lean` take one for each parameter set, and ML-KEM-1024's own
implementations (`Proof/MlKem1024/X86_64/`) prove theirs importing only this
(and `nosp_of`, that code never writes the stack pointer).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- A verified implementation `c`, named `n`, of the compression for the
widths `ws` (`vg_mlkem_compress_encode`, `vg_mlkem1024_compress_encode`). -/
structure CEImpl (n : String) (c : Prog isa) (ws : List Nat) : Prop where
  le : ∀ d ∈ ws, d ≤ 11
  correct : ∀ s, (compressEncodeWK ws).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (compressEncodeWK ws).post s s'
  ct : ConstantTime isa (compressEncodeWK ws).pre (compressEncodeWK ws).pub c
  nosp : NoSp c
  depth : c.depth = 0

/-- A verified implementation `c`, named `n`, of the decompression for the
widths `ws` (`vg_mlkem_decode_decompress`, `vg_mlkem1024_decode_decompress`). -/
structure DDImpl (n : String) (c : Prog isa) (ws : List Nat) : Prop where
  le : ∀ d ∈ ws, d ≤ 11
  correct : ∀ s, (decodeDecompressWK ws).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (decodeDecompressWK ws).post s s'
  ct : ConstantTime isa (decodeDecompressWK ws).pre (decodeDecompressWK ws).pub c
  nosp : NoSp c
  depth : c.depth = 0

end VG.Proof.MlKem.X86_64
