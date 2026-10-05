import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.AArch64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Spec.MlKem.Contract1024

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.AArch64.Args`. -/
section

/-!
# ML-KEM-1024 on AArch64: the calls of the compression functions

The calls of ML-KEM-1024's compression functions, from their proofs (as
`PrimCall.lean` of ML-KEM-768), which the top-level functions make at the
widths `d_u` and `d_v`.
-/

namespace VG.Proof.MlKem1024.AArch64

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem1024_compress_encode(f, d, out, 32 d)`. -/
theorem compressEncode1024_call {s : State} {f o : Addr} {d : Nat} (h0 : s.gpr .x0 = f)
    (h1 : ((s.gpr .x1).setWidth 32).toNat = d) (h2 : s.gpr .x2 = o) (h3 : (s.gpr .x3).toNat = 32 * d)
    (hdw : d ∈ Spec.MlKem1024.compressWidths) (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩)
    (hr : Reduced s.mem f) (hc : Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨o, 32 * d⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) →
      Q s') :
    WP isa (.call "vg_mlkem1024_compress_encode" Impl.MlKem1024.AArch64.compressEncode) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : ((s.callEntry.gpr .x1).setWidth 32).toNat = d := by rw [entry s]; exact h1
  have c2 : s.callEntry.gpr .x2 = o := (entry s).trans h2
  have c3 : (s.callEntry.gpr .x3).toNat = 32 * d := by rw [entry s]; exact h3
  refine WP.callV (k := MlKem1024.compressEncodeAArch64) MlKem1024.AArch64.CE.correct (rd := [⟨f, 1024⟩]) (wr := [⟨o, 32 * d⟩]) ?_
    hc hw ?_
  · simp only [MlKem1024.compressEncodeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [MlKem1024.compressEncodeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- `vg_mlkem1024_decode_decompress(b, 32 d, d, f)`. -/
theorem decodeDecompress1024_call {s : State} {b f : Addr} {d : Nat} (h0 : s.gpr .x0 = b)
    (h1 : (s.gpr .x1).toNat = 32 * d) (h2 : ((s.gpr .x2).setWidth 32).toNat = d) (h3 : s.gpr .x3 = f)
    (hdw : d ∈ Spec.MlKem1024.compressWidths) (hd : Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩)
    (hc : Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' →
      PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') :
    WP isa (.call "vg_mlkem1024_decode_decompress" Impl.MlKem1024.AArch64.decodeDecompress) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = 32 * d := by rw [entry s]; exact h1
  have c2 : ((s.callEntry.gpr .x2).setWidth 32).toNat = d := by rw [entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = f := (entry s).trans h3
  refine WP.callV (k := MlKem1024.decodeDecompressAArch64) MlKem1024.AArch64.DD.correct (rd := [⟨b, 32 * d⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [MlKem1024.decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [MlKem1024.decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem1024.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps`. -/
section

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_encaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Encaps.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`),
whose compression functions at the widths 11 and 5 are ML-KEM-1024's own
(`calls1024`); the taint analyses of its code are decided on its literals.
-/

namespace VG.Proof.MlKem1024.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem1024.AArch64 (compressEncode1024_call decodeDecompress1024_call)
open VG.Impl.MlKem.AArch64 (KemLay)

theorem calls1024 : Calls lay1024 :=
  ⟨fun h0 h1 h2 h3 hd => VG.Proof.MlKem1024.AArch64.compressEncode1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide),
    fun h0 h1 h2 h3 hd => VG.Proof.MlKem1024.AArch64.decodeDecompress1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide)⟩

theorem setupTaint1024 : SetupTaint lay1024 := by
  intro i hi j hj
  change i < 4 at hi
  change j < 4 at hj
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  exact ⟨_, by taint_decide⟩

theorem taints1024 : EnTaints lay1024 keccak :=
  ⟨keccak.mlkem1024EnATaint, keccak.mlkem1024EnCTaint, VG.Proof.MlKem1024.AArch64.Encaps.setupTaint1024⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem encaps_correctWith (s : State) (hs : (encapsAArch64 lay1024).pre s) :
    ∃ t s', Exec isa (encapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧
      (encapsAArch64 lay1024).post s s' :=
  encaps_correct KeyGen.wf1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 hs

theorem encaps_verifiedWith :
    Verified AArch64.target (encapsWith keccak.callee) (Spec.MlKem1024.encapsContract AArch64.abi 16) :=
  Verified.of_correct (VG.Proof.MlKem1024.AArch64.Encaps.encaps_correctWith (keccak := keccak)) (ct KeyGen.wf1024 VG.Proof.MlKem1024.AArch64.Encaps.taints1024) (by
    mlkem_implies [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsAArch64, lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.ekLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [sat]
      using VG.Proof.MlKem1024.AArch64.Encaps.sat)

theorem encaps_verified :
    Verified AArch64.target encaps (Spec.MlKem1024.encapsContract AArch64.abi 16) :=
  VG.Proof.MlKem1024.AArch64.Encaps.encaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem1024.AArch64.Encaps

end
