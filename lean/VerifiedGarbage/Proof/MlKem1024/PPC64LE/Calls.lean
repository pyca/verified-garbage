module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.CallsCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KemLay
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Top
import VerifiedGarbage.Proof.MlKem.PPC64LE.Calls
import VerifiedGarbage.Proof.MlKem.PPC64LE.Prims
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.CallsCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.KemLay
meta import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress
meta import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Top
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Calls
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Prims
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM-1024 on PPC64LE: the parameter set

Key generation, encapsulation and decapsulation are the functions of
`Impl/MlKem/PPC64LE/Top.lean` for `kl1024`, proven once for any parameter set
(`Proof/MlKem/PPC64LE/`). What they need of `kl1024` it proves here: its
well-formedness (`kl1024_wf`, by `decide`), and what `KemLay.CallsOk` asks of
its code (`kl1024_calls`). As `Proof/MlKem/PPC64LE/Calls.lean` and
`CallsCT.lean` for the other primitives: a contract written with the
precondition of the proof of `vg_mlkem1024_compress_encode` (and of
`vg_mlkem1024_decode_decompress`) and what it shows, the call of it with its
arguments at offsets in the buffers of a layout (`compressL4`,
`decompressL4`), and that it is constant time from any state whose argument
registers are public (`compress4T`, `decompress4T`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE

/-! ## `vg_mlkem1024_compress_encode`, `vg_mlkem1024_decode_decompress` -/

def kCmp4 : Contract isa := mkK CompressEncode.Pre
  (fun s₀ s => bytesAt s.mem (CompressEncode.O s₀) (CompressEncode.L s₀) = CompressEncode.E s₀)
  (regsEq [.r3, .r4, .r5, .r6])

theorem kCmp4_ok : ∀ s, kCmp4.pre s → ∃ t s', Exec isa compressEncode1024 s t s' ∧
    abiPreserved s s' ∧ kCmp4.post s s' :=
  mkK_ok fun _ hp => WP.mono (CompressEncode.correct hp) fun _ ⟨h1, h2, h3, h⟩ =>
    ⟨h1, h2, h3, bytesAt_eq! (compressEncode_length _ _ ▸ hp.len.symm) h⟩

def kDcm4 : Contract isa := mkK Decompress.Pre
  (fun s₀ s => PolyIs s.mem (Decompress.F s₀) (Decompress.D s₀)) (regsEq [.r3, .r4, .r5, .r6])

theorem kDcm4_ok : ∀ s, kDcm4.pre s → ∃ t s', Exec isa decodeDecompress1024 s t s' ∧
    abiPreserved s s' ∧ kDcm4.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Decompress.correct hp) fun _ ⟨h1, h2, h3, h⟩ =>
    ⟨h1, h2, h3, polyIs_of_coeffAt (p := Decompress.F s₀) fun j hj => by
      rw [h j (by rw [VG.Proof.MlKem.n_eq] at hj; exact hj)]; rfl⟩

theorem width_lt4 {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) :
    d < 2 ^ 32 ∧ 32 * d < 2 ^ 32 := by
  rcases mem_compressWidths1024 hd with rfl | rfl <;> decide

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `(i, o)` into the
`32 d` bytes at `(j, o')`. -/
theorem compressL4 {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g3 : s.gpr .r3 = L.A i o) (g4 : s.gpr .r4 = BitVec.ofNat 64 d)
    (g5 : s.gpr .r5 = L.A j o') (g6 : s.gpr .r6 = BitVec.ofNat 64 (32 * d))
    (hd : d ∈ Proof.MlKem1024.compressWidths) (hs : sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {f : Poly} (hf : PolyIs s.mem (L.A i o) f)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' →
      bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f → Q s') :
    WP isa kl1024.callCU s Q := by
  have ⟨d1, d2⟩ := width_lt4 hd
  have hd0 : 0 < 32 * d := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  let V := view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]
  have eF : CompressEncode.F V = L.A i o := by simp only [V, CompressEncode.F, view_r3, g3]
  have eO : CompressEncode.O V = L.A j o' := by simp only [V, CompressEncode.O, view_r5, g5]
  have eD : CompressEncode.dN V = d := by simp only [V, CompressEncode.dN, view_r4, g4, dN_eq d1]
  have eL : CompressEncode.L V = 32 * d := by simp only [V, CompressEncode.L, view_r6, g6, len_eq d2]
  have cw : Covers [⟨L.A j o', 32 * d⟩] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  have hpre : CompressEncode.Pre V :=
    ⟨by simp only [V, eF, State.withRegions_rd],
      by simp only [V, CompressEncode.outR, eO, eL, State.withRegions_wr],
      by simp only [CompressEncode.outR, eF, eO, eL]; exact Lay.disj hL hs,
      by rw [eF]; exact Lay.fitB hL (sepB_bounds hs) (by decide),
      by rw [eO, eL]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) hd0,
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact hf.1⟩
  refine call_kept (k := kCmp4) kCmp4_ok (by decide +kernel) (rd := [polyRegion (L.A i o)])
    (wr := [⟨L.A j o', 32 * d⟩]) hpre
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  have hq' : bytesAt (s'.withRegions _ _).mem (CompressEncode.O V) (CompressEncode.L V) =
    CompressEncode.E V := hq
  simp only [CompressEncode.E, CompressEncode.P, eF, eO, eL, eD, State.withRegions_mem, V,
    State.callEntry_mem, hf.2] at hq'
  exact hq'

/-- `Decompress_d(ByteDecode_d(·))` of the `32 d` bytes at `(i, o)` into the
polynomial at `(j, o')`. -/
theorem decompressL4 {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g3 : s.gpr .r3 = L.A i o) (g4 : s.gpr .r4 = BitVec.ofNat 64 (32 * d))
    (g5 : s.gpr .r5 = BitVec.ofNat 64 d) (g6 : s.gpr .r6 = L.A j o')
    (hd : d ∈ Proof.MlKem1024.compressWidths) (hs : sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') :
    WP isa kl1024.callDU s Q := by
  have ⟨d1, d2⟩ := width_lt4 hd
  have hd0 : 0 < 32 * d := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  let V := view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]
  have eB : Decompress.B V = L.A i o := by simp only [V, Decompress.B, view_r3, g3]
  have eF : Decompress.F V = L.A j o' := by simp only [V, Decompress.F, view_r6, g6]
  have eD : Decompress.dN V = d := by simp only [V, Decompress.dN, view_r5, g5, dN_eq d1]
  have eL : Decompress.L V = 32 * d := by simp only [V, Decompress.L, view_r4, g4, len_eq d2]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  have hpre : Decompress.Pre V :=
    ⟨by simp only [V, Decompress.inR, eB, eL, State.withRegions_rd],
      by simp only [V, eF, State.withRegions_wr],
      by simp only [Decompress.inR, eB, eF, eL]; exact Lay.disj hL hs,
      by rw [eB, eL]; exact Lay.fitB hL (sepB_bounds hs) hd0,
      by rw [eF]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide),
      by rw [eD]; exact hd, by rw [eL, eD]⟩
  refine call_kept (k := kDcm4) kDcm4_ok (by decide +kernel) (rd := [⟨L.A i o, 32 * d⟩])
    (wr := [polyRegion (L.A j o')]) hpre
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  have hq' : PolyIs (s'.withRegions _ _).mem (Decompress.F V) (Decompress.D V) := hq
  simp only [Decompress.D, Decompress.Bl, eB, eF, eL, eD, State.withRegions_mem, V,
    State.callEntry_mem] at hq'
  exact hq'

theorem compress4T :
    ConstantTime isa (fun _ => True) (regsEq [.r3, .r4, .r5, .r6]) compressEncode1024 := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.seq (VG.Proof.MlKem.PPC64LE.CompressEncode.zext_rel.mono
      (fun s₁ s₂ ⟨_, _, hsp, hr⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)))
  refine ⟨hsp, fun r hm => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp), by rw [hr .r4 (by simp)]⟩

theorem decompress4T :
    ConstantTime isa (fun _ => True) (regsEq [.r3, .r4, .r5, .r6]) decodeDecompress1024 := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.seq (VG.Proof.MlKem.PPC64LE.DecodeDecompress.zext_rel.mono
      (fun s₁ s₂ ⟨_, _, hsp, hr⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)))
  refine ⟨hsp, fun r hm => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp), by rw [hr .r5 (by simp)]⟩

/-! ## The parameter set -/

theorem kl1024_wf : kl1024.WF := .of (by decide)

theorem kl1024_calls : kl1024.CallsOk :=
  ⟨fun hL _ _ _ _ _ g3 g4 g5 g6 hd =>
      compressL4 hL g3 g4 g5 g6 (by rcases hd with rfl | rfl <;> decide),
    fun hL _ _ _ _ _ g3 g4 g5 g6 hd =>
      decompressL4 hL g3 g4 g5 g6 (by rcases hd with rfl | rfl <;> decide),
    compress4T, decompress4T, fun t => by cases t <;> exact ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.MlKem1024.PPC64LE
