module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Wipe
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.Zeroize.PPC64LE
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KeyGenCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.EncapsCT
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Top
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.EncapsHSat
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Decaps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.MlKem.PPC64LE.EncryptCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.RowCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Decaps
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.EncryptCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.RowCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Encrypt
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KemLay
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress
import VerifiedGarbage.Proof.MlKem.PPC64LE.Calls
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.KemLay
meta import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress
meta import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Top
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Calls
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Covers

/-! ### `MlKem1024.PPC64LE.Calls`, which only this module used -/

section

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

end

end

/-! ### `MlKem.PPC64LE.DecapsCT`, which only this module used -/

section

/-!
# ML-KEM on PPC64LE: decapsulation, constant time and `Verified`

As on 32-bit ARM (`Proof/MlKem/Arm/CallWipe.lean`): two runs from states that
agree on the public data (the pointers, the stack pointer and `ρ` in `dk`,
which the contract lets the function leak) leak the same trace (`all_ct`),
phase by phase: the blocks by the taint analysis, from the pointers, or
because they access no memory; the calls of the primitives on the same
pointers; the hashes by `hash_ct`; and the re-encryption by `encrypt_ct`. The
comparison of `c` and `c'` and the selection of the key branch on nothing but
their counters: the taint analysis proves them constant time from the
pointers, which are the same in both runs. What each run is at each point
comes from its correctness (`Decaps.lean`).

All of it holds for any parameter set: the taint analyses of the blocks whose
immediates depend on it are facts of `KemLay.CallsOk`, which the parameter set
checks by evaluation.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Decaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)

theorem rhoD_eq (K : KemLay) (s : State) : ρD K s = dkRho K.p (DK K s) :=
  VG.Proof.MlKem.KPke.ekRho_dkEk K.p (DK K s)

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  r4 : s₁.gpr .r4 = s₂.gpr .r4
  r5 : s₁.gpr .r5 = s₂.gpr .r5
  r6 : s₁.gpr .r6 = s₂.gpr .r6
  rho : ρD K s₁ = ρD K s₂

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.layEq : lay s₂ K = lay s₁ K := by
  simp only [Decaps.lay, pScr, pDk, pKey, two.r3, two.r5, two.r6, two.sp]

theorem Two.aEq (i o : Nat) : (lay s₁ K).A i o = (lay s₂ K).A i o := by rw [two.layEq]

theorem Two.regs {a b : State} (ha : DEnv K s₁ a) (hb : DEnv K s₂ b) : a.gpr .r31 = b.gpr .r31 := by
  rw [ha.ctx.r31, hb.ctx.r31, two.layEq]

theorem Two.spE {a b : State} (ha : DEnv K s₁ a) (hb : DEnv K s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

theorem Two.spD {a b : State} (ha : DD K s₁ a) (hb : DD K s₂ b) : a.sp = b.sp :=
  two.spE ha.env hb.env

theorem Two.spV {f g : Poly} {a b : State} (ha : DV K s₁ f a) (hb : DV K s₂ g b) : a.sp = b.sp :=
  two.spD ha.1 hb.1

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : DD K s₁ a) (hb : DD K s₂ b)
    (hi : ∀ {s₀ s : State}, Pre K s₀ → DD K s₀ s → ∀ p ∈ ins, PieceOk (lay s₀ K) didx s false p)
    (ho : ∀ {s₀ s : State}, Pre K s₀ → DD K s₀ s → ∀ p ∈ outs, PieceOk (lay s₀ K) didx s true p) :
    HashOk (lay s₁ K) didx ins outs a ∧ HashOk (lay s₁ K) didx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.env.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩,
    by rw [← two.layEq]; exact ⟨hb.env.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩,
    two.spE ha.env hb.env⟩

/-! ## `û` -/

theorem decU_ct {x y : State} (hx : DD K s₁ x) (hy : DD K s₂ y) {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => UInv K s₁ x j a ∧ UInv K s₂ y j b) K.decUBody fun a b =>
      (UInv K s₁ x (j + 1) a ∧ (a.gpr .r0 != 0) = decide (j + 1 ≠ K.k)) ∧
      (UInv K s₂ y (j + 1) b ∧ (b.gpr .r0 != 0) = decide (j + 1 ≠ K.k)) := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b hab =>
    ⟨decU_step hp₁ hx hj hab.1, decU_step hp₂ hy hj hab.2⟩
  refine RelCT.seq (R := fun (a b : State) =>
      (Only u a ∧ a.gpr .r3 = (lay s₁ K).A 0 (oCin + K.uLen * j) ∧
        a.gpr .r4 = BitVec.ofNat 64 (32 * K.du) ∧ a.gpr .r5 = BitVec.ofNat 64 K.du ∧
        a.gpr .r6 = (lay s₁ K).A 0 (oPoly (K.k + j))) ∧
      (Only w b ∧ b.gpr .r3 = (lay s₂ K).A 0 (oCin + K.uLen * j) ∧
        b.gpr .r4 = BitVec.ofNat 64 (32 * K.du) ∧ b.gpr .r5 = BitVec.ofNat 64 K.du ∧
        b.gpr .r6 = (lay s₂ K).A 0 (oPoly (K.k + j))))
    (relct_wp (relct_noMem (by rw [List.all_append, List.all_append]; rfl)) fun a b hab =>
      ⟨by rw [hab.1]; exact u1_ok hp₁ hx hj hu, by rw [hab.2]; exact u1_ok hp₂ hy hj hw⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => UB K s₁ j u a ∧ UB K s₂ j w b)
    (relct_wp (RelCT.callT hp₁.calls.duT (regs4 fun a b hab =>
      ⟨by rw [hab.1.1.sp, hab.2.1.sp, hu.kx.sp, hw.kx.sp]; exact two.spD hx hy,
        by rw [hab.1.2.1, hab.2.2.1, two.aEq], by rw [hab.1.2.2.1, hab.2.2.2.1],
        by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2, two.aEq]⟩))
      fun a b ⟨⟨o₁, a3, a4, a5, a6⟩, ⟨o₂, b3, b4, b5, b6⟩⟩ =>
        ⟨u2_ok hp₁ hx hj hu o₁ a3 a4 a5 a6, u2_ok hp₂ hy hj hw o₂ b3 b4 b5 b6⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (UB K s₁ j u a ∧ a.gpr .r3 = (lay s₁ K).A 0 (oPoly (K.k + j)) ∧
        a.gpr .r4 = (lay s₁ K).A 0 K.oNtt) ∧
      (UB K s₂ j w b ∧ b.gpr .r3 = (lay s₂ K).A 0 (oPoly (K.k + j)) ∧
        b.gpr .r4 = (lay s₂ K).A 0 K.oNtt))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨u3_ok hp₁ hx hj hu hab.1, u3_ok hp₂ hy hj hw hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT nttT (regs2 fun a b hab =>
      ⟨by rw [hab.1.1.kx.sp, hab.2.1.kx.sp, hu.kx.sp, hw.kx.sp]; exact two.spD hx hy,
        by rw [hab.1.2.1, hab.2.2.1, two.aEq], by rw [hab.1.2.2, hab.2.2.2, two.aEq]⟩))
    (relct_noMem (by rfl))

/-! ## K-PKE.Decrypt -/

theorem decrypt_ct {x y : State} (hx : DD K s₁ x) (hy : DD K s₂ y) :
    RelCT isa (fun a b => a = x ∧ b = y) K.decrypt fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- `û`
  refine RelCT.seq (R := fun (a b : State) => UInv K s₁ x 0 a ∧ UInv K s₂ y 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨by rw [hab.1]; exact dU_init, by rw [hab.2]; exact dU_init⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => UInv K s₁ x K.k a ∧ UInv K s₂ y K.k b)
    (relct_loop_nz (N := K.k) hK.k1 fun j hj => decU_ct two hx hy hj) ?_
  refine RelCT.pointwise fun x₃ y₃ ⟨hx₃, hy₃⟩ => ?_
  have d₁ := dU_done hp₁ hx hx₃
  have d₂ := dU_done hp₂ hy hy₃
  obtain ⟨hc₁, g30₁, hs₁, hr₁⟩ := dT_pre hp₁ d₁
  obtain ⟨hc₂, g30₂, hs₂, hr₂⟩ := dT_pre hp₂ d₂
  -- `ŝ`
  refine RelCT.seq (R := fun (a b : State) =>
      DecInv K (lay s₁ K) 2 0 x₃ 0 a ∧ DecInv K (lay s₁ K) 2 0 y₃ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨by rw [hab.1]; exact decT_init, by rw [hab.2]; exact decT_init⟩) ?_
  rw [two.layEq] at hc₂ g30₂ hr₂
  refine RelCT.seq (R := fun (a b : State) =>
      DecInv K (lay s₁ K) 2 0 x₃ K.k a ∧ DecInv K (lay s₁ K) 2 0 y₃ K.k b)
    (relct_loop_nz (N := K.k) hK.k1 fun j hj => decT_ctG hK hc₁ hc₂ g30₁ g30₂ hs₁ hr₁ hr₂ hj) ?_
  refine RelCT.pointwise fun x₅ y₅ ⟨hx₅, hy₅⟩ => ?_
  obtain ⟨e₁, ŝ₁, û₁⟩ := dT_done hp₁ d₁ hx₃.u hx₅
  rw [← two.layEq] at hy₅
  obtain ⟨e₂, ŝ₂, û₂⟩ := dT_done hp₂ d₂ hy₃.u hy₅
  -- `ŝ ∘ û`
  refine RelCT.seq (R := fun (a b : State) =>
      DV K s₁ (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k) a ∧
      DV K s₂ (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k) b)
    (relct_wp (dot_ct hK (L := lay s₁ K) e₁.env.ctx (by rw [← two.layEq]; exact e₂.env.ctx) ŝ₁ û₁
      (by rw [← two.layEq]; exact ŝ₂) (by rw [← two.layEq]; exact û₂) hp₁.calls) fun a b hab =>
      ⟨by rw [hab.1]; exact dDot_ok hp₁ e₁ ŝ₁ û₁, by rw [hab.2]; exact dDot_ok hp₂ e₂ ŝ₂ û₂⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DV K s₁ (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k) a ∧ True) ∧
        a.gpr .r3 = (lay s₁ K).A 0 K.oAcc ∧ a.gpr .r4 = (lay s₁ K).A 0 K.oNtt) ∧
      ((DV K s₂ (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k) b ∧ True) ∧
        b.gpr .r3 = (lay s₂ K).A 0 K.oAcc ∧ b.gpr .r4 = (lay s₂ K).A 0 K.oNtt))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨WP.mono (dArgs_ok hp₁ hab.1 (o := K.oAcc) (o' := K.oNtt) (by offs) (by offs))
        fun _ ⟨⟨h, _⟩, g⟩ => ⟨⟨h, trivial⟩, g⟩,
       WP.mono (dArgs_ok hp₂ hab.2 (o := K.oAcc) (o' := K.oNtt) (by offs) (by offs))
        fun _ ⟨⟨h, _⟩, g⟩ => ⟨⟨h, trivial⟩, g⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
      DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b)
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b hab =>
      ⟨two.spV hab.1.1.1 hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
        by rw [hab.1.2.2, hab.2.2.2, two.aEq]⟩))
      fun a b hab => ⟨dInv_ok hp₁ hab.1.1.1 hab.1.2.1 hab.1.2.2,
        dInv_ok hp₂ hab.2.1.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `v'`
  refine RelCT.seq (R := fun (a b : State) =>
      (DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
        a.gpr .r3 = (lay s₁ K).A 0 (oCin + K.uLen * K.k) ∧
        a.gpr .r4 = BitVec.ofNat 64 (32 * K.dv) ∧ a.gpr .r5 = BitVec.ofNat 64 K.dv ∧
        a.gpr .r6 = (lay s₁ K).A 0 (oPoly (3 * K.k))) ∧
      (DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b ∧
        b.gpr .r3 = (lay s₂ K).A 0 (oCin + K.uLen * K.k) ∧
        b.gpr .r4 = BitVec.ofNat 64 (32 * K.dv) ∧ b.gpr .r5 = BitVec.ofNat 64 K.dv ∧
        b.gpr .r6 = (lay s₂ K).A 0 (oPoly (3 * K.k))))
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨dV1_ok hp₁ hab.1, dV1_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
        PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))) ∧
      (DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b ∧
        PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))))
    (relct_wp (RelCT.callT hp₁.calls.duT (regs4 fun a b hab =>
      ⟨two.spV hab.1.1 hab.2.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
        by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1],
        by rw [hab.1.2.2.2.2, hab.2.2.2.2.2, two.aEq]⟩))
      fun a b ⟨⟨h₁, a3, a4, a5, a6⟩, ⟨h₂, b3, b4, b5, b6⟩⟩ =>
        ⟨dV2_ok hp₁ h₁ a3 a4 a5 a6, dV2_ok hp₂ h₂ b3 b4 b5 b6⟩) ?_
  -- `w`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
        PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))) ∧
        a.gpr .r3 = (lay s₁ K).A 0 (oPoly (3 * K.k)) ∧ a.gpr .r4 = (lay s₁ K).A 0 K.oAcc) ∧
      ((DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b ∧
        PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))) ∧
        b.gpr .r3 = (lay s₂ K).A 0 (oPoly (3 * K.k)) ∧ b.gpr .r4 = (lay s₂ K).A 0 K.oAcc))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨WP.mono (dArgs_ok hp₁ hab.1.1 (o := oPoly (3 * K.k)) (o' := K.oAcc) (by offs) (by offs))
        fun _ ⟨⟨h, m⟩, g⟩ => ⟨⟨h, by rw [m]; exact hab.1.2⟩, g⟩,
       WP.mono (dArgs_ok hp₂ hab.2.1 (o := oPoly (3 * K.k)) (o' := K.oAcc) (by offs) (by offs))
        fun _ ⟨⟨h, m⟩, g⟩ => ⟨⟨h, by rw [m]; exact hab.2.2⟩, g⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k)))
        (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))
          (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)))) ∧
      (DD K s₂ b ∧ PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k)))
        (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))
          (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)))))
    (relct_wp (RelCT.callT subT (regs2 fun a b hab =>
      ⟨two.spV hab.1.1.1 hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
        by rw [hab.1.2.2, hab.2.2.2, two.aEq]⟩))
      fun a b hab => ⟨dV4_ok hp₁ hab.1.1.1 hab.1.1.2 hab.1.2.1 hab.1.2.2,
        dV4_ok hp₂ hab.2.1.1 hab.2.1.2 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `m'`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DD K s₁ a ∧ PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k)))
          (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))
            (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)))) ∧
        a.gpr .r3 = (lay s₁ K).A 0 (oPoly (3 * K.k)) ∧ a.gpr .r4 = BitVec.ofNat 64 1 ∧
        a.gpr .r5 = (lay s₁ K).A 0 oMsg ∧ a.gpr .r6 = BitVec.ofNat 64 (32 * 1)) ∧
      ((DD K s₂ b ∧ PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k)))
          (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))
            (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)))) ∧
        b.gpr .r3 = (lay s₂ K).A 0 (oPoly (3 * K.k)) ∧ b.gpr .r4 = BitVec.ofNat 64 1 ∧
        b.gpr .r5 = (lay s₂ K).A 0 oMsg ∧ b.gpr .r6 = BitVec.ofNat 64 (32 * 1)))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨dM1_ok hp₁ hab.1.1 hab.1.2, dM1_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.callT compressT (regs4 ?_)
  intro a b hab
  exact ⟨two.spD hab.1.1.1 hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
    by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1, two.aEq],
    by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.decaps fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  have hL₁ := lay_ok hp₁
  have hL₂ := lay_ok hp₂
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (DEnv K s₁ a ∧ a.gpr .r30 = pDk s₁ ∧ a.gpr .r28 = pC s₁ ∧
        bytesAt a.mem ((layC s₁ K).A 2 0) K.ctLen = CT K s₁) ∧
      (DEnv K s₂ b ∧ b.gpr .r30 = pDk s₂ ∧ b.gpr .r28 = pC s₂ ∧
        bytesAt b.mem ((layC s₂ K).A 2 0) K.ctLen = CT K s₂))
    (relct_wp (taint_block [.r3, .r4, .r5, .r6] (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact two.r3
        · exact two.r4
        · exact two.r5
        · exact two.r6) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `c` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (DEnv K s₁ a ∧ a.gpr .r30 = pDk s₁ ∧ bytesAt a.mem ((lay s₁ K).A 0 oCin) K.ctLen = CT K s₁) ∧
      (DEnv K s₂ b ∧ b.gpr .r30 = pDk s₂ ∧ bytesAt b.mem ((lay s₂ K).A 0 oCin) K.ctLen = CT K s₂))
    (relct_wp (hp₁.calls.ctT.relct (fun a b hab => two.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.2.1, hab.2.2.2.1]; exact two.r4
        · exact two.regs hab.1.1 hab.2.1))
      fun a b hab =>
        ⟨WP.mono (copyC_ok hp₁ hab.1.1 hab.1.2.2.1 hab.1.2.2.2) fun _ ⟨e, g, c⟩ =>
            ⟨e, by rw [g, hab.1.2.1], c⟩,
          WP.mono (copyC_ok hp₂ hab.2.1 hab.2.2.2.1 hab.2.2.2.2) fun _ ⟨e, g, c⟩ =>
            ⟨e, by rw [g, hab.2.2.1], c⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DD K s₁ a ∧ DD K s₂ b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨WP.mono ptr28_ok fun _ h => dd_of hp₁ hab.1.1 hab.1.2.1 hab.1.2.2 h,
        WP.mono ptr28_ok fun _ h => dd_of hp₂ hab.2.1 hab.2.2.1 hab.2.2.2 h⟩) ?_
  -- K-PKE.Decrypt
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = MM K s₁) ∧
      (DD K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = MM K s₂))
    (relct_wp (RelCT.pointwise fun x y hxy => decrypt_ct two hxy.1 hxy.2) fun a b hab =>
      ⟨decrypt_ok hp₁ hab.1, decrypt_ok hp₂ hab.2⟩) ?_
  -- the frames' disjointness from the outputs, for both runs
  have sG : sepAll (dSz K) (0, oMsg, 32) (kRegs ++ [(0, oG, 64)]) = true := by ddecide
  have sJm : sepAll (dSz K) (0, oMsg, 32) (kRegs ++ [(0, oKbar, 32)]) = true := by ddecide
  have sJg : sepAll (dSz K) (0, oG, 32) (kRegs ++ [(0, oKbar, 32)]) = true := by ddecide
  have sJs : sepAll (dSz K) (0, oSigma, 32) (kRegs ++ [(0, oKbar, 32)]) = true := by ddecide
  -- `G(m' ‖ h)`
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = MM K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = K1 K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = R1 K s₁) ∧
      (DD K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = MM K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = K1 K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = R1 K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := didx) VG.Proof.MlKem.rate72 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.r31, oMsg, 32⟩, ⟨.r30, 768 * K.k + 32, 32⟩]) (outs := [⟨.r31, oG, 64⟩])
          hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceD hp h (.inr rfl) (by simp) (by show oMsg < 32768; decide)
              (by show (32 : Nat) < 32768; decide) (by show 0 < 32; decide) (by ddecide)
          · exact pieceD hp h (.inl rfl) (by simp)
              (by show 768 * K.k + 32 < 32768; have := hK.k4; omega_using [this])
              (by show (32 : Nat) < 32768; decide) (by show 0 < 32; decide) (by ddecide))
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceD hp h (.inr rfl) (fun _ => rfl) (by show oG < 32768; decide)
            (by show (64 : Nat) < 32768; decide) (by show 0 < 64; decide) (by ddecide)))
      fun a b hab =>
        ⟨WP.mono (hashG_ok hp₁ hab.1.1 hab.1.2) fun _ ⟨d, f, k, r⟩ =>
          ⟨d, (Lay.bytes_keep hL₁ f sG (by decide)).trans hab.1.2, k, r⟩,
         WP.mono (hashG_ok hp₂ hab.2.1 hab.2.2) fun _ ⟨d, f, k, r⟩ =>
          ⟨d, (Lay.bytes_keep hL₂ f sG (by decide)).trans hab.2.2, k, r⟩⟩) ?_
  -- `J(z ‖ c)`
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = MM K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = K1 K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = R1 K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oKbar) 32 = KB K s₁) ∧
      (DD K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = MM K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = K1 K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = R1 K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oKbar) 32 = KB K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := didx) VG.Proof.MlKem.rate136 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.r30, 768 * K.k + 64, 32⟩, ⟨.r31, oCin, K.ctLen⟩])
          (outs := [⟨.r31, oKbar, 32⟩]) hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceD hp h (.inl rfl) (by simp)
              (by show 768 * K.k + 64 < 32768; have := hK.k4; omega_using [this])
              (by show (32 : Nat) < 32768; decide) (by show 0 < 32; decide) (by ddecide)
          · exact pieceD hp h (.inr rfl) (by simp) (by show oCin < 32768; decide)
              (by show K.ctLen < 32768; have := ct_le hK; omega_using [this]) (ct_pos hK) (by ddecide))
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceD hp h (.inr rfl) (fun _ => rfl) (by show oKbar < 32768; decide)
            (by show (32 : Nat) < 32768; decide) (by show 0 < 32; decide) (by ddecide)))
      fun a b hab =>
        ⟨WP.mono (hashJ_ok hp₁ hab.1.1) fun _ ⟨d, f, kb⟩ =>
          ⟨d, (Lay.bytes_keep hL₁ f sJm (by decide)).trans hab.1.2.1,
            (Lay.bytes_keep hL₁ f sJg (by decide)).trans hab.1.2.2.1,
            (Lay.bytes_keep hL₁ f sJs (by decide)).trans hab.1.2.2.2, kb⟩,
         WP.mono (hashJ_ok hp₂ hab.2.1) fun _ ⟨d, f, kb⟩ =>
          ⟨d, (Lay.bytes_keep hL₂ f sJm (by decide)).trans hab.2.2.1,
            (Lay.bytes_keep hL₂ f sJg (by decide)).trans hab.2.2.2.1,
            (Lay.bytes_keep hL₂ f sJs (by decide)).trans hab.2.2.2.2, kb⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DP K s₁ a ∧ DP K s₂ b)
    (relct_wp (relct_noMem (by rfl)) fun a b ⟨⟨d, m, k, r, kb⟩, ⟨d', m', k', r', kb'⟩⟩ =>
      ⟨ptrs_dp hp₁ d m k r kb, ptrs_dp hp₂ d' m' k' r' kb'⟩) ?_
  -- the re-encryption
  refine RelCT.seq (R := fun (a b : State) => DQ K s₁ a ∧ DQ K s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨reenc_ok hp₁ hab.1, reenc_ok hp₂ hab.2⟩) ?_
  · have ey : EncPre K (lay s₁ K) (db K) y := by rw [← two.layEq]; exact encPre hp₂ hxy.2
    refine encrypt_ct (encPre hp₁ hxy.1) ey ?_
    show ekRho K.p (ekB K (lay s₁ K) (db K) x) = ekRho K.p (ekB K (lay s₁ K) (db K) y)
    have e₁ : ekB K (lay s₁ K) (db K) x = eK K s₁ := ek_of hK hxy.1
    have e₂ : ekB K (lay s₁ K) (db K) y = eK K s₂ := by
      rw [← two.layEq]; exact ek_of hK hxy.2
    rw [e₁, e₂]; exact two.rho
  -- the comparison and the selection
  refine RelCT.seq (R := fun (a b : State) => DR K s₁ a ∧ DR K s₂ b)
    (relct_wp (hp₁.calls.cmpT.relct (fun a b hab => two.spE hab.1.env hab.2.env)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.r28, hab.2.r28, two.aEq]
        · exact two.regs hab.1.env hab.2.env))
      fun a b hab => ⟨cmp_ok hp₁ hab.1, cmp_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DS K s₁ a ∧ DS K s₂ b)
    (relct_wp (taint_block [.r31] (fun a b hab => two.spE hab.1.q.env hab.2.q.env)
      (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact two.regs hab.1.q.env hab.2.q.env) (by taint_decide))
      fun a b hab => ⟨mask_ok hp₁ hab.1, mask_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DEnv K s₁ a ∧ DEnv K s₂ b)
    (relct_wp (taint_prog [.r3, .r4, .r5, .r26] (fun a b hab => two.spE hab.1.q.env hab.2.q.env)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hab.1.r3, hab.2.r3, two.aEq]
        · rw [hab.1.r4, hab.2.r4, two.aEq]
        · rw [hab.1.r5, hab.2.r5]; exact two.r5
        · rw [hab.1.r26, hab.2.r26]) (by taint_decide))
      fun a b hab => ⟨WP.mono (sel_ok hp₁ hab.1) fun _ h => h.1,
        WP.mono (sel_ok hp₂ hab.2) fun _ h => h.1⟩) ?_
  exact taint_block [.r31] (fun a b hab => two.spE hab.1 hab.2)
    (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact two.regs hab.1 hab.2) (by taint_decide)

end

/-! ## The outcome -/

theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => decapsInternal K.p iters (DK K s₀) (CT K s₀))
      (if okEnc K.k (ρD K s₀) K.k then 1 else 0)
      (if CT K s₀ = C2 K s₀ then K1 K s₀ else KB K s₀) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc K.k (ρD K s₀) K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.decapsInternal_eq, VG.Proof.MlKem.KPke.kpkeEncrypt_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.decapsInternal_eq,
      VG.Proof.MlKem.KPke.kpkeEncrypt_some ⟨hK.η₁, hK.η₂⟩ (enc_some (r := R1 K s₀) hk)]
    rfl

theorem DK_eq (K : KemLay) (s₀ : State) : DK K s₀ = bytesAt s₀.mem (s₀.gpr .r3) K.dkLen := by
  simp only [DK, Lay.A, BitVec.add_zero]; rfl

theorem CT_eq (K : KemLay) (s₀ : State) : CT K s₀ = bytesAt s₀.mem (s₀.gpr .r4) K.ctLen := by
  simp only [CT, Lay.A, BitVec.add_zero]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.decapsBodyContract PPC64LE.abi 48).pre s) : Pre kl768 s := by
  sig_pre [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl768_wf, kl768_calls, h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl768.k (ρD kl768 s₀) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 =
      if CT kl768 s₀ = C2 kl768 s₀ then K1 kl768 s₀ else KB kl768 s₀) :
    (Proof.MlKem.Scrubbed.decapsBodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl768.k (ρD kl768 s₀) kl768.k then (1 : BitVec 64) else 0) =
      if okEnc kl768.k (ρD kl768 s₀) kl768.k then 1 else 0 := by
    cases okEnc kl768.k (ρD kl768 s₀) kl768.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 2400 = DK kl768 s₀ := (DK_eq kl768 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r4) 1088 = CT kl768 s₀ := (CT_eq kl768 s₀).symm
  rw [h3, e, hkey, e0, e1]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem.PPC64LE.decaps (Proof.MlKem.Scrubbed.decapsBodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρD kl768 s₁ = ρD kl768 s₂ := by
      rw [rhoD_eq, rhoD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.Decaps

end

end

/-! ### `MlKem1024.PPC64LE.KeyGenCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_keygen`, `Verified`

The function of `Proof/MlKem/PPC64LE/KeyGenCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE VG.Proof.MlKem1024.PPC64LE
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.KeyGen hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.keyGen1024BodyContract PPC64LE.abi 48).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h3 : s.gpr .r3 = if okK kl1024 s₀ kl1024.k then 1 else 0)
    (hek : bytesAt s.mem (pEk s₀) 1568 = EK kl1024 s₀)
    (hdk : bytesAt s.mem (pDk s₀) 3168 = DK kl1024 s₀) :
    (Proof.MlKem.Scrubbed.keyGen1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32 (if okK kl1024 s₀ kl1024.k then (1 : BitVec 64) else 0) =
      if okK kl1024 s₀ kl1024.k then 1 else 0 := by
    cases okK kl1024 s₀ kl1024.k <;> rfl
  rw [h3, hek, hdk, e]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.keygen1024 (Proof.MlKem.Scrubbed.keyGen1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hek hdk⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρ₀ kl1024 s₁ = ρ₀ kl1024 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.KeyGen

end

end

/-! ### `MlKem1024.PPC64LE.EncapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_encaps`, `Verified`

The function of `Proof/MlKem/PPC64LE/EncapsCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.Encaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE VG.Proof.MlKem1024.PPC64LE
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.Encaps hiding pre_of post_of satState verified pre_ofH post_ofH verifiedH

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.encaps1024BodyContract PPC64LE.abi 48).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, by rw [h1]; exact .head _, by rw [h1]; exact .tail _ (.head _), h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4,
    b5, f1, f2, f3, f4, f5⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 = KK kl1024 s₀)
    (hct : bytesAt s.mem (pCt s₀) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 s₀)) (RR kl1024 s₀)) (EK kl1024 s₀) (M kl1024 s₀) (RR kl1024 s₀)) :
    (Proof.MlKem.Scrubbed.encaps1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 1568 = EK kl1024 s₀ := (EK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r4) 32 = M kl1024 s₀ := (M_eq kl1024 s₀).symm
  rw [h3, e, hkey, hct, e0, e1]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.encaps1024 (Proof.MlKem.Scrubbed.encaps1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey hct⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 s₁) = ekRho kl1024.p (EK kl1024 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, g7, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

/-! ## `encapsH` -/

theorem pre_ofH {s : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract PPC64LE.abi 48).pre s) : PreH kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, dh1, dh2, dh3, d4, d5, d6, d7, d8, d9, b1, bh, b2, b3, b4, b5,
    f1, fh, f2, f3, f4, f5, hh⟩ := h
  have r : (args s).rd = _ := h1
  exact ⟨⟨kl1024_wf, kl1024_calls, h0, by rw [r]; exact .head _, by rw [r]; exact .tail _ (.tail _ (.head _)),
    h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5⟩,
    by rw [h1]; exact .tail _ (.head _), dh3, bh, fh, by rw [EK_eq]; exact hh⟩

/-- `post_of` for `encapsH`, whose arguments after `ek` are one register later. -/
theorem post_ofH {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey (args s₀)) 32 = KK kl1024 (args s₀))
    (hct : bytesAt s.mem (pCt (args s₀)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 (args s₀))) (RR kl1024 (args s₀))) (EK kl1024 (args s₀)) (M kl1024 (args s₀))
      (RR kl1024 (args s₀))) :
    (Proof.MlKem.Scrubbed.encapsH1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 1568 = EK kl1024 (args s₀) := (EK_eq kl1024 (args s₀)).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r5) 32 = M kl1024 (args s₀) := (M_eq kl1024 (args s₀)).symm
  have hkey' : bytesAt s.mem (s₀.gpr .r6) 32 = KK kl1024 (args s₀) := hkey
  have hct' : bytesAt s.mem (s₀.gpr .r7) 1568 = _ := hct
  rw [h3, e, hkey', hct', e0, e1]
  exact outcome kl1024_wf (args s₀)

theorem verifiedH :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.encapsH1024 (Proof.MlKem.Scrubbed.encapsH1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correctH (pre_ofH hs)
    exact ⟨t, s', he, ⟨fun r hr => (hpres r hr).trans (args_preserved s r hr), hsp, hlr⟩, post_ofH h3 hkey hct⟩
  · have hq₁ := pre_ofH h₁
    have hq₂ := pre_ofH h₂
    sig_pub [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
      PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7, g8⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 (args s₁)) = ekRho kl1024.p (EK kl1024 (args s₂)) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ctH ⟨hq₁, hq₂, hsp, g3, g4, g5, g6, g7, g8, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlKem.PPC64LE.Encaps.satStateH 1568 1568 49152, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | exact VG.Proof.MlKem.hMem_h (by decide)
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.Encaps

end

end

/-! ### `MlKem1024.PPC64LE.DecapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_decaps`, `Verified`

The function of `Proof/MlKem/PPC64LE/CallWipe.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.Decaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE VG.Proof.MlKem1024.PPC64LE
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.Decaps hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.decaps1024BodyContract PPC64LE.abi 48).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 =
      if CT kl1024 s₀ = C2 kl1024 s₀ then K1 kl1024 s₀ else KB kl1024 s₀) :
    (Proof.MlKem.Scrubbed.decaps1024BodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ρD kl1024 s₀) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 3168 = DK kl1024 s₀ := (DK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r4) 1568 = CT kl1024 s₀ := (CT_eq kl1024 s₀).symm
  rw [h3, e, hkey, e0, e1]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem1024.PPC64LE.decaps1024 (Proof.MlKem.Scrubbed.decaps1024BodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρD kl1024 s₁ = ρD kl1024 s₂ := by
      rw [rhoD_eq, rhoD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.Decaps

end

end


/-!
# ML-KEM on PPC64LE: the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/PPC64LE.lean`) of its code, which zeroes all of
`scratch` with `vg_zeroize` once that code returns, and is verified against
the same contract with 48 more bytes of stack and `scratch` left scrubbed
(`Verified.callWipe'`; `*_scrubbed`, the contracts of
`Proof/MlKem/Scrubbed.lean`), since every byte of it is zero
(`Scrubbed.keyGen_wiped`, …). `*_verified` state them as the contracts of
`Spec/MlKem/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Wipe

open VG VG.PPC64LE

/-- `vg_zeroize` has no frames. -/
theorem zeroize_sdepth : sdepth Impl.Zeroize.PPC64LE.zeroize ≤ 0 := by decide

/-! ## What the contracts read of the memory -/

/-- Memories agreeing on the region of `k` bytes at `p` agree on the `n`
bytes at offset `o` within it. -/
theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {o n : Nat} (hn : o + n ≤ k) :
    Spec.Sha3.bytesAt m₁ (p + BitVec.ofNat 64 o) n = Spec.Sha3.bytesAt m₂ (p + BitVec.ofNat 64 o) n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [Offset.add_add]
  exact h _ (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hk, hn, hi]))

/-- `bytesAt_agree` at offset 0. -/
theorem bytesAt_agree0 {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {n : Nat} (hn : n ≤ k) :
    Spec.Sha3.bytesAt m₁ p n = Spec.Sha3.bytesAt m₂ p n := by
  have := bytesAt_agree h hk (o := 0) (n := n) (by omega_using [hn])
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- Two buffers of a contract, one of them writable, lie apart. -/
theorem pw_disj {l : List (Region × Bool)} (h : l.Pairwise (fun a b => (a.2 || b.2) = true → a.1.Disjoint b.1))
    {i j : Nat} (hij : i < j) (hj : j < l.length) (hw : (l[i].2 || l[j].2) = true) : l[i].1.Disjoint l[j].1 :=
  List.pairwise_iff_getElem.mp h i j (by omega_using [hij, hj]) hj hij hw

/-! ## The functions, with any code verified against their contracts -/

/-- `vg_mlkem768_keygen`. -/
theorem keyGen_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGenBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 32768 "vg_mlkem768_keygen" body) (Scrubbed.keyGenContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1184) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 2400) (by decide)]
      exact h)
    (Scrubbed.keyGen_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsHBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r8 32768 "vg_mlkem768_encaps_h" body) (Scrubbed.encapsHContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encapsH_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_encaps`. -/
theorem encaps_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r7 32768 "vg_mlkem768_encaps" body) (Scrubbed.encapsContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_decaps`. -/
theorem decaps_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decapsBodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 32768 "vg_mlkem768_decaps" body) (Scrubbed.decapsContract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1088) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 49152 "vg_mlkem1024_keygen" body) (Scrubbed.keyGen1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 3168) (by decide)]
      exact h)
    (Scrubbed.keyGen1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r8 49152 "vg_mlkem1024_encaps_h" body) (Scrubbed.encapsH1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encapsH1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encaps1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r7 49152 "vg_mlkem1024_encaps" body) (Scrubbed.encaps1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decaps1024BodyContract abi st))
    (hd : sdepth body ≤ st) (hst : st + 48 < 2 ^ 64)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi (st + 48)).pre s) :
    Verified target (Impl.MlKem.PPC64LE.Wipe.wiped .r6 49152 "vg_mlkem1024_decaps" body) (Scrubbed.decaps1024Contract abi (st + 48)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.PPC64LE.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hst hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])

/-! ## The stack the functions use: their callees' frames, at most 48 bytes -/

theorem keyGen_sdepth : sdepth Impl.MlKem.PPC64LE.keygen ≤ 48 := by lit_decide
theorem encapsH_sdepth : sdepth Impl.MlKem.PPC64LE.encapsH ≤ 48 := by lit_decide
theorem encaps_sdepth : sdepth Impl.MlKem.PPC64LE.encaps ≤ 48 := by lit_decide
theorem decaps_sdepth : sdepth Impl.MlKem.PPC64LE.decaps ≤ 48 := by lit_decide
theorem keyGen1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.keygen1024 ≤ 48 := by lit_decide
theorem encapsH1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.encapsH1024 ≤ 48 := by lit_decide
theorem encaps1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.encaps1024 ≤ 48 := by lit_decide
theorem decaps1024_sdepth : sdepth Impl.MlKem1024.PPC64LE.decaps1024 ≤ 48 := by lit_decide

/-! ## The states satisfying the preconditions, with the frame's 48 more bytes of stack -/

/-- A state satisfying a precondition built with `Sig.contract`, after
`sig_apply_check`. -/
macro "wipe_sat " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (sig_apply_check
   · decide +kernel
   · sig_reduce [$ls,*]
     sig_and_intros
     all_goals first
       | exact VG.Proof.MlKem.hMem_h (by decide)
       | trivial
       | decide +kernel))

theorem keyGen_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.KeyGen.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encaps_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Encaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encapsH_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Encaps.satStateH 1184 1088 32768, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs]

theorem decaps_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Decaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, PPC64LE.abi, PPC64LE.argRegs]

theorem keyGen1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem1024.PPC64LE.KeyGen.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem1024.PPC64LE.Encaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, PPC64LE.abi, PPC64LE.argRegs]

theorem encapsH1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem.PPC64LE.Encaps.satStateH 1568 1568 49152, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs]

theorem decaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 96).pre s := by
  refine ⟨Proof.MlKem1024.PPC64LE.Decaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, PPC64LE.abi, PPC64LE.argRegs]

/-! ## The functions, with 96 bytes of stack -/

theorem keyGen_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.keyGen (Scrubbed.keyGenContract abi 96) :=
  keyGen_wipe Proof.MlKem.PPC64LE.KeyGen.verified keyGen_sdepth (by decide) keyGen_sat

theorem keyGen_verified : Verified target Impl.MlKem.PPC64LE.Wipe.keyGen (Spec.MlKem.keyGenContract abi 96) :=
  keyGen_scrubbed

theorem encapsH_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.encapsH (Scrubbed.encapsHContract abi 96) :=
  encapsH_wipe Proof.MlKem.PPC64LE.Encaps.verifiedH encapsH_sdepth (by decide) encapsH_sat

theorem encapsH_verified : Verified target Impl.MlKem.PPC64LE.Wipe.encapsH (Spec.MlKem.encapsHContract abi 96) :=
  encapsH_scrubbed

theorem encaps_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.encaps (Scrubbed.encapsContract abi 96) :=
  encaps_wipe Proof.MlKem.PPC64LE.Encaps.verified encaps_sdepth (by decide) encaps_sat

theorem encaps_verified : Verified target Impl.MlKem.PPC64LE.Wipe.encaps (Spec.MlKem.encapsContract abi 96) :=
  encaps_scrubbed

theorem decaps_scrubbed : Verified target Impl.MlKem.PPC64LE.Wipe.decaps (Scrubbed.decapsContract abi 96) :=
  decaps_wipe Proof.MlKem.PPC64LE.Decaps.verified decaps_sdepth (by decide) decaps_sat

theorem decaps_verified : Verified target Impl.MlKem.PPC64LE.Wipe.decaps (Spec.MlKem.decapsContract abi 96) :=
  decaps_scrubbed

theorem keyGen1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.keyGen1024 (Scrubbed.keyGen1024Contract abi 96) :=
  keyGen1024_wipe Proof.MlKem1024.PPC64LE.KeyGen.verified keyGen1024_sdepth (by decide) keyGen1024_sat

theorem keyGen1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.keyGen1024 (Spec.MlKem1024.keyGenContract abi 96) :=
  keyGen1024_scrubbed

theorem encapsH1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.encapsH1024 (Scrubbed.encapsH1024Contract abi 96) :=
  encapsH1024_wipe Proof.MlKem1024.PPC64LE.Encaps.verifiedH encapsH1024_sdepth (by decide) encapsH1024_sat

theorem encapsH1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.encapsH1024 (Spec.MlKem1024.encapsHContract abi 96) :=
  encapsH1024_scrubbed

theorem encaps1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.encaps1024 (Scrubbed.encaps1024Contract abi 96) :=
  encaps1024_wipe Proof.MlKem1024.PPC64LE.Encaps.verified encaps1024_sdepth (by decide) encaps1024_sat

theorem encaps1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.encaps1024 (Spec.MlKem1024.encapsContract abi 96) :=
  encaps1024_scrubbed

theorem decaps1024_scrubbed :
    Verified target Impl.MlKem.PPC64LE.Wipe.decaps1024 (Scrubbed.decaps1024Contract abi 96) :=
  decaps1024_wipe Proof.MlKem1024.PPC64LE.Decaps.verified decaps1024_sdepth (by decide) decaps1024_sat

theorem decaps1024_verified :
    Verified target Impl.MlKem.PPC64LE.Wipe.decaps1024 (Spec.MlKem1024.decapsContract abi 96) :=
  decaps1024_scrubbed

end VG.Proof.MlKem.PPC64LE.Wipe
