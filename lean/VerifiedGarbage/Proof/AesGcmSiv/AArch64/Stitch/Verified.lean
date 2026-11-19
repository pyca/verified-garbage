module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Verified
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Poly
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesGcm.AArch64.Tag

/-! ### `AesGcmSiv.AArch64.Stitch.Fn`, which only this module used -/

section

/-! ### `AesGcmSiv.AArch64.Stitch.Open`, which only this module used -/

section

/-! ### `AesGcmSiv.AArch64.Stitch.Crypt`, which only this module used -/

section

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: counter mode

Untrusted: everything here is checked by Lean. The keystream of the loops
(`Ctx.ks`) is that of RFC 8452 §4 (`ks_eq`): the counter blocks `cv q` the
loops build are `counterBlock icb q` when the counter block at `W + 96` is
`icb` (`st_cv`). So what `ctrLoop` leaves is counter mode of the batches
(`ctrPart_of_dataInv`), and the blocks after them go as in
`Proof.AesGcmSiv.AArch64.crypt_ok` (`blocksFrom_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs CtrSt)
open VG.Proof.Aes.AArch64 (DataInv)
open VG.Proof.Aes.AArch64.Aese (st st_ext getD_st vbyte_readW)
open VG.Proof.AesGcm.AArch64 (Others lsr_ofNat eval_zero)
open VG.Proof.AesGcmSiv.AArch64 (setWidth_rt32 read4_readW)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (byRounds)

/-! ## The counter blocks -/

theorem vbyte_setLane32_0 (x : BitVec 128) (w : BitVec 32) {j : Nat} (hj : j < 16) :
    vbyte (setLane x 32 0 w) j = if j < 4 then w.extractLsb' (8 * j) 8 else vbyte x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : j < 4
  · rw [ite_eq_left h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega_arith,
      show 8 * j + i < 32 by omega_arith, show ¬ 8 * j + i < 0 by omega_arith]
    simp
  · rw [ite_eq_right h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega_arith,
      show ¬ 8 * j + i < 32 by omega_arith, show ¬ 8 * j + i < 0 by omega_arith]
    simp [BitVec.getLsbD_of_ge w (8 * j + i) (by omega_arith)]

/-- The loops' counter block `q` is RFC 8452's, of the counter block at `W + 96`. -/
theorem st_cv {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) (q : Nat) :
    st (σ.cv q) = Vector.ofFn fun k => (Spec.GcmSiv.counterBlock icb q).getD k 0 := by
  refine st_ext fun k hk => ?_
  rw [getD_st _ hk, Proof.Aes.AArch64.Aese.getD_ofFn hk, Ctx.cv, vbyte_setLane32_0 _ _ hk,
    GcmSiv.counterBlock_word]
  dsimp only
  obtain hw : σ.c0 + BitVec.ofNat 32 q = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + q) := by
    show σ.m₀.readW (σ.W + BitVec.ofNat 64 96) 32 + _ = _
    rw [C.word, Nat.add_zero, ← BitVec.ofNat_add]
  by_cases h : k < 4
  · rw [ite_eq_left h, hw, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [Proof.Cmac.length_le4]; exact h)]
    simp [Proof.Cmac.le4, h]
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [Proof.Cmac.length_le4]; omega_arith), Proof.Cmac.length_le4,
      ← List.getD_eq_getElem?_getD, vbyte_readW _ _ hk, ← C.rest,
      Proof.Cmac.getD_bytesAt _ _ (by omega_arith), Offset.add_add, Offset.add_add, show 100 + (k - 4) = 96 + k by omega_arith]
    rfl

/-- The loops' keystream is RFC 8452's. -/
theorem ks_eq {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) (i : Nat) :
    σ.ks i = (GcmSiv.ksBlock (Spec.GcmSiv.ctxCiph σ.m₀ σ.K σ.nr) icb (i / 16)).getD (i % 16) 0 := by
  simp only [Ctx.ks, GcmSiv.ksBlock, Spec.GcmSiv.ctxCiph, Spec.GcmSiv.aesWith, st_cv C]
  obtain hi : i % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem hi, Option.getD_some]
  simp [Vector.getD, hi]

/-- The data after the batches' counter mode: `ctrPart` of it. -/
theorem ctrPart_of_dataInv {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) {m : Mem} {n : Nat}
    {x : List Byte} (hx : bytesAt σ.m₀ σ.D n = x)
    (hd : DataInv σ.m₀ m σ.D (8 * σ.nb) (8 * σ.nb) σ.ks)
    (hf : ∀ q < n, 128 * σ.nb ≤ q → m (σ.D + BitVec.ofNat 64 q) = σ.m₀ (σ.D + BitVec.ofNat 64 q)) :
    bytesAt m σ.D n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph σ.m₀ σ.K σ.nr) icb x (128 * σ.nb) := by
  obtain hxl : x.length = n := by rw [← hx, Proof.AesGcm.AArch64.length_bytesAt]
  refine GcmSiv.ext_getD (by rw [Proof.AesGcm.AArch64.length_bytesAt, GcmSiv.length_ctrPart, hxl]) fun q hq => ?_
  rw [Proof.AesGcm.AArch64.length_bytesAt] at hq
  rw [Proof.Cmac.getD_bytesAt _ _ hq, GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; exact hq), ← hx,
    Proof.Cmac.getD_bytesAt _ _ hq]
  by_cases h : q < 128 * σ.nb
  · rw [ite_eq_left h, hd q (by omega_arith), ite_eq_left (by omega_arith), ks_eq C]
  · rw [ite_eq_right h, hf q hq (by omega_arith)]

/-! ## The blocks after the batches -/

open VG.Proof.AesGcmSiv.AArch64 (BlocksPost cryptBlock_ok ciph_cryR) in
/-- `Proof.AesGcmSiv.AArch64.blocks_ok` from block `b₀`. -/
theorem blocksFrom_ok (v : Proof.AesGcm.AArch64.GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b₀ : Nat} (hb : b₀ < p.n / 16)
    (h27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * b₀)) (h28 : t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * b₀))
    (C : CtrSt p.W icb b₀ t.mem) (hx : bytesAt t.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * b₀))
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (.loop (Impl.AesGcmSiv.AArch64.cryptBlock v.callees) (.nonzero .x .x9)) t
      (BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := Impl.AesGcmSiv.AArch64.cryptBlock v.callees) (c := .nonzero .x .x9)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - b₀) t ⟨b₀, rfl, hb, ⟨E, rfl, rfl, h27, h28, C, hx, Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  obtain hc' : Spec.GcmSiv.ctxCiph t'.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_ok v L P.env hxl (j := j) (by omega_arith) P.x27 P.x28 P.ctr P.data hc') fun t'' Q => ?_
  obtain P' : BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.x27, Q.x28, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  obtain ev := Proof.AesGcm.AArch64.eval_nonzero Q.x9 (by have := L.n_lt; omega_arith)
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega_arith), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), p.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, P'⟩

/-! ## The batches -/

open VG.Proof.AesGcmSiv.AArch64 (cryR) in
/-- What counter mode of the batches leaves, from `t`. -/
structure BatchPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ctr : CtrSt p.W icb (8 * (p.n / 128)) t'.mem
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x (128 * (p.n / 128))
  frame : Frame (cryR p.Wn p.W p.D p.n) t.mem t'.mem

/-- `ctrSetup ++ batches`: the counter's word, the key schedule and the batches. -/
theorem ctrSetup_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa (ctrSetup ++ batches) t = some t₁ ∧
      t₁.read .w .x10 = t.mem.readW (p.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 32 ∧
      t₁.gpr .x15 = p.W + BitVec.ofNat 64 240 ∧ t₁.gpr .x9 = p.D + BitVec.ofNat 64 (128 * 0) ∧
      t₁.gpr .x11 = BitVec.ofNat 64 (p.n / 128 - 0) ∧
      Others [.x9, .x10, .x11, .x15] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  obtain c₀ := E.perm.wR (show 96 + 4 ≤ 1760 by decide)
  refine ⟨_, by simp only [ctrSetup, batches, List.cons_append, List.nil_append]; grun [E.x19, c₀], ?_, ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
  · simp [State.read, gpr_write, E.x19, setWidth_rt32, read4_readW]; rfl
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x25]
  · simp [gpr_write, E.x26, lsr_ofNat _ _ L.n_lt]

/-- `ctrFinish`: the counter's word stored back, after the batches. -/
theorem ctrFinish_ok {p : Prm} (L : Lay p) {H : Spec.Gcm.Block} {m₀ : Mem} {rd wr : List Region} {icb : List Byte}
    (C : CtrSt p.W icb 0 m₀) {s₀ t₂ : State}
    (I : CInv ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, H, m₀, rd, wr⟩ s₀ (p.n / 128) (p.n / 128) t₂)
    (E₂ : Env p t₂) :
    WP isa (.block ctrFinish) t₂ fun t₃ => Env p t₃ ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr ∧ t₃.v = t₂.v ∧
      CtrSt p.W icb (8 * (p.n / 128)) t₃.mem ∧
      bytesAt t₃.mem p.D p.n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph m₀ (p.W + BitVec.ofNat 64 240) p.R) icb
        (bytesAt m₀ p.D p.n) (128 * (p.n / 128)) ∧
      Frame (VG.Proof.AesGcmSiv.AArch64.cryR p.Wn p.W p.D p.n) m₀ t₃.mem ∧
      Frame [⟨p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem t₃.mem := by
  have hn := L.n_lt
  have hww := L.ww
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, H, m₀, rd, wr⟩
  obtain c₁ := E₂.perm.wW (show 96 + 4 ≤ 1760 by decide)
  have hf₂ : Frame [σ.dR] m₀ t₂.mem := I.frame
  obtain dDR : ∀ {d k : Nat}, d + k ≤ 3808 → ∀ q ∈ [σ.dR], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ((L.d_w' h).sub_left (Region.sub_prefix (by show 128 * (p.n / 128) ≤ p.n; omega_arith))).symm
  obtain r₂ : bytesAt t₂.mem (p.W + BitVec.ofNat 64 100) 12 = bytesAt m₀ (p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.AArch64.bytesAt_frame hf₂ (dDR (by decide)) (by decide)
  obtain fw : ∀ v : BitVec 32, Frame [⟨p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem
      (t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hmem : ∀ v : BitVec 32, t₂.mem.write (p.W + BitVec.ofNat 64 96) 4 v =
      t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v := fun v => by
    simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  obtain hd₂ : bytesAt t₂.mem p.D p.n =
      GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph m₀ (p.W + BitVec.ofNat 64 240) p.R) icb (bytesAt m₀ p.D p.n)
        (128 * (p.n / 128)) :=
    ctrPart_of_dataInv (σ := σ) C rfl I.data fun q hq hq' =>
      frame_outside (a := 0) (n := 128 * (p.n / 128)) hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact .inl (by show (⟨p.D, 128 * (p.n / 128)⟩ : Region) = ⟨p.D + BitVec.ofNat 64 0, _⟩; simp))
        hn (by omega_arith) q hq (.inr (by rw [Nat.zero_add]; exact hq'))
  refine WP.run ⟨_, by simp only [ctrFinish]; grun [E₂.x19, c₁], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  refine ⟨E₂.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) rfl rfl rfl,
    by simp only [rd_write], by simp only [wr_write], rfl, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write]
    refine ⟨?_, ?_⟩
    · rw [hmem, Mem.readW_writeW_self32]
      have h := I.x10
      simp only [State.read, Size.bits] at h
      rw [h]
      show m₀.readW (p.W + BitVec.ofNat 64 96) 32 + _ = _
      rw [C.word, Nat.add_zero, ← BitVec.ofNat_add]
    · rw [hmem, Proof.AesGcm.AArch64.bytesAt_frame (fw _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
          (by decide), r₂, C.rest]
  · simp only [mem_write]
    rw [hmem, Proof.AesGcm.AArch64.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)) (Nat.le_of_lt hn), hd₂]
  · simp only [mem_write]
    rw [hmem]
    refine (hf₂.sub fun q hq => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains p.W (Nat.le_refl _) (by decide) (by decide))
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨⟨p.D, p.n⟩, by simp, Region.sub_prefix (by show 128 * (p.n / 128) ≤ p.n; omega_arith)⟩
  · simp only [mem_write]; rw [hmem]; exact fw _

theorem ctrBatch_ok (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {icb : List Byte}
    (C : CtrSt p.W icb 0 t.mem) (hnb : 1 ≤ p.n / 128) :
    WP isa (.seq (.block (ctrSetup ++ batches)) (.seq (byRounds (ctrLoop e3)) (.block ctrFinish))) t
      (BatchPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R) icb (bytesAt t.mem p.D p.n) t) := by
  have hn := L.n_lt
  have hww := L.ww
  obtain ⟨t₁, run₁, x10₁, x15₁, x9₁, x11₁, o₁, m₁, sp₁, rd₁, wr₁⟩ := ctrSetup_ok L E
  obtain E₁ : Env p t₁ := E.keep (fun r hr => o₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, 0, t.mem, t.rd, t.wr⟩
  obtain hp : KPreC σ := {
    rounds := by rcases L.rounds with h | h <;> simp [σ, h]
    nb1 := hnb
    n16 := by show 128 * (p.n / 128) < 2 ^ 64; omega_arith
    k_in := by
      show InRegions (t.rd ++ t.wr) (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))
      exact E.perm.wR (by rcases L.rounds with h | h <;> rw [h] <;> decide)
    c_in := E.perm.wR (by decide)
    d_in := by
      show InRegions t.wr p.D (128 * (p.n / 128))
      exact E.perm.d _ _ ⟨⟨p.D, p.n⟩, List.mem_singleton_self _, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith⟩
    d_k := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩
      exact (L.d_w' (d := 240) (k := 16 * (p.R + 1)) (by rcases L.rounds with h | h <;> rw [h] <;> decide)).sub_left
        (Region.sub_prefix (by omega_arith))
    d_c := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega_arith))
    wrap_c := by show p.W.toNat + 96 + 16 ≤ 2 ^ 64; omega_arith
    wrap_k := by
      show (p.W + BitVec.ofNat 64 240).toNat + 16 * (p.R + 1) ≤ 2 ^ 64
      rw [L.toNat_W (by decide)]; rcases L.rounds with h | h <;> rw [h] <;> omega_arith }
  obtain hI : CInv σ t₁ 0 0 t₁ := {
    le := Nat.zero_le _
    x9 := x9₁
    x10 := by rw [x10₁, Nat.mul_zero, BitVec.add_zero]
    x11 := x11₁
    gpr := fun _ _ => rfl
    data := fun i _ => by
      rw [m₁, ite_eq_right (by omega_arith)]; show t.mem _ = t.mem _ ^^^ 0; simp
    frame := by rw [m₁]; exact Frame.refl _ _
    sp := rfl
    rd := rfl
    wr := rfl }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (byRounds_ok (P := CInv σ t₁ 0 0) L.rounds3 E₁.x22
    (fun s' hg _ hm hsp hrd hwr => hI.of_x1314 hg hm hsp hrd hwr)
    (fun s hs => ctrLoop_ok e3 hp (by rw [E₁.x19]) x15₁ (by rw [rd₁, wr₁]) wr₁ hs)) fun t₂ I => ?_
  obtain E₂ : Env p t₂ := E₁.keep (fun r hr => I.gpr r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (by rw [I.sp]) I.rd I.wr
  refine WP.mono (ctrFinish_ok L C I E₂) fun t₃ ⟨E₃, rd₃, wr₃, _, C₃, d₃, f₃, _⟩ =>
    ⟨E₃, by rw [rd₃, I.rd, rd₁], by rw [wr₃, I.wr, wr₁], C₃, d₃, f₃⟩


/-- The batches, if the data has one. -/
theorem ctrBatches_ok (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {icb : List Byte}
    (C : CtrSt p.W icb 0 t.mem) :
    WP isa (ifBatch (.seq (.block (ctrSetup ++ batches)) (.seq (byRounds (ctrLoop e3)) (.block ctrFinish)))) t
      (BatchPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R) icb (bytesAt t.mem p.D p.n) t) := by
  have hn := L.n_lt
  unfold ifBatch
  refine WP.seq (WP.mono (batchHead_ok L E) fun t₂ ⟨x9₂, E₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.ite (decide (p.n / 128 = 0)) (eval_zero x9₂ (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n / 128 = 0 := by simpa using h
    refine WP.block_nil ⟨E₂, rd₂, wr₂, ?_, ?_, by rw [m₂]; exact Frame.refl _ _⟩
    · rw [h0, m₂]; exact C
    · rw [h0, m₂, Nat.mul_zero, GcmSiv.ctrPart_zero]
  · have h1 : 1 ≤ p.n / 128 := by simp at h; omega_arith
    rw [← m₂] at C
    refine WP.mono (ctrBatch_ok e3 L E₂ C h1) fun t₃ B => ?_
    rw [m₂] at B
    exact ⟨B.env, by rw [B.rd, rd₂], by rw [B.wr, wr₂], B.ctr, B.data, by rw [← m₂]; exact B.frame⟩

open VG.Proof.AesGcmSiv.AArch64 (headMem) in
/-- The counter block `cryptHead` writes. -/
theorem headMem_ctr {p : Prm} (m : Mem) :
    CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt m p.W 16)) 0 (headMem m p.W) := by
  obtain hicb : bytesAt (headMem m p.W) (p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt m p.W 16) := by
    rw [headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
        rw [Proof.AesGcm.AArch64.add_ofNat_assoc], Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words,
      Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  obtain h4 := Proof.Cmac.bytesAt_add (headMem m p.W) (p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, Proof.AesGcm.AArch64.add_ofNat_assoc] at h4
  refine ⟨?_, ?_⟩
  · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
  · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

/-! ## The rest -/

open VG.Proof.AesGcmSiv.AArch64 (BlocksPost TailPost cryptTail_ok ciph_cryR cryR) in
/-- `cryptRest`: counter mode of the data past its batches. -/
theorem cryptRest_ok (v : Proof.AesGcm.AArch64.GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n)
    (C : CtrSt p.W icb (8 * (p.n / 128)) t.mem)
    (hx : bytesAt t.mem p.D p.n = GcmSiv.ctrPart ciph icb x (128 * (p.n / 128)))
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (cryptRest v.callees) t (TailPost p ciph icb x t) := by
  have hn := L.n_lt
  obtain hcl : ∀ y, (ciph y).length = 16 := fun y => by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  rw [cryptRest, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (rest_ok L E) fun t₁ ⟨x27₁, x28₁, E₁, _, m₁, rd₁, wr₁⟩ => ?_
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₂ ht₂ => ?_
  obtain hlt : p.n - 128 * (p.n / 128) < 2 ^ 64 := by omega_arith
  obtain x9₂ : t₂.gpr .x9 = BitVec.ofNat 64 ((p.n - 128 * (p.n / 128)) / 16) := by
    rw [← ht₂]; simp [gpr_write, State.read, x28₁, lsr_ofNat _ _ hlt]
  obtain E₂ : Env p t₂ := by rw [← ht₂]; exact E₁.write (by decide) _
  obtain x27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * (8 * (p.n / 128))) := by
    rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x27₁, show 16 * (8 * (p.n / 128)) = 128 * (p.n / 128) by omega_arith]
  obtain x28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * (8 * (p.n / 128))) := by
    rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x28₁, show 16 * (8 * (p.n / 128)) = 128 * (p.n / 128) by omega_arith]
  obtain m₂ : t₂.mem = t.mem := by rw [← ht₂, mem_write, m₁]
  obtain rd₂ : t₂.rd = t.rd := by rw [← ht₂, rd_write, rd₁]
  obtain wr₂ : t₂.wr = t.wr := by rw [← ht₂, wr_write, wr₁]
  rw [← m₂] at C hx hc
  -- The whole blocks.
  obtain hmid : WP isa (.ite (.zero .x .x9) (.block []) (.loop (Impl.AesGcmSiv.AArch64.cryptBlock v.callees)
      (.nonzero .x .x9))) t₂ (BlocksPost p ciph icb x (p.n / 16) t₂) := by
    refine WP.ite (decide ((p.n - 128 * (p.n / 128)) / 16 = 0)) (eval_zero x9₂ (by omega_arith)) (fun h => ?_) (fun h => ?_)
    · have h0 : (p.n - 128 * (p.n / 128)) / 16 = 0 := by simpa using h
      obtain e : p.n / 16 = 8 * (p.n / 128) := by omega_arith
      refine WP.block_nil ?_
      rw [e]
      exact ⟨E₂, rfl, rfl, x27₂, x28₂, C, by rw [hx]; congr 1; omega_arith, Frame.refl _ _⟩
    · have h0 : (p.n - 128 * (p.n / 128)) / 16 ≠ 0 := by simpa using h
      exact blocksFrom_ok v L E₂ hxl (by omega_arith) x27₂ x28₂ C (by rw [hx]; congr 1; omega_arith) hc
  refine WP.seq (WP.mono hmid fun t₃ B => ?_)
  obtain x28₃ : t₃.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [B.x28]; congr 1; omega_arith
  refine WP.ite (decide (p.n % 16 = 0)) (eval_zero x28₃ (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨B.env, by rw [B.rd, rd₂], by rw [B.wr, wr₂], ?_, by have f := B.frame; rwa [m₂] at f⟩
    rw [B.data, show 16 * (p.n / 16) = p.n by omega_arith]
  · have h0 : p.n % 16 ≠ 0 := by simpa using h
    obtain hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
      rw [ciph_cryR L B.frame, hc]
    refine WP.mono (cryptTail_ok v L B.env hxl (b := p.n / 16) (r := p.n % 16) (by omega_arith) (by omega_arith) (by omega_arith)
      B.x27 x28₃ B.ctr B.data hc₃) fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, B.rd, rd₂], by rw [T.wr, B.wr, wr₂], T.data, ?_⟩
    obtain f := B.frame.trans T.frame
    rwa [m₂] at f

/-! ## Counter mode -/

open VG.Proof.AesGcmSiv.AArch64 (CryptPost cryptHead_ok headMem cryR) in
theorem crypt_ok (e3 : Bool) (v : Proof.AesGcm.AArch64.GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (crypt e3 v.callees) t (CryptPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, _, _, _, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  obtain hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  obtain hxl : (bytesAt t.mem p.D p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  obtain f₁ : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
      rw [Proof.AesGcm.AArch64.add_ofNat_assoc]]
    exact Proof.Cmac.frame_store2 _ _ _
  obtain dD : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  obtain hx₁ : bytesAt t₁.mem p.D p.n = bytesAt t.mem p.D p.n :=
    Proof.AesGcm.AArch64.bytesAt_frame f₁ dD (Nat.le_of_lt hn)
  obtain hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_arith)]
  obtain C₀ : CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
    rw [hm₁]; exact headMem_ctr _
  obtain E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  obtain fC : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ cryR p.Wn p.W p.D p.n, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The batches.
  obtain hb := WP.mono (ctrBatches_ok e3 L E₁ C₀) fun t₂ (B : BatchPost p _ _ _ t₁ t₂) => by
    rw [hc₁, hx₁] at B; exact B
  refine WP.seq (WP.mono hb fun t₂ B => ?_)
  obtain hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    rw [VG.Proof.AesGcmSiv.AArch64.ciph_cryR L B.frame, hc₁]
  refine WP.mono (cryptRest_ok v L B.env hxl B.ctr B.data hc₂) fun t₃ T => ?_
  refine ⟨T.env, by rw [T.rd, B.rd, rd₁], by rw [T.wr, B.wr, wr₁], ((f₁.sub fC).trans B.frame).trans T.frame, ?_⟩
  rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end


/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: decryption

Untrusted: everything here is checked by Lean. `openData` decrypts the data
in place and absorbs what it decrypted (`openData_ok`): the batches by
`openLoop`, which decrypts batch `i + 1` while it hashes batch `i`
(`openBatch_ok`), the rest by `crypt`'s blocks (`cryptRest_ok`) and
`absorb`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs CtrSt cryR absR absorbR absorbR_buf Absorbed AbsPost
  absorb_ok elemsAt)
open VG.Proof.AesGcm.AArch64 (GcmImpl Others lsr_ofNat eval_zero)
open VG.Proof.Gcm.AArch64.Pmull (ext8 PrepPow ext8_ext8)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (Y C byRounds)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-- The counter block, after code that misses it. -/
theorem ctrSt_frame {W : Addr} {icb : List Byte} {j : Nat} {m m' : Mem} (h : CtrSt W icb j m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 96, 16⟩ : Region).Disjoint r) : CtrSt W icb j m' :=
  ⟨by rw [hf.readW (r := ⟨W + BitVec.ofNat 64 96, 4⟩) (Region.contains_self _ _)
        (fun r hr => (hd r hr).sub_left (Offset.sub W (by decide) (by decide))) (by decide), h.word],
    by rw [Proof.AesGcm.AArch64.bytesAt_frame hf
        (fun r hr => (hd r hr).sub_left (Offset.sub W (by decide) (by decide))) (by decide), h.rest]⟩

/-- `ctrSetup`: the counter's word and the key schedule. -/
theorem ctrSet_ok {p : Prm} {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa ctrSetup t = some t₁ ∧
      t₁.read .w .x10 = t.mem.readW (p.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 32 ∧
      t₁.gpr .x15 = p.W + BitVec.ofNat 64 240 ∧
      Others [.x10, .x15] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  obtain c₀ := E.perm.wR (show 96 + 4 ≤ 1760 by decide)
  refine ⟨_, by simp only [ctrSetup]; grun [E.x19, c₀], ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
  · simp [State.read, gpr_write, E.x19, VG.Proof.AesGcmSiv.AArch64.setWidth_rt32,
      VG.Proof.AesGcmSiv.AArch64.read4_readW]; rfl
  · simp [gpr_write, E.x19]

/-! ## The batches -/

/-- What `open`'s batches leave, from `t`. -/
structure OBatchPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ctr : CtrSt p.W icb (8 * (p.n / 128)) t'.mem
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x (128 * (p.n / 128))
  frame : Frame (cryR p.Wn p.W p.D p.n ++ absR p.W) t.mem t'.mem
  out : blockAt t'.mem (p.W + BitVec.ofNat 64 80) =
    ghashFrom (blockAt t.mem (p.W + BitVec.ofNat 64 64)) (blockAt t.mem (p.W + BitVec.ofNat 64 80))
      (elemsAt t'.mem p.D (8 * (p.n / 128)))

theorem openBatch_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {icb : List Byte} (C : CtrSt p.W icb 0 t.mem) (hnb : 1 ≤ p.n / 128) :
    WP isa (.seq (.block (tblBuild ++ ctrSetup ++ batches ++ ghSetup))
      (.seq (byRounds (openLoop e3)) (.block (ctrFinish ++ ghFinish)))) t
      (OBatchPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R) icb (bytesAt t.mem p.D p.n) t) := by
  have hn := L.n_lt
  have hww := L.ww
  rw [List.append_assoc, List.append_assoc, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (tblBuild_ok hP (by rw [E.x19]; exact E.perm.wR (by decide)) (by rw [E.x19]; exact E.perm.wW (by decide)))
    fun s₁ ⟨tok₁, f₁, g₁, sp₁, rd₁, wr₁⟩ => ?_
  obtain E₁ : Env p s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)) sp₁ rd₁ wr₁
  rw [E.x19] at tok₁ f₁
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, x10₂, x15₂, o₂, m₂, sp₂, rd₂, wr₂⟩ := ctrSet_ok E₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain E₂ : Env p s₂ := E₁.keep (fun r hr => o₂ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  refine WP.mono (ghPre_ok L E₂) fun s₃ ⟨x9₃, x11₃, c₃, y₃, o₃, m₃, sp₃, rd₃, wr₃⟩ => ?_
  obtain E₃ : Env p s₃ := E₂.keep (fun r hr => o₃ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  obtain m₁₃ : s₃.mem = s₁.mem := by rw [m₃, m₂]
  -- What the table changed.
  obtain dT : ∀ {d k : Nat}, d + k ≤ 480 → ∀ r ∈ [tblR p.W], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by show d + k ≤ 480; exact h)) (by omega_arith) (by decide)
  obtain dTD : ∀ r ∈ [tblR p.W], (⟨p.D, p.n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)
  obtain C₃ : CtrSt p.W icb 0 s₃.mem := by rw [m₁₃]; exact ctrSt_frame C f₁ (dT (by decide))
  obtain hY : blockAt s₂.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) := by
    rw [m₂]; exact Proof.AesGcm.AArch64.blockAt_frame f₁ (dT (by decide))
  obtain hc₃ : Spec.GcmSiv.ctxCiph s₃.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    rw [m₁₃]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => (dT (k := 240) (by decide) r hr).sub_left
      (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega_arith)]
  obtain hx₃ : bytesAt s₃.mem p.D p.n = bytesAt t.mem p.D p.n := by
    rw [m₁₃]; exact Proof.AesGcm.AArch64.bytesAt_frame f₁ dTD (Nat.le_of_lt hn)
  -- The context of the loop.
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, blockAt t.mem (p.W + BitVec.ofNat 64 64),
    s₃.mem, t.rd, t.wr⟩
  obtain hp : KPre σ := {
    rounds := by rcases L.rounds with h | h <;> simp [σ, h]
    nb1 := hnb
    n16 := by show 128 * (p.n / 128) < 2 ^ 64; omega_arith
    k_in := by
      show InRegions (t.rd ++ t.wr) (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))
      exact E.perm.wR (by rcases L.rounds with h | h <;> rw [h] <;> decide)
    c_in := E.perm.wR (by decide)
    d_in := by
      show InRegions t.wr p.D (128 * (p.n / 128))
      exact E.perm.d _ _ ⟨⟨p.D, p.n⟩, List.mem_singleton_self _, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith⟩
    t_in := E.perm.wR (by decide)
    d_k := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩
      exact (L.d_w' (d := 240) (k := 16 * (p.R + 1)) (by rcases L.rounds with h | h <;> rw [h] <;> decide)).sub_left
        (Region.sub_prefix (by omega_arith))
    d_c := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega_arith))
    d_t := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega_arith))
    wrap_t := by show p.W.toNat + 480 + 192 ≤ 2 ^ 64; omega_arith
    wrap_c := by show p.W.toNat + 96 + 16 ≤ 2 ^ 64; omega_arith
    wrap_k := by
      show (p.W + BitVec.ofNat 64 240).toNat + 16 * (p.R + 1) ≤ 2 ^ 64
      rw [L.toNat_W (by decide)]; rcases L.rounds with h | h <;> rw [h] <;> omega_arith
    tbl := by show TblOk s₃.mem p.W _; rw [m₁₃]; exact tok₁ }
  obtain hI : CInv σ s₃ 0 0 s₃ := {
    le := Nat.zero_le _
    x9 := x9₃
    x10 := by
      simp only [State.read] at x10₂ ⊢
      rw [o₃ _ (by decide), x10₂, Nat.mul_zero, BitVec.add_zero]
      show _ = s₃.mem.readW _ 32
      rw [m₃, m₂]
    x11 := x11₃
    gpr := fun _ _ => rfl
    data := fun i _ => by rw [ite_eq_right (by omega_arith)]; show s₃.mem _ = s₃.mem _ ^^^ 0; simp
    frame := Frame.refl _ _
    sp := rfl
    rd := rfl
    wr := rfl }
  have x19₃ : s₃.gpr .x19 = p.W := E₃.x19
  obtain x15₃ : s₃.gpr .x15 = p.W + BitVec.ofNat 64 240 := by rw [o₃ _ (by decide), x15₂]
  refine WP.seq (WP.mono (byRounds_ok (P := fun s' => CInv σ s₃ 0 0 s' ∧ s'.v = s₃.v) L.rounds3 E₃.x22
    (fun s' hg hv hm hsp hrd hwr => ⟨hI.of_x1314 hg hm hsp hrd hwr, hv⟩)
    (fun s ⟨hs, hv⟩ => openLoop_ok hp gh (y := blockAt t.mem (p.W + BitVec.ofNat 64 80)) x19₃ x15₃
      (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]) (by rw [wr₃, wr₂, wr₁]) e3 hs (by rw [hv, y₃, hY]) (by rw [hv]; exact c₃)))
    fun s₄ O => ?_)
  -- The counter's word and `Y` stored back.
  obtain E₄ : Env p s₄ := E₃.keep (fun r hr => O.ci.gpr r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) O.ci.sp O.ci.rd O.ci.wr
  rw [WP.block_append_iff]
  refine WP.mono (ctrFinish_ok L C₃ O.ci E₄) fun s₅ ⟨E₅, rd₅, wr₅, v₅, C₅, d₅, f₅, fw₅⟩ => ?_
  refine WP.mono (ghFinish_ok (p := p) (s := s₅) E₅.x19 (by rw [wr₅, O.ci.wr, wr₃, wr₂, wr₁]; exact E.perm.wW (by decide)))
    fun s₆ ⟨b₆, f₆, g₆, sp₆, rd₆, wr₆⟩ => ?_
  obtain dY : ∀ {d k : Nat}, (96 ≤ d ∨ d + k ≤ 80) → d + k ≤ 3808 →
      ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 80, 16⟩ : Region)], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases h₁ with h | h
      · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain dYD : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 80, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)
  refine ⟨E₅.keep (fun r _ => by rw [g₆]) sp₆ rd₆ wr₆, by rw [rd₆, rd₅, O.ci.rd, rd₃, rd₂, rd₁],
    by rw [wr₆, wr₅, O.ci.wr, wr₃, wr₂, wr₁], ctrSt_frame C₅ f₆ (dY (.inl (by decide)) (by decide)), ?_, ?_, ?_⟩
  · rw [Proof.AesGcm.AArch64.bytesAt_frame f₆ dYD (Nat.le_of_lt hn), d₅, hc₃, hx₃]
  · have fA : Frame (cryR p.Wn p.W p.D p.n ++ absR p.W) t.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨p.W + BitVec.ofNat 64 480, 1280⟩, by simp [absR], Region.sub_prefix (by decide)⟩
    obtain fB : Frame (cryR p.Wn p.W p.D p.n ++ absR p.W) s₃.mem s₅.mem :=
      f₅.mono fun r hr => List.mem_append_left _ hr
    obtain fC : Frame (cryR p.Wn p.W p.D p.n ++ absR p.W) s₅.mem s₆.mem := f₆.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [absR]
    rw [← m₁₃] at fA
    exact (fA.trans fB).trans fC
  · rw [b₆, v₅, O.y, ext8_ext8, yh]
    refine congrArg _ ?_
    obtain hr : ∀ i < 8 * (p.n / 128), s₄.mem.readW (p.D + BitVec.ofNat 64 (16 * i)) 128 =
        s₆.mem.readW (p.D + BitVec.ofNat 64 (16 * i)) 128 := fun i hi => by
      obtain hc : (⟨p.D, p.n⟩ : Region).Contains (p.D + BitVec.ofNat 64 (16 * i)) 16 :=
        Offset.contains_base p.D (by omega_arith) (by omega_arith)
      rw [f₆.readW hc dYD (by decide), fw₅.readW hc (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by decide)]
    rw [← elemsAt_eq hr]
    exact List.map_congr_left fun i hi =>
      (readW_of_dataInv hp.n16 O.ci.data (List.mem_range.mp hi) (Nat.le_refl _)).symm


/-- The batches, if the data has one. -/
theorem openBatches_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {icb : List Byte} (C : CtrSt p.W icb 0 t.mem) :
    WP isa (ifBatch (.seq (.block (tblBuild ++ ctrSetup ++ batches ++ ghSetup))
      (.seq (byRounds (openLoop e3)) (.block (ctrFinish ++ ghFinish))))) t
      (OBatchPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R) icb (bytesAt t.mem p.D p.n) t) := by
  have hn := L.n_lt
  unfold ifBatch
  refine WP.seq (WP.mono (batchHead_ok L E) fun t₂ ⟨x9₂, E₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.ite (decide (p.n / 128 = 0)) (eval_zero x9₂ (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n / 128 = 0 := by simpa using h
    refine WP.block_nil ⟨E₂, rd₂, wr₂, ?_, ?_, by rw [m₂]; exact Frame.refl _ _, ?_⟩
    · rw [h0, m₂]; exact C
    · rw [h0, m₂, Nat.mul_zero, GcmSiv.ctrPart_zero]
    · rw [h0, m₂]; simp [elemsAt, ghashFrom]
  · have h1 : 1 ≤ p.n / 128 := by simp at h; omega_arith
    rw [← m₂] at C
    refine WP.mono (openBatch_ok hP gh e3 L E₂ C h1) fun t₃ B => ?_
    rw [m₂] at B
    exact ⟨B.env, by rw [B.rd, rd₂], by rw [B.wr, wr₂], B.ctr, B.data, by rw [← m₂]; exact B.frame,
      by rw [B.out, m₂]⟩

/-! ## The data -/

/-- The elements of the first `k` blocks of `n` bytes, from the bytes. -/
theorem elemsAt_of_getD {m₁ m₂ : Mem} {D : Addr} {n k : Nat} (hk : 16 * k ≤ n)
    (h : ∀ q < 16 * k, (bytesAt m₁ D n).getD q 0 = (bytesAt m₂ D n).getD q 0) :
    elemsAt m₁ D k = elemsAt m₂ D k := by
  refine List.map_congr_left fun i hi => congrArg _ (GcmSiv.ext_getD (by simp [Proof.Cmac.bytesAt_length]) fun t ht => ?_)
  obtain hi' := List.mem_range.mp hi
  rw [Proof.Cmac.bytesAt_length] at ht
  obtain e := h (16 * i + t) (by omega_arith)
  rw [Proof.Cmac.getD_bytesAt _ _ (by omega_arith), Proof.Cmac.getD_bytesAt _ _ (by omega_arith)] at e
  rw [Proof.Cmac.getD_bytesAt _ _ ht, Proof.Cmac.getD_bytesAt _ _ ht, Offset.add_add, e, ← Offset.add_add]

/-- What `openData` leaves, from `t`. -/
structure OpenPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR p.Wn p.W p.D p.n ++ absorbR p.W) t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n)
  out : blockAt t'.mem (p.W + BitVec.ofNat 64 80) =
    ghashFrom (blockAt t.mem (p.W + BitVec.ofNat 64 64)) (blockAt t.mem (p.W + BitVec.ofNat 64 80))
      (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t'.mem p.D p.n)))

open VG.Proof.AesGcmSiv.AArch64 (cryptHead_ok headMem TailPost key_cryR) in
theorem openData_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (openData e3 v.callees) t (OpenPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, _, _, _, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  obtain hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  obtain hxl : (bytesAt t.mem p.D p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  -- What the parts miss.
  obtain dCry : ∀ {d k : Nat}, d + k ≤ 96 → ∀ r ∈ cryR p.Wn p.W p.D p.n, (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (L.d_w' (by omega_arith)).symm
  obtain dAbs : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ absR p.W, (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h r hr => by
      simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain dKey : ∀ r ∈ cryR p.Wn p.W p.D p.n ++ absR p.W,
      (⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact (key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le)
    · simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := L.rounds_le
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain f₁ : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
      rw [Proof.AesGcm.AArch64.add_ofNat_assoc]]
    exact Proof.Cmac.frame_store2 _ _ _
  obtain d96 : ∀ {d k : Nat}, d + k ≤ 96 → ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q := fun {d k} h q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain dD : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  obtain hx₁ : bytesAt t₁.mem p.D p.n = bytesAt t.mem p.D p.n :=
    Proof.AesGcm.AArch64.bytesAt_frame f₁ dD (Nat.le_of_lt hn)
  obtain hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_arith)]
  obtain hH₁ : blockAt t₁.mem (p.W + BitVec.ofNat 64 64) = blockAt t.mem (p.W + BitVec.ofNat 64 64) :=
    Proof.AesGcm.AArch64.blockAt_frame f₁ (d96 (by decide))
  obtain hY₁ : blockAt t₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
    Proof.AesGcm.AArch64.blockAt_frame f₁ (d96 (by decide))
  obtain C₀ : CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
    rw [hm₁]; exact headMem_ctr _
  obtain E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The batches.
  obtain hb := WP.mono (openBatches_ok hP gh e3 L E₁ C₀) fun t₂ (B : OBatchPost p _ _ _ t₁ t₂) => by
    rw [hc₁, hx₁] at B; exact B
  refine WP.seq (WP.mono hb fun t₂ B => ?_)
  obtain hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    rw [← hc₁]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame B.frame dKey (by have := L.rounds_le; omega_arith)]
  -- The rest, decrypted.
  refine WP.seq (WP.mono (cryptRest_ok v L B.env hxl B.ctr B.data hc₂) fun t₃ T => ?_)
  -- The rest, absorbed.
  refine WP.seq (WP.mono (rest_ok L T.env) fun t₄ ⟨x27₄, x28₄, E₄, _, m₄, rd₄, wr₄⟩ => ?_)
  obtain hc : Covers [⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩] (t₄.rd ++ t₄.wr) := by
    rw [rd₄, wr₄, T.rd, T.wr, B.rd, B.wr, rd₁, wr₁]
    exact Proof.AesGcm.AArch64.covers_left (Proof.AesGcm.AArch64.covers_off E.perm.d (by omega_arith) hn)
  obtain dW : (⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W, p.Wn⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega_arith))
  refine WP.mono (absorb_ok v L E₄ hc (by omega_arith) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * (p.n / 128)) (by omega_arith)]
      have := L.dw; have := Nat.mod_le (p.D.toNat + 128 * (p.n / 128)) (2 ^ 64); omega_arith)
    dW x27₄ x28₄) fun t₅ P₅ => ?_
  obtain d₅ : bytesAt t₅.mem p.D p.n = bytesAt t₃.mem p.D p.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame P₅.frame (absorbR_buf L.d_w) (Nat.le_of_lt hn), m₄]
  obtain hd₅ : bytesAt t₅.mem p.D p.n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n) := by
    rw [d₅, T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  refine ⟨P₅.env, by rw [P₅.rd, rd₄, T.rd, B.rd, rd₁], by rw [P₅.wr, wr₄, T.wr, B.wr, wr₁], ?_, hd₅, ?_⟩
  · have g₁ : Frame (cryR p.Wn p.W p.D p.n ++ absorbR p.W) t.mem t₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
    obtain g₂ : Frame (cryR p.Wn p.W p.D p.n ++ absorbR p.W) t₁.mem t₂.mem := B.frame.mono fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    obtain g₃ : Frame (cryR p.Wn p.W p.D p.n ++ absorbR p.W) t₂.mem t₄.mem := by
      rw [m₄]; exact T.frame.mono fun r hr => List.mem_append_left _ hr
    obtain g₄ : Frame (cryR p.Wn p.W p.D p.n ++ absorbR p.W) t₄.mem t₅.mem :=
      P₅.frame.mono fun r hr => List.mem_append_right _ hr
    exact ((g₁.trans g₂).trans g₃).trans g₄
  · have hH₄ : blockAt t₄.mem (p.W + BitVec.ofNat 64 64) = blockAt t.mem (p.W + BitVec.ofNat 64 64) := by
      rw [m₄, Proof.AesGcm.AArch64.blockAt_frame T.frame (dCry (by decide)),
        Proof.AesGcm.AArch64.blockAt_frame B.frame (fun r hr => by
          rcases List.mem_append.mp hr with hr | hr
          · exact dCry (by decide) r hr
          · exact dAbs (by decide) r hr), hH₁]
    obtain hY₄ : blockAt t₄.mem (p.W + BitVec.ofNat 64 80) = blockAt t₂.mem (p.W + BitVec.ofNat 64 80) := by
      rw [m₄, Proof.AesGcm.AArch64.blockAt_frame T.frame (dCry (by decide))]
    obtain hr₅ : bytesAt t₅.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) =
        bytesAt t₄.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) :=
      Proof.AesGcm.AArch64.bytesAt_frame P₅.frame (absorbR_buf dW) (by omega_arith)
    obtain he : elemsAt t₅.mem p.D (8 * (p.n / 128)) = elemsAt t₂.mem p.D (8 * (p.n / 128)) := by
      refine elemsAt_of_getD (n := p.n) (by omega_arith) fun q hq => ?_
      rw [d₅, T.data, B.data, GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; omega_arith),
        GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; omega_arith), ite_eq_left (by omega_arith), ite_eq_left (by omega_arith)]
    rw [P₅.out, hH₄, hY₄, B.out, hH₁, hY₁, elems_split t₅.mem, Proof.Gcm.ghashFrom_append, he, hr₅]

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end


/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `seal_wp` is
`Proof.AesGcmSiv.AArch64.seal_wp` with the interleaved `polyval` and
`crypt`; `open_wp` is `Proof.AesGcmSiv.AArch64.open_wp` with the additional
data absorbed first and the data decrypted and absorbed by `openData`
(`openMid_ok`), which leaves what `crypt` then `polyval` did.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG hkeyOf)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs cryR polyR absorbR absR absorbR_H absorbR_buf Absorbed
  AbsPost absorb_ok lens_ok tagIn_ok tagInMem_frame tagInMem_bytes TagInputEq bytesAt_keep ciph_keep TagSlot
  prmOf args_of_seal args_of_open entry_ok keys_ok tag_ok tagOut_ok recv_ok cmp_ok mask_ok entryR ciph_cryR
  decrypt_eq sealPre openPre)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok Others length_bytesAt)
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

theorem forall_app {l₁ l₂ : List Region} {P : Region → Prop} (h₁ : ∀ r ∈ l₁, P r) (h₂ : ∀ r ∈ l₂, P r) :
    ∀ r ∈ l₁ ++ l₂, P r := fun r hr => (List.mem_append.mp hr).elim (h₁ r) (h₂ r)

/-! ## `seal` -/

theorem seal_wp (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) (hti : TagInputEq) {s : State} (h : sealPre Wn s) :
    WP isa (Impl.AesGcmSiv.AArch64.Stitch.«seal» e3 v.callees) s fun s' =>
      GprAbi s s' ∧ Proof.AesGcmSiv.AArch64.sealAArch64.post s s' := by
  obtain ⟨L, P, hTw, hA⟩ := args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₁ ⟨E₁, sv₁, f₁, sl₁, rd₁, wr₁⟩ => ?_)
  -- The keys.
  refine WP.seq (WP.mono (Proof.AesGcmSiv.AArch64.WP.rdwr (keys_ok v L E₁)) fun s₂ ⟨Ky, _, kw⟩ => ?_)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok hP gh e3 v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok e3 v L Tg.env) fun s₅ Cr => ?_)
  -- The copy of the tag, and `restore`.
  obtain sl₅ : TagSlot (prmOf s) s₅.mem :=
    (((sl₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L)
  obtain w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, kw, wr₁]
  obtain ⟨s₆, run₆, fT, hT₆, -, ho₆, sp₆, rd₆, wr₆⟩ := tagOut_ok L Cr.env sl₅ (by rw [w₅]; exact hTw)
  obtain E₆ : Env (prmOf s) s₆ := Cr.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  obtain sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (((((sv₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 88 ≤ 1760 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (exit_ok (s₀ := s) E₆.x19 E₆.sp E₆.w1760R sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R) (Spec.GcmSiv.keyLen (prmOf s).R)
      (bytesAt s.mem (prmOf s).N 12) (bytesAt s.mem (prmOf s).D (prmOf s).n) (bytesAt s.mem (prmOf s).A (prmOf s).al) =
    (bytesAt s'.mem (prmOf s).D (prmOf s).n, bytesAt s'.mem (prmOf s).T 16)
  rw [hm, hT₆, bytesAt_keep fT (by disj_tac L) (by omega_using [hn])]
  -- What the pieces read.
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (prmOf s).K (prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  obtain n₁ : bytesAt s₁.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := bytesAt_keep f₁ (by disj_tac L) (by decide)
  obtain n₂ : bytesAt s₂.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  obtain a₂ : bytesAt s₂.mem (prmOf s).A (prmOf s).al = bytesAt s.mem (prmOf s).A (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega_using [this]),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega_using [this])]
  obtain d₂ : bytesAt s₂.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega_using [hn]), bytesAt_keep f₁ (by disj_tac L) (by omega_using [hn])]
  obtain d₄ : bytesAt s₄.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by omega_using [hn]), bytesAt_keep Po.frame (by disj_tac L) (by omega_using [hn]), d₂]
  obtain key₃ : Spec.GcmSiv.ctxCiph s₃.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  obtain key₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R := by
    rw [ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  obtain t₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  rw [L.w0] at t₅
  have tg := Tg.out
  rw [L.w0] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-! ## `open` -/

/-- What the additional data absorbed, `openData`, the lengths and the tag
input leave, from `t`: what `crypt` then `polyval` leave. -/
structure OpenMid (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR p.Wn p.W p.D p.n ++ polyR p.W) t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n)
  out : bytesAt t'.mem (p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem p.N 12) (bytesAt t'.mem p.D p.n)
      (bytesAt t.mem p.A p.al)

theorem openMid_ok (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0) {k : Prog isa} {Q : State → Prop}
    (hk : ∀ t', OpenMid p t t' → WP isa k t' Q) :
    WP isa (.seq (.block [Impl.AesGcm.AArch64.mov .x27 .x23, Impl.AesGcm.AArch64.mov .x28 .x24])
      (.seq (Impl.AesGcmSiv.AArch64.absorb v.callees) (.seq (Impl.AesGcmSiv.AArch64.Stitch.openData e3 v.callees)
      (.seq (Impl.AesGcmSiv.AArch64.lens v.callees) (.seq (.block Impl.AesGcmSiv.AArch64.tagIn) k))))) t Q := by
  have hn := L.n_lt
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((E.write (by decide) _).write (by decide) _)
    (by simp only [rd_write, wr_write]; exact E.perm.aad) L.al_lt L.aw L.a_w
    (by simp [gpr_write, E.x23]) (by simp [gpr_write, E.x24])) fun t₂ P₂ => ?_)
  simp only [mem_write] at P₂
  obtain P₂' := P₂.of_eq (t := t) rfl rfl rfl
  -- The data.
  refine WP.seq (WP.mono (openData_ok hP gh e3 v L P₂.env) fun t₄ O => ?_)
  obtain hH : ∀ r ∈ cryR p.Wn p.W p.D p.n ++ absorbR p.W, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
    forall_app (by disj_tac L) (absorbR_H L)
  obtain sA : ∀ r ∈ absorbR p.W, ∃ r' ∈ cryR p.Wn p.W p.D p.n ++ absorbR p.W, Region.Sub r r' :=
    fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  obtain P₂₄ := Absorbed.trans hH (P₂'.sub sA) ⟨O.env, O.rd, O.wr, O.frame, O.out⟩
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  obtain P₂₅ := Absorbed.trans hH P₂₄ (P₅.sub sA)
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok P₂₅.env
  refine WP.seq (WP.of_runBlock ⟨t₆, run₆, hk t₆ ?_⟩)
  obtain E₆ : Env p t₆ := P₂₅.env.keep (fun q hq => ho₆ q (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  -- What the absorbing of the additional data kept.
  obtain dA : ∀ {Q : Addr} {k : Nat}, (⟨Q, k⟩ : Region).Disjoint ⟨p.W, p.Wn⟩ → k ≤ 2 ^ 64 →
      bytesAt t₂.mem Q k = bytesAt t.mem Q k := fun hd hk' => by
    rw [Proof.AesGcm.AArch64.bytesAt_frame P₂'.frame (absorbR_buf hd) hk']
  obtain fT : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t₅.mem t₆.mem := by rw [hm₆]; exact tagInMem_frame _ _ _
  obtain d₆ : bytesAt t₆.mem p.D p.n = bytesAt t₄.mem p.D p.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame fT (by disj_tac L) (Nat.le_of_lt hn),
      Proof.AesGcm.AArch64.bytesAt_frame P₅.frame (absorbR_buf L.d_w) (Nat.le_of_lt hn)]
  refine ⟨E₆, by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => ?_).trans (fT.mono fun q hq => ?_)
    · rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
    · simp only [List.mem_singleton] at hq; subst hq
      exact List.mem_append_right _ List.mem_cons_self
  · have hk : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
        Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R :=
      ciph_keep P₂'.frame (by disj_tac L) L.rounds_le
    obtain hw0 := bytesAt_keep P₂'.frame (P := p.W + BitVec.ofNat 64 0) (n := 16) (by disj_tac L) (by decide)
    rw [L.w0] at hw0
    rw [d₆, O.data, hw0, hk, dA L.d_w (Nat.le_of_lt hn)]
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
    obtain nN : bytesAt t₅.mem p.N 12 = bytesAt t.mem p.N 12 :=
      Proof.AesGcm.AArch64.bytesAt_frame P₂₅.frame (forall_app (by disj_tac L) (absorbR_buf L.n_w)) (by decide)
    rw [d₆, hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) (hti : TagInputEq) {s : State} (h : openPre Wn s) :
    WP isa (Impl.AesGcmSiv.AArch64.Stitch.«open» e3 v.callees) s fun s' =>
      GprAbi s s' ∧ Proof.AesGcmSiv.AArch64.openAArch64.post s s' := by
  obtain ⟨L, P, hA⟩ := args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₀ ⟨E₀, sv₀, f₀, sl₀, _, _⟩ => ?_)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, -, ho₁, sp₁, rd₁, wr₁⟩ := recv_ok L E₀ sl₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain E₁ : Env (prmOf s) s₁ := E₀.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  obtain fR' : Frame [⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by rw [L.w0]; exact fR
  obtain sv₁ : SavedAt s₁.mem (prmOf s).W s := sv₀.frame fR' (by disj_tac L)
  obtain f₁ : Frame [entryR (prmOf s).W, ⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩, by simp, fun _ h => h⟩)
  obtain hT₁ : bytesAt s₁.mem (prmOf s).W 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [hR₁, bytesAt_keep f₀ (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  -- The additional data, then the data decrypted and absorbed, the lengths and the tag input.
  refine openMid_ok hP gh e3 v L Ky.env Ky.hkey Ky.acc fun s₄ Md => ?_
  obtain dMd : ∀ {R' : Region}, (∀ r ∈ cryR (prmOf s).W (prmOf s).D (prmOf s).n, R'.Disjoint r) →
      (∀ r ∈ polyR (prmOf s).W, R'.Disjoint r) → ∀ r ∈ cryR (prmOf s).W (prmOf s).D (prmOf s).n ++ polyR (prmOf s).W,
        R'.Disjoint r := fun h₁ h₂ => forall_app h₁ h₂
  -- Its tag at `W + 224`.
  refine WP.seq (WP.mono (tag_ok v L Md.env (o := 224) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, x27₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env (prmOf s) s₆ := Tg.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ x27₆) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  refine WP.block_append (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  obtain sv₇ : SavedAt s₇.mem (prmOf s).W s := by
    have := (((sv₁.frame Ky.frame (by disj_tac L)).frame Md.frame (dMd (by disj_tac L) (by disj_tac L))).frame
      Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok (s₀ := s) (Mk.env.write (by decide) _).x19 (Mk.env.write (by decide) _).sp
    (Mk.env.write (by decide) _).w1760R (by simp only [mem_write]; exact sv₇)) fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (prmOf s).K (prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  obtain n₁ : bytesAt s₁.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := bytesAt_keep f₁ (by disj_tac L) (by decide)
  obtain n₂ : bytesAt s₂.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  obtain a₂ : bytesAt s₂.mem (prmOf s).A (prmOf s).al = bytesAt s.mem (prmOf s).A (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega_using [this]),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega_using [this])]
  obtain d₂ : bytesAt s₂.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega_using [hn]), bytesAt_keep f₁ (by disj_tac L) (by omega_using [hn])]
  obtain tag₂ : bytesAt s₂.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), L.w0, hT₁]
  obtain tag₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by decide),
      bytesAt_keep Md.frame (dMd (by disj_tac L) (by disj_tac L)) (by decide), tag₂]
  rw [L.w0] at tag₂ tag₅
  obtain ci₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R :=
    ciph_keep Md.frame (dMd (by disj_tac L) (by disj_tac L)) hRb
  obtain d₆ : bytesAt s₆.mem (prmOf s).D (prmOf s).n = bytesAt s₄.mem (prmOf s).D (prmOf s).n := by
    rw [hm₆, bytesAt_keep Tg.frame (by disj_tac L) (by omega_using [hn])]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Md.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Md.out
  rw [← au, n₂, a₂, pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.data
  rw [hm₆, tg, tag₅] at md
  rw [← hm₆, d₆, pt₃] at md
  obtain ax : s'.gpr .x0 = s₆.gpr .x27 := by
    rw [hx0]; simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero]; exact Mk.x27
  rw [x27₆, tg, tag₅] at ax
  show openPost (openResult s) s' (prmOf s).D (prmOf s).n
  obtain hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
            (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
          bytesAt s.mem (prmOf s).T 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
        (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
      bytesAt s.mem (prmOf s).T 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (prmOf s).T 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) := Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end

/-! ### `AesGcmSiv.AArch64.Stitch.CT`, which only this module used -/

section

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the functions are constant time

Untrusted: everything here is checked by Lean. As
`Proof.AesGcmSiv.AArch64.seal_ct` and `open_ct`: the batches, which call
nothing, pass the taint analysis (`Stitch/Taint.lean`); the blocks after
them go as `Proof.AesGcmSiv.AArch64.crypt_rel`'s, from block `8 ⌊n / 128⌋`
(`cryptRest_rel`), and the rest of the data is absorbed by `absorb`
(`absorb_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs CtrSt pubRegs rel_env rel_loop BL cryptBlock_rel
  cryptBlockL_ok cryptTailRest_check tag_rel tag_ok absorb_rel absorb_ok lens_ok mov2_ok polyA_check polyD_check
  lensBlock_check tagIn_check tagIn_ok chunkB_rel keys_rel keys_ok entry_rel entry_ok entry_pub rel_ldrT recv_ok
  recv_check sealEnd_check openEnd_check args_of_seal args_of_open TagSlot prmOf KeysPost TagPost CryptPost PolyPost
  cryptHead_ok cryptHead_check sealPre openPre cryR polyR bytesAt_keep)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ctr rel_ite rel_taint ct_of GcmImpl eval_zero eval_nonzero Others
  lsr_ofNat)
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)
open VG.Impl.AesGcmSiv.AArch64.Stitch

/-! ## Counter mode past the batches -/

/-- `rest` and the number of blocks past the batches. -/
theorem restC_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block (rest ++ ([.lsr .x .x9 .x28 4] : List Instr))) t fun t' => BL p (8 * (p.n / 128)) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * (8 * (p.n / 128))) / 16) := by
  have hn := L.n_lt
  rw [WP.block_append_iff]
  refine WP.mono (rest_ok L E) fun t₁ ⟨x27₁, x28₁, E₁, _, _, _, _⟩ => ?_
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₂ ht₂ => ?_
  have e : 16 * (8 * (p.n / 128)) = 128 * (p.n / 128) := by omega_using []
  refine ⟨⟨by rw [← ht₂]; exact E₁.write (by decide) _, ?_, ?_⟩, ?_⟩
  · rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x27₁, e]
  · rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x28₁, e]
  · rw [← ht₂, e]
    simp [gpr_write, State.read, x28₁, lsr_ofNat _ _ (show p.n - 128 * (p.n / 128) < 2 ^ 64 by omega_using [])]

/-- The whole blocks of counter mode from block `b`, for their registers. -/
theorem cryptMidFrom_ok (v : GcmImpl) {p : Prm} (L : Lay p) {b : Nat} (hb : 16 * b ≤ p.n) {t : State}
    (B : BL p b t) (h9 : t.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * b) / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (Impl.AesGcmSiv.AArch64.cryptBlock v.callees) (.nonzero .x .x9))) t
      (BL p (p.n / 16)) := by
  have hn := L.n_lt
  refine WP.ite (decide ((p.n - 16 * b) / 16 = 0)) (eval_zero h9 (by omega_using [hn])) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (p.n - 16 * b) / 16 = 0 := by simpa using ht
    rw [show p.n / 16 = b by omega_using [hb, h0]]; exact WP.block_nil B
  · have h0 : (p.n - 16 * b) / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ b ≤ j ∧ j < p.n / 16 ∧ BL p j t') ?_
      (p.n / 16 - b) t ⟨b, rfl, Nat.le_refl _, by omega_using [h0], B⟩
    rintro k t' ⟨j, rfl, hbj, hj, B'⟩
    refine WP.mono (cryptBlockL_ok v L (j := j) (by omega_using [hj]) B') fun t'' ⟨B'', x9⟩ => ?_
    have ev := eval_nonzero x9 (by omega_using [hn])
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega_using [he]), he ▸ B''⟩
    · right
      exact ⟨ev.trans (by simp; omega_using [hj, he]), p.n / 16 - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hbj], by omega_using [hj, he], B''⟩

/-- `cryptRest`, in two runs with the same public arguments. -/
theorem cryptRest_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (cryptRest v.callees) TT := by
  have hn := L.n_lt
  have hb : 16 * (8 * (p.n / 128)) ≤ p.n := by omega_using []
  refine rel_seq (rel_env E₁ E₂ [] (by simp) restC_check) (restC_ok L E₁) (restC_ok L E₂)
    fun u₁ u₂ ⟨B₁, x9₁⟩ ⟨B₂, x9₂⟩ => ?_
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega_using [])) (eval_zero x9₂ (by omega_using []))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (cryptMidFrom_ok v L hb B₁ x9₁) (cryptMidFrom_ok v L hb B₂ x9₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : (p.n - 16 * (8 * (p.n / 128))) / 16 ≠ 0 := by simpa using hf
    refine rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ 8 * (p.n / 128) ≤ j ∧ j < p.n / 16 ∧ BL p j t₁ ∧
        BL p j t₂) (fun k t₁ t₂ ⟨j, hk, hbj, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 8 * (p.n / 128))
      ⟨8 * (p.n / 128), rfl, Nat.le_refl _, by omega_using [h0], B₁, B₂⟩
    refine Proof.AesGcmSiv.AArch64.rel_wpQ
      (cryptBlock_rel v L J₁.env J₂.env (j := j) (by omega_using [hj]) J₁.x27 J₂.x27 J₁.x28 J₂.x28)
      (cryptBlockL_ok v L (by omega_using [hj]) J₁) (cryptBlockL_ok v L (by omega_using [hj]) J₂) fun a b ⟨K₁, x9₁⟩ ⟨K₂, x9₂⟩ => ?_
    have ev₁ := eval_nonzero x9₁ (by omega_using [hn])
    have ev₂ := eval_nonzero x9₂ (by omega_using [hn])
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : j + 1 ≠ p.n / 16 := by simp at hc; omega_using [hc]
    exact ⟨p.n / 16 - (j + 1), by omega_using [hk, hj], j + 1, rfl, by omega_using [hbj], by omega_using [hj, he], K₁, K₂⟩
  -- The last bytes.
  have x28₁ : w₁.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₁.x28]; congr 1; omega_using []
  have x28₂ : w₂.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₂.x28]; congr 1; omega_using []
  refine rel_ite (eval_zero x28₁ (by omega_using [])) (eval_zero x28₂ (by omega_using []))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun _ => ?_)
  refine rel_seq (tag_rel v L C₁.env C₂.env (o := 224) (by decide)) (tag_ok v L C₁.env (o := 224) (by decide))
    (tag_ok v L C₂.env (o := 224) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact rel_env T₁.env T₂.env [.x27, .x28] (by simp [T₁.x27, T₂.x27, T₁.x28, T₂.x28, C₁.x27, C₂.x27, C₁.x28, C₂.x28])
    cryptTailRest_check

/-- `cryptHead`: the counter block from the tag. -/
theorem cryptHeadC_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block Impl.AesGcmSiv.AArch64.cryptHead) t fun t₁ => Env p t₁ ∧
      CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
  obtain ⟨t₁, run₁, hm₁, _, _, _, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  exact WP.of_runBlock ⟨t₁, run₁, E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁,
    by rw [hm₁]; exact headMem_ctr _⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt e3 v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [] (by simp) cryptHead_check) (cryptHeadC_ok L E₁) (cryptHeadC_ok L E₂)
    fun u₁ u₂ ⟨F₁, C₁⟩ ⟨F₂, C₂⟩ => ?_
  refine rel_seq (rel_env F₁ F₂ [] (by simp) (ctrB_check e3)) (ctrBatches_ok e3 L F₁ C₁) (ctrBatches_ok e3 L F₂ C₂)
    fun w₁ w₂ B₁ B₂ => ?_
  exact cryptRest_rel v L B₁.env B₂.env

/-! ## Absorbing the data -/

/-- `rest` then `absorb`: the data past its batches absorbed, in two runs
with the same public arguments. -/
theorem restAbs_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block rest) (Impl.AesGcmSiv.AArch64.absorb v.callees)) TT := by
  have hn := L.n_lt
  refine rel_seq (rel_env E₁ E₂ [] (by simp) rest_check) (rest_ok L E₁) (rest_ok L E₂)
    fun c₁ c₂ ⟨x27₁, x28₁, G₁, _, _, _, _⟩ ⟨x27₂, x28₂, G₂, _, _, _, _⟩ => ?_
  have dW : (⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩ : Region).Disjoint
      ⟨p.W, p.Wn⟩ := L.d_w.sub_left (Offset.sub_base p.D (by omega_using []))
  have hc : ∀ {c : State}, Env p c →
      Covers [⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩] (c.rd ++ c.wr) := fun G =>
    Proof.AesGcm.AArch64.covers_left (Proof.AesGcm.AArch64.covers_off G.perm.d (by omega_using []) hn)
  exact absorb_rel v L G₁ G₂ (by omega_using []) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * (p.n / 128)) (by omega_using [hn])]
      have := L.dw; have := Nat.mod_le (p.D.toNat + 128 * (p.n / 128)) (2 ^ 64); omega_arith)
    dW (hc G₁) (hc G₂) x27₁ x27₂ x28₁ x28₂

/-- `polyData`, in two runs with the same public arguments. -/
theorem polyData_rel (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State}
    (E₁ : Env p σ₁) (E₂ : Env p σ₂) : RelCT isa (Eq2 σ₁ σ₂) (polyData e3 v.callees) TT :=
  rel_seq (rel_env E₁ E₂ [] (by simp) (polyB_check e3)) (polyBatches_ok hP gh e3 L E₁)
    (polyBatches_ok hP gh e3 L E₂)
    fun _ _ A₁ A₂ => restAbs_rel v L A₁.env A₂.env

/-- The lengths, in two runs with the same public arguments. -/
theorem lens_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcmSiv.AArch64.lens v.callees) TT := by
  have wL : ∀ {d : State}, Env p d → WP isa (.block Impl.AesGcmSiv.AArch64.lensBlock) d fun t =>
      Env p t ∧ t.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t.gpr .x28 = BitVec.ofNat 64 16 := fun E => by
    have w₀ := E.perm.wW (show 224 + 8 ≤ 1760 by decide)
    have w₈ := E.perm.wW (show 232 + 8 ≤ 1760 by decide)
    refine WP.run ⟨_, by simp only [Impl.AesGcmSiv.AArch64.lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], rfl⟩
      fun t ht => ?_
    subst ht
    refine ⟨E.keep (fun q hq => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write, E.x19], by simp [gpr_write, Proof.AesGcmSiv.AArch64.movz_lit (show 16 < 2 ^ 16 by decide)]⟩
  exact rel_seq (rel_env E₁ E₂ [] (by simp) lensBlock_check) (wL E₁) (wL E₂)
    fun f₁ f₂ ⟨K₁, x27₁, x28₁⟩ ⟨K₂, x27₂, x28₂⟩ => chunkB_rel v L K₁ K₂ x27₁ x27₂ x28₁ x28₂

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State}
    (E₁ : Env p σ₁) (E₂ : Env p σ₂) : RelCT isa (Eq2 σ₁ σ₂) (polyval e3 v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [] (by simp) polyA_check) (mov2_ok E₁ (a := .x23) (b := .x24) (by decide) (by decide))
    (mov2_ok E₂ (a := .x23) (b := .x24) (by decide) (by decide)) fun a₁ a₂ ⟨G₁, a27₁, a28₁, _, rd₁, wr₁⟩
      ⟨G₂, a27₂, a28₂, _, rd₂, wr₂⟩ => ?_
  rw [E₁.x23] at a27₁; rw [E₁.x24] at a28₁; rw [E₂.x23] at a27₂; rw [E₂.x24] at a28₂
  have hc₁ : Covers [⟨p.A, p.al⟩] (a₁.rd ++ a₁.wr) := G₁.perm.aad
  have hc₂ : Covers [⟨p.A, p.al⟩] (a₂.rd ++ a₂.wr) := G₂.perm.aad
  refine rel_seq (absorb_rel v L G₁ G₂ L.al_lt L.aw L.a_w hc₁ hc₂ a27₁ a27₂ a28₁ a28₂)
    (absorb_ok v L G₁ hc₁ L.al_lt L.aw L.a_w a27₁ a28₁) (absorb_ok v L G₂ hc₂ L.al_lt L.aw L.a_w a27₂ a28₂)
    fun b₁ b₂ B₁ B₂ => ?_
  refine rel_seq (polyData_rel hP gh e3 v L B₁.env B₂.env) (polyData_ok hP gh e3 v L B₁.env)
    (polyData_ok hP gh e3 v L B₂.env) fun d₁ d₂ D₁ D₂ => ?_
  exact rel_seq (lens_rel v L D₁.env D₂.env) (lens_ok v L D₁.env) (lens_ok v L D₂.env) fun e₁ e₂ F₁ F₂ =>
    rel_env F₁.env F₂.env [] (by simp) tagIn_check

/-! ## Decryption -/

open VG.Proof.AesGcmSiv.AArch64 (key_cryR absR) in
/-- The key schedule, after code that writes only what counter mode and the
batches' POLYVAL write. -/
theorem ciph_cryAbs {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (cryR p.Wn p.W p.D p.n ++ absR p.W) m m') :
    Spec.GcmSiv.ctxCiph m' (p.W + BitVec.ofNat 64 240) p.R = Spec.GcmSiv.ctxCiph m (p.W + BitVec.ofNat 64 240) p.R := by
  have hR := L.rounds_le
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])]
  rcases List.mem_append.mp hr with hr | hr
  · exact (key_cryR L r hr).sub_left (Region.sub_prefix hR)
  · simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inr (by omega_using [])) (by omega_using [hR]) (by decide)
    · exact L.w_w (.inl (by omega_using [hR])) (by omega_using [hR]) (by decide)

/-- `openData`, in two runs with the same public arguments. -/
theorem openData_rel (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State}
    (E₁ : Env p σ₁) (E₂ : Env p σ₂) : RelCT isa (Eq2 σ₁ σ₂) (openData e3 v.callees) TT := by
  have wR : ∀ {u w : State} {icb : List Byte}, OBatchPost p (Spec.GcmSiv.ctxCiph u.mem (p.W + BitVec.ofNat 64 240) p.R)
      icb (bytesAt u.mem p.D p.n) u w → WP isa (cryptRest v.callees) w (Env p) := fun B =>
    WP.mono (cryptRest_ok v L B.env (Proof.Cmac.bytesAt_length _ _ _) B.ctr B.data (ciph_cryAbs L B.frame))
      fun _ T => T.env
  refine rel_seq (rel_env E₁ E₂ [] (by simp) cryptHead_check) (cryptHeadC_ok L E₁) (cryptHeadC_ok L E₂)
    fun u₁ u₂ ⟨F₁, C₁⟩ ⟨F₂, C₂⟩ => ?_
  refine rel_seq (rel_env F₁ F₂ [] (by simp) (openB_check e3)) (openBatches_ok hP gh e3 L F₁ C₁)
    (openBatches_ok hP gh e3 L F₂ C₂) fun w₁ w₂ B₁ B₂ => ?_
  exact rel_seq (cryptRest_rel v L B₁.env B₂.env) (wR B₁) (wR B₂) fun _ _ G₁ G₂ => restAbs_rel v L G₁ G₂

/-! ## The functions -/

theorem seal_ct (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    ConstantTime isa Proof.AesGcmSiv.AArch64.sealAArch64.pre Proof.AesGcmSiv.AArch64.sealAArch64.pub
      («seal» e3 v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -, hA₁⟩ := args_of_seal h₁
  obtain ⟨-, P₂, -, hA₂⟩ := args_of_seal h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  refine rel_seq (keys_rel v L E₁ E₂) (keys_ok v L E₁) (keys_ok v L E₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (polyval_rel hP gh e3 v L K₁.env K₂.env) (polyval_ok hP gh e3 v L K₁.env K₁.hkey K₁.acc)
    (polyval_ok hP gh e3 v L K₂.env K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  refine rel_seq (tag_rel v L P₁.env P₂.env (o := 0) (by decide)) (tag_ok v L P₁.env (o := 0) (by decide))
    (tag_ok v L P₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  refine rel_seq (crypt_rel e3 v L T₁.env T₂.env) (crypt_ok e3 v L T₁.env) (crypt_ok e3 v L T₂.env)
    fun d₁ d₂ C₁ C₂ => ?_
  have sl : ∀ {τ a b c d : State}, TagSlot (prmOf σ₁) τ.mem → KeysPost (prmOf σ₁) τ a → PolyPost (prmOf σ₁) a b →
      TagPost (prmOf σ₁) 0 b c → CryptPost (prmOf σ₁) c d → TagSlot (prmOf σ₁) d.mem := fun S K P T C =>
    (((S.frame K.frame (by disj_tac L)).frame P.frame (by disj_tac L)).frame T.frame (by disj_tac L)).frame C.frame
      (by disj_tac L)
  exact rel_ldrT (l := Impl.AesGcmSiv.AArch64.tagOut.tail ++ Impl.AesGcm.AArch64.restore) C₁.env C₂.env
    (sl S₁ K₁ P₁ T₁ C₁) (sl S₂ K₂ P₂ T₂ C₂) sealEnd_check

theorem open_ct (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    ConstantTime isa Proof.AesGcmSiv.AArch64.openAArch64.pre Proof.AesGcmSiv.AArch64.openAArch64.pub
      («open» e3 v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, hA₁⟩ := args_of_open h₁
  obtain ⟨-, P₂, hA₂⟩ := args_of_open h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  have wr : ∀ {τ : State}, Env (prmOf σ₁) τ → TagSlot (prmOf σ₁) τ.mem →
      WP isa (.block Impl.AesGcmSiv.AArch64.recv) τ (Env (prmOf σ₁)) :=
    fun E S => by
      obtain ⟨t, run, -, -, -, ho, sp, rd, wr⟩ := recv_ok L E S
      exact WP.of_runBlock ⟨t, run, E.keep (fun r hr => ho r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr⟩
  refine rel_seq (rel_ldrT (l := Impl.AesGcmSiv.AArch64.recv.tail) E₁ E₂ S₁ S₂ recv_check) (wr E₁ S₁) (wr E₂ S₂)
    fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine rel_seq (keys_rel v L R₁ R₂) (keys_ok v L R₁) (keys_ok v L R₂) fun a₁ a₂ K₁ K₂ => ?_
  -- The additional data.
  refine rel_seq (rel_env K₁.env K₂.env [] (by simp) polyA_check)
    (mov2_ok K₁.env (a := .x23) (b := .x24) (by decide) (by decide))
    (mov2_ok K₂.env (a := .x23) (b := .x24) (by decide) (by decide)) fun b₁ b₂ ⟨G₁, b27₁, b28₁, _⟩
      ⟨G₂, b27₂, b28₂, _⟩ => ?_
  rw [K₁.env.x23] at b27₁; rw [K₁.env.x24] at b28₁; rw [K₂.env.x23] at b27₂; rw [K₂.env.x24] at b28₂
  have hc₁ : Covers [⟨(prmOf σ₁).A, (prmOf σ₁).al⟩] (b₁.rd ++ b₁.wr) := G₁.perm.aad
  have hc₂ : Covers [⟨(prmOf σ₁).A, (prmOf σ₁).al⟩] (b₂.rd ++ b₂.wr) := G₂.perm.aad
  refine rel_seq (absorb_rel v L G₁ G₂ L.al_lt L.aw L.a_w hc₁ hc₂ b27₁ b27₂ b28₁ b28₂)
    (absorb_ok v L G₁ hc₁ L.al_lt L.aw L.a_w b27₁ b28₁) (absorb_ok v L G₂ hc₂ L.al_lt L.aw L.a_w b27₂ b28₂)
    fun c₁ c₂ B₁ B₂ => ?_
  -- The data, decrypted and absorbed.
  refine rel_seq (openData_rel hP gh e3 v L B₁.env B₂.env) (openData_ok hP gh e3 v L B₁.env)
    (openData_ok hP gh e3 v L B₂.env) fun d₁ d₂ O₁ O₂ => ?_
  -- The lengths and the tag input.
  refine rel_seq (lens_rel v L O₁.env O₂.env) (lens_ok v L O₁.env) (lens_ok v L O₂.env) fun e₁ e₂ D₁ D₂ => ?_
  have wT : ∀ {d : State}, Env (prmOf σ₁) d →
      WP isa (.block Impl.AesGcmSiv.AArch64.tagIn) d (Env (prmOf σ₁)) := fun E => by
    obtain ⟨t, run, -, ho, sp, rd, wr⟩ := tagIn_ok E
    exact WP.of_runBlock ⟨t, run, E.keep (fun r hr => ho r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr⟩
  refine rel_seq (rel_env D₁.env D₂.env [] (by simp) tagIn_check) (wT D₁.env) (wT D₂.env) fun f₁ f₂ T₁ T₂ => ?_
  -- Its tag at `W + 224`, the comparison and the mask.
  exact rel_seq (tag_rel v L T₁ T₂ (o := 224) (by decide)) (tag_ok v L T₁ (o := 224) (by decide))
    (tag_ok v L T₂ (o := 224) (by decide)) fun _ _ X₁ X₂ => rel_env X₁.env X₂.env [] (by simp) openEnd_check

end VG.Proof.AesGcmSiv.AArch64.Stitch

end

end


/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: `Verified`

Untrusted: everything here is checked by Lean. As
`Proof/AesGcmSiv/AArch64/Verified.lean`, for the interleaved `seal` and
`open` (`Impl.AesGcmSiv.AArch64.Stitch`), which keep `v8`–`v15` too; and,
for `Generic/AesGcm/AArch64/AesGcmSiv.lean`, the code of each function: the
interleaved one if the CPUs have PMULL (`v.gh.pmull`), with `eor3` if they
have FEAT_SHA3 too (`v.stitch`), and the other otherwise.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.Impl.AesGcmSiv.AArch64
open VG.Proof.AesGcm.AArch64 (GcmImpl)
open VG.Proof.AesGcmSiv.AArch64 (tagInput_eq sealSat openSat sealFrameSat_pre openFrameSat_pre sealAArch64
  openAArch64 oneLay onePub args rounds openResult openPost sealPre openPre)
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-! ## v8–v15 -/

theorem seal_keepsV (e3 : Bool) (v : GcmImpl) : (Stitch.«seal» e3 v.callees).allInstrs keepsV = true := by
  cases e3 <;>
  simp only [Stitch.«seal», keys, derive, expand, Stitch.polyval, Stitch.polyData, Stitch.ifBatch, absorb, absTail,
    absTailPre, chunk, chunkPre, chunkLen, revLoop, lens, tag, tagOut, Stitch.crypt, Stitch.cryptRest, cryptBlock,
    cryptTail, callCtr, callKey, callGh, Impl.AesGcm.AArch64.copyLoop, Impl.AesGcm.AArch64.xorLoop,
    Stitch.ghLoop, Stitch.ctrLoop, Impl.Gcm.AArch64.Stitch.byRounds, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  all_goals decide +kernel

theorem open_keepsV (e3 : Bool) (v : GcmImpl) : (Stitch.«open» e3 v.callees).allInstrs keepsV = true := by
  cases e3 <;>
  simp only [Stitch.«open», keys, derive, expand, Stitch.openData, Stitch.ifBatch, absorb, absTail, absTailPre, chunk,
    chunkPre, chunkLen, revLoop, lens, tag, recv, Stitch.cryptRest, cryptBlock, cryptTail, mask, callCtr, callKey,
    callGh, Impl.AesGcm.AArch64.copyLoop, Impl.AesGcm.AArch64.xorLoop, Stitch.openLoop,
    Impl.Gcm.AArch64.Stitch.byRounds, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  all_goals decide +kernel

/-! ## Correctness -/

theorem seal_correct (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa (Stitch.«seal» e3 v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp hP gh e3 v tagInput_eq hs) (seal_keepsV e3 v)

theorem open_correct (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa (Stitch.«open» e3 v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp hP gh e3 v tagInput_eq hs) (open_keepsV e3 v)

/-! ## The shared contracts, with the working space as an argument -/

theorem seal_verified (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    Verified AArch64.target (Stitch.«seal» e3 v.callees) (Proof.AesGcmSiv.sealScratchContract AArch64.abi 476) :=
  Verified.of_correct (seal_correct hP gh e3 v) (seal_ct hP gh e3 v) (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Proof.AesGcmSiv.sealRoundsPost, sealAArch64, sealPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
      AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat] using sealSat)

theorem open_verified (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    Verified AArch64.target (Stitch.«open» e3 v.callees) (Proof.AesGcmSiv.openScratchContract AArch64.abi 476) :=
  Verified.of_correct (open_correct hP gh e3 v) (open_ct hP gh e3 v)
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
          openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
          AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openAArch64, openResult, openPost,
        openPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat] using openSat }

theorem seal_framed (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.«seal» e3 v.callees))
      (Proof.AesGcmSiv.sealRoundsContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.sealPre AArch64.abi.ptrBits)
    (post := Proof.AesGcmSiv.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (seal_verified hP gh e3 v) (by decide) (by decide) (sealPre_local _) (sealPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre

theorem open_framed (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.«open» e3 v.callees))
      (Proof.AesGcmSiv.openRoundsContract AArch64.abi 3824) :=
  AArch64.Verified.stackArgScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 476) (pre := Spec.GcmSiv.openPre AArch64.abi.ptrBits)
    (post := Proof.AesGcmSiv.openRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 3824)
    (leak := some (Spec.GcmSiv.openLeak AArch64.abi.ptrBits))
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified hP gh e3 v)) (by decide) (by decide) (openPre_local _)
    (openPost_local _) (fun vs m m₁ m₂ r hl _ => Proof.AesGcmSiv.openPostOut_local _ vs m m₁ m₂ r hl) openFrameSat_pre
    (hleak := openLeak_local _)

/-! ## The code of each function -/

/-- `vg_aes_gcm_siv_seal`: interleaved if `v.gh.pmull`, with `eor3` if `v.stitch`. -/
def sealCode (v : GcmImpl) : Prog isa :=
  if v.gh.pmull then Stitch.«seal» v.stitch v.callees else «seal» v.callees

/-- `vg_aes_gcm_siv_open`: interleaved if `v.gh.pmull`, with `eor3` if `v.stitch`. -/
def openCode (v : GcmImpl) : Prog isa :=
  if v.gh.pmull then Stitch.«open» v.stitch v.callees else «open» v.callees

theorem sealCode_framed (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (sealCode v))
      (Proof.AesGcmSiv.sealRoundsContract AArch64.abi 3824) := by
  unfold sealCode
  split
  · exact seal_framed hP gh v.stitch v
  · exact Proof.AesGcmSiv.AArch64.seal_framed v

theorem openCode_framed (hP : PrepPow) (gh : Gh8Ok) (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (openCode v))
      (Proof.AesGcmSiv.openRoundsContract AArch64.abi 3824) := by
  unfold openCode
  split
  · exact open_framed hP gh v.stitch v
  · exact Proof.AesGcmSiv.AArch64.open_framed v

end VG.Proof.AesGcmSiv.AArch64.Stitch
