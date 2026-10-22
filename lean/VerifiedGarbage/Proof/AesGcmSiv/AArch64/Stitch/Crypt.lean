module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Loops
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Poly
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

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
      hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega,
      show 8 * j + i < 32 by omega, show ¬ 8 * j + i < 0 by omega]
    simp
  · rw [ite_eq_right h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega,
      show ¬ 8 * j + i < 32 by omega, show ¬ 8 * j + i < 0 by omega]
    simp [BitVec.getLsbD_of_ge w (8 * j + i) (by omega)]

/-- The loops' counter block `q` is RFC 8452's, of the counter block at `W + 96`. -/
theorem st_cv {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) (q : Nat) :
    st (σ.cv q) = Vector.ofFn fun k => (Spec.GcmSiv.counterBlock icb q).getD k 0 := by
  refine st_ext fun k hk => ?_
  rw [getD_st _ hk, Proof.Aes.AArch64.Aese.getD_ofFn hk, Ctx.cv, vbyte_setLane32_0 _ _ hk,
    GcmSiv.counterBlock_word]
  dsimp only
  have hw : σ.c0 + BitVec.ofNat 32 q = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + q) := by
    show σ.m₀.readW (σ.W + BitVec.ofNat 64 96) 32 + _ = _
    rw [C.word, Nat.add_zero, ← BitVec.ofNat_add]
  by_cases h : k < 4
  · rw [ite_eq_left h, hw, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [Proof.Cmac.length_le4]; exact h)]
    simp [Proof.Cmac.le4, h]
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [Proof.Cmac.length_le4]; omega), Proof.Cmac.length_le4,
      ← List.getD_eq_getElem?_getD, vbyte_readW _ _ hk, ← C.rest,
      Proof.Cmac.getD_bytesAt _ _ (by omega), Offset.add_add, Offset.add_add, show 100 + (k - 4) = 96 + k by omega]
    rfl

/-- The loops' keystream is RFC 8452's. -/
theorem ks_eq {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) (i : Nat) :
    σ.ks i = (GcmSiv.ksBlock (Spec.GcmSiv.ctxCiph σ.m₀ σ.K σ.nr) icb (i / 16)).getD (i % 16) 0 := by
  simp only [Ctx.ks, GcmSiv.ksBlock, Spec.GcmSiv.ctxCiph, Spec.GcmSiv.aesWith, st_cv C]
  have hi : i % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem hi, Option.getD_some]
  simp [Vector.getD, hi]

/-- The data after the batches' counter mode: `ctrPart` of it. -/
theorem ctrPart_of_dataInv {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) {m : Mem} {n : Nat}
    {x : List Byte} (hx : bytesAt σ.m₀ σ.D n = x)
    (hd : DataInv σ.m₀ m σ.D (8 * σ.nb) (8 * σ.nb) σ.ks)
    (hf : ∀ q < n, 128 * σ.nb ≤ q → m (σ.D + BitVec.ofNat 64 q) = σ.m₀ (σ.D + BitVec.ofNat 64 q)) :
    bytesAt m σ.D n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph σ.m₀ σ.K σ.nr) icb x (128 * σ.nb) := by
  have hxl : x.length = n := by rw [← hx, Proof.AesGcm.AArch64.length_bytesAt]
  refine GcmSiv.ext_getD (by rw [Proof.AesGcm.AArch64.length_bytesAt, GcmSiv.length_ctrPart, hxl]) fun q hq => ?_
  rw [Proof.AesGcm.AArch64.length_bytesAt] at hq
  rw [Proof.Cmac.getD_bytesAt _ _ hq, GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; exact hq), ← hx,
    Proof.Cmac.getD_bytesAt _ _ hq]
  by_cases h : q < 128 * σ.nb
  · rw [ite_eq_left h, hd q (by omega), ite_eq_left (by omega), ks_eq C]
  · rw [ite_eq_right h, hf q hq (by omega)]

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
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_ok v L P.env hxl (j := j) (by omega) P.x27 P.x28 P.ctr P.data hc') fun t'' Q => ?_
  have P' : BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.x27, Q.x28, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := Proof.AesGcm.AArch64.eval_nonzero Q.x9 (by have := L.n_lt; omega)
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, P'⟩

/-! ## The batches -/

open VG.Proof.AesGcmSiv.AArch64 (cryR) in
/-- What counter mode of the batches leaves, from `t`. -/
structure BatchPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ctr : CtrSt p.W icb (8 * (p.n / 128)) t'.mem
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x (128 * (p.n / 128))
  frame : Frame (cryR p.W p.D p.n) t.mem t'.mem

/-- `ctrSetup ++ batches`: the counter's word, the key schedule and the batches. -/
theorem ctrSetup_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa (ctrSetup ++ batches) t = some t₁ ∧
      t₁.read .w .x10 = t.mem.readW (p.W + BitVec.ofNat 64 Impl.AesGcmSiv.AArch64.cbO) 32 ∧
      t₁.gpr .x15 = p.W + BitVec.ofNat 64 240 ∧ t₁.gpr .x9 = p.D + BitVec.ofNat 64 (128 * 0) ∧
      t₁.gpr .x11 = BitVec.ofNat 64 (p.n / 128 - 0) ∧
      Others [.x9, .x10, .x11, .x15] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have c₀ := E.perm.wR (show 96 + 4 ≤ 3808 by decide)
  refine ⟨_, by simp only [ctrSetup, batches, List.cons_append, List.nil_append]; grun [E.x19, c₀], ?_, ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
  · simp [State.read, gpr_write, E.x19, setWidth_rt32, read4_readW]; rfl
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x25]
  · simp [gpr_write, E.x26, lsr_ofNat _ _ L.n_lt]

theorem ctrBatch_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {icb : List Byte}
    (C : CtrSt p.W icb 0 t.mem) (hnb : 1 ≤ p.n / 128) :
    WP isa (.seq (.block (ctrSetup ++ batches)) (.seq (byRounds ctrLoop) (.block ctrFinish))) t
      (BatchPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R) icb (bytesAt t.mem p.D p.n) t) := by
  have hn := L.n_lt
  have hww := L.ww
  obtain ⟨t₁, run₁, x10₁, x15₁, x9₁, x11₁, o₁, m₁, sp₁, rd₁, wr₁⟩ := ctrSetup_ok L E
  have E₁ : Env p t₁ := E.keep (fun r hr => o₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, 0, t.mem, t.rd, t.wr⟩
  have hp : KPreC σ := {
    rounds := by rcases L.rounds with h | h <;> simp [σ, h]
    nb1 := hnb
    n16 := by show 128 * (p.n / 128) < 2 ^ 64; omega
    k_in := by
      show InRegions (t.rd ++ t.wr) (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))
      exact E.perm.wR (by rcases L.rounds with h | h <;> rw [h] <;> decide)
    c_in := E.perm.wR (by decide)
    d_in := by
      show InRegions t.wr p.D (128 * (p.n / 128))
      exact E.perm.d _ _ ⟨⟨p.D, p.n⟩, List.mem_singleton_self _, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega⟩
    d_k := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩
      exact (L.d_w' (d := 240) (k := 16 * (p.R + 1)) (by rcases L.rounds with h | h <;> rw [h] <;> decide)).sub_left
        (Region.sub_prefix (by omega))
    d_c := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega))
    wrap_c := by show p.W.toNat + 96 + 16 ≤ 2 ^ 64; omega
    wrap_k := by
      show (p.W + BitVec.ofNat 64 240).toNat + 16 * (p.R + 1) ≤ 2 ^ 64
      rw [L.toNat_W (by decide)]; rcases L.rounds with h | h <;> rw [h] <;> omega }
  have hI : CInv σ t₁ 0 0 t₁ := {
    le := Nat.zero_le _
    x9 := x9₁
    x10 := by rw [x10₁, Nat.mul_zero, BitVec.add_zero]
    x11 := x11₁
    gpr := fun _ _ => rfl
    data := fun i _ => by
      rw [m₁, ite_eq_right (by omega)]; show t.mem _ = t.mem _ ^^^ 0; simp
    frame := by rw [m₁]; exact Frame.refl _ _
    sp := rfl
    rd := rfl
    wr := rfl }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (byRounds_ok (P := CInv σ t₁ 0 0) L.rounds3 E₁.x22
    (fun s' hg _ hm hsp hrd hwr => hI.of_x1314 hg hm hsp hrd hwr)
    (fun s hs => ctrLoop_ok hp (by rw [E₁.x19]) x15₁ (by rw [rd₁, wr₁]) wr₁ hs)) fun t₂ I => ?_
  -- The counter's word stored back.
  have E₂ : Env p t₂ := E₁.keep (fun r hr => I.gpr r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (by rw [I.sp]) I.rd I.wr
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 3808 by decide)
  have hf₂ : Frame [σ.dR] t.mem t₂.mem := I.frame
  have dDR : ∀ {d k : Nat}, d + k ≤ 3808 → ∀ q ∈ [σ.dR], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ((L.d_w' h).sub_left (Region.sub_prefix (by show 128 * (p.n / 128) ≤ p.n; omega))).symm
  have r₂ : bytesAt t₂.mem (p.W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.AArch64.bytesAt_frame hf₂ (dDR (by decide)) (by decide)
  have fw : ∀ v : BitVec 32, Frame [⟨p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem
      (t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hmem : ∀ v : BitVec 32, t₂.mem.write (p.W + BitVec.ofNat 64 96) 4 v =
      t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v := fun v => by
    simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  have hd₂ : bytesAt t₂.mem p.D p.n =
      GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R) icb (bytesAt t.mem p.D p.n)
        (128 * (p.n / 128)) :=
    ctrPart_of_dataInv (σ := σ) C rfl I.data fun q hq hq' =>
      frame_outside (a := 0) (n := 128 * (p.n / 128)) hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact .inl (by show (⟨p.D, 128 * (p.n / 128)⟩ : Region) = ⟨p.D + BitVec.ofNat 64 0, _⟩; simp))
        hn (by omega) q hq (.inr (by rw [Nat.zero_add]; exact hq'))
  refine WP.run ⟨_, by simp only [ctrFinish]; grun [E₂.x19, c₁], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  refine ⟨E₂.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) rfl rfl rfl,
    by simp only [rd_write]; rw [I.rd, rd₁], by simp only [wr_write]; rw [I.wr, wr₁], ?_, ?_, ?_⟩
  · simp only [mem_write]
    refine ⟨?_, ?_⟩
    · rw [hmem, Mem.readW_writeW_self32]
      have h := I.x10
      simp only [State.read, Size.bits] at h
      rw [h]
      show t.mem.readW (p.W + BitVec.ofNat 64 96) 32 + _ = _
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
    exact ⟨⟨p.D, p.n⟩, by simp, Region.sub_prefix (by show 128 * (p.n / 128) ≤ p.n; omega)⟩

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
  have hcl : ∀ y, (ciph y).length = 16 := fun y => by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  rw [cryptRest, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (rest_ok L E) fun t₁ ⟨x27₁, x28₁, E₁, _, m₁, rd₁, wr₁⟩ => ?_
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₂ ht₂ => ?_
  have hlt : p.n - 128 * (p.n / 128) < 2 ^ 64 := by omega
  have x9₂ : t₂.gpr .x9 = BitVec.ofNat 64 ((p.n - 128 * (p.n / 128)) / 16) := by
    rw [← ht₂]; simp [gpr_write, State.read, x28₁, lsr_ofNat _ _ hlt]
  have E₂ : Env p t₂ := by rw [← ht₂]; exact E₁.write (by decide) _
  have x27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * (8 * (p.n / 128))) := by
    rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x27₁, show 16 * (8 * (p.n / 128)) = 128 * (p.n / 128) by omega]
  have x28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * (8 * (p.n / 128))) := by
    rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x28₁, show 16 * (8 * (p.n / 128)) = 128 * (p.n / 128) by omega]
  have m₂ : t₂.mem = t.mem := by rw [← ht₂, mem_write, m₁]
  have rd₂ : t₂.rd = t.rd := by rw [← ht₂, rd_write, rd₁]
  have wr₂ : t₂.wr = t.wr := by rw [← ht₂, wr_write, wr₁]
  rw [← m₂] at C hx hc
  -- The whole blocks.
  have hmid : WP isa (.ite (.zero .x .x9) (.block []) (.loop (Impl.AesGcmSiv.AArch64.cryptBlock v.callees)
      (.nonzero .x .x9))) t₂ (BlocksPost p ciph icb x (p.n / 16) t₂) := by
    refine WP.ite (decide ((p.n - 128 * (p.n / 128)) / 16 = 0)) (eval_zero x9₂ (by omega)) (fun h => ?_) (fun h => ?_)
    · have h0 : (p.n - 128 * (p.n / 128)) / 16 = 0 := by simpa using h
      have e : p.n / 16 = 8 * (p.n / 128) := by omega
      refine WP.block_nil ?_
      rw [e]
      exact ⟨E₂, rfl, rfl, x27₂, x28₂, C, by rw [hx]; congr 1; omega, Frame.refl _ _⟩
    · have h0 : (p.n - 128 * (p.n / 128)) / 16 ≠ 0 := by simpa using h
      exact blocksFrom_ok v L E₂ hxl (by omega) x27₂ x28₂ C (by rw [hx]; congr 1; omega) hc
  refine WP.seq (WP.mono hmid fun t₃ B => ?_)
  have x28₃ : t₃.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [B.x28]; congr 1; omega
  refine WP.ite (decide (p.n % 16 = 0)) (eval_zero x28₃ (by omega)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨B.env, by rw [B.rd, rd₂], by rw [B.wr, wr₂], ?_, by have f := B.frame; rwa [m₂] at f⟩
    rw [B.data, show 16 * (p.n / 16) = p.n by omega]
  · have h0 : p.n % 16 ≠ 0 := by simpa using h
    have hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
      rw [ciph_cryR L B.frame, hc]
    refine WP.mono (cryptTail_ok v L B.env hxl (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)
      B.x27 x28₃ B.ctr B.data hc₃) fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, B.rd, rd₂], by rw [T.wr, B.wr, wr₂], T.data, ?_⟩
    have f := B.frame.trans T.frame
    rwa [m₂] at f

/-! ## Counter mode -/

open VG.Proof.AesGcmSiv.AArch64 (CryptPost cryptHead_ok headMem cryR) in
theorem crypt_ok (v : Proof.AesGcm.AArch64.GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (crypt v.callees) t (CryptPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, _, _, _, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem p.D p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
      rw [Proof.AesGcm.AArch64.add_ofNat_assoc]]
    exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁.mem p.D p.n = bytesAt t.mem p.D p.n :=
    Proof.AesGcm.AArch64.bytesAt_frame f₁ dD (Nat.le_of_lt hn)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hicb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16) := by
    rw [hm₁, headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
        rw [Proof.AesGcm.AArch64.add_ofNat_assoc], Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words,
      Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, Proof.AesGcm.AArch64.add_ofNat_assoc] at h4
  have C₀ : CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fC : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ cryR p.W p.D p.n, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The batches.
  have hb : WP isa (ifBatch (.seq (.block (ctrSetup ++ batches)) (.seq (byRounds ctrLoop) (.block ctrFinish)))) t₁
      (BatchPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n) t₁) := by
    unfold ifBatch
    refine WP.seq (WP.mono (batchHead_ok L E₁) fun t₂ ⟨x9₂, E₂, m₂, rd₂, wr₂⟩ => ?_)
    refine WP.ite (decide (p.n / 128 = 0)) (eval_zero x9₂ (by omega)) (fun h => ?_) (fun h => ?_)
    · have h0 : p.n / 128 = 0 := by simpa using h
      refine WP.block_nil ⟨E₂, rd₂, wr₂, ?_, ?_, by rw [m₂]; exact Frame.refl _ _⟩
      · rw [h0, m₂]; exact C₀
      · rw [h0, m₂, Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁]
    · have h1 : 1 ≤ p.n / 128 := by simp at h; omega
      rw [← m₂] at C₀
      refine WP.mono (ctrBatch_ok L E₂ C₀ h1) fun t₃ B => ?_
      rw [m₂, hc₁, hx₁] at B
      exact ⟨B.env, by rw [B.rd, rd₂], by rw [B.wr, wr₂], B.ctr, B.data, by rw [← m₂]; exact B.frame⟩
  refine WP.seq (WP.mono hb fun t₂ B => ?_)
  have hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    rw [VG.Proof.AesGcmSiv.AArch64.ciph_cryR L B.frame, hc₁]
  refine WP.mono (cryptRest_ok v L B.env hxl B.ctr B.data hc₂) fun t₃ T => ?_
  refine ⟨T.env, by rw [T.rd, B.rd, rd₁], by rw [T.wr, B.wr, wr₁], ((f₁.sub fC).trans B.frame).trans T.frame, ?_⟩
  rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.AArch64.Stitch
