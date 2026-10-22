module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Poly
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Stream

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
  have c₀ := E.perm.wR (show 96 + 4 ≤ 3808 by decide)
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
  frame : Frame (cryR p.W p.D p.n ++ absR p.W) t.mem t'.mem
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
  have E₁ : Env p s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by simp at hr; rcases hr with h|h|h|h|h|h|h|h <;> subst h <;> decide)) sp₁ rd₁ wr₁
  rw [E.x19] at tok₁ f₁
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, x10₂, x15₂, o₂, m₂, sp₂, rd₂, wr₂⟩ := ctrSet_ok E₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have E₂ : Env p s₂ := E₁.keep (fun r hr => o₂ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  refine WP.mono (ghPre_ok L E₂) fun s₃ ⟨x9₃, x11₃, c₃, y₃, o₃, m₃, sp₃, rd₃, wr₃⟩ => ?_
  have E₃ : Env p s₃ := E₂.keep (fun r hr => o₃ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have m₁₃ : s₃.mem = s₁.mem := by rw [m₃, m₂]
  -- What the table changed.
  have dT : ∀ {d k : Nat}, d + k ≤ 480 → ∀ r ∈ [tblR p.W], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by show d + k ≤ 480; exact h)) (by omega) (by decide)
  have dTD : ∀ r ∈ [tblR p.W], (⟨p.D, p.n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)
  have C₃ : CtrSt p.W icb 0 s₃.mem := by rw [m₁₃]; exact ctrSt_frame C f₁ (dT (by decide))
  have hY : blockAt s₂.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) := by
    rw [m₂]; exact Proof.AesGcm.AArch64.blockAt_frame f₁ (dT (by decide))
  have hc₃ : Spec.GcmSiv.ctxCiph s₃.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    rw [m₁₃]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => (dT (k := 240) (by decide) r hr).sub_left
      (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega)]
  have hx₃ : bytesAt s₃.mem p.D p.n = bytesAt t.mem p.D p.n := by
    rw [m₁₃]; exact Proof.AesGcm.AArch64.bytesAt_frame f₁ dTD (Nat.le_of_lt hn)
  -- The context of the loop.
  let σ : Ctx := ⟨p.W, p.W + BitVec.ofNat 64 240, p.D, p.R, p.n / 128, blockAt t.mem (p.W + BitVec.ofNat 64 64),
    s₃.mem, t.rd, t.wr⟩
  have hp : KPre σ := {
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
    t_in := E.perm.wR (by decide)
    d_k := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩
      exact (L.d_w' (d := 240) (k := 16 * (p.R + 1)) (by rcases L.rounds with h | h <;> rw [h] <;> decide)).sub_left
        (Region.sub_prefix (by omega))
    d_c := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega))
    d_t := by
      show (⟨p.D, 128 * (p.n / 128)⟩ : Region).Disjoint _
      exact (L.d_w' (by decide)).sub_left (Region.sub_prefix (by omega))
    wrap_t := by show p.W.toNat + 480 + 192 ≤ 2 ^ 64; omega
    wrap_c := by show p.W.toNat + 96 + 16 ≤ 2 ^ 64; omega
    wrap_k := by
      show (p.W + BitVec.ofNat 64 240).toNat + 16 * (p.R + 1) ≤ 2 ^ 64
      rw [L.toNat_W (by decide)]; rcases L.rounds with h | h <;> rw [h] <;> omega
    tbl := by show TblOk s₃.mem p.W _; rw [m₁₃]; exact tok₁ }
  have hI : CInv σ s₃ 0 0 s₃ := {
    le := Nat.zero_le _
    x9 := x9₃
    x10 := by
      simp only [State.read] at x10₂ ⊢
      rw [o₃ _ (by decide), x10₂, Nat.mul_zero, BitVec.add_zero]
      show _ = s₃.mem.readW _ 32
      rw [m₃, m₂]
    x11 := x11₃
    gpr := fun _ _ => rfl
    data := fun i _ => by rw [ite_eq_right (by omega)]; show s₃.mem _ = s₃.mem _ ^^^ 0; simp
    frame := Frame.refl _ _
    sp := rfl
    rd := rfl
    wr := rfl }
  have x19₃ : s₃.gpr .x19 = p.W := E₃.x19
  have x15₃ : s₃.gpr .x15 = p.W + BitVec.ofNat 64 240 := by rw [o₃ _ (by decide), x15₂]
  refine WP.seq (WP.mono (byRounds_ok (P := fun s' => CInv σ s₃ 0 0 s' ∧ s'.v = s₃.v) L.rounds3 E₃.x22
    (fun s' hg hv hm hsp hrd hwr => ⟨hI.of_x1314 hg hm hsp hrd hwr, hv⟩)
    (fun s ⟨hs, hv⟩ => openLoop_ok hp gh (y := blockAt t.mem (p.W + BitVec.ofNat 64 80)) x19₃ x15₃
      (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]) (by rw [wr₃, wr₂, wr₁]) e3 hs (by rw [hv, y₃, hY]) (by rw [hv]; exact c₃)))
    fun s₄ O => ?_)
  -- The counter's word and `Y` stored back.
  have E₄ : Env p s₄ := E₃.keep (fun r hr => O.ci.gpr r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) O.ci.sp O.ci.rd O.ci.wr
  rw [WP.block_append_iff]
  refine WP.mono (ctrFinish_ok L C₃ O.ci E₄) fun s₅ ⟨E₅, rd₅, wr₅, v₅, C₅, d₅, f₅, fw₅⟩ => ?_
  refine WP.mono (ghFinish_ok (p := p) (s := s₅) E₅.x19 (by rw [wr₅, O.ci.wr, wr₃, wr₂, wr₁]; exact E.perm.wW (by decide)))
    fun s₆ ⟨b₆, f₆, g₆, sp₆, rd₆, wr₆⟩ => ?_
  have dY : ∀ {d k : Nat}, (96 ≤ d ∨ d + k ≤ 80) → d + k ≤ 3808 →
      ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 80, 16⟩ : Region)], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases h₁ with h | h
      · exact L.w_w (.inr (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
  have dYD : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 80, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)
  refine ⟨E₅.keep (fun r _ => by rw [g₆]) sp₆ rd₆ wr₆, by rw [rd₆, rd₅, O.ci.rd, rd₃, rd₂, rd₁],
    by rw [wr₆, wr₅, O.ci.wr, wr₃, wr₂, wr₁], ctrSt_frame C₅ f₆ (dY (.inl (by decide)) (by decide)), ?_, ?_, ?_⟩
  · rw [Proof.AesGcm.AArch64.bytesAt_frame f₆ dYD (Nat.le_of_lt hn), d₅, hc₃, hx₃]
  · have fA : Frame (cryR p.W p.D p.n ++ absR p.W) t.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨p.W + BitVec.ofNat 64 480, 1280⟩, by simp [absR], Region.sub_prefix (by decide)⟩
    have fB : Frame (cryR p.W p.D p.n ++ absR p.W) s₃.mem s₅.mem :=
      f₅.mono fun r hr => List.mem_append_left _ hr
    have fC : Frame (cryR p.W p.D p.n ++ absR p.W) s₅.mem s₆.mem := f₆.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [absR]
    rw [← m₁₃] at fA
    exact (fA.trans fB).trans fC
  · rw [b₆, v₅, O.y, ext8_ext8, yh]
    refine congrArg _ ?_
    have hr : ∀ i < 8 * (p.n / 128), s₄.mem.readW (p.D + BitVec.ofNat 64 (16 * i)) 128 =
        s₆.mem.readW (p.D + BitVec.ofNat 64 (16 * i)) 128 := fun i hi => by
      have hc : (⟨p.D, p.n⟩ : Region).Contains (p.D + BitVec.ofNat 64 (16 * i)) 16 :=
        Offset.contains_base p.D (by omega) (by omega)
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
  refine WP.ite (decide (p.n / 128 = 0)) (eval_zero x9₂ (by omega)) (fun h => ?_) (fun h => ?_)
  · have h0 : p.n / 128 = 0 := by simpa using h
    refine WP.block_nil ⟨E₂, rd₂, wr₂, ?_, ?_, by rw [m₂]; exact Frame.refl _ _, ?_⟩
    · rw [h0, m₂]; exact C
    · rw [h0, m₂, Nat.mul_zero, GcmSiv.ctrPart_zero]
    · rw [h0, m₂]; simp [elemsAt, ghashFrom]
  · have h1 : 1 ≤ p.n / 128 := by simp at h; omega
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
  have hi' := List.mem_range.mp hi
  rw [Proof.Cmac.bytesAt_length] at ht
  have e := h (16 * i + t) (by omega)
  rw [Proof.Cmac.getD_bytesAt _ _ (by omega), Proof.Cmac.getD_bytesAt _ _ (by omega)] at e
  rw [Proof.Cmac.getD_bytesAt _ _ ht, Proof.Cmac.getD_bytesAt _ _ ht, Offset.add_add, e, ← Offset.add_add]

/-- What `openData` leaves, from `t`. -/
structure OpenPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR p.W p.D p.n ++ absorbR p.W) t.mem t'.mem
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
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem p.D p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  -- What the parts miss.
  have dCry : ∀ {d k : Nat}, d + k ≤ 96 → ∀ r ∈ cryR p.W p.D p.n, (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.d_w' (by omega)).symm
  have dAbs : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ absR p.W, (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun {d k} h r hr => by
      simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have dKey : ∀ r ∈ cryR p.W p.D p.n ++ absR p.W,
      (⟨p.W + BitVec.ofNat 64 240, 16 * (p.R + 1)⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact (key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le)
    · simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := L.rounds_le
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
      rw [Proof.AesGcm.AArch64.add_ofNat_assoc]]
    exact Proof.Cmac.frame_store2 _ _ _
  have d96 : ∀ {d k : Nat}, d + k ≤ 96 → ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q := fun {d k} h q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by omega)) (by omega) (by decide)
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
  have hH₁ : blockAt t₁.mem (p.W + BitVec.ofNat 64 64) = blockAt t.mem (p.W + BitVec.ofNat 64 64) :=
    Proof.AesGcm.AArch64.blockAt_frame f₁ (d96 (by decide))
  have hY₁ : blockAt t₁.mem (p.W + BitVec.ofNat 64 80) = blockAt t.mem (p.W + BitVec.ofNat 64 80) :=
    Proof.AesGcm.AArch64.blockAt_frame f₁ (d96 (by decide))
  have C₀ : CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
    rw [hm₁]; exact headMem_ctr _
  have E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The batches.
  have hb := WP.mono (openBatches_ok hP gh e3 L E₁ C₀) fun t₂ (B : OBatchPost p _ _ _ t₁ t₂) => by
    rw [hc₁, hx₁] at B; exact B
  refine WP.seq (WP.mono hb fun t₂ B => ?_)
  have hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    rw [← hc₁]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame B.frame dKey (by have := L.rounds_le; omega)]
  -- The rest, decrypted.
  refine WP.seq (WP.mono (cryptRest_ok v L B.env hxl B.ctr B.data hc₂) fun t₃ T => ?_)
  -- The rest, absorbed.
  refine WP.seq (WP.mono (rest_ok L T.env) fun t₄ ⟨x27₄, x28₄, E₄, _, m₄, rd₄, wr₄⟩ => ?_)
  have hc : Covers [⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩] (t₄.rd ++ t₄.wr) := by
    rw [rd₄, wr₄, T.rd, T.wr, B.rd, B.wr, rd₁, wr₁]
    exact Proof.AesGcm.AArch64.covers_left (Proof.AesGcm.AArch64.covers_off E.perm.d (by omega) hn)
  have dW : (⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega))
  refine WP.mono (absorb_ok v L E₄ hc (by omega) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * (p.n / 128)) (by omega)]
      have := L.dw; have := Nat.mod_le (p.D.toNat + 128 * (p.n / 128)) (2 ^ 64); omega)
    dW x27₄ x28₄) fun t₅ P₅ => ?_
  have d₅ : bytesAt t₅.mem p.D p.n = bytesAt t₃.mem p.D p.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame P₅.frame (absorbR_buf L.d_w) (Nat.le_of_lt hn), m₄]
  have hd₅ : bytesAt t₅.mem p.D p.n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n) := by
    rw [d₅, T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  refine ⟨P₅.env, by rw [P₅.rd, rd₄, T.rd, B.rd, rd₁], by rw [P₅.wr, wr₄, T.wr, B.wr, wr₁], ?_, hd₅, ?_⟩
  · have g₁ : Frame (cryR p.W p.D p.n ++ absorbR p.W) t.mem t₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
    have g₂ : Frame (cryR p.W p.D p.n ++ absorbR p.W) t₁.mem t₂.mem := B.frame.mono fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    have g₃ : Frame (cryR p.W p.D p.n ++ absorbR p.W) t₂.mem t₄.mem := by
      rw [m₄]; exact T.frame.mono fun r hr => List.mem_append_left _ hr
    have g₄ : Frame (cryR p.W p.D p.n ++ absorbR p.W) t₄.mem t₅.mem :=
      P₅.frame.mono fun r hr => List.mem_append_right _ hr
    exact ((g₁.trans g₂).trans g₃).trans g₄
  · have hH₄ : blockAt t₄.mem (p.W + BitVec.ofNat 64 64) = blockAt t.mem (p.W + BitVec.ofNat 64 64) := by
      rw [m₄, Proof.AesGcm.AArch64.blockAt_frame T.frame (dCry (by decide)),
        Proof.AesGcm.AArch64.blockAt_frame B.frame (fun r hr => by
          rcases List.mem_append.mp hr with hr | hr
          · exact dCry (by decide) r hr
          · exact dAbs (by decide) r hr), hH₁]
    have hY₄ : blockAt t₄.mem (p.W + BitVec.ofNat 64 80) = blockAt t₂.mem (p.W + BitVec.ofNat 64 80) := by
      rw [m₄, Proof.AesGcm.AArch64.blockAt_frame T.frame (dCry (by decide))]
    have hr₅ : bytesAt t₅.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) =
        bytesAt t₄.mem (p.D + BitVec.ofNat 64 (128 * (p.n / 128))) (p.n - 128 * (p.n / 128)) :=
      Proof.AesGcm.AArch64.bytesAt_frame P₅.frame (absorbR_buf dW) (by omega)
    have he : elemsAt t₅.mem p.D (8 * (p.n / 128)) = elemsAt t₂.mem p.D (8 * (p.n / 128)) := by
      refine elemsAt_of_getD (n := p.n) (by omega) fun q hq => ?_
      rw [d₅, T.data, B.data, GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; omega),
        GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; omega), ite_eq_left (by omega), ite_eq_left (by omega)]
    rw [P₅.out, hH₄, hY₄, B.out, hH₁, hY₁, elems_split t₅.mem, Proof.Gcm.ghashFrom_append, he, hr₅]

end VG.Proof.AesGcmSiv.AArch64.Stitch
