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

theorem openBatch_ok (hP : PrepPow) (gh : Gh8Ok) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {icb : List Byte} (C : CtrSt p.W icb 0 t.mem) (hnb : 1 ≤ p.n / 128) :
    WP isa (.seq (.block (tblBuild ++ ctrSetup ++ batches ++ ghSetup))
      (.seq (byRounds openLoop) (.block (ctrFinish ++ ghFinish)))) t
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
      (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]) (by rw [wr₃, wr₂, wr₁]) hs (by rw [hv, y₃, hY]) (by rw [hv]; exact c₃)))
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

end VG.Proof.AesGcmSiv.AArch64.Stitch
