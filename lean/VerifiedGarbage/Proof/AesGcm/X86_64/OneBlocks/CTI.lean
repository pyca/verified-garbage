module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.OkI
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.OkI
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT

/-!
# AES-GCM on x86-64: `oneBlocks` calling the function given the block index, in two runs

Untrusted: everything here is checked by Lean. As `oneBlocksD_rel`, for
`vg_aes_gcm_decrypt_blocks_prepared_iv96`, from states whose `SP` holds the
block index of the counter block, 2 in both runs (`IdxAt`): both runs call it
with the same arguments, the same index among them (`obFrameDI_rel`), so they
leak the same (`oneBlocksDI_rel`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (blockAt ctrIndex)
open Gcm.X86_64.Stitch (CtxMode)

/-- The block index of the counter block at `cbA W`, 2, also in the readable
word at `SP`. -/
structure IdxAt (W SP : Addr) (s : State) : Prop where
  cb : ctrIndex (blockAt s.mem (cbA W)) = 2
  w : (s.mem.readW SP 64).setWidth 32 = 2
  r : InRegions (s.rd ++ s.wr) SP 8

theorem IdxAt.hidx {W SP : Addr} {s : State} (h : IdxAt W SP s) :
    ctrIndex (blockAt s.mem (cbA W)) = (s.mem.readW SP 64).setWidth 32 := h.cb.trans h.w.symm

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {M : CtxMode}
  (a_w : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
include L a_w

/-- `IdxAt` after code writing only the total length's slot. -/
theorem IdxAt.keep {s s' : State} (h : IdxAt W SP s) {v : BitVec 64}
    (hm : s'.mem = s.mem.writeW (W + BitVec.ofNat 64 192) v) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    IdxAt W SP s' := by
  have hs : Region.Sub ⟨SP, 8⟩ ⟨SP - BitVec.ofNat 64 8, 16⟩ := by
    have := Offset.sub_base (SP - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 16) (by decide)
    rwa [BitVec.sub_add_cancel] at this
  have hf : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨?_, ?_, by rw [hrd, hwr]; exact h.r⟩
  · rw [blockAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [cbA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))]
    exact h.cb
  · rw [hf.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (a_w.sub_right (Lay.wSub (by decide))).sub_left hs) (by decide)]
    exact h.w

/-- The length kept, and the arguments of the call when there are whole
blocks, keeping `IdxAt`. -/
theorem ob12I_ok {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) (hI : IdxAt W SP s) :
    WP isa (.block obB1) s fun s₁ => s₁.zf = some (decide (n / 16 = 0)) ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      (n / 16 ≠ 0 → WP isa (.block obB2) s₁ fun s₂ =>
        ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ ∧ IdxAt W SP s₂) := by
  have hn : n < 2 ^ 64 := h.data.ok.lt
  have he := h.env
  obtain ⟨e176, e200, -, -, -, -, -, -, f192⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine WP.mono (ob1_ok hn he h.len) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine ⟨z₁, he₁, fun hz => ?_⟩
  have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [m₁, e176]; exact h.rounds.1, h.rounds.2⟩
  have hd₁ : s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [m₁, e200, h.dat]
  refine WP.mono (ob2_ok he₁ hR₁ hd₁) fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) rd₂ wr₂
  exact ⟨⟨he₂, h.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁), by omega, h.t_c, h.t_w, h.t_d, h.sp24, a1, a2, a3,
    a4, a5, by rw [a6, r₁], a7, h.rounds.2, h.t_w.sub_right (Lay.wSub (by decide)),
    h.ext.keep (rd₂.trans rd₁) (wr₂.trans wr₁) (by rw [m₂, m₁]; exact f192) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ext.cw.sub_right (Lay.wSub (by decide)))⟩,
    hI.keep L a_w (m₂.trans m₁) (rd₂.trans rd₁) (wr₂.trans wr₁)⟩

/-- The frame of the call of `vg_aes_gcm_decrypt_blocks_prepared_iv96` in two
runs with the same arguments and index. -/
theorem obFrameDI_rel (F : DecFnI M) {R : Nat} {D : Addr} {n q : Nat}
    (a_d : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, n⟩) (w_sp : SP.toNat + 8 ≤ 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => (ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n q s₁ ∧ IdxAt W SP s₁) ∧
        (ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n q s₂ ∧ IdxAt W SP s₂))
      (.frame (.push [.rax]) (.call F.fn.name F.fn.code) (.pop .rax 1)) fun _ _ => True := by
  have a_st : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 16, 80⟩ :=
    a_w.sub_right (Lay.wSub (by decide))
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.env.rsp, h.2.1.env.rsp])
    (RelCT.callEx (k := Proof.AesGcm.decryptBlocksIv96X86_64M M) F.ok F.ct fun _ _ ⟨s₁, s₂, hp, ha, hb⟩ => ?_)
  subst ha hb
  have L₀ : Lay Ctx (W + BitVec.ofNat 64 16) W SP := L
  have c₁ := ObIn.callI L₀ hp.1.1 hp.1.2.hidx a_st a_w a_d hp.1.2.r w_sp
  have c₂ := ObIn.callI L₀ hp.2.1 hp.2.2.hidx a_st a_w a_d hp.2.2.r w_sp
  have hsp : (pushed [.rax] s₁).gpr .rsp = (pushed [.rax] s₂).gpr .rsp := by
    rw [pushed_rsp, pushed_rsp, hp.1.1.env.rsp, hp.2.1.env.rsp]
  obtain ⟨-, -, eC₁, -, -, -⟩ := ObIn.push_eqs L₀ hp.1.1
  obtain ⟨-, -, eC₂, -, -, -⟩ := ObIn.push_eqs L₀ hp.2.1
  refine ⟨_, _, _, _, c₁.pre, c₂.pre, ⟨blk_pub c₁.toBlkCall c₂.toBlkCall hsp, ?_⟩, c₁.readsI, c₁.toBlkCall.writes,
    c₂.readsI, c₂.toBlkCall.writes, hsp⟩
  show (stackArg _ 1).setWidth 32 = (stackArg _ 1).setWidth 32
  rw [c₁.arg1, c₂.arg1, eC₁, eC₂]
  exact hp.1.2.cb.trans hp.2.2.cb.symm

/-- `oneBlocks` of the decrypting function given the block index, in two runs
from states holding the index at `SP`: after it, what stays in `W`. -/
theorem oneBlocksDI_rel (F : DecFnI M) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat)
    (a_d : (⟨SP - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, n⟩) (w_sp : SP.toNat + 8 ≤ 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => OneS₂ M Ctx W SP R A al D n T s₁ s₂ ∧ IdxAt W SP s₁ ∧ IdxAt W SP s₂) (oneBlocks F.fn)
      (OneS₂ M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := by
  have pre : ∀ s, OneS M Ctx W SP R A al D n T s → ObPre M Ctx W SP R D n s := fun s h =>
    ⟨h.env, h.rounds, h.dat, h.len, h.dD, t_c, t_w, t_d, sp24, h.ext⟩
  let G₁ : State → Prop := fun s₁ => s₁.zf = some (decide (n / 16 = 0)) ∧
    Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ (n / 16 ≠ 0 → WP isa (.block obB2) s₁ fun s₂ =>
      ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ ∧ IdxAt W SP s₂)
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => OneS₂ M Ctx W SP R A al D n T s₁ s₂ ∧ IdxAt W SP s₁ ∧
      IdxAt W SP s₂) [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h.1) ⟨_, by taint_decide⟩)
    (F₁ := fun s => OneS M Ctx W SP R A al D n T s ∧ IdxAt W SP s)
    (F₂ := fun s => OneS M Ctx W SP R A al D n T s ∧ IdxAt W SP s)
    (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩) (G₁ := G₁) (G₂ := G₁)
    (fun s h => ob12I_ok L a_w (pre s h.1) h.2)
    (fun s h => ob12I_ok L a_w (pre s h.1) h.2)
  have t := rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some true) (c := .block [])
    [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩
  have hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block obB2) s fun s₂ =>
      ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ ∧ IdxAt W SP s₂ :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some false) (c := .block obB2)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨⟨h.1.2.1, h.2⟩, ⟨h.1.2.2, by rw [h.1.2.2.1, ← h.1.2.1.1, h.2]⟩⟩) hw₂ hw₂
  let G₃ : State → Prop := fun s => s.gpr .r13 = Ctx ∧ s.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s.gpr .r15 = W ∧
    s.gpr .rsp = SP
  have hw₃ : ∀ s, ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s ∧ IdxAt W SP s →
      WP isa (.frame (.push [.rax]) (.call F.fn.name F.fn.code) (.pop .rax 1)) s G₃ := fun s h =>
    WP.mono (obFrameDI_ok L F h.1 h.2.hidx (a_w.sub_right (Lay.wSub (by decide))) a_w a_d h.2.r w_sp)
      fun _ hc => ⟨by rw [hc.1 .r13 (by decide)]; exact h.1.env.r13,
        by rw [hc.1 .r14 (by decide)]; exact h.1.env.r14, by rw [hc.1 .r15 (by decide)]; exact h.1.env.r15,
        by rw [hc.1 .rsp (by decide)]; exact h.1.env.rsp⟩
  have c := rel_wp ((obFrameDI_rel L a_w F a_d w_sp).mono (P' := fun s₁ s₂ => True ∧
      (ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₁ ∧ IdxAt W SP s₁) ∧
      (ObIn M Ctx (W + BitVec.ofNat 64 16) W SP R D n (n / 16) s₂ ∧ IdxAt W SP s₂))
      (fun _ _ h => h.2) fun _ _ h => h) (fun _ _ h => h.2) hw₃ hw₃
  have d := rel_taint (P := fun s₁ s₂ => True ∧ G₃ s₁ ∧ G₃ s₂) (c := .block obB3) [.r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => by
      obtain ⟨-, ⟨a₁, b₁, c₁, d₁⟩, ⟨a₂, b₂, c₂, d₂⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [d₁, d₂]) ⟨_, by taint_decide⟩
  have hw : ∀ s, OneS M Ctx W SP R A al D n T s ∧ IdxAt W SP s → WP isa (oneBlocks F.fn) s
      (OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := fun s h =>
    WP.mono (oneBlocksDI_ok L F (pre s h.1) h.2.hidx a_w a_d h.2.r w_sp) fun _ ⟨P, _⟩ => ObPost.oneS L t_w h.1 P
  have r := RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.1, h.2.2.1]) t (RelCT.seq b (RelCT.seq c d)))
  rw [← oneBlocks_eq] at r
  exact (rel_wp (r.mono (fun _ _ h => h) fun _ _ _ => trivial) (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
    hw hw).mono (fun _ _ h => h) fun _ _ h => h.2

end

end VG.Proof.AesGcm.X86_64
