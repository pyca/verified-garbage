module

import VerifiedGarbage.Proof.AesCcm.RISCV64.MacCT
import VerifiedGarbage.Proof.AesCcm.RISCV64.CtrCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.MacCT
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.CtrCT
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Open
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Entry
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesCcm.RISCV64.Ctrs
import VerifiedGarbage.Proof.AesCcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesCcm.RISCV64.Open
import VerifiedGarbage.Proof.AesCcm.RISCV64.Tag
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Ctrs
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Mac
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Tag
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Entry
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
meta import VerifiedGarbage.Impl.AesCcm.RISCV64
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesCcm.RISCV64.Mac
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# AES-CCM on RISCV64: constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`
from the stack, which the taint analysis takes as secret (it reads memory):
the block is split after the load, and the rest runs from `t1` and `t0`,
which hold `work` and the stack pointer in both runs (`entry_rel`). So do the
loads of the tag's address from its slot in `W`, before `tagOut` and `cmp`.
The other pieces are related by `MacCT.lean` and `CtrCT.lean` (`seal_rel`,
`open_rel`). `open` compares the tags and masks the plaintext without a
branch: whether it succeeds is not leaked.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.Impl.AesCcm.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint ct_of)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {σ₁ σ₂ : State} (A₂ : Args (cxOf σ₂) (σ₂.gpr .a2) σ₂)
    (hq : onePub σ₁ σ₂) : Args (cxOf σ₁) (σ₁.gpr .a2) σ₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have hcx : cxOf σ₂ = cxOf σ₁ := by
    simp only [cxOf, q0, q1, q3, q4, q5, q6, q7, qa 0 (by decide), qa 1 (by decide), qa 2 (by decide)]
  rw [hcx, ← q2] at A₂
  exact A₂

/-- `work` and the stack pointer. -/
theorem entryLd_wp {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block [.addSp .t0 0, .load .d .t1 .t0 16]) s fun s' =>
      s'.gpr .t1 = c.W ∧ s'.gpr .t0 = s.sp ∧ s'.sp = s.sp := by
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have t0₁ : s₁.gpr .t0 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 2) (by decide) (by rw [t0₁]; rfl) (Spill.al8 Ar.spal (by omega))
    (by rw [u₁.rd, u₁.wr, stackArgAddr_succ]; exact in_off Ar.argsC (by omega) (by decide))
    fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl, by rw [u₂.other _ (by decide), t0₁],
      by rw [u₂.sp, u₁.sp]⟩

/-- The entry in two runs. -/
theorem entry_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have e : entry = [.addSp .t0 0, .load .d .t1 .t0 16] ++ entry.drop 2 := rfl
  rw [e]
  refine RelCT.block_append (rel_seqR (rel_taint [] hsp (by simp) (by taint_decide))
    (Runs.of_wp (entryLd_wp A₁)) (Runs.of_wp (entryLd_wp A₂)) fun τ₁ τ₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ => ?_)
  refine rel_taint [.t1, .t0] (by rw [c₁, c₂, hsp]) (fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂, hsp]

/-- The tag's address, from its slot. -/
theorem ldT_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .s5 .s1 tagO]) s fun s' => s'.gpr .s5 = c.T ∧ Env c s' ∧ s'.sp = s.sp :=
  wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, S.tag], E.of_pk (PK.ofUpd u₁), u₁.sp⟩

/-- `tagOut`'s arguments. -/
theorem tagOutBlk_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .a1 .s1 tagO, Impl.AesCbc.RISCV64.mov .a0 .s1, Impl.AesCbc.RISCV64.mov .a2 .s2]) s
      fun s' => s'.gpr .a1 = c.T ∧ s'.gpr .a0 = c.W ∧ s'.gpr .a2 = BitVec.ofNat 64 c.tl ∧ Env c s' ∧
        s'.sp = s.sp := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  have pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, S.tag],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s1],
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s2], E.of_pk pk₃, pk₃.sp⟩

/-- `vg_aes_ccm_seal` in two runs. -/
theorem seal_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂) (hsp : σ₁.sp = σ₂.sp)
    (hT₁ : Covers [⟨c.T, c.tl⟩] σ₁.wr) (hT₂ : Covers [⟨c.T, c.tl⟩] σ₂.wr) :
    RelCT isa (Eq2 σ₁ σ₂) «seal» TT := by
  have L := A₁.lay
  unfold «seal»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  have h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [.a2, .a3] En.env En'.env h₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [En.a2, En'.a2]
      · rw [En.a3, En'.a3]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (ctrs_wp L En.env (A₁.nonce.of_eq En.rd En.wr) En.a2 En.a3))
    (Runs.of_wp (ctrs_wp L En'.env (A₂.nonce.of_eq En'.rd En'.wr) En'.a2 En'.a3))
    fun s₂ t₂ ⟨pk₂, f₂, c₂⟩ ⟨pk₂', f₂', c₂'⟩ => ?_
  have E₂ := En.env.of_pk pk₂
  have E₂' := En'.env.of_pk pk₂'
  have h₂ : s₂.sp = t₂.sp := by rw [pk₂.sp, pk₂'.sp, h₁]
  have hnl : ∀ m, (bytesAt m N c.nl).length = c.nl := fun m => length_bytesAt _ _ _
  refine rel_seqR (mac_rel L E₂ E₂' h₂ (.inl rfl) (En.slots.mut L (f₂.sub (c0_mut c)))
      (En'.slots.mut L (f₂'.sub (c0_mut c))))
    (Runs.of_wp (mac_wp L E₂ (En.slots.mut L (f₂.sub (c0_mut c))) (hnl _) c₂ (.inl rfl)))
    (Runs.of_wp (mac_wp L E₂' (En'.slots.mut L (f₂'.sub (c0_mut c))) (hnl _) c₂' (.inl rfl)))
    fun s₃ t₃ M M' => ?_
  have E₃ := E₂.of_pk M.pk
  have E₃' := E₂'.of_pk M'.pk
  have h₃ : s₃.sp = t₃.sp := by rw [M.pk.sp, M'.pk.sp, h₂]
  have fM := M.frame
  have fM' := M'.frame
  rw [macR_list] at fM fM'
  have c₃ := (Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide)).trans c₂
  have c₃' := (Proof.Cmac.bytesAt_frame fM' (w_keep L (by decide) (by decide)) (by decide)).trans c₂'
  refine rel_seqR (tag_rel L E₃ E₃' h₃ (.inl rfl)) (Runs.of_wp (tag_wp L E₃ (hnl _) c₃ (.inl rfl)))
    (Runs.of_wp (tag_wp L E₃' (hnl _) c₃' (.inl rfl))) fun s₄ t₄ ⟨pk₄, _, f₄, _⟩ ⟨pk₄', _, f₄', _⟩ => ?_
  have E₄ := E₃.of_pk pk₄
  have E₄' := E₃'.of_pk pk₄'
  have h₄ : s₄.sp = t₄.sp := by rw [pk₄.sp, pk₄'.sp, h₃]
  have f₄l := f₄
  have f₄l' := f₄'
  rw [ctrR_list] at f₄l f₄l'
  have c₄ := (Proof.Cmac.bytesAt_frame f₄l (w_keep L (by decide) (by decide)) (by decide)).trans c₃
  have c₄' := (Proof.Cmac.bytesAt_frame f₄l' (w_keep L (by decide) (by decide)) (by decide)).trans c₃'
  refine rel_seqR (ctr_rel L E₄ E₄' h₄ (hnl _) (hnl _) c₄ c₄') (Runs.of_wp (ctr_wp L E₄ (hnl _) c₄))
    (Runs.of_wp (ctr_wp L E₄' (hnl _) c₄')) fun s₅ t₅ ⟨pk₅, f₅, _⟩ ⟨pk₅', f₅', _⟩ => ?_
  have E₅ := E₄.of_pk pk₅
  have E₅' := E₄'.of_pk pk₅'
  have h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  have S₅ := En.slots.mut L ((((f₂.sub (c0_mut c)).trans (M.frame.sub (macR_mut (.inl rfl)))).trans
    (f₄.sub (ctrR_mut c (.inl rfl)))).trans (f₅.sub (crR_mut c)))
  have S₅' := En'.slots.mut L ((((f₂'.sub (c0_mut c)).trans (M'.frame.sub (macR_mut (.inl rfl)))).trans
    (f₄'.sub (ctrR_mut c (.inl rfl)))).trans (f₅'.sub (crR_mut c)))
  have wr₅ : s₅.wr = σ₁.wr := by rw [pk₅.wr, pk₄.wr, M.pk.wr, pk₂.wr, En.wr]
  have wr₅' : t₅.wr = σ₂.wr := by rw [pk₅'.wr, pk₄'.wr, M'.pk.wr, pk₂'.wr, En'.wr]
  refine rel_seqR ?_ (Runs.of_wp (tagOut_wp L E₅ S₅ (by rw [wr₅]; exact hT₁)))
    (Runs.of_wp (tagOut_wp L E₅' S₅' (by rw [wr₅']; exact hT₂))) fun s₆ t₆ ⟨pk₆, _⟩ ⟨pk₆', _⟩ => ?_
  · unfold tagOut
    refine rel_seqR (rel_env [] E₅ E₅' h₅ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (tagOutBlk_wp L E₅ S₅))
      (Runs.of_wp (tagOutBlk_wp L E₅' S₅')) fun τ₁ τ₂ ⟨a₁, b₁, c₁', F₁, sp₁⟩ ⟨a₂, b₂, c₂', F₂, sp₂⟩ => ?_
    refine rel_env [.a0, .a2, .a1] F₁ F₂ (by rw [sp₁, sp₂, h₅]) (fun r hr => ?_) ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [c₁', c₂']
    · rw [a₁, a₂]
  · exact rel_env [] (E₅.of_pk pk₆) (E₅'.of_pk pk₆') (by rw [pk₆.sp, pk₆'.sp, h₅]) (by simp) ⟨_, by taint_decide⟩

/-- `vg_aes_ccm_open` in two runs. -/
theorem open_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) «open» TT := by
  have L := A₁.lay
  unfold «open»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  have h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [.a2, .a3] En.env En'.env h₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [En.a2, En'.a2]
      · rw [En.a3, En'.a3]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (ctrs_wp L En.env (A₁.nonce.of_eq En.rd En.wr) En.a2 En.a3))
    (Runs.of_wp (ctrs_wp L En'.env (A₂.nonce.of_eq En'.rd En'.wr) En'.a2 En'.a3))
    fun s₂ t₂ ⟨pk₂, f₂, c₂⟩ ⟨pk₂', f₂', c₂'⟩ => ?_
  have E₂ := En.env.of_pk pk₂
  have E₂' := En'.env.of_pk pk₂'
  have h₂ : s₂.sp = t₂.sp := by rw [pk₂.sp, pk₂'.sp, h₁]
  have hnl : ∀ m, (bytesAt m N c.nl).length = c.nl := fun m => length_bytesAt _ _ _
  refine rel_seqR (ctr_rel L E₂ E₂' h₂ (hnl _) (hnl _) c₂ c₂') (Runs.of_wp (ctr_wp L E₂ (hnl _) c₂))
    (Runs.of_wp (ctr_wp L E₂' (hnl _) c₂')) fun s₃ t₃ ⟨pk₃, f₃, _⟩ ⟨pk₃', f₃', _⟩ => ?_
  have E₃ := E₂.of_pk pk₃
  have E₃' := E₂'.of_pk pk₃'
  have h₃ : s₃.sp = t₃.sp := by rw [pk₃.sp, pk₃'.sp, h₂]
  have g₁₃ := (f₂.sub (c0_mut c)).trans (f₃.sub (crR_mut c))
  have g₁₃' := (f₂'.sub (c0_mut c)).trans (f₃'.sub (crR_mut c))
  have c₃ := (Proof.Cmac.bytesAt_frame f₃ (crR_disj L (.inl (by decide))) (by decide)).trans c₂
  have c₃' := (Proof.Cmac.bytesAt_frame f₃' (crR_disj L (.inl (by decide))) (by decide)).trans c₂'
  refine rel_seqR (mac_rel L E₃ E₃' h₃ (.inr rfl) (En.slots.mut L g₁₃) (En'.slots.mut L g₁₃'))
    (Runs.of_wp (mac_wp L E₃ (En.slots.mut L g₁₃) (hnl _) c₃ (.inr rfl)))
    (Runs.of_wp (mac_wp L E₃' (En'.slots.mut L g₁₃') (hnl _) c₃' (.inr rfl))) fun s₄ t₄ M M' => ?_
  have E₄ := E₃.of_pk M.pk
  have E₄' := E₃'.of_pk M'.pk
  have h₄ : s₄.sp = t₄.sp := by rw [M.pk.sp, M'.pk.sp, h₃]
  have fM := M.frame
  have fM' := M'.frame
  rw [macR_list] at fM fM'
  have c₄ := (Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide)).trans c₃
  have c₄' := (Proof.Cmac.bytesAt_frame fM' (w_keep L (by decide) (by decide)) (by decide)).trans c₃'
  refine rel_seqR (tag_rel L E₄ E₄' h₄ (.inr rfl)) (Runs.of_wp (tag_wp L E₄ (hnl _) c₄ (.inr rfl)))
    (Runs.of_wp (tag_wp L E₄' (hnl _) c₄' (.inr rfl))) fun s₅ t₅ ⟨pk₅, _, f₅, _⟩ ⟨pk₅', _, f₅', _⟩ => ?_
  have E₅ := E₄.of_pk pk₅
  have E₅' := E₄'.of_pk pk₅'
  have h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  have S₅ := En.slots.mut L ((g₁₃.trans (M.frame.sub (macR_mut (.inr rfl)))).trans (f₅.sub (ctrR_mut c (.inr rfl))))
  have S₅' := En'.slots.mut L ((g₁₃'.trans (M'.frame.sub (macR_mut (.inr rfl)))).trans
    (f₅'.sub (ctrR_mut c (.inr rfl))))
  refine rel_seqR (rel_env [] E₅ E₅' h₅ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (ldT_wp L E₅ S₅))
    (Runs.of_wp (ldT_wp L E₅' S₅')) fun s₆ t₆ ⟨a₁, F₁, sp₁⟩ ⟨a₂, F₂, sp₂⟩ => ?_
  exact rel_env [.s5] F₁ F₂ (by rw [sp₁, sp₂, h₅]) (by simp [a₁, a₂]) ⟨_, by taint_decide⟩

theorem seal_ct : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» :=
  ct_of fun σ₁ σ₂ h₁ h₂ hq => by
    have B₁ := args_of_seal h₁
    have B₂ := args_of_seal h₂
    have A₂ := args_two B₂.1 hq
    obtain ⟨-, -, -, -, -, -, -, -, qsp, qa⟩ := hq
    exact seal_rel B₁.1 A₂ qsp B₁.2 (by
      simpa only [cxOf, qa 0 (by decide), qa 1 (by decide)] using B₂.2)

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» :=
  ct_of fun _ _ h₁ h₂ hq => open_rel (args_of_open h₁) (args_two (args_of_open h₂) hq.1)
    hq.1.2.2.2.2.2.2.2.2.1

end VG.Proof.AesCcm.RISCV64
