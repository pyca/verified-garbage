module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Seal
public import VerifiedGarbage.Proof.AesOcb.RISCV64.FrontCT
public import VerifiedGarbage.Proof.AesOcb.RISCV64.CmpMask
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.FrontCT
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.CmpMask
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Seal
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Impl.AesOcb.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# AES-OCB on RISC-V: `vg_aes_ocb_seal` and `vg_aes_ocb_open` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments (`onePub`) have the same arguments of `front_rel` (`FnArgs`, with
the values of the first run). After `front`, `seal` copies the tag out and
restores our caller's registers: code without calls, which the taint
analysis checks from the public registers. `open` copies the received tag
and compares it with the one it computed, by code the taint analysis checks,
then masks the data without a branch: the mask loads the data's address
from its slot, the same in both runs by the correctness proofs, so its head
is checked on its own (`maskHead_ok`), and the rest, and `restore`, from
that address and the public registers (`openTail_rel`). `open` leaks nothing
more than `seal`, in particular not whether the tag is right. As on PPC64LE
(`Proof/AesOcb/PPC64LE/FnCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Proof.AesGcm.RISCV64 (Keeps)
open VG.Impl.AesGcm.RISCV64 (restore)

/-- A relation of two runs of `(a; b); c`, from one of `a; (b; c)`. -/
theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `FnArgs` in two runs with the same public arguments, with the values of
the first. -/
theorem args₂_of {σ₁ σ₂ : State} (hq : onePub σ₁ σ₂)
    (A₂ : FnArgs σ₂ (σ₂.gpr .a0) (stackArg σ₂ 2) (σ₂.gpr .a2) (σ₂.gpr .a4) (σ₂.gpr .a6) (σ₂.gpr .a1).toNat
      (σ₂.gpr .a3).toNat (σ₂.gpr .a5).toNat (σ₂.gpr .a7).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0)) :
    FnArgs σ₂ (σ₁.gpr .a0) (stackArg σ₁ 2) (σ₁.gpr .a2) (σ₁.gpr .a4) (σ₁.gpr .a6) (σ₁.gpr .a1).toNat
      (σ₁.gpr .a3).toNat (σ₁.gpr .a5).toNat (σ₁.gpr .a7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0) := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, qa⟩ := hq
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qa 0 (by decide), ← qa 1 (by decide),
    ← qa 2 (by decide)] at A₂
  exact A₂

/-- `front enc d; k` in two runs with the same public arguments. -/
theorem front_relq (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {k : Prog isa} {σ₁ σ₂ : State}
    (hk : ∀ (V₁ V₂ : Reg → BitVec 64) (τ₁ τ₂ : State), Agree V₁ V₂ →
      FrontOut V₁ σ₁.sp (stackArg σ₁ 2) (σ₁.gpr .a4) (σ₁.gpr .a6) (stackArg σ₁ 0) (σ₁.gpr .a7).toNat
        (stackArg σ₁ 1).toNat σ₁ τ₁ →
      FrontOut V₂ σ₁.sp (stackArg σ₁ 2) (σ₁.gpr .a4) (σ₁.gpr .a6) (stackArg σ₁ 0) (σ₁.gpr .a7).toNat
        (stackArg σ₁ 1).toNat σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) k TT)
    (A₁ : FnArgs σ₁ (σ₁.gpr .a0) (stackArg σ₁ 2) (σ₁.gpr .a2) (σ₁.gpr .a4) (σ₁.gpr .a6) (σ₁.gpr .a1).toNat
      (σ₁.gpr .a3).toNat (σ₁.gpr .a5).toNat (σ₁.gpr .a7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (A₂ : FnArgs σ₂ (σ₂.gpr .a0) (stackArg σ₂ 2) (σ₂.gpr .a2) (σ₂.gpr .a4) (σ₂.gpr .a6) (σ₂.gpr .a1).toNat
      (σ₂.gpr .a3).toNat (σ₂.gpr .a5).toNat (σ₂.gpr .a7).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0))
    (hq : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.seq (front enc d) k) TT := by
  have A₂' := args₂_of hq A₂
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  exact front_rel enc hd hk A₁ A₂' rfl rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
    (qa 2 (by decide)).symm (qa 0 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3)
    q4.symm (o' q5) q6.symm (o' q7) qsp

theorem seal_ct : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «seal»
  refine front_relq true (.inl rfl) (fun _ _ _ _ hV O₁ O₂ => ?_) (sealArgs_of h₁) (sealArgs_of h₂) hq
  exact rel_env O₁.env O₂.env hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

/-- The head of `mask`: the data's address, from its slot, and its length. -/
theorem maskHead_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) (hal : (V .s0).toNat % 8 = 0)
    {A D : Addr} (hS : Slots (V .s0) A D s.mem) :
    WP isa (.block [.load .d .s4 .s0 Impl.AesGcm.RISCV64.dataO, Impl.AesGcm.RISCV64.mov .s5 .s11,
      .li .t2 0, .sub .t5 .t2 .a0]) s fun s₁ =>
      s₁.gpr .s4 = D ∧ s₁.gpr .s5 = V .s11 ∧ (∀ r, r ∉ maskRegs → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ :=
  wp_ld (off := 240) (a := V .s0 + BitVec.ofNat 64 240) (by decide) (by rw [E.s0]) (Spill.al8 hal (by decide))
    (E.perm.wR (by decide)) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_li (imm := 0) (by decide) fun t₃ u₃ =>
    wp_sub fun t₄ u₄ => WP.block_nil
    ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hS.data],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s11],
      fun r hr => by
        rw [u₄.other _ (ne_of_not_mem hr), u₃.other _ (ne_of_not_mem hr), u₂.other _ (ne_of_not_mem hr),
          u₁.other _ (ne_of_not_mem hr)],
      ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩⟩

/-- What `open` runs after `front`, in two runs, from what `front` leaves. -/
theorem openTail_rel {σ₁ σ₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (A₁ : FnArgs σ₁ K W N A D R nl al n tl T) (A₂ : FnArgs σ₂ K W N A D R nl al n tl T) {sp : Addr}
    {V₁ V₂ : Reg → BitVec 64} {τ₁ τ₂ : State} (hV : Agree V₁ V₂) (O₁ : FrontOut V₁ sp W A D T n tl σ₁ τ₁)
    (O₂ : FrontOut V₂ sp W A D T n tl σ₂ τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (.seq recv (.seq cmp (.seq mask (.block restore)))) TT := by
  have hal₁ : (V₁ .s0).toNat % 8 = 0 := by rw [O₁.s0]; exact A₁.lay.wal
  have hal₂ : (V₂ .s0).toNat % 8 = 0 := by rw [O₂.s0]; exact A₂.lay.wal
  have E₁ := O₁.env
  have E₂ := O₂.env
  -- the received tag
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (recv_ok E₁ hal₁ O₁.s8 A₁.t1 A₁.t16 (by rw [O₁.s9, O₁.rd, O₁.wr]; exact A₁.tag.rd)
      (by rw [O₁.s9, O₁.s0]; exact A₁.tag.w))
    (recv_ok E₂ hal₂ O₂.s8 A₂.t1 A₂.t16 (by rw [O₂.s9, O₂.rd, O₂.wr]; exact A₂.tag.rd)
      (by rw [O₂.s9, O₂.s0]; exact A₂.tag.w))
    fun u₁ u₂ ⟨_, f₁, g₁, sp₁, rd₁, wr₁⟩ ⟨_, f₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have U₁ := E₁.others g₁ sp₁ rd₁ wr₁
  have U₂ := E₂.others g₂ sp₂ rd₂ wr₂
  rw [O₁.s0] at f₁
  rw [O₂.s0] at f₂
  have S₁ : Slots W A D u₁.mem := Slots.mut A₁.lay A₁.data.w (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide)) O₁.slots
  have S₂ : Slots W A D u₂.mem := Slots.mut A₂.lay A₂.data.w (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide)) O₂.slots
  -- the comparison
  refine rel_seq (rel_env U₁ U₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (cmp_ok U₁ hal₁ O₁.s8 A₁.t1 A₁.t16) (cmp_ok U₂ hal₂ O₂.s8 A₂.t1 A₂.t16)
    fun v₁ v₂ ⟨_, f₁', g₁', sp₁', rd₁', wr₁'⟩ ⟨_, f₂', g₂', sp₂', rd₂', wr₂'⟩ => ?_
  have Y₁ := U₁.others g₁' sp₁' rd₁' wr₁'
  have Y₂ := U₂.others g₂' sp₂' rd₂' wr₂'
  rw [O₁.s0] at f₁'
  rw [O₂.s0] at f₂'
  have S₁' : Slots (V₁ .s0) A D v₁.mem := by
    rw [O₁.s0]; exact Slots.mut A₁.lay A₁.data.w (f₁'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutB (by decide) (by decide)) S₁
  have S₂' : Slots (V₂ .s0) A D v₂.mem := by
    rw [O₂.s0]; exact Slots.mut A₂.lay A₂.data.w (f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutB (by decide) (by decide)) S₂
  -- the mask, then `restore`
  unfold mask
  refine RelCT.assoc' (rel_seq (rel_env Y₁ Y₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (maskHead_ok Y₁ hal₁ S₁') (maskHead_ok Y₂ hal₂ S₂') fun w₁ w₂ ⟨a4₁, a5₁, g₁'', k₁⟩ ⟨a4₂, a5₂, g₂'', k₂⟩ => ?_)
  exact rel_env (Y₁.others g₁'' k₁.sp k₁.rd k₁.wr) (Y₂.others g₂'' k₂.sp k₂.rd k₂.wr) hV [.s4, .s5]
    (by agree_rv64 [a4₁, a4₂, a5₁, a5₂, hV .s11 (by decide)]) ⟨_, by taint_decide⟩

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «open»
  exact front_relq false (.inr rfl) (fun _ _ _ _ hV O₁ O₂ =>
    openTail_rel (openArgs_of h₁) (args₂_of hq.1 (openArgs_of h₂)) hV O₁ O₂) (openArgs_of h₁) (openArgs_of h₂) hq.1

end VG.Proof.AesOcb.RISCV64
