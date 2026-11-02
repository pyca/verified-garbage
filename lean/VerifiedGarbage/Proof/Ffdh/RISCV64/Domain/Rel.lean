module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.Body
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.Body
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# FFDH's domain checks on RISC-V: the pieces in constant time

As for the exchange (`Proof/Ffdh/RISCV64/CT.lean`): two runs with the same
public data are related at each cut by `Two`, both satisfying a predicate for
it. Each piece of code shared by `vg_ffdh_check_public` and
`vg_ffdh_check_domain` is checked once by the taint analysis, from the
registers a predicate fixes (`Pins`); `two_ite` relates a branch on a
register that a predicate fixes as a function of the data.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Domain

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Domain
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-! ## Pins -/

theorem pins_base {α : Type} {Φ : α → State → Prop} (f : α → DD) (h : ∀ a s, Φ a s → DBase (f a) s) :
    Pins Φ dbaseRegs :=
  fun a _ _ h₁ h₂ => DBase.pins (h a _ h₁) (h a _ h₂)

theorem pins_one {α : Type} {Φ : α → State → Prop} (r : Reg) (f : α → BitVec 64)
    (h : ∀ a s, Φ a s → s.gpr r = f a) : Pins Φ [r] := by
  intro a s₁ s₂ h₁ h₂ r' hr
  rw [List.mem_singleton] at hr
  subst hr
  rw [h a _ h₁, h a _ h₂]

theorem pins_cons {α : Type} {Φ : α → State → Prop} {r : Reg} {rs : List Reg} (h₁ : Pins Φ [r]) (h₂ : Pins Φ rs) :
    Pins Φ (r :: rs) := by
  intro a s₁ s₂ g₁ g₂ r' hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h₁ a _ _ g₁ g₂ _ List.mem_cons_self
  · exact h₂ a _ _ g₁ g₂ _ hr

theorem pins_and {α : Type} {Φ Ψ : α → State → Prop} {rs : List Reg} (h : Pins Φ rs) :
    Pins (fun a s => Φ a s ∧ Ψ a s) rs :=
  fun a _ _ h₁ h₂ => h a _ _ h₁.1 h₂.1

theorem pins_nil {α : Type} {Φ : α → State → Prop} : Pins Φ ([] : List Reg) :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- A branch on whether `r` is zero, which `Φ` fixes as `b`. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {r : Reg} (b : α → Bool)
    (hb : ∀ a s, Φ a s → (s.gpr r == 0) = b a) {t e : Prog isa} {Q : State → State → Prop}
    (ht : RelCT isa (Two fun a s => Φ a s ∧ b a = true) t Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ b a = false) e Q) :
    RelCT isa (Two Φ) (.ite (.zero r) t e) Q := by
  refine RelCT.ite (fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => by rw [Steps.eval_zero, Steps.eval_zero, hb a _ h₁, hb a _ h₂])
    (ht.mono (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
    (he.mono (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
  · rw [Steps.eval_zero, hb a _ h₁, Option.some.injEq] at hc
    exact ⟨a, ⟨h₁, hc⟩, ⟨h₂, hc⟩, hsp⟩
  · rw [Steps.eval_zero, hb a _ h₁, Option.some.injEq] at hc
    exact ⟨a, ⟨h₁, hc⟩, ⟨h₂, hc⟩, hsp⟩

/-! ## The shared pieces, by the taint analysis -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem loadN_rel (h : Pins Φ (.s7 :: .s8 :: dbaseRegs)) :
    RelCT isa (Two Φ) Precompute.loadN fun _ _ => True := two_taint _ h (by taint_decide)

theorem check1_rel (h : Pins Φ (.s7 :: .s8 :: dbaseRegs)) :
    RelCT isa (Two Φ) (.block Precompute.check1) fun _ _ => True := two_taint _ h (by taint_decide)

theorem check2_rel (h : Pins Φ (.s8 :: .t4 :: dbaseRegs)) :
    RelCT isa (Two Φ) Precompute.check2 fun _ _ => True := two_taint _ h (by taint_decide)

theorem range_rel (h : Pins Φ (.a6 :: dbaseRegs)) :
    RelCT isa (Two Φ) range fun _ _ => True := two_taint _ h (by taint_decide)

theorem hasQ_rel (h : Pins Φ dbaseRegs) :
    RelCT isa (Two Φ) (.block hasQ) fun _ _ => True := two_taint _ h (by taint_decide)

theorem sg1_rel (h : Pins Φ dbaseRegs) :
    RelCT isa (Two Φ) (.seq r2 (.block qPtr)) fun _ _ => True := two_taint _ h (by taint_decide)

theorem powWin_rel (h : Pins Φ (.s9 :: .s10 :: dbaseRegs)) :
    RelCT isa (Two Φ) ModExp.powWin fun _ _ => True := two_taint _ h (by taint_decide)

theorem isOne_rel (h : Pins Φ dbaseRegs) :
    RelCT isa (Two Φ) isOne fun _ _ => True := two_taint _ h (by taint_decide)

theorem fail_rel : RelCT isa (Two Φ) (.block [.li .a0 0]) fun _ _ => True := two_taint _ pins_nil (by taint_decide)

theorem restore_rel (h : Pins Φ [.s6]) :
    RelCT isa (Two Φ) (.block PublicChecked.restore) fun _ _ => True := two_taint _ h (by taint_decide)

end

/-! ## Predicates at the cuts shared by both functions -/

/-- After the branches: the working space in `s6`. -/
def CF (x : DD) (s : State) : Prop := s.gpr .s6 = x.S

theorem pins_CF : Pins CF [.s6] := pins_one .s6 (fun x => x.S) fun _ _ h => h

theorem pins_P1 : Pins P1 (.s7 :: .s8 :: dbaseRegs) :=
  pins_cons (pins_one .s7 (fun x => off x.D 0) fun _ _ h => h.2.1)
    (pins_cons (pins_one .s8 (fun x => BitVec.ofNat 64 x.k) fun _ _ h => h.2.2) (pins_base id fun _ _ h => h.1))

theorem pins_P2 : Pins P2 (.s7 :: .s8 :: dbaseRegs) :=
  pins_cons (pins_one .s7 (fun x => off x.D 0) fun _ _ h => h.2.2.1)
    (pins_cons (pins_one .s8 (fun x => BitVec.ofNat 64 x.k) fun _ _ h => h.2.2.2) (pins_base id fun _ _ h => h.1))

theorem pins_P3 : Pins P3 (.s8 :: .t4 :: dbaseRegs) :=
  pins_cons (pins_one .s8 (fun x => BitVec.ofNat 64 x.k) fun _ _ h => h.2.2.1)
    (pins_cons (pins_one .t4 (fun x => BitVec.ofNat 64 ((x.db.take x.k).getD 0 0).toNat) fun _ _ h => h.2.2.2.1)
      (pins_base id fun _ _ h => h.1))

/-- `loadP`, from `P1` to `P4`. -/
theorem loadP_rel : RelCT isa (Two P1) loadP (Two P4) := by
  unfold loadP Precompute.check
  exact RelCT.seq (two_post (loadN_rel pins_P1) fun _ _ h => WP.mono (loadN_P h) fun _ h => h.1)
    (RelCT.seq (two_post (check1_rel pins_P2) fun _ _ h => WP.mono (check1_P h) fun _ h => h.1)
      (two_post (check2_rel pins_P3) fun _ _ h => WP.mono (check2_P h) fun _ h => h.1))

/-- The branch on p's validity. -/
theorem p_ite {t : Prog isa} {Q : State → State → Prop}
    (ht : RelCT isa (Two fun x s => P4 x s ∧ (!Spec.Rsa.modulusValid x.p x.k) = false) t Q)
    (he : RelCT isa (Two fun x s => P4 x s ∧ (!Spec.Rsa.modulusValid x.p x.k) = true) (.block [.li .a0 0]) Q) :
    RelCT isa (Two P4) (.ite (.zero .s0) t (.block [.li .a0 0])) Q := by
  refine two_ite (fun x => !(!Spec.Rsa.modulusValid x.p x.k)) (fun x s h => ?_)
    (ht.mono (fun _ _ ⟨x, ⟨h₁, c₁⟩, ⟨h₂, c₂⟩, sp⟩ => ⟨x, ⟨h₁, by simpa using c₁⟩, ⟨h₂, by simpa using c₂⟩, sp⟩)
      fun _ _ h => h)
    (he.mono (fun _ _ ⟨x, ⟨h₁, c₁⟩, ⟨h₂, c₂⟩, sp⟩ => ⟨x, ⟨h₁, by simpa using c₁⟩, ⟨h₂, by simpa using c₂⟩, sp⟩)
      fun _ _ h => h)
  rw [Bool.not_not]
  exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq]; exact h.2.2)

/-- The invalid-p branch reaches `CF`. -/
theorem pFail_rel : RelCT isa (Two fun x s => P4 x s ∧ (!Spec.Rsa.modulusValid x.p x.k) = true)
    (.block [.li .a0 0]) (Two CF) :=
  two_post fail_rel fun x s h => WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [exec_li]; exact ⟨_, rfl⟩)
    (by rfl) (by rfl)) fun _ ⟨_, k⟩ => (k.gpr (by decide)).trans h.1.1.s6

/-- A failed check reaches `CF`. -/
theorem fail_CF {Φ : DD → State → Prop} (hb : ∀ x s, Φ x s → DBase x s) :
    RelCT isa (Two Φ) (.block [.li .a0 0]) (Two CF) :=
  two_post fail_rel fun x s h => WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [exec_li]; exact ⟨_, rfl⟩)
    (by rfl) (by rfl)) fun _ ⟨_, k⟩ => (k.gpr (by decide)).trans (hb x s h).s6

/-- The subgroup check of `v x`, from `PV`, reaches `CF`. -/
theorem subgroup_rel {Φ : DD → State → Prop} (v : DD → Nat)
    (h : ∀ x s, Φ x s → PV x s ∧ wordsVal s.mem x.S (slot x.w 4) x.w = v x ∧ x.L = 3 * x.k) :
    RelCT isa (Two Φ) subgroup (Two CF) := by
  unfold subgroup
  have pinsSG : Pins (fun x s => SG1 x (v x) s ∧ x.L = 3 * x.k) (.s9 :: .s10 :: dbaseRegs) :=
    pins_cons (pins_one .s9 (fun x => off x.D (2 * x.k)) fun _ _ h => h.1.2.2.2.2.1)
      (pins_cons (pins_one .s10 (fun x => BitVec.ofNat 64 x.k) fun _ _ h => h.1.2.2.2.2.2)
        (pins_base id fun _ _ h => h.1.1.1))
  have pinsPW : Pins (fun x s => PV x s ∧ wordsVal s.mem x.S (slot x.w 4) x.w = v x ^ x.q % x.p) dbaseRegs :=
    pins_base id fun _ _ h => h.1.1
  refine RelCT.seq (two_post (sg1_rel (pins_base id fun _ _ g => (h _ _ g).1.1)) fun x s g =>
    WP.mono (sg1_ok (h x s g).1 (h x s g).2.1) fun _ k => ⟨k.1, (h x s g).2.2⟩) (RelCT.seq
      (two_post (powWin_rel pinsSG) fun x s g => WP.mono (sg2_ok g.1 g.2) fun _ k => k.1)
      (two_post (isOne_rel pinsPW) fun x s g => WP.mono (isOne_ok g.1 g.2) fun _ k => k.1.1.s6))

end VG.Proof.Ffdh.RISCV64.Domain
