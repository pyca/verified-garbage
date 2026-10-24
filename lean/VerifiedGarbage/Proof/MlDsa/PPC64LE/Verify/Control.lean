module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inv
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Samp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA verification on PPC64LE: two runs, and the branches on the result

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Control.lean`): two runs with the
same layout (`VTwo`), the constant time of a piece without calls by the
taint analysis from the pointers (`vrel31`), what holds throughout kept by
writes of `r3` and `r24` (`VC.regs2`), and `ifOk c`, a branch on the result
so far in `r24` (`ifOk_piece`), which is a function of the public data.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31 taint4
  Regs2)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-- 1 if `b`, 0 if not. -/
def flag (b : Bool) : BitVec 64 := if b then 1 else 0

theorem flag_01 (b : Bool) : flag b = 0 ∨ flag b = 1 := by cases b <;> simp [flag]

theorem flag_ne {b : Bool} : flag b ≠ 0 ↔ b = true := by cases b <;> simp [flag]

theorem vptr_ok {r : Reg} (hr : KeyGen.baseReg r = true) {o : Nat} (h : o < 2 ^ 31) :
    KeyGen.argOk (.ptr (r, o)) = true := by
  simp only [KeyGen.argOk, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hr, h⟩

/-- Proves that an offset into the buffers is below `2³¹`, for any parameter
set with the facts `hF`. -/
syntax "vlt " term:max : tactic
macro_rules
  | `(tactic| vlt $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).w1; have := ($hF).w1l; have := ($hF).pk
      have := ($hF).hint; have := ($hF).ct; have := ($hF).lz
      try dsimp only [VG.Impl.MlDsa.PPC64LE.Verify.oP, VG.Impl.MlDsa.PPC64LE.Verify.oB,
        VG.Impl.MlDsa.PPC64LE.Verify.oSS, VG.Impl.MlDsa.PPC64LE.Verify.oSB, VG.Impl.MlDsa.PPC64LE.Verify.oCT]
      omega))

/-! ## Two runs -/

theorem vc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : vPub p σ₁ σ₂) (h₁ : VC p STK σ₁ x)
    (h₂ : VC p STK σ₂ y) : Two (vlay p STK σ₁) vWb STK x y :=
  ⟨h₁.site, vlay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

/-- Two runs whose entry states have the same layout. -/
def VTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, Two (vlay p STK σ) vWb STK x y

theorem vc_two {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : vPub p σ₁ σ₂) (h₁ : VC p STK σ₁ x)
    (h₂ : VC p STK σ₂ y) : VTwo p STK x y :=
  ⟨σ₁, vc_twoL pub h₁ h₂⟩

theorem vtaint31 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) :
    RelCT isa (VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h

theorem vtaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r28, .r29, .r30, .r31]) c hc).isSome = true) :
    RelCT isa (VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h

/-- A piece without calls, checked by the taint analysis from `scratch`. -/
theorem vrel31 {p : Params} {STK : Nat} {I : State → State → Prop} (hI : ∀ σ s, I σ s → VC p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (VPre p STK) (vPub p) I) c fun _ _ => True :=
  rel_of (vtaint31 h) fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, vc_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-! ## The state, but for `r3` and `r24` -/

theorem VC.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s) (hr : Regs2 s s') :
    VC p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .r3 ∧ r ≠ .r24 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.pk, by rw [hr.mem]; exact h.mu, by rw [hr.mem]; exact h.sg⟩

/-! ## A branch on `r24` -/

/-- `ifOk c`: `c` if `r24 ≠ 0`, where `r24` is `v σ`, a function of the
public data. -/
theorem ifOk_piece {p : Params} {STK : Nat} {I J : State → State → Prop} {c : Prog isa} {v : State → BitVec 64}
    (hv : ∀ σ s, VPre p STK σ → I σ s → s.gpr .r24 = v σ)
    (hpub : ∀ σ₁ σ₂, VPre p STK σ₁ → VPre p STK σ₂ → vPub p σ₁ σ₂ → v σ₁ = v σ₂)
    (hc : VPiece p STK (fun σ s => I σ s ∧ v σ ≠ 0) J c)
    (he : ∀ σ s, VPre p STK σ → I σ s → v σ = 0 → J σ s) :
    VPiece p STK I J (ifOk c) := by
  refine ⟨fun σ s hp hs => ?_, ?_⟩
  · have h24 := hv σ s hp hs
    refine WP.ite _ (eval_nonzero s .r24) (fun hb => hc.ok σ _ hp ⟨hs, ?_⟩) fun hb => ?_
    · rw [← h24]; simpa using hb
    · have : v σ = 0 := by rw [← h24]; simpa using hb
      exact WP.block_nil (he σ _ hp hs this)
  · refine RelCT.ite ?_ ?_ ?_
    · rintro _ _ ⟨σ₁, σ₂, p₁, p₂, pub, hx, hy⟩
      rw [eval_nonzero, eval_nonzero, hv _ _ p₁ hx, hv _ _ p₂ hy, hpub _ _ p₁ p₂ pub]
    · refine RelCT.mono hc.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, hx, hy⟩, hb⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨hx, ?_⟩, ⟨hy, ?_⟩⟩) fun _ _ h => h
      · rw [eval_nonzero] at hb
        rw [← hv _ _ p₁ hx]; simpa using hb
      · rw [eval_nonzero] at hb
        rw [← hpub _ _ p₁ p₂ pub, ← hv _ _ p₁ hx]; simpa using hb
    · exact RelCT.block_nil fun _ _ _ => trivial

end VG.Proof.MlDsa.PPC64LE.Verify
