module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Init
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Arithmetic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

theorem only_vchg {s s' : State} {rs : List VReg} (h : VChg rs s s')
    (hp : ∀ r ∈ preservedV, r ∉ rs := by decide +kernel) : Only [] s s' :=
  ⟨fun _ _ => congrFun h.gpr _, h.mem, h.rd, h.wr, h.sp,
    fun r hr => by rw [h.get r (hp r hr)]⟩

def compute (terms : List (Nat × Nat)) : List Instr :=
  clear ++ terms.flatMap Impl.MlKem.AArch64.Dot.dotTerm ++ [.ldrq .v18 .x3 0] ++ finish

theorem compute_ok {s : State} (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat}
    (hc : VConsts s) (hn : terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInput s fg (F fg) (G fg))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16)
    (hg : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 0) 16) Γ)
    (bg : ∀ e < 4, Γ e < 3329) :
    WP isa (.block (compute terms)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧
      Lanes (s'.v .v21) (fun e => ((sumTerms terms F G zeroSums e).even +
        (sumTerms terms F G zeroSums e).odd * Γ e) % 3329) ∧
      Lanes (s'.v .v23) (fun e => (sumTerms terms F G zeroSums e).cross % 3329) := by
  simp only [compute, List.append_assoc]
  refine clear_ok fun s₁ h₁ a₁ => ?_
  have k₁ := only_vchg h₁
  have input₁ : ∀ fg ∈ terms, TermInput s₁ fg (F fg) (G fg) :=
    fun fg hf => (hin fg hf).keep (k₁.mono (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (terms_ok terms (hc.chg h₁) a₁
    (n := 0) (fun _ _ => by simp only [zeroSums, Sums.Bounded]; decide)
    (by simpa only [Nat.zero_add] using hn) input₁) fun s₂ ⟨k₂,c₂,a₂⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) rfl
    (by rw [k₂.rd,k₂.wr,k₁.rd,k₁.wr,k₂.get .x3,k₁.get .x3]; exact hr) fun s₃ h₃ => ?_
  have g₃ : Lanes (s₃.v .v18) Γ := by
    rw [h₃.v,k₂.mem,k₁.mem,k₂.get .x3,k₁.get .x3]; exact hg
  have ab : ∀ e < 4, (sumTerms terms F G zeroSums e).Bounded terms.length := by
    simpa only [Nat.zero_add] using sumTerms_bound terms (n := 0)
      (a := zeroSums) (fun _ _ => by simp only [zeroSums, Sums.Bounded]; decide)
      (fun fg hf => (hin fg hf).boundF) (fun fg hf => (hin fg hf).boundG)
  have a₃ : Accum s₃ (sumTerms terms F G zeroSums) := by
    refine ⟨?_,?_,?_⟩
    · rw [h₃.get .v21]; exact a₂.1
    · rw [h₃.get .v22]; exact a₂.2.1
    · rw [h₃.get .v23]; exact a₂.2.2
  rw [← List.append_nil finish]
  refine finish_ok (c₂.chg h₃.chg) a₃.1 a₃.2.1 a₃.2.2 g₃
    (fun e he => ((ab e he).machine hn).1)
    (fun e he => ((ab e he).machine hn).2.1)
    (fun e he => ((ab e he).machine hn).2.2) bg fun s₄ h₄ l₁ l₂ => wp_nil ?_
  exact ⟨(((k₁.trans k₂).trans (only_vchg h₃.chg)).trans (only_vchg h₄)).mono (by simp),
    (c₂.chg h₃.chg).chg h₄, l₁, l₂⟩

end VG.Proof.MlKem.AArch64.Dot
