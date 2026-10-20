module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Gather
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Accumulate
public import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def termCore : List Instr := loads ++ gather ++ accumulate
abbrev termClob : List VReg := [.v0, .v1, .v4, .v5, .v6, .v7, .v19, .v20, .v21, .v22, .v23]

theorem termCore_ok {rest : List Instr} {s : State} {Q : State → Prop}
    {F G A B C : Nat → Nat}
    (hrf : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16)
    (hrg : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16*i)) 16)
    (hf : ∀ e < 8, (coeffAt s.mem (s.gpr .x1) e).toNat = F e)
    (hg : ∀ e < 8, (coeffAt s.mem (s.gpr .x2) e).toNat = G e)
    (ha : Lanes (s.v .v21) A) (hb : Lanes (s.v .v22) B) (hc : Lanes (s.v .v23) C)
    (ba : ∀ e < 4, A e + F (2*e) * G (2*e) < 2 ^ 32)
    (bb : ∀ e < 4, B e + F (2*e+1) * G (2*e+1) < 2 ^ 32)
    (bc : ∀ e < 4, C e + F (2*e) * G (2*e+1) + F (2*e+1) * G (2*e) < 2 ^ 32)
    (k : ∀ s', VChg termClob s s' →
      Lanes (s'.v .v21) (fun e => A e + F (2*e) * G (2*e)) →
      Lanes (s'.v .v22) (fun e => B e + F (2*e+1) * G (2*e+1)) →
      Lanes (s'.v .v23) (fun e => C e + F (2*e) * G (2*e+1) + F (2*e+1) * G (2*e)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (termCore ++ rest)) s Q := by
  simp only [termCore, List.append_assoc]
  refine loads_ok hrf hrg fun s₁ h₁ l0 l1 l4 l5 => ?_
  have f0 : Lanes (s₁.v .v0) F := by
    rw [l0]
    simpa only [coeffAddr, Nat.mul_zero, BitVec.add_zero] using
      (lanes_coeffs (m := s.mem) (p := s.gpr .x1) (j := 0) (A := F) (fun e he => by simpa only [Nat.zero_add] using hf e (by omega)))
  have f1 : Lanes (s₁.v .v1) (fun e => F (4+e)) := by
    rw [l1]
    exact lanes_coeffs (m := s.mem) (p := s.gpr .x1) (j := 4) (fun e he => hf (4+e) (by omega))
  have g0 : Lanes (s₁.v .v4) G := by
    rw [l4]
    simpa only [coeffAddr, Nat.mul_zero, BitVec.add_zero] using
      (lanes_coeffs (m := s.mem) (p := s.gpr .x2) (j := 0) (A := G) (fun e he => by simpa only [Nat.zero_add] using hg e (by omega)))
  have g1 : Lanes (s₁.v .v5) (fun e => G (4+e)) := by
    rw [l5]
    exact lanes_coeffs (m := s.mem) (p := s.gpr .x2) (j := 4) (fun e he => hg (4+e) (by omega))
  refine gather_ok f0 f1 g0 g1 fun s₂ h₂ fe fo ge go => ?_
  have a₂ : Lanes (s₂.v .v21) A := by rw [h₂.get .v21, h₁.get .v21]; exact ha
  have b₂ : Lanes (s₂.v .v22) B := by rw [h₂.get .v22, h₁.get .v22]; exact hb
  have c₂ : Lanes (s₂.v .v23) C := by rw [h₂.get .v23, h₁.get .v23]; exact hc
  refine accumulate_ok a₂ b₂ c₂ fe fo ge go ba bb bc fun s₃ h₃ a₃ b₃ c₃ => ?_
  exact k s₃ ((h₁.trans h₂).trans h₃).mono a₃ b₃ c₃

end VG.Proof.MlKem.AArch64.Dot
