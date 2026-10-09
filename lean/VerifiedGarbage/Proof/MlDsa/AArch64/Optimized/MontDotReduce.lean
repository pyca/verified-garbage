import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotTerms
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- The selected five-instruction REDC and two-instruction correction produce
canonical Montgomery residues, including zero and values just above q. -/
theorem canonicalReduce_ok (p : Nat→BitVec 64) {s : State}
    (a₁ : s.v .v2=ofVDwords (p 0) (p 1)) (a₂ : s.v .v3=ofVDwords (p 2) (p 3))
    (hq : s.v .v16=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (hp : ∀e<4,(p e).toNat<q*2^32)
    {rest : List Instr} {Q : State→Prop}
    (next : ∀t,VChg [.v0,.v2,.v3,.v4] s t →
      Lanes (t.v .v0) (fun e=>mont (p e).toNat%q) → WP isa (.block rest) t Q) :
    WP isa (.block (reduce .v0++Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4++rest)) s Q := by
  rw [List.append_assoc]
  refine reduce_ok p a₁ a₂ hq hqi fun a ha hv=>?_
  have hqa : Lanes (a.v .v16) (fun _=>q) := by
    rw [ha.get .v16 (by decide),hq]
    intro e he
    rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl <;> rfl
  have hl : Lanes (a.v .v0) (fun e=>mont (p e).toNat) := by
    rw [hv]
    intro e he
    have hr := redc_nat (p e) (hp e he)
    rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl <;>
      simpa only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3] using hr
  refine csub_ok (by decide) hqa hl (fun e he=>mont_lt (hp e he)) fun t ht hval=>?_
  exact next t ((ha.trans ht).mono (by simp)) hval

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
