module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeLayout
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generate
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawArguments
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawWitness
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo

/-! # Witness copying depends only on public tape pointers and consumption -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def DrawAt (p : PrimeConfig × Nat) (s : State) : Prop :=
  PrimeReady p.1 s ∧ s.mem.readW (off p.1.base primeUsed) 32 = BitVec.ofNat 32 p.2

def DrawPointers (len draw : Nat) (p : PrimeConfig × Nat) (s : State) : Prop :=
  (s.gpr .edi).toNat = p.1.base.toNat ∧
    s.gpr .esi = p.1.tape + BitVec.ofNat 32 (p.2 + (draw - len)) ∧
    s.gpr .edx = p.1.witness ∧ s.gpr .ecx = BitVec.ofNat 32 len

theorem drawWitness_ct (len draw : Nat) : RelCT isa (Two DrawAt) (drawWitness len draw) (fun _ _ => True) := by
  unfold drawWitness
  refine RelCT.seq (two_piece (Ψ := DrawPointers len draw) [.edi] ?_ (hc := .block []) ?_ ?_) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.1.context.scr.edi_toNat.trans ht.1.context.scr.edi_toNat.symm)
  · exact (congrArg Option.isSome (VG.Proof.Mont.X86.Dynamic.check_of_erase_eq
      (.block (drawWitnessArgs len draw)) (.block (drawWitnessArgs 1 1)) (τr [.edi]) (.block []) rfl rfl rfl)).trans (by rfl)
  · intro p s R
    have room : primeWitness + 4 ≤ p.1.size := by have := p.1.room; unfold primeWitness primeExponent at *; omega
    refine WP.mono (drawWitnessArgs_ok (len := len) (draw := draw) R.1.context.scr room R.1.tape R.2 R.1.witness)
      fun t ⟨si, dx, cx, _, _, K⟩ => ?_
    exact ⟨by rw [K.1 _ (by decide)]; exact R.1.context.scr.edi_toNat, si, dx, cx⟩
  · refine two_taint [.edi, .esi, .edx, .ecx] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.1.trans ht.1.symm)
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.1.trans ht.2.2.1.symm
    · exact hs.2.2.2.trans ht.2.2.2.symm
end VG.Proof.Dsa.X86.Generation
