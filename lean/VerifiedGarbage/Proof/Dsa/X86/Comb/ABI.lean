module


import VerifiedGarbage.Proof.Dsa.X86.Comb.BodyWide
public import VerifiedGarbage.Proof.Dsa.X86.PowABI
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core

/-! The merged comb contracts provide the ordinary DSA calling resources. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 numAt_eq4)

def contract (prepare : Bool) (n e : Nat) : Contract isa :=
  if prepare then Proof.Dsa.FixedBaseComb.prepareContract (layout n e) abi 20
  else Proof.Dsa.FixedBaseComb.powerContract (layout n e) abi 20

theorem abi_of {n e : Nat} {s : State} (supported : Supported n e) (prepare : Bool)
    (h : (contract prepare n e).pre s) :
    Pow.ABI n e s ∧ (layout n e).size≤bytes s ∧
    (prepare=false → canonical n e
      (wordsVal s.mem (ws s) (slot n 0) n) (wordsVal s.mem (ws s) (slot n 5) n) (ws s) s.mem) := by
  have sz : contextBytes n≤(layout n e).size := by
    rcases supported with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  change contextBytes n≤context n+272*n at sz
  cases prepare
  all_goals
    sig_pre [contract,Proof.Dsa.FixedBaseComb.prepareContract,Proof.Dsa.FixedBaseComb.powerContract,
      Proof.Dsa.FixedBaseComb.arithmeticPre,Proof.Dsa.ModPow.sig,layout,VG.Impl.Dsa.X86.Pow.layout,
      abi,argSlots,argVal,argBytes,stackBelow] at h
    sig_split h
    refine ⟨?_,?_,?_⟩
    · constructor <;> try with_reducible assumption
      all_goals dsimp only [bytes]; omega
    · change context n+272*n≤(arg s 1).toNat*8
      omega
  · intro _
    unfold canonical
    simpa only [Proof.Dsa.FixedBaseComb.contextAt,layout,VG.Impl.Dsa.X86.Pow.layout,numAt_eq8] using h
  · intro eq; cases eq

end VG.Proof.Dsa.X86.Comb
