module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.ABI
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-! Concrete small-modulus witnesses satisfy both helper contracts. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic

def satMem (n e : Nat) (a : Addr) : Byte :=
  let p := a.toNat
  if 0xf0000004≤p ∧ p<0xf0000008 then BitVec.ofNat 8 (0x10000/256^(p-0xf0000004))
  else if 0xf0000008≤p ∧ p<0xf000000c then BitVec.ofNat 8 (((layout n e).size/8)/256^(p-0xf0000008))
  else if p<0x10000 then 0
  else let o := p-0x10000
    if o=slot n 0 then 3
    else if o=slot n 5 then 1
    else if context n≤o ∧ o<context n+272*n ∧ (o-context n)%(8*n)=0 then
      if o=context n then 3 else 1
    else 0

def satState (n e : Nat) : State where
  gpr r := if r=.esp then 0xf0000000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem n e
  rd := [⟨0xf0000004,8⟩]
  wr := [⟨0x10000,(layout n e).size⟩]

theorem satisfiable {n e : Nat} (supported : Supported n e) (prepare : Bool) :
    ∃ s, (contract prepare n e).pre s := by
  refine ⟨satState n e,?_⟩
  have valid := layout_valid supported
  rcases supported with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases prepare
  all_goals
    sig_pre [contract,Spec.Dsa.FixedBaseComb.prepareContract,Spec.Dsa.FixedBaseComb.powerContract,
      Spec.Dsa.FixedBaseComb.arithmeticPre,Spec.Dsa.ModPow.sig,layout,VG.Impl.Dsa.X86.Pow.layout,
      abi,argSlots,argVal,argBytes,stackBelow]
    sig_and_intros
  all_goals try exact Region.disjoint_of_sep (by decide)
  all_goals try exact valid
  all_goals try unfold Spec.Dsa.FixedBaseComb.contextAt
  all_goals decide +kernel

end VG.Proof.Dsa.X86.Comb
