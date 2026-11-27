module

public import VerifiedGarbage.Impl.Aes.X86.Callee
public import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
public import VerifiedGarbage.Proof.Aes.X86.ExpandKeyCT
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.ScrubSide

/-! Contracts and execution properties that every x86 AES variant supplies to callers. -/

@[expose] public section

namespace VG.Proof.Aes.X86
open VG.X86
/-- The contracts of an implementation of `vg_aes_ctr32_to` with a scratch
buffer of `B` bytes (`ctr32X86N`, `ctr32ToX86N`): what a caller that sets
aside no more for it calls it with. -/
structure Ctr32With (code : Prog isa) (B : Nat) : Prop where
  ok : ∀ s, (Proof.Aes.ctr32X86N B).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.ctr32X86N B).post s s'
  ct : ConstantTime isa (Proof.Aes.ctr32X86N B).pre (Proof.Aes.ctr32X86N B).pub code
  okTo : ∀ s, (Proof.Aes.ctr32ToX86N B).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.ctr32ToX86N B).post s s'
  ctTo : ConstantTime isa (Proof.Aes.ctr32ToX86N B).pre (Proof.Aes.ctr32ToX86N B).pub code

structure Ctr32Impl where
  callee : Impl.Aes.X86.Ctr32
  depth : stackUse callee.code = 0
  stack : stackUse callee.code = 0
  ok : ∀ s, Proof.Aes.ctr32X86.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86.post s s'
  ct : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub callee.code
  nosp : NoSp callee.code
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- Its code, and the code it calls, has no MMX instruction and makes no indirect call (`calleeOk`):
  what the cleanup of every function that calls it needs of it, with its
  stack (`X86.Scrub.calleeSide`), so that each proves only its own
  code, whatever the implementation (`Proof/Framework/X86/ScrubCall.lean`). -/
  scrub : calleeOk callee.code = true
  suffix : String
  features : List String
  /-- The same code out of place. -/
  okTo : ∀ s, Proof.Aes.ctr32ToX86.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32ToX86.post s s'
  ctTo : ConstantTime isa Proof.Aes.ctr32ToX86.pre Proof.Aes.ctr32ToX86.pub callee.code
  /-- How much of its scratch buffer it uses: all 2048 bytes, or fewer if it
  gives its contracts with them (`small`), for the callers whose frame holds
  no more for it (AES-GCM's, `Proof/AesGcm/X86/Callee.lean`), which then wipe
  no more on return. -/
  scr : Nat := 2048
  scr_le : scr ≤ 2048 := by decide
  small : Ctr32With callee.code scr
  expand : Impl.Aes.X86.ExpandKey
  expandDepth : stackUse expand.code = 0
  expandStack : stackUse expand.code = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86.pre Proof.Aes.expandKeyX86.pub expand.code
  expandNosp : NoSp expand.code
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true
  /-- `scrub`, of `expand`. -/
  expandScrub : calleeOk expand.code = true
end VG.Proof.Aes.X86
