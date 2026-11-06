module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct
import VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rc2.X86.KeyLit
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86

def wideContract (d : Spec.Rc2.Direction) : Contract isa :=
  { contract d with
    pre := fun s =>
    let key : Region := ⟨addr32 (arg s 0), 128⟩
    let iv : Region := ⟨addr32 (arg s 1), 8⟩
    let data : Region := ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩
    let buf : Region := ⟨addr32 (arg s 4), 512⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key] ∧ s.wr = [iv, data, buf, args] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region :=
  [⟨addr32 (arg s 0), 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨addr32 (arg s 1), 8⟩, ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩, ⟨addr32 (arg s 4), 512⟩]

tactic_template "rc2_cbc_narrow" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [VG.Proof.Rc2.X86.Cbc.contract, VG.Proof.Rc2.X86.Cbc.wideContract,
                     VG.Proof.Rc2.X86.Cbc.narrowRd, VG.Proof.Rc2.X86.Cbc.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)
tactic_template "rc2_cbc_narrow" : tactic => `(tactic| rc2_cbc_narrow at ⊢)

end VG.Proof.Rc2.X86.Cbc
