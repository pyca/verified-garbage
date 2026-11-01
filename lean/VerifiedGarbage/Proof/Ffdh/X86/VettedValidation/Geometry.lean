module

import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainVerified
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainTop
public import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.X86.Target

/-! The original cdecl contract already reserves all input, scratch, and stack resources. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.X86.Wp
open VG.Impl.Ffdh.X86.VettedValidation

def contract := Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts) 172
def plain (s : State) := stripConsts tableConsts s
def domain (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (byteAddr (arg s 0)) (arg s 1).toNat
def scratch (s : State) : Region := ⟨byteAddr (arg s 3), (arg s 4).toNat * 8⟩

theorem plain_arg (s : State) (i : Nat) : arg (plain s) i = arg s i := rfl

theorem plain_argAddr (s : State) (i : Nat) : argAddr (plain s) i = argAddr s i := rfl

theorem pre_plain {s : State} (h : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi 172).pre (plain s) ∧ ConstsOk tableConsts 172 s := pre_consts.mp h

theorem geometry {s : State} (h : contract.pre s) : CheckDomainABI (plain s) :=
  checkDomainABI_of (pre_plain h).1

theorem stack_low {s : State} (h : contract.pre s) : 172 ≤ (s.gpr .esp).toNat := (geometry h).stackLow

theorem stack_bound {s : State} (h : contract.pre s) : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 :=
  (geometry h).stackBound

theorem plain_covers (s : State) : Covers ((plain s).rd ++ (plain s).wr) (s.rd ++ s.wr) :=
  (Covers.of_mem (fun _ h => List.mem_of_mem_take h)).append (Covers.refl _)

theorem read_args {s : State} (h : contract.pre s) : InRegions (s.rd ++ s.wr) (argAddr s 0) 20 := by
  have wr := (geometry h).wr
  change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
  exact ⟨_, List.mem_append_right _ (by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self),
    Region.contains_self _ _⟩

theorem read_domain {s : State} (h : contract.pre s) :
    InRegions (s.rd ++ s.wr) (byteAddr (arg s 0)) (arg s 1).toNat := by
  have rd := (geometry h).rd
  refine (plain_covers s) _ _ ⟨_, List.mem_append_left _ ?_, Region.contains_self _ _⟩
  rw [rd]
  exact List.mem_cons_self

theorem scratch_room {s : State} (h : contract.pre s) : 48 ≤ (scratch s).len := by
  have sizes := (geometry h).pLen
  have space := (geometry h).scratchLength
  change Spec.Rsa.scratchWords (arg s 2).toNat ≤ (arg s 4).toNat at space
  simp only [Spec.Rsa.scratchWords] at space
  change 48 ≤ (arg s 4).toNat * 8
  omega

private theorem singleton_fit {name : String} {words : List (BitVec 64)} {s : State} {st : Nat}
    (h : ConstsOk [(name, words)] st s) :
    (s.syms name).toNat + 8 * words.length ≤ 2 ^ 32 := by
  have fit := (h.2.2.1 ⟨symAddr s name, 8 * words.length⟩ List.mem_cons_self).1
  change (symAddr s name).toNat + 8 * words.length ≤ 2 ^ 32 at fit
  simpa only [symAddr, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (s.syms name).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using fit

theorem table_fit {s : State} (h : contract.pre s) : (s.syms tableSym).toNat + 17744 ≤ 2 ^ 32 := by
  have fit := singleton_fit (pre_plain h).2
  simpa only [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] using fit

end VG.Proof.Ffdh.X86.VettedValidation
