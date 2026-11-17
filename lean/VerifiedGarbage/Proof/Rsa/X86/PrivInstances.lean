module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86.RtShape
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.TCB.X86.Isa
public import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.TimeTop
public import VerifiedGarbage.Proof.Rsa.Contract

/-! ### `Bignum.X86.PrecomputedRt.Verified`, which this module and modules that import it used -/

section

/-! # Precomputed public RSA at a run-time width on i686 against its contract

Correctness (`correct`), constant time (`constantTime`), and a state meeting
the precondition, with 40 bytes of stack below `esp` for the calls.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.Impl.Bignum.X86

/-- Disjoint 512-bit buffers; the zero-valued packed key is rejected at runtime. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 64 else if a = 0x2000d then 32
    else if a = 0x20010 then 16 else if a = 0x20015 then 48 else if a = 0x20018 then 1
    else if a = 0x2001d then 64 else if a = 0x20020 then 64 else if a = 0x20025 then 128
    else if a = 0x20028 then 128 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1024⟩, ⟨0x20004, 40⟩]

theorem satisfiable : ∃ s, (Proof.Rsa.publicPrecomputedCheckedContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 16 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 64 := by decide
  have a8 : arg satState 8 = 32768 := by decide
  have a9 : arg satState 9 = 128 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp, satState, Spec.Rsa.lenValid,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords] using satState

theorem verified : Verified target PrecomputedRt.code (Proof.Rsa.publicPrecomputedCheckedContract abi 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Bignum.X86.PrecomputedRt

end

end

/-! # Instantiate checked private RSA with the verified baseline i686 callees -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86

theorem allStack_noSp {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) : NoSp c := by
  have instr : ∀ i : Instr, (!isa.writesSp i) = !Taint.clobbers i .esp := by
    intro i
    cases i <;> rfl
  have eq : c.all (fun i => !isa.writesSp i) = c.allInstrs (fun i => !Taint.clobbers i .esp) := by
    clear h
    induction c with
    | icall x _ b n hb hn =>
      simp only [Code.all, Code.allInstrs]
      rw [hb, hn, instr]
    | block is =>
      induction is with
      | nil => rfl
      | cons i is ih =>
        change ((!isa.writesSp i) && Code.all (fun j => !isa.writesSp j) ((.block is) : Prog isa)) =
          ((!Taint.clobbers i .esp) && Code.allInstrs (fun j => !Taint.clobbers j .esp) ((.block is) : Prog isa))
        rw [instr, ih]
    | seq a b ha hb | ite cc a b ha hb => simp only [Code.all, Code.allInstrs, ha, hb]
    | loop b cc hb | call n b hb => exact hb
    | frame i b j hb =>
      simp only [Code.all, Code.allInstrs]
      rw [hb, instr, instr]
  exact NoSp.of_all (eq ▸ h)

def baseline : CrtImpl where
  name := "vg_rsa_private_crt"
  code := Impl.Bignum.X86.CrtRt.code
  verified := Bignum.X86.CrtRt.verified
  stack := by rw [RtShape.privateCrt_stack]
  noSp := allStack_noSp RtShape.privateCrt_spSafe
  pcName := "vg_rsa_public_precompute"
  pc := Impl.Bignum.X86.PrecomputeFn.code
  pcVerified := Bignum.X86.precompute_verified
  pcStack := by decide +kernel
  pcNoSp := NoSp.of_all (by decide +kernel)
  pdName := "vg_rsa_public_precomputed_checked"
  pd := Impl.Bignum.X86.PrecomputedRt.code
  pdVerified := Bignum.X86.PrecomputedRt.verified
  pdStack := by rw [RtShape.precomputed_stack]
  pdNoSp := allStack_noSp RtShape.precomputed_spSafe

end VG.Proof.Rsa.X86.PrivChecked
