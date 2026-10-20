module

public import VerifiedGarbage.Proof.Bignum.X86.CrtStackSafety
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Verified
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Impl.Bignum.X86.CrtRt
import VerifiedGarbage.Impl.Bignum.X86.PrecomputedRt

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
  stack := by decide +kernel
  noSp := NoSp.of_all (by decide +kernel)
  pcName := "vg_rsa_public_precompute"
  pc := Impl.Bignum.X86.PrecomputeFn.code
  pcVerified := Bignum.X86.precompute_verified
  pcStack := by decide +kernel
  pcNoSp := NoSp.of_all (by decide +kernel)
  pdName := "vg_rsa_public_precomputed_checked"
  pd := Impl.Bignum.X86.PrecomputedRt.code
  pdVerified := Bignum.X86.PrecomputedRt.verified
  pdStack := by decide +kernel
  pdNoSp := NoSp.of_all (by decide +kernel)

end VG.Proof.Rsa.X86.PrivChecked
