module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# DSA on x86-64, with Montgomery multiplication by calls

`vg_dsa_sign_adx` and `vg_dsa_verify_adx` call `vg_rsa_mont_mul_adx`
(`CallMont`) where they would run its code inline: their code `c` has the
inlined code proven before as `c.inline` (`hin`, which the registration
evaluates), and
`Verified.of_inline` gives it the shared contract with 8 bytes of stack, for
the calls' return address. The baseline's code, without calls, is its own
`c.inline`.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64

open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem signingSatisfiable8 : ∃ s, (Spec.Dsa.signContract abi 8).pre s := by
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
    [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem verifyingSatisfiable8 : ∃ s, (Spec.Dsa.verifyContract abi 8).pre s := by
  sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
    [verifyingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifyingSatState

theorem sign_implies8 : (Spec.Dsa.signContract abi).Implies (Spec.Dsa.signContract abi 8) :=
  (Contract.Implies.refl signingSatisfiable).stack8_abi signingSatisfiable8

theorem verify_implies8 : (Spec.Dsa.verifyContract abi).Implies (Spec.Dsa.verifyContract abi 8) :=
  (Contract.Implies.refl verifyingSatisfiable).stack8_abi verifyingSatisfiable8

/-- The signature's output is apart from the calls' return address. -/
theorem sign_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : (Spec.Dsa.signContract abi 8).pre s)
    (hp : (Spec.Dsa.signContract abi).post s b) :
    (Spec.Dsa.signContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have ha := signingABI_of (Sig.pre_stack0_abi hs)
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [ha.wr]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp ⊢
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rw [show Spec.Rsa.bytesAt (overlay (hole (s.gpr .rsp)) hv b.mem) (s.gpr .rdi) (s.gpr .rsi).toNat =
    Spec.Rsa.bytesAt b.mem (s.gpr .rdi) (s.gpr .rsi).toNat from bytes_patch (u := u) hb]
  exact hp.2

/-- Verification's postcondition reads no memory it writes. -/
theorem verify_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (_ : (Spec.Dsa.verifyContract abi 8).pre s)
    (hp : (Spec.Dsa.verifyContract abi).post s b) :
    (Spec.Dsa.verifyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at hp ⊢
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at hp ⊢
  exact hp

theorem signing_call_verified (mm : Nat → Nat → Nat → Prog isa) (M : Mont)
    (hc : (SignVerify.sign mm).InlineOk = true) (hin : (SignVerify.sign mm).inline = SignVerify.sign M.mm)
    (hmx : (SignVerify.sign M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (SignVerify.sign mm) (Spec.Dsa.signContract abi 8) :=
  Verified.of_inline hc (hin ▸ signingCorrect M hmx) (hin ▸ signingConstantTime M) sign_implies8
    (fun _ h => Sig.clear_of_pre h) sign_patch (fun _ _ _ _ h => Sig.rsp_of_pub h)

theorem verifying_call_verified (mm : Nat → Nat → Nat → Prog isa) (M : Mont)
    (hc : (SignVerify.verify mm).InlineOk = true) (hin : (SignVerify.verify mm).inline = SignVerify.verify M.mm)
    (hmx : (SignVerify.verify M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (SignVerify.verify mm) (Spec.Dsa.verifyContract abi 8) :=
  Verified.of_inline hc (hin ▸ verifyingCorrect M hmx) (hin ▸ verifyingConstantTime M) verify_implies8
    (fun _ h => Sig.clear_of_pre h) verify_patch (fun _ _ _ _ h => Sig.rsp_of_pub h)

end VG.Proof.Dsa.X86_64
