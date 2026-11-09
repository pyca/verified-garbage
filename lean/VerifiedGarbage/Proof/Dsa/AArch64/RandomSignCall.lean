module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningABI
import VerifiedGarbage.Proof.Framework.Omega

/-! Call any registered supplied-nonce signer, retaining its contract and frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def randomSignerName (v : Backend) : String := "vg_dsa_sign" ++ v.suffix

/-- A supplied-nonce signer the randomized wrapper calls: the fully checked
signer of a backend (`valid` always true), or its signer for a validated
private key (`valid` is `validatePrivateKeyBytes`). It is verified against
`signContract` under `valid` of the exact key bytes it is called with. -/
structure Signer where
  name : String
  code : Prog isa
  stack : Nat
  valid : Nat → Nat → List Byte → Bool
  verified : Verified target code (signContractWith valid abi stack)
  sp : code.all (fun i => !isa.writesSp i) = true
  depth : 16 * code.aarch64Depth ≤ stack
  stackBound : stack < 2 ^ 32

theorem signWith_pre {valid : Nat → Nat → List Byte → Bool} {s : State} {stack : Nat}
    (h : (signContractWith valid abi stack).pre s) :
    (Spec.Dsa.signContract abi stack).pre s ∧
      valid (s.gpr .x4).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) = true := by
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_and_intros <;> with_reducible assumption

theorem signWith_of_pre {valid : Nat → Nat → List Byte → Bool} {s : State} {stack : Nat}
    (h : (Spec.Dsa.signContract abi stack).pre s)
    (hv : valid (s.gpr .x4).toNat (s.gpr .x6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) = true) :
    (signContractWith valid abi stack).pre s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem signWith_post {valid : Nat → Nat → List Byte → Bool} {s t : State} {stack : Nat}
    (h : (Spec.Dsa.signContract abi stack).post s t) : (signContractWith valid abi stack).post s t := h

theorem signWith_post' {valid : Nat → Nat → List Byte → Bool} {s t : State} {stack : Nat}
    (h : (signContractWith valid abi stack).post s t) : (Spec.Dsa.signContract abi stack).post s t := h

theorem signWith_pub {valid : Nat → Nat → List Byte → Bool} {s t : State} {stack : Nat}
    (h : (signContractWith valid abi stack).pub s t) : (Spec.Dsa.signContract abi stack).pub s t := h

theorem signWith_pub' {valid : Nat → Nat → List Byte → Bool} {s t : State} {stack : Nat}
    (h : (Spec.Dsa.signContract abi stack).pub s t) : (signContractWith valid abi stack).pub s t := h

theorem random_signer_call (S : Signer) {s : State} {rd wr : List Region}
    (hp : (signContractWith S.valid abi S.stack).pre (s.callEntry.withRegions rd wr))
    (hr : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.call S.name S.code) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧
      Frame (wr ++ [below s.sp S.stack]) s.mem t.mem ∧
      (signContractWith S.valid abi S.stack).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  have hd := S.depth
  have hb := S.stackBound
  refine WP.callFV S.verified.1 hp hr hw (fun t hrd hwr hsp hf hcs hv hp => ?_) (by omega)
  exact ⟨hrd, hwr, hsp, hcs, Frame.below_mono hf hd (by omega), hp, hv⟩

end VG.Proof.Dsa.AArch64
