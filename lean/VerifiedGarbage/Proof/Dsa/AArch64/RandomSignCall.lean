module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.AArch64.ModeSim
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInput
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.Octets
public import Mathlib.Algebra.Group.Nat.Defs

/-! ### `Dsa.AArch64.SigningABI`, which this module and modules that import it used -/

section

/-! # The signing ABI and its shared-contract precondition -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem dsaSignStackArgs (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

structure SigningABI (s : State) : Prop where
  stackBound : s.sp.toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x5, (s.gpr .x6).toNat⟩,
    ⟨s.gpr .x7, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 24⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  keyScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  nonceScratch : (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  digestScratch : (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  scratchArgs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩
  outBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  keyBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  nonceBound : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  digestBound : (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x4).toNat (s.gpr .x6).toNat
  outLength : (s.gpr .x1).toNat = 2 * (s.gpr .x6).toNat
  keyLength : (s.gpr .x3).toNat = 3 * (s.gpr .x4).toNat + 2 * (s.gpr .x6).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 2).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

def SigningABI.input {s : State} (h : SigningABI s) : SigningInput where
  base := stackArg s 1
  digestPointer := s.gpr .x7
  pLen := (s.gpr .x4).toNat
  qLen := (s.gpr .x6).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  nonce := Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
  digest := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  nonceLength := bytesAt_length _ _ _
  digestBound := by rw [bytesAt_length]; exact (stackArg s 0).isLt

theorem SigningABI.used {s : State} (h : SigningABI s) : usedBytes ≤ (stackArg s 2).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

end VG.Proof.Dsa.AArch64

end

end

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
  noDit : code.all (fun i => !i.touchesDit) = true

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
  refine WP.callFV S.verified.1 hp hr hw (fun t hrd hwr hsp hf hcs hv hp => ?_) (by omega_using [hd, hb])
  exact ⟨hrd, hwr, hsp, hcs, Frame.below_mono hf hd (by omega_using [hb]), hp, hv⟩

end VG.Proof.Dsa.AArch64
