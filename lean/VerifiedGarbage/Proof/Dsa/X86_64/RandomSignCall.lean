module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.ModeSim
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
public import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.X86_64.SigningABI`, which this module and modules that import it used -/

section

/-! # The signing ABI and its shared-contract precondition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

structure SigningABI (s : State) : Prop where
  stackBound : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  keyScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  nonceScratch : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  digestScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  scratchArgs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  keyBound : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  nonceBound : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  digestBound : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r8).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 2 * (stackArg s 0).toNat
  keyLength : (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat + 2 * (stackArg s 0).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 4).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
  sig_split h
  constructor <;> with_reducible assumption

def SigningABI.input {s : State} (h : SigningABI s) : SigningInput where
  base := stackArg s 3
  digestPointer := stackArg s 1
  pLen := (s.gpr .r8).toNat
  qLen := (stackArg s 0).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  nonce := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
  digest := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  nonceLength := bytesAt_length _ _ _
  digestBound := by rw [bytesAt_length]; exact (stackArg s 2).isLt

theorem SigningABI.used {s : State} (h : SigningABI s) : usedBytes ≤ (stackArg s 4).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

end VG.Proof.Dsa.X86_64

end

end

/-! Call any registered supplied-nonce signer, retaining its contract and frame. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64

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
  depth : code.x86_64Depth ≤ stack
  stackBound : stack < 2 ^ 32
  noMx : code.allInstrs (fun i => !touchesMxcsr i) = true

theorem signWith_pre {valid : Nat → Nat → List Byte → Bool} {s : State} {stack : Nat}
    (h : (signContractWith valid abi stack).pre s) :
    (Spec.Dsa.signContract abi stack).pre s ∧
      valid (s.gpr .r8).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true := by
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  sig_and_intros <;> with_reducible assumption

theorem signWith_of_pre {valid : Nat → Nat → List Byte → Bool} {s : State} {stack : Nat}
    (h : (Spec.Dsa.signContract abi stack).pre s)
    (hv : valid (s.gpr .r8).toNat (stackArg s 0).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true) :
    (signContractWith valid abi stack).pre s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
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
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame (wr ++ [below (s.gpr .rsp) (S.code.x86_64Depth + 8)]) s.mem t.mem ∧
      (∃ u : State, u.mem = t.mem ∧ (∀ r, r ≠ .rsp → u.gpr r = t.gpr r) ∧
        (signContractWith S.valid abi S.stack).post (s.callEntry.withRegions rd wr) u) ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hd := S.depth
  have hb := S.stackBound
  exact WP.call_sp_mx S.verified.1 (SpSafe.of_all S.sp) (by omega_using [hd, hb]) hp hr hw
    (fun _ hrd hwr hcs hf _ hpost hmx => ⟨hrd, hwr, hcs, hf, hpost, hmx⟩)

end VG.Proof.Dsa.X86_64
