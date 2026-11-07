module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI

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
  exact WP.call_sp_mx S.verified.1 (SpSafe.of_all S.sp) (by omega) hp hr hw
    (fun _ hrd hwr hcs hf _ hpost hmx => ⟨hrd, hwr, hcs, hf, hpost, hmx⟩)

end VG.Proof.Dsa.X86_64
