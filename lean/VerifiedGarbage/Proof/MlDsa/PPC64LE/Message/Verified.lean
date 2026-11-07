module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.VerifyCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds

/-!
# ML-DSA on PPC64LE, `sign_message` and `verify_message_cached`: their contracts

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message_cached` meet their
contracts with `S` bytes of stack, for any verified function on `μ` with at
most `S` bytes of stack (at least the 48 the sponge functions' frames take):
by correctness (`signMessage_wp`, `verifyMessageCached_wp`) and constant time
(`signMessage_ct`, `verifyMessageCached_ct`). The contracts' satisfiability
(by `msSat`, `mcSat`) is evaluated once
`S` is known; `mcSat` holds `tr = H(pk, 64)` of its key (`mcSat_digest`),
which is not evaluated.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Message
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A state that satisfies `signMessageContract`'s precondition. -/
def msSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x8000 | .r6 => 0x9000 | .r8 => 0xA000 | .r9 => 0xB000 | .r10 => 0x20000
    | _ => 0
  lr := 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, 32⟩]
  wr := [⟨0xB000, p.sigLen⟩, ⟨0x20000, messageScratchWords p * 8⟩]

/-- The memory of a state that satisfies `verifyMessageCachedContract`'s
precondition: zeros, but `tr = H(pk, 64)` of the zeros at `0x1000` at
`0xC000`. -/
def mcSatMem (p : Params) : Mem := fun a =>
  if 0xC000 ≤ a.toNat ∧ a.toNat < 0xC040 then
    (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0xC000) 0
  else 0

/-- A state that satisfies `verifyMessageCachedContract`'s precondition. -/
def mcSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x8000 | .r6 => 0x9000 | .r8 => 0xA000 | .r9 => 0x20000 | .r10 => 0xC000
    | _ => 0
  lr := 0
  sp := 0x100000
  mem := mcSatMem p
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, p.sigLen⟩, ⟨0xC000, 64⟩]
  wr := [⟨0x20000, messageScratchWords p * 8⟩]

theorem mcSat_key {p : Params} (hp : p.pkLen < 0xB000) :
    bytesAt (mcSatMem p) 0x1000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x1000 : Addr) + BitVec.ofNat 64 i).toNat = 0x1000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [mcSatMem, he]
  split
  · omega
  · rfl

theorem mcSat_digest {p : Params} (hp : p.pkLen < 0xB000) :
    bytesAt (mcSat p).mem 0xC000 64 = pkTr (bytesAt (mcSat p).mem 0x1000 p.pkLen) := by
  show bytesAt (mcSatMem p) 0xC000 64 = pkTr (bytesAt (mcSatMem p) 0x1000 p.pkLen)
  rw [mcSat_key hp]
  have hl : (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0xC000 : Addr) + BitVec.ofNat 64 i).toNat = 0xC000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [mcSatMem, he, show 0xC000 ≤ 0xC000 + i ∧ 0xC000 + i < 0xC040 by omega, true_and, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- `vg_mldsa*_sign_message` (or `_sign_message_prepared`, `pr`) of the
parameter set `p`, calling the signing function on `μ` `f`, named `n`, meets
its contract with `S` bytes of stack. -/
theorem signMessage_verified {p : Params} {pr : Bool} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat}
    (h48 : 48 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => signK p pr PPC64LE.abi stk) S) (n : String)
    (hsat : ∃ s, (msgSK p pr PPC64LE.abi S).pre s) :
    Verified PPC64LE.target (signMessage n f p) (msgSK p pr PPC64LE.abi S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => signMessage_wp hF h48 hf (Nat.le_refl _) (mspre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  have hpub' : MSPub p s₁ s₂ := by
    cases pr <;> simp only [msgSK, Bool.false_eq_true, ↓reduceIte] at hpub
    all_goals
      sig_pub [signMessageContract, signMessageSig, preparedSignMessageContract, preparedSignMessageSig,
        PPC64LE.abi, PPC64LE.argRegs] at hpub
      obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
      refine ⟨hsp, hl, fun r hr => ?_⟩
      simp only [mArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h3, h4, h5, h6, h7, h8, h9, h10]
  exact signMessage_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mspre_of h₁) (mspre_of h₂)
    hpub' e₁ e₂

/-- `vg_mldsa*_verify_message_cached` (or `_verify_message_prepared`, `pr`) of
the parameter set `p`, calling the verification function on `μ` `f`, named
`n`, meets its contract with `S` bytes of stack. -/
theorem verifyMessageCached_verified {p : Params} {pr : Bool} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    {S : Nat} (h48 : 48 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => verifyK p pr PPC64LE.abi stk) S) (n : String)
    (hsat : ∃ s, (msgVK p pr PPC64LE.abi S).pre s) :
    Verified PPC64LE.target (verifyMessageCached n f p) (msgVK p pr PPC64LE.abi S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => verifyMessageCached_wp hF h48 hf (Nat.le_refl _) (mcpre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  have hpub' : MCPub p s₁ s₂ := by
    cases pr <;> simp only [msgVK, Bool.false_eq_true, ↓reduceIte] at hpub
    all_goals
      sig_pub [verifyMessageCachedContract, verifyMessageCachedSig, preparedVerifyMessageContract,
        preparedVerifyMessageSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
      obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
      refine ⟨hsp, hl, fun r hr => ?_⟩
      simp only [cArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h3, h4, h5, h6, h7, h8, h9, h10]
  exact verifyMessageCached_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mcpre_of h₁) (mcpre_of h₂)
    hpub' e₁ e₂

end VG.Proof.MlDsa.PPC64LE.Message
