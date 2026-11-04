module
-- separate module: built in parallel with `Sign/Inst` and `Verify/Inst`, which `Inst` also imports

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.VerifyCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Message

/-!
# ML-DSA on RISC-V, `sign_message` and `verify_message_cached`: their contracts

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message_cached` meet their
contracts with `S` bytes of stack, for any verified function on `μ` with at
most `S` bytes of stack (at least the 1168 the sponge functions' frames
take): by correctness (`signMessage_wp`, `verifyMessageCached_wp`) and
constant time (`signMessage_ct`, `verifyMessageCached_ct`). The contracts'
satisfiability (by `msSat`, `mvcSat`) is evaluated once
`S` is known.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A state that satisfies `signMessageContract`'s precondition. -/
def msSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a3 => 0x9000 | .a5 => 0xA000 | .a6 => 0xB000 | .a7 => 0x20000
    | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, 32⟩]
  wr := [⟨0xB000, p.sigLen⟩, ⟨0x20000, messageScratchWords p * 8⟩]

/-- The memory of `mvcSat`: zeros, but `tr` at `0xC000`, which is `H` of a key of zeros. -/
def mvcMem (p : Params) : Mem := fun a =>
  if 0xC000 ≤ a.toNat ∧ a.toNat < 0xC040 then (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0xC000) 0
  else 0

/-- A state that satisfies `verifyMessageCachedContract`'s precondition. -/
def mvcSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a3 => 0x9000 | .a5 => 0xA000 | .a6 => 0x20000 | .a7 => 0xC000 | _ => 0
  sp := 0x100000
  mem := mvcMem p
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, p.sigLen⟩, ⟨0xC000, 64⟩]
  wr := [⟨0x20000, messageScratchWords p * 8⟩]

theorem mvcMem_key {p : Params} (hp : p.pkLen ≤ 0xB000) :
    bytesAt (mvcMem p) 0x1000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x1000 : Addr) + BitVec.ofNat 64 i).toNat = 0x1000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [mvcMem, he]
  split
  · rename_i h; omega
  · rfl

/-- `mvcSat`'s `tr` is `H` of its key. -/
theorem mvcMem_tr {p : Params} (hp : p.pkLen ≤ 0xB000) :
    bytesAt (mvcMem p) 0xC000 64 = pkTr (bytesAt (mvcMem p) 0x1000 p.pkLen) := by
  rw [mvcMem_key hp]
  have hl : (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0xC000 : Addr) + BitVec.ofNat 64 i).toNat = 0xC000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [mvcMem, he, show 0xC000 ≤ 0xC000 + i ∧ 0xC000 + i < 0xC040 by omega, and_self, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- `vg_mldsa*_sign_message` of the parameter set `p`, calling the signing
function on `μ` `f`, named `n`, meets its contract with `S` bytes of stack. -/
theorem signMessage_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat}
    (h48 : 1168 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => signContract p RISCV64.abi stk) S) (n : String)
    (hsat : (signMessageContract p RISCV64.abi S).pre (msSat p)) :
    Verified RISCV64.target (signMessage n f p) (signMessageContract p RISCV64.abi S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => signMessage_wp hF h48 hf (Nat.le_refl _) (mspre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨msSat p, hsat⟩⟩
  sig_pub [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
  refine signMessage_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mspre_of h₁) (mspre_of h₂)
    ⟨hsp, hl, fun r hr => ?_⟩ e₁ e₂
  simp only [mArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h3, h4, h5, h6, h7, h8, h9, h10]

/-- `vg_mldsa*_verify_message_cached` of the parameter set `p`, calling the
verification function on `μ` `f`, named `n`, meets its contract with `S`
bytes of stack. -/
theorem verifyMessageCached_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat}
    (h48 : 1168 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => verifyContract p RISCV64.abi stk) S) (n : String)
    (hsat : (verifyMessageCachedContract p RISCV64.abi S).pre (mvcSat p)) :
    Verified RISCV64.target (verifyMessageCached n f p) (verifyMessageCachedContract p RISCV64.abi S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => verifyMessageCached_wp hF h48 hf (Nat.le_refl _) (mvcpre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨mvcSat p, hsat⟩⟩
  sig_pub [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
  refine verifyMessageCached_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mvcpre_of h₁) (mvcpre_of h₂)
    ⟨hsp, hl, fun r hr => ?_⟩ e₁ e₂
  simp only [vcArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h3, h4, h5, h6, h7, h8, h9, h10]

end VG.Proof.MlDsa.RISCV64.Message
