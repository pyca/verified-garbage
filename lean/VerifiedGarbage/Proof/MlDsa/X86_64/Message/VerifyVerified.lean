module
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCall

import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCorrect
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on x86-64, `verify_message_cached`: verified

Untrusted: everything here is checked by Lean. `verifyMessageCached n c p`,
for any verification function on `μ` `c` that `verify_message_cached` can
call (`VerifyFn`), is verified against
`verifyMessageCachedContract p X86_64.abi 112`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The memory of a state satisfying the precondition: `pk` (zeros) at
`0x1000`, `tr = H(pk, 64)` at `0x8000`, and the stack arguments `scratch =
0x10000` and `tr = 0x8000` at `0x80008` and `0x80010`. -/
def stkMem : Mem := fun a => if a = 0x8000A then 0x01 else if a = 0x80011 then 0x80 else 0

def satMem (p : Params) : Mem := fun a =>
  if 0x8000 ≤ a.toNat ∧ a.toNat < 0x8040 then
    (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0x8000) 0
  else stkMem a

theorem satMem_stk (p : Params) {a : Addr} (ha : 0x8040 ≤ a.toNat) (hb : a.toNat + 8 < 2 ^ 64) :
    (satMem p).readW a 64 = stkMem.readW a 64 :=
  Mem.readW_congr fun i hi => by
    have he : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [satMem, he]
    split
    · omega
    · rfl

theorem satMem_key {p : Params} (hp : p.pkLen < 0x7000) :
    bytesAt (satMem p) 0x1000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x1000 : Addr) + BitVec.ofNat 64 i).toNat = 0x1000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [satMem, he]
  split
  · omega
  simp only [stkMem]
  repeat' split
  all_goals first
    | rfl
    | (rename_i e _; have := congrArg BitVec.toNat e; simp only [he, BitVec.reduceToNat] at this; omega)
    | (rename_i e; have := congrArg BitVec.toNat e; simp only [he, BitVec.reduceToNat] at this; omega)

theorem satMem_digest {p : Params} (hp : p.pkLen < 0x7000) :
    bytesAt (satMem p) 0x8000 64 = pkTr (bytesAt (satMem p) 0x1000 p.pkLen) := by
  rw [satMem_key hp]
  have hl : (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0x8000 : Addr) + BitVec.ofNat 64 i).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [satMem, he, show 0x8000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x8040 by omega, true_and, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- A state satisfying the precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem p
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x8000, 64⟩, ⟨0x80008, 16⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (verifyMessageCachedContract p X86_64.abi 112).pre s := by
  refine ⟨verifySat p, ?_⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  have a0 : stackArg (verifySat p) 0 = 0x10000 := by
    rw [stackArg, show stackArgAddr (verifySat p) 0 = 0x80008 from rfl]
    exact (satMem_stk p (by decide) (by decide)).trans (by decide)
  have a1 : stackArg (verifySat p) 1 = 0x8000 := by
    rw [stackArg, show stackArgAddr (verifySat p) 1 = 0x80010 from rfl]
    exact (satMem_stk p (by decide) (by decide)).trans (by decide)
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, X86_64.abi, X86_64.argRegs,
      List.range, List.range.loop] <;> sig_and_intros <;> (try simp only [a0, a1])
  all_goals first
    | exact satMem_digest (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    Verified X86_64.target (verifyMessageCached n c p) (verifyMessageCachedContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessage_wp hV hp h; ⟨t, s', he, ha, hq⟩,
    verifyMessage_ct hV hp, verifyMessage_sat hp⟩

end VG.Proof.MlDsa.X86_64.Message
