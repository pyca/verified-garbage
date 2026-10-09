import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCT

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- An explicit satisfiability witness stores a valid digest away from the key. -/
def satMem (p : Params) : Mem := fun a =>
  if 0x8000 ≤ a.toNat ∧ a.toNat < 0x8040 then
    (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0x8000) 0
  else 0

theorem satMem_key {p : Params} (hp : p.pkLen < 0x7000) :
    bytesAt (satMem p) 0x1000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x1000 : Addr) + BitVec.ofNat 64 i).toNat = 0x1000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [satMem, he]
  split
  · rename_i h; omega
  · rfl

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

def verifySat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x3100 | .x5 => 0x3200 | .x6 => 0x10000 | .x7 => 0x8000
    | _ => 0
  sp := 0x80000
  mem := satMem p
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x8000, 64⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (verifyMessageCachedContract p AArch64.abi 16).pre s := by
  refine ⟨verifySat p, ?_⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, AArch64.abi, AArch64.argRegs,
      List.range, List.range.loop] <;> sig_and_intros
  all_goals first
    | exact satMem_digest (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hV : Message.VerifyFn p c) (hp : p ∈ params) :
    Verified AArch64.target (verifyMessageCached v.callee n c p) (verifyMessageCachedContract p AArch64.abi 16) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessageCached_wp v hV hp h; ⟨t, s', he, ha, hq⟩,
    verifyMessage_ct v hV hp, verifyMessage_sat hp⟩

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
