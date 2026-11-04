module
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCall
public import VerifiedGarbage.Spec.MlDsa.CachedVerify

import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on ARMv7, `sign_message`, `verify_message` and `verify_message_cached`: verified

Untrusted: everything here is checked by Lean. `signMessage n c p`,
`verifyMessage n c p` and `verifyMessageCached n c p`, for any functions on
`μ` `c` they can call (`SignFn`, `VerifyFn`), are verified against
`signMessageContract p Arm.abi 36`, `verifyMessageContract p Arm.abi 36` and
`verifyMessageCachedContract p Arm.abi 36`; `vg_mldsa*_sign` and
`vg_mldsa*_verify` are such functions (`sign44Fn`, …), and
`verifyMessageCached44_verified`, … are the cached verifications of
`vg_mldsa*_verify`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition of signing: `ctx_len = 0`, `rnd`,
`sig` and `scratch` on the stack. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80005 then 0x32 else if a = 0x80009 then 0x40 else if a = 0x8000E then 1 else 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩, ⟨0x80000, 16⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩]

theorem signMessage_sat {p : Params} (hp : p ∈ params) : ∃ s, (signMessageContract p Arm.abi 36).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa44
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa65
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa87

theorem signMessage_verified {p : Params} {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    Verified Arm.target (signMessage n c p) (signMessageContract p Arm.abi 36) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := signMessage_wp hS hp h; ⟨t, s', he, ha, hq⟩,
    signMessage_ct hS hp, signMessage_sat hp⟩

/-- A state satisfying the precondition of verification: `ctx_len = 0`, `sig`
and `scratch` on the stack. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80005 then 0x32 else if a = 0x8000A then 1 else 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x80000, 12⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) : ∃ s, (verifyMessageContract p Arm.abi 36).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using verifySat mlDsa44
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using verifySat mlDsa65
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using verifySat mlDsa87

theorem verifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    Verified Arm.target (verifyMessage n c p) (verifyMessageContract p Arm.abi 36) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessage_wp hV hp h; ⟨t, s', he, ha, hq⟩,
    verifyMessage_ct hV hp, verifyMessage_sat hp⟩

/-- The memory of a state satisfying the precondition of verification with a
cached `tr`: `ctx_len = 0`, `sig`, `scratch` and `tr` on the stack, and `tr`
the digest of the key. -/
def cachedSatMem (p : Params) : Mem := fun a =>
  if 0x8000 ≤ a.toNat ∧ a.toNat < 0x8040 then
    (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0x8000) 0
  else if a = 0x80005 then 0x32 else if a = 0x8000A then 1 else if a = 0x8000D then 0x80 else 0

theorem cachedSatMem_key {p : Params} (hp : p.pkLen < 0x7000) :
    bytesAt (cachedSatMem p) 0x1000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x1000 : Addr) + BitVec.ofNat 64 i).toNat = 0x1000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  have ne : ∀ b : Addr, 0x8000 ≤ b.toNat → (0x1000 : Addr) + BitVec.ofNat 64 i ≠ b := fun b hb e => by
    have := congrArg BitVec.toNat e; rw [he] at this; omega
  simp only [cachedSatMem, he]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by decide))), ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by decide)))]

theorem cachedSatMem_digest {p : Params} (hp : p.pkLen < 0x7000) :
    bytesAt (cachedSatMem p) 0x8000 64 = pkTr (bytesAt (cachedSatMem p) 0x1000 p.pkLen) := by
  rw [cachedSatMem_key hp]
  have hl : (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0x8000 : Addr) + BitVec.ofNat 64 i).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [cachedSatMem, he, show 0x8000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x8040 by omega, true_and, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- A state satisfying the precondition of verification with a cached `tr`. -/
def cachedSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem := cachedSatMem p
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x8000, 64⟩, ⟨0x80000, 16⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem cachedSat_tr {p : Params} (hp : p.pkLen < 0x7000)
    (h3 : BitVec.setWidth 64 (stackArg (cachedSat p) 3) = 0x8000) :
    bytesAt (cachedSat p).mem (BitVec.setWidth 64 (stackArg (cachedSat p) 3)) 64 =
      pkTr (bytesAt (cachedSat p).mem (BitVec.setWidth 64 ((cachedSat p).gpr .r0)) p.pkLen) := by
  rw [h3, show BitVec.setWidth 64 ((cachedSat p).gpr .r0) = 0x1000 from rfl]
  exact cachedSatMem_digest hp

theorem verifyMessageCached_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (verifyMessageCachedContract p Arm.abi 36).pre s := by
  refine ⟨cachedSat p, ?_⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] <;> sig_and_intros
  all_goals first
    | exact cachedSat_tr (by decide) (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verifyMessageCached_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) :
    Verified Arm.target (verifyMessageCached n c p) (verifyMessageCachedContract p Arm.abi 36) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessageCached_wp hV hp h; ⟨t, s', he, ha, hq⟩,
    verifyMessageCached_ct hV hp, verifyMessageCached_sat hp⟩

/-! ## The functions on `μ` -/

theorem sign44Fn : SignFn mlDsa44 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa44) :=
  ⟨Sign.sign44_verified', by decide +kernel⟩
theorem sign65Fn : SignFn mlDsa65 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa65) :=
  ⟨Sign.sign65_verified', by decide +kernel⟩
theorem sign87Fn : SignFn mlDsa87 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa87) :=
  ⟨Sign.sign87_verified', by decide +kernel⟩

theorem verify44Fn : VerifyFn mlDsa44 Impl.MlDsa.Arm.Verify.verify44 :=
  ⟨Verify.verify44_verified, by decide +kernel⟩
theorem verify65Fn : VerifyFn mlDsa65 Impl.MlDsa.Arm.Verify.verify65 :=
  ⟨Verify.verify65_verified, by decide +kernel⟩
theorem verify87Fn : VerifyFn mlDsa87 Impl.MlDsa.Arm.Verify.verify87 :=
  ⟨Verify.verify87_verified, by decide +kernel⟩

theorem verifyMessageCached44_verified :
    Verified Arm.target (verifyMessageCached verify44Api.name Impl.MlDsa.Arm.Verify.verify44 mlDsa44)
      (verifyMessageCachedContract mlDsa44 Arm.abi 36) :=
  verifyMessageCached_verified verify44Fn (List.mem_cons_self ..)
theorem verifyMessageCached65_verified :
    Verified Arm.target (verifyMessageCached verify65Api.name Impl.MlDsa.Arm.Verify.verify65 mlDsa65)
      (verifyMessageCachedContract mlDsa65 Arm.abi 36) :=
  verifyMessageCached_verified verify65Fn (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem verifyMessageCached87_verified :
    Verified Arm.target (verifyMessageCached verify87Api.name Impl.MlDsa.Arm.Verify.verify87 mlDsa87)
      (verifyMessageCachedContract mlDsa87 Arm.abi 36) :=
  verifyMessageCached_verified verify87Fn (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

end VG.Proof.MlDsa.Arm.Message
