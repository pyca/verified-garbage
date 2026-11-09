module
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCall
public import VerifiedGarbage.Spec.MlDsa.CachedVerify

import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Entry
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Entry
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Verified
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message_cached`: verified

Untrusted: everything here is checked by Lean. `signMessage n c p` and
`verifyMessageCached n c p`, for any functions on `μ` `c` they can call
(`SignFn`, `VerifyFn`), are verified against `signMessageContract p Arm.abi
52` and `verifyMessageCachedContract p Arm.abi 52`; `vg_mldsa*_sign` and
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

theorem signMessage_sat {p : Params} (hp : p ∈ params) : ∃ s, (signMessageContract p Arm.abi 52).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa44
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa65
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa87

theorem signMessage_verified {p : Params} {n : String} {c : Prog isa} (hS : SignFn p false c) (hp : p ∈ params) :
    Verified Arm.target (signMessage n c p) (signMessageContract p Arm.abi 52) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := signMessage_wp hS hp (sPre_of h); ⟨t, s', he, ha, hq⟩,
    fun _ _ _ _ _ _ h₁ h₂ hp' e₁ e₂ => signMessage_ct hS hp _ _ _ _ _ _ (sPre_of h₁) (sPre_of h₂) (sPub_of hp') e₁ e₂,
    signMessage_sat hp⟩

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
    ∃ s, (verifyMessageCachedContract p Arm.abi 52).pre s := by
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

theorem verifyMessageCached_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p false c)
    (hp : p ∈ params) :
    Verified Arm.target (verifyMessageCached n c p) (verifyMessageCachedContract p Arm.abi 52) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessageCached_wp hV hp (cPre_of h); ⟨t, s', he, ha, hq⟩,
    fun _ _ _ _ _ _ h₁ h₂ hp' e₁ e₂ =>
      verifyMessageCached_ct hV hp _ _ _ _ _ _ (cPre_of h₁) (cPre_of h₂) (cPub_of hp') e₁ e₂,
    verifyMessageCached_sat hp⟩

/-! ## The functions on `μ` -/

theorem sign44Fn : SignFn mlDsa44 false (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa44) :=
  ⟨(Sign.signE_verified (.inl rfl)).1, (Sign.signE_verified (.inl rfl)).2.1, by decide +kernel⟩
theorem sign65Fn : SignFn mlDsa65 false (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa65) :=
  ⟨(Sign.signE_verified (.inr (.inl rfl))).1, (Sign.signE_verified (.inr (.inl rfl))).2.1, by decide +kernel⟩
theorem sign87Fn : SignFn mlDsa87 false (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa87) :=
  ⟨(Sign.signE_verified (.inr (.inr rfl))).1, (Sign.signE_verified (.inr (.inr rfl))).2.1, by decide +kernel⟩

theorem verify44Fn : VerifyFn mlDsa44 false Impl.MlDsa.Arm.Verify.verify44 :=
  ⟨(Verify.verifyE_verified (.inl rfl)).1, (Verify.verifyE_verified (.inl rfl)).2.1, by decide +kernel⟩
theorem verify65Fn : VerifyFn mlDsa65 false Impl.MlDsa.Arm.Verify.verify65 :=
  ⟨(Verify.verifyE_verified (.inr (.inl rfl))).1, (Verify.verifyE_verified (.inr (.inl rfl))).2.1, by decide +kernel⟩
theorem verify87Fn : VerifyFn mlDsa87 false Impl.MlDsa.Arm.Verify.verify87 :=
  ⟨(Verify.verifyE_verified (.inr (.inr rfl))).1, (Verify.verifyE_verified (.inr (.inr rfl))).2.1, by decide +kernel⟩

theorem verifyMessageCached44_verified :
    Verified Arm.target (verifyMessageCached verify44Api.name Impl.MlDsa.Arm.Verify.verify44 mlDsa44)
      (verifyMessageCachedContract mlDsa44 Arm.abi 52) :=
  verifyMessageCached_verified verify44Fn (List.mem_cons_self ..)
theorem verifyMessageCached65_verified :
    Verified Arm.target (verifyMessageCached verify65Api.name Impl.MlDsa.Arm.Verify.verify65 mlDsa65)
      (verifyMessageCachedContract mlDsa65 Arm.abi 52) :=
  verifyMessageCached_verified verify65Fn (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem verifyMessageCached87_verified :
    Verified Arm.target (verifyMessageCached verify87Api.name Impl.MlDsa.Arm.Verify.verify87 mlDsa87)
      (verifyMessageCachedContract mlDsa87 Arm.abi 52) :=
  verifyMessageCached_verified verify87Fn (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-! ## Prepared keys -/

/-- The bytes of the arguments on the stack of `signSat`. -/
def satArgBytes (a : Addr) : BitVec 8 :=
  if a = 0x80005 then 0x32 else if a = 0x80009 then 0x40 else if a = 0x8000E then 1 else 0

/-- `signSat`, with a prepared private key at `0x200000` in the memory `m`. -/
def preparedSignSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .r0 => 0x200000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if 0x80000 ≤ a.toNat ∧ a.toNat < 0x80010 then satArgBytes a else m a
  rd := [⟨0x200000, preparedSecretKeyBytes p⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩, ⟨0x80000, 16⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩]

/-- The bytes at `0x200000` of a memory but for the arguments on the stack. -/
theorem key_bytes {m : Mem} {f : Addr → BitVec 8} {len : Nat} (hl : len < 0x100000) :
    bytesAt (fun a => if 0x80000 ≤ a.toNat ∧ a.toNat < 0x80010 then f a else m a) 0x200000 len =
      bytesAt m 0x200000 len := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x200000 : Addr) + BitVec.ofNat 64 i).toNat = 0x200000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [he]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The arguments on the stack at `0x80000` depend only on the 16 bytes there. -/
theorem stackArg_eq_of {s s' : State} (hsp : s.sp = 0x80000) (hsp' : s'.sp = 0x80000) {i : Nat} (hi : i < 4)
    (h : ∀ a : Addr, 0x80000 ≤ a.toNat → a.toNat < 0x80010 → s.mem a = s'.mem a) : stackArg s i = stackArg s' i := by
  unfold stackArg stackArgAddr
  rw [hsp, hsp']
  apply Mem.readW_congr
  intro j hj
  have e : (State.addr ((0x80000 : BitVec 32) + BitVec.ofNat 32 (4 * i)) + BitVec.ofNat 64 j).toNat =
      0x80000 + 4 * i + j := by
    simp only [State.addr, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  exact h _ (by rw [e]; omega) (by rw [e]; omega)

theorem preparedSignSat_arg {p : Params} {m : Mem} {i : Nat} (hi : i < 4) :
    stackArg (preparedSignSat p m) i = stackArg (preparedSignSat p (fun _ => 0)) i :=
  stackArg_eq_of rfl rfl hi fun a h₁ h₂ => by simp only [preparedSignSat, h₁, h₂, and_self, ite_true]

theorem preparedSignSat_pre {p : Params} (hp : p ∈ params) {m : Mem} (hk : PreparedSecretKey p m 0x200000) :
    (preparedSignMessageContract p Arm.abi 52).pre (preparedSignSat p m) := by
  have hk' : PreparedSecretKey p (preparedSignSat p m).mem 0x200000 :=
    PreparedKey.preparedSecretKey_of_bytes (key_bytes (by
      simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide)) hk
  have a0 := preparedSignSat_arg (p := p) (m := m) (i := 0) (by decide)
  have a1 := preparedSignSat_arg (p := p) (m := m) (i := 1) (by decide)
  have a2 := preparedSignSat_arg (p := p) (m := m) (i := 2) (by decide)
  have a3 := preparedSignSat_arg (p := p) (m := m) (i := 3) (by decide)
  have sa : stackArgAddr (preparedSignSat p m) 0 = stackArgAddr (preparedSignSat p (fun _ => 0)) 0 := rfl
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [preparedSignMessageContract, preparedSignMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] <;> simp only [a0, a1, a2, a3, sa] <;> sig_and_intros
  all_goals first
    | exact hk'
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem preparedSignMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (preparedSignMessageContract p Arm.abi 52).pre s := by
  have h3 : PreparedKey.Ok3 p := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp; exact hp
  obtain ⟨m, hk⟩ := PreparedKey.prepared_secret_mem h3
  exact ⟨_, preparedSignSat_pre hp hk⟩

theorem preparedSignMessage_verified {p : Params} {n : String} {c : Prog isa} (hS : SignFn p true c)
    (hp : p ∈ params) :
    Verified Arm.target (signMessage n c p) (preparedSignMessageContract p Arm.abi 52) := by
  refine ⟨fun s h => ?_, fun _ _ _ _ _ _ h₁ h₂ hp' e₁ e₂ =>
    signMessage_ct hS hp _ _ _ _ _ _ (sPre_of_prepared h₁) (sPre_of_prepared h₂) (sPub_of_prepared hp') e₁ e₂,
    preparedSignMessage_sat hp⟩
  obtain ⟨t, s', he, ha, hq⟩ := signMessage_wp hS hp (sPre_of_prepared h)
  refine ⟨t, s', he, ha, ?_⟩
  sig_post [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  sig_post [preparedSignMessageContract, preparedSignMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  exact hq

/-- The bytes of the arguments on the stack of `cachedSat`. -/
def cachedArgBytes (a : Addr) : BitVec 8 :=
  if a = 0x80005 then 0x32 else if a = 0x8000A then 1 else if a = 0x8000D then 0x80 else 0

/-- `cachedSatMem`, with a prepared public key at `0x200000` in the memory `m`. -/
def preparedCachedMem (p : Params) (m : Mem) : Mem := fun a =>
  if 0x8000 ≤ a.toNat ∧ a.toNat < 0x8040 then
    (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0x8000) 0
  else if 0x80000 ≤ a.toNat ∧ a.toNat < 0x80010 then cachedArgBytes a else m a

/-- `cachedSat`, with a prepared public key at `0x200000` in the memory `m`. -/
def preparedCachedSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .r0 => 0x200000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem := preparedCachedMem p m
  rd := [⟨0x200000, preparedPublicKeyBytes p⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x8000, 64⟩,
    ⟨0x80000, 16⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem preparedCachedMem_key {p : Params} {m : Mem} {len : Nat} (hl : len < 0x100000) :
    bytesAt (preparedCachedMem p m) 0x200000 len = bytesAt m 0x200000 len := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x200000 : Addr) + BitVec.ofNat 64 i).toNat = 0x200000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [preparedCachedMem, he]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem preparedCachedMem_digest {p : Params} (hp : p.pkLen < 0x7000) {m : Mem}
    (hm : bytesAt m 0x200000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen) :
    bytesAt (preparedCachedMem p m) 0x8000 64 = pkTr (bytesAt (preparedCachedMem p m) 0x200000 p.pkLen) := by
  rw [preparedCachedMem_key (by omega), hm]
  have hl : (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0x8000 : Addr) + BitVec.ofNat 64 i).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [preparedCachedMem, he, show 0x8000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x8040 by omega, true_and, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem preparedCachedSat_arg {p : Params} {m : Mem} {i : Nat} (hi : i < 4) :
    stackArg (preparedCachedSat p m) i = stackArg (preparedCachedSat p (fun _ => 0)) i :=
  stackArg_eq_of rfl rfl hi fun a h₁ h₂ => by
    simp only [preparedCachedSat, preparedCachedMem, h₁, h₂, and_self, ite_true]

theorem preparedCachedSat_pre {p : Params} (hp : p ∈ params) {m : Mem}
    (hm : bytesAt m 0x200000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen) (hk : PreparedPublicKey p m 0x200000) :
    (preparedVerifyMessageContract p Arm.abi 52).pre (preparedCachedSat p m) := by
  have hl : preparedPublicKeyBytes p < 0x100000 ∧ p.pkLen < 0x7000 := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  have hk' : PreparedPublicKey p (preparedCachedSat p m).mem 0x200000 :=
    PreparedKey.preparedPublicKey_of_bytes (preparedCachedMem_key hl.1) hk
  have htr := preparedCachedMem_digest hl.2 hm
  have a0 := preparedCachedSat_arg (p := p) (m := m) (i := 0) (by decide)
  have a1 := preparedCachedSat_arg (p := p) (m := m) (i := 1) (by decide)
  have a2 := preparedCachedSat_arg (p := p) (m := m) (i := 2) (by decide)
  have a3 := preparedCachedSat_arg (p := p) (m := m) (i := 3) (by decide)
  have sa : stackArgAddr (preparedCachedSat p m) 0 = stackArgAddr (preparedCachedSat p (fun _ => 0)) 0 := rfl
  have e3 : BitVec.setWidth 64 (stackArg (preparedCachedSat p (fun _ => 0)) 3) = 0x8000 := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] <;> simp only [a0, a1, a2, a3, sa] <;> sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide)
    | decide
    | exact hk'
    | exact (congrArg (fun a => bytesAt (preparedCachedMem _ m) a 64) e3).trans htr
    | rfl

theorem preparedVerifyMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (preparedVerifyMessageContract p Arm.abi 52).pre s := by
  have h3 : PreparedKey.Ok3 p := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp; exact hp
  obtain ⟨m, hm, hk⟩ := PreparedKey.prepared_public_mem h3
  exact ⟨_, preparedCachedSat_pre hp hm hk⟩

theorem preparedVerifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p true c)
    (hp : p ∈ params) :
    Verified Arm.target (verifyMessageCached n c p) (preparedVerifyMessageContract p Arm.abi 52) := by
  refine ⟨fun s h => ?_, fun _ _ _ _ _ _ h₁ h₂ hp' e₁ e₂ =>
    verifyMessageCached_ct hV hp _ _ _ _ _ _ (cPre_of_prepared h₁) (cPre_of_prepared h₂) (cPub_of_prepared hp') e₁ e₂,
    preparedVerifyMessage_sat hp⟩
  obtain ⟨t, s', he, ha, hq⟩ := verifyMessageCached_wp hV hp (cPre_of_prepared h)
  refine ⟨t, s', he, ha, ?_⟩
  sig_post [verifyMessageCachedContract, verifyMessageCachedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at hq
  sig_post [preparedVerifyMessageContract, preparedVerifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  exact hq

/-! ## The functions on `μ` with prepared keys -/

theorem signPreparedFn {p : Params} (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    SignFn p true (Impl.MlDsa.Arm.Sign.signPrepared Sign.prims p) :=
  ⟨Sign.entry_correct h3 true, Sign.entry_ct h3 true, by rcases h3 with rfl | rfl | rfl <;> decide +kernel⟩

theorem verifyPreparedFn {p : Params} (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifyFn p true (Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims p) :=
  ⟨Verify.entry_correct h3 true, Verify.entry_ct h3 true, by rcases h3 with rfl | rfl | rfl <;> decide +kernel⟩

end VG.Proof.MlDsa.Arm.Message
