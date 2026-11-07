module
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.Sign.Entry
public import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract

public import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Entry
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Entry
public import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlKem.X86.TopKem
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst
meta import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Impl.MlDsa.X86.Sign.Entry
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall
meta import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Entry
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Entry
meta import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlKem.X86.TopKem
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ML-DSA on x86 (32-bit): the functions on `μ` and on messages, with encoded and prepared keys

Untrusted: everything here is checked by Lean. For each parameter set:

* `vg_mldsa*_sign` and `vg_mldsa*_sign_prepared` (`Sign/Entry.lean`), which
  call `vg_mldsa*_sign_core`, meet `signContract` and `preparedSignContract`
  (`sign44_verified`, `signPrepared44_verified`, …), and so `signKContract`
  of an encoded key and of a prepared one (`secretKey`); the same for
  verification (`Verify/Entry.lean`);
* `vg_mldsa*_sign_message` and `vg_mldsa*_sign_message_prepared` (the same
  code, calling the two functions on `μ`) meet `signMessageContract` and
  `preparedSignMessageContract`; `vg_mldsa*_verify_message_cached` and
  `vg_mldsa*_verify_message_prepared`, `verifyMessageCachedContract` and
  `preparedVerifyMessageContract`.

The preconditions with a prepared key hold of a key that
`vg_mldsa*_prepare_signing_key` or `vg_mldsa*_prepare_verifying_key` wrote
(`signPrepared_sat`, `verifyPrepared_sat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.X86.PreparedKey (above above_eq above_low above_readW secret_congr public_congr)
open VG.Impl.MlDsa.X86.Sign (signEntry signPrepared)
open VG.Impl.MlDsa.X86.Verify (verifyOf verifyPreparedOf)

/-! ## Prepared keys as `KeyArg`s -/

theorem bytes_pt {m m' : Mem} {a : Addr} {n : Nat} (h : bytesAt m' a n = bytesAt m a n) :
    ∀ i < n, m' (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i) := fun i hi => by
  have e := congrArg (fun l : List Byte => l[i]!) h
  rwa [Proof.MlKem.bytesAt_getElem! _ _ hi, Proof.MlKem.bytesAt_getElem! _ _ hi] at e

/-- A prepared private key. -/
abbrev secretKey (p : Params) : KeyArg := ⟨preparedSecretKeyBytes p, PreparedSecretKey p⟩
/-- A prepared public key. -/
abbrev publicKey (p : Params) : KeyArg := ⟨preparedPublicKeyBytes p, PreparedPublicKey p⟩

theorem secretKey_ok {p : Params} (hp : p ∈ params) : (secretKey p).Ok p.skLen := by
  refine ⟨(skLen_ge hp).1, by simp only [preparedSecretKeyBytes]; omega, ?_,
    fun h k => secret_congr k (bytes_pt h)⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem publicKey_ok {p : Params} (hp : p ∈ params) : (publicKey p).Ok p.pkLen := by
  refine ⟨(pkLen_ge hp).1, by simp only [preparedPublicKeyBytes]; omega, ?_,
    fun h k => public_congr k (bytes_pt h)⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- What `preparedVerifyMessageContract` requires of `pk` and `tr`. -/
abbrev preparedTr (p : Params) (m : Mem) (pk tr : Addr) : Prop :=
  PreparedPublicKey p m pk ∧ bytesAt m tr 64 = pkTr (bytesAt m pk p.pkLen)

theorem preparedSignContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    Proof.MlDsa.preparedSignContract p A stack = signKContract p (secretKey p) A stack := rfl
theorem preparedVerifyContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    Proof.MlDsa.preparedVerifyContract p A stack = verifyKContract p (publicKey p) A stack := rfl
theorem preparedSignMessageContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    preparedSignMessageContract p A stack = signMessageKContract p (secretKey p) A stack := rfl
theorem preparedVerifyMessageContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    preparedVerifyMessageContract p A stack =
      verifyMessageKContract p (preparedPublicKeyBytes p) (preparedTr p) A stack := rfl

/-! ## The preconditions with prepared keys can hold -/

/-- `satMemS`, with `sk` at `0x8000`. -/
def satMemSP : Mem := fun a => if a = 0x5005 then 0x80 else satMemS a

theorem signPrepared_sat {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (signMessageKContract p (secretKey p) X86.abi 176).pre s := by
  obtain ⟨m, hm⟩ := PreparedKey.secret_at Verify.prims_ok hp3
  have hk : PreparedSecretKey p (above satMemSP m) 0x8000 := secret_congr hm fun i hi => above_eq
    (Nat.lt_of_lt_of_le hi (by rcases hp3 with rfl | rfl | rfl <;> decide))
  refine ⟨Proof.MlKem.X86.satState (above satMemSP m) [⟨0x8000, preparedSecretKeyBytes p⟩, ⟨0x2000, 0⟩,
    ⟨0x2000, 0⟩, ⟨0x3000, 32⟩] [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩], ?_⟩
  have a0 : ∀ τ : State, τ.mem = above satMemSP m → τ.gpr .esp = 0x5000 →
      arg τ 0 = 0x8000 ∧ arg τ 1 = 0x2000 ∧ arg τ 2 = 0 ∧ arg τ 3 = 0x2000 ∧ arg τ 4 = 0 ∧ arg τ 5 = 0x3000 ∧
        arg τ 6 = 0x6000 ∧ arg τ 7 = 0x10000 := by
    intro τ e he
    simp only [arg, argAddr, e, he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [above_readW]
    all_goals first | decide | kernel_rfl
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := a0 (Proof.MlKem.X86.satState (above satMemSP m)
    [⟨0x8000, preparedSecretKeyBytes p⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, 32⟩]
    [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) rfl rfl
  have ag : argAddr (Proof.MlKem.X86.satState (above satMemSP m) [⟨0x8000, preparedSecretKeyBytes p⟩, ⟨0x2000, 0⟩,
    ⟨0x2000, 0⟩, ⟨0x3000, 32⟩] [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) 0 = 0x5004 := rfl
  sig_pre [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  simp only [b0, b1, b2, b3, b4, b5, b6, b7, ag]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    and_intros
    all_goals first
      | exact hk
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

/-- `satMemC0`, with `pk` at `0x8000` and `tr` at `0x7800`. -/
def satMemVP0 : Mem := fun a => if a = 0x5005 then 0x80 else if a = 0x5021 then 0x78 else satMemC0 a

/-- `above satMemVP0 m`, with `tr = H(pk, 64)` of the key at `0x8000` at `0x7800`. -/
def satMemVP (p : Params) (m : Mem) : Mem := fun a =>
  if 0x7800 ≤ a.toNat ∧ a.toNat < 0x7840 then (pkTr (bytesAt m 0x8000 p.pkLen)).getD (a.toNat - 0x7800) 0
  else above satMemVP0 m a

theorem satMemVP_low {p : Params} {m : Mem} {x : Addr} (hx : x.toNat < 0x7800) : satMemVP p m x = satMemVP0 x := by
  simp only [satMemVP, show ¬(0x7800 ≤ x.toNat ∧ x.toNat < 0x7840) by omega, ↓reduceIte]
  exact above_low (a := satMemVP0) (m := m) (by omega)

theorem satMemVP_high {p : Params} {m : Mem} {i : Nat} (hi : i < 2 ^ 32) :
    satMemVP p m (0x8000 + BitVec.ofNat 64 i) = m (0x8000 + BitVec.ofNat 64 i) := by
  have e : (0x8000 + BitVec.ofNat 64 i : Addr).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
  simp only [satMemVP, e, show ¬(0x7800 ≤ 0x8000 + i ∧ 0x8000 + i < 0x7840) by omega, ↓reduceIte]
  exact above_eq hi

theorem verifyPrepared_sat {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (verifyMessageKContract p (preparedPublicKeyBytes p) (preparedTr p) X86.abi 172).pre s := by
  obtain ⟨m, hm⟩ := PreparedKey.public_at Verify.prims_ok hp3
  have hb : preparedPublicKeyBytes p < 2 ^ 32 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hk : PreparedPublicKey p (satMemVP p m) 0x8000 := public_congr hm fun i hi => satMemVP_high (by omega)
  have hkb : bytesAt (satMemVP p m) 0x8000 p.pkLen = bytesAt m 0x8000 p.pkLen :=
    Proof.MlKem.bytesAt_congr fun i hi => satMemVP_high (by simp only [preparedPublicKeyBytes] at hb; omega)
  have htr : bytesAt (satMemVP p m) 0x7800 64 = pkTr (bytesAt (satMemVP p m) 0x8000 p.pkLen) := by
    rw [hkb]
    apply Proof.MlKem.bytesAt_eq (H_length _ _)
    intro i hi
    have he : ((0x7800 : Addr) + BitVec.ofNat 64 i).toNat = 0x7800 + i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
    simp only [satMemVP, he, show 0x7800 ≤ 0x7800 + i ∧ 0x7800 + i < 0x7840 by omega, and_self, ↓reduceIte,
      Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [pkTr, H_length]; omega), Option.getD_some]
    rfl
  refine ⟨Proof.MlKem.X86.satState (satMemVP p m) [⟨0x8000, preparedPublicKeyBytes p⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩,
    ⟨0x3000, p.sigLen⟩, ⟨0x7800, 64⟩] [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩], ?_⟩
  have a0 : ∀ τ : State, τ.mem = satMemVP p m → τ.gpr .esp = 0x5000 →
      arg τ 0 = 0x8000 ∧ arg τ 1 = 0x2000 ∧ arg τ 2 = 0 ∧ arg τ 3 = 0x2000 ∧ arg τ 4 = 0 ∧ arg τ 5 = 0x3000 ∧
        arg τ 6 = 0x10000 ∧ arg τ 7 = 0x7800 := by
    intro τ e he
    simp only [arg, argAddr, e, he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [Mem.readW_congr (m' := satMemVP0) fun j hj => satMemVP_low ?_]
    all_goals first | kernel_rfl | (revert hj; revert j; decide)
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := a0 (Proof.MlKem.X86.satState (satMemVP p m)
    [⟨0x8000, preparedPublicKeyBytes p⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩, ⟨0x7800, 64⟩]
    [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) rfl rfl
  have ag : argAddr (Proof.MlKem.X86.satState (satMemVP p m) [⟨0x8000, preparedPublicKeyBytes p⟩, ⟨0x2000, 0⟩,
    ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩, ⟨0x7800, 64⟩] [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]) 0 = 0x5004 := rfl
  sig_pre [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  simp only [b0, b1, b2, b3, b4, b5, b6, b7, ag]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    and_intros
    all_goals first
      | exact hk
      | exact htr
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

private theorem noSp_all {f : Prog isa} (h : NoSp f) :
    f.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simp only [h i hi, Bool.not_false]

-- Check the wrapper once without re-evaluating its verified callee.
private theorem entryBody_all {q : Instr → Bool} {f : Prog isa}
    (hf : f.allInstrs q = true) (p : Params) (pre : Prog isa) (n : String) :
    (VG.Impl.MlDsa.X86.Sign.entryBody p pre n f).allInstrs q =
      (VG.Impl.MlDsa.X86.Sign.entryBody p pre n (.block [])).allInstrs q := by
  simp only [VG.Impl.MlDsa.X86.Sign.entryBody, VG.Impl.MlDsa.X86.KeyGen.callPR,
    VG.Impl.MlKem.X86.callRet, Code.allInstrs, hf]

private theorem signEntry_all {q : Instr → Bool} {f : Prog isa}
    (hf : f.allInstrs q = true) (p : Params) (n : String) :
    (signEntry p n f).allInstrs q = (signEntry p n (.block [])).allInstrs q := by
  simp only [signEntry, VG.Impl.MlKem.X86.leaf, Code.allInstrs, entryBody_all hf]

private theorem signPrepared_all {q : Instr → Bool} {f : Prog isa}
    (hf : f.allInstrs q = true) (p : Params) (n : String) :
    (signPrepared p n f).allInstrs q = (signPrepared p n (.block [])).allInstrs q := by
  simp only [signPrepared, VG.Impl.MlKem.X86.leaf, Code.allInstrs, entryBody_all hf]

/-! ## ML-DSA-44 -/

private theorem core44_noSp : NoSp (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44) := NoSp.of_all (by lit_decide)

theorem sign44_verified : Verified X86.target (signEntry mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44)) (signContract mlDsa44 X86.abi 136) :=
  SignEntry.entry_verified (.inl rfl) Sign.signCore44_verified core44_noSp (by lit_decide)
    (by native_taint_decide) (NoSp.of_all (by rw [entryBody_all (noSp_all core44_noSp)]; lit_decide))

theorem signPrepared44_verified :
    Verified X86.target (signPrepared mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44)) (Proof.MlDsa.preparedSignContract mlDsa44 X86.abi 136) :=
  SignEntry.prepared_verified (.inl rfl) Sign.signCore44_verified core44_noSp (by lit_decide)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (NoSp.of_all (by rw [entryBody_all (noSp_all core44_noSp)]; lit_decide))
    (PreparedKey.prepared_sign_sat Verify.prims_ok (.inl rfl))

theorem verify44_verified : Verified X86.target Impl.MlDsa.X86.Verify.verify44 (verifyContract mlDsa44 X86.abi 136) :=
  VerifyEntry.entry_verified Verify.prims_ok (.inl rfl) Verify.verifyCore44_verified (NoSp.of_all (by lit_decide))
    (by lit_decide) (by native_taint_decide) (NoSp.of_all (by lit_decide))

theorem verifyPrepared44_verified :
    Verified X86.target (verifyPreparedOf mlDsa44 "mldsa44") (Proof.MlDsa.preparedVerifyContract mlDsa44 X86.abi 136) :=
  VerifyEntry.prepared_verified (.inl rfl) Verify.verifyCore44_verified (NoSp.of_all (by lit_decide)) (by lit_decide)
    (by native_taint_decide) (NoSp.of_all (by lit_decide)) (PreparedKey.prepared_verify_sat Verify.prims_ok (.inl rfl))

theorem sign44Fn : SignFn mlDsa44 (plainKey mlDsa44.skLen) (signEntry mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44)) :=
  ⟨by rw [← signContract_eq]; exact sign44_verified, NoSp.of_all (by rw [signEntry_all (noSp_all core44_noSp)]; lit_decide), by lit_decide⟩
theorem signPrepared44Fn : SignFn mlDsa44 (secretKey mlDsa44) (signPrepared mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44)) :=
  ⟨by rw [← preparedSignContract_eq]; exact signPrepared44_verified, NoSp.of_all (by rw [signPrepared_all (noSp_all core44_noSp)]; lit_decide), by lit_decide⟩
theorem verify44Fn : VerifyFn mlDsa44 (plainKey mlDsa44.pkLen) Impl.MlDsa.X86.Verify.verify44 :=
  ⟨by rw [← verifyContract_eq]; exact verify44_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
theorem verifyPrepared44Fn : VerifyFn mlDsa44 (publicKey mlDsa44) (verifyPreparedOf mlDsa44 "mldsa44") :=
  ⟨by rw [← preparedVerifyContract_eq]; exact verifyPrepared44_verified, NoSp.of_all (by lit_decide), by lit_decide⟩

theorem signMessage44_verified :
    Verified X86.target (signMessage sign44Api.name (signEntry mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44)) mlDsa44) (signMessageContract mlDsa44 X86.abi 176) := by
  rw [signMessageContract_eq]
  exact signMessage_verified (plainKey_ok (skLen_ge (List.mem_cons_self ..))) sign44Fn (by native_taint_decide) (signMessage_sat (List.mem_cons_self ..))

theorem signMessagePrepared44_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa44") (signPrepared mlDsa44 (Impl.MlDsa.X86.Sign.coreName "mldsa44") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44)) mlDsa44)
      (preparedSignMessageContract mlDsa44 X86.abi 176) := by
  rw [preparedSignMessageContract_eq]
  exact signMessage_verified (secretKey_ok (List.mem_cons_self ..)) signPrepared44Fn (by native_taint_decide) (signPrepared_sat (.inl rfl))

theorem verifyMessageCached44_verified :
    Verified X86.target (verifyMessageCached verify44Api.name Impl.MlDsa.X86.Verify.verify44 mlDsa44)
      (verifyMessageCachedContract mlDsa44 X86.abi 172) := by
  rw [verifyMessageCachedContract_eq]
  exact verifyMessageCached_verified (plainKey_ok (pkLen_ge (List.mem_cons_self ..))) (fun h => ⟨trivial, h⟩) verify44Fn
    (by native_taint_decide) (verifyMessageCached_sat (List.mem_cons_self ..))

theorem verifyMessagePrepared44_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.preparedName "mldsa44") (verifyPreparedOf mlDsa44 "mldsa44") mlDsa44)
      (preparedVerifyMessageContract mlDsa44 X86.abi 172) := by
  rw [preparedVerifyMessageContract_eq]
  exact verifyMessageCached_verified (publicKey_ok (List.mem_cons_self ..)) (fun h => h) verifyPrepared44Fn
    (by native_taint_decide) (verifyPrepared_sat (.inl rfl))

/-! ## ML-DSA-65 -/

private theorem core65_noSp : NoSp (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65) := NoSp.of_all (by lit_decide)

theorem sign65_verified : Verified X86.target (signEntry mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65)) (signContract mlDsa65 X86.abi 136) :=
  SignEntry.entry_verified (.inr (.inl rfl)) Sign.signCore65_verified core65_noSp (by lit_decide)
    (by native_taint_decide) (NoSp.of_all (by rw [entryBody_all (noSp_all core65_noSp)]; lit_decide))

theorem signPrepared65_verified :
    Verified X86.target (signPrepared mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65)) (Proof.MlDsa.preparedSignContract mlDsa65 X86.abi 136) :=
  SignEntry.prepared_verified (.inr (.inl rfl)) Sign.signCore65_verified core65_noSp (by lit_decide)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (NoSp.of_all (by rw [entryBody_all (noSp_all core65_noSp)]; lit_decide))
    (PreparedKey.prepared_sign_sat Verify.prims_ok (.inr (.inl rfl)))

theorem verify65_verified : Verified X86.target Impl.MlDsa.X86.Verify.verify65 (verifyContract mlDsa65 X86.abi 136) :=
  VerifyEntry.entry_verified Verify.prims_ok (.inr (.inl rfl)) Verify.verifyCore65_verified (NoSp.of_all (by lit_decide))
    (by lit_decide) (by native_taint_decide) (NoSp.of_all (by lit_decide))

theorem verifyPrepared65_verified :
    Verified X86.target (verifyPreparedOf mlDsa65 "mldsa65") (Proof.MlDsa.preparedVerifyContract mlDsa65 X86.abi 136) :=
  VerifyEntry.prepared_verified (.inr (.inl rfl)) Verify.verifyCore65_verified (NoSp.of_all (by lit_decide)) (by lit_decide)
    (by native_taint_decide) (NoSp.of_all (by lit_decide)) (PreparedKey.prepared_verify_sat Verify.prims_ok (.inr (.inl rfl)))

theorem sign65Fn : SignFn mlDsa65 (plainKey mlDsa65.skLen) (signEntry mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65)) :=
  ⟨by rw [← signContract_eq]; exact sign65_verified, NoSp.of_all (by rw [signEntry_all (noSp_all core65_noSp)]; lit_decide), by lit_decide⟩
theorem signPrepared65Fn : SignFn mlDsa65 (secretKey mlDsa65) (signPrepared mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65)) :=
  ⟨by rw [← preparedSignContract_eq]; exact signPrepared65_verified, NoSp.of_all (by rw [signPrepared_all (noSp_all core65_noSp)]; lit_decide), by lit_decide⟩
theorem verify65Fn : VerifyFn mlDsa65 (plainKey mlDsa65.pkLen) Impl.MlDsa.X86.Verify.verify65 :=
  ⟨by rw [← verifyContract_eq]; exact verify65_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
theorem verifyPrepared65Fn : VerifyFn mlDsa65 (publicKey mlDsa65) (verifyPreparedOf mlDsa65 "mldsa65") :=
  ⟨by rw [← preparedVerifyContract_eq]; exact verifyPrepared65_verified, NoSp.of_all (by lit_decide), by lit_decide⟩

theorem signMessage65_verified :
    Verified X86.target (signMessage sign65Api.name (signEntry mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65)) mlDsa65) (signMessageContract mlDsa65 X86.abi 176) := by
  rw [signMessageContract_eq]
  exact signMessage_verified (plainKey_ok (skLen_ge (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) sign65Fn (by native_taint_decide) (signMessage_sat (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem signMessagePrepared65_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa65") (signPrepared mlDsa65 (Impl.MlDsa.X86.Sign.coreName "mldsa65") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65)) mlDsa65)
      (preparedSignMessageContract mlDsa65 X86.abi 176) := by
  rw [preparedSignMessageContract_eq]
  exact signMessage_verified (secretKey_ok (List.mem_cons_of_mem _ (List.mem_cons_self ..))) signPrepared65Fn (by native_taint_decide) (signPrepared_sat (.inr (.inl rfl)))

theorem verifyMessageCached65_verified :
    Verified X86.target (verifyMessageCached verify65Api.name Impl.MlDsa.X86.Verify.verify65 mlDsa65)
      (verifyMessageCachedContract mlDsa65 X86.abi 172) := by
  rw [verifyMessageCachedContract_eq]
  exact verifyMessageCached_verified (plainKey_ok (pkLen_ge (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (fun h => ⟨trivial, h⟩) verify65Fn
    (by native_taint_decide) (verifyMessageCached_sat (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem verifyMessagePrepared65_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.preparedName "mldsa65") (verifyPreparedOf mlDsa65 "mldsa65") mlDsa65)
      (preparedVerifyMessageContract mlDsa65 X86.abi 172) := by
  rw [preparedVerifyMessageContract_eq]
  exact verifyMessageCached_verified (publicKey_ok (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (fun h => h) verifyPrepared65Fn
    (by native_taint_decide) (verifyPrepared_sat (.inr (.inl rfl)))

/-! ## ML-DSA-87 -/

private theorem core87_noSp : NoSp (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87) := NoSp.of_all (by lit_decide)

theorem sign87_verified : Verified X86.target (signEntry mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87)) (signContract mlDsa87 X86.abi 136) :=
  SignEntry.entry_verified (.inr (.inr rfl)) Sign.signCore87_verified core87_noSp (by lit_decide)
    (by native_taint_decide) (NoSp.of_all (by rw [entryBody_all (noSp_all core87_noSp)]; lit_decide))

theorem signPrepared87_verified :
    Verified X86.target (signPrepared mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87)) (Proof.MlDsa.preparedSignContract mlDsa87 X86.abi 136) :=
  SignEntry.prepared_verified (.inr (.inr rfl)) Sign.signCore87_verified core87_noSp (by lit_decide)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (NoSp.of_all (by rw [entryBody_all (noSp_all core87_noSp)]; lit_decide))
    (PreparedKey.prepared_sign_sat Verify.prims_ok (.inr (.inr rfl)))

theorem verify87_verified : Verified X86.target Impl.MlDsa.X86.Verify.verify87 (verifyContract mlDsa87 X86.abi 136) :=
  VerifyEntry.entry_verified Verify.prims_ok (.inr (.inr rfl)) Verify.verifyCore87_verified (NoSp.of_all (by lit_decide))
    (by lit_decide) (by native_taint_decide) (NoSp.of_all (by lit_decide))

theorem verifyPrepared87_verified :
    Verified X86.target (verifyPreparedOf mlDsa87 "mldsa87") (Proof.MlDsa.preparedVerifyContract mlDsa87 X86.abi 136) :=
  VerifyEntry.prepared_verified (.inr (.inr rfl)) Verify.verifyCore87_verified (NoSp.of_all (by lit_decide)) (by lit_decide)
    (by native_taint_decide) (NoSp.of_all (by lit_decide)) (PreparedKey.prepared_verify_sat Verify.prims_ok (.inr (.inr rfl)))

theorem sign87Fn : SignFn mlDsa87 (plainKey mlDsa87.skLen) (signEntry mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87)) :=
  ⟨by rw [← signContract_eq]; exact sign87_verified, NoSp.of_all (by rw [signEntry_all (noSp_all core87_noSp)]; lit_decide), by lit_decide⟩
theorem signPrepared87Fn : SignFn mlDsa87 (secretKey mlDsa87) (signPrepared mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87)) :=
  ⟨by rw [← preparedSignContract_eq]; exact signPrepared87_verified, NoSp.of_all (by rw [signPrepared_all (noSp_all core87_noSp)]; lit_decide), by lit_decide⟩
theorem verify87Fn : VerifyFn mlDsa87 (plainKey mlDsa87.pkLen) Impl.MlDsa.X86.Verify.verify87 :=
  ⟨by rw [← verifyContract_eq]; exact verify87_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
theorem verifyPrepared87Fn : VerifyFn mlDsa87 (publicKey mlDsa87) (verifyPreparedOf mlDsa87 "mldsa87") :=
  ⟨by rw [← preparedVerifyContract_eq]; exact verifyPrepared87_verified, NoSp.of_all (by lit_decide), by lit_decide⟩

theorem signMessage87_verified :
    Verified X86.target (signMessage sign87Api.name (signEntry mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87)) mlDsa87) (signMessageContract mlDsa87 X86.abi 176) := by
  rw [signMessageContract_eq]
  exact signMessage_verified (plainKey_ok (skLen_ge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) sign87Fn (by native_taint_decide) (signMessage_sat (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem signMessagePrepared87_verified :
    Verified X86.target (signMessage (Impl.MlDsa.X86.Sign.preparedName "mldsa87") (signPrepared mlDsa87 (Impl.MlDsa.X86.Sign.coreName "mldsa87") (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87)) mlDsa87)
      (preparedSignMessageContract mlDsa87 X86.abi 176) := by
  rw [preparedSignMessageContract_eq]
  exact signMessage_verified (secretKey_ok (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) signPrepared87Fn (by native_taint_decide) (signPrepared_sat (.inr (.inr rfl)))

theorem verifyMessageCached87_verified :
    Verified X86.target (verifyMessageCached verify87Api.name Impl.MlDsa.X86.Verify.verify87 mlDsa87)
      (verifyMessageCachedContract mlDsa87 X86.abi 172) := by
  rw [verifyMessageCachedContract_eq]
  exact verifyMessageCached_verified (plainKey_ok (pkLen_ge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) (fun h => ⟨trivial, h⟩) verify87Fn
    (by native_taint_decide) (verifyMessageCached_sat (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem verifyMessagePrepared87_verified :
    Verified X86.target (verifyMessageCached (Impl.MlDsa.X86.Verify.preparedName "mldsa87") (verifyPreparedOf mlDsa87 "mldsa87") mlDsa87)
      (preparedVerifyMessageContract mlDsa87 X86.abi 172) := by
  rw [preparedVerifyMessageContract_eq]
  exact verifyMessageCached_verified (publicKey_ok (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (fun h => h) verifyPrepared87Fn
    (by native_taint_decide) (verifyPrepared_sat (.inr (.inr rfl)))

end VG.Proof.MlDsa.X86.Message
