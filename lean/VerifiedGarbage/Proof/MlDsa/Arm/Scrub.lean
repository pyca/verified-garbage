module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.PkTr
public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Verified
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
meta import VerifiedGarbage.Proof.MlDsa.Arm.PkTr
meta import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Verified
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
meta import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Verified
meta import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-DSA on ARMv7, without secret residue

ML-DSA's public functions keep secrets in the frames of the functions they
call, and none makes an indirect call. Their postconditions read the memory
on return only within their outputs, and those of verification not at all
(`Arm.Scrub.PostOut`): each is registered followed by a wipe of the stack its
contract reserves, and by instructions that set the registers a callee may
change, but the result, and the flags to constants (`Arm.Scrub.scrubRegF`).

The wipe is a frame of the model, of a multiple of 8 bytes, so each contract
reserves one:

* `pk_tr`: 8 bytes, which its sponge uses.
* Key generation: 40, and the preparations of keys: 48, which their proofs
  are stated with.
* `sign` and `sign_prepared`: 48, and `verify` and `verify_prepared`: 56.
  Their proofs are with the 44 and 52 bytes the message functions call them
  with, and hold with more (`Arm.Scrub.Verified.stack_le`).
* The message functions: 56, for the 52 their proofs are with.

The message functions call the functions on `μ` (`vg_mldsa*_sign`, …) as
they are verified, without the wipe, under names of their own
(`signEntryName`, …), which the emitter writes as internal functions: their
own wipe covers the frames of those calls.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.Message (signMessage verifyMessageCached muHash)

/-! ## The postconditions -/

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

section
variable (p : Params) (stack : Nat)

theorem keyGenOut : PostOut (keyGenContract p Arm.abi stack) ((keyGenSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seed, pk, sk, sc], _ =>
      simp only [keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ pk p.pkLen, Spec.Sha3.bytesAt m₂ sk p.skLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.1, bytesAt_of (Nat.le_refl _) hb.2.2.1]
      exact h

theorem pkTrOut : PostOut (pkTrContract p Arm.abi stack) ((pkTrSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [pk, tr, sc], _ =>
      simp only [pkTrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sha3.bytesAt m₂ tr 64 = _
      rw [bytesAt_of (Nat.le_refl _) hb.2.1]
      exact h

theorem signOut : PostOut (signContract p Arm.abi stack) ((signSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [signSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem preparedSignOut :
    PostOut (Spec.MlDsa.preparedSignContract p Arm.abi stack) ((Spec.MlDsa.preparedSignSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [Spec.MlDsa.preparedSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.2.2.1]
      exact h

theorem signMessageOut : PostOut (signMessageContract p Arm.abi stack) ((signMessageSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [signMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int Arm.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int Arm.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem preparedSignMessageOut :
    PostOut (preparedSignMessageContract p Arm.abi stack) ((preparedSignMessageSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [preparedSignMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int Arm.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int Arm.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

theorem verifyOut : PostOut (verifyContract p Arm.abi stack) ((verifySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem preparedVerifyOut :
    PostOut (Spec.MlDsa.preparedVerifyContract p Arm.abi stack) ((Spec.MlDsa.preparedVerifySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

theorem verifyMessageCachedOut :
    PostOut (verifyMessageCachedContract p Arm.abi stack) ((verifyMessageCachedSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

theorem preparedVerifyMessageOut :
    PostOut (preparedVerifyMessageContract p Arm.abi stack) ((preparedVerifyMessageSig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

end

/-! ### Prepared keys -/

theorem agreeBuf {m₁ m₂ : Mem} {q : Addr} {N : Nat} (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hN, hi]))).symm

theorem bytesAt_congr {m₁ m₂ : Mem} {q : Addr} {n N : Nat} (hn : n ≤ N)
    (h : ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i)) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n :=
  List.map_congr_left fun i hi => h i (by have := List.mem_range.mp hi; omega_using [hn, this])

/-- A polynomial stored in the `1024` bytes at `q + d` of a buffer of `N`
bytes at `q`, in memories that agree on the buffer. -/
theorem polyStored_congr {m₁ m₂ : Mem} {q : Addr} {d N : Nat} {f : Poly} (hd : d + 4 * n ≤ N)
    (h : ∀ i < N, m₂ (q + BitVec.ofNat 64 i) = m₁ (q + BitVec.ofNat 64 i))
    (hf : PolyStored m₁ (q + BitVec.ofNat 64 d) f) : PolyStored m₂ (q + BitVec.ofNat 64 d) f := by
  intro i hi
  rw [← hf i hi]
  congr 1
  apply Mem.readW_congr
  intro t ht
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  exact h _ (by simp only [n] at hi hd; omega_using [hd, hi, ht])

variable {p : Params}

theorem key_bytes (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    preparedPublicKeyBytes p < 2 ^ 64 ∧ preparedSecretKeyBytes p < 2 ^ 64 := by
  rcases h3 with rfl | rfl | rfl <;> decide

theorem preparePublicOut (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (stack : Nat) :
    PostOut (preparePublicKeyContract p Arm.abi stack) ((preparePublicKeySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [preparePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (key_bytes h3).1 hb.2.1
    obtain ⟨h₁, h₂⟩ := h
    change Spec.Sha3.bytesAt m₁ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen at h₁
    change PreparedPublicKey p m₁ prep at h₂
    change Spec.Sha3.bytesAt m₂ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen ∧ PreparedPublicKey p m₂ prep
    have e := bytesAt_congr (n := p.pkLen) (by simp [preparedPublicKeyBytes]) hw
    refine ⟨?_, fun i hi => ?_⟩
    · exact e.trans h₁
    · rw [e]
      exact polyStored_congr (N := preparedPublicKeyBytes p)
        (by simp only [preparedPublicKeyBytes]; have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

theorem prepareSecretOut (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (stack : Nat) :
    PostOut (prepareSecretKeyContract p Arm.abi stack) ((prepareSecretKeySig p).retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨prep, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [prepareSecretKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hw := agreeBuf (key_bytes h3).2 hb.2.1
    obtain ⟨h₁, h₂⟩ := h
    change Spec.Sha3.bytesAt m₁ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen at h₁
    change PreparedSecretKey p m₁ prep at h₂
    change Spec.Sha3.bytesAt m₂ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen ∧ PreparedSecretKey p m₂ prep
    have e := bytesAt_congr (n := p.skLen) (by simp [preparedSecretKeyBytes]) hw
    refine ⟨?_, fun i hi => ?_⟩
    · exact e.trans h₁
    · rw [e]
      exact polyStored_congr (N := preparedSecretKeyBytes p)
        (by simp only [preparedSecretKeyBytes]
            have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.ℓ + 2 * p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_8 : FrameOk 8 := by decide
theorem frameOk_40 : FrameOk 40 := by decide
theorem frameOk_48 : FrameOk 48 := by decide
theorem frameOk_56 : FrameOk 56 := by decide

section
variable (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
include h3

theorem mem_params : p ∈ Message.params := by
  simp only [Message.params, List.mem_cons, List.not_mem_nil, or_false]; exact h3

theorem keyGen_code : armStack (Impl.MlDsa.Arm.KeyGen.keyGen Impl.MlDsa.Arm.KeyGen.prims p) ≤ 40 ∧
    noIcall (Impl.MlDsa.Arm.KeyGen.keyGen Impl.MlDsa.Arm.KeyGen.prims p) = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

theorem pkTr_code : armStack (Impl.MlDsa.Arm.PkTr.pkTr p) ≤ 8 ∧ noIcall (Impl.MlDsa.Arm.PkTr.pkTr p) = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

theorem preparePublic_code : armStack (Impl.MlDsa.Arm.PreparedKey.preparePublic Sign.prims p) ≤ 48 ∧
    noIcall (Impl.MlDsa.Arm.PreparedKey.preparePublic Sign.prims p) = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

theorem prepareSecret_code : armStack (Impl.MlDsa.Arm.PreparedKey.prepareSecret Sign.prims p) ≤ 48 ∧
    noIcall (Impl.MlDsa.Arm.PreparedKey.prepareSecret Sign.prims p) = true := by
  rcases h3 with rfl | rfl | rfl <;> lit_decide

theorem signEntry_code (prepared : Bool) : armStack (Impl.MlDsa.Arm.Sign.signEntry Sign.prims p prepared) ≤ 44 ∧
    noIcall (Impl.MlDsa.Arm.Sign.signEntry Sign.prims p prepared) = true := by
  rcases h3 with rfl | rfl | rfl <;> cases prepared <;> lit_decide

theorem verifyEntry_code (prepared : Bool) :
    armStack (Impl.MlDsa.Arm.Verify.verifyEntry Impl.MlDsa.Arm.Verify.prims p prepared) ≤ 52 ∧
      noIcall (Impl.MlDsa.Arm.Verify.verifyEntry Impl.MlDsa.Arm.Verify.prims p prepared) = true := by
  rcases h3 with rfl | rfl | rfl <;> cases prepared <;> lit_decide

end

/-- `sign_message`'s frames are those of its sponge and its callee's below a
frame of 8 bytes, and it makes no indirect call if its callee makes none. -/
theorem signMessage_code {n : String} {c : Prog isa} (p : Params) (hc : armStack c ≤ 44 ∧ noIcall c = true) :
    armStack (signMessage n c p) ≤ 56 ∧ noIcall (signMessage n c p) = true := by
  obtain hm : armStack (muHash (.slotOff Impl.MlDsa.Arm.Message.fKey 64)) ≤ 56 ∧
      noIcall (muHash (.slotOff Impl.MlDsa.Arm.Message.fKey 64)) = true := by lit_decide
  simp only [signMessage, Impl.MlDsa.Arm.Message.top, armStack, noIcall, hm.2, hc.2, Bool.and_self,
    List.length_cons, List.length_nil, Nat.zero_max, Nat.max_zero, and_true]
  omega_using [hm.1, hc.1]

/-- `verify_message_cached`'s frames are those of its sponge and its callee's,
and it makes no indirect call if its callee makes none. -/
theorem verifyMessageCached_code {n : String} {c : Prog isa} (p : Params) (hc : armStack c ≤ 52 ∧ noIcall c = true) :
    armStack (verifyMessageCached n c p) ≤ 56 ∧ noIcall (verifyMessageCached n c p) = true := by
  obtain hm : armStack (muHash (.slot Impl.MlDsa.Arm.Message.fRnd)) ≤ 56 ∧
      noIcall (muHash (.slot Impl.MlDsa.Arm.Message.fRnd)) = true := by lit_decide
  simp only [verifyMessageCached, Impl.MlDsa.Arm.Message.top, armStack, noIcall, hm.2, hc.2, Bool.and_self,
    Nat.zero_max, Nat.max_zero, and_true]
  omega_using [hm.1, hc.1]

/-! ## The functions on `μ`, as the message functions call them -/

/-- The names the message functions call `vg_<module>_sign`,
`vg_<module>_sign_prepared`, `vg_<module>_verify` and
`vg_<module>_verify_prepared` by, as they are verified, without the wipe. -/
def signEntryName (module : String) : String := s!"vg_{module}_sign_entry"
def signPreparedEntryName (module : String) : String := s!"vg_{module}_sign_prepared_entry"
def verifyEntryName (module : String) : String := s!"vg_{module}_verify_entry"
def verifyPreparedEntryName (module : String) : String := s!"vg_{module}_verify_prepared_entry"

section
variable (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
include h3

theorem signFn : Message.SignFn p false (Impl.MlDsa.Arm.Sign.sign Sign.prims p) := by
  rcases h3 with rfl | rfl | rfl
  exacts [Message.sign44Fn, Message.sign65Fn, Message.sign87Fn]

theorem verifyFn : Message.VerifyFn p false (Impl.MlDsa.Arm.Verify.verify Impl.MlDsa.Arm.Verify.prims p) := by
  rcases h3 with rfl | rfl | rfl
  exacts [Message.verify44Fn, Message.verify65Fn, Message.verify87Fn]

/-! ## With a frame size of the model -/

theorem sign_verified :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign Sign.prims p) (signContract p Arm.abi 48) :=
  Verified.stack_le (by decide) (Sign.sign_verified h3) (Sign.sign_sat h3)

theorem signPrepared_verified :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.signPrepared Sign.prims p) (Spec.MlDsa.preparedSignContract p Arm.abi 48) :=
  Verified.stack_le (by decide) (Message.externalSign_verified (mem_params h3)) (Message.externalSign_sat (mem_params h3))

theorem verify_verified :
    Verified Arm.target (Impl.MlDsa.Arm.Verify.verify Impl.MlDsa.Arm.Verify.prims p) (verifyContract p Arm.abi 56) :=
  Verified.stack_le (by decide) (Verify.verify_verified h3) (Verify.verify_sat h3)

theorem verifyPrepared_verified :
    Verified Arm.target (Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims p)
      (Spec.MlDsa.preparedVerifyContract p Arm.abi 56) :=
  Verified.stack_le (by decide) (Message.externalVerify_verified (mem_params h3))
    (Message.externalVerify_sat (mem_params h3))

theorem signMessage_verified (n : String) :
    Verified Arm.target (signMessage n (Impl.MlDsa.Arm.Sign.sign Sign.prims p) p) (signMessageContract p Arm.abi 56) :=
  Verified.stack_le (by decide) (Message.signMessage_verified (signFn h3) (mem_params h3))
    (Message.signMessage_sat (mem_params h3))

theorem preparedSignMessage_verified (n : String) :
    Verified Arm.target (signMessage n (Impl.MlDsa.Arm.Sign.signPrepared Sign.prims p) p)
      (preparedSignMessageContract p Arm.abi 56) :=
  Verified.stack_le (by decide) (Message.preparedSignMessage_verified (Message.signPreparedFn h3) (mem_params h3))
    (Message.preparedSignMessage_sat (mem_params h3))

theorem verifyMessageCached_verified (n : String) :
    Verified Arm.target (verifyMessageCached n (Impl.MlDsa.Arm.Verify.verify Impl.MlDsa.Arm.Verify.prims p) p)
      (verifyMessageCachedContract p Arm.abi 56) :=
  Verified.stack_le (by decide) (Message.verifyMessageCached_verified (verifyFn h3) (mem_params h3))
    (Message.verifyMessageCached_sat (mem_params h3))

theorem preparedVerifyMessage_verified (n : String) :
    Verified Arm.target (verifyMessageCached n (Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims p) p)
      (preparedVerifyMessageContract p Arm.abi 56) :=
  Verified.stack_le (by decide) (Message.preparedVerifyMessage_verified (Message.verifyPreparedFn h3) (mem_params h3))
    (Message.preparedVerifyMessage_sat (mem_params h3))

end

/-! ## The registrations -/

section
variable (p : Params) (module name : String) (h3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)

/-- `vg_<module>_keygen`. -/
def keyGenReg : Registration (keyGenApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.KeyGen.keyGen Impl.MlDsa.Arm.KeyGen.prims p
      verified := KeyGen.keyGen_verified KeyGen.prims_ok p h3 }
    (keyGen_code h3).1 (keyGen_code h3).2 frameOk_40 (keyGenOut p _) rfl

/-- `vg_<module>_pk_tr`. -/
def pkTrReg : Registration (pkTrApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.PkTr.pkTr p
      verified := PkTr.pkTr_verified p h3 }
    (pkTr_code h3).1 (pkTr_code h3).2 frameOk_8 (pkTrOut p _) rfl

/-- `vg_<module>_prepare_verifying_key`. -/
def preparePublicReg : Registration (preparePublicKeyApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.PreparedKey.preparePublic Sign.prims p
      verified := PreparedKey.preparePublic_verified h3 }
    (preparePublic_code h3).1 (preparePublic_code h3).2 frameOk_48 (preparePublicOut h3 _) rfl

/-- `vg_<module>_prepare_signing_key`. -/
def prepareSecretReg : Registration (prepareSecretKeyApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.PreparedKey.prepareSecret Sign.prims p
      verified := PreparedKey.prepareSecret_verified h3 }
    (prepareSecret_code h3).1 (prepareSecret_code h3).2 frameOk_48 (prepareSecretOut h3 _) rfl

/-- `vg_<module>_sign`. -/
def signReg : Registration (signApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.Sign.sign Sign.prims p
      verified := sign_verified h3 }
    (Nat.le_trans (signEntry_code h3 false).1 (Nat.le_add_right 44 4)) (signEntry_code h3 false).2 frameOk_48 (signOut p _) rfl

/-- `vg_<module>_sign_prepared`. -/
def signPreparedReg : Registration (preparedSignApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.Sign.signPrepared Sign.prims p
      verified := signPrepared_verified h3 }
    (Nat.le_trans (signEntry_code h3 true).1 (Nat.le_add_right 44 4)) (signEntry_code h3 true).2 frameOk_48
    (preparedSignOut p _) rfl

/-- `vg_<module>_sign_message`. -/
def signMessageReg : Registration (signMessageApi p module name) Arm.target :=
  scrubRegF {
      code := signMessage (signEntryName module) (Impl.MlDsa.Arm.Sign.sign Sign.prims p) p
      verified := signMessage_verified h3 _ }
    (signMessage_code p (signEntry_code h3 false)).1 (signMessage_code p (signEntry_code h3 false)).2 frameOk_56
    (signMessageOut p _) rfl

/-- `vg_<module>_sign_message_prepared`. -/
def preparedSignMessageReg : Registration (preparedSignMessageApi p module name) Arm.target :=
  scrubRegF {
      code := signMessage (signPreparedEntryName module) (Impl.MlDsa.Arm.Sign.signPrepared Sign.prims p) p
      verified := preparedSignMessage_verified h3 _ }
    (signMessage_code p (signEntry_code h3 true)).1 (signMessage_code p (signEntry_code h3 true)).2 frameOk_56
    (preparedSignMessageOut p _) rfl

/-- `vg_<module>_verify`. -/
def verifyReg : Registration (verifyApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.Verify.verify Impl.MlDsa.Arm.Verify.prims p
      verified := verify_verified h3 }
    (Nat.le_trans (verifyEntry_code h3 false).1 (Nat.le_add_right 52 4)) (verifyEntry_code h3 false).2 frameOk_56
    (verifyOut p _) rfl

/-- `vg_<module>_verify_prepared`. -/
def verifyPreparedReg : Registration (preparedVerifyApi p module name) Arm.target :=
  scrubRegF {
      code := Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims p
      verified := verifyPrepared_verified h3 }
    (Nat.le_trans (verifyEntry_code h3 true).1 (Nat.le_add_right 52 4)) (verifyEntry_code h3 true).2 frameOk_56
    (preparedVerifyOut p _) rfl

/-- `vg_<module>_verify_message_cached`. -/
def verifyMessageCachedReg : Registration (verifyMessageCachedApi p module name) Arm.target :=
  scrubRegF {
      code := verifyMessageCached (verifyEntryName module)
        (Impl.MlDsa.Arm.Verify.verify Impl.MlDsa.Arm.Verify.prims p) p
      verified := verifyMessageCached_verified h3 _ }
    (verifyMessageCached_code p (verifyEntry_code h3 false)).1
    (verifyMessageCached_code p (verifyEntry_code h3 false)).2 frameOk_56 (verifyMessageCachedOut p _) rfl

/-- `vg_<module>_verify_message_prepared`. -/
def preparedVerifyMessageReg : Registration (preparedVerifyMessageApi p module name) Arm.target :=
  scrubRegF {
      code := verifyMessageCached (verifyPreparedEntryName module)
        (Impl.MlDsa.Arm.Verify.verifyPrepared Impl.MlDsa.Arm.Verify.prims p) p
      verified := preparedVerifyMessage_verified h3 _ }
    (verifyMessageCached_code p (verifyEntry_code h3 true)).1
    (verifyMessageCached_code p (verifyEntry_code h3 true)).2 frameOk_56 (preparedVerifyMessageOut p _) rfl

end

end VG.Proof.MlDsa.Arm.Scrub
