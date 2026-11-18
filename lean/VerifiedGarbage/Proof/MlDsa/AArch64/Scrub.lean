module

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Message
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SignEntryTiming
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on AArch64, without secret residue

The postconditions of key generation, of `pk_tr` and of signing a message
(with a key or a prepared key) read the memory on return only within their
outputs, and those of verifying a message not at all (`ScrubAll.ScrubAllOk`,
as x86-64's `Proof/MlDsa/X86_64/Scrub.lean` proves them): each
implementation, generic over the Keccak-f[1600] implementation it calls,
returns with every register it may leave secret cleared and its whole stack
zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.MlDsa

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

variable (p : Params)

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem keyGenOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (keyGenContract p (abi.withConsts (c₀ :: cs)) W) W ((keyGenSig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := keyGenSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seed, pk, sk, sc], _ =>
      simp only [keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Outcome _ r (Spec.Sha3.bytesAt m₂ pk p.pkLen, Spec.Sha3.bytesAt m₂ sk p.skLen)
      rw [bytesAt_of (Nat.le_refl _) hb.2.1, bytesAt_of (Nat.le_refl _) hb.2.2.1]
      exact h

theorem pkTrOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (pkTrContract p abi W) W ((pkTrSig p).retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := pkTrSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [pk, tr, sc], _ =>
      simp only [pkTrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sha3.bytesAt m₂ tr 64 = _
      rw [bytesAt_of (Nat.le_refl _) hb.2.1]
      exact h


/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem signMessageOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (signMessageContract p (abi.withConsts (c₀ :: cs)) W) W ((signMessageSig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := signMessageSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [signMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem preparedSignMessageOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (preparedSignMessageContract p (abi.withConsts (c₀ :: cs)) W) W ((preparedSignMessageSig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := preparedSignMessageSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [preparedSignMessageSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2
        | some M' => Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M'
            (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem verifyMessageCachedOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (verifyMessageCachedContract p (abi.withConsts (c₀ :: cs)) W) W ((verifyMessageCachedSig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := verifyMessageCachedSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem preparedVerifyMessageOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (preparedVerifyMessageContract p (abi.withConsts (c₀ :: cs)) W) W ((preparedVerifyMessageSig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := preparedVerifyMessageSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h


/-! ## The contracts the registrations state -/

open VG.Proof.MlDsa.AArch64.PreparedKey (messageSignK messageVerifyK)

theorem signMessagePairedOk : ScrubAllOk
    (messageSignK p false (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 64
    ((signMessageSig p).retBits abi.ptrBits) := by
  rw [messageSignK, ite_eq_right Bool.false_ne_true, Proof.MlDsa.AArch64.Sign.pairedSignRootConsts_eq]
  exact signMessageOk_consts p 64 _ _

theorem preparedSignMessagePairedOk : ScrubAllOk
    (messageSignK p true (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 64
    ((preparedSignMessageSig p).retBits abi.ptrBits) := by
  rw [messageSignK, ite_eq_left rfl, Proof.MlDsa.AArch64.Sign.pairedSignRootConsts_eq]
  exact preparedSignMessageOk_consts p 64 _ _

theorem verifyMessageCachedSelectedOk : ScrubAllOk
    (messageVerifyK p false Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 64
    ((verifyMessageCachedSig p).retBits abi.ptrBits) := by
  rw [messageVerifyK, ite_eq_right Bool.false_ne_true]
  exact verifyMessageCachedOk_consts p 64 _ _

theorem preparedVerifyMessageSelectedOk : ScrubAllOk
    (messageVerifyK p true Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 64
    ((preparedVerifyMessageSig p).retBits abi.ptrBits) := by
  rw [messageVerifyK, ite_eq_left rfl]
  exact preparedVerifyMessageOk_consts p 64 _ _

/-! ## Signing and verifying `μ` -/

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem signOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (signContract p (abi.withConsts (c₀ :: cs)) W) W ((signSig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := signSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [signSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.1
      show Outcome (fun b => signMu p b (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m mu 64)
        (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem preparedSignOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (preparedSignContract p (abi.withConsts (c₀ :: cs)) W) W ((preparedSignSig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := preparedSignSig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, mu, rnd, sig, sc], _ =>
      simp only [Spec.MlDsa.preparedSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.1
      show Outcome (fun b => signMu p b (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m mu 64)
        (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m₂ sig p.sigLen)
      rw [e]
      exact h

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem verifyOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (verifyContract p (abi.withConsts (c₀ :: cs)) W) W ((verifySig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := verifySig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

/-- `ScrubAllOk` of the contract, for code that takes tables of constants. -/
theorem preparedVerifyOk_consts (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))
    (hW : 0 < W := by decide) :
    ScrubAllOk (preparedVerifyContract p (abi.withConsts (c₀ :: cs)) W) W ((preparedVerifySig p).retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := preparedVerifySig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _], _ => exact h

open VG.Proof.MlDsa.AArch64.PreparedKey (rawSignK rawVerifyK)

theorem signPairedOk : ScrubAllOk
    (rawSignK p false (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 64
    ((signSig p).retBits abi.ptrBits) := by
  rw [rawSignK, ite_eq_right Bool.false_ne_true, Proof.MlDsa.AArch64.Sign.pairedSignRootConsts_eq]
  exact signOk_consts p 64 _ _

theorem preparedSignPairedOk : ScrubAllOk
    (rawSignK p true (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 64
    ((preparedSignSig p).retBits abi.ptrBits) := by
  rw [rawSignK, ite_eq_left rfl, Proof.MlDsa.AArch64.Sign.pairedSignRootConsts_eq]
  exact preparedSignOk_consts p 64 _ _

theorem verifySelectedOk : ScrubAllOk
    (rawVerifyK p false Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 64
    ((verifySig p).retBits abi.ptrBits) := by
  rw [rawVerifyK, ite_eq_right Bool.false_ne_true]
  exact verifyOk_consts p 64 _ _

theorem preparedVerifySelectedOk : ScrubAllOk
    (rawVerifyK p true Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 64
    ((preparedVerifySig p).retBits abi.ptrBits) := by
  rw [rawVerifyK, ite_eq_left rfl]
  exact preparedVerifyOk_consts p 64 _ _

/-! ## The entries the message functions call -/

/-- The message functions call the entries as emitted, scrubbed whole: that
code keeps `Message.DLe 4`, its frame of 64 bytes being 4 units, whatever
registers it clears. -/
theorem dle_scrubAll {c : Prog VG.AArch64.isa} (cl : VG.Impl.Residue.AArch64.Clear)
    (h : VG.Proof.MlDsa.AArch64.Message.DLe 4 c) :
    VG.Proof.MlDsa.AArch64.Message.DLe 4 (VG.Impl.Residue.AArch64.scrubAll 64 32 cl c) := by
  refine ⟨?_, ?_⟩
  · have hl := h.le
    show Code.aarch64Depth (.seq (VG.Impl.Residue.AArch64.withRet 32
      (.seq c (.block (VG.Impl.Residue.AArch64.clearsOf cl))))
      (VG.Impl.Residue.AArch64.scrubTailG 64 (List.range 4))) ≤ 4
    simp only [VG.Impl.Residue.AArch64.withRet, VG.Impl.Residue.AArch64.scrubTailG, Code.aarch64Depth,
      Instr.frameUnits, Nat.max_le, Nat.zero_le, Nat.reduceDiv, Nat.zero_add, Nat.le_refl, and_true]
    exact hl
  · have hn := h.nd
    show Code.all (fun i => !i.touchesDit) (.seq (VG.Impl.Residue.AArch64.withRet 32
      (.seq c (.block (VG.Impl.Residue.AArch64.clearsOf cl))))
      (VG.Impl.Residue.AArch64.scrubTailG 64 (List.range 4))) = true
    simp only [VG.Impl.Residue.AArch64.withRet, VG.Impl.Residue.AArch64.scrubTailG, Code.all, hn,
      Bool.true_and, VG.Impl.Residue.AArch64.clearsOf, List.all_append, List.all_map,
      Function.comp_def]
    simp [Instr.touchesDit]
    exact ⟨by decide, by decide⟩

open VG.Proof.MlDsa.AArch64.PreparedKey (MessageSignFn MessageVerifyFn message_sign_fn message_verify_fn)

/-- What a message signing function calls: the signing entry, scrubbed whole. -/
theorem message_sign_fn_scrub (v : Proof.Sha3.AArch64.Permutation) (hp : Proof.MlDsa.AArch64.Sign.Ok3 p)
    (name : String) (prepared : Bool) :
    MessageSignFn p prepared
      (VG.Impl.Residue.AArch64.scrubAll 64 32
        (VG.Impl.Residue.AArch64.Clear.of (Proof.MlDsa.AArch64.PreparedKey.signCode v p name prepared))
        (Proof.MlDsa.AArch64.PreparedKey.signCode v p name prepared)) := by
  obtain h := message_sign_fn v hp name prepared
  refine ⟨Verified.scrubAll (VG.Impl.Residue.AArch64.Clear.of_wf _) h.ver (by decide) (by decide) ?_, dle_scrubAll _ h.dle⟩
  cases prepared
  · exact signPairedOk p
  · exact preparedSignPairedOk p

/-- What a message verification function calls: the verification entry, scrubbed whole. -/
theorem message_verify_fn_scrub (v : Proof.Sha3.AArch64.Permutation) (hp : Proof.MlDsa.AArch64.Sign.Ok3 p)
    (name : String) (prepared : Bool) :
    MessageVerifyFn p prepared
      (VG.Impl.Residue.AArch64.scrubAll 64 32
        (VG.Impl.Residue.AArch64.Clear.of (Proof.MlDsa.AArch64.PreparedKey.verifyCode v p name prepared))
        (Proof.MlDsa.AArch64.PreparedKey.verifyCode v p name prepared)) := by
  obtain h := message_verify_fn v hp name prepared
  refine ⟨Verified.scrubAll (VG.Impl.Residue.AArch64.Clear.of_wf _) h.ver (by decide) (by decide) ?_, dle_scrubAll _ h.dle⟩
  cases prepared
  · exact verifySelectedOk p
  · exact preparedVerifySelectedOk p

/-! ## Preparing keys -/

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

theorem pub_bytes : ∀ p ∈ [mlDsa44, mlDsa65, mlDsa87], preparedPublicKeyBytes p < 2 ^ 64 := by decide
theorem sec_bytes : ∀ p ∈ [mlDsa44, mlDsa65, mlDsa87], preparedSecretKeyBytes p < 2 ^ 64 := by decide

theorem mem_of {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    p ∈ [mlDsa44, mlDsa65, mlDsa87] := by
  rcases hp with rfl | rfl | rfl <;> simp

theorem preparePublicOk {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (W : Nat)
    (hW : 0 < W := by decide) :
    ScrubAllOk (preparePublicKeyContract p abi W) W ((preparePublicKeySig p).retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := preparePublicKeySig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [pk, prep, sc], _ =>
      simp only [preparePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      have hw := agreeBuf (pub_bytes p (mem_of hp)) hb.2.1
      obtain ⟨h₁, h₂⟩ := h
      change Spec.Sha3.bytesAt m₁ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen at h₁
      change PreparedPublicKey p m₁ prep at h₂
      change Spec.Sha3.bytesAt m₂ prep p.pkLen = Spec.Sha3.bytesAt m pk p.pkLen ∧ PreparedPublicKey p m₂ prep
      have e := bytesAt_congr (n := p.pkLen) (by simp [preparedPublicKeyBytes]) hw
      refine ⟨e.trans h₁, fun i hi => ?_⟩
      rw [e]
      exact polyStored_congr (N := preparedPublicKeyBytes p)
        (by simp only [preparedPublicKeyBytes]; have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

theorem prepareSecretOk {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (W : Nat)
    (hW : 0 < W := by decide) :
    ScrubAllOk (prepareSecretKeyContract p abi W) W ((prepareSecretKeySig p).retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := prepareSecretKeySig p) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, prep, sc], _ =>
      simp only [prepareSecretKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      have hw := agreeBuf (sec_bytes p (mem_of hp)) hb.2.1
      obtain ⟨h₁, h₂⟩ := h
      change Spec.Sha3.bytesAt m₁ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen at h₁
      change PreparedSecretKey p m₁ prep at h₂
      change Spec.Sha3.bytesAt m₂ prep p.skLen = Spec.Sha3.bytesAt m sk p.skLen ∧ PreparedSecretKey p m₂ prep
      have e := bytesAt_congr (n := p.skLen) (by simp [preparedSecretKeyBytes]) hw
      refine ⟨e.trans h₁, fun i hi => ?_⟩
      rw [e]
      exact polyStored_congr (N := preparedSecretKeyBytes p)
        (by simp only [preparedSecretKeyBytes]
            have := Nat.mul_le_mul_left (4 * n) (show i + 1 ≤ p.ℓ + 2 * p.k by omega_using [hi])
            rw [Nat.mul_add, Nat.mul_one] at this; omega_using [this]) hw (h₂ i hi)

end VG.Proof.MlDsa.AArch64.Scrub
