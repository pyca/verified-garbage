module

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Impl.MlDsa.AArch64.PkTr
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.MlDsa.AArch64.PkTr
import VerifiedGarbage.Proof.Sha3.AArch64.Scrub
import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Verified
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Impl.MlDsa.AArch64.Fn
import VerifiedGarbage.Proof.Framework.AArch64.SideFill
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedVerified
public import VerifiedGarbage.Impl.MlDsa.AArch64.Message
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Prepare
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Message
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedVerified
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
returns with every register the calling convention does not preserve cleared
and its whole stack zeroed (`Impl.MlDsa.AArch64.Fn`). `pk_tr` as emitted is
`Impl.MlDsa.AArch64.Fn.pkTr`, whose registers are its own with those its
permutation states it writes. `Fn` below has the theorems, which the
registrations bind.
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
      (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all
        (Proof.MlDsa.AArch64.PreparedKey.signCode v p name prepared)) := by
  obtain h := message_sign_fn v hp name prepared
  refine ⟨Verified.scrubAll clearAll_wf h.ver (by decide) (by decide) ?_, dle_scrubAll _ h.dle⟩
  cases prepared
  · exact signPairedOk p
  · exact preparedSignPairedOk p

/-- What a message verification function calls: the verification entry, scrubbed whole. -/
theorem message_verify_fn_scrub (v : Proof.Sha3.AArch64.Permutation) (hp : Proof.MlDsa.AArch64.Sign.Ok3 p)
    (name : String) (prepared : Bool) :
    MessageVerifyFn p prepared
      (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all
        (Proof.MlDsa.AArch64.PreparedKey.verifyCode v p name prepared)) := by
  obtain h := message_verify_fn v hp name prepared
  refine ⟨Verified.scrubAll clearAll_wf h.ver (by decide) (by decide) ?_, dle_scrubAll _ h.dle⟩
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

/-! ## What the cleanup needs of the code that prepares keys

`ScrubAll.scrubSide` of the two functions, with each parameter set:
evaluated here, by the kernel. -/

/-- Of preparing a verifying key. -/
theorem preparePublicSide {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    scrubSide (Impl.MlDsa.AArch64.PreparedKey.preparePublic p)
      80 ((preparePublicKeySig p).retBits abi.ptrBits) Impl.MlDsa.AArch64.Fn.preparePublicClear [] = true := by
  have e : ([mlDsa44, mlDsa65, mlDsa87].all fun p =>
      scrubSide (Impl.MlDsa.AArch64.PreparedKey.preparePublic p)
      80 ((preparePublicKeySig p).retBits abi.ptrBits) Impl.MlDsa.AArch64.Fn.preparePublicClear []) = true := by lit_decide
  exact List.all_eq_true.mp e p (mem_of hp)

/-- Of preparing a signing key. -/
theorem prepareSecretSide {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    scrubSide (Impl.MlDsa.AArch64.PreparedKey.prepareSecret p)
      80 ((prepareSecretKeySig p).retBits abi.ptrBits) Impl.MlDsa.AArch64.Fn.prepareSecretClear [] = true := by
  have e : ([mlDsa44, mlDsa65, mlDsa87].all fun p =>
      scrubSide (Impl.MlDsa.AArch64.PreparedKey.prepareSecret p)
      80 ((prepareSecretKeySig p).retBits abi.ptrBits) Impl.MlDsa.AArch64.Fn.prepareSecretClear []) = true := by lit_decide
  exact List.all_eq_true.mp e p (mem_of hp)

/-! ## `pk_tr`, with any implementation of the permutation

What the cleanup needs of `pk_tr`'s code is proved of its own instructions
once, with a permutation that does nothing in its place
(`Proof.Sha3.AArch64.Scrub.stub`), of the sponge's functions it calls in
`Proof.Sha3.AArch64.Scrub`, and of each implementation of the permutation
where it is defined (`Permutation.scrub`). -/

open VG.Proof.Sha3.AArch64.Scrub (stub absorbWith_side padWith_side squeezeWith_side)

private theorem pkTr_all {q : Instr → Bool} (c : Impl.Sha3.AArch64.Callee) (p : Params)
    (h0 : sideAll q (Impl.MlDsa.AArch64.PkTr.pkTrWith stub p) = true)
    (ha : sideAll q (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hp : sideAll q (Impl.Sha3.AArch64.Stream.padWith c) = true)
    (hs : sideAll q (Impl.Sha3.AArch64.Stream.squeezeWith c) = true) :
    sideAll q (Impl.MlDsa.AArch64.PkTr.pkTrWith c p) = true := by
  simp only [Impl.MlDsa.AArch64.PkTr.pkTrWith, Impl.MlDsa.AArch64.KeyGen.shake256With,
    Impl.MlKem.AArch64.hashWith, Impl.MlKem.AArch64.absorbsWith, Impl.MlKem.AArch64.squeezesWith,
    sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, ha, hp, hs, and_self]

/-- `pk_tr`'s own instructions write only the registers `Impl/` states
(`Impl.MlDsa.AArch64.Fn.pkTrOwn`), for any parameter set. -/
private theorem pkTr_own (p : Params) :
    calleeSide (Impl.MlDsa.AArch64.PkTr.pkTrWith stub p) Impl.MlDsa.AArch64.Fn.pkTrOwn = true := by
  kernel_rfl

theorem pkTr_side (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    scrubSide (Impl.MlDsa.AArch64.PkTr.pkTrWith v.callee p) 16 0
      (Impl.MlDsa.AArch64.Fn.pkTrOwn.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (pkTr_all v.callee p (sideAll_union_left (pkTr_own p)) (absorbWith_side v (by decide))
      (padWith_side v (by decide)) (squeezeWith_side v (by decide))) (by decide)
  simp only [Impl.MlDsa.AArch64.PkTr.pkTrWith, Impl.MlDsa.AArch64.KeyGen.shake256With,
    Impl.MlKem.AArch64.hashWith, Impl.MlKem.AArch64.absorbsWith, Impl.MlKem.AArch64.squeezesWith,
    Code.aarch64Depth, v.absorb_depth, v.pad_depth, v.squeeze_depth]
  decide

end VG.Proof.MlDsa.AArch64.Scrub

/-! ## The functions

Of preparing a key, and of `vg_mldsa*_pk_tr` with the implementation `v` of
the permutation: the code that is emitted (`Impl.MlDsa.AArch64.Fn`) meets the
function's contract in constant time and returns without secret residue. -/

namespace VG.Proof.MlDsa.AArch64.Fn

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.MlDsa

theorem preparePublic {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.preparePublic p) (preparePublicKeyContract p abi 80) 0 :=
  verifiedScrubbed (api := preparePublicKeyApi p "" "")
    { code := Impl.MlDsa.AArch64.PreparedKey.preparePublic p,
      verified := Proof.MlDsa.AArch64.PreparedKey.preparePublic_verified p hp }
    _ (Scrub.preparePublicOk hp 80) (Scrub.preparePublicSide hp)

theorem preparePublic44 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.preparePublic mlDsa44) (preparePublicKeyContract mlDsa44 abi 80) 0 :=
  preparePublic (.inl rfl)

theorem preparePublic65 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.preparePublic mlDsa65) (preparePublicKeyContract mlDsa65 abi 80) 0 :=
  preparePublic (.inr (.inl rfl))

theorem preparePublic87 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.preparePublic mlDsa87) (preparePublicKeyContract mlDsa87 abi 80) 0 :=
  preparePublic (.inr (.inr rfl))

theorem prepareSecret {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.prepareSecret p) (prepareSecretKeyContract p abi 80) 0 :=
  verifiedScrubbed (api := prepareSecretKeyApi p "" "")
    { code := Impl.MlDsa.AArch64.PreparedKey.prepareSecret p,
      verified := Proof.MlDsa.AArch64.PreparedKey.prepareSecret_verified p hp }
    _ (Scrub.prepareSecretOk hp 80) (Scrub.prepareSecretSide hp)

theorem prepareSecret44 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.prepareSecret mlDsa44) (prepareSecretKeyContract mlDsa44 abi 80) 0 :=
  prepareSecret (.inl rfl)

theorem prepareSecret65 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.prepareSecret mlDsa65) (prepareSecretKeyContract mlDsa65 abi 80) 0 :=
  prepareSecret (.inr (.inl rfl))

theorem prepareSecret87 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.prepareSecret mlDsa87) (prepareSecretKeyContract mlDsa87 abi 80) 0 :=
  prepareSecret (.inr (.inr rfl))

theorem pkTr44 (v : Proof.Sha3.AArch64.Permutation) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.pkTr v.callee mlDsa44) (pkTrContract mlDsa44 abi 16) 0 :=
  verifiedScrubbed (api := pkTr44Api)
    { code := Impl.MlDsa.AArch64.PkTr.pkTrWith v.callee mlDsa44,
      verified := Proof.MlDsa.AArch64.PkTr.pkTr_verified v _ (.inl rfl) }
    _ (Scrub.pkTrOk _ 16) (Scrub.pkTr_side v _)

theorem pkTr65 (v : Proof.Sha3.AArch64.Permutation) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.pkTr v.callee mlDsa65) (pkTrContract mlDsa65 abi 16) 0 :=
  verifiedScrubbed (api := pkTr65Api)
    { code := Impl.MlDsa.AArch64.PkTr.pkTrWith v.callee mlDsa65,
      verified := Proof.MlDsa.AArch64.PkTr.pkTr_verified v _ (.inr (.inl rfl)) }
    _ (Scrub.pkTrOk _ 16) (Scrub.pkTr_side v _)

theorem pkTr87 (v : Proof.Sha3.AArch64.Permutation) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.pkTr v.callee mlDsa87) (pkTrContract mlDsa87 abi 16) 0 :=
  verifiedScrubbed (api := pkTr87Api)
    { code := Impl.MlDsa.AArch64.PkTr.pkTrWith v.callee mlDsa87,
      verified := Proof.MlDsa.AArch64.PkTr.pkTr_verified v _ (.inr (.inr rfl)) }
    _ (Scrub.pkTrOk _ 16) (Scrub.pkTr_side v _)

/-! ### Key generation, signing and verification, with any implementation of the permutation

Each function's code is the code built with the permutation's body empty and
a hole in the place of its backend's absorb loop, with those holes filled
(`Code.fill2`): an equation the kernel checks with the implementation a
variable. What the cleanup needs of the code, that no instruction writes
PSTATE.DIT and nothing is called indirectly, and the depth of its frames,
are evaluated of that closed code, once for each parameter set and each kind
of paired sampler (`Callee.pairedSha3`), and hold for every implementation
(`side_depth_of_fill2`). -/

private theorem keyGen_sd (c : Impl.Sha3.AArch64.Callee)
    (hb : sideAll (fun i => !i.writesDit) c.code = true) (hbd : c.code.aarch64Depth = 0)
    (ho : sideAll (fun i => !i.writesDit) (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hod : (Impl.Sha3.AArch64.Stream.absorbWith c).aarch64Depth ≤ 1) {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    sideAll (fun i => !i.writesDit) (Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith c p) = true ∧
      (Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith c p).aarch64Depth ≤ 1 := by
  rcases c with ⟨n, code, sfx, cl, ps, ao⟩
  rcases hp with rfl | rfl | rfl
  · cases ps
    · exact side_depth_of_fill2 (a := .call n code) (da := 0)
        (e := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ mlDsa44)
        (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · exact side_depth_of_fill2 (a := .call n code) (da := 0)
        (e := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ mlDsa44)
        (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · exact side_depth_of_fill2 (a := .call n code) (da := 0)
        (e := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ mlDsa65)
        (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · exact side_depth_of_fill2 (a := .call n code) (da := 0)
        (e := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ mlDsa65)
        (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · exact side_depth_of_fill2 (a := .call n code) (da := 0)
        (e := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ mlDsa87)
        (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · exact side_depth_of_fill2 (a := .call n code) (da := 0)
        (e := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ mlDsa87)
        (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

private theorem sign_sd (c : Impl.Sha3.AArch64.Callee)
    (hb : sideAll (fun i => !i.writesDit) c.code = true) (hbd : c.code.aarch64Depth = 0)
    (ho : sideAll (fun i => !i.writesDit) (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hod : (Impl.Sha3.AArch64.Stream.absorbWith c).aarch64Depth ≤ 1) {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (name : String) (prepared : Bool) :
    sideAll (fun i => !i.writesDit) (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
        (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache c
          (Impl.MlDsa.AArch64.Fn.signPrims c) p) p prepared) = true ∧
      (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
        (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache c
          (Impl.MlDsa.AArch64.Fn.signPrims c) p) p prepared).aarch64Depth ≤ 4 := by
  rcases c with ⟨n, code, sfx, cl, ps, ao⟩
  rcases hp with rfl | rfl | rfl
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

private theorem verify_sd (c : Impl.Sha3.AArch64.Callee)
    (hb : sideAll (fun i => !i.writesDit) c.code = true) (hbd : c.code.aarch64Depth = 0)
    (ho : sideAll (fun i => !i.writesDit) (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hod : (Impl.Sha3.AArch64.Stream.absorbWith c).aarch64Depth ≤ 1) {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (name : String) (prepared : Bool) :
    sideAll (fun i => !i.writesDit) (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
        (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache c
          (Impl.MlDsa.AArch64.KeyGen.primsWith c) p) p prepared) = true ∧
      (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
        (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache c
          (Impl.MlDsa.AArch64.KeyGen.primsWith c) p) p prepared).aarch64Depth ≤ 4 := by
  rcases c with ⟨n, code, sfx, cl, ps, ao⟩
  rcases hp with rfl | rfl | rfl
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
            (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
              (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

private theorem signMessage_sd (c : Impl.Sha3.AArch64.Callee)
    (hb : sideAll (fun i => !i.writesDit) c.code = true) (hbd : c.code.aarch64Depth = 0)
    (ho : sideAll (fun i => !i.writesDit) (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hod : (Impl.Sha3.AArch64.Stream.absorbWith c).aarch64Depth ≤ 1) {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (name name' : String) (prepared : Bool) :
    sideAll (fun i => !i.writesDit) (Impl.MlDsa.AArch64.Message.signMessage c name'
        (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
          (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache c
            (Impl.MlDsa.AArch64.Fn.signPrims c) p) p prepared)) p) = true ∧
      (Impl.MlDsa.AArch64.Message.signMessage c name'
        (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
          (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache c
            (Impl.MlDsa.AArch64.Fn.signPrims c) p) p prepared)) p).aarch64Depth ≤ 4 := by
  rcases c with ⟨n, code, sfx, cl, ps, ao⟩
  rcases hp with rfl | rfl | rfl
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Message.signMessage ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Sign.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.Fn.signPrims ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

private theorem verifyMessage_sd (c : Impl.Sha3.AArch64.Callee)
    (hb : sideAll (fun i => !i.writesDit) c.code = true) (hbd : c.code.aarch64Depth = 0)
    (ho : sideAll (fun i => !i.writesDit) (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hod : (Impl.Sha3.AArch64.Stream.absorbWith c).aarch64Depth ≤ 1) {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (name name' : String) (prepared : Bool) :
    sideAll (fun i => !i.writesDit) (Impl.MlDsa.AArch64.Optimized.verifyMessageCached c name'
        (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
          (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache c
            (Impl.MlDsa.AArch64.KeyGen.primsWith c) p) p prepared)) p) = true ∧
      (Impl.MlDsa.AArch64.Optimized.verifyMessageCached c name'
        (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
          (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache c
            (Impl.MlDsa.AArch64.KeyGen.primsWith c) p) p prepared)) p).aarch64Depth ≤ 4 := by
  rcases c with ⟨n, code, sfx, cl, ps, ao⟩
  rcases hp with rfl | rfl | rfl
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 false)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa44) mlDsa44 true)) mlDsa44)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 false)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa65) mlDsa65 true)) mlDsa65)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  · cases ps
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, false, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
    · cases prepared
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 false)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
      · exact side_depth_of_fill2 (a := .call n code) (da := 0)
          (e := Impl.MlDsa.AArch64.Optimized.verifyMessageCached ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩ name'
            (VG.Impl.Residue.AArch64.scrubAll 64 32 VG.Impl.Residue.AArch64.Clear.all (Impl.MlDsa.AArch64.PreparedKey.Verify.entry name
              (Impl.MlDsa.AArch64.PreparedKey.Verify.withCache ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩
                (Impl.MlDsa.AArch64.KeyGen.primsWith ⟨"", .block [], sfx, cl, true, some (.call "" (.seq (.block []) (.block [])))⟩) mlDsa87) mlDsa87 true)) mlDsa87)
          (by kernel_rfl) hb (Nat.le_of_eq hbd) ho hod (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

section
variable (v : Proof.Sha3.AArch64.Permutation)

private theorem perm_side : sideAll (fun i => !i.writesDit) v.callee.code = true :=
  sideAll_noDit_of_calleeSide v.scrub

private theorem absorb_side : sideAll (fun i => !i.writesDit) (Impl.Sha3.AArch64.Stream.absorbWith v.callee) = true :=
  sideAll_noDit_of_calleeSide
    (Proof.Sha3.AArch64.Scrub.absorbWith_side v (own := Impl.Sha3.AArch64.Fn.updateOwn) (by decide))

/-- `vg_mldsa<n>_keygen` over `v`, as emitted. -/
theorem keyGen {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.keyGen v.callee p)
      (keyGenContract p (abi.withConsts Proof.MlDsa.AArch64.Sign.signRootConsts) 16) 32 := by
  obtain ⟨hs, hd⟩ := keyGen_sd v.callee (perm_side v) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames)
    (absorb_side v) (Nat.le_of_eq v.absorb_depth) hp
  exact verifiedScrubbedAll (Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v hp)
    (Scrub.keyGenOk_consts _ 16 _ _) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)

theorem keyGen44 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.keyGen v.callee mlDsa44)
      (keyGenContract mlDsa44 (abi.withConsts Proof.MlDsa.AArch64.Sign.signRootConsts) 16) 32 :=
  keyGen v (.inl rfl)

theorem keyGen65 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.keyGen v.callee mlDsa65)
      (keyGenContract mlDsa65 (abi.withConsts Proof.MlDsa.AArch64.Sign.signRootConsts) 16) 32 :=
  keyGen v (.inr (.inl rfl))

theorem keyGen87 :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.keyGen v.callee mlDsa87)
      (keyGenContract mlDsa87 (abi.withConsts Proof.MlDsa.AArch64.Sign.signRootConsts) 16) 32 :=
  keyGen v (.inr (.inr rfl))

open VG.Proof.MlDsa.AArch64.PreparedKey (rawSignK rawVerifyK messageSignK messageVerifyK)

/-- `vg_<module>_sign` (or `_sign_prepared`) over `v`, as emitted. -/
theorem sign {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (module : String)
    (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.sign v.callee p module prepared)
      (rawSignK p prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 := by
  obtain ⟨hs, hd⟩ := sign_sd v.callee (perm_side v) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames)
    (absorb_side v) (Nat.le_of_eq v.absorb_depth) hp
    (s!"vg_{module}_sign_with_cache" ++ v.callee.suffix) prepared
  cases prepared
  · exact verifiedScrubbedAll (Proof.MlDsa.AArch64.PreparedKey.sign_entry_verified v hp _ false)
      (Scrub.signPairedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)
  · exact verifiedScrubbedAll (Proof.MlDsa.AArch64.PreparedKey.sign_entry_verified v hp _ true)
      (Scrub.preparedSignPairedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)

/-- `vg_<module>_verify` (or `_verify_prepared`) over `v`, as emitted. -/
theorem verify {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (module : String)
    (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verify v.callee p module prepared)
      (rawVerifyK p prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 := by
  obtain ⟨hs, hd⟩ := verify_sd v.callee (perm_side v) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames)
    (absorb_side v) (Nat.le_of_eq v.absorb_depth) hp
    (s!"vg_{module}_verify_with_cache" ++ v.callee.suffix) prepared
  cases prepared
  · exact verifiedScrubbedAll (Proof.MlDsa.AArch64.PreparedKey.verify_entry_verified v hp _ false)
      (Scrub.verifySelectedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)
  · exact verifiedScrubbedAll (Proof.MlDsa.AArch64.PreparedKey.verify_entry_verified v hp _ true)
      (Scrub.preparedVerifySelectedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)

/-- `vg_<module>_sign_message` (or `_sign_message_prepared`) over `v`, as
emitted: it calls `sign` as emitted. -/
theorem signMessage {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (module : String)
    (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.signMessage v.callee p module prepared)
      (messageSignK p prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 := by
  cases prepared
  · obtain ⟨hs, hd⟩ := signMessage_sd v.callee (perm_side v)
      (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (absorb_side v) (Nat.le_of_eq v.absorb_depth) hp
      (s!"vg_{module}_sign_with_cache" ++ v.callee.suffix) (s!"vg_{module}_sign" ++ v.callee.suffix) false
    exact verifiedScrubbedAll
      (Proof.MlDsa.AArch64.PreparedKey.message_sign_verified v hp (Scrub.message_sign_fn_scrub p v hp _ false))
      (Scrub.signMessagePairedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)
  · obtain ⟨hs, hd⟩ := signMessage_sd v.callee (perm_side v)
      (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (absorb_side v) (Nat.le_of_eq v.absorb_depth) hp
      (s!"vg_{module}_sign_with_cache" ++ v.callee.suffix) (s!"vg_{module}_sign_prepared" ++ v.callee.suffix)
      true
    exact verifiedScrubbedAll
      (Proof.MlDsa.AArch64.PreparedKey.message_sign_verified v hp (Scrub.message_sign_fn_scrub p v hp _ true))
      (Scrub.preparedSignMessagePairedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)

/-- `vg_<module>_verify_message_cached` (or `_verify_message_prepared`) over
`v`, as emitted: it calls `verify` as emitted. -/
theorem verifyMessage {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (module : String)
    (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verifyMessage v.callee p module prepared)
      (messageVerifyK p prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 := by
  cases prepared
  · obtain ⟨hs, hd⟩ := verifyMessage_sd v.callee (perm_side v)
      (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (absorb_side v) (Nat.le_of_eq v.absorb_depth) hp
      (s!"vg_{module}_verify_with_cache" ++ v.callee.suffix) (s!"vg_{module}_verify" ++ v.callee.suffix) false
    exact verifiedScrubbedAll
      (Proof.MlDsa.AArch64.PreparedKey.message_verify_verified v hp
        (Scrub.message_verify_fn_scrub p v hp _ false))
      (Scrub.verifyMessageCachedSelectedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)
  · obtain ⟨hs, hd⟩ := verifyMessage_sd v.callee (perm_side v)
      (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (absorb_side v) (Nat.le_of_eq v.absorb_depth) hp
      (s!"vg_{module}_verify_with_cache" ++ v.callee.suffix)
      (s!"vg_{module}_verify_prepared" ++ v.callee.suffix) true
    exact verifiedScrubbedAll
      (Proof.MlDsa.AArch64.PreparedKey.message_verify_verified v hp
        (Scrub.message_verify_fn_scrub p v hp _ true))
      (Scrub.preparedVerifyMessageSelectedOk p) (by decide) (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (by decide)

theorem sign44 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa44 "mldsa44" prepared)
      (rawSignK mlDsa44 prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 :=
  sign v (.inl rfl) "mldsa44" prepared

theorem sign65 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa65 "mldsa65" prepared)
      (rawSignK mlDsa65 prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 :=
  sign v (.inr (.inl rfl)) "mldsa65" prepared

theorem sign87 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.sign v.callee mlDsa87 "mldsa87" prepared)
      (rawSignK mlDsa87 prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 :=
  sign v (.inr (.inr rfl)) "mldsa87" prepared

theorem verify44 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa44 "mldsa44" prepared)
      (rawVerifyK mlDsa44 prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 :=
  verify v (.inl rfl) "mldsa44" prepared

theorem verify65 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa65 "mldsa65" prepared)
      (rawVerifyK mlDsa65 prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 :=
  verify v (.inr (.inl rfl)) "mldsa65" prepared

theorem verify87 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verify v.callee mlDsa87 "mldsa87" prepared)
      (rawVerifyK mlDsa87 prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 :=
  verify v (.inr (.inr rfl)) "mldsa87" prepared

theorem signMessage44 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa44 "mldsa44" prepared)
      (messageSignK mlDsa44 prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 :=
  signMessage v (.inl rfl) "mldsa44" prepared

theorem signMessage65 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa65 "mldsa65" prepared)
      (messageSignK mlDsa65 prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 :=
  signMessage v (.inr (.inl rfl)) "mldsa65" prepared

theorem signMessage87 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.signMessage v.callee mlDsa87 "mldsa87" prepared)
      (messageSignK mlDsa87 prepared (abi.withConsts Proof.MlDsa.AArch64.Sign.pairedSignRootConsts)) 32 :=
  signMessage v (.inr (.inr rfl)) "mldsa87" prepared

theorem verifyMessage44 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa44 "mldsa44" prepared)
      (messageVerifyK mlDsa44 prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 :=
  verifyMessage v (.inl rfl) "mldsa44" prepared

theorem verifyMessage65 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa65 "mldsa65" prepared)
      (messageVerifyK mlDsa65 prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 :=
  verifyMessage v (.inr (.inl rfl)) "mldsa65" prepared

theorem verifyMessage87 (prepared : Bool) :
    VerifiedScrubbed target (Impl.MlDsa.AArch64.Fn.verifyMessage v.callee mlDsa87 "mldsa87" prepared)
      (messageVerifyK mlDsa87 prepared Proof.MlDsa.AArch64.Verify.OptimizedSelected.selectedAbi) 32 :=
  verifyMessage v (.inr (.inr rfl)) "mldsa87" prepared

end

end VG.Proof.MlDsa.AArch64.Fn
