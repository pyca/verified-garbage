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

end VG.Proof.MlDsa.AArch64.Scrub
