module

public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Consts
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on AArch64, without secret residue

The postconditions of key generation, encapsulation (hashing the key, or
with `H(ek)` given) and decapsulation of ML-KEM-768 and ML-KEM-1024 read the
memory on return only within their outputs and their scratch space
(`ScrubAll.ScrubAllOk`, as x86-64's `Proof/MlKem/X86_64/CallWipe.lean` proves
them): each implementation, generic over the Keccak-f[1600] implementations
it calls, returns with every register it may leave secret cleared and its
whole stack zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

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

/-- A buffer scrubbed in one memory on return is in another that agrees on it. -/
theorem scrubbed_of {m m₁ m₂ : Mem} {p : Addr} {len : Nat}
    (hb : ∀ a, Region.Contains ⟨p, len⟩ a 1 → m₁ a = m₂ a) (h : Spec.Zeroize.scrubbed m m₁ p len) :
    Spec.Zeroize.scrubbed m m₂ p len := fun a ha => hb a ha ▸ h a ha

/-- `Outcome` of one output holds of another equal to it. -/
theorem outcome_of {α : Type} {f : Nat → Option α} {r : BitVec 32} {x y : α} (e : x = y)
    (h : Spec.MlKem.Outcome f r y) : Spec.MlKem.Outcome f r x := e ▸ h

/-- `Outcome` of a pair of outputs holds of another pair equal to it. -/
theorem outcome_of₂ {α β : Type} {f : Nat → Option (α × β)} {r : BitVec 32} {a₁ a₂ : α} {b₁ b₂ : β}
    (ea : a₁ = a₂) (eb : b₁ = b₂) (h : Spec.MlKem.Outcome f r (a₂, b₂)) :
    Spec.MlKem.Outcome f r (a₁, b₁) := ea ▸ eb ▸ h

variable (W : Nat) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))

theorem keyGenOk (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.keyGenContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem.keyGenSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem.keyGenSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seed, ek, dk, sc], _ =>
      simp only [Spec.MlKem.keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2 h2⟩
      exact outcome_of₂ (bytesAt_of (Nat.le_refl _) hb.2.1) (bytesAt_of (Nat.le_refl _) hb.2.2.1) h1

theorem keyGen1024Ok (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.keyGenContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem1024.keyGenSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem1024.keyGenSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seed, ek, dk, sc], _ =>
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2 h2⟩
      exact outcome_of₂ (bytesAt_of (Nat.le_refl _) hb.2.1) (bytesAt_of (Nat.le_refl _) hb.2.2.1) h1

theorem encapsOk (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.encapsContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem.encapsSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem.encapsSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ek, msg, key, ct, sc], _ =>
      simp only [Spec.MlKem.encapsSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2.2 h2⟩
      exact outcome_of₂ (bytesAt_of (Nat.le_refl _) hb.2.2.1) (bytesAt_of (Nat.le_refl _) hb.2.2.2.1) h1

theorem encaps1024Ok (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.encapsContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem1024.encapsSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem1024.encapsSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ek, msg, key, ct, sc], _ =>
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2.2 h2⟩
      exact outcome_of₂ (bytesAt_of (Nat.le_refl _) hb.2.2.1) (bytesAt_of (Nat.le_refl _) hb.2.2.2.1) h1

theorem encapsHOk (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.encapsHContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem.encapsHSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem.encapsHSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ek, hek, msg, key, ct, sc], _ =>
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2.2.2 h2⟩
      exact outcome_of₂ (bytesAt_of (Nat.le_refl _) hb.2.2.2.1) (bytesAt_of (Nat.le_refl _) hb.2.2.2.2.1) h1

theorem encapsH1024Ok (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.encapsHContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem1024.encapsHSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem1024.encapsHSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ek, hek, msg, key, ct, sc], _ =>
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2.2.2 h2⟩
      exact outcome_of₂ (bytesAt_of (Nat.le_refl _) hb.2.2.2.1) (bytesAt_of (Nat.le_refl _) hb.2.2.2.2.1) h1

theorem decapsOk (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.decapsContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem.decapsSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem.decapsSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [dk, ct, key, sc], _ =>
      simp only [Spec.MlKem.decapsSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2 h2⟩
      exact outcome_of (bytesAt_of (Nat.le_refl _) hb.2.2.1) h1

theorem decaps1024Ok (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.decapsContract (abi.withConsts (c₀ :: cs)) W) W
      (Spec.MlKem1024.decapsSig.retBits abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.MlKem1024.decapsSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [dk, ct, key, sc], _ =>
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, scrubbed_of hb.2.2.2 h2⟩
      exact outcome_of (bytesAt_of (Nat.le_refl _) hb.2.2.1) h1

/-! ## With the implementations' tables -/

section
open VG.Proof.MlKem.AArch64.Optimized (constants)

theorem keyGenOk_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.keyGenContract (abi.withConsts constants) W) W (Spec.MlKem.keyGenSig.retBits abi.ptrBits) :=
  keyGenOk W _ _ hW

theorem keyGen1024Ok_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.keyGenContract (abi.withConsts constants) W) W (Spec.MlKem1024.keyGenSig.retBits abi.ptrBits) :=
  keyGen1024Ok W _ _ hW

theorem encapsOk_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.encapsContract (abi.withConsts constants) W) W (Spec.MlKem.encapsSig.retBits abi.ptrBits) :=
  encapsOk W _ _ hW

theorem encaps1024Ok_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.encapsContract (abi.withConsts constants) W) W (Spec.MlKem1024.encapsSig.retBits abi.ptrBits) :=
  encaps1024Ok W _ _ hW

theorem encapsHOk_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.encapsHContract (abi.withConsts constants) W) W (Spec.MlKem.encapsHSig.retBits abi.ptrBits) :=
  encapsHOk W _ _ hW

theorem encapsH1024Ok_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.encapsHContract (abi.withConsts constants) W) W (Spec.MlKem1024.encapsHSig.retBits abi.ptrBits) :=
  encapsH1024Ok W _ _ hW

theorem decapsOk_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem.decapsContract (abi.withConsts constants) W) W (Spec.MlKem.decapsSig.retBits abi.ptrBits) :=
  decapsOk W _ _ hW

theorem decaps1024Ok_tables (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.MlKem1024.decapsContract (abi.withConsts constants) W) W (Spec.MlKem1024.decapsSig.retBits abi.ptrBits) :=
  decaps1024Ok W _ _ hW

end

end VG.Proof.MlKem.AArch64.Scrub
