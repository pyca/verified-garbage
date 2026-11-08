module

public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Framework.PostMono
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

-- separate module: every target's CBC proofs share it

/-!
# AES-CBC leaving `scratch` scrubbed, on every target

An implementation of `vg_aes_cbc_encrypt` or `vg_aes_cbc_decrypt` meets its
contract with `scratch` left scrubbed (`scrubbedPost`: each byte unchanged
or zero, `Spec.Zeroize.scrubbed`) where it writes nothing in `scratch`
(`Verified.cbc_of_unwritten`), and otherwise as a call of it followed by the
zeroize function on the whole of `scratch`, which the target's `callWipe`
proves zero on return (`wiped`). Until the contracts in `Spec/Cbc/` state
it, such a proof is registered weakened to them (`Verified.of_scrubbed`).

`callWipe` needs the CBC functions' postconditions to read the memory on
entry only within the buffers (`encPost_local`, `decPost_local`) and the
memory on return only within the buffers apart from `scratch`
(`encPost_out`, `decPost_out`): the key schedule, the chaining value and the
data. The locality of the memory's pieces is ECB's (`Proof/AesEcb/Wipe.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.Wipe

open VG VG.Spec.Cbc VG.Proof.AesEcb

theorem blocksAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt]
  refine List.map_congr_left fun j hj => bytesAt_congr fun i hi => ?_
  have hj := List.mem_range.mp hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

/-! ## The contracts -/

/-- The precondition of every CBC function. -/
def pre (pb : Nat) : Curry (aesSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _scratch _ => rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- `aesEncryptContract`'s postcondition. -/
def encPost (pb : Nat) : aesSig.Post pb := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Spec.Aes.KeySchedule m schedule rounds.toNat key →
    let ciph := aes key
    let cs := encrypt ciph (Spec.Aes.bytesAt m iv 16) (blocksAt m data n.toNat)
    blocksAt m' data n.toNat = cs ∧ Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) cs

/-- `aesDecryptContract`'s postcondition. -/
def decPost (pb : Nat) : aesSig.Post pb := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Spec.Aes.KeySchedule m schedule rounds.toNat key →
    let ciphInv := aesInv key
    let cs := blocksAt m data n.toNat
    blocksAt m' data n.toNat = decrypt ciphInv (Spec.Aes.bytesAt m iv 16) cs ∧
      Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) cs

/-- `P`, and nothing written left in `scratch`. -/
def scrubbedPost (pb : Nat) (P : aesSig.Post pb) : aesSig.Post pb :=
  fun schedule rounds iv data n scratch m m' x =>
    P schedule rounds iv data n scratch m m' x ∧ Spec.Zeroize.scrubbed m m' scratch 2176

theorem encrypt_eq {M : ISA} (A : Abi M) (stack : Nat) :
    aesEncryptContract A stack = aesSig.contract A (pre A.ptrBits) (encPost A.ptrBits) false stack none :=
  rfl

theorem decrypt_eq {M : ISA} (A : Abi M) (stack : Nat) :
    aesDecryptContract A stack = aesSig.contract A (pre A.ptrBits) (decPost A.ptrBits) false stack none :=
  rfl

/-- The arguments, six words. -/
theorem vs_eq {pb : Nat} {vs : List (BitVec 64)} (h : vs.length = (aesSig.words pb).length) :
    ∃ a b c d e f, vs = [a, b, c, d, e, f] := by
  obtain ⟨a, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) h
  replace h := Nat.succ.inj h
  obtain ⟨b, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain ⟨e, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain ⟨f, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain rfl := List.eq_nil_of_length_eq_zero h
  exact ⟨a, b, c, d, e, f, rfl⟩

theorem bufs_eq {a b c d e f : BitVec 64} :
    Sig.bufs aesSig.params [a, b, c, d, e, f] =
      [(⟨a, 240⟩, false), (⟨c, 16⟩, true), (⟨d, e.toNat * 16⟩, true), (⟨f, 2176⟩, true)] :=
  rfl

/-! ## Locality of the contracts -/

/-- The precondition reads no memory. -/
theorem pre_local (pb : Nat) : ∀ vs (m₁ m₂ : Mem), vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (pre pb) vs m₁ → Curry.apply (aesSig.words pb) (pre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, _, _, _, _, _, rfl⟩ := vs_eq hlen
  exact h

theorem encPost_local (pb : Nat) : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (encPost pb) vs m₁ m' x →
      Curry.apply (aesSig.words pb) (encPost pb) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  intro key hk
  show blocksAt m' d (e.setWidth pb).toNat =
      encrypt (aes key) (Spec.Aes.bytesAt m₂ c 16) (blocksAt m₂ d (e.setWidth pb).toNat) ∧
    Spec.Aes.bytesAt m' c 16 = next (Spec.Aes.bytesAt m₂ c 16)
      (encrypt (aes key) (Spec.Aes.bytesAt m₂ c 16) (blocksAt m₂ d (e.setWidth pb).toNat))
  have hd := agree_of hb.2.2.1
  rw [bytesAt_congr (agree_of hb.2.1),
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega)]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

theorem decPost_local (pb : Nat) : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (decPost pb) vs m₁ m' x →
      Curry.apply (aesSig.words pb) (decPost pb) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  intro key hk
  show blocksAt m' d (e.setWidth pb).toNat =
      decrypt (aesInv key) (Spec.Aes.bytesAt m₂ c 16) (blocksAt m₂ d (e.setWidth pb).toNat) ∧
    Spec.Aes.bytesAt m' c 16 = next (Spec.Aes.bytesAt m₂ c 16) (blocksAt m₂ d (e.setWidth pb).toNat)
  have hd := agree_of hb.2.2.1
  rw [bytesAt_congr (agree_of hb.2.1),
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega)]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

theorem encPost_out (pb : Nat) : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (encPost pb) vs m m₁ x →
      Curry.apply (aesSig.words pb) (encPost pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Bool.or_true, Bool.true_or, forall_const, List.Pairwise.nil, and_true] at hpw
  intro key hk
  show blocksAt m₂ d (e.setWidth pb).toNat =
      encrypt (aes key) (Spec.Aes.bytesAt m c 16) (blocksAt m d (e.setWidth pb).toNat) ∧
    Spec.Aes.bytesAt m₂ c 16 = next (Spec.Aes.bytesAt m c 16)
      (encrypt (aes key) (Spec.Aes.bytesAt m c 16) (blocksAt m d (e.setWidth pb).toNat))
  have hd := agree_of (hb.2.2.1 hpw.2.2.1)
  rw [bytesAt_congr (agree_of (hb.2.1 hpw.2.1.2)),
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega)]
  exact h key hk

theorem decPost_out (pb : Nat) : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (decPost pb) vs m m₁ x →
      Curry.apply (aesSig.words pb) (decPost pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Bool.or_true, Bool.true_or, forall_const, List.Pairwise.nil, and_true] at hpw
  intro key hk
  show blocksAt m₂ d (e.setWidth pb).toNat =
      decrypt (aesInv key) (Spec.Aes.bytesAt m c 16) (blocksAt m d (e.setWidth pb).toNat) ∧
    Spec.Aes.bytesAt m₂ c 16 = next (Spec.Aes.bytesAt m c 16) (blocksAt m d (e.setWidth pb).toNat)
  have hd := agree_of (hb.2.2.1 hpw.2.2.1)
  rw [bytesAt_congr (agree_of (hb.2.1 hpw.2.1.2)),
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega)]
  exact h key hk

/-- With the whole of `scratch` zero on return, `scrubbedPost`. -/
theorem wiped (pb : Nat) (P : aesSig.Post pb) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) 2176 = Spec.Zeroize.zeros 2176 →
      Curry.apply (aesSig.words pb) (scrubbedPost pb P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  exact ⟨h, scrubbed_of_zeros hz⟩

/-- With nothing of `scratch` written, `scrubbedPost`. -/
theorem unwritten (pb : Nat) (P : aesSig.Post pb) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) P vs m m' x →
    (∀ b ∈ Sig.arrays aesSig.params vs, b.1 = "scratch" →
      ∀ i, 0 ≤ i → i < b.2.len → m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply (aesSig.words pb) (scrubbedPost pb P) vs m m' x := by
  intro vs m m' x hlen h hw
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  refine ⟨h, scrubbed_of_unchanged fun i hi => ?_⟩
  exact hw ("scratch", ⟨f, 2176⟩) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))) rfl i (Nat.zero_le _) hi

/-- A proof of a CBC function's contract is one of `scrubbedPost`'s for code
that writes nothing in `scratch`, on a calling convention that gives each
run the six arguments (`hlen`). -/
theorem Verified.cbc_of_unwritten {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    {P : aesSig.Post A.ptrBits}
    (h : Verified T c (aesSig.contract A (pre A.ptrBits) P false stack none))
    (hw : ∀ s t s', (aesSig.contract A (pre A.ptrBits) P false stack none).pre s →
      Exec T.isa c s t s' → Sig.writtenWithin A aesSig [("scratch", 0)] s s')
    (hlen : ∀ s vals, A.args ((aesSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      (vals s).length = (aesSig.words A.ptrBits).length) :
    Verified T c (aesSig.contract A (pre A.ptrBits) (scrubbedPost A.ptrBits P) false stack none) := by
  obtain ⟨hc, hct, hsat⟩ := h
  refine ⟨fun s hs => ?_, hct, hsat⟩
  obtain ⟨t, s', he, ha, hq⟩ := hc s hs
  have hW := hw s t s' hs he
  refine ⟨t, s', he, ha, ?_⟩
  revert hs hq hW
  simp only [Sig.contract, Sig.writtenWithin]
  split
  · intro hs; exact hs.elim
  · rename_i vals hv
    intro _ hq
    split
    · rename_i hv'
      exact absurd (hv.symm.trans hv') (Option.some_ne_none _)
    rename_i vals' hv'
    obtain rfl := Option.some.inj (hv.symm.trans hv')
    intro hW
    exact unwritten _ P _ _ _ _ (hlen s vals hv) hq fun b hb hn i hi hl =>
      hW _ (List.mem_singleton_self _) b hb hn i hi hl

/-- `scrubbedPost P` implies `P`. -/
theorem scrubbedPost_imp (pb : Nat) (P : aesSig.Post pb) : aesSig.PostImp pb (scrubbedPost pb P) P :=
  fun _ _ _ _ _ _ _ _ _ h => h.1

/-- A proof that leaves `scratch` scrubbed is one of the contract without it. -/
theorem Verified.of_scrubbed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    {P : aesSig.Post A.ptrBits}
    (h : Verified T c (aesSig.contract A (pre A.ptrBits) (scrubbedPost A.ptrBits P) false stack none)) :
    Verified T c (aesSig.contract A (pre A.ptrBits) P false stack none) :=
  h.post_mono (scrubbedPost_imp _ P)


/-! ## Zeroing the part of `scratch` left written -/

/-- A buffer whose first `w` bytes are zero and whose others are unchanged
or zero holds nothing written. -/
theorem scrubbed_of_prefix' {m m' : Mem} {p : Addr} {w len : Nat}
    (hz : Spec.Zeroize.bytesAt m' p w = Spec.Zeroize.zeros w)
    (ht : ∀ i, w ≤ i → i < len →
      m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) ∨ m' (p + BitVec.ofNat 64 i) = 0) :
    Spec.Zeroize.scrubbed m m' p len := by
  intro a ha
  have hi : (a - p).toNat < len := by simp only [Region.Contains] at ha; omega
  have ea : p + BitVec.ofNat 64 (a - p).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  by_cases hw : (a - p).toNat < w
  · right
    have he := congrArg (·[(a - p).toNat]?) hz
    simp only [Spec.Zeroize.bytesAt, Spec.Zeroize.zeros, List.getElem?_map, List.getElem?_range hw,
      List.getElem?_replicate, hw, ite_true, Option.map_some, Option.some.injEq] at he
    rwa [ea] at he
  · have he := ht _ (Nat.le_of_not_lt hw) hi
    rwa [ea] at he

/-- `P`, with each byte of `scratch` at offset `w` and beyond unchanged or
zero. -/
def tailPost (pb : Nat) (P : aesSig.Post pb) (w : Nat) : aesSig.Post pb :=
  fun schedule rounds iv data n scratch m m' x =>
    P schedule rounds iv data n scratch m m' x ∧ ∀ i, w ≤ i → i < 2176 →
      m' (scratch + BitVec.ofNat 64 i) = m (scratch + BitVec.ofNat 64 i) ∨ m' (scratch + BitVec.ofNat 64 i) = 0

/-- `tailPost` reads the memory on entry only within the buffers, if `P` does. -/
theorem tailPost_local (pb : Nat) {P : aesSig.Post pb} (w : Nat)
    (hP : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
      (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) P vs m₁ m' x → Curry.apply (aesSig.words pb) P vs m₂ m' x) :
    ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (tailPost pb P w) vs m₁ m' x →
      Curry.apply (aesSig.words pb) (tailPost pb P w) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  obtain ⟨hp, ht⟩ := h
  refine ⟨hP [a, b, c, d, e, f] m₁ m₂ m' x hlen hb hp, fun i h1 h2 => ?_⟩
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  have e₂ := (agree_of hb.2.2.2 i (by omega)).symm
  show m' (f + BitVec.ofNat 64 i) = m₂ (f + BitVec.ofNat 64 i) ∨ m' (f + BitVec.ofNat 64 i) = 0
  rw [← e₂]
  exact ht i h1 h2

/-- `tailPost` reads the memory on return only within the buffers apart from
the first `w` bytes of `scratch`, if `P` reads it only apart from `scratch`. -/
theorem tailPost_out (pb : Nat) {P : aesSig.Post pb} {w : Nat} (hw : w ≤ 2176)
    (hP : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
      (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) P vs m m₁ x → Curry.apply (aesSig.words pb) P vs m m₂ x) :
    ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 →
      ¬(⟨vs.getD 5 0, w⟩ : Region).Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (tailPost pb P w) vs m m₁ x →
      Curry.apply (aesSig.words pb) (tailPost pb P w) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  obtain ⟨hp, ht⟩ := h
  refine ⟨hP [a, b, c, d, e, f] m m₁ m₂ x hlen hpw
    (fun r hr hrd y hy => hb r hr y hy fun hc => hrd y hy (Region.sub_prefix hw y hc)) hp, fun i h1 h2 => ?_⟩
  have hc : (⟨f, 2176⟩ : Region).Contains (f + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have hn : ¬ (⟨f, w⟩ : Region).Contains (f + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, BitVec.add_comm f, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
    omega
  show m₂ (f + BitVec.ofNat 64 i) = m (f + BitVec.ofNat 64 i) ∨ m₂ (f + BitVec.ofNat 64 i) = 0
  rw [← hb (⟨f, 2176⟩, true) (by rw [bufs_eq]; simp) _ hc hn]
  exact ht i h1 h2

/-- With the first `w` bytes of `scratch` zero on return, `scrubbedPost`. -/
theorem wipedTail (pb : Nat) (P : aesSig.Post pb) (w : Nat) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) (tailPost pb P w) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) w = Spec.Zeroize.zeros w →
      Curry.apply (aesSig.words pb) (scrubbedPost pb P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  exact ⟨h.1, scrubbed_of_prefix' hz h.2⟩

/-- `tailPost P 0` is `scrubbedPost P`'s. -/
theorem tailPost_zero (pb : Nat) (P : aesSig.Post pb) : aesSig.PostImp pb (tailPost pb P 0) (scrubbedPost pb P) := by
  intro schedule rounds iv data n scratch m m' x h
  exact ⟨h.1, scrubbed_of_prefix' (w := 0) rfl h.2⟩

/-- A proof of a CBC function's contract is one of `tailPost w`'s for code
that leaves each byte of `scratch` at offset `w` and beyond unchanged or
zero, on a calling convention that gives each run the six arguments
(`hlen`). -/
theorem Verified.tail_of {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w : Nat}
    {P : aesSig.Post A.ptrBits}
    (h : Verified T c (aesSig.contract A (pre A.ptrBits) P false stack none))
    (hw : ∀ s t s', (aesSig.contract A (pre A.ptrBits) P false stack none).pre s → Exec T.isa c s t s' →
      ∀ vals, A.args ((aesSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      ∀ i, w ≤ i → i < 2176 →
        A.mem s' ((vals s).getD 5 0 + BitVec.ofNat 64 i) = A.mem s ((vals s).getD 5 0 + BitVec.ofNat 64 i) ∨
          A.mem s' ((vals s).getD 5 0 + BitVec.ofNat 64 i) = 0)
    (hlen : ∀ s vals, A.args ((aesSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      (vals s).length = (aesSig.words A.ptrBits).length) :
    Verified T c (aesSig.contract A (pre A.ptrBits) (tailPost A.ptrBits P w) false stack none) := by
  obtain ⟨hc, hct, hsat⟩ := h
  refine ⟨fun s hs => ?_, hct, hsat⟩
  obtain ⟨t, s', he, ha, hq⟩ := hc s hs
  have hW := hw s t s' hs he
  refine ⟨t, s', he, ha, ?_⟩
  revert hs hq hW
  simp only [Sig.contract]
  split
  · intro hs; exact hs.elim
  · rename_i vals hv
    intro _ hq hW
    have hW' := hW vals hv
    obtain ⟨a, b, c, d, e, f, he'⟩ := vs_eq (hlen s vals hv)
    rw [he'] at hq hW' ⊢
    exact ⟨hq, hW'⟩

end VG.Proof.AesCbc.Wipe
