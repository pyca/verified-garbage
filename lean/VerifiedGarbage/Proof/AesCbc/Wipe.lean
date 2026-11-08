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

/-! ## Wiping only what an implementation writes -/

/-- `P`, and the bytes of `scratch` from `w` on unchanged. -/
def tailPost (pb : Nat) (w : Nat) (P : aesSig.Post pb) : aesSig.Post pb :=
  fun schedule rounds iv data n scratch m m' x =>
    P schedule rounds iv data n scratch m m' x ∧
      ∀ i, w ≤ i → i < 2176 → m' (scratch + BitVec.ofNat 64 i) = m (scratch + BitVec.ofNat 64 i)

/-- With nothing of `scratch` written from `w` on, `tailPost`. -/
theorem tail_of_written (pb : Nat) (w : Nat) (P : aesSig.Post pb) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) P vs m m' x →
    (∀ b ∈ Sig.arrays aesSig.params vs, b.1 = "scratch" →
      ∀ i, w ≤ i → i < b.2.len → m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply (aesSig.words pb) (tailPost pb w P) vs m m' x := by
  intro vs m m' x hlen h hw
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  exact ⟨h, fun i hi hl => hw ("scratch", ⟨f, 2176⟩) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))) rfl i hi hl⟩

/-- A proof of a CBC function's contract, and that it writes nothing in
`scratch` from `w` on (its `written` bound), is one of `tailPost`'s, on a
calling convention that gives each run the six arguments (`hlen`). -/
theorem Verified.cbc_tail_of_written {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    {P : aesSig.Post A.ptrBits} {w : Nat}
    (h : Verified T c (aesSig.contract A (pre A.ptrBits) P false stack none))
    (hw : ∀ s t s', (aesSig.contract A (pre A.ptrBits) P false stack none).pre s →
      Exec T.isa c s t s' → Sig.writtenWithin A aesSig [("scratch", w)] s s')
    (hlen : ∀ s vals, A.args ((aesSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      (vals s).length = (aesSig.words A.ptrBits).length) :
    Verified T c (aesSig.contract A (pre A.ptrBits) (tailPost A.ptrBits w P) false stack none) := by
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
    exact tail_of_written _ w P _ _ _ _ (hlen s vals hv) hq fun b hb hn i hi hl =>
      hW _ (List.mem_singleton_self _) b hb hn i hi hl

/-- Every byte of `scratch` past the whole of it is unchanged: `tailPost`
of 2176, of any proof. -/
theorem Verified.cbc_tail_full {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    {P : aesSig.Post A.ptrBits}
    (h : Verified T c (aesSig.contract A (pre A.ptrBits) P false stack none)) :
    Verified T c (aesSig.contract A (pre A.ptrBits) (tailPost A.ptrBits 2176 P) false stack none) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ h => ⟨h, fun _ hi hl => absurd hl (Nat.not_lt.mpr hi)⟩

/-- `tailPost` reads the memory on entry only within the buffers, if `P`
does. -/
theorem tailPost_local (pb : Nat) (w : Nat) (P : aesSig.Post pb)
    (hP : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
      (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) P vs m₁ m' x → Curry.apply (aesSig.words pb) P vs m₂ m' x) :
    ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
      (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) (tailPost pb w P) vs m₁ m' x →
        Curry.apply (aesSig.words pb) (tailPost pb w P) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  have hP' := hP vs m₁ m₂ m' x hlen hb
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  have hs := agree_of hb.2.2.2
  exact ⟨hP' h.1, fun i hi hl => by rw [h.2 i hi hl]; exact (hs i hl).symm⟩

/-- `tailPost` reads the memory on return only within the buffers apart
from the first `w` bytes of `scratch`, if `P` reads it only within those
apart from `scratch` (the form `Verified.callWipeTail'` takes). -/
theorem tailPost_out (pb : Nat) (w : Nat) (P : aesSig.Post pb)
    (hP : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
      (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) P vs m m₁ x → Curry.apply (aesSig.words pb) P vs m m₂ x)
    (hw : w ≤ 2176) :
    ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
      (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 →
        ¬(⟨vs.getD 5 0, w⟩ : Region).Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) (tailPost pb w P) vs m m₁ x →
        Curry.apply (aesSig.words pb) (tailPost pb w P) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hag h
  have hP' := hP vs m m₁ m₂ x hlen hpw fun b hb hbA a ha =>
    hag b hb a ha fun hp => hbA a ha (Region.sub_prefix (by simp only [Elem.size]; omega) a hp)
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  have hs := hag _ (by rw [bufs_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  refine ⟨hP' h.1, fun i hi hl => ?_⟩
  have hi64 : i < 2 ^ 64 := by omega
  rw [← h.2 i hi hl]
  refine (hs _ (Offset.contains_base _ (by omega) hi64) fun hc => ?_).symm
  simp only [Region.Contains, List.getD_cons_succ, List.getD_cons_zero] at hc
  rw [Mem.sub_ofNat_toNat f hi64] at hc
  omega

/-- With `scratch` unchanged from `w` on and zero before, `scrubbedPost`. -/
theorem wipedTail (pb : Nat) (w : Nat) (P : aesSig.Post pb) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) (tailPost pb w P) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) w = Spec.Zeroize.zeros w →
      Curry.apply (aesSig.words pb) (scrubbedPost pb P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  obtain ⟨h1, h2⟩ := h
  replace h2 : ∀ i, w ≤ i → i < 2176 → m' (f + BitVec.ofNat 64 i) = m (f + BitVec.ofNat 64 i) := h2
  replace hz : Spec.Zeroize.bytesAt m' f w = Spec.Zeroize.zeros w := hz
  refine ⟨h1, fun y hy => ?_⟩
  replace hy : (⟨f, 2176⟩ : Region).Contains y 1 := hy
  have hi : (y - f).toNat < 2176 := by simp only [Region.Contains] at hy; omega
  have hy' : f + BitVec.ofNat 64 (y - f).toNat = y := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  by_cases hl : (y - f).toNat < w
  · right
    have he := congrArg (·[(y - f).toNat]?) hz
    simp only [Spec.Zeroize.bytesAt, Spec.Zeroize.zeros, List.getElem?_map, List.getElem?_range hl,
      List.getElem?_replicate, hl, ite_true, Option.map_some, Option.some.injEq] at he
    rw [hy'] at he
    exact he
  · left
    have he := h2 _ (Nat.le_of_not_lt hl) hi
    rw [hy'] at he
    exact he

end VG.Proof.AesCbc.Wipe
