module

public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Framework.PublicOut
public import VerifiedGarbage.Proof.Zeroize.Wiped
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: every target's CBC proofs share it

/-!
# AES-CBC leaving `scratch` scrubbed, on every target

An implementation of `vg_aes_cbc_encrypt` or `vg_aes_cbc_decrypt` leaves the
bytes of `scratch` at the offsets `S` zero and the others unchanged
(`wipedPost`), for an `S` that depends only on the code: none where it writes
nothing in `scratch` (`Verified.cbc_of_unwritten`), and otherwise as a call of it
followed by the zeroize function on the part of `scratch` that it writes, which
the target's `callWipe` proves zero on return (`wiped`, `wipedTail`,
`wipedTailZ`). So each target proves its functions against a contract that says
which bytes those are (`wipedContract`), which implies the specification's
(`encrypt_imp`, `decrypt_imp`: each byte of `scratch` is unchanged or zero,
`Spec.Zeroize.scrubbed`), and that which bytes are zero is public
(`scratch_public`, `Spec.Cbc.aesScratchOut`).

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
  exact h _ (by omega_using [hi, hj])

/-! ## The contracts -/

/-- `P`, and the bytes of `scratch` at the offsets `S` zero, the others unchanged. -/
def wipedPost (pb : Nat) (P : aesSig.Post pb) (S : Nat → Bool) : aesSig.Post pb :=
  fun schedule rounds iv data n scratch m m' x =>
    P schedule rounds iv data n scratch m m' x ∧ Zeroize.WipedBy S m m' scratch 2176

/-- `Spec.Cbc.aesEncryptContract`, for `P` `encPost`, and `Spec.Cbc.aesDecryptContract`, for
`P` `decPost`, for code that leaves the bytes of `scratch` at the offsets `S` zero and the
others as they were. -/
def wipedContract (P : ∀ pb, aesSig.Post pb) (S : Nat → Bool) {M : ISA} (A : Abi M) (stack : Nat := 0) :
    Contract M :=
  aesSig.contract A (pre A.ptrBits) (wipedPost A.ptrBits (P A.ptrBits) S) false stack none

/-- An `Api` with that contract: the forms that clean up a function's code take one. -/
def wipedApi (P : ∀ pb, aesSig.Post pb) (S : Nat → Bool) : Api :=
  { aesEncryptApi with contracts := some fun A stack => wipedContract P S A stack }

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
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])]
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
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])]
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
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])]
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
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])]
  exact h key hk

/-- `encPost` reads the memory on return only within the buffers. -/
theorem encPost_ret (pb : Nat) : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (encPost pb) vs m m₁ x →
      Curry.apply (aesSig.words pb) (encPost pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  intro key hk
  have hd := agree_of hb.2.2.1
  have hb' : blocksAt m₂ d (e.setWidth pb).toNat = blocksAt m₁ d (e.setWidth pb).toNat :=
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])
  exact ⟨hb'.trans (h key hk).1, (bytesAt_congr (agree_of hb.2.1)).trans (h key hk).2⟩

/-- `decPost` reads the memory on return only within the buffers. -/
theorem decPost_ret (pb : Nat) : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (decPost pb) vs m m₁ x →
      Curry.apply (aesSig.words pb) (decPost pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  intro key hk
  have hd := agree_of hb.2.2.1
  have hb' : blocksAt m₂ d (e.setWidth pb).toNat = blocksAt m₁ d (e.setWidth pb).toNat :=
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])
  exact ⟨hb'.trans (h key hk).1, (bytesAt_congr (agree_of hb.2.1)).trans (h key hk).2⟩

/-- `wipedPost` reads the memory on return only within the buffers, if `P` does. -/
theorem wipedPost_ret (pb : Nat) (P : aesSig.Post pb) (S : Nat → Bool)
    (hP : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
      (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) P vs m m₁ x → Curry.apply (aesSig.words pb) P vs m m₂ x) :
    ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
      (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) (wipedPost pb P S) vs m m₁ x →
        Curry.apply (aesSig.words pb) (wipedPost pb P S) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hb h
  have hP' := hP vs m m₁ m₂ x hlen hb
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  exact ⟨hP' h.1, h.2.congr (fun _ _ => rfl) (agree_of hb.2.2.2)⟩

/-- With the whole of `scratch` zero on return, `wipedPost` of all of it. -/
theorem wiped (pb : Nat) (P : aesSig.Post pb) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) 2176 = Spec.Zeroize.zeros 2176 →
      Curry.apply (aesSig.words pb) (wipedPost pb P fun i => decide (i < 2176)) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  exact ⟨h, .of_zeros hz⟩

/-- With nothing of `scratch` written, `wipedPost` of none of it. -/
theorem unwritten (pb : Nat) (P : aesSig.Post pb) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) P vs m m' x →
    (∀ b ∈ Sig.arrays aesSig.params vs, b.1 = "scratch" →
      ∀ i, 0 ≤ i → i < b.2.len → m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply (aesSig.words pb) (wipedPost pb P fun _ => false) vs m m' x := by
  intro vs m m' x hlen h hw
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  refine ⟨h, .of_unchanged fun i hi => ?_⟩
  exact hw ("scratch", ⟨f, 2176⟩) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))) rfl i (Nat.zero_le _) hi

/-- A proof of a CBC function's contract is one of `wipedPost`'s for code
that writes nothing in `scratch`, on a calling convention that gives each
run the six arguments (`hlen`). -/
theorem Verified.cbc_of_unwritten {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    {P : aesSig.Post A.ptrBits}
    (h : Verified T c (aesSig.contract A (pre A.ptrBits) P false stack none))
    (hw : ∀ s t s', (aesSig.contract A (pre A.ptrBits) P false stack none).pre s →
      Exec T.isa c s t s' → Sig.writtenWithin A aesSig [("scratch", 0)] s s')
    (hlen : ∀ s vals, A.args ((aesSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      (vals s).length = (aesSig.words A.ptrBits).length) :
    Verified T c (aesSig.contract A (pre A.ptrBits) (wipedPost A.ptrBits P fun _ => false) false stack none) := by
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
    hag b hb a ha fun hp => hbA a ha (Region.sub_prefix (by simp only [Elem.size]; omega_using [hw]) a hp)
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  have hs := hag _ (by rw [bufs_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  refine ⟨hP' h.1, fun i hi hl => ?_⟩
  have hi64 : i < 2 ^ 64 := by omega_using [hl]
  rw [← h.2 i hi hl]
  refine (hs _ (Offset.contains_base _ (by omega_using [hl]) hi64) fun hc => ?_).symm
  simp only [Region.Contains, List.getD_cons_succ, List.getD_cons_zero] at hc
  rw [Mem.sub_ofNat_toNat f hi64] at hc
  omega_using [hi, hc]

/-- With `scratch` unchanged from `w` on and zero before, `wipedPost`. -/
theorem wipedTail (pb : Nat) (w : Nat) (P : aesSig.Post pb) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) (tailPost pb w P) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) w = Spec.Zeroize.zeros w →
      Curry.apply (aesSig.words pb) (wipedPost pb P fun i => decide (i < w)) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  exact ⟨h.1, .of_prefix hz h.2⟩

/-- `tailPost 0 P` is `wipedPost P`'s of none of `scratch`. -/
theorem tailPost_zero (pb : Nat) (P : aesSig.Post pb) :
    aesSig.PostImp pb (tailPost pb 0 P) (wipedPost pb P fun i => decide (i < 0)) :=
  fun _ _ _ _ _ _ _ _ _ h => ⟨h.1, .of_prefix rfl h.2⟩

/-! ## Zeroing the part of `scratch` left written -/

/-- `P`, with the bytes of `scratch` at offset `w` and beyond zero at the offsets `Z`, and
unchanged at the others. -/
def tailZPost (pb : Nat) (P : aesSig.Post pb) (w : Nat) (Z : Nat → Bool) : aesSig.Post pb :=
  fun schedule rounds iv data n scratch m m' x =>
    P schedule rounds iv data n scratch m m' x ∧ ∀ i, w ≤ i → i < 2176 →
      m' (scratch + BitVec.ofNat 64 i) = if Z i then 0 else m (scratch + BitVec.ofNat 64 i)

/-- `tailZPost` reads the memory on entry only within the buffers, if `P` does. -/
theorem tailZPost_local (pb : Nat) {P : aesSig.Post pb} (w : Nat) (Z : Nat → Bool)
    (hP : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
      (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) P vs m₁ m' x → Curry.apply (aesSig.words pb) P vs m₂ m' x) :
    ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (tailZPost pb P w Z) vs m₁ m' x →
      Curry.apply (aesSig.words pb) (tailZPost pb P w Z) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  obtain ⟨hp, ht⟩ := h
  refine ⟨hP [a, b, c, d, e, f] m₁ m₂ m' x hlen hb hp, fun i h1 h2 => ?_⟩
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  have e₂ := (agree_of hb.2.2.2 i (by omega_using [h2])).symm
  show m' (f + BitVec.ofNat 64 i) = if Z i then 0 else m₂ (f + BitVec.ofNat 64 i)
  rw [← e₂]
  exact ht i h1 h2

/-- `tailZPost` reads the memory on return only within the buffers apart from
the first `w` bytes of `scratch`, if `P` reads it only apart from `scratch`. -/
theorem tailZPost_out (pb : Nat) {P : aesSig.Post pb} {w : Nat} {Z : Nat → Bool} (hw : w ≤ 2176)
    (hP : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
      (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (aesSig.words pb) P vs m m₁ x → Curry.apply (aesSig.words pb) P vs m m₂ x) :
    ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 →
      ¬(⟨vs.getD 5 0, w⟩ : Region).Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (tailZPost pb P w Z) vs m m₁ x →
      Curry.apply (aesSig.words pb) (tailZPost pb P w Z) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  obtain ⟨hp, ht⟩ := h
  refine ⟨hP [a, b, c, d, e, f] m m₁ m₂ x hlen hpw
    (fun r hr hrd y hy => hb r hr y hy fun hc => hrd y hy (Region.sub_prefix hw y hc)) hp, fun i h1 h2 => ?_⟩
  have hc : (⟨f, 2176⟩ : Region).Contains (f + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [h2]) (by omega_using [h2])
  have hn : ¬ (⟨f, w⟩ : Region).Contains (f + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, BitVec.add_comm f, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
    omega_using [h1, h2]
  show m₂ (f + BitVec.ofNat 64 i) = if Z i then 0 else m (f + BitVec.ofNat 64 i)
  rw [← hb (⟨f, 2176⟩, true) (by rw [bufs_eq]; simp) _ hc hn]
  exact ht i h1 h2

/-- The first `w` bytes zero, and the others zero at the offsets `Z`, unchanged at the
others. -/
theorem wipedBy_of_prefix {m m' : Mem} {p : Addr} {w len : Nat} {Z : Nat → Bool}
    (hz : Spec.Zeroize.bytesAt m' p w = Spec.Zeroize.zeros w)
    (ht : ∀ i, w ≤ i → i < len →
      m' (p + BitVec.ofNat 64 i) = if Z i then 0 else m (p + BitVec.ofNat 64 i)) :
    Zeroize.WipedBy (fun i => decide (i < w) || Z i) m m' p len := by
  intro i hi
  by_cases hw : i < w
  · have h0 := Zeroize.WipedBy.of_zeros (m := m) hz i hw
    simp only [hw, decide_true, Bool.true_or, ite_true] at h0 ⊢
    exact h0
  · simp only [hw, decide_false, Bool.false_or]
    exact ht i (Nat.le_of_not_lt hw) hi

/-- With the first `w` bytes of `scratch` zero on return, `wipedPost`. -/
theorem wipedTailZ (pb : Nat) (P : aesSig.Post pb) (w : Nat) (Z : Nat → Bool) : ∀ vs m m' x,
    vs.length = (aesSig.words pb).length →
    Curry.apply (aesSig.words pb) (tailZPost pb P w Z) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) w = Spec.Zeroize.zeros w →
      Curry.apply (aesSig.words pb) (wipedPost pb P fun i => decide (i < w) || Z i) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  exact ⟨h.1, wipedBy_of_prefix hz h.2⟩

/-- `tailZPost P 0 Z` is `wipedPost P`'s of `Z`. -/
theorem tailZPost_zero (pb : Nat) (P : aesSig.Post pb) (Z : Nat → Bool) :
    aesSig.PostImp pb (tailZPost pb P 0 Z) (wipedPost pb P fun i => decide (i < 0) || Z i) :=
  fun _ _ _ _ _ _ _ _ _ h => ⟨h.1, wipedBy_of_prefix rfl h.2⟩

/-- A proof of a CBC function's contract is one of `tailZPost w Z`'s for code
that leaves the bytes of `scratch` at offset `w` and beyond zero at the offsets
`Z` and unchanged at the others, on a calling convention that gives each run the
six arguments (`hlen`). -/
theorem Verified.tailZ_of {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w : Nat} {Z : Nat → Bool}
    {P : aesSig.Post A.ptrBits}
    (h : Verified T c (aesSig.contract A (pre A.ptrBits) P false stack none))
    (hw : ∀ s t s', (aesSig.contract A (pre A.ptrBits) P false stack none).pre s → Exec T.isa c s t s' →
      ∀ vals, A.args ((aesSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      ∀ i, w ≤ i → i < 2176 →
        A.mem s' ((vals s).getD 5 0 + BitVec.ofNat 64 i) =
          if Z i then 0 else A.mem s ((vals s).getD 5 0 + BitVec.ofNat 64 i))
    (hlen : ∀ s vals, A.args ((aesSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      (vals s).length = (aesSig.words A.ptrBits).length) :
    Verified T c (aesSig.contract A (pre A.ptrBits) (tailZPost A.ptrBits P w Z) false stack none) := by
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

/-! ## The specification's contracts, and the public output -/

/-- What `wipedContract encPost` requires of a run meets `Spec.Cbc.aesEncryptContract`. -/
theorem encrypt_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat} {S : Nat → Bool}
    (h : VerifiedScrubbed T c (wipedContract encPost S A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (wipedContract encPost S A stack) rb) →
      T.noResidue.elim False fun R => R c (aesEncryptContract A stack) rb) :
    VerifiedScrubbed T c (aesEncryptContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ ⟨hp, hw⟩ => ⟨hp, hw.scrubbed⟩

/-- What `wipedContract decPost` requires of a run meets `Spec.Cbc.aesDecryptContract`. -/
theorem decrypt_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat} {S : Nat → Bool}
    (h : VerifiedScrubbed T c (wipedContract decPost S A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (wipedContract decPost S A stack) rb) →
      T.noResidue.elim False fun R => R c (aesDecryptContract A stack) rb) :
    VerifiedScrubbed T c (aesDecryptContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ ⟨hp, hw⟩ => ⟨hp, hw.scrubbed⟩

/-- `F` at the arguments `vs`. -/
theorem aes_apply {α : Type} (pb : Nat) (F : Curry (aesSig.words pb) α) :
    ∀ vs, Curry.apply (aesSig.words pb) F vs =
      @id (Addr → BitVec pb → Addr → Addr → BitVec pb → Addr → α) F (vs.getD 0 0) ((vs.getD 1 0).setWidth pb)
        (vs.getD 2 0) (vs.getD 3 0) ((vs.getD 4 0).setWidth pb) (vs.getD 5 0)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

/-- Which bytes of `scratch` are zero is public, under any contract that differs from
`wipedContract` only in the postcondition. -/
theorem scratch_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat} {S : Nat → Bool}
    {P : ∀ pb, aesSig.Post pb} {post : aesSig.Post A.ptrBits}
    (h : VerifiedScrubbed T c (wipedContract P S A stack) rb) :
    aesScratchOut.Of A c (aesSig.contract A (pre A.ptrBits) post false stack none) := by
  refine PublicOut.of_post h.verified fun vals _ s₁ s₂ s₁' s₂' _ _ _ hg h₁ h₂ => ?_
  replace hg := (congrFun (aes_apply A.ptrBits _ _) _).symm.trans
    (hg.trans (congrFun (aes_apply A.ptrBits _ _) _))
  replace h₁ := (congrFun (congrFun (congrFun (aes_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (aes_apply A.ptrBits _ _) _) _) _).mp h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (aes_apply A.ptrBits (aesScratchOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s'))
    ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, aesScratchOut] at hg ⊢
  exact h₁.2.left h₂.2 hg

end VG.Proof.AesCbc.Wipe
