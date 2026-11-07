module

public import VerifiedGarbage.Spec.AesEcb.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

-- separate module: every target's `Proof/AesEcb/<ISA>.lean` imports it (PPC64LE's so far).

/-!
# AES-ECB from the blocks functions and a wipe: what every target shares

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` (`Spec/AesEcb/Contract.lean`)
are `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` that leave `scratch`
scrubbed. On each target an implementation of the blocks function is called
by that target's `callWipe` (`Proof/Framework/<ISA>/CallWipe.lean`), which
then zeroes the bytes of `scratch` it may write. `Verified.callWipe'` needs,
of the blocks contracts' pre- and postconditions, what is proven here for any
pointer width `pb`:

* the precondition reads no memory (`pre_local`);
* the postcondition reads the memory on entry only within the buffers
  (`encPost_local`, `decPost_local`): the key schedule (of at most 240 bytes
  for any schedule `Aes.KeySchedule` allows) and the data;
* it reads the memory on return only within the buffers apart from
  `scratch` (`encPost_out`, `decPost_out`): the data;
* with the first `len` bytes of `scratch` zero, and the rest unchanged, the
  ECB postcondition holds (`encPost_wiped`, `decPost_wiped`).
-/

@[expose] public section

namespace VG.Proof.AesEcb

open VG VG.Spec.Aes

/-! ## Locality -/

section
variable {m₁ m₂ : Mem} {p : Addr}

theorem bytesAt_congr {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem statesAt_congr {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    statesAt m₂ p n = statesAt m₁ p n := by
  simp only [statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [stateAt]
  congr 1
  funext i
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

/-- A key schedule is read within the 240 bytes at `schedule`. -/
theorem keySchedule_congr {r : Nat} {key : List Byte}
    (h : ∀ i < 240, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    KeySchedule m₂ p r key ↔ KeySchedule m₁ p r key := by
  simp only [KeySchedule]
  constructor <;> rintro ⟨hl, hr, hb⟩ <;> refine ⟨hl, hr, ?_⟩ <;>
    · have : 16 * (r + 1) ≤ 240 := by
        simp only [Spec.Aes.rounds] at hr; omega
      first
      | rw [← bytesAt_congr fun i hi => h i (by omega)]; exact hb
      | rw [bytesAt_congr fun i hi => h i (by omega)]; exact hb

end

/-! ## The contracts' conditions -/

variable (pb : Nat)

/-- The blocks functions' precondition. -/
def blocksPre : Curry (blocksSig.words pb) (Mem → Prop) := fun _schedule rounds _data _n _scratch _ =>
  rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- The `n` blocks' bytes, within the `l` 16-byte elements of the slice. -/
theorem len_le (l : BitVec 64) : (l.setWidth pb).toNat ≤ l.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-- The five argument words of a list of the signature's length. -/
theorem words5 {vs : List (BitVec 64)} (hlen : vs.length = (blocksSig.words pb).length) :
    ∃ sch r d n scr, vs = [sch, r, d, n, scr] := by
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨scr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact ⟨sch, r, d, n, scr, rfl⟩

theorem bufs5 (sch r d n scr : BitVec 64) :
    Sig.bufs blocksSig.params [sch, r, d, n, scr] =
      [(⟨sch, 240⟩, false), (⟨d, n.toNat * 16⟩, true), (⟨scr, 2048⟩, true)] := rfl

/-- A blocks function's postcondition, for the cipher `f` of a key's length in
words and the key. -/
def blocksPost (f : Nat → List Byte → State → State) : blocksSig.Post pb :=
  fun schedule rounds data n _scratch m m' _ =>
    ∀ key, KeySchedule m schedule rounds.toNat key →
      statesAt m' data n.toNat = (statesAt m data n.toNat).map (f (key.length / 4) key)

/-- The ECB function's postcondition: the blocks function's, with `scratch`
scrubbed. -/
def ecbPost (f : Nat → List Byte → State → State) : blocksSig.Post pb :=
  fun schedule rounds data n scratch m m' x =>
    blocksPost pb f schedule rounds data n scratch m m' x ∧ Spec.Zeroize.scrubbed m m' scratch 2048

theorem blocksPost_curry (f : Nat → List Byte → State → State) (sch r d n scr : BitVec 64) (m m' : Mem) x :
    Curry.apply (blocksSig.words pb) (blocksPost pb f) [sch, r, d, n, scr] m m' x =
      ∀ key, KeySchedule m sch (r.setWidth pb).toNat key →
        statesAt m' d (n.setWidth pb).toNat = (statesAt m d (n.setWidth pb).toNat).map (f (key.length / 4) key) :=
  rfl

theorem ecbPost_curry (f : Nat → List Byte → State → State) (sch r d n scr : BitVec 64) (m m' : Mem) x :
    Curry.apply (blocksSig.words pb) (ecbPost pb f) [sch, r, d, n, scr] m m' x =
      (Curry.apply (blocksSig.words pb) (blocksPost pb f) [sch, r, d, n, scr] m m' x ∧
        Spec.Zeroize.scrubbed m m' scr 2048) :=
  rfl

/-- The precondition reads no memory. -/
theorem pre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (blocksSig.words pb).length →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (blocksPre pb) vs m₁ → Curry.apply (blocksSig.words pb) (blocksPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, _, _, _, _, rfl⟩ := words5 pb hlen
  exact h

theorem post_local {f : Nat → List Byte → State → State} :
    ∀ vs m₁ m₂ m' x, vs.length = (blocksSig.words pb).length →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (blocksPost pb f) vs m₁ m' x →
    Curry.apply (blocksSig.words pb) (blocksPost pb f) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨sch, r, d, n, scr, rfl⟩ := words5 pb hlen
  rw [bufs5] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  replace h := Eq.mp (blocksPost_curry pb f sch r d n scr m₁ m' x) h
  refine Eq.mpr (blocksPost_curry pb f sch r d n scr m₂ m' x) ?_
  intro key hk
  have hd := agree_of hb.2.1
  rw [statesAt_congr (fun i hi => hd i (by have := len_le pb n; omega))]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

theorem post_out {f : Nat → List Byte → State → State} :
    ∀ vs m m₁ m₂ x, vs.length = (blocksSig.words pb).length →
    (Sig.bufs blocksSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs blocksSig.params vs, b.1.Disjoint ⟨vs.getD 4 0, 256 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (blocksPost pb f) vs m m₁ x →
    Curry.apply (blocksSig.words pb) (blocksPost pb f) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨sch, r, d, n, scr, rfl⟩ := words5 pb hlen
  rw [bufs5] at hb hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.getD_cons_succ,
    List.getD_cons_zero, Elem.size] at hb
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Bool.true_or, Bool.or_true, forall_const, List.Pairwise.nil, and_true] at hpw
  replace h := Eq.mp (blocksPost_curry pb f sch r d n scr m m₁ x) h
  refine Eq.mpr (blocksPost_curry pb f sch r d n scr m m₂ x) ?_
  intro key hk
  have hd := agree_of (hb.2.1 hpw.2.1)
  rw [statesAt_congr (fun i hi => hd i (by have := len_le pb n; omega))]
  exact h key hk

/-- With the 2048 bytes of `scratch` zero, they are scrubbed. -/
theorem scrubbed_of_zero {m m' : Mem} {p : Addr}
    (h : Spec.Zeroize.bytesAt m' p 2048 = Spec.Zeroize.zeros 2048) : Spec.Zeroize.scrubbed m m' p 2048 := by
  intro a ha
  refine .inr ?_
  simp only [Region.Contains] at ha
  have hi : (a - p).toNat < 2048 := ha
  have e := congrArg (fun l => l[(a - p).toNat]?) h
  simp only [Spec.Zeroize.bytesAt, Spec.Zeroize.zeros, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, List.getElem?_replicate, hi, ite_true, Option.some.injEq] at e
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at e

theorem post_wiped {f : Nat → List Byte → State → State} :
    ∀ vs m m' x, vs.length = (blocksSig.words pb).length →
    Curry.apply (blocksSig.words pb) (blocksPost pb f) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) 2048 = Spec.Zeroize.zeros 2048 →
    Curry.apply (blocksSig.words pb) (ecbPost pb f) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨sch, r, d, n, scr, rfl⟩ := words5 pb hlen
  exact Eq.mpr (ecbPost_curry pb f sch r d n scr m m' x) ⟨h, scrubbed_of_zero hz⟩

end VG.Proof.AesEcb
