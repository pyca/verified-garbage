module

public import VerifiedGarbage.Spec.AesEcb.Contract
public import VerifiedGarbage.Proof.Framework.PublicOut
public import VerifiedGarbage.Proof.Zeroize.Wiped
public import VerifiedGarbage.Proof.Aes.Rounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: every target's ECB proofs share it

/-!
# AES-ECB from the blocks functions, on every target

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` are the code of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (or of one of their
variants) where it writes nothing in `scratch` (`Verified.ecb_of_unwritten`),
and otherwise a call of it followed by the zeroize function on the whole of
`scratch`, or on the part of it that they write, which the target's
`callWipe` proves zero on return (`wiped`, `wipedTail`). Either way, the first
`w` bytes of `scratch` are zero and the others unchanged (`ecbPost`), for a `w`
that depends only on the code. So each target proves its functions against a
contract that says which bytes those are (`wipedContract`), which implies the
specification's (`encrypt_imp`, `decrypt_imp`: each byte of `scratch` is unchanged
or zero, `Spec.Zeroize.scrubbed`), and that which bytes are zero is public
(`scratch_public`, `Spec.AesEcb.scratchOut`).

`callWipe` needs the blocks functions' postcondition to read the memory on
entry only within the buffers (`post_local`) and the memory on return only
within the buffers apart from `scratch` (`post_out`): the key schedule, of at
most 240 bytes for any schedule `Spec.Aes.KeySchedule` allows, and the data.
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
  · exact Offset.contains_base _ (by omega_using [hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hi, hw]

theorem statesAt_congr {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    statesAt m₂ p n = statesAt m₁ p n := by
  simp only [statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [stateAt]
  refine congrArg Vector.ofFn (funext fun i => ?_)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega_using [hj])

/-- A key schedule is read within the 240 bytes at `schedule`. -/
theorem keySchedule_congr {r : Nat} {key : List Byte}
    (h : ∀ i < 240, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    KeySchedule m₂ p r key ↔ KeySchedule m₁ p r key := by
  simp only [KeySchedule]
  constructor <;> rintro ⟨hl, hr, hb⟩ <;> refine ⟨hl, hr, ?_⟩ <;>
    · have : 16 * (r + 1) ≤ 240 := by
        simp only [Spec.Aes.rounds] at hr; omega_using [hl, hr]
      first
      | rw [← bytesAt_congr fun i hi => h i (by omega_using [this, hi])]; exact hb
      | rw [bytesAt_congr fun i hi => h i (by omega_using [this, hi])]; exact hb

end

/-! ## The contracts -/

/-- The precondition of the blocks functions and of ECB. -/
def pre (pb : Nat) : Curry (blocksSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _data _n _scratch _ => rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- The postcondition of the blocks functions, for `g key` the cipher or the
inverse cipher of `key`. -/
def post (pb : Nat) (g : List Byte → State → State) : blocksSig.Post pb :=
  fun schedule rounds data n _scratch m m' _ =>
    ∀ key, KeySchedule m schedule rounds.toNat key →
      statesAt m' data n.toNat = (statesAt m data n.toNat).map (g key)

/-- The postcondition of ECB that each target proves: the blocks functions', and
the first `w` bytes of `scratch` zero, the others unchanged. -/
def ecbPost (pb : Nat) (g : List Byte → State → State) (w : Nat) : blocksSig.Post pb :=
  fun schedule rounds data n scratch m m' x =>
    post pb g schedule rounds data n scratch m m' x ∧
      Zeroize.WipedBy (fun i => decide (i < w)) m m' scratch 2048

/-- The cipher of a key. -/
def enc (key : List Byte) : State → State := cipher (Spec.Aes.rounds (key.length / 4)) (expandKey key)

/-- The inverse cipher of a key. -/
def dec (key : List Byte) : State → State := invCipher (Spec.Aes.rounds (key.length / 4)) (expandKey key)

theorem encryptBlocks_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Proof.Aes.encryptBlocksContract A stack = blocksSig.contract A (pre A.ptrBits) (post A.ptrBits enc) false stack none :=
  rfl

theorem decryptBlocks_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Proof.Aes.decryptBlocksContract A stack = blocksSig.contract A (pre A.ptrBits) (post A.ptrBits dec) false stack none :=
  rfl

/-- `Spec.AesEcb.encryptContract`, for `g` `enc`, and `Spec.AesEcb.decryptContract`, for
`g` `dec`, for code that leaves the first `w` bytes of `scratch` zero and the others as
they were. -/
def wipedContract (g : List Byte → State → State) (w : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A (pre A.ptrBits) (ecbPost A.ptrBits g w) false stack none

/-- An `Api` with that contract: the forms that clean up a function's code take one. -/
def wipedApi (g : List Byte → State → State) (w : Nat) : Api :=
  { Spec.AesEcb.encryptApi with contracts := some fun A stack => wipedContract g w A stack }

/-- The arguments, five words. -/
theorem vs_eq {pb : Nat} {vs : List (BitVec 64)} (h : vs.length = (blocksSig.words pb).length) :
    ∃ a b c d e, vs = [a, b, c, d, e] := by
  obtain ⟨a, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) h
  replace h := Nat.succ.inj h
  obtain ⟨b, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain ⟨e, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one h
  replace h := Nat.succ.inj h
  obtain rfl := List.eq_nil_of_length_eq_zero h
  exact ⟨a, b, c, d, e, rfl⟩

theorem bufs_eq {a b c d e : BitVec 64} :
    Sig.bufs blocksSig.params [a, b, c, d, e] =
      [(⟨a, 240⟩, false), (⟨c, d.toNat * 16⟩, true), (⟨e, 2048⟩, true)] :=
  rfl

/-- The number of blocks the contract sees is at most that of the data's
region. -/
theorem n_le {pb : Nat} (d : BitVec 64) : (d.setWidth pb).toNat ≤ d.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-! ## Locality of the contracts -/

/-- The precondition reads no memory. -/
theorem pre_local (pb : Nat) : ∀ vs (m₁ m₂ : Mem), vs.length = (blocksSig.words pb).length →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (pre pb) vs m₁ → Curry.apply (blocksSig.words pb) (pre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, _, _, _, _, rfl⟩ := vs_eq hlen
  exact h

/-- The postcondition reads the memory on entry only within the buffers. -/
theorem post_local (pb : Nat) (g : List Byte → State → State) : ∀ vs m₁ m₂ m' x,
    vs.length = (blocksSig.words pb).length →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (post pb g) vs m₁ m' x →
      Curry.apply (blocksSig.words pb) (post pb g) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  intro key hk
  show statesAt m' c (d.setWidth pb).toNat = (statesAt m₂ c (d.setWidth pb).toNat).map (g key)
  have hd := agree_of hb.2.1
  rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := pb) d; omega_using [hi, this])]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

/-- The postcondition reads the memory on return only within the buffers
apart from `scratch`. -/
theorem post_out (pb : Nat) (g : List Byte → State → State) : ∀ vs m m₁ m₂ x,
    vs.length = (blocksSig.words pb).length →
    (Sig.bufs blocksSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs blocksSig.params vs, b.1.Disjoint ⟨vs.getD 4 0, 256 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (post pb g) vs m m₁ x →
      Curry.apply (blocksSig.words pb) (post pb g) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Bool.or_true, Bool.true_or, forall_const, List.Pairwise.nil, and_true] at hpw
  intro key hk
  show statesAt m₂ c (d.setWidth pb).toNat = (statesAt m c (d.setWidth pb).toNat).map (g key)
  have hd := agree_of (hb.2.1 hpw.2.1)
  rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := pb) d; omega_using [hi, this])]
  exact h key hk

/-- ECB's postcondition reads the memory on return only within the buffers. -/
theorem ecbPost_out (pb : Nat) (g : List Byte → State → State) (w : Nat) : ∀ vs m m₁ m₂ x,
    vs.length = (blocksSig.words pb).length →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (ecbPost pb g w) vs m m₁ x →
      Curry.apply (blocksSig.words pb) (ecbPost pb g w) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hb h
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun key hk => ?_, h2.congr (fun _ _ => rfl) (agree_of hb.2.2)⟩
  show statesAt m₂ c (d.setWidth pb).toNat = (statesAt m c (d.setWidth pb).toNat).map (g key)
  have hd := agree_of hb.2.1
  rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := pb) d; omega_using [hi, this])]
  exact h1 key hk

/-- With the whole of `scratch` zero on return, the postcondition of ECB. -/
theorem wiped (pb : Nat) (g : List Byte → State → State) : ∀ vs m m' x,
    vs.length = (blocksSig.words pb).length →
    Curry.apply (blocksSig.words pb) (post pb g) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) 2048 = Spec.Zeroize.zeros 2048 →
      Curry.apply (blocksSig.words pb) (ecbPost pb g 2048) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  exact ⟨h, .of_zeros hz⟩

/-- With nothing of `scratch` written, the postcondition of ECB. -/
theorem unwritten (pb : Nat) (g : List Byte → State → State) : ∀ vs m m' x,
    vs.length = (blocksSig.words pb).length →
    Curry.apply (blocksSig.words pb) (post pb g) vs m m' x →
    (∀ b ∈ Sig.arrays blocksSig.params vs, b.1 = "scratch" →
      ∀ i, 0 ≤ i → i < b.2.len → m' (b.2.base + BitVec.ofNat 64 i) = m (b.2.base + BitVec.ofNat 64 i)) →
      Curry.apply (blocksSig.words pb) (ecbPost pb g 0) vs m m' x := by
  intro vs m m' x hlen h hw
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  exact ⟨h, .of_prefix rfl (hw ("scratch", ⟨e, 2048⟩) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl)⟩

/-- A proof of the blocks functions' contract is one of ECB's for code that
writes nothing in `scratch`, on a calling convention that gives each run the
five arguments (`hlen`). -/
theorem Verified.ecb_of_unwritten {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    {g : List Byte → State → State}
    (h : Verified T c (blocksSig.contract A (pre A.ptrBits) (post A.ptrBits g) false stack none))
    (hw : ∀ s t s', (blocksSig.contract A (pre A.ptrBits) (post A.ptrBits g) false stack none).pre s →
      Exec T.isa c s t s' → Sig.writtenWithin A blocksSig [("scratch", 0)] s s')
    (hlen : ∀ s vals, A.args ((blocksSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      (vals s).length = (blocksSig.words A.ptrBits).length) :
    Verified T c (blocksSig.contract A (pre A.ptrBits) (ecbPost A.ptrBits g 0) false stack none) := by
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
    exact unwritten _ g _ _ _ _ (hlen s vals hv) hq fun b hb hn i hi hl =>
      hW _ (List.mem_singleton_self _) b hb hn i hi hl


/-! ## Zeroing the part of `scratch` that is written -/

/-- The blocks functions' postcondition, with the bytes of `scratch` at
offset `w` and beyond unchanged. -/
def postTail (pb : Nat) (g : List Byte → State → State) (w : Nat) : blocksSig.Post pb :=
  fun schedule rounds data n scratch m m' x =>
    post pb g schedule rounds data n scratch m m' x ∧
      ∀ i, w ≤ i → i < 2048 → m' (scratch + BitVec.ofNat 64 i) = m (scratch + BitVec.ofNat 64 i)

/-- `postTail` reads the memory on entry only within the buffers. -/
theorem postTail_local (pb : Nat) (g : List Byte → State → State) (w : Nat) : ∀ vs m₁ m₂ m' x,
    vs.length = (blocksSig.words pb).length →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (postTail pb g w) vs m₁ m' x →
      Curry.apply (blocksSig.words pb) (postTail pb g w) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  obtain ⟨hp, ht⟩ := h
  refine ⟨post_local pb g [a, b, c, d, e] m₁ m₂ m' x hlen hb hp, fun i h1 h2 => ?_⟩
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  rw [ht i h1 h2]
  exact (agree_of hb.2.2 i (by omega_using [h2])).symm

/-- `postTail` reads the memory on return only within the buffers apart
from the first `w` bytes of `scratch`. -/
theorem postTail_out (pb : Nat) (g : List Byte → State → State) {w : Nat} (hw : w ≤ 2048) : ∀ vs m m₁ m₂ x,
    vs.length = (blocksSig.words pb).length →
    (Sig.bufs blocksSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs blocksSig.params vs, ∀ a, b.1.Contains a 1 →
      ¬(⟨vs.getD 4 0, w⟩ : Region).Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (blocksSig.words pb) (postTail pb g w) vs m m₁ x →
      Curry.apply (blocksSig.words pb) (postTail pb g w) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  obtain ⟨hp, ht⟩ := h
  refine ⟨post_out pb g [a, b, c, d, e] m m₁ m₂ x hlen hpw
    (fun r hr hrd y hy => hb r hr y hy fun hc => hrd y hy (Region.sub_prefix hw y hc)) hp, fun i h1 h2 => ?_⟩
  have hc : (⟨e, 2048⟩ : Region).Contains (e + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [h2]) (by omega_using [h2])
  have hn : ¬ (⟨e, w⟩ : Region).Contains (e + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, BitVec.add_comm e, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
    omega_using [h1, h2]
  show m₂ (e + BitVec.ofNat 64 i) = m (e + BitVec.ofNat 64 i)
  rw [← hb (⟨e, 2048⟩, true) (by rw [bufs_eq]; simp) _ hc hn]
  exact ht i h1 h2

/-- With the first `w` bytes of `scratch` zero on return, the postcondition
of ECB. -/
theorem wipedTail (pb : Nat) (g : List Byte → State → State) (w : Nat) : ∀ vs m m' x,
    vs.length = (blocksSig.words pb).length →
    Curry.apply (blocksSig.words pb) (postTail pb g w) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) w = Spec.Zeroize.zeros w →
      Curry.apply (blocksSig.words pb) (ecbPost pb g w) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
  exact ⟨h.1, .of_prefix hz h.2⟩

/-- A proof of the blocks functions' contract is one with `postTail w` for
code that writes `scratch` only within its first `w` bytes. -/
theorem Verified.tail_of_written {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w : Nat}
    {g : List Byte → State → State}
    (h : Verified T c (blocksSig.contract A (pre A.ptrBits) (post A.ptrBits g) false stack none))
    (hw : ∀ s t s', (blocksSig.contract A (pre A.ptrBits) (post A.ptrBits g) false stack none).pre s →
      Exec T.isa c s t s' → Sig.writtenWithin A blocksSig [("scratch", w)] s s')
    (hlen : ∀ s vals, A.args ((blocksSig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals →
      (vals s).length = (blocksSig.words A.ptrBits).length) :
    Verified T c (blocksSig.contract A (pre A.ptrBits) (postTail A.ptrBits g w) false stack none) := by
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
    have hl := hlen s vals hv
    obtain ⟨a, b, c, d, e, he'⟩ := vs_eq hl
    rw [he'] at hq hW ⊢
    refine ⟨hq, fun i h1 h2 => ?_⟩
    exact hW _ (List.mem_singleton_self _) ("scratch", ⟨e, 2048⟩)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl i h1 h2

/-! ## The specification's contracts, and the public output -/

/-- What `wipedContract enc` requires of a run meets `Spec.AesEcb.encryptContract`. -/
theorem encrypt_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb w : Nat}
    (h : VerifiedScrubbed T c (wipedContract enc w A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (wipedContract enc w A stack) rb) →
      T.noResidue.elim False fun R => R c (Spec.AesEcb.encryptContract A stack) rb) :
    VerifiedScrubbed T c (Spec.AesEcb.encryptContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ ⟨hp, hw⟩ => ⟨hp, hw.scrubbed⟩

/-- What `wipedContract dec` requires of a run meets `Spec.AesEcb.decryptContract`. -/
theorem decrypt_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb w : Nat}
    (h : VerifiedScrubbed T c (wipedContract dec w A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (wipedContract dec w A stack) rb) →
      T.noResidue.elim False fun R => R c (Spec.AesEcb.decryptContract A stack) rb) :
    VerifiedScrubbed T c (Spec.AesEcb.decryptContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ ⟨hp, hw⟩ => ⟨hp, hw.scrubbed⟩

/-- `F` at the arguments `vs`. -/
theorem blocks_apply {α : Type} (pb : Nat) (F : Curry (blocksSig.words pb) α) :
    ∀ vs, Curry.apply (blocksSig.words pb) F vs =
      @id (Addr → BitVec pb → Addr → BitVec pb → Addr → α) F (vs.getD 0 0) ((vs.getD 1 0).setWidth pb)
        (vs.getD 2 0) ((vs.getD 3 0).setWidth pb) (vs.getD 4 0)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

/-- Which bytes of `scratch` are zero is public, under any contract that differs from
`wipedContract` only in the postcondition. -/
theorem scratch_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb w : Nat}
    {g : List Byte → State → State} {post : blocksSig.Post A.ptrBits}
    (h : VerifiedScrubbed T c (wipedContract g w A stack) rb) :
    Spec.AesEcb.scratchOut.Of A c (blocksSig.contract A (pre A.ptrBits) post false stack none) := by
  refine PublicOut.of_post h.verified fun vals _ s₁ s₂ s₁' s₂' _ _ _ hg h₁ h₂ => ?_
  replace hg := (congrFun (blocks_apply A.ptrBits _ _) _).symm.trans
    (hg.trans (congrFun (blocks_apply A.ptrBits _ _) _))
  replace h₁ := (congrFun (congrFun (congrFun (blocks_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (blocks_apply A.ptrBits _ _) _) _) _).mp h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (blocks_apply A.ptrBits (Spec.AesEcb.scratchOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s'))
    ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, Spec.AesEcb.scratchOut] at hg ⊢
  exact h₁.2.left h₂.2 hg

end VG.Proof.AesEcb
