module

public import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# Camellia with its working space as an argument

`vg_camellia_expand_key` and the ECB functions keep their working space in a
frame of their own, which they zero before returning
(`Verified.stackScratchWiped`), around code proved with the working space as
a last argument: `expandKeyScratchContract n` and `ecbScratchContract n` are
the shared contracts with a `scratch` buffer of `n` words appended, whatever
it holds (each target lays out its own).

The frame zeroes the buffer after the code, which needs the postconditions
to read the memory on return only within the function's buffers
(`expandKeyPostOut_local`, `ecbPostOut_local`), as the postconditions on the
subkeys at the schedule (`ecbPostSk`) do.
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `vg_camellia_expand_key` with `scratch: *mut [u64; n]`. -/
def expandKeyScratchSig (n : Nat) : Sig where
  params := expandKeySig.params ++ [("scratch", .array true .u64 n)]

/-- `expandKeyContract`, whatever `scratch` is. -/
def expandKeyScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (expandKeyScratchSig n).contract A
    (pre := fun key keyLen schedule _scratch => expandKeyPre A.ptrBits key keyLen schedule)
    (post := fun key keyLen schedule _scratch => expandKeyPost A.ptrBits key keyLen schedule)
    (stack := stack)

theorem expandKeyScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    expandKeyScratchContract A n stack = Sig.scratchContract A expandKeySig "scratch" .u64 n
      (expandKeyPre A.ptrBits) (expandKeyPost A.ptrBits) false stack := rfl

/-! ## The contracts on the subkeys at the schedule

The proofs show the mode functions correct under the subkeys they read from
the schedule (`subkeysAt`), whoever wrote them: `ecbPostSk` and the others
(`CtrScratch.lean`, `FbScratch.lean`, `CbcScratch.lean`) are the
postconditions so stated, for `rounds` of 18 or 24, and `ecbContractSk` the
contract with it. The shared contracts (`ecbContract`, …) state them for a
schedule `vg_camellia_expand_key` wrote from a key (`KeySchedule`), under
that key's subkeys (`expandKey`): `subkeysAt_of_keySchedule` reads them back,
and `verified_of_post` moves a proof from the one contract to the other. -/

/-- `f` implies `g` for every value of the arguments: for a postcondition
`g` of `Sig.contract`, the implementations meeting `f` meet it. -/
def Curry.Imp {β : Type} : (ws : List ArgWord) → Curry ws (Mem → Mem → β → Prop) →
    Curry ws (Mem → Mem → β → Prop) → Prop
  | [], f, g => ∀ m m' r, f m m' r → g m m' r
  | _ :: ws, f, g => ∀ x, Curry.Imp ws (f x) (g x)

theorem Curry.Imp.apply {β : Type} : ∀ {ws : List ArgWord} {f g : Curry ws (Mem → Mem → β → Prop)},
    Curry.Imp ws f g → ∀ vs m m' r, Curry.apply ws f vs m m' r → Curry.apply ws g vs m m' r
  | [], _, _, h, _, m, m', r, hf => h m m' r hf
  | _ :: _, _, _, h, _ :: vs, m, m', r, hf => Curry.Imp.apply (h _) vs m m' r hf
  | _ :: _, _, _, h, [], m, m', r, hf => Curry.Imp.apply (h _) [] m m' r hf

/-- A function verified with a postcondition `post` is verified with any
`post'` that `post` implies. -/
theorem verified_of_post {T : Target} {c : Prog T.isa} {A : Abi T.isa} {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post post' : sig.Post A.ptrBits}
    {wa : Bool} {stack : Nat} (h : Verified T c (sig.contract A pre post wa stack))
    (hp : Curry.Imp _ post post') : Verified T c (sig.contract A pre post' wa stack) :=
  Verified.of_implies h
    { pre := fun _ h => h
      post := fun s s' _ => by
        simp only [Sig.contract]
        split
        · exact id
        · exact hp.apply _ _ _ _
      pub := fun _ _ _ _ h => h
      sat := h.2.2 }

theorem ofBytes_wordBytes (w : BitVec 64) : ofBytes 64 (wordBytes w) = w := by
  apply BitVec.eq_of_toNat_eq
  simp only [ofBytes, wordBytes, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons, List.foldl_nil,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

theorem rounds_of_keySchedule {m : Mem} {p : Addr} {R : Nat} {key : List Byte}
    (h : KeySchedule m p R key) : R = 18 ∨ R = 24 := by
  obtain ⟨_, rfl, _⟩ := h
  simp only [rounds]; split <;> simp

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, BitVec.ofNat_add, BitVec.add_assoc]

/-- The words read from bytes stored as `wordBytes` of each of `ws`, in order,
are `ws`. -/
theorem words_of_bytes {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)},
    bytesAt m p (8 * ws.length) = ws.flatMap wordBytes →
      (List.range ws.length).map (fun i => wordAt m (p + BitVec.ofNat 64 (8 * i))) = ws
  | _, [], _ => rfl
  | p, w :: ws, h => by
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm, bytesAt_add, List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [bytesAt, wordBytes])
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp only [wordAt, Nat.mul_zero, BitVec.add_zero, h₁, ofBytes_wordBytes]
    · refine Eq.trans (List.map_congr_left fun i _ => ?_) (words_of_bytes h₂)
      simp only [Function.comp, Nat.mul_succ, Nat.add_comm _ 8, BitVec.ofNat_add, BitVec.add_assoc]

/-- Subkeys of `R` rounds, as many as `expandKey` gives, read back from their
stored order. -/
theorem subkeysOfWords_scheduleWords {sk : Subkeys} {R : Nat} (hR : R = 18 ∨ R = 24)
    (hkw : sk.kw.length = 4) (hk : sk.k.length = R) (hke : sk.ke.length = R / 3 - 2) :
    subkeysOfWords R (scheduleWords sk) = sk ∧ (scheduleWords sk).length = scheduleLength R := by
  obtain ⟨kw, k, ke⟩ := sk
  dsimp only at hkw hk hke
  iterate 4
    obtain ⟨_, kw, rfl⟩ := List.exists_cons_of_length_eq_add_one hkw
    replace hkw := Nat.succ.inj hkw
  obtain rfl := List.eq_nil_of_length_eq_zero hkw
  rcases hR with rfl | rfl
  · iterate 18
      obtain ⟨_, k, rfl⟩ := List.exists_cons_of_length_eq_add_one hk
      replace hk := Nat.succ.inj hk
    obtain rfl := List.eq_nil_of_length_eq_zero hk
    iterate 4
      obtain ⟨_, ke, rfl⟩ := List.exists_cons_of_length_eq_add_one hke
      replace hke := Nat.succ.inj hke
    obtain rfl := List.eq_nil_of_length_eq_zero hke
    constructor <;> simp [subkeysOfWords, scheduleWords, scheduleLength, List.range_succ]
  · iterate 24
      obtain ⟨_, k, rfl⟩ := List.exists_cons_of_length_eq_add_one hk
      replace hk := Nat.succ.inj hk
    obtain rfl := List.eq_nil_of_length_eq_zero hk
    iterate 6
      obtain ⟨_, ke, rfl⟩ := List.exists_cons_of_length_eq_add_one hke
      replace hke := Nat.succ.inj hke
    obtain rfl := List.eq_nil_of_length_eq_zero hke
    constructor <;> simp [subkeysOfWords, scheduleWords, scheduleLength, List.range_succ]

theorem expandKey_lengths (key : List Byte) :
    (expandKey key).kw.length = 4 ∧ (expandKey key).k.length = rounds key.length ∧
      (expandKey key).ke.length = rounds key.length / 3 - 2 := by
  unfold expandKey rounds
  dsimp only
  split <;> simp only [List.length_cons, List.length_nil] <;> decide

/-- The subkeys read from a schedule that `vg_camellia_expand_key` wrote are
the key's. -/
theorem subkeysAt_of_keySchedule {m : Mem} {p : Addr} {R : Nat} {key : List Byte}
    (h : KeySchedule m p R key) : subkeysAt m p R = expandKey key := by
  have hR := rounds_of_keySchedule h
  obtain ⟨-, rfl, hb⟩ := h
  obtain ⟨h₁, h₂, h₃⟩ := expandKey_lengths key
  obtain ⟨hrt, hlen⟩ := subkeysOfWords_scheduleWords hR h₁ h₂ h₃
  rw [subkeysAt, ← hlen]
  rw [← hlen, scheduleBytes] at hb
  rw [words_of_bytes hb, hrt]

/-- ECB's postcondition on the subkeys at `schedule`, for `rounds` of 18 or 24. -/
def ecbPostSk (direction : Direction) (pb : Nat) : ecbSig.Post pb := fun schedule rounds data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    blocksAt m' data n.toNat =
      ecb (subkeysAt m schedule rounds.toNat) direction (blocksAt m data n.toNat)

/-- `ecbContract` with `ecbPostSk`. -/
def ecbContractSk {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (pre := ecbPre A.ptrBits) (post := ecbPostSk direction A.ptrBits) (stack := stack)

theorem ecbPost_of_sk (direction : Direction) (pb : Nat) :
    Curry.Imp _ (ecbPostSk direction pb) (ecbPost direction pb) := by
  intro _ _ _ _ _ _ _ h key hk
  rw [← subkeysAt_of_keySchedule hk]
  exact h (rounds_of_keySchedule hk)

theorem ecb_of_sk {T : Target} {c : Prog T.isa} {A : Abi T.isa} {direction : Direction}
    {stack : Nat} (h : Verified T c (ecbContractSk A direction stack)) :
    Verified T c (ecbContract A direction stack) :=
  verified_of_post h (ecbPost_of_sk direction A.ptrBits)

/-- The ECB functions with `scratch: *mut [u64; n]`. -/
def ecbScratchSig (n : Nat) : Sig where
  params := ecbSig.params ++ [("scratch", .array true .u64 n)]

/-- `ecbContractSk`, whatever `scratch` is. -/
def ecbScratchContract {M : ISA} (A : Abi M) (direction : Direction) (n : Nat) (stack : Nat := 0) :
    Contract M :=
  (ecbScratchSig n).contract A
    (pre := fun schedule rounds data n _scratch => ecbPre A.ptrBits schedule rounds data n)
    (post := fun schedule rounds data n _scratch => ecbPostSk direction A.ptrBits schedule rounds data n)
    (stack := stack)

theorem ecbScratchContract_eq {M : ISA} (A : Abi M) (direction : Direction) (n stack : Nat) :
    ecbScratchContract A direction n stack = Sig.scratchContract A ecbSig "scratch" .u64 n
      (ecbPre A.ptrBits) (ecbPostSk direction A.ptrBits) false stack := rfl

/-! ## Locality -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem blocksAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 16 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt, blockAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  congr 1
  funext j
  have : 16 * i + j.val < 16 * n := by have := j.isLt; omega_arith
  rw [Offset.add_add]
  exact h _ this

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

theorem scheduleLength_rounds_le (k : Nat) : scheduleLength (rounds k) ≤ 34 := by
  simp only [scheduleLength, rounds]; split <;> omega_arith

variable (pb : Nat)

theorem expandKeyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₁ r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₂ r
  dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h ⊢
  intro hk
  rw [bytesAt_congr fun i hi => hs i (by
    have := scheduleLength_rounds_le (kl.setWidth pb).toNat
    omega_arith)]
  exact h hk

theorem expandKeyPre_local : ∀ vs m₁ m₂, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPre pb) vs m₁ →
      Curry.apply (expandKeySig.words pb) (expandKeyPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem expandKeyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₁ m' r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 2
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hk := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m₂ m' r
  dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h hk ⊢
  intro hl
  rw [bytesAt_congr fun i hi => hk i (by
    rw [BitVec.toNat_setWidth] at hi; exact Nat.lt_of_lt_of_le hi (Nat.mod_le _ _))]
  exact h hl

theorem ecbPostOut_local (direction : Direction) : ∀ vs m m₁ m₂ r,
    vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPostSk direction pb) vs m m₁ r →
      Curry.apply (ecbSig.words pb) (ecbPostSk direction pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (ecbPostSk direction pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (ecbPostSk direction pb) _ m m₂ r
  dsimp only [Curry.apply, ecbPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h hR

theorem subkeysAt_congr {m₁ m₂ : Mem} {p : Addr} {R : Nat} (hR : scheduleLength R ≤ 34)
    (h : ∀ i < 272, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    subkeysAt m₂ p R = subkeysAt m₁ p R := by
  simp only [subkeysAt]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  simp only [wordAt]
  congr 1
  exact bytesAt_congr fun j hj => by rw [Offset.add_add]; exact h _ (by omega_arith)

theorem ecbPre_local : ∀ vs m₁ m₂, vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPre pb) vs m₁ → Curry.apply (ecbSig.words pb) (ecbPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem ecbPost_local (direction : Direction) : ∀ vs m₁ m₂ m' r,
    vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPostSk direction pb) vs m₁ m' r →
      Curry.apply (ecbSig.words pb) (ecbPostSk direction pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rounds, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hd := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (ecbPostSk direction pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (ecbPostSk direction pb) _ m₂ m' r
  dsimp only [Curry.apply, ecbPostSk, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  intro hR
  rw [subkeysAt_congr (by simp only [scheduleLength]; omega_arith) fun i hi => hs i (by omega_arith),
    blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith)]
  exact h hR

end VG.Proof.Camellia
