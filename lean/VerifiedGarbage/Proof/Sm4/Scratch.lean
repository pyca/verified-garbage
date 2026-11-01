module

public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SM4 key expansion and ECB with their working space as an argument

`vg_sm4_expand_key` and the ECB functions keep their working space in a
frame of their own (`Verified.stackScratchWiped`), around code proved with
the working space as an argument: `expandKeyScratchContract n` and
`ecbScratchContract n` are the shared contracts with a `scratch` buffer of
`n` words appended, whatever it holds (each target lays out its own), and
so is `ctrScratchContract n`.

The frames zero the working space before returning, which needs the
postconditions to read the memory on return only within the functions'
buffers (`expandKeyPostOut_local`, `ecbPostOut_local`, `ctrPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG.Spec.Sm4

/-- `vg_sm4_expand_key` with `scratch: *mut [u64; n]`. -/
def expandKeyScratchSig (n : Nat) : Sig where
  params := [("key", .array false .u8 16), ("schedule", .array true .u8 128),
    ("scratch", .array true .u64 n)]

/-- `expandKeyContract`'s postcondition. -/
def expandKeyPost (pb : Nat) : expandKeySig.Post pb := fun key schedule m m' _ =>
  scheduleAt m' schedule = expandKey (blockAt m key)

/-- `expandKeyContract`, whatever `scratch` is. -/
def expandKeyScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (expandKeyScratchSig n).contract A
    (post := fun key schedule _scratch => expandKeyPost A.ptrBits key schedule)
    (stack := stack)

/-- The ECB functions with `scratch: *mut [u64; n]`. -/
def ecbScratchSig (n : Nat) : Sig where
  params := [("schedule", .array false .u8 128), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 n)]

/-- `ecbContract`, whatever `scratch` is. -/
def ecbScratchContract {M : ISA} (A : Abi M) (direction : Direction) (n : Nat) (stack : Nat := 0) :
    Contract M :=
  (ecbScratchSig n).contract A
    (post := fun schedule data len _scratch => ecbPost direction A.ptrBits schedule data len)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_ctr` with `scratch: *mut [u64; n]`. -/
def ctrScratchSig (n : Nat) : Sig where
  params := [("schedule", .array false .u8 128), ("ctr", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n"), ("scratch", .array true .u64 n)]

/-- `ctrContract`'s postcondition. -/
def ctrPost (pb : Nat) : ctrSig.Post pb := fun schedule ctr data n m m' _ =>
  Spec.Cbc.blocksAt m' data n.toNat =
      Spec.Ctr.crypt (cipher (scheduleAt m schedule)) (Spec.Aes.bytesAt m ctr 16) (Spec.Cbc.blocksAt m data n.toNat) ∧
    Spec.Aes.bytesAt m' ctr 16 = Spec.Ctr.next (Spec.Aes.bytesAt m ctr 16) n.toNat

/-- `ctrContract`, whatever `scratch` is. -/
def ctrScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ctrScratchSig n).contract A
    (post := fun schedule ctr data len _scratch => ctrPost A.ptrBits schedule ctr data len)
    (writeArgs := true) (stack := stack)

/-- `ecbDirContract`'s precondition. -/
def ecbDirPre (pb : Nat) : Curry (ecbDirSig.words pb) (Mem → Prop) :=
  fun _schedule _data _n decrypt _ => decrypt.toNat ≤ 1

/-- `ecbDirContract`'s postcondition. -/
def ecbDirPost (pb : Nat) : ecbDirSig.Post pb := fun schedule data n decrypt m m' _ =>
  blocksAt m' data n.toNat = ecb (scheduleAt m schedule) (directionOf decrypt.toNat) (blocksAt m data n.toNat)

/-- `vg_sm4_ecb` with `scratch: *mut [u64; n]`. -/
def ecbDirScratchSig (n : Nat) : Sig where
  params := [("schedule", .array false .u8 128), ("data", .slice true (.array .u8 16) "n"),
    ("decrypt", .int .usize true), ("scratch", .array true .u64 n)]

/-- `ecbDirContract`, whatever `scratch` is. -/
def ecbDirScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ecbDirScratchSig n).contract A
    (pre := fun schedule data len decrypt _scratch => ecbDirPre A.ptrBits schedule data len decrypt)
    (post := fun schedule data len decrypt _scratch => ecbDirPost A.ptrBits schedule data len decrypt)
    (writeArgs := true) (stack := stack)

theorem ecbDirContract_eq {M : ISA} (A : Abi M) (stack : Nat) :
    ecbDirContract A stack = ecbDirSig.contract A (ecbDirPre A.ptrBits) (ecbDirPost A.ptrBits) true stack := rfl

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, b, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact foldl_congr l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

private theorem scheduleAt_congr
    (h : ∀ i < 128, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    scheduleAt m₂ p = scheduleAt m₁ p := by
  simp only [scheduleAt]
  congr 1
  funext i
  refine foldl_congr _ _ fun j hj out => ?_
  rw [h _ (by have := i.isLt; have := List.mem_range.mp hj; omega_arith)]

private theorem blocksAt_congr {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt, blockAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  congr 1
  funext j
  have : 16 * i + j.val < n * 16 := by have := j.isLt; omega_arith
  rw [Offset.add_add]
  exact h _ this

private theorem blockAt_congr (h : ∀ i < 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blockAt m₂ p = blockAt m₁ p := by
  simp only [blockAt]
  congr 1
  funext j
  exact h _ j.isLt

private theorem bytesAt_congr {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => bytesAt_congr fun j hj => ?_
  have := List.mem_range.mp hi
  rw [Offset.add_add]
  exact h _ (by omega_arith)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

end

/-- The schedule, in memory changed only outside it. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) : scheduleAt m' p = scheduleAt m p :=
  scheduleAt_congr fun _ hi => hf.bytes (R := ⟨p, 128⟩) hd (show 128 ≤ 2 ^ 64 by decide) hi

/-- The blocks, in memory changed only outside them. -/
theorem blocksAt_frame {rs : List Region} {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n * 16⟩ r) (hfit : n * 16 ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n :=
  blocksAt_congr fun _ hi => hf.bytes (R := ⟨p, n * 16⟩) hd hfit hi

variable (pb : Nat)

theorem expandKeyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₁ r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.addr] (expandKeyPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr] (expandKeyPost pb) _ m m₂ r
  dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h ⊢
  rw [scheduleAt_congr hs]
  exact h

theorem ecbPostOut_local (direction : Direction) : ∀ vs m m₁ m₂ r,
    vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m m₁ r →
      Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost direction pb) _
    m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost direction pb) _
    m m₂ r
  dsimp only [Curry.apply, ecbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega_arith)]
  exact h

theorem ctrPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ctrSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrSig.words pb) (ctrPost pb) vs m m₁ r →
      Curry.apply (ctrSig.words pb) (ctrPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ctr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctrPost pb) _
    m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctrPost pb) _
    m m₂ r
  dsimp only [Curry.apply, ctrPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega_arith), bytesAt_congr hc]
  exact h

theorem ecbDirPostOut_local : ∀ vs m m₁ m₂ r,
    vs.length = (ecbDirSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbDirSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbDirSig.words pb) (ecbDirPost pb) vs m m₁ r →
      Curry.apply (ecbDirSig.words pb) (ecbDirPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ecbDirSig, ecbSig, List.cons_append, List.nil_append, Sig.bufs, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hd := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.int pb] (ecbDirPost pb) _
    m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.int pb] (ecbDirPost pb) _
    m m₂ r
  dsimp only [Curry.apply, ecbDirPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega_arith)]
  exact h

/-- `ecbDirPre` reads no memory. -/
theorem ecbDirPre_local : ∀ vs m₁ m₂, vs.length = (ecbDirSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbDirSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbDirSig.words pb) (ecbDirPre pb) vs m₁ → Curry.apply (ecbDirSig.words pb) (ecbDirPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- `ecbDirPost` reads the memory on entry only within the schedule and the data. -/
theorem ecbDirPost_local : ∀ vs m₁ m₂ m' r,
    vs.length = (ecbDirSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbDirSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbDirSig.words pb) (ecbDirPost pb) vs m₁ m' r →
      Curry.apply (ecbDirSig.words pb) (ecbDirPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ecbDirSig, ecbSig, List.cons_append, List.nil_append, Sig.bufs, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hd := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.int pb] (ecbDirPost pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.int pb] (ecbDirPost pb) _
    m₂ m' r
  dsimp only [Curry.apply, ecbDirPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega_arith)]
  exact h

/-- `expandKeyPost` reads the memory on entry only within the key. -/
theorem expandKeyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₁ m' r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hk := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.addr] (expandKeyPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr] (expandKeyPost pb) _ m₂ m' r
  dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h ⊢
  rw [blockAt_congr hk]
  exact h

/-- `ecbPost` reads the memory on entry only within the schedule and the data. -/
theorem ecbPost_local (direction : Direction) : ∀ vs m₁ m₂ m' r,
    vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m₁ m' r →
      Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hd := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost direction pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ecbPost direction pb) _
    m₂ m' r
  dsimp only [Curry.apply, ecbPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, blocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega_arith)]
  exact h

theorem ctrPost_local : ∀ vs m₁ m₂ m' r, vs.length = (ctrSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrSig.words pb) (ctrPost pb) vs m₁ m' r → Curry.apply (ctrSig.words pb) (ctrPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  have hv := agree_of hb.2.1
  have hd := agree_of hb.2.2
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctrPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (ctrPost pb) _ m₂ m' r
  dsimp only [Curry.apply, ctrPost, ArgWord.ofRaw] at h ⊢
  have := Nat.mod_le n.toNat (2 ^ pb)
  rw [scheduleAt_congr hs, bytesAt_congr hv, cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
    rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega_arith)]
  exact h

end VG.Proof.Sm4
