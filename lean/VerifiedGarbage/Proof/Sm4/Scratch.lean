import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4 key expansion and ECB with their working space as an argument

`vg_sm4_expand_key` and the ECB functions keep their working space in a
frame of their own (`Verified.stackScratchWiped`), around code proved with
the working space as an argument: `expandKeyScratchContract n` and
`ecbScratchContract n` are the shared contracts with a `scratch` buffer of
`n` words appended, whatever it holds (each target lays out its own).

The frames zero the working space before returning, which needs the
postconditions to read the memory on return only within the functions'
buffers (`expandKeyPostOut_local`, `ecbPostOut_local`).
-/

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
  rw [h _ (by have := i.isLt; have := List.mem_range.mp hj; omega)]

private theorem blocksAt_congr {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt, blockAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  congr 1
  funext j
  have : 16 * i + j.val < n * 16 := by have := j.isLt; omega
  rw [Offset.add_add]
  exact h _ this

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

end

variable (pb : Nat)

theorem expandKeyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₁ r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₂ r
  | [_, sch], m, m₁, m₂, r, _, hb, h => by
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
      Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m m₂ r
  | [_, data, n], m, m₁, m₂, r, _, hb, h => by
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
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 16 this; omega)]
    exact h

end VG.Proof.Sm4
