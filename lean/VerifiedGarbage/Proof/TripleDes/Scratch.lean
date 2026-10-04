import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Triple DES key expansion and ECB with their working space as an argument

`vg_triple_des_expand_key` and the ECB functions keep their working space in
a frame of their own (`Verified.stackScratch`, `Verified.regScratch`), around
code proved with the working space as an argument: `expandKeyScratchContract`
and `ecbScratchContract` are the shared contracts with the `scratch` buffer
appended, whatever it holds.

On x86 the frame also holds a copy of the arguments passed on the stack,
which needs the postconditions to read the memory on entry only within the
function's buffers (`expandKeyPost_local`, `ecbPost_local`). The frames zero
the working space before returning, which needs them to read the memory on
return only within those buffers too (`expandKeyPostOut_local`,
`ecbPostOut_local`).
-/

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

/-- `vg_triple_des_expand_key` with `scratch: *mut [u64; 64]`. -/
def expandKeyScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 384),
    ("scratch", .array true .u64 64)]

/-- `expandKeyContract`, whatever `scratch` is. -/
def expandKeyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeyScratchSig.contract A
    (pre := fun key keyLen schedule _scratch => expandKeyPre A.ptrBits key keyLen schedule)
    (post := fun key keyLen schedule _scratch => expandKeyPost A.ptrBits key keyLen schedule)
    (stack := stack)

/-- The ECB functions with `scratch: *mut [u64; 128]`. -/
def ecbScratchSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .slice true (.array .u8 8) "n"),
    ("scratch", .array true .u64 128)]

/-- `ecbContract`, whatever `scratch` is. -/
def ecbScratchContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) :
    Contract M :=
  ecbScratchSig.contract A
    (post := fun schedule data n _scratch => ecbPost direction A.ptrBits schedule data n)
    (writeArgs := true) (stack := stack)

def ecbEncryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbScratchContract A .encrypt stack

def ecbDecryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbScratchContract A .decrypt stack

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

private theorem bytesAt_congr {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem scheduleAt_congr
    (h : ∀ i < 384, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    scheduleAt m₂ p = scheduleAt m₁ p := by
  simp only [scheduleAt]
  congr 1
  funext i
  refine foldl_congr _ _ fun j hj out => ?_
  rw [h _ (by have := i.isLt; have := List.mem_range.mp hj; omega)]

private theorem blocksAt_congr {n : Nat}
    (h : ∀ i < n * 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt, blockAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  congr 1
  funext j
  have : 8 * i + j.val < n * 8 := by have := j.isLt; omega
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

theorem expandKeyPre_local : ∀ vs m₁ m₂, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPre pb) vs m₁ →
      Curry.apply (expandKeySig.words pb) (expandKeyPre pb) vs m₂
  | [_, _, _], _, _, _, _, h => h

theorem expandKeyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₁ m' r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m₂ m' r
  | [key, kl, _], m₁, m₂, m', r, _, hb, h => by
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m₂ m' r
    dsimp only [Curry.apply, expandKeyPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem ecbPost_local (direction : Direction) : ∀ vs m₁ m₂ m' r,
    vs.length = (ecbSig.words pb).length →
    (∀ b ∈ Sig.bufs ecbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m₁ m' r →
      Curry.apply (ecbSig.words pb) (ecbPost direction pb) vs m₂ m' r
  | [sch, data, n], m₁, m₂, m', r, _, hb, h => by
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
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 8 this; omega)]
    exact h

theorem expandKeyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (expandKeySig.words pb).length →
    (∀ b ∈ Sig.bufs expandKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₁ r →
      Curry.apply (expandKeySig.words pb) (expandKeyPost pb) vs m m₂ r
  | [_, _, sch], m, m₁, m₂, r, _, hb, h => by
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (expandKeyPost pb) _ m m₂ r
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
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mul_le_mul_right 8 this; omega)]
    exact h

end VG.Proof.TripleDes
