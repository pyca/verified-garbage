import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Contracts with and without a scratch buffer argument

A function whose last argument was a scratch buffer, working space its
contract says nothing of, can instead take the buffer from its own stack
frame (`Impl/StackScratch/`). Its contract without the argument,
`sig.contract A pre post …`, then follows from the one with it
(`Sig.scratchContract`): the same `pre` and `post`, which ignore the buffer
(`Curry.withScratch`), on the signature with one more, last, parameter
(`Sig.withScratch`). Each target's `StackScratch.lean` proves the step.

A contract may also declare a leak (`Sig.contract`'s `leak`), which the code's
contract takes too, ignoring the buffer. Where the frame copies arguments into
memory, the leak must read memory only within the function's buffers
(`Sig.LeakLocal`, which holds of no leak), as the precondition and
postcondition must; the two runs then agree on the code's leak if they agree
on the function's (`leakAgree_withScratch`). Where the frame only passes the
buffer in a register, the code reads the same memory as the function, and no
locality is needed (`leakAgree_withScratch_same`).

A list of slices (`Param.slices`) is memory `Sig.contract` reads from the
memory on entry: its descriptors and the slices they list (`Sig.lists`).
Memories that agree on the descriptors list the same slices
(`Sig.lists_congr`), so a frame that writes outside the lists keeps them; a
frame that copies arguments then needs the contract to read memory only
within the buffers and the lists (`Sig.Local`, `Sig.LeakLocalL`).
-/

namespace VG

/-- `sig` with one more parameter, last: a writable array of `n` elements `e`. -/
def Sig.withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) : Sig :=
  { sig with params := sig.params ++ [(nm, .array true e n)] }

/-- `f`, its arguments after the first `a` taken through `g`. -/
def Curry.app {α : Type} {b b' : List ArgWord} (g : Curry b α → Curry b' α) :
    (a : List ArgWord) → Curry (a ++ b) α → Curry (a ++ b') α
  | [], f => g f
  | _ :: a, f => fun x => Curry.app g a (f x)

/-- `f` applied to the values `vs` of its first arguments `a`. -/
def Curry.part {α : Type} {b : List ArgWord} :
    (a : List ArgWord) → Curry (a ++ b) α → List (BitVec 64) → Curry b α
  | [], f, _ => f
  | w :: a, f, v :: vs => Curry.part a (f (w.ofRaw v)) vs
  | w :: a, f, [] => Curry.part a (f (w.ofRaw 0)) []

theorem Curry.apply_append {α : Type} {b : List ArgWord} :
    ∀ (a : List ArgWord) (f : Curry (a ++ b) α) (us vs : List (BitVec 64)), us.length = a.length →
      Curry.apply (a ++ b) f (us ++ vs) = Curry.apply b (Curry.part a f us) vs
  | [], _, [], _, _ => rfl
  | _ :: a, f, u :: us, vs, h => Curry.apply_append a _ us vs (by simpa using h)

theorem Curry.part_app {α : Type} {b b' : List ArgWord} (g : Curry b α → Curry b' α) :
    ∀ (a : List ArgWord) (f : Curry (a ++ b) α) (us : List (BitVec 64)), us.length = a.length →
      Curry.part a (Curry.app g a f) us = g (Curry.part a f us)
  | [], _, [], _ => rfl
  | _ :: a, f, u :: us, h => Curry.part_app g a _ us (by simpa using h)

/-- `f`, taking one more argument, a pointer, last, which it ignores. -/
def Curry.withScratch {α : Type} (pb : Nat) (nm : String) (e : Elem) (n : Nat) :
    (ps : List (String × Param)) → Curry (ps.flatMap fun p => p.2.words pb) α →
      Curry ((ps ++ [((nm, .array true e n) : String × Param)]).flatMap fun p => p.2.words pb) α
  | [], f => fun _ => f
  | p :: ps, f => Curry.app (Curry.withScratch pb nm e n ps) (p.2.words pb) f

theorem Curry.apply_withScratch {α : Type} (pb : Nat) (nm : String) (e : Elem) (n : Nat) :
    ∀ (ps : List (String × Param)) (f : Curry (ps.flatMap fun p => p.2.words pb) α)
      (vs : List (BitVec 64)) (x : BitVec 64), vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Curry.apply _ (Curry.withScratch pb nm e n ps f) (vs ++ [x]) = Curry.apply _ f vs
  | [], _, [], _, _ => rfl
  | p :: ps, f, vs, x, h => by
    rw [List.flatMap_cons, List.length_append] at h
    have hl : (vs.take (p.2.words pb).length).length = (p.2.words pb).length := by
      rw [List.length_take]; omega
    have hr : (vs.drop (p.2.words pb).length).length = (ps.flatMap fun p => p.2.words pb).length := by
      rw [List.length_drop]; omega
    rw [← List.take_append_drop (p.2.words pb).length vs, List.append_assoc]
    show Curry.apply (p.2.words pb ++ _) (Curry.app _ (p.2.words pb) f) _ =
      Curry.apply (p.2.words pb ++ _) f _
    rw [Curry.apply_append _ _ _ _ hl, Curry.apply_append _ _ _ _ hl, Curry.part_app _ _ _ _ hl]
    exact Curry.apply_withScratch pb nm e n ps _ _ x hr

/-- The contract of a function whose last argument is a scratch buffer of
`n` elements `e`, working space that `pre`, `post` and `leak` ignore: the
contract that `sig.contract A pre post writeArgs stack leak` follows from, for
a function that allocates the buffer itself. -/
def Sig.scratchContract {M : ISA} (A : Abi M) (sig : Sig) (nm : String) (e : Elem) (n : Nat)
    (pre : Curry (sig.words A.ptrBits) (Mem → Prop)) (post : sig.Post A.ptrBits)
    (writeArgs : Bool) (stack : Nat)
    (leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat)) := none) : Contract M :=
  (sig.withScratch nm e n).contract A (Curry.withScratch A.ptrBits nm e n sig.params pre)
    (Curry.withScratch A.ptrBits nm e n sig.params post) writeArgs stack
    (leak.map (Curry.withScratch A.ptrBits nm e n sig.params))

theorem Sig.words_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) (pb : Nat) :
    (sig.withScratch nm e n).words pb = sig.words pb ++ ([.addr] : List ArgWord) := by
  simp [Sig.withScratch, Sig.words, Param.words]

theorem Param.pubs_length (p : Param) (pb : Nat) : p.pubs.length = (p.words pb).length := by
  cases p <;> rfl

theorem Sig.pubs_length (ps : List (String × Param)) (pb : Nat) :
    (ps.flatMap (·.2.pubs)).length = (ps.flatMap fun p => p.2.words pb).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.flatMap_cons, ih, Param.pubs_length p.2 pb]

/-- The buffers of the parameters followed by one more array, given values
for the others and its address `x`. -/
theorem Sig.bufs_append_array (pb : Nat) (nm : String) (e : Elem) (n : Nat) (x : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.bufs (ps ++ [((nm, .array true e n) : String × Param)]) (vs ++ [x]) =
        Sig.bufs ps vs ++ [(⟨x, n * e.size⟩, true)]
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_array pb nm e n x ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_array pb nm e n x ps vs (by omega)]
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_array pb nm e n x ps vs (by omega)]
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_array pb nm e n x ps vs (by omega)
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h

/-- The lists of slices of the parameters followed by one more array: those
of the others. -/
theorem Sig.lists_append_array (pb : Nat) (m : Mem) (nm : String) (e : Elem) (n : Nat) (x : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.lists pb m (ps ++ [((nm, .array true e n) : String × Param)]) (vs ++ [x]) = Sig.lists pb m ps vs
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    exact Sig.lists_append_array pb m nm e n x ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    exact Sig.lists_append_array pb m nm e n x ps vs (by omega)
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    exact Sig.lists_append_array pb m nm e n x ps vs (by omega)
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    rw [Sig.lists_append_array pb m nm e n x ps vs (by omega)]
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h

/-- The descriptors of the parameters followed by one more array: those of
the others. -/
theorem Sig.descs_append_array (pb : Nat) (nm : String) (e : Elem) (n : Nat) (x : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.descs pb (ps ++ [((nm, .array true e n) : String × Param)]) (vs ++ [x]) = Sig.descs pb ps vs
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    exact Sig.descs_append_array pb nm e n x ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    exact Sig.descs_append_array pb nm e n x ps vs (by omega)
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    exact Sig.descs_append_array pb nm e n x ps vs (by omega)
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    rw [Sig.descs_append_array pb nm e n x ps vs (by omega)]
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h

/-! ## Lists of slices -/

theorem filter_fun_false {α : Type} (l : List α) : l.filter (fun _ => false) = [] :=
  List.filter_eq_nil_iff.mpr (by simp)

/-- A byte at an offset below `k` lies in `k` bytes. -/
theorem Region.contains_ofNat (p : Addr) {d k : Nat} (h : d < k) :
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) 1 := by
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le d (2 ^ 64)
  omega

/-- The slices the descriptors list depend only on the descriptors. -/
theorem Sig.listed_congr (pb : Nat) {m₁ m₂ : Mem} (e : Elem) (p : Addr) (n : Nat)
    (h : ∀ a, (Sig.descRegion pb p n).Contains a 1 → m₁ a = m₂ a) :
    Sig.listed pb m₁ e p n = Sig.listed pb m₂ e p n := by
  simp only [Sig.listed]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hw : (i + 1) * (2 * (pb / 8)) ≤ n * (2 * (pb / 8)) := Nat.mul_le_mul_right _ hi
  have hs : (i + 1) * (2 * (pb / 8)) = i * (2 * (pb / 8)) + 2 * (pb / 8) := Nat.succ_mul _ _
  have hrd : ∀ d, d + pb / 8 ≤ (i + 1) * (2 * (pb / 8)) →
      m₁.readW (p + BitVec.ofNat 64 d) pb = m₂.readW (p + BitVec.ofNat 64 d) pb := fun d hd => by
    simp only [Mem.readW]
    congr 1
    refine Mem.read_congr fun j hj => ?_
    rw [Offset.add_add]
    refine h _ (Region.contains_ofNat p ?_)
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hd hw)
  have e₁ := hrd (i * (2 * (pb / 8))) (by omega)
  have e₂ := hrd (i * (2 * (pb / 8)) + pb / 8) (by omega)
  rw [← Offset.add_add] at e₂
  simp only [e₁, e₂]

/-- The descriptors of the lists of slices are among the memory they take. -/
theorem Sig.descs_sub_lists (pb : Nat) (m : Mem) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)), ∀ r ∈ Sig.descs pb ps vs,
      r ∈ Sig.lists pb m ps vs
  | [], _, _, h => by simp [Sig.descs] at h
  | (_, .int ..) :: ps, _ :: vs, r, h => Sig.descs_sub_lists pb m ps vs r h
  | (_, .array ..) :: ps, _ :: vs, r, h => Sig.descs_sub_lists pb m ps vs r h
  | (_, .slice ..) :: ps, _ :: _ :: vs, r, h => Sig.descs_sub_lists pb m ps vs r h
  | (_, .slices ..) :: ps, _ :: _ :: vs, r, h => by
    simp only [Sig.descs, List.mem_cons] at h
    simp only [Sig.lists, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Sig.descs_sub_lists pb m ps vs r h)
  | (_, .int ..) :: _, [], _, h => by simp [Sig.descs] at h
  | (_, .array ..) :: _, [], _, h => by simp [Sig.descs] at h
  | (_, .slice ..) :: _, [], _, h => by simp [Sig.descs] at h
  | (_, .slice ..) :: _, [_], _, h => by simp [Sig.descs] at h
  | (_, .slices ..) :: _, [], _, h => by simp [Sig.descs] at h
  | (_, .slices ..) :: _, [_], _, h => by simp [Sig.descs] at h

/-- Memories that agree on the descriptors of the lists of slices list the
same slices. -/
theorem Sig.lists_congr (pb : Nat) {m₁ m₂ : Mem} :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      (∀ r ∈ Sig.descs pb ps vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Sig.lists pb m₁ ps vs = Sig.lists pb m₂ ps vs
  | [], _, _ => rfl
  | (_, .int ..) :: ps, _ :: vs, h => Sig.lists_congr pb ps vs h
  | (_, .array ..) :: ps, _ :: vs, h => Sig.lists_congr pb ps vs h
  | (_, .slice ..) :: ps, _ :: _ :: vs, h => Sig.lists_congr pb ps vs h
  | (_, .slices e _) :: ps, p :: n :: vs, h => by
    simp only [Sig.descs, List.mem_cons, forall_eq_or_imp] at h
    simp only [Sig.lists]
    rw [Sig.listed_congr pb e p n.toNat h.1, Sig.lists_congr pb ps vs h.2]
  | (_, .int ..) :: _, [], _ => rfl
  | (_, .array ..) :: _, [], _ => rfl
  | (_, .slice ..) :: _, [], _ => rfl
  | (_, .slice ..) :: _, [_], _ => rfl
  | (_, .slices ..) :: _, [], _ => rfl
  | (_, .slices ..) :: _, [_], _ => rfl

/-- Memories that agree on the lists of slices one of them takes list the
same slices: the other takes the same. -/
theorem Sig.lists_eq_of_agree (pb : Nat) {m₁ m₂ : Mem} {ps : List (String × Param)}
    {vs : List (BitVec 64)} (h : ∀ r ∈ Sig.lists pb m₁ ps vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) :
    Sig.lists pb m₁ ps vs = Sig.lists pb m₂ ps vs :=
  Sig.lists_congr pb ps vs fun r hr => h r (Sig.descs_sub_lists pb m₁ ps vs r hr)

/-- A precondition (or a postcondition, with the memory on exit `m'` and the
result `x` fixed) reads the memory on entry only within the buffers and the
lists of slices: memories that agree there give the same. -/
def Sig.Local (pb : Nat) (sig : Sig) {α : Type} (f : Curry (sig.words pb) (Mem → α)) : Prop :=
  ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
    (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂

/-- No parameter is a list of slices (`Param.slices`), whose memory
`Sig.contract` reads from the memory on entry: the frame of a stack scratch
buffer is proved only for signatures without one. -/
def Sig.noLists (ps : List (String × Param)) : Bool :=
  ps.all fun p => match p.2 with
    | .slices .. => false
    | _ => true

theorem Sig.lists_of_noLists (pb : Nat) (m : Mem) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)), Sig.noLists ps = true →
      Sig.lists pb m ps vs = []
  | [], _, _ => rfl
  | (_, .int ..) :: ps, _ :: vs, h => Sig.lists_of_noLists pb m ps vs (by simpa [Sig.noLists] using h)
  | (_, .array ..) :: ps, _ :: vs, h => Sig.lists_of_noLists pb m ps vs (by simpa [Sig.noLists] using h)
  | (_, .slice ..) :: ps, _ :: _ :: vs, h => Sig.lists_of_noLists pb m ps vs (by simpa [Sig.noLists] using h)
  | (_, .slices ..) :: _, _, h => by simp [Sig.noLists] at h
  | (_, .int ..) :: _, [], _ => rfl
  | (_, .array ..) :: _, [], _ => rfl
  | (_, .slice ..) :: _, [], _ => rfl
  | (_, .slice ..) :: _, [_], _ => rfl

theorem Sig.descs_of_noLists (pb : Nat) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)), Sig.noLists ps = true →
      Sig.descs pb ps vs = []
  | [], _, _ => rfl
  | (_, .int ..) :: ps, _ :: vs, h => Sig.descs_of_noLists pb ps vs (by simpa [Sig.noLists] using h)
  | (_, .array ..) :: ps, _ :: vs, h => Sig.descs_of_noLists pb ps vs (by simpa [Sig.noLists] using h)
  | (_, .slice ..) :: ps, _ :: _ :: vs, h => Sig.descs_of_noLists pb ps vs (by simpa [Sig.noLists] using h)
  | (_, .slices ..) :: _, _, h => by simp [Sig.noLists] at h
  | (_, .int ..) :: _, [], _ => rfl
  | (_, .array ..) :: _, [], _ => rfl
  | (_, .slice ..) :: _, [], _ => rfl
  | (_, .slice ..) :: _, [_], _ => rfl

theorem Sig.noLists_withScratch {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    (h : Sig.noLists sig.params = true) : Sig.noLists (sig.withScratch nm e n).params = true := by
  simpa [Sig.withScratch, Sig.noLists, List.all_append] using h

/-! ## Leaks -/

/-- What a contract's `leak` says of two runs, from their argument values and
memory: that they agree on it, and nothing if there is none (as in
`Sig.contract`'s `pub`). -/
def leakAgree {ws : List ArgWord} : Option (Curry ws (Mem → List Nat)) → List (BitVec 64) → Mem →
    List (BitVec 64) → Mem → Prop
  | none, _, _, _, _ => True
  | some f, vs₁, m₁, vs₂, m₂ => Curry.apply ws f vs₁ m₁ = Curry.apply ws f vs₂ m₂

/-- A contract's leak reads memory only within the function's buffers: two
memories that agree there give the same leak. No leak is local. -/
def Sig.LeakLocal (pb : Nat) (sig : Sig) : Option (Curry (sig.words pb) (Mem → List Nat)) → Prop
  | none => True
  | some f => ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂

/-- A contract's leak reads memory only within the function's buffers and its
lists of slices (`Sig.Local`). No leak is local. -/
def Sig.LeakLocalL (pb : Nat) (sig : Sig) : Option (Curry (sig.words pb) (Mem → List Nat)) → Prop
  | none => True
  | some f => Sig.Local pb sig f

/-- A leak local within the buffers is local within the buffers and the
lists. -/
theorem Sig.LeakLocal.toL {pb : Nat} {sig : Sig} {leak : Option (Curry (sig.words pb) (Mem → List Nat))}
    (h : Sig.LeakLocal pb sig leak) : Sig.LeakLocalL pb sig leak := by
  cases leak with
  | none => trivial
  | some f => exact fun vs m₁ m₂ hl hb _ => h vs m₁ m₂ hl hb

/-- `leakAgree_withScratch`, for a leak local within the buffers and the
lists. -/
theorem leakAgree_withScratchL {pb : Nat} {sig : Sig} {nm : String} {e : Elem} {n : Nat}
    {leak : Option (Curry (sig.words pb) (Mem → List Nat))} (hleak : Sig.LeakLocalL pb sig leak)
    {vs₁ vs₂ : List (BitVec 64)} {m₁ m₂ m₁' m₂' : Mem} (x₁ x₂ : BitVec 64)
    (l₁ : vs₁.length = (sig.words pb).length) (l₂ : vs₂.length = (sig.words pb).length)
    (a₁ : ∀ b ∈ Sig.bufs sig.params vs₁, ∀ a, b.1.Contains a 1 → m₁' a = m₁ a)
    (a₁' : ∀ r ∈ Sig.lists pb m₁' sig.params vs₁, ∀ a, r.Contains a 1 → m₁' a = m₁ a)
    (a₂ : ∀ b ∈ Sig.bufs sig.params vs₂, ∀ a, b.1.Contains a 1 → m₂' a = m₂ a)
    (a₂' : ∀ r ∈ Sig.lists pb m₂' sig.params vs₂, ∀ a, r.Contains a 1 → m₂' a = m₂ a)
    (h : leakAgree leak vs₁ m₁ vs₂ m₂) :
    leakAgree (ws := (sig.withScratch nm e n).words pb)
      (leak.map (Curry.withScratch pb nm e n sig.params)) (vs₁ ++ [x₁]) m₁' (vs₂ ++ [x₂]) m₂' := by
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs₁ ++ [x₁]) m₁' =
      Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs₂ ++ [x₂]) m₂'
    rw [Curry.apply_withScratch pb nm e n sig.params f vs₁ x₁ l₁,
      Curry.apply_withScratch pb nm e n sig.params f vs₂ x₂ l₂]
    exact (hleak vs₁ m₁' m₁ l₁ a₁ a₁').trans (h.trans (hleak vs₂ m₂' m₂ l₂ a₂ a₂').symm)

/-- Two runs that agree on a local leak agree on the leak of the contract with
the buffer (`Sig.scratchContract`), from any buffer addresses and memories
that agree with theirs within the function's buffers. -/
theorem leakAgree_withScratch {pb : Nat} {sig : Sig} {nm : String} {e : Elem} {n : Nat}
    {leak : Option (Curry (sig.words pb) (Mem → List Nat))} (hleak : Sig.LeakLocal pb sig leak)
    {vs₁ vs₂ : List (BitVec 64)} {m₁ m₂ m₁' m₂' : Mem} (x₁ x₂ : BitVec 64)
    (l₁ : vs₁.length = (sig.words pb).length) (l₂ : vs₂.length = (sig.words pb).length)
    (a₁ : ∀ b ∈ Sig.bufs sig.params vs₁, ∀ a, b.1.Contains a 1 → m₁' a = m₁ a)
    (a₂ : ∀ b ∈ Sig.bufs sig.params vs₂, ∀ a, b.1.Contains a 1 → m₂' a = m₂ a)
    (h : leakAgree leak vs₁ m₁ vs₂ m₂) :
    leakAgree (ws := (sig.withScratch nm e n).words pb)
      (leak.map (Curry.withScratch pb nm e n sig.params)) (vs₁ ++ [x₁]) m₁' (vs₂ ++ [x₂]) m₂' := by
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs₁ ++ [x₁]) m₁' =
      Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs₂ ++ [x₂]) m₂'
    rw [Curry.apply_withScratch pb nm e n sig.params f vs₁ x₁ l₁,
      Curry.apply_withScratch pb nm e n sig.params f vs₂ x₂ l₂]
    exact (hleak vs₁ m₁' m₁ l₁ a₁).trans (h.trans (hleak vs₂ m₂' m₂ l₂ a₂).symm)

/-- Two runs that agree on a leak agree on the leak of the contract with the
buffer (`Sig.scratchContract`), from any buffer addresses, in the same
memories. -/
theorem leakAgree_withScratch_same {pb : Nat} {sig : Sig} {nm : String} {e : Elem} {n : Nat}
    {leak : Option (Curry (sig.words pb) (Mem → List Nat))} {vs₁ vs₂ : List (BitVec 64)}
    {m₁ m₂ : Mem} (x₁ x₂ : BitVec 64)
    (l₁ : vs₁.length = (sig.words pb).length) (l₂ : vs₂.length = (sig.words pb).length)
    (h : leakAgree leak vs₁ m₁ vs₂ m₂) :
    leakAgree (ws := (sig.withScratch nm e n).words pb)
      (leak.map (Curry.withScratch pb nm e n sig.params)) (vs₁ ++ [x₁]) m₁ (vs₂ ++ [x₂]) m₂ := by
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs₁ ++ [x₁]) m₁ =
      Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs₂ ++ [x₂]) m₂
    rw [Curry.apply_withScratch pb nm e n sig.params f vs₁ x₁ l₁,
      Curry.apply_withScratch pb nm e n sig.params f vs₂ x₂ l₂]
    exact h

end VG
