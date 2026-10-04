import VerifiedGarbage.Proof.Framework.Scratch

/-!
# Contracts with a tag and with working space in its place

A function one of whose parameters (number `q`) is a 16-byte tag, read or
written, can run code written for a function whose parameter there is a
buffer of working space that carries the tag in its first 16 bytes
(`Sig.tagWork`): each target's `TagScratch.lean` allocates the buffer in a
frame of its own, copies the tag into it before the code and back after it,
and passes the buffer in the tag's place.

The code's contract (`preI`, `postI`, `leakI`) is related to the function's
(`preO`, `postO`, `leakO`) by `Sig.TagFrame`, on the values of the arguments
before the tag (`vs₁`) and after it (`vs₂`), the tag's address `t` and the
buffer's `W`: on entry, the code's memory agrees with the function's on the
other buffers and holds the tag's 16 bytes at `W` (`TagIn`); on return, the
function's memory is the code's but for the tag, which holds the buffer's
first 16 bytes (`TagOut`), and the other buffers are separate from the tag.
Both may assume the function's precondition on entry.
-/

namespace VG

/-- `sig` with parameter `q` replaced by a writable array of `n` elements
`e`, named `nm`. -/
def Sig.tagWork (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n : Nat) : Sig :=
  { sig with params := sig.params.set q (nm, .array true e n) }

/-- The argument words of the parameters `ps`. -/
abbrev Sig.psWords (ps : List (String × Param)) (pb : Nat) : List ArgWord :=
  ps.flatMap fun p => p.2.words pb

/-- On entry: the code's memory `m₂` agrees with the function's `m₁` on the
other buffers `B`, and holds the tag's 16 bytes (at `t`) at `W`. -/
def TagIn (B : List (Region × Bool)) (t W : Addr) (m₁ m₂ : Mem) : Prop :=
  (∀ b ∈ B, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) ∧
    ∀ i < 16, m₂ (W + BitVec.ofNat 64 i) = m₁ (t + BitVec.ofNat 64 i)

/-- On return: the function's memory `m'` is the code's `m₃` but for the
tag's 16 bytes (at `t`), which hold the 16 bytes at `W`. -/
def TagOut (t W : Addr) (m₃ m' : Mem) : Prop :=
  (∀ a, ¬ (⟨t, 16⟩ : Region).Contains a 1 → m' a = m₃ a) ∧
    ∀ i < 16, m' (t + BitVec.ofNat 64 i) = m₃ (W + BitVec.ofNat 64 i)

/-- The function's contract (`preO`, `postO`, `leakO`) follows from the code's
(`preI`, `postI`, `leakI`), whose parameter `q` is the working space that
carries the tag (`Sig.tagWork`): see the module documentation. -/
structure Sig.TagFrame (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n : Nat) (pb : Nat)
    (preO : Curry (sig.words pb) (Mem → Prop)) (postO : sig.Post pb)
    (leakO : Option (Curry (sig.words pb) (Mem → List Nat)))
    (preI : Curry ((sig.tagWork q nm e n).words pb) (Mem → Prop))
    (postI : (sig.tagWork q nm e n).Post pb)
    (leakI : Option (Curry ((sig.tagWork q nm e n).words pb) (Mem → List Nat))) : Prop where
  pre : ∀ vs₁ vs₂ t W m₁ m₂, vs₁.length = (Sig.psWords (sig.params.take q) pb).length →
    vs₂.length = (Sig.psWords (sig.params.drop (q + 1)) pb).length →
    TagIn (Sig.bufs (sig.params.take q) vs₁ ++ Sig.bufs (sig.params.drop (q + 1)) vs₂) t W m₁ m₂ →
    Curry.apply _ preO (vs₁ ++ t :: vs₂) m₁ → Curry.apply _ preI (vs₁ ++ W :: vs₂) m₂
  post : ∀ vs₁ vs₂ t W m₁ m₂ m₃ m' r, vs₁.length = (Sig.psWords (sig.params.take q) pb).length →
    vs₂.length = (Sig.psWords (sig.params.drop (q + 1)) pb).length →
    TagIn (Sig.bufs (sig.params.take q) vs₁ ++ Sig.bufs (sig.params.drop (q + 1)) vs₂) t W m₁ m₂ →
    Curry.apply _ preO (vs₁ ++ t :: vs₂) m₁ →
    (∀ b ∈ Sig.bufs (sig.params.take q) vs₁ ++ Sig.bufs (sig.params.drop (q + 1)) vs₂,
      b.1.Disjoint ⟨t, 16⟩) →
    TagOut t W m₃ m' →
    Curry.apply _ postI (vs₁ ++ W :: vs₂) m₂ m₃ r → Curry.apply _ postO (vs₁ ++ t :: vs₂) m₁ m' r
  leak : match leakO, leakI with
    | none, none => True
    | some f, some g => ∀ vs₁ vs₂ t W m₁ m₂,
      vs₁.length = (Sig.psWords (sig.params.take q) pb).length →
      vs₂.length = (Sig.psWords (sig.params.drop (q + 1)) pb).length →
      TagIn (Sig.bufs (sig.params.take q) vs₁ ++ Sig.bufs (sig.params.drop (q + 1)) vs₂) t W m₁ m₂ →
      Curry.apply _ preO (vs₁ ++ t :: vs₂) m₁ →
      Curry.apply _ g (vs₁ ++ W :: vs₂) m₂ = Curry.apply _ f (vs₁ ++ t :: vs₂) m₁
    | _, _ => False

/-! ## Signatures -/

/-- The buffers of two lists of parameters, given values for the first's
words and the second's. -/
theorem Sig.bufs_append (pb : Nat) :
    ∀ (ps₁ ps₂ : List (String × Param)) (vs₁ vs₂ : List (BitVec 64)),
      vs₁.length = (Sig.psWords ps₁ pb).length →
      Sig.bufs (ps₁ ++ ps₂) (vs₁ ++ vs₂) = Sig.bufs ps₁ vs₁ ++ Sig.bufs ps₂ vs₂
  | [], _, [], _, _ => rfl
  | (_, .int ..) :: ps, ps₂, v :: vs, vs₂, h => by
    simp only [Sig.psWords, List.flatMap_cons, Param.words.eq_1, List.length_append,
      List.length_cons, List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append pb ps ps₂ vs vs₂ (by simp only [Sig.psWords]; omega)
  | (_, .array ..) :: ps, ps₂, v :: vs, vs₂, h => by
    simp only [Sig.psWords, List.flatMap_cons, Param.words.eq_2, List.length_append,
      List.length_cons, List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append pb ps ps₂ vs vs₂ (by simp only [Sig.psWords]; omega)]
  | (_, .slice ..) :: ps, ps₂, v :: l :: vs, vs₂, h => by
    simp only [Sig.psWords, List.flatMap_cons, Param.words.eq_3, List.length_append,
      List.length_cons, List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append pb ps ps₂ vs vs₂ (by simp only [Sig.psWords]; omega)]
  | (_, .slices ..) :: ps, ps₂, v :: l :: vs, vs₂, h => by
    simp only [Sig.psWords, List.flatMap_cons, Param.words.eq_4, List.length_append,
      List.length_cons, List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append pb ps ps₂ vs vs₂ (by simp only [Sig.psWords]; omega)
  | [], _, _ :: _, _, h => by simp at h
  | (_, .int ..) :: _, _, [], _, h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, _, [], _, h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, _, [], _, h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, _, [_], _, h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, _, [], _, h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, _, [_], _, h => by simp [Param.words.eq_4] at h

/-- The buffers of parameters with an array of `n` elements `e` (at `x`)
between two lists of them. -/
theorem Sig.bufs_middle (pb : Nat) (ps₁ ps₂ : List (String × Param)) (nm : String) (w : Bool)
    (e : Elem) (n : Nat) (vs₁ vs₂ : List (BitVec 64)) (x : BitVec 64)
    (h : vs₁.length = (Sig.psWords ps₁ pb).length) :
    Sig.bufs (ps₁ ++ (nm, .array w e n) :: ps₂) (vs₁ ++ x :: vs₂) =
      Sig.bufs ps₁ vs₁ ++ (⟨x, n * e.size⟩, w) :: Sig.bufs ps₂ vs₂ := by
  rw [Sig.bufs_append pb _ _ _ _ h]
  rfl

/-- The parameters of `sig`, around parameter `q`, `p`. -/
theorem Sig.params_split {sig : Sig} {q : Nat} {p : String × Param} (hq : sig.params[q]? = some p) :
    sig.params = sig.params.take q ++ p :: sig.params.drop (q + 1) := by
  obtain ⟨hl, hp⟩ := List.getElem?_eq_some_iff.mp hq
  rw [← hp, List.getElem_cons_drop hl, List.take_append_drop]

theorem Sig.tagWork_params {sig : Sig} {q : Nat} {p : String × Param} (nm : String) (e : Elem)
    (n : Nat) (hq : sig.params[q]? = some p) :
    (sig.tagWork q nm e n).params =
      sig.params.take q ++ (nm, .array true e n) :: sig.params.drop (q + 1) := by
  have hl := (List.getElem?_eq_some_iff.mp hq).1
  simp only [Sig.tagWork, List.set_eq_take_append_cons_drop, hl, ite_true]

section
variable {sig : Sig} {q : Nat} {nmT : String} {wT : Bool} {eT : Elem} {nT : Nat}
  (nm : String) (e : Elem) (n : Nat) (pb : Nat)

/-- The words of `sig`, around its array parameter `q`. -/
theorem Sig.words_split (hq : sig.params[q]? = some (nmT, .array wT eT nT)) :
    sig.words pb =
      Sig.psWords (sig.params.take q) pb ++ .addr :: Sig.psWords (sig.params.drop (q + 1)) pb := by
  show sig.params.flatMap _ = _
  conv => lhs; rw [Sig.params_split hq]
  rw [List.flatMap_append, List.flatMap_cons]
  rfl

theorem Sig.words_tagWork (hq : sig.params[q]? = some (nmT, .array wT eT nT)) :
    (sig.tagWork q nm e n).words pb = sig.words pb := by
  rw [Sig.words_split pb hq, Sig.words, Sig.tagWork_params nm e n hq, List.flatMap_append,
    List.flatMap_cons]
  rfl

theorem Sig.noLists_tagWork (hq : sig.params[q]? = some (nmT, .array wT eT nT))
    (hl : Sig.noLists sig.params = true) : Sig.noLists (sig.tagWork q nm e n).params = true := by
  rw [Sig.params_split hq] at hl
  rw [Sig.tagWork_params nm e n hq]
  simp only [Sig.noLists, List.all_append, List.all_cons, Bool.and_eq_true] at hl ⊢
  exact ⟨hl.1, trivial, hl.2.2⟩

theorem Sig.pubs_tagWork (hq : sig.params[q]? = some (nmT, .array wT eT nT)) :
    (sig.tagWork q nm e n).params.flatMap (·.2.pubs) = sig.params.flatMap (·.2.pubs) := by
  rw [Sig.tagWork_params nm e n hq]
  conv => rhs; rw [Sig.params_split hq]
  simp only [List.flatMap_append, List.flatMap_cons]
  rfl

/-- The buffers of `sig`, for arguments around its array parameter `q`. -/
theorem Sig.bufs_split (hq : sig.params[q]? = some (nmT, .array wT eT nT)) (vs₁ vs₂ : List (BitVec 64))
    (x : BitVec 64) (h : vs₁.length = (Sig.psWords (sig.params.take q) pb).length) :
    Sig.bufs sig.params (vs₁ ++ x :: vs₂) =
      Sig.bufs (sig.params.take q) vs₁ ++ (⟨x, nT * eT.size⟩, wT) ::
        Sig.bufs (sig.params.drop (q + 1)) vs₂ := by
  conv => lhs; rw [Sig.params_split hq]
  exact Sig.bufs_middle pb _ _ _ _ _ _ _ _ _ h

theorem Sig.bufs_tagWork (hq : sig.params[q]? = some (nmT, .array wT eT nT))
    (vs₁ vs₂ : List (BitVec 64)) (x : BitVec 64)
    (h : vs₁.length = (Sig.psWords (sig.params.take q) pb).length) :
    Sig.bufs (sig.tagWork q nm e n).params (vs₁ ++ x :: vs₂) =
      Sig.bufs (sig.params.take q) vs₁ ++ (⟨x, n * e.size⟩, true) ::
        Sig.bufs (sig.params.drop (q + 1)) vs₂ := by
  rw [Sig.tagWork_params nm e n hq]
  exact Sig.bufs_middle pb _ _ _ _ _ _ _ _ _ h

end

/-- A list of values, around its value `k`. -/
theorem List.split_at {vs : List (BitVec 64)} {k : Nat} (h : k < vs.length) :
    vs = vs.take k ++ vs.getD k 0 :: vs.drop (k + 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some,
    List.getElem_cons_drop h, List.take_append_drop]

end VG
