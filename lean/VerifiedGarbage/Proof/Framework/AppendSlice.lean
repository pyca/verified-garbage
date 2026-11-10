module

public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Contracts with one more read-only slice argument

A function whose contract `k'` takes one more parameter than `k`, last, a
read-only slice its code never reads (`Sig.withSlice`), satisfies `k'` if it
satisfies `k` and `k'` asks no more of it: the buffers, lists and descriptors
of the signature are those of the shorter one and the slice
(`Sig.bufs_append_slice`, …). The RSA functions given a key's precomputed
values `pre`, which an implementation may ignore, are proven so from those
without them.
-/

@[expose] public section

namespace VG

/-- `sig` with one more parameter, last: a read-only slice of `e`. -/
def Sig.withSlice (sig : Sig) (nm : String) (e : Elem) (ln : String) : Sig :=
  { sig with params := sig.params ++ [(nm, .slice false e ln)] }

theorem Sig.words_withSlice (sig : Sig) (nm : String) (e : Elem) (ln : String) (pb : Nat) :
    (sig.withSlice nm e ln).words pb = sig.words pb ++ ([.addr, .int pb] : List ArgWord) := by
  simp [Sig.withSlice, Sig.words, Param.words]

/-- The buffers of the parameters followed by one more read-only slice, given values
for the others and its address `x`. -/
theorem Sig.bufs_append_slice (pb : Nat) (nm : String) (e : Elem) (ln : String) (x y : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.bufs (ps ++ [((nm, .slice false e ln) : String × Param)]) (vs ++ [x, y]) =
        Sig.bufs ps vs ++ [(⟨x, y.toNat * e.size⟩, false)]
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_slice pb nm e ln x y ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_slice pb nm e ln x y ps vs (by omega)]
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_slice pb nm e ln x y ps vs (by omega)]
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_slice pb nm e ln x y ps vs (by omega)
  | (_, .table _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_5, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_slice pb nm e ln x y ps vs (by omega)
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h
  | (_, .table _) :: _, [], h => by simp [Param.words.eq_5] at h

/-- The aligned buffers of the parameters followed by one more read-only slice, given
values for the others and its address `x`: `x` too, with its element's
alignment, if that is more than 1. -/
theorem Sig.alignedBufs_append_slice (pb : Nat) (nm : String) (e : Elem) (ln : String) (x y : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.alignedBufs (ps ++ [((nm, .slice false e ln) : String × Param)]) (vs ++ [x, y]) =
        Sig.alignedBufs ps vs ++ (if 1 < e.align then [(x, e.align)] else [])
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.alignedBufs]
    exact Sig.alignedBufs_append_slice pb nm e ln x y ps vs (by omega)
  | (_, .array _ e' _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.alignedBufs]
    rw [Sig.alignedBufs_append_slice pb nm e ln x y ps vs (by omega)]
    split <;> rfl
  | (_, .slice _ e' _) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.alignedBufs]
    rw [Sig.alignedBufs_append_slice pb nm e ln x y ps vs (by omega)]
    split <;> rfl
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.alignedBufs]
    exact Sig.alignedBufs_append_slice pb nm e ln x y ps vs (by omega)
  | (_, .table _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_5, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.alignedBufs]
    rw [Sig.alignedBufs_append_slice pb nm e ln x y ps vs (by omega)]
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h
  | (_, .table _) :: _, [], h => by simp [Param.words.eq_5] at h

/-- The lists of slices of the parameters followed by one more read-only slice: those
of the others. -/
theorem Sig.lists_append_slice (pb : Nat) (m : Mem) (nm : String) (e : Elem) (ln : String) (x y : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.lists pb m (ps ++ [((nm, .slice false e ln) : String × Param)]) (vs ++ [x, y]) = Sig.lists pb m ps vs
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    exact Sig.lists_append_slice pb m nm e ln x y ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    exact Sig.lists_append_slice pb m nm e ln x y ps vs (by omega)
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    exact Sig.lists_append_slice pb m nm e ln x y ps vs (by omega)
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    rw [Sig.lists_append_slice pb m nm e ln x y ps vs (by omega)]
  | (_, .table _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_5, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.lists]
    rw [Sig.lists_append_slice pb m nm e ln x y ps vs (by omega)]
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h
  | (_, .table _) :: _, [], h => by simp [Param.words.eq_5] at h

/-- The descriptors of the parameters followed by one more read-only slice: those of
the others. -/
theorem Sig.descs_append_slice (pb : Nat) (nm : String) (e : Elem) (ln : String) (x y : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.descs pb (ps ++ [((nm, .slice false e ln) : String × Param)]) (vs ++ [x, y]) = Sig.descs pb ps vs
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    exact Sig.descs_append_slice pb nm e ln x y ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    exact Sig.descs_append_slice pb nm e ln x y ps vs (by omega)
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    exact Sig.descs_append_slice pb nm e ln x y ps vs (by omega)
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    rw [Sig.descs_append_slice pb nm e ln x y ps vs (by omega)]
  | (_, .table _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_5, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.descs]
    exact Sig.descs_append_slice pb nm e ln x y ps vs (by omega)
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h
  | (_, .table _) :: _, [], h => by simp [Param.words.eq_5] at h


/-! ## Contracts -/

theorem getD_append_lt {α : Type} (l l' : List α) (d : α) {i : Nat} (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_of_ge {α : Type} (l : List α) (d : α) {i : Nat} (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none h]

/-- An entry of a contract's memory, a region and whether it is writable, within
another of the same kind. -/
def RegionBelow (a b : Region × Bool) : Prop := Region.Prefix a.1 b.1 ∧ a.2 = b.2

theorem RegionBelow.refl (a : Region × Bool) : RegionBelow a a := ⟨⟨rfl, Nat.le_refl _⟩, rfl⟩

theorem Region.Prefix.sub {a b : Region} (h : Region.Prefix a b) : Region.Sub a b := fun x hx => by
  obtain ⟨hb, hl⟩ := h
  simp only [Region.Contains, ← hb] at *; omega

/-- Entries within entries, their writability and-ed with the same flag. -/
theorem forall₂_below_map (wa : Bool) {l l' : List (Region × Bool)} (h : List.Forall₂ RegionBelow l l') :
    List.Forall₂ RegionBelow (l.map fun (r, w) => (r, w && wa)) (l'.map fun (r, w) => (r, w && wa)) := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons ⟨hx.1, by simp only; rw [hx.2]⟩ ih

/-- Each entry within some entry. -/
theorem below_mem {l l' : List (Region × Bool)} (h : List.Forall₂ RegionBelow l l') {a : Region × Bool}
    (ha : a ∈ l) : ∃ b ∈ l', RegionBelow a b := by
  induction h with
  | nil => cases ha
  | @cons x x' _ _ hx _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨x', List.mem_cons_self .., hx⟩
    · obtain ⟨b, hb, hab⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- Pairwise disjointness carries over to entries within the entries. -/
theorem pairwise_below {l l' : List (Region × Bool)} (h : List.Forall₂ RegionBelow l l')
    (hp : l'.Pairwise fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :
    l.Pairwise fun a b => (a.2 || b.2) → a.1.Disjoint b.1 := by
  induction h with
  | nil => exact .nil
  | @cons a a' l l' ha _ ih =>
    obtain ⟨h₁, h₂⟩ := List.pairwise_cons.mp hp
    refine List.pairwise_cons.mpr ⟨fun b hb hw => ?_, ih h₂⟩
    obtain ⟨b', hb', hbb⟩ := below_mem ‹List.Forall₂ RegionBelow l l'› hb
    have d := h₁ b' hb' (by rw [← ha.2, ← hbb.2]; exact hw)
    exact (d.sub_left ha.1.sub).sub_right hbb.1.sub

theorem forall₂_below_append {a a' b b' : List (Region × Bool)} (h₁ : List.Forall₂ RegionBelow a a')
    (h₂ : List.Forall₂ RegionBelow b b') : List.Forall₂ RegionBelow (a ++ b) (a' ++ b') := by
  induction h₁ with
  | nil => exact h₂
  | cons hx _ ih => exact .cons hx ih

theorem forall₂_below_refl (l : List (Region × Bool)) : List.Forall₂ RegionBelow l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (RegionBelow.refl a) ih

/-- The regions of entries, filtered by writability, within those of entries containing them. -/
theorem covers_filter {l l' : List (Region × Bool)} (h : ∀ a ∈ l, ∃ b ∈ l', RegionBelow a b) (f : Bool → Bool) :
    Covers ((l.filter fun x => f x.2).map (·.1)) ((l'.filter fun x => f x.2).map (·.1)) := by
  intro x n ⟨r, hr, hc⟩
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  obtain ⟨ha, haf⟩ := List.mem_filter.mp ha
  obtain ⟨b, hb, hab⟩ := h a ha
  refine ⟨b.1, List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, by rw [← hab.2]; exact haf⟩, rfl⟩, ?_⟩
  obtain ⟨hb', hl⟩ := hab.1
  simp only [Region.Contains, ← hb'] at hc ⊢; omega

/-- A parameter's word index, in a longer parameter list. -/
theorem Sig.wordIndex_append : ∀ (ps q : List (String × Param)) (x : String) (k : Nat),
    Sig.wordIndex ps x = some k → Sig.wordIndex (ps ++ q) x = some k
  | [], _, _, _, h => by simp [Sig.wordIndex] at h
  | (n, p) :: ps, q, x, k, h => by
    simp only [Sig.wordIndex, List.cons_append] at h ⊢
    split at h
    · simp only [↓reduceIte, *] at h ⊢
    · simp only [↓reduceIte, *]
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [Sig.wordIndex_append ps q x k' hk']; rfl

/-- A function verified against `sig.contract A pre post …` is verified against
the contract of `sig.withSlice nm e ln` (one more, last, parameter, a read-only
slice its code need not read) whose precondition implies `pre`, whose
postcondition follows from `post`, and whose leak, agreed on, gives `leak`'s:
the code runs as it does from the state permitted the shorter contract's
memory, which the longer one's covers (`RegionModel.verified_narrowTo`). The
calling convention `T.abi` must pass the slice's two words after the others,
with an argument area at least as long, and ignore the permissions in what it
reads of a state. -/
theorem Verified.withSlice {T : Target} (R : RegionModel T.isa)
    (habi : ∀ s s₁ r w, T.abiPreserved (R.withRegions s r w) s₁ →
      T.abiPreserved s (R.withRegions s₁ (R.rd s) (R.wr s)))
    (A A' : Abi T.isa) (hpb : A'.ptrBits = A.ptrBits)
    (hrd : ∀ s, A'.rd s = R.rd s) (hwr : ∀ s, A'.wr s = R.wr s)
    (hrdA : ∀ s, A.rd s = R.rd s) (hwrA : ∀ s, A.wr s = R.wr s)
    (hmem : ∀ s, A.mem s = R.mem s) (hmem' : ∀ s, A'.mem s = R.mem s)
    (hret : ∀ s r w, A.ret (R.withRegions s r w) = A'.ret s)
    (hpubA : ∀ s₁ s₂ r₁ w₁ r₂ w₂, A'.pub s₁ s₂ → A.pub (R.withRegions s₁ r₁ w₁) (R.withRegions s₂ r₂ w₂))
    (hres : ∀ n s r w, A.reserved n (R.withRegions s r w) = A'.reserved n s)
    (halign : A.alignsBufs = false) (halign' : A'.alignsBufs = false)
    {sig : Sig} {nm ln : String} {e : Elem}
    {vals : T.isa.State → List (BitVec 64)} {X Y : T.isa.State → BitVec 64}
    (hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) = some vals)
    (hargs' : A'.args (((sig.withSlice nm e ln).words A'.ptrBits).map (·.bits A'.ptrBits)) =
      some fun s => vals s ++ [X s, Y s])
    (hlen : ∀ s, (vals s).length = (sig.words A.ptrBits).length)
    (hvals : ∀ s r w, vals (R.withRegions s r w) = vals s)
    (hwf : ∀ n s r w, A'.wf (((sig.withSlice nm e ln).words A'.ptrBits).map (·.bits A'.ptrBits)) n s →
      A.wf ((sig.words A.ptrBits).map (·.bits A.ptrBits)) n (R.withRegions s r w))
    (harea : ∀ s, List.Forall₂ RegionBelow (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s)
      (A'.argArea (((sig.withSlice nm e ln).words A'.ptrBits).map (·.bits A'.ptrBits)) s))
    (harea_with : ∀ s r w, A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) (R.withRegions s r w) =
      A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s)
    {c : Prog T.isa} {writeArgs : Bool} {stack : Nat}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {pre' : Curry ((sig.withSlice nm e ln).words A'.ptrBits) (Mem → Prop)}
    {post' : (sig.withSlice nm e ln).Post A'.ptrBits}
    {leak' : Option (Curry ((sig.withSlice nm e ln).words A'.ptrBits) (Mem → List Nat))}
    (h : Verified T c (sig.contract A pre post writeArgs stack leak))
    (hpre : ∀ s, Curry.apply _ pre' (vals s ++ [X s, Y s]) (A'.mem s) → Curry.apply _ pre (vals s) (A.mem s))
    (hpost : ∀ s m' (v : BitVec 64), Curry.apply _ pre' (vals s ++ [X s, Y s]) (A'.mem s) →
      Curry.apply _ post (vals s) (A.mem s) m' (v.setWidth _) →
      Curry.apply _ post' (vals s ++ [X s, Y s]) (A'.mem s) m' (v.setWidth _))
    (hleak : ∀ s₁ s₂, Curry.apply _ pre' (vals s₁ ++ [X s₁, Y s₁]) (A'.mem s₁) →
      Curry.apply _ pre' (vals s₂ ++ [X s₂, Y s₂]) (A'.mem s₂) →
      (∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((vals s₁).getD i 0).setWidth (((sig.words A.ptrBits).map (·.bits A.ptrBits)).getD i 64) =
          ((vals s₂).getD i 0).setWidth (((sig.words A.ptrBits).map (·.bits A.ptrBits)).getD i 64)) →
      leakAgree leak' (vals s₁ ++ [X s₁, Y s₁]) (A'.mem s₁) (vals s₂ ++ [X s₂, Y s₂]) (A'.mem s₂) →
      leakAgree leak (vals s₁) (A.mem s₁) (vals s₂) (A.mem s₂))
    (hsat : ∃ s, ((sig.withSlice nm e ln).contract A' pre' post' writeArgs stack leak').pre s) :
    Verified T c ((sig.withSlice nm e ln).contract A' pre' post' writeArgs stack leak') := by
  obtain ⟨pb', args', argArea', reserved', wf', pub', mem', rd', wr', ret', sym', align', mode'⟩ := A'
  dsimp only at hpb hrd hwr hmem' hret hpubA hres halign' hargs' hwf harea hpre hpost hleak
  subst hpb
  have hl : ∀ s, (vals s).length = (sig.params.flatMap fun p => p.2.words A.ptrBits).length := hlen
  have hB : ∀ s, Sig.bufs (sig.withSlice nm e ln).params (vals s ++ [X s, Y s]) =
      Sig.bufs sig.params (vals s) ++ [(⟨X s, (Y s).toNat * e.size⟩, false)] := fun s =>
    Sig.bufs_append_slice A.ptrBits nm e ln _ _ sig.params (vals s) (hl s)
  have hL : ∀ s m, Sig.lists A.ptrBits m (sig.withSlice nm e ln).params (vals s ++ [X s, Y s]) =
      Sig.lists A.ptrBits m sig.params (vals s) := fun s m =>
    Sig.lists_append_slice A.ptrBits m nm e ln _ _ sig.params (vals s) (hl s)
  have hD : ∀ s, Sig.descs A.ptrBits (sig.withSlice nm e ln).params (vals s ++ [X s, Y s]) =
      Sig.descs A.ptrBits sig.params (vals s) := fun s =>
    Sig.descs_append_slice A.ptrBits nm e ln _ _ sig.params (vals s) (hl s)
  have hM : ∀ s r w, A.mem (R.withRegions s r w) = A.mem s := fun s r w => by
    rw [hmem, hmem, R.mem_with]
  have hMM : ∀ s, mem' s = A.mem s := fun s => by rw [hmem', hmem]
  -- The shorter contract's memory, from the state's arguments.
  let oldAll : T.isa.State → List (Region × Bool) := fun s =>
    (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
    (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map fun (r, w) => (r, w && writeArgs)
  let newAll : T.isa.State → List (Region × Bool) := fun s =>
    ((Sig.bufs sig.params (vals s) ++ [(⟨X s, (Y s).toNat * e.size⟩, false)]) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
    (argArea' (((sig.withSlice nm e ln).words A.ptrBits).map (·.bits A.ptrBits)) s).map
      fun (r, w) => (r, w && writeArgs)
  let midAll : T.isa.State → List (Region × Bool) := fun s =>
    (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
    (argArea' (((sig.withSlice nm e ln).words A.ptrBits).map (·.bits A.ptrBits)) s).map
      fun (r, w) => (r, w && writeArgs)
  have hsub : ∀ s, (midAll s).Sublist (newAll s) := fun s =>
    List.Sublist.append (List.Sublist.append (List.sublist_append_left _ _) (List.Sublist.refl _))
      (List.Sublist.refl _)
  have hrel : ∀ s, List.Forall₂ RegionBelow (oldAll s) (midAll s) := fun s =>
    forall₂_below_append (forall₂_below_refl _) (forall₂_below_map writeArgs (harea s))
  have hbelow : ∀ s, ∀ a ∈ oldAll s, ∃ b ∈ newAll s, RegionBelow a b := fun s a ha => by
    obtain ⟨b, hb, hab⟩ := below_mem (hrel s) ha
    exact ⟨b, (hsub s).subset hb, hab⟩
  refine R.verified_narrowTo habi h (fun s => ((oldAll s).filter (!·.2)).map (·.1))
    (fun s => ((oldAll s).filter (·.2)).map (·.1)) ?_ ?_ ?_ ?_ ?_ hsat
  · intro s hs
    simp only [Sig.contract, hargs, hargs'] at hs ⊢
    rw [hB, hMM, hL] at hs
    obtain ⟨wf, rd, wr, pw, rs, bd, hp⟩ := hs
    simp only [halign', Bool.cond_false] at hp
    simp only [hrdA, hwrA, R.rd_with, R.wr_with, hvals, hM, harea_with, halign, hres, Bool.cond_false]
    refine ⟨hwf _ _ _ _ wf, rfl, rfl, pairwise_below (hrel s) ((pw.sublist (hsub s))), ?_, ?_, ?_⟩
    · intro r hr a ha
      obtain ⟨b, hb, hab⟩ := hbelow s a ha
      exact (rs r hr b hb).sub_right hab.1.sub
    · intro a ha
      apply bd a
      rcases List.mem_append.mp ha with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h
    · exact hpre s (by rw [hMM]; exact hp)
  · intro s hs
    simp only [Sig.contract, hargs'] at hs
    rw [hB, hMM, hL] at hs
    obtain ⟨-, rd, wr, -⟩ := hs
    change Covers _ (R.rd s ++ R.wr s)
    rw [← hrd, ← hwr, rd, wr]
    exact (covers_filter (hbelow s) (fun b => !b)).append (covers_filter (hbelow s) id)
  · intro s hs
    simp only [Sig.contract, hargs'] at hs
    rw [hB, hMM, hL] at hs
    obtain ⟨-, -, wr, -⟩ := hs
    change Covers _ (R.wr s)
    rw [← hwr, wr]
    exact covers_filter (hbelow s) id
  · intro s s' hs hq
    simp only [Sig.contract, hargs, hargs'] at hs hq ⊢
    rw [hB, hMM, hL] at hs
    simp only [hvals, hM, hret] at hq
    obtain ⟨-, -, -, -, -, -, hp⟩ := hs
    simp only [halign', Bool.cond_false] at hp
    have := hpost s (A.mem s') (ret' s') (by rw [hMM]; exact hp) hq
    simp only [hMM] at this ⊢
    exact this
  · intro s₁ s₂ h₁ h₂ hp
    simp only [Sig.contract, hargs, hargs'] at h₁ h₂ hp ⊢
    rw [hB, hMM, hL] at h₁ h₂
    simp only [hvals, hM, halign', Bool.cond_false] at h₁ h₂ ⊢
    rw [hD, hMM, hMM] at hp
    have p₁ := h₁.2.2.2.2.2.2
    have p₂ := h₂.2.2.2.2.2.2
    obtain ⟨hpA, hpi, hpd⟩ := hp
    have hpo : ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((vals s₁).getD i 0).setWidth (((sig.words A.ptrBits).map (·.bits A.ptrBits)).getD i 64) =
          ((vals s₂).getD i 0).setWidth (((sig.words A.ptrBits).map (·.bits A.ptrBits)).getD i 64) := by
      intro i hi
      have hpl := Sig.pubs_length sig.params A.ptrBits
      have hlt : i < (sig.params.flatMap (·.2.pubs)).length := by
        by_contra hge
        rw [getD_of_ge _ _ (by omega)] at hi
        cases hi
      have hw' : List.map (fun x => ArgWord.bits A.ptrBits x) ((sig.withSlice nm e ln).words A.ptrBits) =
          List.map (fun x => ArgWord.bits A.ptrBits x) (sig.words A.ptrBits) ++
            [A.ptrBits, A.ptrBits] := by
        rw [Sig.words_withSlice]; simp [ArgWord.bits]
      have hp' : (sig.withSlice nm e ln).params.flatMap (·.2.pubs) =
          sig.params.flatMap (·.2.pubs) ++ [true, true] := by
        simp [Sig.withSlice, List.flatMap_append, Param.pubs]
      have l₁ := hl s₁
      have l₂ := hl s₂
      have lw : (List.map (fun x => ArgWord.bits A.ptrBits x) (sig.words A.ptrBits)).length =
          (sig.params.flatMap fun p => p.2.words A.ptrBits).length := by
        rw [List.length_map]; rfl
      have := hpi i (by rw [hp', getD_append_lt _ _ _ hlt]; exact hi)
      rw [hw', getD_append_lt _ _ _ (by omega), getD_append_lt _ _ _ (by omega),
        getD_append_lt _ _ _ (by omega)] at this
      exact this
    refine ⟨?_, hpo, hpd⟩
    cases leak <;> cases leak' <;> simp only at hpA ⊢
    · exact hpubA _ _ _ _ _ _ hpA
    · exact hpubA _ _ _ _ _ _ hpA.1
    · exact ⟨hpubA _ _ _ _ _ _ hpA, hleak s₁ s₂ (by rw [hMM]; exact p₁) (by rw [hMM]; exact p₂) hpo trivial⟩
    · exact ⟨hpubA _ _ _ _ _ _ hpA.1, hleak s₁ s₂ (by rw [hMM]; exact p₁) (by rw [hMM]; exact p₂) hpo
        (by rw [hMM, hMM]; exact hpA.2)⟩
end VG
