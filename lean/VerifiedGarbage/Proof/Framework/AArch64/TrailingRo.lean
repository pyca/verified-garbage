module

public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A read-only last argument the code never reads (AArch64)

`Verified.dropTrailingRo`: code verified for a function whose arguments fill
the eight argument registers and at least one stack slot is verified for the
function with one more argument, last, a read-only array (`Sig.withRo`),
which the code never reads, with a precondition that implies the old one and
a postcondition and leak that the old ones give. The array's address is the
next stack argument, after the others: the code reads only the old ones.

The code runs as it does from the state permitted only the old contract's
regions (`RegionModel.verified_narrowTo`): its buffers, but not the array,
and its stack arguments, but not the new one's slot.
-/

@[expose] public section

namespace VG

/-- `sig` with one more parameter, last: a read-only array of `n` elements
`e`. -/
def Sig.withRo (sig : Sig) (nm : String) (e : Elem) (n : Nat) : Sig :=
  { sig with params := sig.params ++ [(nm, .array false e n)] }

theorem Sig.words_withRo (sig : Sig) (nm : String) (e : Elem) (n : Nat) (pb : Nat) :
    (sig.withRo nm e n).words pb = sig.words pb ++ ([.addr] : List ArgWord) := by
  simp [Sig.withRo, Sig.words, Param.words]

theorem Sig.noLists_withRo {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    (h : Sig.noLists sig.params = true) : Sig.noLists (sig.withRo nm e n).params = true := by
  simpa [Sig.withRo, Sig.noLists, List.all_append] using h

/-- The buffers of the parameters followed by one more read-only array,
given values for the others and its address `x`. -/
theorem Sig.bufs_append_ro (pb : Nat) (nm : String) (e : Elem) (n : Nat) (x : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.bufs (ps ++ [((nm, .array false e n) : String × Param)]) (vs ++ [x]) =
        Sig.bufs ps vs ++ [(⟨x, n * e.size⟩, false)]
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_ro pb nm e n x ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_ro pb nm e n x ps vs (by omega)]
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_ro pb nm e n x ps vs (by omega)]
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_ro pb nm e n x ps vs (by omega)
  | (_, .table _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_5, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_ro pb nm e n x ps vs (by omega)
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp [Param.words.eq_4] at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h
  | (_, .table _) :: _, [], h => by simp [Param.words.eq_5] at h

end VG

namespace VG.AArch64

/-! ## The arguments of the signature with the array -/

section
variable (sig : Sig) (nm : String) (e : Elem) (n : Nat)

theorem nStack_withRo (hk : 8 ≤ (sig.words abi.ptrBits).length) :
    nStack (sig.withRo nm e n) = nStack sig + 1 := by
  simp only [nStack, Sig.words_withRo, List.length_append, List.length_singleton]
  omega_using [hk]

theorem allArgs_withRo_eq (s : State) : allArgs (sig.withRo nm e n) s = allArgs (sig.withScratch nm e n) s := by
  simp only [allArgs, nStack, Sig.words_withRo, Sig.words_withScratch]

theorem argsOk_withRo (hk : 8 ≤ (sig.words abi.ptrBits).length) (hA : ArgsOk sig) :
    ArgsOk (sig.withRo nm e n) := by
  have h := argsOk_withScratch nm e n hk hA
  unfold ArgsOk at h ⊢
  rw [Sig.words_withRo, funext (allArgs_withRo_eq sig nm e n)]
  rwa [Sig.words_withScratch] at h

theorem allArgs_withRo (hk : 8 ≤ (sig.words abi.ptrBits).length) (s : State) :
    allArgs (sig.withRo nm e n) s = allArgs sig s ++ [stackArg s (nStack sig)] := by
  rw [allArgs_withRo_eq]
  exact allArgs_withScratch sig nm e n hk s s (fun _ _ => rfl) (fun _ _ => rfl)

/-- The buffers and the argument area of the signature with the array. -/
theorem allRegions_withRo (hk : 8 ≤ (sig.words abi.ptrBits).length) (s : State) :
    allRegions (sig.withRo nm e n) s = Sig.bufs sig.params (allArgs sig s) ++
      [(⟨stackArg s (nStack sig), n * e.size⟩, false),
        (⟨stackArgAddr s 0, 8 * (nStack sig + 1)⟩, false)] := by
  rw [allRegions, allArgs_withRo sig nm e n hk,
    show (sig.withRo nm e n).params = sig.params ++ [((nm, .array false e n) : String × Param)]
      from rfl, Sig.bufs_append_ro _ nm e n _ sig.params _ (allArgs_length sig s), argArea,
    nStack_withRo sig nm e n hk]
  simp

/-- The buffers and the argument area of the signature, with at least one
stack argument. -/
theorem allRegions_of_stack (hk : 8 < (sig.words abi.ptrBits).length) (s : State) :
    allRegions sig s = Sig.bufs sig.params (allArgs sig s) ++
      [(⟨stackArgAddr s 0, 8 * nStack sig⟩, false)] := by
  have h0 : nStack sig ≠ 0 := by simp only [nStack]; omega_using [hk]
  simp [allRegions, argArea, h0]

end

/-! ## The theorem -/

/-- The regions of the contract without the array, in a state of the
contract with it: its buffers and its argument area. -/
def roRd (sig : Sig) (s : State) : List Region := ((allRegions sig s).filter (!·.2)).map (·.1)
def roWr (sig : Sig) (s : State) : List Region := ((allRegions sig s).filter (·.2)).map (·.1)

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {pre' : Curry ((sig.withRo nm e n).words abi.ptrBits) (Mem → Prop)}
  {post' : (sig.withRo nm e n).Post abi.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
  {leak' : Option (Curry ((sig.withRo nm e n).words abi.ptrBits) (Mem → List Nat))}

/-- Code verified for a function with at least one stack argument is
verified for the function with one more argument, last, a read-only array
of `n` elements `e` that it never reads, with a precondition that implies
the old one (`hpre`), a postcondition that the old one gives (`hpost`) and a
leak that agrees whenever it agrees (`hleak`). -/
theorem Verified.dropTrailingRo {c : Prog isa}
    (h : Verified target c (sig.contract abi pre post wa stack leak))
    (hk : 8 < (sig.words abi.ptrBits).length)
    (hpre : ∀ vs x m, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply _ pre' (vs ++ [x]) m → Curry.apply _ pre vs m)
    (hpost : ∀ vs x m m' r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply _ post vs m m' r → Curry.apply _ post' (vs ++ [x]) m m' r)
    (hleak : ∀ vs₁ x₁ m₁ vs₂ x₂ m₂, vs₁.length = (sig.words abi.ptrBits).length →
      vs₂.length = (sig.words abi.ptrBits).length →
      leakAgree leak' (vs₁ ++ [x₁]) m₁ (vs₂ ++ [x₂]) m₂ → leakAgree leak vs₁ m₁ vs₂ m₂)
    (hsat : ∃ s, ((sig.withRo nm e n).contract abi pre' post' wa stack leak').pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target c ((sig.withRo nm e n).contract abi pre' post' wa stack leak') := by
  have hk8 : 8 ≤ (sig.words abi.ptrBits).length := Nat.le_of_lt hk
  have hA' : ArgsOk (sig.withRo nm e n) := let ⟨_, hs⟩ := hsat; argsOk_of_pre hs
  have hA : ArgsOk sig := let ⟨_, hs⟩ := h.2.2; argsOk_of_pre hs
  have hl' := Sig.noLists_withRo nm e n hl
  have hlen := allArgs_length sig
  refine regionModel.verified_narrowTo (T := target) (fun _ _ _ _ h => h) h
    (roRd sig) (roWr sig) ?_ ?_ ?_ ?_ ?_ hsat
  · -- The narrowed state satisfies the old precondition.
    intro s hs
    rw [pre_args hA' hl', allRegions_withRo sig nm e n hk8, allArgs_withRo sig nm e n hk8,
      nStack_withRo sig nm e n hk8] at hs
    obtain ⟨⟨hst, hfit⟩, -, -, hpw, hres, hnw, hpr⟩ := hs
    refine (pre_args hA hl).mpr ?_
    have eR : allRegions sig (regionModel.withRegions s (roRd sig s) (roWr sig s)) =
        allRegions sig s := rfl
    have eA : allArgs sig (regionModel.withRegions s (roRd sig s) (roWr sig s)) = allArgs sig s :=
      rfl
    have eS : (regionModel.withRegions s (roRd sig s) (roWr sig s)).sp = s.sp := rfl
    have eM : (regionModel.withRegions s (roRd sig s) (roWr sig s)).mem = s.mem := rfl
    have eD : (regionModel.withRegions s (roRd sig s) (roWr sig s)).rd = roRd sig s := rfl
    have eW : (regionModel.withRegions s (roRd sig s) (roWr sig s)).wr = roWr sig s := rfl
    rw [eR, eA, eS, eM, eD, eW]
    refine ⟨⟨hst, by omega⟩, rfl, rfl, ?_⟩
    rw [allRegions_of_stack sig hk s]
    have hsub : Region.Sub ⟨stackArgAddr s 0, 8 * nStack sig⟩
        ⟨stackArgAddr s 0, 8 * (nStack sig + 1)⟩ := Region.sub_prefix (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.pairwise_append] at hpw ⊢
      obtain ⟨hb, hx, hy⟩ := hpw
      refine ⟨hb, List.pairwise_singleton _ _, fun a ha b hb' hw => ?_⟩
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact (hy a ha (⟨stackArgAddr s 0, 8 * (nStack sig + 1)⟩, false)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hw).sub_right hsub
    · intro r hr a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hres r hr a (List.mem_append_left _ ha)
      · simp only [List.mem_singleton] at ha
        subst ha
        exact (hres r hr (⟨stackArgAddr s 0, 8 * (nStack sig + 1)⟩, false)
          (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))).sub_right
          hsub
    · intro a ha
      exact hnw a (by
        rw [show (sig.withRo nm e n).params = sig.params ++ [((nm, .array false e n) : String × Param)]
          from rfl, Sig.bufs_append_ro _ nm e n _ sig.params _ (hlen s)]
        exact List.mem_append_left _ ha)
    · exact hpre _ _ _ (hlen s) hpr
  · -- The narrowed regions are within the old ones.
    intro s hs
    rw [pre_args hA' hl', allRegions_withRo sig nm e n hk8, allArgs_withRo sig nm e n hk8,
      nStack_withRo sig nm e n hk8] at hs
    obtain ⟨-, hrd, hwr, -⟩ := hs
    show Covers _ (s.rd ++ s.wr)
    refine Covers.of_forall fun r hr => ?_
    simp only [roRd, roWr, allRegions_of_stack sig hk s, List.mem_append, List.mem_map,
      List.mem_filter] at hr
    have hin : ∀ a, (a ∈ Sig.bufs sig.params (allArgs sig s) ∨
        a = ((⟨stackArg s (nStack sig), n * e.size⟩ : Region), false) ∨
        a = ((⟨stackArgAddr s 0, 8 * (nStack sig + 1)⟩ : Region), false)) →
        a.1 ∈ s.rd ++ s.wr := fun a ha => by
      rw [hrd, hwr]
      cases hw : a.2
      · refine List.mem_append_left _ (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨?_, by simp [hw]⟩, rfl⟩)
        simpa using ha
      · refine List.mem_append_right _ (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨?_, hw⟩, rfl⟩)
        simpa using ha
    have hcov : ∀ a ∈ Sig.bufs sig.params (allArgs sig s) ++
        [((⟨stackArgAddr s 0, 8 * nStack sig⟩ : Region), false)], Covers [a.1] (s.rd ++ s.wr) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Covers.of_mem fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hin a (.inl ha)
      · simp only [List.mem_singleton] at ha
        subst ha
        refine Covers.of_sub fun r hr => ⟨_, hin _ (.inr (.inr rfl)), 0, ?_, ?_⟩
        · simp only [List.mem_singleton] at hr; subst hr; simp
        · simp only [List.mem_singleton] at hr; subst hr; simp only; omega
    rcases hr with ⟨a, ⟨ha, -⟩, rfl⟩ | ⟨a, ⟨ha, -⟩, rfl⟩
    · exact hcov a (by simpa using ha)
    · exact hcov a (by simpa using ha)
  · -- The writable regions are the old ones.
    intro s hs
    rw [pre_args hA' hl', allRegions_withRo sig nm e n hk8] at hs
    obtain ⟨-, -, hwr, -⟩ := hs
    show Covers _ s.wr
    rw [hwr, roWr, allRegions_of_stack sig hk s]
    simp only [List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
      ↓reduceIte, List.append_nil]
    exact Covers.refl _
  · -- The postcondition.
    intro s s' _ hq
    rw [post_args hA] at hq
    rw [post_args hA', allArgs_withRo sig nm e n hk8]
    exact hpost _ _ _ _ _ (hlen s) hq
  · -- The public data.
    intro s₁ s₂ _ _ hp
    rw [pub_args hA' hl', allArgs_withRo sig nm e n hk8, allArgs_withRo sig nm e n hk8] at hp
    obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
    refine (pub_args hA hl).mpr ⟨⟨hsp, hleak _ _ _ _ _ _ (hlen s₁) (hlen s₂) hlk⟩, fun i hi => ?_⟩
    show ((allArgs sig s₁).getD i 0).setWidth _ = ((allArgs sig s₂).getD i 0).setWidth _
    have lp := Sig.pubs_length sig.params abi.ptrBits
    have hps : ((sig.withRo nm e n).params.flatMap (·.2.pubs)) =
        sig.params.flatMap (·.2.pubs) ++ [true] := by
      simp [Sig.withRo, Param.pubs]
    have hik : i < (sig.words abi.ptrBits).length := by
      by_contra hc
      simp only [List.getD_eq_getElem?_getD] at hi
      rw [List.getElem?_eq_none (by rw [lp]; exact Nat.le_of_not_lt hc)] at hi
      simp at hi
    have hW : (((sig.withRo nm e n).words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 =
        ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 := by
      rw [Sig.words_withRo, List.map_append]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [List.length_map]; exact hik)]
    have := hpa i (by
      rw [hps]
      simp only [List.getD_eq_getElem?_getD] at hi ⊢
      rw [List.getElem?_append_left (by rw [lp]; exact hik)]
      exact hi)
    rw [hW] at this
    simp only [List.getD_eq_getElem?_getD] at this ⊢
    rwa [List.getElem?_append_left (by rw [hlen]; exact hik),
      List.getElem?_append_left (by rw [hlen]; exact hik)] at this

end

end VG.AArch64
