module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.PublicOut
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract

-- separate module: every target's proofs of the functions share it

/-!
# The entropy the DSA parameter search asks for is public

Every target's `vg_dsa_parameter_search_init` and `vg_dsa_parameter_search` are
proven against `parameterInitAskedContract` and `parameterSearchAskedContract`:
the contracts of the specification, but that the length of the tape they ask for
is not any that the specification allows but the one the code asks for
(`FirstAsked`, `Asked`), a function of what is public. They imply the contracts of
the specification (`parameterInit_imp`, `parameterSearch_imp`), and that the length
is public (`parameterInit_public`, `parameterSearch_public`).
-/

@[expose] public section

namespace VG.Proof.Dsa

open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.Dsa
open VG.Proof.Dsa.Generation (Asked FirstAsked requested)

/-- Word 3 of four. -/
theorem word3 {m : Mem} {p : Addr} {a b c d : BitVec 64} (h : wordsAt m p 4 = [a, b, c, d]) :
    m.readW (p + 24) 64 = d := by
  simp only [wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq] at h
  exact h.2.2.2.1

theorem map_toNat_inj {n : Nat} {a b : List (BitVec n)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-! ## `vg_dsa_parameter_search_init` -/

/-- `Spec.Dsa.parameterInitContract`, for code that asks for the first tape as `FirstAsked`
says. -/
def parameterInitAskedContract {M : ISA} (A : Abi M) : Contract M :=
  parameterInitSig.contract A
    (post := fun state pLen _m m' r =>
      match parameterInit pLen.toNat with
      | none => r.toNat = 0 ∧ wordsAt m' state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ ∃ first,
        wordsAt m' state 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧
        FirstAsked pLen.toNat first)
    (leak := some fun _state _pLen _m => [])

/-- `parameterInitApi` with that contract: the forms that clean up a function's code take an
`Api`. -/
def parameterInitAskedApi : Api :=
  { parameterInitApi with contracts := some fun A _ => parameterInitAskedContract A }

/-- `F` at the arguments `vs`. -/
theorem parameterInit_apply {α : Type} (pb : Nat) (F : Curry (parameterInitSig.words pb) α) :
    ∀ vs, Curry.apply (parameterInitSig.words pb) F vs =
      @id (Addr → BitVec pb → α) F
        (vs.getD 0 0) ((vs.getD 1 0).setWidth pb)
  | [] | [_]
  | _ :: _ :: _ => rfl

theorem parameterInit_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {rb : Nat}
    (h : VerifiedScrubbed T c (parameterInitAskedContract A) rb)
    (hR : (T.noResidue.elim False fun R => R c (parameterInitAskedContract A) rb) →
      T.noResidue.elim False fun R => R c (parameterInitContract A) rb) :
    VerifiedScrubbed T c (parameterInitContract A) rb :=
  h.post_mono hR fun state pLen _ m' r h => by
    dsimp only at h ⊢
    generalize parameterInit pLen.toNat = values at h ⊢
    cases values with
    | none => exact h
    | some values => exact ⟨h.1, h.2.choose, h.2.choose_spec.1, h.2.choose_spec.2.1⟩

/-- The word of the first tape's length. -/
theorem parameterInit_first {p : Nat} {m : Mem} {state : Addr} {r : BitVec 32}
    (h : match parameterInit p with
      | none => r.toNat = 0 ∧ wordsAt m state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ ∃ first,
        wordsAt m state 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧ FirstAsked p first) :
    m.readW (state + 24) 64 = if generationPLenValid p then BitVec.ofNat 64 (512 * p) else 0 := by
  unfold parameterInit at h
  by_cases hp : generationPLenValid p = true
  · rw [ite_eq_left hp] at h ⊢
    obtain ⟨-, first, hw, -, rfl⟩ := h
    exact word3 hw
  · rw [ite_eq_right hp] at h ⊢
    exact word3 h.2

/-- The length of the first tape is public. -/
theorem parameterInit_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {rb : Nat}
    (h : VerifiedScrubbed T c (parameterInitAskedContract A) rb) :
    parameterInitOut.Of A c (parameterInitContract A) := by
  refine PublicOut.of_post h.verified fun vals hv s₁ s₂ s₁' s₂' _ _ hpub _ h₁ h₂ => ?_
  simp only [Sig.contract] at hpub
  rw [hv] at hpub
  have h1 : ((vals s₁).getD 1 0).setWidth A.ptrBits = ((vals s₂).getD 1 0).setWidth A.ptrBits :=
    hpub.2.1 1 rfl
  replace h₁ := (congrFun (congrFun (congrFun (parameterInit_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (parameterInit_apply A.ptrBits _ _) _) _) _).mp h₂
  dsimp only [id] at h₁ h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (parameterInit_apply A.ptrBits (parameterInitOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s')) ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, parameterInitOut]
  rw [parameterInit_first h₁, parameterInit_first h₂, h1]

/-! ## `vg_dsa_parameter_search` -/

/-- `Spec.Dsa.parameterSearchContract`, for code that asks for the next tape as `Asked`
says. -/
def parameterSearchAskedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterSearchSig.contract A
    (pre := fun _out outLen _used _rand randLen _scratch scratchLen state m =>
      let pLen := (m.readW (state + 8) 64).toNat
      generationPLenValid pLen ∧
      outLen.toNat = 2 * pLen + generationQLen pLen ∧
      generationScratchWords pLen ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ parameterSeeds ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (parameterEntropy pLen) ∧
      randLen.toNat ≤ parameterEntropy pLen)
    (post := fun out outLen used rand randLen _scratch _scratchLen state m m' r =>
      let pLen := (m.readW (state + 8) 64).toNat
      let result := parameterSearch pLen (m.readW state 64).toNat (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      bytesAt m' out outLen.toNat =
        (match result.outcome with
          | .accepted a => encodeParams pLen (generationQLen pLen) a
          | _ => List.replicate outLen.toNat 0) ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      ∃ requested, wordsAt m' state 4 = [BitVec.ofNat 64 result.remaining,
        BitVec.ofNat 64 pLen, BitVec.ofNat 64 (parameterEntropy pLen),
        BitVec.ofNat 64 requested] ∧
        Asked pLen result requested)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used rand randLen _scratch _scratchLen state m =>
      (wordsAt m state 4).map (·.toNat) ++ (bytesAt m rand randLen.toNat).map (·.toNat))

/-- `parameterSearchApi` with that contract: the forms that clean up a function's code take an
`Api`. -/
def parameterSearchAskedApi : Api :=
  { parameterSearchApi with contracts := some fun A stack => parameterSearchAskedContract A stack }

/-- `F` at the arguments `vs`. -/
theorem parameterSearch_apply {α : Type} (pb : Nat) (F : Curry (parameterSearchSig.words pb) α) :
    ∀ vs, Curry.apply (parameterSearchSig.words pb) F vs =
      @id (Addr → BitVec pb → Addr → Addr → BitVec pb → Addr → BitVec pb → Addr → α) F
        (vs.getD 0 0) ((vs.getD 1 0).setWidth pb) (vs.getD 2 0) (vs.getD 3 0) ((vs.getD 4 0).setWidth pb) (vs.getD 5 0) ((vs.getD 6 0).setWidth pb) (vs.getD 7 0)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem parameterSearch_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (parameterSearchAskedContract A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (parameterSearchAskedContract A stack) rb) →
      T.noResidue.elim False fun R => R c (parameterSearchContract A stack) rb) :
    VerifiedScrubbed T c (parameterSearchContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ _ _ ⟨h₁, h₂, h₃, q, h₄, h₅⟩ => ⟨h₁, h₂, h₃, q, h₄, h₅.1⟩

/-- The length of the next tape is public. -/
theorem parameterSearch_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (parameterSearchAskedContract A stack) rb) :
    parameterSearchOut.Of A c (parameterSearchContract A stack) := by
  refine PublicOut.of_post h.verified fun vals hv s₁ s₂ s₁' s₂' _ _ hpub _ h₁ h₂ => ?_
  simp only [Sig.contract] at hpub
  rw [hv] at hpub
  have hl := hpub.1.2
  replace hl := (congrFun (parameterSearch_apply A.ptrBits _ _) _).symm.trans
    (hl.trans (congrFun (parameterSearch_apply A.ptrBits _ _) _))
  replace h₁ := (congrFun (congrFun (congrFun (parameterSearch_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (parameterSearch_apply A.ptrBits _ _) _) _) _).mp h₂
  dsimp only [id] at hl h₁ h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (parameterSearch_apply A.ptrBits (parameterSearchOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s')) ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, parameterSearchOut]
  obtain ⟨-, -, -, q₁, hw₁, -, hq₁⟩ := h₁
  obtain ⟨-, -, -, q₂, hw₂, -, hq₂⟩ := h₂
  obtain ⟨hw, hb⟩ := List.append_inj hl (by simp [wordsAt])
  have hw := map_toNat_inj hw
  simp only [wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq,
    Nat.mul_zero, BitVec.add_zero] at hw
  have hp := hw.2.1
  refine List.cons_eq_cons.mpr ⟨congrArg BitVec.toNat ?_, rfl⟩
  rw [word3 hw₁, word3 hw₂, hq₁, hq₂, hw.1, map_toNat_inj hb]
  exact congrArg (fun w : BitVec 64 => BitVec.ofNat 64 (requested w.toNat (parameterSearch w.toNat _ _))) hp

end VG.Proof.Dsa
