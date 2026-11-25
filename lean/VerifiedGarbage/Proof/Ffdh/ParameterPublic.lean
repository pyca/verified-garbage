module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.PublicOut
public import VerifiedGarbage.Spec.Ffdh.SievedContract

-- separate module: every target's proofs of the functions share it

/-!
# The entropy the FFDH parameter search asks for is public

Every target's `vg_ffdh_parameter_generation_init` and `vg_ffdh_generate_parameters`
are proven against `parameterInitAskedContract` and
`sievedParameterSearchAskedContract`: the contracts of the specification, but that
the length of the tape they ask for is not any that the specification allows but the
one the code asks for (`FirstAsked`, `Asked`), a function of what is public. They
imply the contracts of the specification (`parameterInit_imp`,
`sievedParameterSearch_imp`), and that the length is public
(`parameterInit_public`, `sievedParameterSearch_public`).
-/

@[expose] public section

namespace VG.Proof.Ffdh

open VG.Spec.Rsa (bytesAt wordsAt i2osp)
open VG.Spec.Ffdh

/-- Word 3 of four. -/
theorem word3 {m : Mem} {p : Addr} {a b c d : BitVec 64} (h : wordsAt m p 4 = [a, b, c, d]) :
    m.readW (p + 24) 64 = d := by
  simp only [wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq] at h
  exact h.2.2.2.1

theorem map_toNat_inj {n : Nat} {a b : List (BitVec n)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-! ## `vg_ffdh_parameter_generation_init` -/

/-- `Spec.Ffdh.parameterInitContract`, for code that asks for the first tape as `FirstAsked`
says. -/
def parameterInitAskedContract {M : ISA} (A : Abi M) : Contract M :=
  parameterInitSig.contract A
    (post := fun state bits generator _ m' r =>
      match parameterInit bits.toNat generator.toNat with
      | none => r.toNat = 0 ∧ wordsAt m' state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ ∃ first,
        wordsAt m' state 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧
        FirstAsked bits.toNat first)

/-- `parameterInitApi` with that contract: the forms that clean up a function's code take an
`Api`. -/
def parameterInitAskedApi : Api :=
  { parameterInitApi with contracts := some fun A _ => parameterInitAskedContract A }

/-- `F` at the arguments `vs`. -/
theorem parameterInit_apply {α : Type} (pb : Nat) (F : Curry (parameterInitSig.words pb) α) :
    ∀ vs, Curry.apply (parameterInitSig.words pb) F vs =
      @id (Addr → BitVec pb → BitVec 32 → α) F
        (vs.getD 0 0) ((vs.getD 1 0).setWidth pb) ((vs.getD 2 0).setWidth 32)
  | [] | [_] | [_, _]
  | _ :: _ :: _ :: _ => rfl

theorem parameterInit_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {rb : Nat}
    (h : VerifiedScrubbed T c (parameterInitAskedContract A) rb)
    (hR : (T.noResidue.elim False fun R => R c (parameterInitAskedContract A) rb) →
      T.noResidue.elim False fun R => R c (parameterInitContract A) rb) :
    VerifiedScrubbed T c (parameterInitContract A) rb :=
  h.post_mono hR fun state bits generator _ m' r h => by
    dsimp only at h ⊢
    generalize parameterInit bits.toNat generator.toNat = values at h ⊢
    cases values with
    | none => exact h
    | some values => exact ⟨h.1, h.2.choose, h.2.choose_spec.1, h.2.choose_spec.2.1⟩

/-- The word of the first tape's length. -/
theorem parameterInit_first {b g : Nat} {m : Mem} {state : Addr} {r : BitVec 32}
    (h : match parameterInit b g with
      | none => r.toNat = 0 ∧ wordsAt m state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ ∃ first,
        wordsAt m state 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧ FirstAsked b first) :
    m.readW (state + 24) 64 =
      if (parameterInit b g).isSome then BitVec.ofNat 64 (512 * ((b + 7) / 8)) else 0 := by
  unfold parameterInit at h ⊢
  by_cases hp : (512 ≤ b && b ≤ 8192 && (g == 2 || g == 5)) = true
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
  have h2 : ((vals s₁).getD 2 0).setWidth 32 = ((vals s₂).getD 2 0).setWidth 32 :=
    hpub.2.1 2 rfl
  replace h₁ := (congrFun (congrFun (congrFun (parameterInit_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (parameterInit_apply A.ptrBits _ _) _) _) _).mp h₂
  dsimp only [id] at h₁ h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (parameterInit_apply A.ptrBits (parameterInitOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s')) ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, parameterInitOut]
  rw [parameterInit_first h₁, parameterInit_first h₂, h1, h2]

/-! ## `vg_ffdh_generate_parameters` -/

/-- `Spec.Ffdh.sievedParameterSearchContract`, for code that asks for the next tape as
`Asked` says. -/
def sievedParameterSearchAskedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterSearchSig.contract A
    (pre := fun _out outLen _used bits generator _rand randLen _scratch scratchLen state m =>
      512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ outLen.toNat = (bits.toNat + 7) / 8 ∧
      (generator.toNat = 2 ∨ generator.toNat = 5) ∧
      Spec.Rsa.scratchWords outLen.toNat ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ parameterAttempts bits.toNat ∧
      m.readW (state + 8) 64 = BitVec.ofNat 64 outLen.toNat ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (parameterEntropy bits.toNat) ∧
      randLen.toNat ≤ parameterEntropy bits.toNat)
    (post := fun out outLen used bits generator rand randLen _scratch _scratchLen state m m' r =>
      let result := sievedParameterSearch bits.toNat generator.toNat (m.readW state 64).toNat
        (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      bytesAt m' out outLen.toNat =
        (match result with
          | .accepted p _ => i2osp p outLen.toNat
          | _ => List.replicate outLen.toNat 0) ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      ∃ requested, wordsAt m' state 4 = [BitVec.ofNat 64 result.remaining,
        BitVec.ofNat 64 outLen.toNat, BitVec.ofNat 64 (parameterEntropy bits.toNat),
        BitVec.ofNat 64 requested] ∧
        Asked bits.toNat result requested)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used _bits _generator rand randLen _scratch _scratchLen state m =>
      (bytesAt m rand randLen.toNat).map (·.toNat) ++ (wordsAt m state 4).map (·.toNat))

/-- `sievedParameterSearchApi` with that contract: the forms that clean up a function's code take an
`Api`. -/
def sievedParameterSearchAskedApi : Api :=
  { sievedParameterSearchApi with contracts := some fun A stack => sievedParameterSearchAskedContract A stack }

/-- `F` at the arguments `vs`. -/
theorem parameterSearch_apply {α : Type} (pb : Nat) (F : Curry (parameterSearchSig.words pb) α) :
    ∀ vs, Curry.apply (parameterSearchSig.words pb) F vs =
      @id (Addr → BitVec pb → Addr → BitVec pb → BitVec 32 → Addr → BitVec pb → Addr → BitVec pb → Addr → α) F
        (vs.getD 0 0) ((vs.getD 1 0).setWidth pb) (vs.getD 2 0) ((vs.getD 3 0).setWidth pb) ((vs.getD 4 0).setWidth 32) (vs.getD 5 0) ((vs.getD 6 0).setWidth pb) (vs.getD 7 0) ((vs.getD 8 0).setWidth pb) (vs.getD 9 0)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem sievedParameterSearch_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (sievedParameterSearchAskedContract A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (sievedParameterSearchAskedContract A stack) rb) →
      T.noResidue.elim False fun R => R c (sievedParameterSearchContract A stack) rb) :
    VerifiedScrubbed T c (sievedParameterSearchContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨h₁, h₂, h₃, q, h₄, h₅⟩ => ⟨h₁, h₂, h₃, q, h₄, h₅.1⟩

/-- The length of the next tape is public. -/
theorem sievedParameterSearch_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (sievedParameterSearchAskedContract A stack) rb) :
    sievedParameterSearchOut.Of A c (sievedParameterSearchContract A stack) := by
  refine PublicOut.of_post h.verified fun vals hv s₁ s₂ s₁' s₂' _ _ hpub _ h₁ h₂ => ?_
  simp only [Sig.contract] at hpub
  rw [hv] at hpub
  have hl := hpub.1.2
  have h3 : ((vals s₁).getD 3 0).setWidth A.ptrBits = ((vals s₂).getD 3 0).setWidth A.ptrBits :=
    hpub.2.1 3 rfl
  have h4 : ((vals s₁).getD 4 0).setWidth 32 = ((vals s₂).getD 4 0).setWidth 32 :=
    hpub.2.1 4 rfl
  have h6 : ((vals s₁).getD 6 0).setWidth A.ptrBits = ((vals s₂).getD 6 0).setWidth A.ptrBits :=
    hpub.2.1 6 rfl
  replace hl := (congrFun (parameterSearch_apply A.ptrBits _ _) _).symm.trans
    (hl.trans (congrFun (parameterSearch_apply A.ptrBits _ _) _))
  replace h₁ := (congrFun (congrFun (congrFun (parameterSearch_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (parameterSearch_apply A.ptrBits _ _) _) _) _).mp h₂
  dsimp only [id] at hl h₁ h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (parameterSearch_apply A.ptrBits (sievedParameterSearchOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s')) ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, sievedParameterSearchOut]
  obtain ⟨-, -, -, q₁, hw₁, -, hq₁⟩ := h₁
  obtain ⟨-, -, -, q₂, hw₂, -, hq₂⟩ := h₂
  obtain ⟨hb, hw⟩ := List.append_inj hl (by simp only [List.length_map, bytesAt, List.length_range, h6])
  have hw := map_toNat_inj hw
  simp only [wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq,
    Nat.mul_zero, BitVec.add_zero] at hw
  refine List.cons_eq_cons.mpr ⟨congrArg BitVec.toNat ?_, rfl⟩
  rw [word3 hw₁, word3 hw₂, hq₁, hq₂, hw.1, map_toNat_inj hb, h3, h4]

end VG.Proof.Ffdh
