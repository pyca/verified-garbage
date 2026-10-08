import VerifiedGarbage.Proof.Ed448.X86.VerifyCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 verification's equation on x86 (32-bit): `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean`), constant time
(`VerifyCT.lean`), and a concrete state satisfying the signature's contract,
with the 20 bytes of stack below the return address that the calls of the
field functions use. The contract lets timing depend on the inputs; the
code's depends on the pointers alone. The local contract only reads the
arguments; the shared one lets the code write them too (`writeArgs`), which
it does not (`Verified.narrowTo`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (RecoverOk VerifyEqOk)
open VG.Impl.Ed448.X86 (verifyEquation)

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqOk) (s : State) (h : verifyEquationLocal.pre s) :
    ∃ tr t, Exec isa verifyEquation s tr t ∧ abiPreserved s t ∧ verifyEquationLocal.post s t := by
  obtain ⟨tr, t, he, h1, h2⟩ := verifyEquation_main hR hE (VerifyPre.of h)
  exact ⟨tr, t, he, h1, h2⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def verifyEquationSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30
  else if a = 0x8011 then 0x40 else 0

/-- A state satisfying the shared contract's precondition. -/
def verifyEquationSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := verifyEquationSatMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8004, 16⟩]

/-- `verifyEquationLocal`, the arguments writable as the shared contract has them. -/
def verifyEquationWide : Contract isa :=
  { verifyEquationLocal with
  pre := fun s =>
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let sig : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let challenge : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩
    s.rd = [pk, sig, challenge] ∧ s.wr = [scratch, args] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint pk ∧
      stk.Disjoint sig ∧ stk.Disjoint challenge ∧ stk.Disjoint scratch }

def verifyEquationRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 1).setWidth 64, 114⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨argAddr s 0, 16⟩]
def verifyEquationWr (s : State) : List Region := [⟨(arg s 3).setWidth 64, 8192⟩]

theorem verifyEquationWide_pre (s : State) (h : verifyEquationWide.pre s) :
    verifyEquationLocal.pre (s.withRegions (verifyEquationRd s) (verifyEquationWr s)) := by
  simp only [verifyEquationLocal, verifyEquationRd, verifyEquationWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verifyEquationWide_implies :
    verifyEquationWide.Implies (Spec.Ed448.verifyEquationContract X86.abi 20) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, verifyEquationWide, verifyEquationLocal, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = _ at h
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [Spec.Ed448.bytesAt, List.length_map,
      List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [Spec.Ed448.bytesAt, List.length_map,
      List.length_range])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    have a0 : arg verifyEquationSat 0 = 0x1000 := by decide
    have a1 : arg verifyEquationSat 1 = 0x2000 := by decide
    have a2 : arg verifyEquationSat 2 = 0x3000 := by decide
    have a3 : arg verifyEquationSat 3 = 0x4000 := by decide
    have e : argAddr verifyEquationSat 0 = 0x8004 := by decide
    have esp : verifyEquationSat.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, verifyEquationWide, verifyEquationLocal, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] [a0, a1, a2, a3, e, esp] using verifyEquationSat

theorem verifyEquation_verified (hR : RecoverOk) (hE : VerifyEqOk) :
    Verified X86.target verifyEquation (Spec.Ed448.verifyEquationContract X86.abi 20) := by
  have hsat := verifyEquationWide_implies.sat_left
  have satLocal : ∃ s, verifyEquationLocal.pre s := hsat.elim fun s h => ⟨_, verifyEquationWide_pre s h⟩
  have verifiedLocal : Verified X86.target verifyEquation verifyEquationLocal :=
    Verified.of_correct (verifyEquation_ok hR hE) (verifyEquation_ct hR) (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal verifyEquationRd verifyEquationWr
    verifyEquationWide_pre ?_ ?_ ?_ ?_ hsat) verifyEquationWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [verifyEquationRd, verifyEquationWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl | rfl) | rfl <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [verifyEquationWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp
  · intro s t _ h
    exact h
  · intro s t _ _ h
    simpa only [verifyEquationWide, verifyEquationLocal, arg_withRegions, State.withRegions_gpr,
      State.withRegions_mem] using h

end VG.Proof.Ed448.X86
