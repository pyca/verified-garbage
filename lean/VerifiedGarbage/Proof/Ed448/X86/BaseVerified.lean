import VerifiedGarbage.Proof.Ed448.X86.BaseCT

/-!
# Ed448 base-point multiplication on x86 (32-bit): `Verified`

Correctness (`BaseMain.lean`), constant time (`BaseCT.lean`),
satisfiability, and the shared contract of `Spec/` with the 20 bytes of stack
below the return address that the calls of the field functions use, given that the ladder the
code computes encodes as `[k]B` (`Proof.Ed448.BaseLadderOk`, proven with the
group law in `Proof/Ed448/Facts.lean`, which only the registration file
imports). The local contract only reads the arguments; the shared one lets
the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (BaseLadderOk decodeLE_below)
open VG.Impl.Ed448.X86 (scalarBase)

theorem scalarBase_ok (hl : BaseLadderOk) (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨tr, t, he, h1, h2⟩ := scalarBase_ladder (BasePre.of h)
  refine ⟨tr, t, he, h1, ?_⟩
  change Spec.Ed448.bytesAt t.mem _ 57 =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul _ Spec.Ed448.basePoint)
  rw [h2, hl _ (decodeLE_below (by simp [Spec.Ed448.bytesAt]))]

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def scalarBaseSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the shared contract's precondition. -/
def scalarBaseSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := scalarBaseSatMem
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

/-- `scalarBaseLocal`, the arguments writable as the shared contract has them. -/
def scalarBaseWide : Contract isa :=
  { scalarBaseLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩
    s.rd = [scalar] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint out ∧
      stk.Disjoint scratch }

def scalarBaseRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
def scalarBaseWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarBaseWide_pre (s : State) (h : scalarBaseWide.pre s) :
    scalarBaseLocal.pre (s.withRegions (scalarBaseRd s) (scalarBaseWr s)) := by
  simp only [scalarBaseLocal, scalarBaseRd, scalarBaseWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarBaseWide_implies :
    scalarBaseWide.Implies (Spec.Ed448.scalarBaseContract X86.abi 20) := by
  have a0 : arg scalarBaseSat 0 = 0x1000 := by decide
  have a1 : arg scalarBaseSat 1 = 0x2000 := by decide
  have a2 : arg scalarBaseSat 2 = 0x4000 := by decide
  have e : argAddr scalarBaseSat 0 = 0x8004 := by decide
  have esp : scalarBaseSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
    Spec.Ed448.scratchWords, scalarBaseWide, scalarBaseLocal, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, e, esp] using scalarBaseSat

theorem scalarBase_verified (hl : BaseLadderOk) :
    Verified X86.target scalarBase (Spec.Ed448.scalarBaseContract X86.abi 20) := by
  have hsat := scalarBaseWide_implies.sat_left
  have satLocal : ∃ s, scalarBaseLocal.pre s := hsat.elim fun s h => ⟨_, scalarBaseWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarBase scalarBaseLocal :=
    Verified.of_correct (scalarBase_ok hl) scalarBase_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarBaseRd scalarBaseWr
    scalarBaseWide_pre ?_ ?_ ?_ ?_ hsat) scalarBaseWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarBaseRd, scalarBaseWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarBaseWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86
