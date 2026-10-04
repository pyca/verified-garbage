import VerifiedGarbage.Proof.Ed448.X86.BaseMain
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified

/-!
# Ed448 base-point multiplication on x86 (32-bit): `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`, given that the ladder the
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

theorem scalarBase_wf {s : State} (h : scalarBaseLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  have hp := BasePre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarBase_agree {s t : State} (hs : scalarBaseLocal.pre s) (ht : scalarBaseLocal.pre t)
    (hp : scalarBaseLocal.pub s t) : VG.X86.Taint.Agree (scalarTaint 2 3) s t := by
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := BasePre.of hs
  have pt := BasePre.of ht
  refine scalarTaint_agree (scalarBase_wf hs) (scalarBase_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem scalarBase_ct :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase :=
  VG.Taint.constantTime (A := taint) (scalarTaint 2 3) (fun _ _ hs ht hp => scalarBase_agree hs ht hp)
    (by taint_decide)

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
    s.rd = [scalar] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def scalarBaseRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
def scalarBaseWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarBaseWide_pre (s : State) (h : scalarBaseWide.pre s) :
    scalarBaseLocal.pre (s.withRegions (scalarBaseRd s) (scalarBaseWr s)) := by
  simp only [scalarBaseLocal, scalarBaseRd, scalarBaseWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarBaseWide_implies :
    scalarBaseWide.Implies (Spec.Ed448.scalarBaseContract X86.abi) := by
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
    Verified X86.target scalarBase (Spec.Ed448.scalarBaseContract X86.abi) := by
  have hsat := scalarBaseWide_implies.sat_left
  have satLocal : ∃ s, scalarBaseLocal.pre s := hsat.elim fun s h => ⟨_, scalarBaseWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarBase scalarBaseLocal :=
    Verified.of_correct (scalarBase_ok hl) scalarBase_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarBaseRd scalarBaseWr
    scalarBaseWide_pre ?_ ?_ ?_ ?_ hsat) scalarBaseWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scalarBaseRd, scalarBaseWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
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
