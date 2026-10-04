import VerifiedGarbage.Proof.Ed448.X86.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 verification's equation on x86 (32-bit): `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean`), constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant or a counter), and a concrete state satisfying
the signature's contract. The contract lets timing depend on the inputs; the
code's depends on the pointers alone. The local contract only reads the
arguments; the shared one lets the code write them too (`writeArgs`), which
it does not (`Verified.narrowTo`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (RecoverOk VerifyEqOk)
open VG.Impl.Ed448.X86 (verifyEquation)

/-- The taint analysis starts with the stack arguments public, and the word
holding `scratch` known to be the base address of the writable region. -/
def verifyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8192], argLen := 20, argBases := [(16, 0)] }

theorem verifyTaint_wf {s : State} (h : verifyEquationLocal.pre s) : VG.X86.Taint.Wf verifyTaint s := by
  have hp := VerifyPre.of h
  have hf := hp.f3; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, verifyTaint], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [verifyTaint]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [verifyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    exact ⟨by simp [verifyTaint], by simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]⟩

theorem verifyTaint_agree {s t : State} (hs : verifyEquationLocal.pre s) (ht : verifyEquationLocal.pre t)
    (hp : verifyEquationLocal.pub s t) : VG.X86.Taint.Agree verifyTaint s t := by
  obtain ⟨hsp, a0, a1, a2, a3, _⟩ := hp
  have ps := VerifyPre.of hs
  have pt := VerifyPre.of ht
  have ha : ∀ i < 4, arg s i = arg t i := fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, verifyTaint_wf hs, verifyTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [verifyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [ps.wr, pt.wr, a3]
  · simp only [verifyTaint] at hk
    have fs := ps.sp_fit
    have ft := pt.sp_fit
    rw [show VG.X86.Taint.depth verifyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega) h4 hk, VG.X86.Taint.argByte_eq (by omega) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega))

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation :=
  VG.Taint.constantTime (A := taint) verifyTaint (fun _ _ hs ht hp => verifyTaint_agree hs ht hp)
    (by taint_decide)

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
    s.rd = [pk, sig, challenge] ∧ s.wr = [scratch, args] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

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
    verifyEquationWide.Implies (Spec.Ed448.verifyEquationContract X86.abi) where
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
    Verified X86.target verifyEquation (Spec.Ed448.verifyEquationContract X86.abi) := by
  have hsat := verifyEquationWide_implies.sat_left
  have satLocal : ∃ s, verifyEquationLocal.pre s := hsat.elim fun s h => ⟨_, verifyEquationWide_pre s h⟩
  have verifiedLocal : Verified X86.target verifyEquation verifyEquationLocal :=
    Verified.of_correct (verifyEquation_ok hR hE) verifyEquation_ct (.refl satLocal)
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
