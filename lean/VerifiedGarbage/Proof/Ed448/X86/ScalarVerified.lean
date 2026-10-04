import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAddMain
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 scalar arithmetic on x86 (32-bit): `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses: the only branches are on the
loop counters, and every address is a pointer plus a constant or a counter.
The local contracts only read the arguments; the shared contract of `Spec/`
lets the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`). A concrete witness proves it satisfiable.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Impl.Ed448.X86 (scalarReduce scalarMulAdd)

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` (argument `scidx` of `argc`) known to be the base
addresses of the writable regions. -/
def scalarTaint (scidx argc : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [57, 8192], argLen := 4 + 4 * argc,
    argBases := [(4, 0), (4 + 4 * scidx, 1)] }

theorem scalarTaint_wf {s : State} {argc scidx : Nat} (hp : Args s argc scidx)
    (hw : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hos : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s scidx)))
    (hofit : (arg s 0).toNat + 57 ≤ 2 ^ 32)
    (hret : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩)
    (hao : (⟨argAddr s 0, 4 * argc⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩) :
    VG.X86.Taint.Wf (scalarTaint scidx argc) s := by
  have hf := hp.sc_fit; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, scalarTaint], by simpa [hw] using hos, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by change (s.gpr .esp).toNat + (4 + 4 * argc) ≤ 2 ^ 32; omega_using [spfit], ?_⟩, ?_⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hf, hofit]
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hret hao
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [scalarTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by dsimp only [scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]
    · refine ⟨by dsimp only [scalarTaint]; have := hp.sc_lt; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]

theorem scalarTaint_agree {s t : State} {scidx argc : Nat}
    (hs : VG.X86.Taint.Wf (scalarTaint scidx argc) s) (ht : VG.X86.Taint.Wf (scalarTaint scidx argc) t)
    (hsp : s.gpr .esp = t.gpr .esp) (ha : ∀ i < argc, arg s i = arg t i)
    (hi : scidx < argc)
    (hws : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s scidx)])
    (hwt : t.wr = [⟨(arg t 0).setWidth 64, 57⟩, scR (arg t scidx)])
    (hss : (s.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32)
    (hst : (t.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32) :
    VG.X86.Taint.Agree (scalarTaint scidx argc) s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [scalarTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [hws, hwt, ha 0 (by omega_using [hi]), ha scidx hi]
  · simp only [scalarTaint] at hk
    rw [show VG.X86.Taint.depth (scalarTaint scidx argc).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega_using [hss]) h4 hk,
      VG.X86.Taint.argByte_eq (by omega_using [hst]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk, h4]))

/-! ## Reduction -/

theorem scalarReduce_wf {s : State} (h : scalarReduceLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  have hp := ReducePre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 2 3) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := ReducePre.of hs
  have pt := ReducePre.of ht
  refine scalarTaint_agree (scalarReduce_wf hs) (scalarReduce_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem scalarReduce_ok (s : State) (h : scalarReduceLocal.pre s) :
    ∃ tr t, Exec isa scalarReduce s tr t ∧ abiPreserved s t ∧ scalarReduceLocal.post s t :=
  scalarReduce_correct (ReducePre.of h)

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def scalarReduceSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the shared contract's precondition. -/
def scalarReduceSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := scalarReduceSatMem
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

/-- `scalarReduceLocal`, the arguments writable as the shared contract has them. -/
def scalarReduceWide : Contract isa :=
  { scalarReduceLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let wide : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [wide] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      wide.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def scalarReduceRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 114⟩, ⟨argAddr s 0, 12⟩]
def scalarReduceWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarReduceWide_pre (s : State) (h : scalarReduceWide.pre s) :
    scalarReduceLocal.pre (s.withRegions (scalarReduceRd s) (scalarReduceWr s)) := by
  simp only [scalarReduceLocal, scalarReduceRd, scalarReduceWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarReduceWide_implies :
    scalarReduceWide.Implies (Spec.Ed448.scalarReduceContract X86.abi) := by
  have a0 : arg scalarReduceSat 0 = 0x1000 := by decide
  have a1 : arg scalarReduceSat 1 = 0x2000 := by decide
  have a2 : arg scalarReduceSat 2 = 0x4000 := by decide
  have e : argAddr scalarReduceSat 0 = 0x8004 := by decide
  have esp : scalarReduceSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.scalarReduceContract, Spec.Ed448.scalarReduceSig,
    Spec.Ed448.scratchWords, scalarReduceWide, scalarReduceLocal, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, e, esp] using scalarReduceSat

theorem scalarReduce_verified :
    Verified X86.target scalarReduce (Spec.Ed448.scalarReduceContract X86.abi) := by
  have hsat := scalarReduceWide_implies.sat_left
  have satLocal : ∃ s, scalarReduceLocal.pre s := hsat.elim fun s h => ⟨_, scalarReduceWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarReduce scalarReduceLocal :=
    Verified.of_correct scalarReduce_ok scalarReduce_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarReduceRd scalarReduceWr
    scalarReduceWide_pre ?_ ?_ ?_ ?_ hsat) scalarReduceWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scalarReduceRd, scalarReduceWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarReduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarReduceWide, scalarReduceLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarReduceWide, scalarReduceLocal, arg_withRegions, State.withRegions_gpr] using h

/-! ## Multiply-add -/

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 4 5) s := by
  have hp := MulAddPre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 4 5) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := MulAddPre.of hs
  have pt := MulAddPre.of ht
  refine scalarTaint_agree (scalarMulAdd_wf hs) (scalarMulAdd_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  scalarMulAdd_correct (MulAddPre.of h)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x5000, 0x6000` at `0x8004`. -/
def scalarMulAddSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x50 else if a = 0x8015 then 0x60 else 0

/-- A state satisfying the shared contract's precondition. -/
def scalarMulAddSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := scalarMulAddSatMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x5000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x6000, 8192⟩, ⟨0x8004, 20⟩]

/-- `scalarMulAddLocal`, the arguments writable as the shared contract has them. -/
def scalarMulAddWide : Contract isa :=
  { scalarMulAddLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧ args.Disjoint out ∧
      args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

def scalarMulAddRd (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 57⟩, ⟨(arg s 3).setWidth 64, 57⟩,
    ⟨argAddr s 0, 20⟩]
def scalarMulAddWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

theorem scalarMulAddWide_pre (s : State) (h : scalarMulAddWide.pre s) :
    scalarMulAddLocal.pre (s.withRegions (scalarMulAddRd s) (scalarMulAddWr s)) := by
  simp only [scalarMulAddLocal, scalarMulAddRd, scalarMulAddWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarMulAddWide_implies :
    scalarMulAddWide.Implies (Spec.Ed448.scalarMulAddContract X86.abi) := by
  have a0 : arg scalarMulAddSat 0 = 0x1000 := by decide
  have a1 : arg scalarMulAddSat 1 = 0x2000 := by decide
  have a2 : arg scalarMulAddSat 2 = 0x3000 := by decide
  have a3 : arg scalarMulAddSat 3 = 0x5000 := by decide
  have a4 : arg scalarMulAddSat 4 = 0x6000 := by decide
  have e : argAddr scalarMulAddSat 0 = 0x8004 := by decide
  have esp : scalarMulAddSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.scalarMulAddContract, Spec.Ed448.scalarMulAddSig,
    Spec.Ed448.scratchWords, scalarMulAddWide, scalarMulAddLocal, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp] using scalarMulAddSat

theorem scalarMulAdd_verified :
    Verified X86.target scalarMulAdd (Spec.Ed448.scalarMulAddContract X86.abi) := by
  have hsat := scalarMulAddWide_implies.sat_left
  have satLocal : ∃ s, scalarMulAddLocal.pre s := hsat.elim fun s h => ⟨_, scalarMulAddWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarMulAdd scalarMulAddLocal :=
    Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarMulAddRd scalarMulAddWr
    scalarMulAddWide_pre ?_ ?_ ?_ ?_ hsat) scalarMulAddWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scalarMulAddRd, scalarMulAddWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarMulAddWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86
