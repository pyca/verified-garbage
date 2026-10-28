module

public import VerifiedGarbage.Proof.Seed.X86.Verified
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Seed.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Seed.X86.G8
import VerifiedGarbage.Proof.Seed.X86.Lanes
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Seed.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# SEED ECB on x86 (32-bit): calls of the blocks functions

`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` allocate their working
space on the stack (1088 bytes, as `vg_seed_{en,de}crypt_blocks` need) and
call the blocks function of their direction with it (`ecbCall`): the
caller's `ebx` pushed in a frame of its own, the four arguments loaded into
`eax`, `ecx`, `edx` and `ebx` and pushed in a frame for the call. That is 24
bytes of stack (`callX86`): the two frames and the call's return address.

`call_wp` proves the code from the blocks function's (`ecb_correct`, by
`WP.callWith`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (argOp)
open VG.Proof.Seed (ecbX86)

/-- The ECB functions' code with the working space as the fourth argument
and 24 bytes of stack, the argument slots read only. -/
def callX86 (d : Spec.Seed.Direction) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * wsSlots⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint scratch ∧ 24 ≤ (s.gpr .esp).toNat ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * wsSlots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post := (ecbX86 d).post
  pub := (ecbX86 d).pub

theorem ecb_noSp (d : Spec.Seed.Direction) : NoSp (ecb d) := by
  cases d
  · exact NoSp.of_all (by lit_decide)
  · exact NoSp.of_all (by lit_decide)

theorem ecb_stackUse (d : Spec.Seed.Direction) : stackUse (ecb d) = 0 := by
  cases d
  · lit_decide
  · lit_decide

/-- The stack the code uses, as the contract writes it. -/
theorem stk_eq {E : BitVec 32} (h : 24 ≤ E.toNat) :
    below E 24 = ⟨E.setWidth 64 - BitVec.ofNat 64 24, 24⟩ := by
  show (⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth h]

/-- The arguments' words, after the push of one word below them. -/
theorem pushed_arg {s : State} (h4 : 4 ≤ (s.gpr .esp).toNat) (hf : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 4) :
    (pushed [.ebx] s).ea (argOp (i + 1)) = argAddr s i ∧
      (pushed [.ebx] s).mem.readW (argAddr s i) 32 = arg s i := by
  refine ⟨?_, ?_⟩
  · show ((pushed [.ebx] s).gpr .esp + BitVec.ofNat 32 (4 + 4 * (i + 1))).setWidth 64 =
      (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64
    rw [pushed_esp]
    refine congrArg (BitVec.setWidth 64) ?_
    have e : BitVec.ofNat 32 (4 + 4 * (i + 1)) = BitVec.ofNat 32 (4 * [Reg.ebx].length) + BitVec.ofNat 32 (4 + 4 * i) := by
      rw [← BitVec.ofNat_add]; congr 1; simp; omega
    rw [e, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  · refine (pushed_frame (rs := [.ebx]) (by decide) (by simpa using h4)).readW (arg_contains s hf hi)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩
    rw [VG.X86.Taint.sub_setWidth h4,
      show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega)]
    exact (VG.Offset.disjoint_below_above _ (m := 4) (a := 4) (l := 16) (by omega)).symm

/-- What the loads leave for the call: the four arguments in `eax`, `ecx`,
`edx` and `ebx`, below the outer frame at `E - 4`. -/
structure Loaded (s₀ : State) (E : BitVec 32) (s : State) : Prop where
  esp : s.gpr .esp = E - BitVec.ofNat 32 4
  eax : s.gpr .eax = arg s₀ 0
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = arg s₀ 2
  ebx : s.gpr .ebx = arg s₀ 3
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .esp → s.gpr r = s₀.gpr r
  mem : s.mem = (pushed [.ebx] s₀).mem
  rd : s.rd = s₀.rd
  wr : s.wr = below E 4 :: s₀.wr

/-- The loads of the arguments, after the outer frame's push. -/
theorem argLoads_ok {s₀ : State} {E : BitVec 32} (hEd : s₀.gpr .esp = E) (hE : 24 ≤ E.toNat)
    (fitE : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32) (hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd) :
    ∃ s₂, runBlock isa [.mov .eax (.mem (argOp 1)), .mov .ecx (.mem (argOp 2)), .mov .edx (.mem (argOp 3)),
      .mov .ebx (.mem (argOp 4))] (pushed [.ebx] s₀) = some s₂ ∧ Loaded s₀ E s₂ := by
  let s₁ := pushed [.ebx] s₀
  have esp₁ : s₁.gpr .esp = E - BitVec.ofNat 32 4 := by rw [pushed_esp, hEd]; rfl
  have pa := fun i (hi : i < 4) => pushed_arg (s := s₀) (by rw [hEd]; omega) fitE hi
  have inA : ∀ {s : State}, s.rd = s₀.rd → ∀ i < 4, InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 :=
    fun h i hi => ⟨_, List.mem_append_left _ (by rw [h]; exact hrA), arg_contains s₀ fitE hi⟩
  have rd₁ : s₁.rd = s₀.rd := pushed_rd _ _
  have ea₂ : ∀ {s : State}, s.gpr .esp = s₁.gpr .esp → ∀ i, s.ea (argOp i) = s₁.ea (argOp i) := fun {s} h i => by
    show (s.gpr .esp + _).setWidth 64 = (s₁.gpr .esp + _).setWidth 64; rw [h]
  obtain ⟨sa, ea, va, oa, ma, rda, wra⟩ := ldArg_ok s₁ .eax 1 (by rw [(pa 0 (by decide)).1]; exact inA rd₁ 0 (by decide))
  obtain ⟨sb, eb, vb, ob, mb, rdb, wrb⟩ := ldArg_ok sa .ecx 2 (by
    rw [ea₂ (oa _ (by decide)), (pa 1 (by decide)).1]; exact inA (by rw [rda, rd₁]) 1 (by decide))
  obtain ⟨sc, ec, vc, oc, mc, rdc, wrc⟩ := ldArg_ok sb .edx 3 (by
    rw [ea₂ (by rw [ob _ (by decide), oa _ (by decide)]), (pa 2 (by decide)).1]
    exact inA (by rw [rdb, rda, rd₁]) 2 (by decide))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldArg_ok sc .ebx 4 (by
    rw [ea₂ (by rw [oc _ (by decide), ob _ (by decide), oa _ (by decide)]), (pa 3 (by decide)).1]
    exact inA (by rw [rdc, rdb, rda, rd₁]) 3 (by decide))
  refine ⟨s₂, ?_, ⟨?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, by rw [m₂, mc, mb, ma],
    by rw [rd₂, rdc, rdb, rda, rd₁], by rw [wr₂, wrc, wrb, wra, pushed_wr, hEd]; rfl⟩⟩
  · rw [show ([.mov .eax (.mem (argOp 1)), .mov .ecx (.mem (argOp 2)), .mov .edx (.mem (argOp 3)),
        .mov .ebx (.mem (argOp 4))] : List Instr) = [.mov .eax (.mem (argOp 1))] ++
        ([.mov .ecx (.mem (argOp 2))] ++ ([.mov .edx (.mem (argOp 3))] ++ [.mov .ebx (.mem (argOp 4))])) from rfl,
      runBlock_append, ea, Option.bind_some, runBlock_append, eb, Option.bind_some, runBlock_append, ec,
      Option.bind_some, e₂]
  · rw [o₂ _ (by decide), oc _ (by decide), ob _ (by decide), oa _ (by decide), esp₁]
  · rw [o₂ _ (by decide), oc _ (by decide), ob _ (by decide), va, (pa 0 (by decide)).1]
    exact (pa 0 (by decide)).2
  · rw [o₂ _ (by decide), oc _ (by decide), vb, ea₂ (oa _ (by decide)), (pa 1 (by decide)).1, ma]
    exact (pa 1 (by decide)).2
  · rw [o₂ _ (by decide), vc, ea₂ (by rw [ob _ (by decide), oa _ (by decide)]), (pa 2 (by decide)).1, mb, ma]
    exact (pa 2 (by decide)).2
  · rw [v₂, ea₂ (by rw [oc _ (by decide), ob _ (by decide), oa _ (by decide)]), (pa 3 (by decide)).1, mc, mb, ma]
    exact (pa 3 (by decide)).2
  · rw [o₂ r h4, oc r h3, ob r h2, oa r h1]; exact pushed_gpr _ _ h5

/-- The regions of `callX86`'s precondition, with the stack's as `below`. -/
structure CallPre' (s₀ : State) (E : BitVec 32) : Prop where
  hEd : s₀.gpr .esp = E
  hE : 24 ≤ E.toNat
  hrd : s₀.rd = [⟨(arg s₀ 0).setWidth 64, 128⟩, ⟨argAddr s₀ 0, 16⟩]
  hwr : s₀.wr = [⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩, ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩]
  dKD : Region.Disjoint ⟨(arg s₀ 0).setWidth 64, 128⟩ ⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩
  dKS : Region.Disjoint ⟨(arg s₀ 0).setWidth 64, 128⟩ ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩
  dDS : Region.Disjoint ⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩ ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩
  sK : Region.Disjoint (below E 24) ⟨(arg s₀ 0).setWidth 64, 128⟩
  sD : Region.Disjoint (below E 24) ⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩
  sS : Region.Disjoint (below E 24) ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩
  fitK : (arg s₀ 0).toNat + 128 ≤ 2 ^ 32
  fitD : (arg s₀ 1).toNat + 16 * (arg s₀ 2).toNat ≤ 2 ^ 32
  fitB : (arg s₀ 3).toNat + 4 * wsSlots ≤ 2 ^ 32

/-- The call of the blocks function, in the frame of its arguments, from
the loads; on return, `esp` and the callee-saved registers as before it, the
memory changed only in the data, the working space and the 20 bytes below
`E - 4`, and the data the ECB of the schedule's blocks. -/
theorem inner_wp (d : Spec.Seed.Direction) {s₀ s₂ : State} {E : BitVec 32} (hc : CallPre' s₀ E)
    (hl : Loaded s₀ E s₂) :
    WP isa (.frame (.push [.ebx, .edx, .ecx, .eax]) (blocksCall d) (.pop .eax 4)) s₂ fun s' =>
      s'.rd = s₂.rd ∧ s'.wr = s₂.wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s₂.gpr r) ∧
      Frame ([⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩, ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩] ++
        [below (s₂.gpr .esp) 20]) s₂.mem s'.mem ∧
      Spec.Seed.blocksAt s'.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat =
        Spec.Seed.ecb (Spec.Seed.scheduleAt s₀.mem ((arg s₀ 0).setWidth 64)) d
          (Spec.Seed.blocksAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat) := by
  obtain ⟨hEd, hE, hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitB⟩ := hc
  have hEl := E.isLt
  have hrs : Reg.esp ∉ [Reg.ebx, .edx, .ecx, .eax] := by decide
  have h4 : 4 ≤ E.toNat := by omega
  have espN₂ : (s₂.gpr .esp).toNat = E.toNat - 4 := by rw [hl.esp, sub_toNat h4]
  have hfit₂ : 4 * [Reg.ebx, .edx, .ecx, .eax].length + 4 ≤ (s₂.gpr .esp).toNat := by
    rw [espN₂]; show 20 ≤ _; omega
  have a0 : arg (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry 0 = arg s₀ 0 := by
    rw [callEntry_arg hfit₂ hrs (i := 0) (by decide)]; exact hl.eax
  have a1 : arg (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry 1 = arg s₀ 1 := by
    rw [callEntry_arg hfit₂ hrs (i := 1) (by decide)]; exact hl.ecx
  have a2 : arg (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry 2 = arg s₀ 2 := by
    rw [callEntry_arg hfit₂ hrs (i := 2) (by decide)]; exact hl.edx
  have a3 : arg (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry 3 = arg s₀ 3 := by
    rw [callEntry_arg hfit₂ hrs (i := 3) (by decide)]; exact hl.ebx
  have espE : ((pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry.gpr .esp).toNat = E.toNat - 24 := by
    rw [callEntry_espNat hfit₂, espN₂]; rfl
  have hin : Region.Sub (below (s₂.gpr .esp) 20) (below E 24) := by
    rw [hl.esp]; exact below_inner (by decide) hE
  have argsE : (⟨argAddr (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry 0, 16⟩ : Region) =
      below (s₂.gpr .esp) 16 := by
    rw [callEntry_argAddr0]; rfl
  have argsSub : Region.Sub ⟨argAddr (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry 0, 16⟩ (below E 24) := by
    rw [argsE]; exact fun x hx => hin x (below_sub (by decide) (by rw [espN₂]; omega) x hx)
  have retSub : Region.Sub ⟨((pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry.gpr .esp).setWidth 64, 4⟩
      (below E 24) := by
    rw [show (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry.gpr .esp =
        s₂.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
      rw [callEntry_esp', BitVec.sub_sub, ← BitVec.ofNat_add]; rfl]
    exact fun x hx => hin x (below_inner (a := 4) (k := 16) (b := 20) (by decide) (by rw [espN₂]; omega) x hx)
  have fE₀ : Frame [below E 24] s₀.mem (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry.mem := by
    have f₁ : Frame [below E 24] s₀.mem s₂.mem := by
      rw [hl.mem]
      exact (pushed_frame (rs := [.ebx]) (by decide) (by simp; rw [hEd]; omega)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, by rw [hEd]; exact below_sub (by simp) hE⟩
    exact f₁.trans ((callEntry_frame hfit₂ hrs).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, hin⟩)
  have hsch := Proof.Seed.scheduleAt_frame fE₀ (p := (arg s₀ 0).setWidth 64) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact sK.symm
  have hblk := Proof.Seed.blocksAt_frame fE₀ (p := (arg s₀ 1).setWidth 64) (n := (arg s₀ 2).toNat)
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; rw [Nat.mul_comm]; exact sD.symm) (by omega)
  cases d <;>
  · refine WP.callWith (k := ecbX86 _) (ecb_correct _) (ecb_noSp _) (by decide) hrs
      (by rw [ecb_stackUse, espN₂]; show 20 ≤ _; omega)
      (rd := [⟨(arg s₀ 0).setWidth 64, 128⟩, ⟨argAddr (pushed [Reg.ebx, .edx, .ecx, .eax] s₂).callEntry 0, 16⟩])
      (wr := [⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩, ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩])
      ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs f ⟨s₃, m₃, post⟩ => ?_
    · simp only [ecbX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
        argAddr_withRegions, a0, a1, a2, a3]
      exact ⟨trivial, trivial, dKD, dKS, dDS, sD.sub_left argsSub, sS.sub_left argsSub,
        sD.sub_left retSub, sS.sub_left retSub, fitK, fitD, fitB, by rw [espE]; omega⟩
    · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.right (Covers.of_mem fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ (by rw [hl.rd, hrd]; simp)
        · rw [argsE]; exact List.mem_append_right _ List.mem_cons_self
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;>
          exact List.mem_cons_of_mem _ (by rw [hl.wr]; exact List.mem_cons_of_mem _ (by rw [hwr]; simp))
    · refine Covers.of_mem fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact List.mem_cons_of_mem _ (by rw [hl.wr]; exact List.mem_cons_of_mem _ (by rw [hwr]; simp))
    · simp only [ecb_stackUse, List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at f
      refine ⟨rd', wr', cs, f, ?_⟩
      rw [← m₃]
      simp only [ecbX86, State.withRegions_mem, arg_withRegions, a0, a1, a2] at post
      rw [post, hsch, hblk]

theorem call_wp (d : Spec.Seed.Direction) {s₀ : State} (hp : (callX86 d).pre s₀) :
    WP isa (ecbCall d) s₀ fun s' => abiPreserved s₀ s' ∧ (callX86 d).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, sK, sD, sS, hE, fitK, fitD, fitB, fitE⟩ := hp
  obtain ⟨E, hEd⟩ : ∃ E, s₀.gpr .esp = E := ⟨_, rfl⟩
  have hEl := E.isLt
  have hE' := hE
  rw [hEd] at hE sK sD sS
  rw [← stk_eq hE] at sK sD sS
  have hc : CallPre' s₀ E := ⟨hEd, hE, hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitB⟩
  have h4 : 4 ≤ E.toNat := by omega
  have hbody : NoSp (.seq (.block [.mov .eax (.mem (argOp 1)), .mov .ecx (.mem (argOp 2)),
      .mov .edx (.mem (argOp 3)), .mov .ebx (.mem (argOp 4))])
      (.frame (.push [.ebx, .edx, .ecx, .eax]) (blocksCall d) (.pop .eax 4)) : Prog isa) := by
    cases d
    · exact NoSp.of_all (by lit_decide)
    · exact NoSp.of_all (by lit_decide)
  refine WP.frame (rs := [.ebx]) (r := .ebx) (by decide) (by decide) (by decide) (by simp; omega) hbody ?_
  obtain ⟨s₂, e₂, hl⟩ := argLoads_ok hEd hE fitE (by rw [hrd]; simp)
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, WP.mono (inner_wp d hc hl) fun s' ⟨rd', wr', cs, f, post⟩ => ?_⟩)
  have esp' : s'.gpr .esp = E - BitVec.ofNat 32 4 := by rw [cs .esp (by decide), hl.esp]
  have hb4 : Region.Sub ⟨(E - BitVec.ofNat 32 4).setWidth 64, 4⟩ (below E 24) :=
    below_sub (a := 4) (by decide) hE
  have fr' : ∀ r ∈ [(⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩ : Region),
      ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩] ++ [below (s₂.gpr .esp) 20],
      Region.Disjoint ⟨(E - BitVec.ofNat 32 4).setWidth 64, 4⟩ r := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sD.sub_left hb4
    · exact sS.sub_left hb4
    · rw [hl.esp, show (E - BitVec.ofNat 32 4).setWidth 64 = E.setWidth 64 - BitVec.ofNat 64 4 from
        VG.X86.Taint.sub_setWidth h4]
      show Region.Disjoint _ ⟨(E - BitVec.ofNat 32 4 - BitVec.ofNat 32 20).setWidth 64, 20⟩
      rw [BitVec.sub_sub, ← BitVec.ofNat_add, VG.X86.Taint.sub_setWidth (by omega)]
      have := VG.Offset.base_disjoint_below (E.setWidth 64 - BitVec.ofNat 64 4) (n := 20) (k := 4) (by omega)
      rwa [VG.Offset.sub_sub_ofNat] at this
  have ebx' : s'.mem.readW ((s'.gpr .esp).setWidth 64) 32 = s₀.gpr .ebx := by
    rw [esp', f.readW (Region.contains_self _ _) fr' (by decide), hl.mem]
    have := pushed_word (rs := [.ebx]) (s := s₀) (by decide) (by simp; omega) (i := 0) (by decide)
    rw [pushed_esp, hEd] at this
    simpa using this
  have fr₀ : Frame ([(⟨(arg s₀ 1).setWidth 64, 16 * (arg s₀ 2).toNat⟩ : Region),
      ⟨(arg s₀ 3).setWidth 64, 4 * wsSlots⟩] ++ [below E 24]) s₀.mem s'.mem := by
    have f₁ : Frame [below E 24] s₀.mem s₂.mem := by
      rw [hl.mem]
      exact (pushed_frame (rs := [.ebx]) (by decide) (by simp; rw [hEd]; omega)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, by rw [hEd]; exact below_sub (by simp) hE⟩
    refine (f₁.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩).trans (f.sub fun r hr => ?_)
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
        rw [hl.esp]; exact below_inner (by decide) hE⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · show ((s'.setReg .ebx (s'.mem.readW ((s'.gpr .esp).setWidth 64) 32)).setReg .esp (s'.gpr .esp + 4)).gpr .ebx = _
      rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, ebx']
    · rw [popped_gpr _ _ _ (by decide) (by decide), cs _ (by decide)]
      exact hl.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), cs _ (by decide)]
      exact hl.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), cs _ (by decide)]
      exact hl.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [popped_esp, esp', hEd]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem]
    refine fr₀.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dRD
    · exact dRS
    · rw [hEd, stk_eq hE]; exact VG.Offset.base_disjoint_below _ (by omega)
  · show Spec.Seed.blocksAt (popped .ebx 1 s').mem _ _ = _
    rw [popped_mem]; exact post

/-! ## Constant time and the contract -/

/-- The initial taint: `esp` public, the words holding `data` and `scratch`
known to be the base addresses of the writable regions, and 24 bytes of
room below the stack pointer for the frames and the call. -/
def callTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 4 * wsSlots], argLen := 20,
    argBases := [(8, 0), (16, 1)], room := 24 }

theorem callTaint_wf {d : Spec.Seed.Direction} {s : State} (hp : (callX86 d).pre s) :
    VG.X86.Taint.Wf callTaint s := by
  obtain ⟨-, hwr, -, -, dDS, dAD, dAS, dRD, dRS, -, sD, sS, hE, -, fitD, fitB, fitE⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [callTaint]; omega, ?_⟩, ?_⟩ fun _ => ⟨hE, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) dRS dAS
  · intro p hp'
    simp only [callTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact sD
    · exact sS

theorem callTaint_agree {d : Spec.Seed.Direction} {s₁ s₂ : State} (h₁ : (callX86 d).pre s₁)
    (h₂ : (callX86 d).pre s₂) (hpub : (callX86 d).pub s₁ s₂) : VG.X86.Taint.Agree callTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, callTaint_wf h₁, callTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [callTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega), ha 2 (by omega), ha 3 (by omega)]
  · simp only [callTaint] at hk
    rw [show VG.X86.Taint.depth callTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 20) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem call_ct (d : Spec.Seed.Direction) : ConstantTime isa (callX86 d).pre (callX86 d).pub (ecbCall d) := by
  cases d
  · exact VG.Taint.constantTime (A := VG.X86.taint) callTaint (fun _ _ h₁ h₂ hp => callTaint_agree h₁ h₂ hp)
      (by native_taint_decide)
  · exact VG.Taint.constantTime (A := VG.X86.taint) callTaint (fun _ _ h₁ h₂ hp => callTaint_agree h₁ h₂ hp)
      (by native_taint_decide)

theorem call_correct (d : Spec.Seed.Direction) (s : State) (hs : (callX86 d).pre s) :
    ∃ t s', Exec isa (ecbCall d) s t s' ∧ abiPreserved s s' ∧ (callX86 d).post s s' :=
  let ⟨t, s', e, a, p⟩ := call_wp d hs
  ⟨t, s', e, a, p⟩

/-- `callX86` with the argument slots writable, as the signature's contract
has them; the code reads them only (`call_verified` narrows to `callX86`). -/
def wideCall (d : Spec.Seed.Direction) : Contract isa :=
  { callX86 d with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * wsSlots⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
      s.rd = [sched] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint scratch ∧ 24 ≤ (s.gpr .esp).toNat ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 4 * wsSlots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

theorem wideCall_pre (d : Spec.Seed.Direction) (s : State) (h : (wideCall d).pre s) :
    (callX86 d).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  simp only [callX86, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x3000, 0, 0x4000` at `0x8004`. -/
def callSat : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 1088⟩, ⟨0x8004, 16⟩]

theorem wideCall_implies (d : Spec.Seed.Direction) :
    (wideCall d).Implies (Proof.Seed.ecbScratchContract X86.abi d 136 24) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideCall, callX86, ecbX86, Impl.Seed.X86.wsSlots] at h
    sig_split h
    sig_reduce [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideCall, callX86, ecbX86, Impl.Seed.X86.wsSlots]
    sig_simp [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideCall, callX86, ecbX86, Impl.Seed.X86.wsSlots] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideCall, callX86, ecbX86, Impl.Seed.X86.wsSlots]
  · sig_implies_pub [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideCall, callX86, ecbX86, Impl.Seed.X86.wsSlots]
  · sig_implies_sat [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideCall, callX86, ecbX86, Impl.Seed.X86.wsSlots]
      [callSat, arg, argAddr, Mem.readW, Mem.read] using callSat

theorem call_verified (d : Spec.Seed.Direction) :
    Verified X86.target (ecbCall d) (Proof.Seed.ecbScratchContract X86.abi d 136 24) := by
  have hsat := (wideCall_implies d).sat_left
  have narrowSat : ∃ s, (callX86 d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideCall_pre d s hs⟩
  apply Verified.of_implies _ (wideCall_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (call_correct d) (call_ct d) (.refl narrowSat))
    narrowRd narrowWr (wideCall_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    simp only [callX86, wideCall, ecbX86, narrowRd, narrowWr, arg_withRegions, State.withRegions_mem] at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    simp only [callX86, ecbX86, narrowRd, narrowWr, arg_withRegions, State.withRegions_gpr]
    exact h

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no blocks at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem ecbFrameSat_pre (d : Spec.Seed.Direction) : ∃ s, (Spec.Seed.ecbContract X86.abi d 1132).pre s := by
  implies_sat [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [ecbFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using ecbFrameSat

/-- ECB in the direction `d`, with its working space on the stack: 1108
bytes (the 1088 of the working space, the copies of the three argument
slots, the working space's address and the return address of the call of
the code), and the code's 24. -/
theorem ecbCall_framed (d : Spec.Seed.Direction) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1108 3 272 (ecbCall d))
      (Spec.Seed.ecbContract X86.abi d 1132) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 136) (post := Spec.Seed.ecbPost d X86.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 1108) (call_verified d) (by decide) (by cases d <;> lit_decide)
    (by cases d <;> lit_decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.ecbPost_local _ _) (Proof.Seed.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Seed.X86
