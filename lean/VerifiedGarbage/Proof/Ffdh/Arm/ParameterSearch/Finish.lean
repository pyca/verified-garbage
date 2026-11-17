module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Isa

/-! ### `Ffdh.Arm.ParameterSearch.FinishMemory`, which this module and modules that import it used -/

section

/-! The final u64 consumption store preserves the prime, controller and saved registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

def savedSlots : List (Reg × Nat) := [(.r4, 0), (.r9, 4), (.r10, 8), (.r11, 12), (.r12, 16), (.lr, 20)]

structure ResultPost (p : SearchParams) (result : Spec.Ffdh.ParameterSearchResult) (s : State) : Prop where
  status : s.gpr .r0 = BitVec.ofNat 32 result.status
  output : searchOutput p result s.mem
  used : Spec.Rsa.wordsAt s.mem (State.addr p.c.usedPtr) 1 = [BitVec.ofNat 64 result.used]
  policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 = searchPolicy p result

structure FinishInput (p : SearchParams) (original : State) (result : Spec.Ffdh.ParameterSearchResult)
    (s : State) : Prop extends SearchDone p result s where
  saved : Spill.Saved s.mem (State.addr s.sp) original.gpr savedSlots
  sp : s.sp = original.sp - 24#32
  stackFits : 24 ≤ original.sp.toNat
  kept : ∀ r ∈ [.r5, .r6, .r7, .r8], s.gpr r = original.gpr r

theorem SearchDone.used_buffer {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} (h : SearchDone p result s) : VG.Proof.Ffdh.Arm.OutputBuffer p.c.usedPtr 8 s :=
  ⟨p.c.usedFits, ⟨_, h.buffers.used.2, Region.contains_self _ _⟩⟩

theorem SearchDone.output_after_used {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} {m : Mem} (h : SearchDone p result s)
    (frame : Frame [⟨State.addr p.c.usedPtr, 8⟩] s.mem m) : searchOutput p result m := by
  unfold searchOutput at *
  have fit : p.c.out.toNat + p.c.length ≤ 2 ^ 32 := p.c.outputFits
  exact (VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by omega_using [fit])
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact p.c.outputUsed)).trans h.output

theorem SearchDone.policy_after_used {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult}
    {s : State} {m : Mem} (h : SearchDone p result s)
    (frame : Frame [⟨State.addr p.c.usedPtr, 8⟩] s.mem m) :
    Spec.Rsa.wordsAt m (State.addr p.control) 4 = searchPolicy p result := by
  have same : Spec.Rsa.wordsAt m (State.addr p.control) 4 =
      Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 := by
    unfold Spec.Rsa.wordsAt
    apply List.map_congr_left
    intro j hj
    have bound : j < 4 := List.mem_range.mp hj
    exact frame.readW (r := ⟨State.addr p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound]))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact p.controlUsed) (by decide)
  exact same.trans h.policy

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! The native controller writes its result and restores the complete AAPCS
callee-saved register set before its final frame pop. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/FinishHead.lean`, which only this module imported.
section

/-! The controller returns its status and writes a full u64 entropy-consumption count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord usedMem)

theorem finishHead_ok (s : State) {base ptr : BitVec 32} {count status : Nat}
    (h : Controller base s) (output : OutputBuffer ptr 8 s)
    (pointer : lowWord s.mem base 6 = ptr) (used : lowWord s.mem base 4 = BitVec.ofNat 32 count)
    (result : lowWord s.mem base 13 = BitVec.ofNat 32 status) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r2 4,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 13, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 status ∧ t.mem = usedMem s.mem ptr (BitVec.ofNat 32 count)) ∧
      Rest [.r0, .r1, .r2, .r3] s t := by
  refine withRest_all [.r0, .r1, .r2, .r3] ?_ (by rfl) (by rfl)
  have write0 : InRegions s.wr (State.addr ptr) 4 := by
    simpa only [BitVec.add_zero] using
      CallLay.inRegions_sub output.writable (off := 0) (by decide : 0 + 4 ≤ 8) (by decide)
  have write4 : InRegions s.wr (off (State.addr ptr) 4) 4 :=
    CallLay.inRegions_sub output.writable (by decide : 4 + 4 ≤ 8) (by decide)
  have addr4 : State.addr (ptr + 4#32) = off (State.addr ptr) 4 := VG.Arm.addr_add (by have := output.fits; omega)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord usedMem at *
  ffrun [h.addr (by decide : 6 < 16), h.addr (by decide : 4 < 16), h.addr (by decide : 13 < 16),
    h.read (by decide : 6 < 16), h.read (by decide : 4 < 16), h.read (by decide : 13 < 16),
    pointer, used, result, BitVec.add_zero, addr4, write0, write4]
  rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (usedMem_frame usedMem_words)

def finishRestoreSlots : List (Reg × Nat) := [(.r9, 4), (.r10, 8), (.r11, 12), (.lr, 20)]

private theorem wordsAt_lost {m m' : Mem} {rs : List Region} (frame : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ w ∈ rs, (⟨a, 8 * n⟩ : Region).Disjoint w) (fit : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' a n = Spec.Rsa.wordsAt m a n := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro j hj
  have bound : j < n := List.mem_range.mp hj
  exact frame.readW (r := ⟨a, 8 * n⟩) (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound, fit]))
    hd (by decide)

theorem finish_ok {p : SearchParams} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : FinishInput p original result s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.finish) s fun t =>
      ∀ m u, Frame [⟨State.addr (original.sp - BitVec.ofNat 32 24), 24⟩] t.mem m →
        abiPreserved original { popped .r4 24 t with mem := m, unknowns := u } ∧
          ResultPost p result { popped .r4 24 t with mem := m, unknowns := u } := by
  change WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r2 4,
    VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 13, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4] ++
    finishRestoreSlots.map (fun e => Instr.ldrSp e.1 e.2))) s _
  rw [WP.block_append_iff]
  refine WP.mono (finishHead_ok s h.buffers.controller h.toSearchDone.used_buffer h.usedPtr h.used h.status) ?_
  rintro u ⟨⟨status, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.c.usedPtr, 8⟩] s.mem u.mem := by rw [mem]; exact usedMem_frame _ _ _
  have saved : Spill.Saved u.mem (State.addr u.sp) original.gpr savedSlots := by
    rw [rest.sp]
    apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simpa only [BitVec.add_zero, Nat.sub_zero] using
      (h.buffers.stackSeparate ⟨State.addr p.c.usedPtr, 8⟩ (by simp)).1
  have read : InRegions (u.rd ++ u.wr) (State.addr u.sp) 24 := by
    rw [rest.rd, rest.wr, rest.sp]
    exact h.buffers.stack
  have fit : u.sp.toNat + 24 ≤ 2 ^ 32 := by
    rw [rest.sp, h.sp, FrameStack.sub_toNat' h.stackFits]
    have := original.sp.isLt
    omega_using []
  refine WP.mono (restoreSlots_ok finishRestoreSlots u original.gpr (by decide) fit read
    (by intro e he
        simp only [finishRestoreSlots, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    (by intro e he
        apply saved e
        simp only [finishRestoreSlots, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl <;> simp [savedSlots])) ?_
  rintro t ⟨restored, memT, restT⟩ m₀ u₀ hfl
  have lost : Frame [⟨State.addr s.sp, 24⟩] u.mem m₀ := by rw [← memT, h.sp]; exact hfl
  have sep := h.buffers.stackSeparate
  have popped4 : (popped .r4 24 t).gpr .r4 = original.gpr .r4 := by
    change t.mem.readW (State.addr t.sp) 32 = _
    rw [memT, restT.sp]
    simpa only [BitVec.add_zero] using saved (.r4, 0) (by simp [savedSlots])
  have kept (r : Reg) (member : r ∈ [.r5, .r6, .r7, .r8]) :
      (popped .r4 24 t).gpr r = original.gpr r := by
    rw [popped_gpr (by cases r <;> simp_all [finishRestoreSlots])]
    exact (restT.gpr r (by cases r <;> simp_all [finishRestoreSlots])).trans
      ((rest.gpr r (by cases r <;> simp_all [finishRestoreSlots])).trans (h.kept r member))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> dsimp only
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact popped4
    · exact kept .r5 (by simp)
    · exact kept .r6 (by simp)
    · exact kept .r7 (by simp)
    · exact kept .r8 (by simp)
    · rw [popped_gpr (by decide : Reg.r9 ≠ .r4)]; exact restored (.r9, 4) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.r10 ≠ .r4)]; exact restored (.r10, 8) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.r11 ≠ .r4)]; exact restored (.r11, 12) (by simp [finishRestoreSlots])
    · rw [popped_gpr (by decide : Reg.lr ≠ .r4)]; exact restored (.lr, 20) (by simp [finishRestoreSlots])
  · rw [popped_sp, restT.sp, rest.sp, h.sp, BitVec.sub_add_cancel]
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r4)]
    exact (restT.gpr .r0 (by simp [finishRestoreSlots])).trans status
  · have before := h.toSearchDone.output_after_used frame
    unfold searchOutput at before ⊢
    have fit : p.c.out.toNat + p.c.length ≤ 2 ^ 32 := p.c.outputFits
    exact (VG.Proof.Bignum.Arm.rsa_bytes_frame lost (by omega_using [fit])
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (sep _ (by simp)).1.symm)).trans before
  · rw [wordsAt_lost (n := 1) lost
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (sep _ (by simp)).1.symm) (by decide), mem]
    exact usedMem_words _ _ _ (by have := h.usedBound; have := p.c.tapeCount; omega_arith)
  · rw [wordsAt_lost (n := 4) lost (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ((sep ⟨State.addr p.control, 128⟩ (by simp)).1.symm.sub_left fun _ hc => by
        simp only [Region.Contains] at hc ⊢; omega_using [hc])) (by decide)]
    exact h.toSearchDone.policy_after_used frame

end VG.Proof.Ffdh.Arm.ParameterSearch
