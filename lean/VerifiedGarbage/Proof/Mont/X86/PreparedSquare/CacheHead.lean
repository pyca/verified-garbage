module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.CacheTail
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Read the public workspace and scratch pointer before saving registers -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

def cacheHead : List Instr := [.mov .eax (.mem (rawArg 0)), .mov .ecx (.mem (at_ .eax 80))]

theorem cacheHead_ok {s : State} {W : Addr} {L S : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : RawArgs s W L A) (base : (A 0).toNat = W.toNat)
    (scratch : w32 s.mem W 80 = (W.toNat + S) % 2 ^ 32) (header : 84 ≤ L) :
    WP isa (.block cacheHead) s fun t =>
      t.gpr .eax = A 0 ∧ t.gpr .ecx = BitVec.ofNat 32 (W.toNat + S) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold cacheHead
  refine wp_movS (ha.read 0 (by decide)) fun s1 U1 _ => ?_
  have ptr : PtrAt s1 W .eax 0 := by
    rw [PtrAt, U1.gpr, base, Nat.add_zero, Nat.mod_eq_of_lt]
    have := hw.nowrap
    omega
  refine wp_movS (readSrc_ptr (hw.of_keeps U1.keeps) ptr (d := 80) header) fun t U2 _ => WP.block_nil ?_
  refine ⟨(U2.other .eax (by decide)).trans U1.gpr, ?_, U2.mem.trans U1.mem,
    (U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))⟩
  rw [U2.gpr, U1.mem, Nat.zero_add]
  apply BitVec.eq_of_toNat_eq
  exact scratch

theorem cacheHead_relCT : RelCT isa (VG.X86.Taint.Agree (argTaint [] 24)) (.block cacheHead)
    (VG.X86.Taint.Agree (argTaint [.eax] 24)) :=
  erased_relCT _ _ (.block []) rfl rfl rfl rfl

theorem cacheRest_relCT : RelCT isa (VG.X86.Taint.Agree (argTaint [.eax, .ecx] 24))
    (.block (saveCode ++ cacheTail)) (VG.X86.Taint.Agree (argTaint [] 24)) :=
  erased_relCT _ _ (.block []) rfl rfl rfl rfl

theorem arg_republish {s t : State} {rs out : List Reg}
    (h : VG.X86.Taint.Agree (argTaint rs 24) s t)
    (regs : ∀ r ∈ out, s.gpr r = t.gpr r) : VG.X86.Taint.Agree (argTaint out 24) s t := by
  have wf {s : State} (H : VG.X86.Taint.Wf (argTaint rs 24) s) : VG.X86.Taint.Wf (argTaint out 24) s :=
    ⟨H.lens, H.bases, H.wbases, H.args, H.argBases, H.stk, H.frames, H.room⟩
  refine ⟨⟨?_, fun h => nomatch h⟩, h.wr, wf h.wf₁, wf h.wf₂, h.ok, h.slots, h.sp, h.argMem⟩
  intro r hr
  simp only [argTaint, RegSet.mem_ofList, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact h.sp (by change 0 < 24; decide)
  · exact regs r hr

end VG.Proof.Mont.X86.PreparedSquare
