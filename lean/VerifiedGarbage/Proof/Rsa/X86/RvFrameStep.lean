module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # A recovery stage through a step that changes ranges of the working space and the stack

`KS.frameStep`: a step that keeps the registers a stage keeps and changes
memory only in ranges `ws` of the working space past its header's first 16
bytes and in the 40 bytes below `sp` (a call of `vg_rsa_mont_mul_at`) keeps
the stage's arrays and header words apart from the ranges, and its arguments.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Bignum.X86.CrtRt (frameR frameR_val32)
open VG.Proof.Dsa.X86 (stackAddress)

/-- An argument through a step that changes ranges of the working space and the 40 bytes below `esp`. -/
theorem _root_.VG.Proof.Bignum.X86.CallArgument.throughFrame {s t : State} {base : Addr} {bytes i : Nat} {v : BitVec 32} {regs : List Reg}
    (h : CallArgument s base bytes i v) (R : CallRoom (s.gpr .esp) base bytes) (K : Keeps regs s t)
    (sp : .esp ∉ regs) {ws : List (Nat × Nat)} (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem)
    (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) (top : (s.gpr .esp).toNat + 4 + 4 * i + 4 ≤ 2 ^ 32) :
    CallArgument t base bytes i v := by
  have low := R.low
  refine h.frame K sp F fun r hr => ?_
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · have ea : (stackAddress s i).toNat = (s.gpr .esp).toNat + (4 + 4 * i) := by
      simp only [stackAddress, VG.X86.addr, VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, BitVec.toNat_add,
        BitVec.toNat_ofNat]
      omega
    have eb : ((s.gpr .esp - BitVec.ofNat 32 40).setWidth 64).toNat = (s.gpr .esp).toNat - 40 := by
      rw [VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega)]
    exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 40) (.inl (by dsimp only; rw [eb, ea]; omega))
      (by dsimp only; rw [eb]; omega) (by dsimp only; rw [ea]; omega)).symm
  · refine h.stack.apart.sub_right ?_
    have := hfit p hp
    have := Offset.sub base (d := p.1) (n := p.2) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

section
variable {g : Geo} {s0 s u : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- The ranges of a frame within the stage's. -/
theorem frameR_stage {ws : List (Nat × Nat)} (hfit : ∀ p ∈ ws, 16 ≤ p.1 ∧ p.1 + p.2 ≤ g.Z) :
    ∀ r ∈ frameR g.B g.sp ws, ∃ r' ∈ stageR g, Region.Sub r r' := by
  intro r hr
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact ⟨_, by simp [frameR], fun _ h => h⟩
  · refine ⟨⟨off g.B 16, g.Z - 16⟩, by simp [frameR], ?_⟩
    have := hfit p hp
    exact Offset.sub g.B (d := p.1) (n := p.2) (e := 16) (k := g.Z - 16) (by omega) (by omega)

theorem KS.frameStep (h : KS g s0 A live AW liveW V ls s) (K : Keeps opRegs s u) {ws : List (Nat × Nat)}
    (F : Frame (frameR g.B g.sp ws) s.mem u.mem) (hfit : ∀ p ∈ ws, 16 ≤ p.1 ∧ p.1 + p.2 ≤ g.Z)
    (hA : ∀ j ∈ live, ∀ p ∈ ws, arr g.w j + 4 * g.w ≤ p.1 ∨ p.1 + p.2 ≤ arr g.w j)
    (hAW : ∀ j ∈ liveW, ∀ p ∈ ws, arr g.W j + 4 * g.W ≤ p.1 ∨ p.1 + p.2 ≤ arr g.W j)
    (hV : ∀ d ∈ ls, ∀ p ∈ ws, d + 4 ≤ p.1 ∨ p.1 + p.2 ≤ d) :
    KS g s0 A live AW liveW V ls u := by
  have nw := h.ws.workspace.nowrap
  have header := h.ws.hdr_le
  have esp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have R : CallRoom (s.gpr .esp) g.B g.Z := by rw [h.sp]; exact h.room
  have F' : Frame (frameR g.B (s.gpr .esp) ws) s.mem u.mem := by rw [h.sp]; exact F
  have hfit' : ∀ p ∈ ws, p.1 + p.2 ≤ g.Z := fun p hp => (hfit p hp).2
  have argTop : ∀ {i : Nat} {v : BitVec 32}, CallArgument s g.B g.Z i v → i ≤ 11 →
      (s.gpr .esp).toNat + 4 + 4 * i + 4 ≤ 2 ^ 32 := fun _ hi => by
    have := h.top; rw [h.sp]; omega
  obtain ⟨a, la, ea, ca⟩ := h.rt.lenArg
  refine ⟨⟨h.rt.ws.rest K (by decide) (by decide),
      ⟨a, la, ea, ca.throughFrame R K (by decide) F' hfit' (argTop ca (by decide))⟩,
      h.rt.wsArg.throughFrame R K (by decide) F' hfit' (argTop h.rt.wsArg (by decide)), h.rt.lenLe, h.rt.layLen⟩,
    h.lower, h.upper, h.frame.trans (F.sub (frameR_stage hfit)), by rw [esp]; exact h.sp, h.room, h.top,
    h.wsLen.throughFrame R K (by decide) F' hfit' (argTop h.wsLen (by decide)), h.z8, h.rest.trans K,
    fun j hj => ?_, fun j hj => ?_, fun d hd => ?_, h.live_lt, h.liveW_lt, h.ls_ok, h.start⟩
  · have fit := h.ws.arr_fit (h.live_lt j hj)
    simp only [S] at fit
    rw [← h.arrs j hj]
    exact frameR_val32 F h.room nw (by omega) (hA j hj) hfit'
  · have fit := h.wsW.arr_fit (h.liveW_lt j hj)
    simp only [S] at fit
    rw [← h.arrsW j hj]
    exact frameR_val32 F h.room nw (by omega) (hAW j hj) hfit'
  · have ok := h.ls_ok d hd
    rw [← h.sl d hd]
    have e := frameR_val32 (d := d) (k := 1) F h.room nw (by unfold SlotOk at ok; unfold hdr at ok header; omega)
      (fun p hp => by have := hV d hd p hp; omega) hfit'
    simpa only [slot, val32, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero] using e

end
end VG.Proof.Rsa.X86.Recover
