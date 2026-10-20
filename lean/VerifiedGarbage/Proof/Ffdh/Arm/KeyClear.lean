module

import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Arm.Isa

/-! A rejected scalar attempt clears a full private or public output encoding. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyClearArgs_ok (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots) :
    WP isa (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = p.slotValue slot ∧ t.gpr .lr = BitVec.ofNat 32 p.k ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
      Rest [.r0, .r2, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  refine withRest [.r0, .r2, .lr] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  ffrun [(by omega : slot < 4096), addr slot fit, addr 32 (by decide), h.locals.read fit, h.locals.read (d := 32) (by decide),
    h.saved slot hs, h.saved 32 hk, Inputs.slotValue]

theorem keyClear_ok (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (output : OutputBuffer (p.slotValue slot) p.k s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput slot) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr (p.slotValue slot)) p.k = List.replicate p.k 0 ∧
      Frame [⟨State.addr (p.slotValue slot), p.k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput, WP.seq_iff]
  refine WP.mono (keyClearArgs_ok s slot h fit hs hk) ?_
  rintro u ⟨⟨ptr, count, zero, mem⟩, restU⟩
  refine WP.mono (zeroBuffer_ok false u (by have := p.minLength; omega) (by have := p.maxLength; omega)
    output.fits (by rw [restU.wr]; exact output.writable) zero (src := u.gpr .r1) rfl ptr count) ?_
  rintro t ⟨bytes, _, _, frame, rest⟩
  exact ⟨bytes, by rw [mem] at frame; exact frame, (restU.mono (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Ffdh.Arm
