module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Mask the full shared-value encoding and reload the saved status without branching. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure MaskOutputInput (p : Inputs) (flag : BitVec 32) (s : State) : Prop where
  locals : Locals p.base p.len s
  output : OutputBuffer p.output p.k s
  separate : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩
  dst : s.mem.readW (off (State.addr s.sp) 4) 32 = p.output
  count : s.mem.readW (off (State.addr s.sp) 32) 32 = BitVec.ofNat 32 p.k
  result : s.mem.readW (off (State.addr s.sp) 64) 32 = flag

theorem maskOutputArgs_ok (s : State) {p : Inputs} {flag : BitVec 32} (h : MaskOutputInput p flag s) :
    WP isa (.block [.ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
      .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)]) s fun t =>
      (t.gpr .r0 = p.output ∧ t.gpr .lr = BitVec.ofNat 32 p.k ∧ t.gpr .r2 = 0 - flag ∧ t.mem = s.mem) ∧
      Rest [.r0, .r2, .r3, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r4 := h.locals.read (d := 4) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have r64 := h.locals.read (d := 64) (by decide)
  refine withRest [.r0, .r2, .r3, .lr] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [.ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
        .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)] : Prog isa)).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  ffrun [addr 4 (by decide), addr 32 (by decide), addr 64 (by decide), r4, r32, r64,
    h.dst, h.count, h.result, off]

theorem maskOutput_ok (s : State) {p : Inputs} {flag : BitVec 32} (h : MaskOutputInput p flag s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput s fun t =>
      t.gpr .r0 = flag ∧ Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        (Spec.Rsa.bytesAt s.mem (State.addr p.output) p.k).map (· &&& (0 - flag).setWidth 8) ∧
      Frame [⟨State.addr p.output, p.k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput, WP.seq_iff]
  refine WP.mono (maskOutputArgs_ok s h) ?_
  rintro u ⟨⟨ptr, count, mask, memU⟩, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (maskBuffer_ok u (by have := p.minLength; omega) (by have := p.maxLength; omega)
    h.output.fits (by rw [restU.wr]; exact h.output.writable) ptr count) ?_
  rintro v ⟨bytes, frameV, restV⟩
  have rest : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    (restV.mono (by simp [roundClobbers]))
  have localV := h.locals.after rest
  have addr : State.addr (v.sp + BitVec.ofNat 32 64) = off (State.addr v.sp) 64 :=
    VG.Arm.addr_add (by have := localV.space.nowrap; omega)
  have kept := frameV.readW (w := 32) (r := ⟨off (State.addr s.sp) 64, 4⟩) (Region.contains_self _ _) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.separate.sub_left (Offset.sub_base _ (by decide))) (by decide)
  refine wp_loadStack (a := off (State.addr v.sp) 64) (by decide) addr (localV.read (d := 64) (by decide)) fun t loaded => WP.block_nil ?_
  have finalRest : Rest roundClobbers s t := (rest.mono (by simp [roundClobbers])).trans
    ((loaded.rest (by simp : Reg.r0 ∈ [.r0])).mono (by simp [roundClobbers]))
  refine ⟨?_, ?_, ?_, finalRest⟩
  · rw [loaded.gpr, rest.sp, kept, memU]
    exact h.result
  · rw [mask, memU] at bytes
    rw [loaded.mem]
    exact bytes
  · rw [memU] at frameV
    rw [loaded.mem]
    exact frameV

end VG.Proof.Ffdh.Arm
