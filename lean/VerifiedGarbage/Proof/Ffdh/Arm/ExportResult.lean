module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Export a shared value through the saved output pointer, at the full modulus width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem exportResultArgs_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block [.mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 32]) s fun t =>
      (t.gpr .r2 = 6 ∧ t.gpr .r4 = p.output ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧ t.mem = s.mem) ∧
      Rest [.r2, .r4, .r6] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r4 := h.locals.read (d := 4) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have v4 := h.saved 4 h4
  have v32 := h.saved 32 h32
  refine withRest_all [.r2, .r4, .r6] ?_ (by rfl) (by rfl)
  ffrun [addr 4 (by decide), addr 32 (by decide), r4, r32, v4, v32, Inputs.slotValue, off]

theorem exportResult_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (output : OutputBuffer p.output p.k s)
    (separate : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (valueFit : numAt s.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k)) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        Spec.Rsa.i2osp (numAt s.mem (State.addr p.base) p.w 6) p.k ∧
      Frame [⟨State.addr p.output, p.k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult, WP.seq_iff]
  refine WP.mono (exportResultArgs_ok s h h4 h32) ?_
  rintro u ⟨⟨index, dst, count, mem⟩, rest⟩
  have readyU := ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans ready.ptr)
  refine WP.mono (exportBE_ok u readyU.workspace readyU.layout readyU.width (by decide : 6 < 8)
    (by have := p.minLength; omega) p.width.2.2.2.1 (by rw [mem]; exact valueFit) output.fits
    (by rw [rest.wr]; exact output.writable) separate readyU.ptr index dst count) ?_
  rintro t ⟨value, frame, _, _, restT⟩
  rw [mem] at value frame
  exact ⟨value, frame, (rest.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Ffdh.Arm
