module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Equal
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Imported key consistency is checked by native exponentiation and full-width equality. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def privateMatchFlag (p : Inputs) (yb xb : List Byte) : BitVec 32 :=
  if Spec.Rsa.powMod p.G (Spec.Rsa.os2ip xb) p.P = Spec.Rsa.os2ip yb then 1 else 0

theorem privateMatch_ok (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic s fun t =>
      t.gpr .r0 = privateMatchFlag p yb xb ∧ Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic, WP.seq_iff]
  refine WP.mono (powerAt_ok s 56 40 44 h stable h56 h40 h44 h32 ready modulus odd r2
    h.gBytes p.gLength scalar positive fits count) ?_
  rintro u ⟨contextU, readyU, power, _, _, _, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 36 32 contextU stable h36 h32 readyU (by decide) (by decide)
    (value.after_workspace frameU restU) (by rw [length]; have := p.minLength; omega)
    (by rw [length]; exact p.width.2.2.2.1) (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro v ⟨_, readyV, y, keepsV, frameV, _⟩
  have fit : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have powerV := (keeps_array_num keepsV fit op6 (by decide)).trans power
  rw [WP.seq_iff]
  refine WP.mono (equal_ok v readyV op6 op1) ?_
  rintro w ⟨_, flag, _, frameW, _⟩
  rw [powerV, y] at flag
  refine WP.mono (finishFlag_ok w) ?_
  rintro t ⟨⟨result, memT⟩, _⟩
  exact ⟨by rw [result, flag]; rfl, by rw [memT]; exact (frameU.trans frameV).trans frameW⟩

end VG.Proof.Ffdh.Arm
