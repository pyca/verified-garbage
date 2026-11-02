module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! FFDH exponentiation uses the same native three-bit window as private RSA. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Mont (off)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt arrAt)

structure PowerInput (base src ep : BitVec 32) (len w M : Nat)
    (bb eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M
  baseBytes : Octets base src len bb s
  exponentBytes : Octets base ep len eb s
  basePositive : 0 < bb.length
  baseFits : bb.length ≤ 8 * w
  exponentPositive : 0 < eb.length
  exponentFits : eb.length < 2 ^ 32
  source : s.gpr .r4 = src
  count : s.gpr .r6 = BitVec.ofNat 32 bb.length
  exponent : s.gpr .r1 = ep
  exponentCount : s.gpr .r2 = BitVec.ofNat 32 eb.length

structure PowerPrepared (base src ep : BitVec 32) (len w M : Nat)
    (bb eb : List Byte) (s : State) : Prop where
  input : PowerInput base src ep len w M bb eb s
  pointer : s.mem.readW (off (State.addr base) 128) 32 = ep
  count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 eb.length

theorem powerControls_ok (s : State) {base src ep : BitVec 32} {len w M : Nat} {bb eb : List Byte}
    (h : PowerInput base src ep len w M bb eb s) :
    WP isa (.block VG.Impl.Bignum.Arm.expControls) s fun t =>
      PowerPrepared base src ep len w M bb eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [] s t := by
  refine WP.mono (expControls_ok s h.ready) ?_
  rintro t ⟨ready, pointer, count, arrays, frame, rest⟩
  refine ⟨⟨⟨ready, (arrays 0 (by decide)).trans h.modulus, h.odd,
    (arrays 4 (by decide)).trans h.r2, h.baseBytes.after_workspace frame rest,
    h.exponentBytes.after_workspace frame rest, h.basePositive, h.baseFits,
    h.exponentPositive, h.exponentFits,
    (rest.gpr .r4 (by simp)).trans h.source, (rest.gpr .r6 (by simp)).trans h.count,
    (rest.gpr .r1 (by simp)).trans h.exponent, (rest.gpr .r2 (by simp)).trans h.exponentCount⟩,
    pointer.trans h.exponent, count.trans h.exponentCount⟩, frame, rest⟩

theorem powerBase_ok (s : State) {base src ep : BitVec 32} {len w M : Nat} {bb eb : List Byte}
    (prepared : PowerPrepared base src ep len w M bb eb s) :
    WP isa (VG.Impl.Bignum.Arm.importOperand 1) s fun t =>
      ExpPhaseInput base ep len w M (Spec.Rsa.os2ip bb) eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have h := prepared.input
  refine WP.mono (importOperand_ok s h.ready (by decide : 1 < 8) (by decide)
    h.basePositive h.baseFits h.baseBytes.fits h.baseBytes.readable h.baseBytes.separate h.source h.count) ?_
  rintro t ⟨ready, value, keeps, frame, rest⟩
  rw [h.baseBytes.bytes] at value
  have ebT := h.exponentBytes.after_workspace frame rest
  have bound : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have modT := (keeps_array_num keeps bound
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide : 0 ≠ 1)).trans h.modulus
  have r2T := (keeps_array_num keeps bound
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide : 4 ≠ 1)).trans h.r2
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at bound; omega
  refine ⟨⟨ready, modT, h.odd, value,
    by rw [r2T]; exact Nat.mod_lt _ (by have := h.ready.modulus; rw [h.modulus] at this; omega),
    by rw [r2T, Nat.mod_mod, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega],
    (keeps_header_readW keeps size (d := 128) (bits := 32) (by decide)).trans prepared.pointer,
    (keeps_header_readW keeps size (d := 132) (bits := 32) (by decide)).trans prepared.count,
    h.exponentPositive, h.exponentFits, ebT.fits, ebT.readable, ebT.separate, ebT.byte⟩, frame, rest⟩

theorem powerImport_ok (s : State) {base src ep : BitVec 32} {len w M : Nat} {bb eb : List Byte}
    (h : PowerInput base src ep len w M bb eb s) :
    WP isa VG.Impl.Ffdh.Arm.powerImport s fun t =>
      ExpPhaseInput base ep len w M (Spec.Rsa.os2ip bb) eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.powerImport, WP.seq_iff]
  refine WP.mono (powerControls_ok s h) ?_
  rintro u ⟨prepared, frameU, restU⟩
  refine WP.mono (powerBase_ok u prepared) ?_
  rintro t ⟨input, frameT, restT⟩
  exact ⟨input, frameU.trans frameT, (restU.mono (by simp [roundClobbers])).trans restT⟩

theorem power_ok (s : State) {base src ep : BitVec 32} {len w M : Nat} {bb eb : List Byte}
    (h : PowerInput base src ep len w M bb eb s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa VG.Impl.Ffdh.Arm.power s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip bb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.power, WP.seq_iff]
  refine WP.mono (powerImport_ok s h) ?_
  rintro u ⟨input, frameU, restU⟩
  refine WP.mono (windowExpPhase_ok u input fits) ?_
  rintro t ⟨ready, result, modulus, r2, one, frameT, restT⟩
  exact ⟨ready, result, modulus, r2, one, frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm
