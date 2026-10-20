module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
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
open VG.Spec.Rsa.Mont (numAt arrAt)

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

theorem power_ok (s : State) {base src ep : BitVec 32} {len w M : Nat} {bb eb : List Byte}
    (h : PowerInput base src ep len w M bb eb s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa VG.Impl.Ffdh.Arm.power s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip bb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.power, WP.seq_iff]
  refine WP.mono (expControls_ok s h.ready) ?_
  rintro u ⟨readyU, epU, countU, arraysU, frameU, restU⟩
  rw [h.exponent] at epU
  rw [h.exponentCount] at countU
  rw [WP.seq_iff]
  have bbU := h.baseBytes.after_workspace frameU restU
  have ebU := h.exponentBytes.after_workspace frameU restU
  refine WP.mono (importOperand_ok u readyU (by decide : 1 < 8) (by decide)
    h.basePositive h.baseFits bbU.fits bbU.readable bbU.separate
    ((restU.gpr .r4 (by simp)).trans h.source) ((restU.gpr .r6 (by simp)).trans h.count)) ?_
  rintro v ⟨readyV, value, keepsV, frameV, restV⟩
  rw [bbU.bytes] at value
  have ebV := ebU.after_workspace frameV restV
  have bound : arrAt w 8 ≤ 8 * len := readyU.width ▸ readyU.layout.2.2.1
  have modV := (keeps_array_num keepsV bound
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide : 0 ≠ 1)).trans
    ((arraysU 0 (by decide)).trans h.modulus)
  have r2V := (keeps_array_num keepsV bound
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide : 4 ≠ 1)).trans
    ((arraysU 4 (by decide)).trans h.r2)
  have size : 256 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at bound; omega
  have input : ExpPhaseInput base ep len w M (Spec.Rsa.os2ip bb) eb v :=
    ⟨readyV, modV, h.odd, value, by rw [r2V]; exact Nat.mod_lt _ (by have := h.ready.modulus; rw [h.modulus] at this; omega),
      by rw [r2V, Nat.mod_mod, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega],
      (keeps_header_readW keepsV size (d := 128) (bits := 32) (by decide)).trans epU,
      (keeps_header_readW keepsV size (d := 132) (bits := 32) (by decide)).trans countU,
      h.exponentPositive, h.exponentFits, ebV.fits, ebV.readable, ebV.separate, ebV.byte⟩
  refine WP.mono (windowExpPhase_ok v input fits) ?_
  rintro t ⟨ready, result, modulus, r2, one, frameT, restT⟩
  exact ⟨ready, result, modulus, r2, one, frameU.trans (frameV.trans frameT),
    (restU.mono (by simp [roundClobbers])).trans (restV.trans restT)⟩

end VG.Proof.Ffdh.Arm
