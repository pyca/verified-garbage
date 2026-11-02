module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! Apply a native mask to one occupied witness word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (arrAt)

theorem witnessMaskStore_ok {s : State} {base : BitVec 32} {capacity w j : Nat}
    (ready : ArithmeticReady base capacity w s) (bound : j < 2 * w)
    (index : s.gpr .r5 = BitVec.ofNat 32 j) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore) s fun t =>
      (t.mem = s.mem.writeW (off (State.addr base) (arrAt w 1 + 4 * j))
        (s.mem.readW (off (State.addr base) (arrAt w 1 + 4 * j)) 32 &&& s.gpr .r7) ∧
        t.gpr .r0 = base) ∧ Rest [.r0, .r3, .r4] s t := by
  have fits : arrAt w 8 ≤ 8 * capacity := ready.width ▸ ready.layout.2.2.1
  have arrayFit := array_end_le (w := w) (j := 1) (k := 8) (by decide)
  have size : 128 ≤ 8 * capacity := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base ready.workspace.nowrap (Nat.le_refl _) ready.layout
  rw [ready.width] at header
  have pointer := header.array 1 (by decide)
  have addr72 : State.addr (base + 72#32) = off (State.addr base) 72 :=
    VG.Arm.addr_add (by have := ready.workspace.nowrap; omega)
  have shifted : BitVec.ofNat 32 j <<< 2 = BitVec.ofNat 32 (4 * j) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 j * BitVec.ofNat 32 4 = _
    rw [BitVec.ofNat_mul_ofNat, Nat.mul_comm]
  have address : State.addr (base + BitVec.ofNat 32 (arrAt w 1) + BitVec.ofNat 32 (4 * j)) =
      off (State.addr base) (arrAt w 1 + 4 * j) := by
    rw [Offset.add_add]
    exact VG.Arm.addr_add (by have := ready.workspace.nowrap; omega)
  have readHeader := ready.workspace.read (off := 72) (by omega)
  have read := ready.workspace.read (off := arrAt w 1 + 4 * j) (by omega)
  have write := ready.workspace.write (off := arrAt w 1 + 4 * j) (by omega)
  refine withRest_all [.r0, .r3, .r4] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore
  ffrun [BitVec.add_zero, ready.stackRead, ready.saved, addr72, readHeader, pointer,
    index, shifted, address, read, write]

end VG.Proof.Ffdh.Arm.ParameterCandidate
