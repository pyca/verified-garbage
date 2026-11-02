module
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpBitsCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHead
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.ExpState
meta import VerifiedGarbage.Impl.Bignum.Arm.Exp
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ExpBitsCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHead
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Processing one exponent byte reveals only that public byte and its address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

structure ExpByteInput (base ep : BitVec 32) (len w M x E : Nat) (b : Byte) (s : State) : Prop where
  power : ExpState base len w M x E s
  pointer : s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep
  read : InRegions (s.rd ++ s.wr) (State.addr ep) 1
  byte : s.mem (State.addr ep) = b

theorem expByte_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 E : Nat} {b : Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => ExpByteInput base ep len w M1 x1 E b s ∧
      ExpByteInput base ep len w M2 x2 E b t ∧ s.sp = t.sp)
      (.seq expByteHead (.seq expBits (.block expByteNext))) (fun _ _ => True) := by
  let P := fun (s t : State) => ExpByteInput base ep len w M1 x1 E b s ∧
    ExpByteInput base ep len w M2 x2 E b t ∧ s.sp = t.sp
  have wpHead (s : State) {M x : Nat} (h : ExpByteInput base ep len w M x E b s) :
      WP isa expByteHead s (ExpBitState base len w M x E b.toNat 0) := by
    have head := expByteHead_ok s h.power h.pointer h.read
    rw [h.byte] at head
    exact WP.mono head (fun _ h => h.1)
  have head := (relCT_keep_sp (expByteHead_ct.mono (P' := P)
    (fun _ _ h => ⟨⟨h.1.power.ready, h.1.pointer⟩, ⟨h.2.1.power.ready, h.2.1.pointer⟩⟩)
    (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpHead s h.1, wpHead t h.2.1⟩)
  have wpBits (s : State) {M x : Nat} (h : ExpBitState base len w M x E b.toNat 0 s) :
      WP isa expBits s (ExpState base len w M x (256 * E + b.toNat)) :=
    WP.mono (expBits_ok s h b.isLt) (fun _ h => h.1)
  have bits := ((expBits_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E := E) fit b.isLt).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpBitState base len w M1 x1 E b.toNat 0 s ∧
      ExpBitState base len w M2 x2 E b.toNat 0 t)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)).wp
    (fun s t h => ⟨wpBits s h.2.1, wpBits t h.2.2⟩)
  have next : RelCT isa (fun s t => True ∧ ExpState base len w M1 x1 (256 * E + b.toNat) s ∧
      ExpState base len w M2 x2 (256 * E + b.toNat) t) (.block expByteNext) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.ready.ptr.trans h.2.2.ready.ptr.symm
  exact head.seq (bits.seq next)

end VG.Proof.Bignum.Arm
