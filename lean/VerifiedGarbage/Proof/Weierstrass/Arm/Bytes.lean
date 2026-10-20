module
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Bswap

import VerifiedGarbage.Proof.Framework.AddrArith
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Impl.Mont.Arm
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Weierstrass.Arm.Mont
import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Impl.Weierstrass.Arm
import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Short Weierstrass curves on 32-bit ARM: big-endian words

What the loads and stores of big-endian numbers (`BytesLen.lean`) share:
`rev` is `byteRev32`, and the 32-bit words of a range whose bytes are kept.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
  VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.Arm (Upd)

theorem rev_eq (w : BitVec 32) : rev w = byteRev32 w := rfl

theorem wp_rev {s : State} {is : List Instr} {Q : State → Prop} {d m : Reg}
    (k : ∀ s', Upd s s' d (rev (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- A 32-bit word of a range whose bytes are kept. -/
theorem readW32_keep {m m' : Mem} {p : Addr} {d : Nat}
    (h : ∀ i < 4, m' (p + BitVec.ofNat 64 (d + i)) = m (p + BitVec.ofNat 64 (d + i))) :
    m'.readW (p + BitVec.ofNat 64 d) 32 = m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_congr fun i hi => by rw [Offset.add_add, h i hi]

end VG.Proof.Weierstrass.Arm
