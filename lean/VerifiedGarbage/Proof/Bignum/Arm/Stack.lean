module

import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Stack loads and saved register slots of the Montgomery wrapper -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Upd)

theorem wp_loadStack {s : State} {is : List Instr} {Q : State → Prop}
    {r : Reg} {d : Nat} {a : Addr} (hd : d < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 d) = a) (hr : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ t, Upd s t r (s.mem.readW a 32) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp r d :: is)) s Q := by
  subst ha
  exact VG.Proof.X25519.Arm.WP.cons
    (by simp only [exec, hd, ite_true, State.load32, hr, Option.map_some]) (k _ (Upd.setReg _ _ _))

end VG.Proof.Bignum.Arm
