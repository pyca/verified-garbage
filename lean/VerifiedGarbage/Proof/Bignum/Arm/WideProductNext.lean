module

public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderIncrement
public import VerifiedGarbage.Proof.Bignum.Arm.HeaderDecrement
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Advance both product pointers and the public row count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProductNext_ok (s : State) {base ap op : BitVec 32} {size c : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = ap)
    (oPtr : s.mem.readW (off (State.addr base) 136) 32 = op)
    (count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 c) :
    WP isa wideProductNext s fun t =>
      t.mem = ((s.mem.writeW (off (State.addr base) 128) (ap + 4)).writeW
        (off (State.addr base) 136) (op + 4)).writeW (off (State.addr base) 140) (BitVec.ofNat 32 (c - 1)) ∧
      t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  rw [wideProductNext, WP.seq_iff]
  refine WP.mono (headerIncrement_ok s ws (by omega) (by decide) (by decide) ptr aPtr) ?_
  rintro u ⟨memU, restU⟩
  have outsideU : Outside (State.addr base) 128 4 s.mem u.mem := by
    rw [memU]; exact writeW32_outside s.mem (State.addr base) (d := 128) (ap + 4) (by decide)
  have oPtrU := (outside_read32 outsideU (d := 136) (by decide) (by decide)).trans oPtr
  have countU := (outside_read32 outsideU (d := 140) (by decide) (by decide)).trans count
  rw [WP.seq_iff]
  refine WP.mono (headerIncrement_ok u (ws.congr restU.wr) (by omega) (by decide) (by decide)
    ((restU.gpr .r0 (by simp)).trans ptr) oPtrU) ?_
  rintro v ⟨memV, restV⟩
  have outsideV : Outside (State.addr base) 136 4 u.mem v.mem := by
    rw [memV]; exact writeW32_outside u.mem (State.addr base) (d := 136) (op + 4) (by decide)
  have countV := (outside_read32 outsideV (d := 140) (by decide) (by decide)).trans countU
  refine WP.mono (headerDecrement_ok v (ws.congr (restV.wr.trans restU.wr)) (by omega) (by decide)
    ((restV.gpr .r0 (by simp)).trans ((restU.gpr .r0 (by simp)).trans ptr)) hc hc' countV) ?_
  rintro t ⟨memT, zero, restT⟩
  exact ⟨by rw [memT, memV, memU]; rfl, zero, restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
