module

import VerifiedGarbage.Proof.Bignum.Arm.CombScanSelect
import VerifiedGarbage.Proof.Bignum.Arm.CombScanControl
import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
public import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState

/-! Scan invariants retain the table and every arithmetic array but array one. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

def HeaderKeeps (base : BitVec 32) (m m' : Mem) : Prop := ∀ d, d+4≤256 →
  (d+4≤220 ∨ 224≤d) → (d+4≤228 ∨ 232≤d) →
  m'.readW (off (State.addr base) d) 32=m.readW (off (State.addr base) d) 32

def ArrayKeeps (base : BitVec 32) (w : Nat) (m m' : Mem) : Prop := ∀ q<8, q≠1 →
  numAt m' (State.addr base) w q=numAt m (State.addr base) w q

theorem HeaderKeeps.refl (base : BitVec 32) (m : Mem) : HeaderKeeps base m m := fun _ _ _ _ => rfl

theorem HeaderKeeps.trans {base : BitVec 32} {m m' m'' : Mem}
    (h : HeaderKeeps base m m') (h' : HeaderKeeps base m' m'') : HeaderKeeps base m m'' :=
  fun d hd ha hb => (h' d hd ha hb).trans (h d hd ha hb)

theorem ArrayKeeps.refl (base : BitVec 32) (w : Nat) (m : Mem) : ArrayKeeps base w m m := fun _ _ _ => rfl

theorem ArrayKeeps.trans {base : BitVec 32} {w : Nat} {m m' m'' : Mem}
    (h : ArrayKeeps base w m m') (h' : ArrayKeeps base w m' m'') : ArrayKeeps base w m m'' :=
  fun q hq ne => (h' q hq ne).trans (h q hq ne)

theorem header_of_writes (m : Mem) (base : BitVec 32) (a b : BitVec 32) :
    HeaderKeeps base m ((m.writeW (off (State.addr base) 220) a).writeW (off (State.addr base) 228) b) := by
  intro d hd ha hb
  exact read_after_writes m base a b ha hb (by decide) (by decide) hd

theorem header_of_outside {base : BitVec 32} {w : Nat} {m m' : Mem}
    (outside : Outside (State.addr base) (arrAt w 1) (8*w) m m') : HeaderKeeps base m m' := by
  intro d hd _ _
  exact outside_read32 outside (Or.inl (by simp only [arrAt,Spec.Rsa.Mont.hdrBytes]; omega)) (by omega)

theorem arrays_of_outside {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (fits : arrAt w 8≤8*len) (nowrap : base.toNat+8*len≤2^32)
    (outside : Outside (State.addr base) (arrAt w 1) (8*w) m m') : ArrayKeeps base w m m' := by
  intro q hq ne
  have endQ := array_end_le (w:=w) hq
  have separate := array_sep (w:=w) ne
  rw [numAt_native,numAt_native]
  exact outside.val32 (by omega) (by omega)

theorem arrays_of_ctl {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (fits : arrAt w 8≤8*len) (nowrap : base.toNat+8*len≤2^32)
    (ctl : CtlOnly base m m') : ArrayKeeps base w m m' := by
  intro q hq _
  exact ctl_num (len:=len) ctl (Nat.le_trans (arrAt_le (by omega)) fits) nowrap

theorem table_after_frame {base table : BitVec 32} {len w M g N : Nat} {s t : State} {rs : List Reg}
    (h : CombTable table w M g N s)
    (separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩)
    (frame : Frame [⟨State.addr base,8*len⟩] s.mem t.mem) (rest : Rest rs s t) :
    CombTable table w M g N t := by
  refine ⟨h.positive,h.fits,?_,?_⟩
  · rw [rest.rd,rest.wr]; exact h.readable
  · intro digit hd
    rw [←h.values digit hd]
    apply val32_congr
    intro j hj
    have efit : 8*w*digit+8*w≤32*(8*w) := by
      have bound := Nat.mul_le_mul_left (8*w) (show digit+1≤32 by omega)
      simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_comm (8*w) 32] using bound
    apply congrArg BitVec.toNat
    exact frame.readW (r:=⟨State.addr table,32*(8*w)⟩)
      (Offset.contains_base _ (by omega) (by have := h.fits; omega))
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact separate) (by decide)

structure Inv (base tablePtr : BitVec 32) (len w M g N d j : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  table : CombTable tablePtr w M g N s
  separate : Region.Disjoint ⟨State.addr tablePtr,32*(8*w)⟩ ⟨State.addr base,8*len⟩
  digitLt : d<32
  digit : s.mem.readW (off (State.addr base) 196) 32=BitVec.ofNat 32 d
  selected : d<j → numAt s.mem (State.addr base) w 1=
    Spec.Rsa.powMod g (Spec.Rsa.FixedBaseComb.exponent N d) M*2^(64*w)%M
  entry : s.mem.readW (off (State.addr base) 220) 32=tablePtr+BitVec.ofNat 32 (8*w*j)
  index : s.mem.readW (off (State.addr base) 228) 32=BitVec.ofNat 32 j

end VG.Proof.Bignum.Arm.CombScan
