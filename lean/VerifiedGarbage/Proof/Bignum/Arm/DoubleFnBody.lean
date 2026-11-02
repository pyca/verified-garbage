module

public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.DoubleBody
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Modular doubling from the shared RSA header preserves all unrelated arrays -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem doubleFnBody_ok (s : State) {base : BitVec 32} {len o a b : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (ptr : s.gpr .r0 = base) (po : s.gpr .r2 = BitVec.ofNat 32 o)
    (pa : s.gpr .r3 = BitVec.ofNat 32 a) (pb : s.gpr .r12 = BitVec.ofNat 32 b)
    (two : w32 s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) a) = 2)
    (inverse : ((word s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) 0)).toNat *
      (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0)
    (operand : numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) b <
      numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) 0) :
    WP isa doubleFnBody s fun t =>
      let w := wOf s.mem (State.addr base)
      let M := numAt s.mem (State.addr base) w 0
      numAt t.mem (State.addr base) w o < M ∧
      numAt t.mem (State.addr base) w o = (2 * numAt s.mem (State.addr base) w b) % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := wOf s.mem (State.addr base)
  have hw : 2 ≤ w := layout.1
  have fits : arrAt w 8 ≤ 8 * len := layout.2.2.1
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  obtain ⟨ctx, finish⟩ := layout_context ws hw fits ho ha hb
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  rw [doubleFnBody, WP.seq_iff]
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 hb.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  refine WP.mono (doubleBody_ok u (ctx.congr keep.wr) (finish.congr keep.wr) regs
    (by rw [mem]; exact two) ?_ ?_) ?_
  · rw [mem, ← numAt_native, ← numAt_native]; exact operand
  · rw [mem]; exact native_inverse s.mem (State.addr base) (by omega) inverse
  · rintro t ⟨value, outside, rest⟩
    rw [mem] at value outside
    have frame : Outs (State.addr base)
        [(arrAt w 2, 4 * (2 * w + 2)), (arrAt w 3, 32), (arrAt w 3 + 16, 8),
          (arrAt w 3, 4 * (2 * w)), (arrAt w o, 4 * (2 * w))] s.mem t.mem :=
      outside.mono (by simp)
    have val : numAt t.mem (State.addr base) w o =
        (2 * numAt s.mem (State.addr base) w b) % numAt s.mem (State.addr base) w 0 := by
      simpa only [numAt_native] using value
    refine ⟨?_, val, keeps_of_native ws.nowrap hw frame, frame_of_native hw ho.1 fits frame, keep.trans rest⟩
    rw [val]
    exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) operand)

end VG.Proof.Bignum.Arm
