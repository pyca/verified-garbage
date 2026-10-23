module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineBody
public import VerifiedGarbage.Spec.Rsa.Mont
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline

/-! Lift any native scanning round through the existing Montgomery pipeline. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Spec.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)

theorem fnBody_ok (round : Prog isa) (law : LoopLaw round) (s : State) {base : BitVec 32} {len o a b : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (ptr : s.gpr .r0 = base) (po : s.gpr .r2 = BitVec.ofNat 32 o)
    (pa : s.gpr .r3 = BitVec.ofNat 32 a) (pb : s.gpr .r12 = BitVec.ofNat 32 b)
    (inverse : ((word s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) 0)).toNat *
      (wordAt s.mem (State.addr base) Spec.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0)
    (operand : numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) b <
      numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) 0) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.fnBody round) s fun t =>
      let w := wOf s.mem (State.addr base)
      let M := numAt s.mem (State.addr base) w 0
      numAt t.mem (State.addr base) w o < M ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % M =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := wOf s.mem (State.addr base)
  have hw : 2 ≤ w := layout.1
  have fits : arrAt w 8 ≤ 8 * len := layout.2.2.1
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  obtain ⟨ctx, finish⟩ := layout_context ws hw fits ho ha hb
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits
    omega
  rw [VG.Impl.Bignum.Arm.MontPipeline.fnBody, WP.seq_iff]
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 hb.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  refine WP.mono (body_ok round law u (ctx.congr keep.wr) (by omega) (finish.congr keep.wr) regs ?_ ?_) ?_
  · rw [mem, ← numAt_native, ← numAt_native]; exact operand
  · rw [mem]; exact native_inverse s.mem (State.addr base) (by omega) inverse
  · rintro t ⟨lt, value, outside, rest⟩
    rw [mem] at lt value outside
    refine ⟨?_, ?_, keeps_of_native ws.nowrap hw outside, frame_of_native hw ho.1 fits outside, keep.trans rest⟩
    · simpa only [numAt_native] using lt
    · rw [numAt_native, numAt_native, numAt_native, numAt_native, Nat.mul_comm _ (2 ^ (64 * w))]
      simpa only [radix32] using value


end VG.Proof.Bignum.Arm.MontPipeline
