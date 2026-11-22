module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
public import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Bignum.Arm.R2Kernel`, which this module and modules that import it used -/

section

/-! One correctness interface for the existing and normalized R-squared calculations. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure R2Kernel where
  code : Prog isa
  correct : ∀ (s : State) {base : BitVec 32} {len w : Nat},
    ArithmeticReady base len w s → 128 * w < 2 ^ 32 →
    WP isa code s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t

def baselineR2Kernel : R2Kernel := ⟨r2, r2_ok⟩

end VG.Proof.Bignum.Arm

end

end

/-! # RSA precomputation from modulus bytes, entirely in proved ARMv7 code -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PrecomputeLaw.lean`, which only this module imported.
section

/-! The common postcondition for RSA modulus import and Montgomery setup. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

def PrecomputeLaw (code : Prog isa) : Prop := ∀ (s : State) {base src : BitVec 32} {len w k : Nat}
    (_ws : Workspace s base (8 * len)) (_layout : Layout s.mem (State.addr base) len)
    (_width : wOf s.mem (State.addr base) = w)
    (_hk : 0 < k) (_fit : k ≤ 8 * w) (_srcFit : src.toNat + k ≤ 2 ^ 32)
    (_read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (_sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (_ptr : s.gpr .r0 = base) (_source : s.gpr .r4 = src) (_count : s.gpr .r6 = BitVec.ofNat 32 k)
    (_stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (_stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (_saved : s.mem.readW (State.addr s.sp) 32 = base)
    (_large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k))
    (_odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1)
    (_countFits : 128 * w < 2 ^ 32),
    WP isa code s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) w 4 =
        2 ^ (128 * w) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t

/-- `PrecomputeLaw`, for code that may also write the 48 bytes below the
stack its callers leave it, as a call of the shared Montgomery product does. -/
def PrecomputeLawS (code : Prog isa) : Prop := ∀ (s : State) {base src : BitVec 32} {len w k : Nat}
    (_ws : Workspace s base (8 * len)) (_layout : Layout s.mem (State.addr base) len)
    (_width : wOf s.mem (State.addr base) = w)
    (_hk : 0 < k) (_fit : k ≤ 8 * w) (_srcFit : src.toNat + k ≤ 2 ^ 32)
    (_read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (_sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (_ptr : s.gpr .r0 = base) (_source : s.gpr .r4 = src) (_count : s.gpr .r6 = BitVec.ofNat 32 k)
    (_stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (_stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (_saved : s.mem.readW (State.addr s.sp) 32 = base)
    (_large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k))
    (_odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1)
    (_countFits : 128 * w < 2 ^ 32) (_cs : CallStack base len s),
    WP isa code s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) w 4 =
        2 ^ (128 * w) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Frame [⟨State.addr base, 8 * len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t

theorem PrecomputeLaw.toS {code : Prog isa} (h : PrecomputeLaw code) : PrecomputeLawS code := by
  intro s base src len w k ws layout width hk fit srcFit read sep ptr source count stackRead stackSep saved large odd
    countFits _
  exact (h s ws layout width hk fit srcFit read sep ptr source count stackRead stackSep saved large odd countFits).mono
    fun _ ⟨a, b, c, f, r⟩ => ⟨a, b, c, f.mono (by simp), r⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem precomputeWith_ok (kernel : R2Kernel) : PrecomputeLaw (precomputeWith kernel.code) := by
  intro s base src len w k ws layout width hk fit srcFit read sep ptr source count
    stackRead stackSep saved large odd countFits
  rw [precomputeWith, WP.seq_iff]
  refine WP.mono (importModulus_ok s ws layout width hk fit srcFit read sep ptr source count
    stackRead stackSep saved) ?_
  rintro u ⟨layoutU, widthU, ptrU, modulus, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (precomputeInverse_ok u (ws.congr restU.wr) layoutU widthU ptrU
    (by rw [modulus]; exact odd) (by rw [modulus]; exact large)
    (by rw [restU.rd, restU.wr, restU.sp]; exact stackRead)
    (by rw [restU.sp]; exact stackSep) (saved_base_kept frameU stackSep saved restU.sp)) ?_
  rintro v ⟨ready, modV, frameV, restV⟩
  refine WP.mono (kernel.correct v ready countFits) ?_
  rintro t ⟨done, value, modT, frameT, restT⟩
  rw [modV, modulus] at value
  exact ⟨done, modT.trans (modV.trans modulus), value,
    frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

theorem precompute_ok : PrecomputeLaw precompute := precomputeWith_ok baselineR2Kernel

end VG.Proof.Bignum.Arm
