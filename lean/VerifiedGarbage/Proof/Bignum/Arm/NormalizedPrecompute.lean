module

public import VerifiedGarbage.Impl.Bignum.Arm.NormalizedPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.NormalizedR2
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! # Modulus import and inverse followed by normalized R-squared preparation -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem normalizedPrecompute_ok {base src : BitVec 32} {len w k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) (hp : P s)
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w)
    (hk : 0 < k) (fit : k ≤ 8 * w) (srcFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (ptr : s.gpr .r0 = base) (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base)
    (large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k))
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1)
    (countFits : 128 * w < 2 ^ 32)
    (normalized : 2 ^ (64 * (w - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
    WP isa (NormalizedPrecompute.precompute K.op) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) w 4 =
        2 ^ (128 * w) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [NormalizedPrecompute.precompute, WP.seq_iff]
  refine WP.mono (importModulus_ok s ws layout width hk fit srcFit read sep ptr source count
    stackRead stackSep saved) ?_
  rintro u ⟨layoutU, widthU, ptrU, modulus, frameU, restU⟩
  have pu := K.stable frameU restU hp
  rw [WP.seq_iff]
  refine WP.mono (precomputeInverse_ok u (ws.congr restU.wr) layoutU widthU ptrU
    (by rw [modulus]; exact odd) (by rw [modulus]; exact large)
    (by rw [restU.rd, restU.wr, restU.sp]; exact stackRead)
    (by rw [restU.sp]; exact stackSep) (saved_base_kept frameU stackSep saved restU.sp)) ?_
  rintro v ⟨ready, modV, frameV, restV⟩
  have pv := K.stable frameV restV pu
  refine WP.mono (normalizedR2_ok K v ready pv countFits
    (by rw [modV, modulus]; exact normalized)) ?_
  rintro t ⟨done, value, modT, pt, frameT, restT⟩
  rw [modV, modulus] at value
  exact ⟨done, modT.trans (modV.trans modulus), value, pt,
    (frameU.trans frameV).mono (by simpa using K.workspace) |>.trans frameT,
    restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
