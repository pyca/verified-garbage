module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByteHead
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByteNext
import VerifiedGarbage.Proof.Framework.Block

/-! # One exponent byte advances the generator-two power by eight bits -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem byte_ok {base ep : BitVec 32} {len w M E c : Nat} {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (s : State) (h : Power base len w M E s) (hp : P s)
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 c)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) 1) :
    WP isa (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block expByteNext))) s fun t =>
      Power base len w M (256 * E + (s.mem (State.addr ep)).toNat) t ∧ P t ∧
      t.mem.readW (off (State.addr base) 128) 32 = ep + 1 ∧
      t.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (byteHead_ok s h pointer read) ?_
  rintro u ⟨ready, headerU, frameU, restU⟩
  have ru : Rest roundClobbers s u := restU.mono (by simp [roundClobbers])
  have pu := K.stable frameU ru hp
  rw [WP.seq_iff]
  refine WP.mono (bits_ok K u ready pu (s.mem (State.addr ep)).isLt) ?_
  rintro v ⟨power, pv, headerV, frameV, restV⟩
  refine WP.mono (byteNext_ok v power hc hc'
    ((headerV 128 (by decide)).trans ((headerU 128 (by decide)).trans pointer))
    ((headerV 132 (by decide)).trans ((headerU 132 (by decide)).trans count))) ?_
  rintro t ⟨final, ptr, counter, zero, frameT, restT⟩
  have rt : Rest roundClobbers v t := restT.mono (by simp [roundClobbers])
  exact ⟨final, K.stable frameT rt pv, ptr, counter, zero,
    (frameU.mono (by simpa using K.workspace)).trans (frameV.trans (frameT.mono (by simpa using K.workspace))),
    ru.trans (restV.trans rt)⟩

end VG.Proof.Bignum.Arm.TwoExp
