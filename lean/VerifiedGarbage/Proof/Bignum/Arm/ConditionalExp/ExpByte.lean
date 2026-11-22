module
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBits

import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteNext
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHead
import VerifiedGarbage.Proof.Framework.Block

/-! # One exponent-buffer byte appends eight bits to the proved power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
variable {ok : Prop} {Q : State → Prop} {regions : List Region}

theorem expByte_ok (s : State) {base ep : BitVec 32} {len w M x E c : Nat}
    (K : TwoExp.Montgomery base len w Q regions) (h : ExpState ok base len w M x E s) (q : Q s) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 c)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) 1) :
    WP isa (.seq expByteHead (.seq (expBitsWith K.op) (.block expByteNext))) s fun t =>
      ExpState ok base len w M x (256 * E + (s.mem (State.addr ep)).toNat) t ∧ Q t ∧
      t.mem.readW (off (State.addr base) 128) 32 = ep + 1 ∧
      t.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (expByteHead_ok s h pointer read) ?_
  rintro u ⟨ready, headerU, frameU, restU⟩
  have qU := K.stable frameU (restU.mono (by decide)) q
  rw [WP.seq_iff]
  refine WP.mono (expBits_ok u K ready qU (s.mem (State.addr ep)).isLt) ?_
  rintro v ⟨power, qV, headerV, frameV, restV⟩
  refine WP.mono (expByteNext_ok v power hc hc'
    ((headerV 128 (by decide)).trans ((headerU 128 (by decide)).trans pointer))
    ((headerV 132 (by decide)).trans ((headerU 132 (by decide)).trans count))) ?_
  rintro t ⟨final, ptr, counter, zero, frameT, restT⟩
  exact ⟨final, K.stable frameT (restT.mono (by decide)) qV, ptr, counter, zero,
    (liftFrame K frameU).trans (frameV.trans (liftFrame K frameT)),
    (restU.mono (by decide)).trans (restV.trans (restT.mono (by decide)))⟩

end VG.Proof.Bignum.Arm.ConditionalExp
