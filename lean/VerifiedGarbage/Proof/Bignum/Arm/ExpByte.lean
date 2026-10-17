module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpByteNext
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # One exponent-buffer byte appends eight bits to the proved power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem expByte_ok (s : State) {base ep : BitVec 32} {len w M x E c : Nat}
    (h : ExpState base len w M x E s) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 c)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) 1) :
    WP isa (.seq expByteHead (.seq expBits (.block expByteNext))) s fun t =>
      ExpState base len w M x (256 * E + (s.mem (State.addr ep)).toNat) t ∧
      t.mem.readW (off (State.addr base) 128) 32 = ep + 1 ∧
      t.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (expByteHead_ok s h pointer read) ?_
  rintro u ⟨ready, headerU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (expBits_ok u ready (s.mem (State.addr ep)).isLt) ?_
  rintro v ⟨power, headerV, frameV, restV⟩
  refine WP.mono (expByteNext_ok v power hc hc'
    ((headerV 128 (by decide)).trans ((headerU 128 (by decide)).trans pointer))
    ((headerV 132 (by decide)).trans ((headerU 132 (by decide)).trans count))) ?_
  rintro t ⟨final, ptr, counter, zero, frameT, restT⟩
  exact ⟨final, ptr, counter, zero, frameU.trans (frameV.trans frameT),
    (restU.mono (by simp [roundClobbers])).trans (restV.trans (restT.mono (by simp [roundClobbers])))⟩

end VG.Proof.Bignum.Arm
