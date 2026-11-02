module
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBits
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteSave
import VerifiedGarbage.Proof.Framework.Block

/-! # Read a byte and establish the complete exponent-bit-loop invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem expByteHead_ok (s : State) {base ep : BitVec 32} {len w M x E : Nat}
    (h : ExpState ok base len w M x E s)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) 1) :
    WP isa expByteHead s fun t => ExpBitState ok base len w M x E (s.mem (State.addr ep)).toNat 0 t ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [.r1, .r2] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  rw [expByteHead, WP.block_append_iff]
  refine WP.mono (expByteLoad_ok s h.ready.workspace (by omega) h.ready.ptr pointer read) ?_
  rintro u ⟨byte, mem, rest⟩
  have state := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  have value : u.gpr .r1 = BitVec.ofNat 32 (s.mem (State.addr ep)).toNat := by
    rw [byte, BitVec.ofNat_toNat]
  refine WP.mono (expByteSave_ready u state (s.mem (State.addr ep)).isLt value) ?_
  rintro t ⟨ready, header, frame, keep⟩
  rw [mem] at header frame
  exact ⟨ready, header, frame, rest.trans (keep.mono (by simp))⟩

end VG.Proof.Bignum.Arm.ConditionalExp
