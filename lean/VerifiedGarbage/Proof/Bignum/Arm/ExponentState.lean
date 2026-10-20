module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentByteCT
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.ExponentByte
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The public buffer and prefix invariants of exponent validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

structure ExponentBuffer (ep : BitVec 32) (eb : List Byte) (s : State) : Prop where
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

structure ExponentState (ep : BitVec 32) (eb : List Byte) (j : Nat) (s : State) : Prop where
  buffer : ExponentBuffer ep eb s
  ptr : s.gpr .r1 = ep + BitVec.ofNat 32 j
  count : s.gpr .lr = BitVec.ofNat 32 (eb.length - j)
  low : s.gpr .r3 = BitVec.ofNat 32 (pre eb j % 2 ^ 32)
  high : s.gpr .r4 = BitVec.ofNat 32 (exponentHigh (pre eb j))

theorem ExponentState.input {s : State} {ep : BitVec 32} {eb : List Byte} {j : Nat}
    (h : ExponentState ep eb j s) (hj : j < eb.length) :
    ExponentByteInput (ep + BitVec.ofNat 32 j) (pre eb j) s := by
  refine ⟨h.ptr, h.low, h.high, ?_⟩
  rw [addr_add (by have := h.buffer.sourceFit; omega)]
  exact CallLay.inRegions_sub h.buffer.read (by omega) (by have := h.buffer.countFit; omega)

theorem exponentState_step (s : State) {ep : BitVec 32} {eb : List Byte} {j : Nat}
    (h : ExponentState ep eb j s) (hj : j < eb.length) :
    WP isa exponentByte s fun t => ExponentState ep eb (j + 1) t ∧ t.z = decide (j + 1 = eb.length) := by
  have input := h.input hj
  have byte : s.mem (State.addr (ep + BitVec.ofNat 32 j)) = eb[j] := by
    rw [addr_add (by have := h.buffer.sourceFit; omega)]
    exact h.buffer.bytes j hj
  refine WP.mono (exponentByte_ok s (by omega) (by have := h.buffer.countFit; omega)
    h.ptr h.count input.read byte h.low h.high) ?_
  rintro t ⟨lo, hi, ptr, count, zero, mem, rest⟩
  have next : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [next] at lo hi
  refine ⟨⟨⟨h.buffer.countFit, h.buffer.sourceFit, ?_, ?_⟩, ?_, ?_, lo, hi⟩, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.buffer.read
  · rw [mem]; exact h.buffer.bytes
  · rw [ptr]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [count]; congr 1
  · rw [zero]; exact decide_eq_decide.mpr (by omega)

theorem exponentInit_ready (s : State) {ep : BitVec 32} {eb : List Byte}
    (h : ExponentBuffer ep eb s) (ptr : s.gpr .r1 = ep) (count : s.gpr .lr = BitVec.ofNat 32 eb.length) :
    WP isa (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) s (ExponentState ep eb 0) := by
  refine wp_mov (op2_imm (by decide)) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun t b => WP.block_nil ?_
  have rest : Rest [.r3, .r4] s t := (a.rest (by simp)).trans (b.rest (by simp))
  refine ⟨⟨h.countFit, h.sourceFit, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.read
  · rw [b.mem, a.mem]; exact h.bytes
  · simpa using (rest.gpr .r1 (by simp)).trans ptr
  · simpa using (rest.gpr .lr (by simp)).trans count
  · exact (b.other .r3 (by decide)).trans a.gpr
  · simpa [pre_zero, exponentHigh] using b.gpr

end VG.Proof.Bignum.Arm
