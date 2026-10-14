module

public import VerifiedGarbage.Impl.Bignum.Arm.Double
public import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
public import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The doubled extended accumulator and its reduction metadata -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp op2_imm dpVal)

theorem doubleProduct_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (ready : CoreReady base size out tmp a b mod acc n s)
    (two : w32 s.mem (State.addr base) a = 2) :
    WP isa doubleProduct s fun t =>
      val32 t.mem (State.addr base) acc (n + 2) = 2 * val32 s.mem (State.addr base) b n ∧
      FinishReady base size tmp out acc mod n t ∧
      Outside (State.addr base) acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClobbers s t := by
  have ctx := ready.round.ctx
  have hn := ctx.count
  have layout := ctx.layout
  have ht := ctx.tmpFits
  have nowrap := ctx.workspace.nowrap
  obtain ⟨inverse, header, hinv⟩ := ready.round.secret
  rw [doubleProduct, WP.seq_iff]
  refine WP.mono (productStage_ok s ctx header (by omega) ready.round.ptr
    ready.round.bound ready.round.operand) ?_
  rintro u ⟨value, hdr, ptr, outside, rest⟩
  refine wp_dp (op2_imm (by decide)) fun t h => WP.block_nil ?_
  have mem := h.mem
  have kept : Rest roundClobbers s t := rest.trans (h.rest (by simp [roundClobbers]))
  have out : u.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out := by
    rw [outside_read32 outside (d := tmp + 24) (by omega) (by omega)]
    exact ready.outPtr
  refine ⟨?_, ?_, ?_, kept⟩
  · rw [mem, value, ready.zero]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, two]
  · refine ⟨ctx.workspace.congr kept.wr, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h.gpr, dpVal, ptr]
      change base + BitVec.ofNat 32 (acc + 4 * n) + BitVec.ofNat 32 16 = _
      rw [Offset.add_add, show acc + 4 * n + 16 = tmp by omega]
    · rw [mem]; exact hdr.count
    · rw [mem]; exact out
    · rw [mem]; exact hdr.accPtr
    · rw [mem]; exact hdr.mPtr
  · rw [mem]; exact outside

end VG.Proof.Bignum.Arm
