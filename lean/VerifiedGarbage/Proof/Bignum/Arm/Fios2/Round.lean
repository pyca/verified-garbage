module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelinePair
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Args
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Code
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Finish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.FiosState

/-! The two-row round meets the two-row round contract. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

/-- An accumulator below `2m`, for `m` of `n` words, has a zero top word. -/
theorem top_zero {mem : Mem} {base : Addr} {acc m n : Nat}
    (hT : val32 mem base acc (n + 2) < 2 * m) (hm : m < 2 ^ (32 * n)) :
    w32 mem base (acc + 4 * (n + 1)) = 0 := by
  rw [show n + 2 = (n + 1) + 1 by omega, val32_succ] at hT
  have p : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := pow32_succ n
  rw [p] at hT
  by_contra hne
  have : 2 ^ 32 * 2 ^ (32 * n) ≤ 2 ^ 32 * 2 ^ (32 * n) * w32 mem base (acc + 4 * (n + 1)) :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
  have : 2 * 2 ^ (32 * n) ≤ 2 ^ 32 * 2 ^ (32 * n) := Nat.mul_le_mul_right _ (by decide)
  omega

theorem round_law : MontPipeline.PairLaw VG.Impl.Bignum.Arm.Fios2.round := by
  intro s base size tmp a b mod acc n i inv ctx even hdr hi ptr hT hB hInv
  have count := ctx.count
  have nowrap := ctx.workspace.nowrap
  have fits := ctx.tmpFits
  have layout := ctx.layout
  rw [VG.Impl.Bignum.Arm.Fios2.round, WP.seq_iff]
  refine WP.mono (args_ok s ctx hdr hi ptr) ?_
  rintro u ⟨a0, a1, p0, p12, p4, p2, p10, cnt, c7, c8, c5, c11, memU, restU⟩
  let c : Fios.Ctx u base size acc b mod n :=
    ⟨ctx.workspace.congr restU.wr, ctx.accFits, ctx.bFits, ctx.mFits, ctx.accB, ctx.accM⟩
  have split : val32 s.mem (State.addr base) mod n =
      w32 s.mem (State.addr base) mod + 2 ^ 32 * val32 s.mem (State.addr base) (mod + 4) (n - 1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n - 1) + 1) := by congr 1; omega
      _ = _ := rfl
  have inverseLow : (w32 u.mem (State.addr base) mod * (u.gpr .r2).toNat + 1) % 2 ^ 32 = 0 := by
    rw [memU, p2]
    rw [split, Nat.add_mul, Nat.add_right_comm, Nat.mul_assoc, Nat.add_mul_mod_self_left] at hInv
    exact hInv
  have high : w32 u.mem (State.addr base) (acc + 4 * (n + 1)) = 0 := by
    rw [memU]
    exact top_zero hT (val32_lt s.mem (State.addr base) mod n)
  rw [WP.seq_iff]
  refine WP.mono (code_ok u c (by omega) even p0 p12 p4 cnt (p10.trans p2.symm) c7 c8 c5 c11
    inverseLow high) ?_
  rintro v ⟨⟨q0, q1, value⟩, ptrV, outsideV, keepV⟩
  have a0n : (u.gpr .r1).toNat = w32 s.mem (State.addr base) (a + 4 * i) := by rw [a0]
  have a1n : (u.gpr .r9).toNat = w32 s.mem (State.addr base) (a + 4 * i + 4) := by rw [a1]
  rw [memU, a0n, a1n] at value
  rw [memU] at outsideV
  have hdrV := hdr.of_outside outsideV (by omega) (by omega)
  refine WP.mono (finish_ok (top := acc + 4 * (n + 1)) (tmp := tmp) v (ctx.workspace.congr (restU.trans keepV).wr)
    (by omega) (by omega) ptrV) ?_
  rintro t ⟨memT, ptrT, zero, keepT⟩
  have nowrap' : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨result, frame⟩ := finish_value (mem := v.mem) (acc := acc) (n := n) (tmp := tmp)
    nowrap' (by omega) rfl (by omega)
  rw [← memT] at result frame
  have hq : q0.toNat + 2 ^ 32 * q1.toNat < 2 ^ 64 := by
    have := q0.isLt; have := q1.isLt; omega
  have hA : w32 s.mem (State.addr base) (a + 4 * i) + 2 ^ 32 * w32 s.mem (State.addr base) (a + 4 * i + 4) <
      2 ^ 64 := by
    have := (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
    have := (s.mem.readW (off (State.addr base) (a + 4 * i + 4)) 32).isLt
    simp only [w32]; omega
  have value' : 2 ^ 64 * val32 t.mem (State.addr base) acc (n + 2) =
      val32 s.mem (State.addr base) acc (n + 2) +
        (w32 s.mem (State.addr base) (a + 4 * i) + 2 ^ 32 * w32 s.mem (State.addr base) (a + 4 * i + 4)) *
          val32 s.mem (State.addr base) b n +
        (q0.toNat + 2 ^ 32 * q1.toNat) * val32 s.mem (State.addr base) mod n := by
    rw [result, value]
  refine ⟨?_, ptrT, ⟨_, hq, value'⟩, MontPipeline.pair_lt value' hT hA hB hq, ?_, ?_, ?_⟩
  · rw [memT]
    exact finish_meta nowrap fits (by omega) hdrV hi
  · have enlarged : Outside (State.addr base) acc (4 * (n + 2)) s.mem v.mem :=
      outsideV.mono (Nat.le_refl _) (by omega)
    exact (Outs.of_outside enlarged (by simp)).trans frame
  · rw [zero, hdrV.remaining]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 2 = 0 ↔ i + 2 = n by omega]
  · exact restU.trans (keepV.trans (keepT.mono (by simp [roundClobbers])))

end VG.Proof.Bignum.Arm.Fios2
