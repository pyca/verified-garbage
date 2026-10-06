import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CtViews

/-! Constant time of the tile's low block and public block setup. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def AfterFront (L : TileLayout) (s : State) : Prop :=
  TileReady L 1 s ∧ s.zf = some (decide (L.n = 0))

theorem front_ct : RelCT isa (Two TileGood) AdxRotate8.tileFront (Two AfterFront) := by
  unfold AdxRotate8.tileFront
  refine RelCT.seq (two_piece [.rdi, .rcx] tile_pins (by taint_decide) begin_fw) ?_
  refine RelCT.seq (two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) head_fw) ?_
  refine RelCT.seq (two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) clear_fw) ?_
  refine two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) ?_
  intro L s h
  refine WP.mono (next_fw L 0 s (by omega) h) fun t ⟨ht, hz⟩ => ⟨ht, ?_⟩
  rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega))
end VG.Proof.Bignum.X86_64.AdxRotate8
