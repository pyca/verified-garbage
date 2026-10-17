module

public import VerifiedGarbage.Proof.Bignum.Arm.WideProductState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # One complete product row implements the next schoolbook multiplication term -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProductRow_ok (s : State) {s0 : State} {base : BitVec 32} {size o a b m n i : Nat}
    (ctx : WideProductCtx s0 base size o a b m n) (h : WideProductInv s0 base o a b m n i s) (hi : i < m) :
    WP isa (.seq (.block wideProductArgs) (.seq rowFull (.block [.ldrSp .r0 0]))) s fun t =>
      val32 t.mem (State.addr base) o (m + n + 2) =
        val32 s0.mem (State.addr base) a (i + 1) * val32 s0.mem (State.addr base) b n ∧
      Outside (State.addr base) (o + 4 * i) (4 * (n + 2)) s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have nowrap := ctx.workspace.nowrap
  have aFits := ctx.aFits
  have bFits := ctx.bFits
  have outFits := ctx.outFits
  have sepB := ctx.separateB
  obtain ⟨aOld, bOld⟩ := h.source ctx hi
  have window := product_window_bound (by omega : i + (n + 2) ≤ m + n + 2) h.value
    (val32_lt s0.mem (State.addr base) a i) (val32_lt s0.mem (State.addr base) b n)
  rw [WP.seq_iff]
  refine WP.mono (wideProductArgs_ok s (ctx.workspace.congr h.rest.wr) ctx.headerFit (by omega)
    h.ptr h.aPtr h.bPtr h.oPtr h.width) ?_
  rintro u ⟨p0, p12, count, scalar, zero, memU, restU⟩
  have rowCtx : RowCtx u base size (o + 4 * i) b n :=
    ⟨nowrap, by omega, bFits, by omega, by rw [restU.wr, h.rest.wr]; exact ctx.workspace.writable⟩
  have fit : val32 u.mem (State.addr base) (o + 4 * i) (n + 2) +
      (u.gpr .r1).toNat * val32 u.mem (State.addr base) b n + (u.gpr .r11).toNat < 2 ^ (32 * (n + 2)) := by
    rw [zero, scalar, memU]
    exact product_row_fits window (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
      (val32_lt s.mem (State.addr base) b n)
  rw [WP.seq_iff]
  refine WP.mono (rowFull_ok u rowCtx ctx.positiveB (by omega) p0 p12 count fit) ?_
  rintro v ⟨value, outside, _, restV⟩
  rw [memU] at outside
  rw [zero, scalar, memU] at value
  change val32 v.mem (State.addr base) (o + 4 * i) (n + 2) =
    val32 s.mem (State.addr base) (o + 4 * i) (n + 2) +
      w32 s.mem (State.addr base) (a + 4 * i) * val32 s.mem (State.addr base) b n at value
  rw [aOld, bOld] at value
  have whole := product_row_value (by omega : i + (n + 2) ≤ m + n + 2) (by omega) outside h.value value
  have frame := outside_workspace outside (size := size) (by omega)
  have restSV : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    (restV.mono (by simp [roundClobbers, loopClobbers]))
  have rest := h.rest.trans restSV
  have frameAll := (ctx.frame h.outside).trans frame
  refine WP.mono (restoreBase_ok v (by rw [rest.rd, rest.wr, rest.sp]; exact ctx.stackRead)
    (saved_base_kept frameAll ctx.stackSep ctx.saved rest.sp)) ?_
  rintro t ⟨ptr, memT, restT⟩
  exact ⟨by rw [memT]; exact whole, by rw [memT]; exact outside, ptr,
    restSV.trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Bignum.Arm
