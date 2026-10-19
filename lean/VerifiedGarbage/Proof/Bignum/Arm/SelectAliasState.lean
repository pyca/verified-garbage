module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectState
import VerifiedGarbage.Impl.Bignum.Arm.Sub

/-! # In-place selection preserves unread source words -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- Each source is either identical to the destination or fully separate from it. -/
structure SelectCtx (s : State) (base : BitVec 32) (size o a b n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  outFits : o + 4 * n ≤ size
  aFits : a + 4 * n ≤ size
  bFits : b + 4 * n ≤ size
  sepA : o + 4 * n ≤ a ∨ a + 4 * n ≤ o ∨ o = a
  sepB : o + 4 * n ≤ b ∨ b + 4 * n ≤ o ∨ o = b
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

theorem selectAlias_value_step {s0 s t : State} {base : BitVec 32} {size o a b n i : Nat}
    (ctx : SelectCtx s0 base size o a b n) (inv : SelectInv s0 base o a b n i s) (hi : i < n)
    (hm : t.mem = s.mem.writeW (off (State.addr base) (o + 4 * i))
      (if (s.gpr .r11).toNat = 0 then s.mem.readW (off (State.addr base) (a + 4 * i)) 32
        else s.mem.readW (off (State.addr base) (b + 4 * i)) 32)) :
    Outside (State.addr base) o (4 * (i + 1)) s0.mem t.mem ∧
      val32 t.mem (State.addr base) o (i + 1) = if (s0.gpr .r11).toNat = 0 then
        val32 s0.mem (State.addr base) a (i + 1) else val32 s0.mem (State.addr base) b (i + 1) := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have ha := ctx.aFits
  have hb := ctx.bFits
  have sa := ctx.sepA
  have sb := ctx.sepB
  have aold := inv.outside.w32 (d := a + 4 * i) (by omega) (by omega)
  have bold := inv.outside.w32 (d := b + 4 * i) (by omega) (by omega)
  have bit := inv.rest.gpr .r11 (by simp [selectLoopClobbers])
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i)
    (if (s.gpr .r11).toNat = 0 then s.mem.readW (off (State.addr base) (a + 4 * i)) 32
      else s.mem.readW (off (State.addr base) (b + 4 * i)) 32) (by omega)
  rw [← hm] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = if (s0.gpr .r11).toNat = 0 then
      w32 s0.mem (State.addr base) (a + 4 * i) else w32 s0.mem (State.addr base) (b + 4 * i) := by
    rw [hm, w32_write_self, bit]
    split <;> first | exact aold | exact bold
  refine ⟨(inv.outside.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_⟩
  rw [val32_succ, low, top, inv.value]
  split <;> rw [val32_succ]

end VG.Proof.Bignum.Arm
