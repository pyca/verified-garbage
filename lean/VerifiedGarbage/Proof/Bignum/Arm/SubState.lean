module

public import VerifiedGarbage.Proof.Bignum.Arm.SubStep
public import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
public import VerifiedGarbage.Proof.Mont.Words32
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Packed-word subtraction: workspace and arithmetic invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

abbrev subLoopClobbers : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r10, .r11, .r12, .lr]

/-- The two inputs may coincide, but the output is separate from both. -/
structure SubCtx (s : State) (base : BitVec 32) (size o a b n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  outFits : o + 4 * n ≤ size
  aFits : a + 4 * n ≤ size
  bFits : b + 4 * n ≤ size
  sepA : o + 4 * n ≤ a ∨ a + 4 * n ≤ o
  sepB : o + 4 * n ≤ b ∨ b + 4 * n ≤ o
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

structure SubInv (s0 : State) (base : BitVec 32) (o a b n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  aPtr : s.gpr .r10 = base + BitVec.ofNat 32 (a + 4 * i)
  bPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  borrow : (s.gpr .r11).toNat ≤ 1
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + val32 s0.mem (State.addr base) b i +
    (s0.gpr .r11).toNat = val32 s0.mem (State.addr base) a i +
      2 ^ (32 * i) * (s.gpr .r11).toNat
  rest : Rest subLoopClobbers s0 s

theorem sub_value_step {s0 s t : State} {base : BitVec 32} {size o a b n i : Nat}
    (ctx : SubCtx s0 base size o a b n) (inv : SubInv s0 base o a b n i s) (hi : i < n)
    (hm : t.mem = s.mem.writeW (off (State.addr base) (o + 4 * i)) (t.gpr .r3))
    (hv : (t.gpr .r3).toNat + w32 s.mem (State.addr base) (b + 4 * i) + (s.gpr .r11).toNat =
      w32 s.mem (State.addr base) (a + 4 * i) + 2 ^ 32 * (t.gpr .r11).toNat) :
    Outside (State.addr base) o (4 * (i + 1)) s0.mem t.mem ∧
      val32 t.mem (State.addr base) o (i + 1) + val32 s0.mem (State.addr base) b (i + 1) +
        (s0.gpr .r11).toNat = val32 s0.mem (State.addr base) a (i + 1) +
          2 ^ (32 * (i + 1)) * (t.gpr .r11).toNat := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have ha := ctx.aFits
  have hb := ctx.bFits
  have sa := ctx.sepA
  have sb := ctx.sepB
  have aold := inv.outside.w32 (d := a + 4 * i) (by omega) (by omega)
  have bold := inv.outside.w32 (d := b + 4 * i) (by omega) (by omega)
  rw [aold, bold] at hv
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r3) (by omega)
  rw [← hm] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r3).toNat := by
    rw [hm, w32_write_self]
  refine ⟨(inv.outside.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_⟩
  rw [val32_succ, val32_succ, val32_succ, low, top, pow32_succ]
  have value := inv.value
  generalize 2 ^ (32 * i) = P at *
  grind

end VG.Proof.Bignum.Arm
