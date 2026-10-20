module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.TCB.Arm.Isa

/-! # The invariant of a packed-word multiply-add row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

abbrev loopClobbers : List Reg := [.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The arrays are disjoint subranges of a writable workspace within the
32-bit address space. No access uses the pointers past the arrays. -/
structure RowCtx (s : State) (base : BitVec 32) (size o b n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  outFits : o + 4 * n ≤ size
  inFits : b + 4 * n ≤ size
  separate : o + 4 * n ≤ b ∨ b + 4 * n ≤ o
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

/-- After `i` steps, the stored prefix plus the outstanding carry is the
original prefix plus the scalar product and initial carry. -/
structure RowInv (s0 : State) (base : BitVec 32) (o b n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  inPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    val32 s0.mem (State.addr base) o i + (s0.gpr .r1).toNat * val32 s0.mem (State.addr base) b i +
      (s0.gpr .r11).toNat
  rest : Rest loopClobbers s0 s

/-- What one step of the row's loop may change: the scalar's halves in `r1`
and `r10`, and the mask in `r9`, stay for the whole loop. -/
abbrev stepClobbers : List Reg := [.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r11, .r12, .lr]

/-- `RowInv` inside the loop, from the state `s0` after the scalar `x` is
split: the same pointers, counter and value, `x` for the scalar. -/
structure RowLoopInv (s0 : State) (x : BitVec 32) (base : BitVec 32) (o b n i : Nat) (s : State) :
    Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  inPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    val32 s0.mem (State.addr base) o i + x.toNat * val32 s0.mem (State.addr base) b i +
      (s0.gpr .r11).toNat
  rest : Rest stepClobbers s0 s

/-- Form the effective address of a word anywhere in the workspace. -/
theorem row_addr {s0 s : State} {base : BitVec 32} {size o b n d : Nat}
    (ctx : RowCtx s0 base size o b n) {r : Reg}
    (hr : s.gpr r = base + BitVec.ofNat 32 d) (hd : d < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 0) = off (State.addr base) d := by
  rw [hr, Offset.add_add, Nat.add_zero]
  exact VG.Arm.addr_add (by have := ctx.nowrap; omega)

/-- Any word in the workspace remains writable throughout the row. -/
theorem row_writable {s0 s : State} {base : BitVec 32} {size o b n d : Nat}
    (ctx : RowCtx s0 base size o b n) (hr : s.wr = s0.wr) (hd : d + 4 ≤ size) :
    InRegions s.wr (off (State.addr base) d) 4 := by
  rw [hr]
  refine ⟨_, ctx.writable, Offset.contains_base _ hd ?_⟩
  have := ctx.nowrap
  omega

/-- Extend the arithmetic invariant with the next stored word, from the
invariant's memory facts alone. -/
theorem row_value_step_of {s0 s t : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n)
    (houtside : Outside (State.addr base) o (4 * i) s0.mem s.mem)
    (hvalue : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
      val32 s0.mem (State.addr base) o i + x.toNat * val32 s0.mem (State.addr base) b i +
        (s0.gpr .r11).toNat) (hi : i < n)
    (hm : t.mem = s.mem.writeW (off (State.addr base) (o + 4 * i)) (t.gpr .r3))
    (hv : (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
      x.toNat * w32 s.mem (State.addr base) (b + 4 * i) +
        w32 s.mem (State.addr base) (o + 4 * i) + (s.gpr .r11).toNat) :
    Outside (State.addr base) o (4 * (i + 1)) s0.mem t.mem ∧
      val32 t.mem (State.addr base) o (i + 1) + 2 ^ (32 * (i + 1)) * (t.gpr .r11).toNat =
        val32 s0.mem (State.addr base) o (i + 1) +
          x.toNat * val32 s0.mem (State.addr base) b (i + 1) + (s0.gpr .r11).toNat := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hs := ctx.separate
  have own := houtside.w32 (d := o + 4 * i) (by omega) (by omega)
  have src := houtside.w32 (d := b + 4 * i) (by omega) (by omega)
  rw [own, src] at hv
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r3) (by omega)
  rw [← hm] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r3).toNat := by
    rw [hm, w32_write_self]
  refine ⟨(houtside.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_⟩
  rw [val32_succ, val32_succ, val32_succ, low, top, pow32_succ]
  have prior := hvalue
  generalize 2 ^ (32 * i) = P at *
  grind

/-- Extend the arithmetic invariant with the next stored word. -/
theorem row_value_step {s0 s t : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n) (inv : RowLoopInv s0 x base o b n i s) (hi : i < n)
    (hm : t.mem = s.mem.writeW (off (State.addr base) (o + 4 * i)) (t.gpr .r3))
    (hv : (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
      x.toNat * w32 s.mem (State.addr base) (b + 4 * i) +
        w32 s.mem (State.addr base) (o + 4 * i) + (s.gpr .r11).toNat) :
    Outside (State.addr base) o (4 * (i + 1)) s0.mem t.mem ∧
      val32 t.mem (State.addr base) o (i + 1) + 2 ^ (32 * (i + 1)) * (t.gpr .r11).toNat =
        val32 s0.mem (State.addr base) o (i + 1) +
          x.toNat * val32 s0.mem (State.addr base) b (i + 1) + (s0.gpr .r11).toNat :=
  row_value_step_of ctx inv.outside inv.value hi hm hv

end VG.Proof.Bignum.Arm
