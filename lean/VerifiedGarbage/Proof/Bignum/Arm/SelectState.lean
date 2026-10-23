module

public import VerifiedGarbage.Proof.Bignum.Arm.SubState
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.TCB.Arm.Isa

/-! # The prefix invariant of branch-free multiword selection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

abbrev selectLoopClobbers : List Reg := [.r0, .r1, .r2, .r3, .r4, .r10, .r12, .lr]

structure SelectInv (s0 : State) (base : BitVec 32) (o a b n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  aPtr : s.gpr .r10 = base + BitVec.ofNat 32 (a + 4 * i)
  bPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i = if (s0.gpr .r11).toNat = 0 then
    val32 s0.mem (State.addr base) a i else val32 s0.mem (State.addr base) b i
  mask : s.gpr .r4 = 0 - s.gpr .r11
  rest : Rest selectLoopClobbers s0 s

theorem select_value_step {s0 s t : State} {base : BitVec 32} {size o a b n i : Nat}
    (ctx : SubCtx s0 base size o a b n) (inv : SelectInv s0 base o a b n i s) (hi : i < n)
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
  have aold := inv.outside.w32 (d := a + 4 * i) (by omega_arith) (by omega_arith)
  have bold := inv.outside.w32 (d := b + 4 * i) (by omega_arith) (by omega_arith)
  have bit := inv.rest.gpr .r11 (by simp [selectLoopClobbers])
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i)
    (if (s.gpr .r11).toNat = 0 then s.mem.readW (off (State.addr base) (a + 4 * i)) 32
      else s.mem.readW (off (State.addr base) (b + 4 * i)) 32) (by omega_arith)
  rw [← hm] at wr
  have low := wr.val32 (d := o) (k := i) (by omega_arith) (by omega_arith)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = if (s0.gpr .r11).toNat = 0 then
      w32 s0.mem (State.addr base) (a + 4 * i) else w32 s0.mem (State.addr base) (b + 4 * i) := by
    rw [hm, w32_write_self, bit]
    split <;> first | exact aold | exact bold
  refine ⟨(inv.outside.mono (Nat.le_refl _) (by omega_arith)).trans (wr.mono (by omega_arith) (by omega_arith)), ?_⟩
  rw [val32_succ, low, top, inv.value]
  split <;> rw [val32_succ]

end VG.Proof.Bignum.Arm
