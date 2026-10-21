module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectState
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Bignum.Arm.Select
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Mem

/-! In-place masked selection from a separate read-only packed word buffer. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure SelectReadCtx (s : State) (dst src : BitVec 32) (n : Nat) : Prop where
  dstFit : dst.toNat + 4 * n ≤ 2 ^ 32
  srcFit : src.toNat + 4 * n ≤ 2 ^ 32
  countFit : n < 2 ^ 32
  write : InRegions s.wr (State.addr dst) (4 * n)
  read : InRegions (s.rd ++ s.wr) (State.addr src) (4 * n)
  sep : Region.Disjoint ⟨State.addr src, 4 * n⟩ ⟨State.addr dst, 4 * n⟩

structure SelectReadInv (s0 : State) (dst src : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = dst + BitVec.ofNat 32 (4 * i)
  aPtr : s.gpr .r10 = dst + BitVec.ofNat 32 (4 * i)
  bPtr : s.gpr .r12 = src + BitVec.ofNat 32 (4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr dst) 0 (4 * i) s0.mem s.mem
  frame : Frame [⟨State.addr dst, 4 * n⟩] s0.mem s.mem
  value : val32 s.mem (State.addr dst) 0 i = if (s0.gpr .r11).toNat = 0 then
    val32 s0.mem (State.addr dst) 0 i else val32 s0.mem (State.addr src) 0 i
  mask : s.gpr .r4 = 0 - s.gpr .r11
  rest : Rest selectLoopClobbers s0 s

theorem selectRead_value_step {s0 s t : State} {dst src : BitVec 32} {n i : Nat}
    (ctx : SelectReadCtx s0 dst src n) (inv : SelectReadInv s0 dst src n i s) (hi : i < n)
    (hm : t.mem = s.mem.writeW (off (State.addr dst) (4 * i))
      (if (s.gpr .r11).toNat = 0 then s.mem.readW (off (State.addr dst) (4 * i)) 32
        else s.mem.readW (off (State.addr src) (4 * i)) 32)) :
    Outside (State.addr dst) 0 (4 * (i + 1)) s0.mem t.mem ∧
      Frame [⟨State.addr dst, 4 * n⟩] s0.mem t.mem ∧
      val32 t.mem (State.addr dst) 0 (i + 1) = if (s0.gpr .r11).toNat = 0 then
        val32 s0.mem (State.addr dst) 0 (i + 1) else val32 s0.mem (State.addr src) 0 (i + 1) := by
  have aold := inv.outside.w32 (d := 4 * i) (by omega) (by have := ctx.dstFit; omega)
  have bold : s.mem.readW (off (State.addr src) (4 * i)) 32 =
      s0.mem.readW (off (State.addr src) (4 * i)) 32 := by
    apply inv.frame.readW (r := ⟨State.addr src, 4 * n⟩)
    · exact Offset.contains_base _ (by omega) (by have := ctx.srcFit; omega)
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ctx.sep
    · decide
  have bit := inv.rest.gpr .r11 (by simp [selectLoopClobbers])
  have wr := writeW32_outside s.mem (State.addr dst) (d := 4 * i)
    (if (s.gpr .r11).toNat = 0 then s.mem.readW (off (State.addr dst) (4 * i)) 32
      else s.mem.readW (off (State.addr src) (4 * i)) 32) (by have := ctx.dstFit; omega)
  rw [← hm] at wr
  have low := wr.val32 (d := 0) (k := i) (by omega) (by have := ctx.dstFit; omega)
  have top : w32 t.mem (State.addr dst) (4 * i) = if (s0.gpr .r11).toNat = 0 then
      w32 s0.mem (State.addr dst) (4 * i) else w32 s0.mem (State.addr src) (4 * i) := by
    rw [hm, w32_write_self, bit]
    split
    · exact aold
    · exact congrArg BitVec.toNat bold
  refine ⟨(inv.outside.mono (by omega) (by omega)).trans (wr.mono (by omega) (by omega)), ?_, ?_⟩
  · rw [hm]
    exact inv.frame.writeW (r := ⟨State.addr dst, 4 * n⟩) (by simp) _
      (Offset.contains_base _ (by omega) (by have := ctx.dstFit; omega))
  · rw [val32_succ, low, show 0 + 4 * i = 4 * i by omega, top, inv.value]
    split <;> simp only [val32_succ, Nat.zero_add]

end VG.Proof.Bignum.Arm
