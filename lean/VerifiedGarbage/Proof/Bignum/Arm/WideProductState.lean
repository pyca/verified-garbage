module
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Invariants for an exact wide product with fixed public row counts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure WideProductCtx (s : State) (base : BitVec 32) (size o a b m n : Nat) : Prop where
  workspace : Workspace s base size
  positiveA : 0 < m
  positiveB : 0 < n
  headerFit : 148 ≤ size
  aHeader : 256 ≤ a
  bHeader : 256 ≤ b
  oHeader : 256 ≤ o
  aFits : a + 4 * m ≤ size
  bFits : b + 4 * n ≤ size
  outFits : o + 4 * (m + n + 2) ≤ size
  separateA : o + 4 * (m + n + 2) ≤ a ∨ a + 4 * m ≤ o
  separateB : o + 4 * (m + n + 2) ≤ b ∨ b + 4 * n ≤ o
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

structure WideProductInv (s0 : State) (base : BitVec 32) (o a b m n i : Nat) (s : State) : Prop where
  index : i ≤ m
  ptr : s.gpr .r0 = base
  aPtr : s.mem.readW (off (State.addr base) 128) 32 = base + BitVec.ofNat 32 (a + 4 * i)
  bPtr : s.mem.readW (off (State.addr base) 132) 32 = base + BitVec.ofNat 32 b
  oPtr : s.mem.readW (off (State.addr base) 136) 32 = base + BitVec.ofNat 32 (o + 4 * i)
  count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 (m - i)
  width : s.mem.readW (off (State.addr base) 144) 32 = BitVec.ofNat 32 n
  outside : Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s0.mem s.mem
  value : val32 s.mem (State.addr base) o (m + n + 2) =
    val32 s0.mem (State.addr base) a i * val32 s0.mem (State.addr base) b n
  rest : Rest roundClobbers s0 s

theorem WideProductCtx.frame {s t : State} {base : BitVec 32} {size o a b m n : Nat}
    (h : WideProductCtx s base size o a b m n)
    (outside : Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s.mem t.mem) :
    Frame [⟨State.addr base, size⟩] s.mem t.mem := by
  refine outside_workspace (o := 0) (n := size) ?_ (by omega)
  intro x hx
  apply outside x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have := h.headerFit
  have := h.outFits
  rcases hr with rfl | rfl <;> omega

theorem WideProductInv.source {s0 s : State} {base : BitVec 32} {size o a b m n i : Nat}
    (ctx : WideProductCtx s0 base size o a b m n) (h : WideProductInv s0 base o a b m n i s) (hi : i < m) :
    w32 s.mem (State.addr base) (a + 4 * i) = w32 s0.mem (State.addr base) (a + 4 * i) ∧
      val32 s.mem (State.addr base) b n = val32 s0.mem (State.addr base) b n := by
  have nowrap := ctx.workspace.nowrap
  have aFits := ctx.aFits
  have bFits := ctx.bFits
  have aHeader := ctx.aHeader
  have bHeader := ctx.bHeader
  have sepA := ctx.separateA
  have sepB := ctx.separateB
  have word := h.outside.val32 (d := a + 4 * i) (k := 1)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> omega) (by omega)
  refine ⟨?_, h.outside.val32 ?_ (by omega)⟩
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using word
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega

end VG.Proof.Bignum.Arm
