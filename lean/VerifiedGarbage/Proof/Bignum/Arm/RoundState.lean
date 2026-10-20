module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundMeta
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Physical layout and postcondition of one Montgomery round -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure RoundCtx (s : State) (base : BitVec 32) (size tmp a b mod acc n : Nat) : Prop where
  workspace : Workspace s base size
  count : 4 ≤ n
  layout : tmp = acc + 4 * (n + 4)
  tmpFits : tmp + 32 ≤ size
  aFits : a + 4 * n ≤ size
  bFits : b + 4 * n ≤ size
  mFits : mod + 4 * n ≤ size
  accA : acc + 4 * (n + 2) ≤ a ∨ a + 4 * n ≤ acc
  accB : acc + 4 * (n + 2) ≤ b ∨ b + 4 * n ≤ acc
  accM : acc + 4 * (n + 2) ≤ mod ∨ mod + 4 * n ≤ acc
  tmpA : tmp + 32 ≤ a ∨ a + 4 * n ≤ tmp
  tmpB : tmp + 32 ≤ b ∨ b + 4 * n ≤ tmp
  tmpM : tmp + 32 ≤ mod ∨ mod + 4 * n ≤ tmp

theorem RoundCtx.congr {s t : State} {base : BitVec 32} {size tmp a b mod acc n : Nat}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hw : t.wr = s.wr) :
    RoundCtx t base size tmp a b mod acc n :=
  ⟨ctx.workspace.congr hw, ctx.count, ctx.layout, ctx.tmpFits, ctx.aFits, ctx.bFits, ctx.mFits,
    ctx.accA, ctx.accB, ctx.accM, ctx.tmpA, ctx.tmpB, ctx.tmpM⟩

theorem RoundCtx.accFits {s : State} {base : BitVec 32} {size tmp a b mod acc n : Nat}
    (ctx : RoundCtx s base size tmp a b mod acc n) : acc + 4 * (n + 2) ≤ size := by
  have := ctx.layout
  have := ctx.tmpFits
  omega

theorem RoundCtx.rowB {s t : State} {base : BitVec 32} {size tmp a b mod acc n : Nat}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hw : t.wr = s.wr) :
    RowCtx t base size acc b n :=
  ⟨ctx.workspace.nowrap, by have := ctx.accFits; omega, ctx.bFits,
    by have := ctx.accB; omega, by rw [hw]; exact ctx.workspace.writable⟩

theorem RoundCtx.rowM {s t : State} {base : BitVec 32} {size tmp a b mod acc n : Nat}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hw : t.wr = s.wr) :
    RowCtx t base size acc mod n :=
  ⟨ctx.workspace.nowrap, by have := ctx.accFits; omega, ctx.mFits,
    by have := ctx.accM; omega, by rw [hw]; exact ctx.workspace.writable⟩

abbrev roundClobbers : List Reg :=
  [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

structure RoundPost (s t : State) (base : BitVec 32) (tmp a b mod acc n i : Nat) (inv : BitVec 32) : Prop where
  hdr : RoundMeta t.mem base tmp a b mod acc n (i + 1) inv
  ptr : t.gpr .r0 = base + BitVec.ofNat 32 tmp
  value : ∃ q < 2 ^ 32, 2 ^ 32 * val32 t.mem (State.addr base) acc (n + 2) =
    val32 s.mem (State.addr base) acc (n + 2) +
      w32 s.mem (State.addr base) (a + 4 * i) * val32 s.mem (State.addr base) b n +
        q * val32 s.mem (State.addr base) mod n
  bound : val32 t.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n
  outside : Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp + 16, 8)] s.mem t.mem
  zero : t.z = decide (i + 1 = n)
  rest : Rest roundClobbers s t

end VG.Proof.Bignum.Arm
