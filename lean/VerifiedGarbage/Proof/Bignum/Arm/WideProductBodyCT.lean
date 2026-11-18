module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductState
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.WideProductRow
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
meta import VerifiedGarbage.Proof.Bignum.Arm.WideProductState
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.WideProductRow
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.Arm.WideProductArgsCT`, which only this module used -/

section

/-! ### `Bignum.Arm.WideProductHead`, which only this module used -/

section

/-! # The scalar source address comes from a public product control -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem wideProductHead_ok (s : State) {base ap : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = ap) :
    WP isa (.block wideProductArgsHead) s fun t => t.gpr .r0 = base ∧ t.gpr .r1 = ap := by
  have addr (d : Nat) (hd : d + 4 ≤ size) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega_using [hd, this])
  unfold wideProductArgsHead
  refine wp_ldr (a := off (State.addr base) 132) (by decide) (addr 132 (by omega_using [fit]))
    (ws.read (by omega_using [fit])) fun u h => ?_
  refine wp_ldr (a := off (State.addr base) 144) (by decide)
    (by rw [h.other .r0 (by decide)]; exact addr 144 (by omega_using [fit]))
    (by rw [h.rd, h.wr]; exact ws.read (by omega_using [fit])) fun v j => ?_
  refine wp_ldr (a := off (State.addr base) 128) (by decide)
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact addr 128 (by omega_using [fit]))
    (by rw [j.rd, j.wr, h.rd, h.wr]; exact ws.read (by omega_using [fit])) fun t l => WP.block_nil ?_
  exact ⟨by rw [l.other .r0 (by decide), j.other .r0 (by decide), h.other .r0 (by decide)]; exact ptr,
    by rw [l.gpr, j.mem, h.mem]; exact aPtr⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Loading a secret product scalar leaks only its public source address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure WideProductArgsInput (base ap : BitVec 32) (size : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  source : s.mem.readW (off (State.addr base) 128) 32 = ap

theorem wideProductArgs_ct {base ap : BitVec 32} {size : Nat} (fit : 148 ≤ size) :
    RelCT isa (fun s t => WideProductArgsInput base ap size s ∧ WideProductArgsInput base ap size t)
      (.block wideProductArgs) (fun _ _ => True) := by
  let P := fun (s t : State) => WideProductArgsInput base ap size s ∧ WideProductArgsInput base ap size t
  have head : RelCT isa P (.block wideProductArgsHead) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have ready := head.wp (fun s t h => ⟨wideProductHead_ok s h.1.workspace fit h.1.ptr h.1.source,
    wideProductHead_ok t h.2.workspace fit h.2.ptr h.2.source⟩)
  have tail : RelCT isa (fun s t => True ∧ (s.gpr .r0 = base ∧ s.gpr .r1 = ap) ∧
      (t.gpr .r0 = base ∧ t.gpr .r1 = ap)) (.block wideProductArgsTail) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1.1.trans h.2.2.1.symm
    · exact h.2.1.2.trans h.2.2.2.symm
  exact RelCT.block_append (ready.seq tail)

end VG.Proof.Bignum.Arm

end

end

/-! # A wide-product row hides its scalar and multiplicand values -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem wideProductBody_ct {s01 s02 : State} {base : BitVec 32} {size o a b m n i : Nat}
    (ctx1 : WideProductCtx s01 base size o a b m n) (ctx2 : WideProductCtx s02 base size o a b m n)
    (hi : i < m) :
    RelCT isa (fun s t => WideProductInv s01 base o a b m n i s ∧
      WideProductInv s02 base o a b m n i t ∧ s.sp = t.sp) wideProductBody (fun _ _ => True) := by
  let P := fun (s t : State) => WideProductInv s01 base o a b m n i s ∧
    WideProductInv s02 base o a b m n i t ∧ s.sp = t.sp
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i) ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .lr = BitVec.ofNat 32 n
  have wp (s0 s : State) (ctx : WideProductCtx s0 base size o a b m n)
      (h : WideProductInv s0 base o a b m n i s) : WP isa (.block wideProductArgs) s Q := by
    exact WP.mono (wideProductArgs_ok s (ctx.workspace.congr h.rest.wr) ctx.headerFit
      (by have := ctx.aFits; omega_using [hi, this]) h.ptr h.aPtr h.bPtr h.oPtr h.width) (fun _ j => ⟨j.1, j.2.1, j.2.2.1⟩)
  have args := ((wideProductArgs_ct ctx1.headerFit).mono (P' := P)
    (fun _ _ h => ⟨⟨ctx1.workspace.congr h.1.rest.wr, h.1.ptr, h.1.aPtr⟩,
      ⟨ctx2.workspace.congr h.2.1.rest.wr, h.2.1.ptr, h.2.1.aPtr⟩⟩) (fun _ _ h => h)).wp
    (fun s t h => ⟨wp s01 s ctx1 h.1, wp s02 t ctx2 h.2.1⟩)
  have row : RelCT isa (fun s t => True ∧ Q s ∧ Q t) rowFull (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨rowFull_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.1.trans h.2.2.1.symm, h.2.1.2.1.trans h.2.2.2.1.symm,
        h.2.1.2.2.trans h.2.2.2.2.symm⟩ e1 e2, trivial⟩
  have core := (relCT_keep_sp (args.seq row) (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 0)
  have ready := (core.assoc).wp (fun s t h => ⟨
    WP.mono (wideProductRow_ok s ctx1 h.1 hi) (fun _ j => j.2.2.1),
    WP.mono (wideProductRow_ok t ctx2 h.2.1 hi) (fun _ j => j.2.2.1)⟩)
  have next : RelCT isa (fun s t => s.sp = t.sp ∧ s.gpr .r0 = base ∧ t.gpr .r0 = base)
      wideProductNext (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  exact ready.seq next

end VG.Proof.Bignum.Arm
