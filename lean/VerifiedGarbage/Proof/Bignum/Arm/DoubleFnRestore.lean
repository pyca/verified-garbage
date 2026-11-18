module

import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBody
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
meta import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
public import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
public import VerifiedGarbage.Impl.Bignum.Arm.Double
import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Double
meta import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT

/-! ### `Bignum.Arm.DoubleFnBodyCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.DoubleCT`, which only this module used -/

section

/-! # Modular doubling reveals only its public workspace layout -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

def DoubleReady (base : BitVec 32) (size out tmp a b mod acc n : Nat) (s : State) : Prop :=
  CoreReady base size out tmp a b mod acc n s ∧ w32 s.mem (State.addr base) a = 2

def DoubleInitReady (base : BitVec 32) (size out tmp a b mod acc n : Nat) (s : State) : Prop :=
  InitReady base size out tmp a b mod acc n s ∧ w32 s.mem (State.addr base) a = 2

theorem doubleCore_ct {base : BitVec 32} {size out tmp a b mod acc n : Nat} (ht : tmp + 32 ≤ size) (hn : 0 < n) :
    RelCT isa (fun s t => DoubleReady base size out tmp a b mod acc n s ∧
      DoubleReady base size out tmp a b mod acc n t) doubleCore (fun _ _ => True) := by
  let P := DoubleReady base size out tmp a b mod acc n
  have ct : RelCT isa (fun s t => P s ∧ P t) doubleProduct (fun _ _ => True) := by
    unfold doubleProduct
    have stage := (productStage_ct (base := base) (size := size) (tmp := tmp) (a := a)
      (b := b) (mod := mod) (acc := acc) (n := n) (i := 0) hn).mono
      (fun _ _ (h : P _ ∧ P _) => ⟨h.1.1.round.stage, h.2.1.round.stage⟩) (fun _ _ h => h)
    refine stage.seq ?_
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : P s) : WP isa doubleProduct s (FinishReady base size tmp out acc mod n) :=
    WP.mono (doubleProduct_ok s h.1 h.2) (fun _ h => h.2.1)
  exact (pair_posts ct wp).seq (montFinish_ct ht)

theorem doubleInit_ready {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (s : State) (h : DoubleInitReady base size out tmp a b mod acc n s) :
    WP isa montInit s (DoubleReady base size out tmp a b mod acc n) := by
  obtain ⟨inv, regs, inverse⟩ := h.1.secret
  refine WP.mono (montInit_ok s h.1.ctx regs h.1.operand inverse) ?_
  rintro t ⟨ready, outside, rest⟩
  have ctx := h.1.ctx
  have hn := ctx.count
  have nowrap := ctx.workspace.nowrap
  have fit := ctx.aFits
  have accA := ctx.accA
  have tmpA := ctx.tmpA
  refine ⟨ready, ?_⟩
  rw [outs_word32 outside (d := a) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fit])]
  exact h.2

theorem doubleBody_ct {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (ht : tmp + 32 ≤ size) (hn : 0 < n) :
    RelCT isa (fun s t => DoubleInitReady base size out tmp a b mod acc n s ∧
      DoubleInitReady base size out tmp a b mod acc n t) doubleBody (fun _ _ => True) := by
  let P := DoubleInitReady base size out tmp a b mod acc n
  have ct : RelCT isa (fun s t => P s ∧ P t) montInit (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨is, rs, _⟩ := h.1.1.secret
    obtain ⟨it, rt, _⟩ := h.2.1.secret
    exact ⟨montInit_ct s t tr1 tr2 u v trivial trivial
      ⟨rs.tmpPtr.trans rt.tmpPtr.symm, rs.accPtr.trans rt.accPtr.symm, rs.count.trans rt.count.symm⟩ e1 e2, trivial⟩
  exact (pair_posts ct doubleInit_ready).seq (doubleCore_ct ht hn)

end VG.Proof.Bignum.Arm

end

end

/-! # Modular doubling through the header has the same public inputs as Montgomery multiplication -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand)

def DoubleFnReady (base : BitVec 32) (len w o a b : Nat) (s : State) : Prop :=
  FnBodyReady base len w o a b s ∧ w32 s.mem (State.addr base) (arrAt w a) = 2

theorem doubleBases_ready {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (s : State) (ready : DoubleFnReady base len w o a b s) :
    WP isa (.block MontFn.bases) s
      (DoubleInitReady base (8 * len) (arrAt w o) (arrAt w 3) (arrAt w a) (arrAt w b) (arrAt w 0) (arrAt w 2) (2 * w)) := by
  have h := ready.1
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  obtain ⟨ctx, _⟩ := layout_context h.workspace hw fits ho ha hb
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega_using [fits]
  refine WP.mono (bases_ok s h.workspace bound header ho.1 ha.1 hb.1 h.ptr h.outIndex h.aIndex h.bIndex) ?_
  rintro t ⟨regs, mem, keep⟩
  refine ⟨⟨ctx.congr keep.wr, ⟨_, regs, ?_⟩, ?_⟩, ?_⟩
  · rw [mem]; exact native_inverse s.mem (State.addr base) (by omega_using [hw]) h.inverse
  · rw [mem, ← numAt_native, ← numAt_native]; exact h.operand
  · rw [mem]; exact ready.2

theorem doubleFnBody_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) :
    RelCT isa (fun s t => DoubleFnReady base len w o a b s ∧ DoubleFnReady base len w o a b t)
      doubleFnBody (fun _ _ => True) := by
  have ct : RelCT isa (fun s t => DoubleFnReady base len w o a b s ∧ DoubleFnReady base len w o a b t)
      (.block MontFn.bases) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.1.ptr.trans h.2.1.ptr.symm
    · exact h.1.1.outIndex.trans h.2.1.outIndex.symm
    · exact h.1.1.aIndex.trans h.2.1.aIndex.symm
    · exact h.1.1.bIndex.trans h.2.1.bIndex.symm
  exact (pair_posts ct (doubleBases_ready ho ha hb)).seq (doubleBody_ct fit hn)

end VG.Proof.Bignum.Arm

end

end

/-! # Compose modular doubling inside the outer RSA stack frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem doubleFnRestore_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (ready : DoubleFnReady base len w o a b s) (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (read : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa doubleFnRestore s fun t =>
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o =
        (2 * numAt s.mem (State.addr base) w b) % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r0 = base := by
  have h := ready.1
  have body := doubleFnBody_ok s h.workspace h.layout ho ha hb h.ptr h.outIndex h.aIndex h.bIndex
    (by rw [h.width]; exact ready.2) (by rw [h.width]; exact h.inverse) (by rw [h.width]; exact h.operand)
  simp only [h.width] at body
  rw [doubleFnRestore, WP.seq_iff]
  refine WP.mono body ?_
  rintro u ⟨bound, value, keeps, frame, rest⟩
  have savedU := saved_base_kept frame sep saved rest.sp
  have readU : InRegions (u.rd ++ u.wr) (State.addr u.sp) 4 := by
    rw [rest.rd, rest.wr, rest.sp]; exact read
  refine WP.mono (restoreBase_ok u readU savedU) ?_
  rintro t ⟨ptr, mem, keep⟩
  rw [← mem] at bound value keeps frame
  exact ⟨bound, value, keeps, frame, rest.trans (keep.mono (by decide)), ptr⟩

theorem doubleFnRestore_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) :
    RelCT isa (fun s t => DoubleFnReady base len w o a b s ∧
      DoubleFnReady base len w o a b t ∧ s.sp = t.sp) doubleFnRestore (fun _ _ => True) := by
  have body := relCT_keep_sp
    ((doubleFnBody_ct ho ha hb fit hn).mono
      (P' := fun (s t : State) => DoubleFnReady base len w o a b s ∧
        DoubleFnReady base len w o a b t ∧ s.sp = t.sp)
      (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact (body.seq (loadStack_ct .r0 0)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
