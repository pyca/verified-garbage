module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
meta import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.CsubCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The whole Montgomery square leaks only the width, as `montOp` does -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand)
open VG.Proof.X25519.Arm (Rest)

theorem sqFinishHeader_cert : SqCert [.r0] (.block sqFinishHeader) := ⟨_, by taint_decide⟩
theorem sqFinishLoad_cert : SqCert [.r0] (.block sqFinishLoad) := ⟨_, by taint_decide⟩
theorem sqFinishArgs_cert : SqCert [.r0, .r7] (.block sqFinishArgs) := ⟨_, by taint_decide⟩

section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

theorem sqFinish_ct :
    RelCT isa (fun s t => RedReady base size out a mod M n sp0 n s ∧ RedReady base size out a mod M n sp0 n t)
      sqFinish (fun _ _ => True) := by
  let R := RedReady base size out a mod M n sp0 n
  have rStable : ∀ s t : State, R s → t.mem = s.mem → ∀ {rs : List Reg}, Rest rs s t → R t :=
    fun s t ⟨sp, m0, inv, h⟩ mem _ rest => ⟨rest.sp.trans sp, m0, inv, h.of_mem mem rest⟩
  let P1 := fun s : State => R s ∧ s.gpr .r0 = base
  let P2 := fun s : State => R s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M ∧ s.gpr .r12 = base + BitVec.ofNat 32 mod
  let P3 := fun s : State => R s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M ∧
    s.gpr .r12 = base + BitVec.ofNat 32 mod ∧ s.gpr .r7 = BitVec.ofNat 32 n ∧ s.gpr .r9 = base + BitVec.ofNat 32 out
  let P4 := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 M ∧
    s.gpr .r12 = base + BitVec.ofNat 32 mod ∧ s.gpr .r7 = BitVec.ofNat 32 n ∧
    s.gpr .r9 = base + BitVec.ofNat 32 out ∧ s.gpr .r10 = base + BitVec.ofNat 32 (M + 24 + 4 * n) ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have S1 : RelCT isa (fun s t => R s ∧ R t) (.block [.ldrSp .r0 0]) (fun s t => P1 s ∧ P1 t) :=
    segStack (fun s t hs ht => hs.1.trans ht.1.symm) fun s hs => by
      have hs' := hs
      obtain ⟨_, m0, inv, h⟩ := hs'
      exact WP.mono (sqBase_ok s h.env .r0) fun t ⟨p, mem, rest⟩ => ⟨rStable s t hs mem rest, p⟩
  have S2 : RelCT isa (fun s t => P1 s ∧ P1 t) (.block sqFinishHeader) (fun s t => P2 s ∧ P2 t) := by
    refine seg sqFinishHeader_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
    · obtain ⟨⟨sp, m0, inv, h⟩, p0⟩ := hs
      have := h.env.fits; have := h.env.header
      exact WP.mono (sqFinishHeader_ok s h.env.workspace (by omega) p0 h.env.modNow h.env.metaNow)
        fun t ⟨q12, q0, mem, rest⟩ => ⟨rStable s t ⟨sp, m0, inv, h⟩ mem rest, q0, q12⟩
  have S3 : RelCT isa (fun s t => P2 s ∧ P2 t) (.block sqFinishLoad) (fun s t => P3 s ∧ P3 t) := by
    refine seg sqFinishLoad_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.1.trans ht.2.1.symm
    · obtain ⟨⟨sp, m0, inv, h⟩, p0, p12⟩ := hs
      have := h.env.fits
      exact WP.mono (sqFinishLoad_ok s (n := n) (out := out) h.env.workspace (by omega) p0 h.md.count h.md.outPtr)
        fun t ⟨g7, g9, _, g0, mem, rest⟩ => ⟨rStable s t ⟨sp, m0, inv, h⟩ mem rest, g0.trans p0,
          by rw [rest.gpr .r12 (by simp)]; exact p12, g7, g9⟩
  have S4 : RelCT isa (fun s t => P3 s ∧ P3 t) (.block sqFinishArgs) (fun s t => P4 s ∧ P4 t) := by
    refine seg sqFinishArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
    · obtain ⟨⟨_, m0, inv, h⟩, p0, p12, p7, p9⟩ := hs
      have := h.env.fits
      exact WP.mono (sqFinishArgs_ok s h.env.workspace (by omega) p0 p7)
        fun t ⟨_, g10, glr, _, rest⟩ => ⟨by rw [rest.gpr .r0 (by simp)]; exact p0,
          by rw [rest.gpr .r12 (by simp)]; exact p12, by rw [rest.gpr .r7 (by simp)]; exact p7,
          by rw [rest.gpr .r9 (by simp)]; exact p9, g10, glr⟩
  have S5 : RelCT isa (fun s t => P4 s ∧ P4 t) csub (fun _ _ => True) :=
    segCTEnd csub_ct fun s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
      · exact hs.2.2.2.2.1.trans ht.2.2.2.2.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.2.2.2.trans ht.2.2.2.2.2.symm
  unfold sqFinish
  exact S1.seq (S2.seq (S3.seq (S4.seq S5)))

theorem sqBody_ct :
    RelCT isa (fun s t => SqStart base size out a mod M n sp0 s ∧ SqStart base size out a mod M n sp0 t)
      sqBody (fun _ _ => True) := by
  unfold sqBody
  exact sqInit_ct.seq (crossRows_ct.seq (sqDouble_ct.seq (sqDiag_ct.seq (sqReduce_ct.seq sqFinish_ct))))

end

/-- `squareBody`'s entry: `montFnBody`'s, with the workspace pointer at `sp`. -/
structure SqFnReady (base : BitVec 32) (len w o a : Nat) (s : State) : Prop where
  body : FnBodyReady base len w o a a s
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem squareBases_ready {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a)
    (s : State) (h : SqFnReady base len w o a s) :
    WP isa (.block MontFn.bases) s
      (SqStart base (8 * len) (arrAt w o) (arrAt w a) (arrAt w 0) (arrAt w 2) (2 * w) s.sp) := by
  obtain ⟨hb, stackRead, stackSep, saved⟩ := h
  obtain ⟨ws, layout, width, ptr, po, pa, pb, inverse, operand⟩ := hb
  subst width
  have hw : 2 ≤ wOf s.mem (State.addr base) := layout.1
  have fits : arrAt (wOf s.mem (State.addr base)) 8 ≤ 8 * len := layout.2.2.1
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 ha.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  have env := sqEnv_of_layout s u ws layout ho ha header
    (native_inverse s.mem (State.addr base) (by omega) inverse) operand stackRead stackSep saved mem keep
  exact ⟨keep.sp, ⟨_, env⟩, regs.accPtr, regs.count, regs.aPtr, regs.outPtr⟩

theorem squareBody_ct {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a) :
    RelCT isa (fun s t => s.sp = t.sp ∧ SqFnReady base len w o a s ∧ SqFnReady base len w o a t)
      squareBody (fun _ _ => True) := by
  have family : ∀ sp0 : BitVec 32, RelCT isa (fun s t => (SqFnReady base len w o a s ∧ s.sp = sp0) ∧
      (SqFnReady base len w o a t ∧ t.sp = sp0)) squareBody (fun _ _ => True) := by
    intro sp0
    have ct : RelCT isa (fun s t => (SqFnReady base len w o a s ∧ s.sp = sp0) ∧
        (SqFnReady base len w o a t ∧ t.sp = sp0)) (.block MontFn.bases) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2, .r3, .r12]) _ (by taint_decide)
      intro s t h
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.1.1.body.ptr.trans h.2.1.body.ptr.symm
      · exact h.1.1.body.outIndex.trans h.2.1.body.outIndex.symm
      · exact h.1.1.body.aIndex.trans h.2.1.body.aIndex.symm
      · exact h.1.1.body.bIndex.trans h.2.1.body.bIndex.symm
    have wp (s : State) (h : SqFnReady base len w o a s ∧ s.sp = sp0) :
        WP isa (.block MontFn.bases) s
          (SqStart base (8 * len) (arrAt w o) (arrAt w a) (arrAt w 0) (arrAt w 2) (2 * w) sp0) :=
      h.2 ▸ squareBases_ready ho ha s h.1
    unfold squareBody
    exact (pair_posts ct wp).seq sqBody_ct
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v ⟨⟨h.2.1, rfl⟩, h.2.2, h.1.symm⟩ e1 e2

theorem squareArgs_ready (s : State) {base : BitVec 32} {len w o a : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a)
    (operand : numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) :
    WP isa (.block (montOpArgs o a a)) s (SqFnReady base len w o a) := by
  refine WP.mono (montOpArgs_ok s ho.1 ha.1 ha.1) ?_
  rintro t ⟨po, pa, pb, mem, rest⟩
  refine ⟨⟨h.workspace.congr rest.wr, ?_, ?_, (rest.gpr .r0 (by simp)).trans h.ptr, po, pa, pb, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [mem]; exact h.inverse
  · rw [mem]; exact operand
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [rest.sp, mem]; exact h.saved

theorem squareOp_ct {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w a < numAt t.mem (State.addr base) w 0) ∧
        s.sp = t.sp)
      (squareOp o a) (fun _ _ => True) := by
  let P := fun (s t : State) =>
    (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0) ∧
    (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w a < numAt t.mem (State.addr base) w 0) ∧
      s.sp = t.sp
  have args : RelCT isa P (.block (montOpArgs o a a)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp args (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨squareArgs_ready s h.1.1 ho ha h.1.2, squareArgs_ready t h.2.1.1 ho ha h.2.1.2⟩)
  have body := relCT_keep_sp (squareBody_ct (base := base) (len := len) (w := w) ho ha) (fun _ _ h => h.1)
  exact (ready.seq (body.seq (loadStack_ct .r0 0))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
