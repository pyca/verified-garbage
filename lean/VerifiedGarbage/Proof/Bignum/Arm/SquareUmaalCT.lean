module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
import VerifiedGarbage.Proof.Bignum.Arm.SquareUmaalDiag
import VerifiedGarbage.Proof.Bignum.Arm.SquareUmaalLoopCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT
meta import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal

/-! UMAAL diagonal arithmetic is silent and keeps the square's public schedule. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt Operand)


section
variable {base : BitVec 32} {size out a mod M n : Nat} {sp0 : BitVec 32}

theorem sqDiagU_ct :
    RelCT isa (fun s t => DblReady base size out a mod M n sp0 s ∧ DblReady base size out a mod M n sp0 t) sqDiagU
      (fun s t => ProdReady base size out a mod M n sp0 s ∧ ProdReady base size out a mod M n sp0 t) := by
  by_cases valid : 0 < n ∧ n < 2 ^ 32
  ·
    refine phase ?_ fun s ⟨sp, m0, inv, h⟩ =>
      WP.mono (sqDiagPhaseU_ok s h) fun t ⟨ht, rt⟩ => ⟨rt.sp.trans sp, m0, inv, ht⟩
    let P2 := fun s : State => s.gpr .r12 = base + BitVec.ofNat 32 a ∧ s.gpr .lr = BitVec.ofNat 32 n ∧
      s.gpr .r0 = base + BitVec.ofNat 32 (M + 24)
    have A := sqAnchor_ct (P := DblReady base size out a mod M n sp0)
      (fun s ⟨sp, m0, inv, h⟩ => ⟨sp, m0, inv, h.env⟩)
      (fun s t ⟨sp, m0, inv, h⟩ mem rest => ⟨rest.sp.trans sp, m0, inv,
        ⟨h.env.of_mem mem rest, by rw [mem]; exact h.md, by rw [mem]; exact h.value, by rw [mem]; exact h.top⟩⟩)
    have B : RelCT isa (fun s t => (DblReady base size out a mod M n sp0 s ∧ s.gpr .r0 = base + BitVec.ofNat 32 M) ∧
        (DblReady base size out a mod M n sp0 t ∧ t.gpr .r0 = base + BitVec.ofNat 32 M)) (.block sqDiagArgs)
        (fun s t => P2 s ∧ P2 t) := by
      refine seg sqDiagArgs_cert (fun s t hs ht r hr => ?_) (fun s hs => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact hs.2.trans ht.2.symm
      · obtain ⟨⟨_, m0, inv, h⟩, p0⟩ := hs
        have := h.env.fits
        exact WP.mono (sqDiagArgs_ok s (M := M) (n := n) (a := a) h.env.workspace (by omega) p0 h.md.count
          h.md.aPtr) fun t ⟨p12, plr, p0, _⟩ => ⟨p12, plr, p0⟩
    have C : RelCT isa (fun s t => P2 s ∧ P2 t) diagLoopU (fun _ _ => True) :=
      (diagLoopU_ct valid.1 valid.2).mono
        (fun _ _ h => ⟨h.1.2.2.trans h.2.2.2.symm, h.1.1.trans h.2.1.symm, h.1.2.1, h.2.2.1⟩)
        (fun _ _ h => h)
    unfold sqDiagU
    exact A.seq (B.seq C)
  · apply RelCT.of_false
    intro s t h
    obtain ⟨_, _, _, hs⟩ := h.1
    have hc := hs.env.count
    have hf := hs.env.fits
    have hn := hs.env.workspace.nowrap
    exact valid ⟨by omega, by omega⟩

theorem sqBodyU_ct :
    RelCT isa (fun s t => SqStart base size out a mod M n sp0 s ∧ SqStart base size out a mod M n sp0 t)
      sqBodyU (fun _ _ => True) := by
  unfold sqBodyU
  exact sqInit_ct.seq (crossRows_ct.seq (sqDouble_ct.seq (sqDiagU_ct.seq (sqReduce_ct.seq sqFinish_ct))))

end

theorem squareBodyU_ct {base : BitVec 32} {len w o a : Nat} (ho : Operand o) (ha : Operand a) :
    RelCT isa (fun s t => s.sp = t.sp ∧ SqFnReady base len w o a s ∧ SqFnReady base len w o a t)
      squareBodyU (fun _ _ => True) := by
  have family : ∀ sp0 : BitVec 32, RelCT isa (fun s t => (SqFnReady base len w o a s ∧ s.sp = sp0) ∧
      (SqFnReady base len w o a t ∧ t.sp = sp0)) squareBodyU (fun _ _ => True) := by
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
    unfold squareBodyU
    exact (pair_posts ct wp).seq sqBodyU_ct
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v ⟨⟨h.2.1, rfl⟩, h.2.2, h.1.symm⟩ e1 e2

end VG.Proof.Bignum.Arm
