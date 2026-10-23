module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Args
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.Arm.Fios2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Taint

/-! The two-row round's addresses and branches depend only on public
pointers and counts. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (wp_ldr)

/-- A check of `c` from the public registers `rs`, by the analysis for `pub`,
that ends with the registers `out` public. -/
private theorem keeping (pub rs out : List Reg) {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s t, P s t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : (((Taint.analysis pub).check (VG.Arm.Taint.ofRegs rs) c hint).map
      fun τ => (RegSet.ofList out).subset τ.regs) = some true) :
    RelCT isa P c (fun s t => ∀ r ∈ out, s.gpr r = t.gpr r) := by
  intro s t tr₁ tr₂ u v h ex ey
  obtain ⟨τ, ht, ho⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨trace, final⟩ := VG.Taint.check_sound ht (VG.Arm.Taint.agree_ofRegs (hp s t h)) ex ey
  exact ⟨trace, fun r hr => final.rf.1 r (RegSet.mem_of_subset ho (RegSet.mem_ofList.mpr hr))⟩

theorem scan_relCT : RelCT isa
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧
      s.gpr .r4 = t.gpr .r4 ∧ s.gpr .lr = t.gpr .lr)
    (.seq VG.Impl.Bignum.Arm.Fios2.first VG.Impl.Bignum.Arm.Fios2.loop)
    (fun s t => ∀ r ∈ [.r0, .r12, .r4], s.gpr r = t.gpr r) := by
  apply keeping [.r0, .r12, .r4, .lr] [.r0, .r12, .r4, .lr] [.r0, .r12, .r4] ?_ (by taint_decide)
  intro s t h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem top_relCT : RelCT isa (fun s t => ∀ r ∈ [.r0, .r12, .r4], s.gpr r = t.gpr r)
    VG.Impl.Bignum.Arm.Fios2.top (fun s t => ∀ r ∈ [.r0], s.gpr r = t.gpr r) :=
  keeping [.r0] [.r0, .r12, .r4] [.r0] (fun _ _ h => h) (by taint_decide)

theorem code_relCT : RelCT isa
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧
      s.gpr .r4 = t.gpr .r4 ∧ s.gpr .lr = t.gpr .lr)
    VG.Impl.Bignum.Arm.Fios2.code (fun s t => s.gpr .r0 = t.gpr .r0) := by
  have h := scan_relCT.seq top_relCT
  unfold VG.Impl.Bignum.Arm.Fios2.code
  exact (RelCT.assoc h).mono (fun _ _ h => h) (fun _ _ h => h .r0 (by simp))

theorem args_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i tmp s ∧
      StageReady base size tmp a b mod acc n i tmp t)
      (.block VG.Impl.Bignum.Arm.Fios2.args) (fun _ _ => True) := by
  let P := StageReady base size tmp a b mod acc n i tmp
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
    s.gpr .r3 = base + BitVec.ofNat 32 (a + 4 * i)
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block [.ldr .r3 .r0 16])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.2.2.trans h.2.2.2.symm)
  have wp (s : State) (h : P s) : WP isa (.block [.ldr .r3 .r0 16]) s Q := by
    obtain ⟨ctx, ⟨inv, hdr⟩, ptr⟩ := h
    have fits := ctx.tmpFits
    refine wp_ldr (by decide) (ctx.workspace.ea ptr (by omega))
      (ctx.workspace.read (by omega)) fun t u => WP.block_nil ?_
    exact ⟨(u.other .r0 (by decide)).trans ptr, u.gpr.trans hdr.aPtr⟩
  unfold VG.Impl.Bignum.Arm.Fios2.args
  change RelCT isa _ (.block ([.ldr .r3 .r0 16] ++ _)) _
  apply RelCT.block_append
  refine (pair_posts ct wp).seq (RelCT.taint (A := taint)
    (Taint.ofRegs [.r0, .r3]) ?_ (by taint_decide))
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem round_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i + 2 ≤ n) :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n i s ∧
      RoundReady base size tmp a b mod acc n i t)
      VG.Impl.Bignum.Arm.Fios2.round (fun _ _ => True) := by
  let P := RoundReady base size tmp a b mod acc n i
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .r4 = base + BitVec.ofNat 32 mod ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block VG.Impl.Bignum.Arm.Fios2.args)
      (fun _ _ => True) := args_ct.mono
    (fun _ _ h => ⟨h.1.stage, h.2.stage⟩) (fun _ _ h => h)
  have wp (s : State) (h : P s) : WP isa (.block VG.Impl.Bignum.Arm.Fios2.args) s Q := by
    obtain ⟨inv, hdr, _⟩ := h.secret
    refine WP.mono (args_ok s h.ctx hdr hi h.ptr) ?_
    rintro t ⟨_, _, p0, p12, p4, _, _, count, _⟩
    exact ⟨p0, p12, p4, count⟩
  have scan : RelCT isa (fun s t => Q s ∧ Q t) VG.Impl.Bignum.Arm.Fios2.code
      (fun s t => s.gpr .r0 = t.gpr .r0) := code_relCT.mono
    (fun _ _ h => ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm,
      h.1.2.2.1.trans h.2.2.2.1.symm, h.1.2.2.2.trans h.2.2.2.2.symm⟩)
    (fun _ _ h => h)
  have finish : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
      (.block VG.Impl.Bignum.Arm.Fios2.finish) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h)
  exact (pair_posts ct wp).seq (scan.seq finish)

end VG.Proof.Bignum.Arm.Fios2
