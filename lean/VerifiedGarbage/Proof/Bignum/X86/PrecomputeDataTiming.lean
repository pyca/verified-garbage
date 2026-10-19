module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputePair
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeImport
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeSized
public import VerifiedGarbage.Proof.Bignum.X86.PublicTiming

/-! # Fixed-width precomputation has data-independent arithmetic and copy traces -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic

def precomputeOutputTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .esp, .ebx], flags := false }

theorem precomputeOut_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree precomputeOutputTaint) (precomputeOut n) (fun _ _ => True) := by
  have H : RelCT isa (VG.X86.Taint.Agree precomputeOutputTaint) (precomputeOut n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply erased_relCT (precomputeOut n) (precomputeOut 1)
      (VG.Taint.hintOf taint precomputeOutputTaint (precomputeOut 1)) rfl rfl rfl
    rfl
  exact H.mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem precomputeOutputArgs_ok {s : State} {dst : BitVec 32}
    (D : readSrc s (.mem (PublicFn.argument 0)) = some dst) :
    WP isa (.block [.mov .ebx (.mem (PublicFn.argument 0))]) s fun t =>
      t.gpr .ebx = dst ∧ t.mem = s.mem ∧ Keeps [.ebx] s t := by
  exact wp_movS D fun _ T _ => WP.block_nil ⟨T.gpr, T.mem, T.keeps⟩

theorem precomputeExport_relCT (n : Nat) (dst : BitVec 32) :
    RelCT isa (fun s t => VG.X86.Taint.Agree argumentTaint s t ∧
      readSrc s (.mem (PublicFn.argument 0)) = some dst ∧
      readSrc t (.mem (PublicFn.argument 0)) = some dst)
      (.seq (.block [.mov .ebx (.mem (PublicFn.argument 0))]) (precomputeOut n)) (fun _ _ => True) := by
  refine VG.RelCT.seq ?_ (precomputeOut_relCT n)
  intro s t tr ur sf tf ⟨A, Ds, Dt⟩ E F
  have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint)
      (.block [.mov .ebx (.mem (PublicFn.argument 0))]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) argumentTaint (fun _ _ h => h) (hc := .block [])
    rfl
  obtain ⟨Ps, _, Ks⟩ := wp_result (precomputeOutputArgs_ok Ds) E
  obtain ⟨Pt, _, Kt⟩ := wp_result (precomputeOutputArgs_ok Dt) F
  refine ⟨(CT _ _ _ _ _ _ A E F).1, agree_regs (rs := [.edi, .esp, .ebx]) ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · exact Ps.trans Pt.symm

theorem precomputeImport_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputePair base bytes len args) (PrecomputeFn.importModulus (Spec.Rsa.modulusWords len))
      (PrecomputePair base bytes len args) := by
  intro s t tr ur sf tf H E F
  have CT := VG.RelCT.seq (loadArguments_relCT 2 3 (args 2) (args 3))
    (loadBE_relCT (Spec.Rsa.modulusWords len) (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0))
  have T := (CT _ _ _ _ _ _ ⟨H.agree, (H.left.stack 2 (by decide)).readSrc,
    (H.right.stack 2 (by decide)).readSrc, (H.left.stack 3 (by decide)).readSrc,
    (H.right.stack 3 (by decide)).readSrc⟩ E F).1
  have W (u : State) (I : PrecomputeInputs base bytes len args u) :=
    PublicContext.precomputeImport_ok I.scratch I.dimensions.1 I.space (by have := I.lower; omega)
      I.dimensions.2.2 (I.stack 2 (by decide))
      (by rw [← I.nLen]; exact I.stack 3 (by decide)) I.nFit I.nRead I.nApart
  obtain ⟨_, Os, Ks⟩ := wp_result (W s H.left) E
  obtain ⟨_, Ot, Kt⟩ := wp_result (W t H.right) F
  have sz := H.left.space
  have eq := PublicContext.size_eq (Spec.Rsa.modulusWords len)
  exact ⟨T, H.keep Ks Kt (by decide) (by decide) (Os.mono (by omega) (by omega))
    (Ot.mono (by omega) (by omega))⟩

end VG.Proof.Bignum.X86
