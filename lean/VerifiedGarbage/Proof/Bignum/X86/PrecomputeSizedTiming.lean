module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeDataTiming
public import VerifiedGarbage.Proof.Bignum.ModulusCheckMath

/-! # Valid moduli select a constant-time precomputation kernel -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic

def PrecomputeValidPair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop :=
  PrecomputePair base bytes len args s t ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true

theorem precomputePrepare_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputeInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa (.seq (PrecomputeFn.importModulus (Spec.Rsa.modulusWords len))
      (VG.Impl.Bignum.X86.PublicContext.setup (Spec.Rsa.modulusWords len))) s fun t =>
      PrecomputeInputs base bytes len args t ∧ t.gpr .esp = s.gpr .esp := by
  have dims := h.dimensions
  have facts := valid_facts valid h.lower
  have sz := h.space
  have eq := PublicContext.size_eq (Spec.Rsa.modulusWords len)
  refine WP.seq (WP.mono (PublicContext.precomputeImport_ok h.scratch dims.1 h.space
    (by have := h.lower; omega) dims.2.2 (h.stack 2 (by decide))
    (by rw [← h.nLen]; exact h.stack 3 (by decide)) h.nFit h.nRead h.nApart)
    fun u ⟨N, O, K⟩ => ?_)
  refine WP.mono (PublicContext.setup_ok (h.scratch.of_keeps K (by decide)) dims.1 dims.2.1 h.space
    N facts.2.1 facts.1) fun t ⟨_, _, _, Ot, Kt⟩ => ?_
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := K.trans (Kt.mono (by decide))
  have Os : Outside base 0 bytes s.mem t.mem :=
    (O.mono (by omega) (by omega)).trans (PublicContext.power_outside (Ot.mono (by
      intro r hr; exact List.mem_append_left _ hr)) h.space)
  exact ⟨h.keep Ks (by decide) (by decide) Os, Ks.1 _ (by decide)⟩

theorem precomputeSized_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputeValidPair base bytes len args) (PrecomputeFn.sized (Spec.Rsa.modulusWords len))
      (fun _ _ => True) := by
  have Setup : RelCT isa (VG.X86.Taint.Agree argumentTaint)
      (VG.Impl.Bignum.X86.PublicContext.setup (Spec.Rsa.modulusWords len)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (workspaceTaint false)
      (fun _ _ H => agree_regs (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.rf.1 _ (by decide)))
      (hc := contextSetupHint)
    rw [PublicContext.setup_check]
    rfl
  have Prepare : RelCT isa (PrecomputeValidPair base bytes len args)
      (.seq (PrecomputeFn.importModulus (Spec.Rsa.modulusWords len))
        (VG.Impl.Bignum.X86.PublicContext.setup (Spec.Rsa.modulusWords len)))
      (PrecomputePair base bytes len args) := by
    intro s t tr ur sf tf H E F
    have CT := VG.RelCT.seq (precomputeImport_relCT base bytes len args)
      (Setup.mono (fun _ _ J => J.agree) (fun _ _ h => h))
    obtain ⟨Is, Ss⟩ := wp_result (precomputePrepare_ok H.1.left H.2.1) E
    obtain ⟨It, St⟩ := wp_result (precomputePrepare_ok H.1.right H.2.2) F
    exact ⟨(CT _ _ _ _ _ _ H.1 E F).1, Is, It, Ss.trans (H.1.sp.trans St.symm)⟩
  apply VG.RelCT.assoc
  exact VG.RelCT.seq Prepare ((precomputeExport_relCT _ (args 0)).mono
    (fun _ _ H => ⟨H.agree, (H.left.stack 0 (by decide)).readSrc, (H.right.stack 0 (by decide)).readSrc⟩)
    (fun _ _ h => h))

end VG.Proof.Bignum.X86
