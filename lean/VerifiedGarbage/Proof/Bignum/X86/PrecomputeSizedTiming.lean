module
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputePair
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86.PrecomputeDataTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicPowerFrame
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeImport
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PublicSetupFast

/-! # Valid moduli select a constant-time precomputation kernel -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic

def PrecomputeValidPair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop :=
  PrecomputePair base bytes len args s t ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len=Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len

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
  have Prepare : RelCT isa (PrecomputeValidPair base bytes len args)
      (.seq (PrecomputeFn.importModulus (Spec.Rsa.modulusWords len))
        (VG.Impl.Bignum.X86.PublicContext.setup (Spec.Rsa.modulusWords len)))
      (PrecomputePair base bytes len args) := by
    intro s t tr ur sf tf H E F
    obtain ⟨Is,Ss⟩ := wp_result (precomputePrepare_ok H.1.left H.2.1) E
    obtain ⟨It,St⟩ := wp_result (precomputePrepare_ok H.1.right H.2.2.1) F
    have Import (u : State) (I : PrecomputeInputs base bytes len args u) :=
      PublicContext.precomputeImport_ok I.scratch I.dimensions.1 I.space (by have := I.lower;omega)
        I.dimensions.2.2 (I.stack 2 (by decide))
        (by rw [← I.nLen];exact I.stack 3 (by decide)) I.nFit I.nRead I.nApart
    cases E with
    | @seq _ _ _ u _ _ _ E1 E2 =>
      cases F with
      | @seq _ _ _ v _ _ _ F1 F2 =>
        have first := (precomputeImport_relCT base bytes len args _ _ _ _ _ _ H.1 E1 F1).1
        obtain ⟨Nu,_,Ku⟩ := wp_result (Import s H.1.left) E1
        obtain ⟨Nv,_,Kv⟩ := wp_result (Import t H.1.right) F1
        have facts := valid_facts H.2.1 H.1.left.lower
        have second := (PublicContext.setup_relCT base bytes (Spec.Rsa.modulusWords len)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len))
          H.1.left.dimensions.1 H.1.left.space facts.2.1 facts.1 _ _ _ _ _ _
          ⟨H.1.left.scratch.of_keeps Ku (by decide),H.1.right.scratch.of_keeps Kv (by decide),
            Nu,by rw [Nv,H.2.2.2]⟩ E2 F2).1
        exact ⟨by rw [first,second],Is,It,Ss.trans (H.1.sp.trans St.symm)⟩
  apply VG.RelCT.assoc
  exact VG.RelCT.seq Prepare ((precomputeExport_relCT _ (args 0)).mono
    (fun _ _ H => ⟨H.agree, (H.left.stack 0 (by decide)).readSrc, (H.right.stack 0 (by decide)).readSrc⟩)
    (fun _ _ h => h))

end VG.Proof.Bignum.X86
