module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.CvABI
public import VerifiedGarbage.Proof.Rsa.X86.CvFrames
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt

import VerifiedGarbage.Proof.Rsa.X86.CvBodyTiming
import VerifiedGarbage.Proof.Rsa.X86.CvEntryTiming
import VerifiedGarbage.Proof.Rsa.X86.CvArgumentsEq
import VerifiedGarbage.Proof.Rsa.X86.CvObservations
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Rsa.X86.CvInstalled
import VerifiedGarbage.Proof.Rsa.X86.CvBuffers
import VerifiedGarbage.Proof.Rsa.X86.CvResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame

/-! # The complete CRT operation leaks only the contract's declared public inputs -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.CrtValuesRt (code)

theorem operation_trace {s t : State} (a : ABI s) (b : ABI t)
    (args : ∀ i < 16, arg s i = arg t i) (sp : s.gpr .esp = t.gpr .esp)
    (modulus : inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa code s tr sf) (et : Exec isa code t ur tf) : tr = ur := by
  have a6 := args 6 (by decide)
  have a7 := args 7 (by decide)
  have a14 := args 14 (by decide)
  have a15 := args 15 (by decide)
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (entry_relCT _ _ _ _ _ _
        ⟨sp, a14, (a.stackArgument (by decide : 14 < 16)).readSrc,
          (b.stackArgument (by decide : 14 < 16)).readSrc⟩ e1 f1).1
      obtain ⟨hs, _, ks, os⟩ := wp_result (installed_ok a) e1
      obtain ⟨ht, _, kt, ot⟩ := wp_result (installed_ok b) f1
      have hv : Inputs (caller s) v := by
        have j := ht.argsEq args
        simpa only [caller, argumentPointer, ← a7, ← a14, ← a15] using j
      have pair : Pair (caller s) u v :=
        ⟨hs, hv, (ks.1 _ (by decide)).trans (sp.trans (kt.1 _ (by decide)).symm)⟩
      have same : inputBytes (caller s) u.mem 0 = inputBytes (caller s) v.mem 0 := by
        have ns := VG.Proof.Bignum.scratch_bytes os (by have := a.lengths.2; change (arg s 7).toNat ≤ _; omega)
          (a.inApart _ (a.inputMember 0) _ (by simp [CallGeometry.writes]))
        have nt := VG.Proof.Bignum.scratch_bytes ot (by have := b.lengths.2; change (arg t 7).toNat ≤ _; omega)
          (b.inApart _ (b.inputMember 0) _ (by simp [CallGeometry.writes]))
        change inputBytes (caller s) u.mem 0 = inputBytes (caller s) s.mem 0 at ns
        change inputBytes (caller t) v.mem 0 = inputBytes (caller t) t.mem 0 at nt
        have align : inputBytes (caller s) v.mem 0 = inputBytes (caller t) v.mem 0 := by
          simp only [inputBytes, caller, CallGeometry.buffer]
          change Spec.Rsa.bytesAt v.mem (byteAddr (arg s 6)) (arg s 7).toNat =
            Spec.Rsa.bytesAt v.mem (byteAddr (arg t 6)) (arg t 7).toNat
          rw [a6, a7]
        exact ns.trans (modulus.trans (align.trans nt).symm)
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have espu : u.gpr .esp = s.gpr .esp := ks.1 _ (by decide)
          have fit : (u.gpr .esp).toNat + 68 ≤ 2 ^ 32 := by rw [espu]; exact a.stackBound
          have apart : ∀ r ∈ (caller s).writes, Region.Disjoint ⟨(u.gpr .esp).setWidth 64, 68⟩ r := by
            intro r hr
            rw [espu]
            exact VG.X86.Taint.frame_disjoint (n := 64) (by have := a.stackBound; omega) (a.retApart r hr)
              (a.argsApart r hr)
          have eq2 := (body_relCT (caller s) a.lengths_ok _ fit apart _ _ _ _ _ _ ⟨⟨pair, rfl⟩, same⟩ e2 f2).1
          obtain ⟨hx, _, _, kx⟩ := wp_result (body_ok hs a.lengths_ok) e2
          obtain ⟨hy, _, _, ky⟩ := wp_result (body_ok hv a.lengths_ok) f2
          have next := pair.after hx hy kx ky (by decide)
          have eq3 := (publicRestore_relCT _ _ _ _ _ _ next.workspace e3 f3).1
          rw [eq1, eq2, eq3]

theorem constantTime : ConstantTime isa (Spec.Rsa.crtValuesContract abi 20).pre
    (Spec.Rsa.crtValuesContract abi 20).pub code := by
  intro s t tr ur sf tf hs ht h es et
  have args := arguments_eq h
  exact operation_trace (abi_of hs) (abi_of ht) args.2 args.1 (modulus_eq h) es et

end VG.Proof.Rsa.X86.CrtValues
