module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvABI
public import VerifiedGarbage.Proof.Rsa.X86.RvResult

import VerifiedGarbage.Proof.Rsa.X86.RvBodyTiming
import VerifiedGarbage.Proof.Rsa.X86.RvEntryTiming
import VerifiedGarbage.Proof.Rsa.X86.RvArgumentsEq
import VerifiedGarbage.Proof.Rsa.X86.RvObservations
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Rsa.X86.RvReturn
import VerifiedGarbage.Proof.Rsa.X86.RvInstalled
import VerifiedGarbage.Proof.Rsa.X86.RvBuffers
import VerifiedGarbage.Proof.Rsa.X86.RvResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame

/-! # The complete recovery operation leaks only the contract's declared public inputs -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Recover

theorem operation_trace {s t : State} (a : ABI s) (b : ABI t)
    (args : ∀ i < 12, arg s i = arg t i) (sp : s.gpr .esp = t.gpr .esp)
    (modulus : inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0)
    (attempts : (calculated (caller s) s.mem).2 = (calculated (caller t) t.mem).2)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa VG.Impl.Rsa.X86.RecoverRt.code s tr sf) (et : Exec isa VG.Impl.Rsa.X86.RecoverRt.code t ur tf) :
    tr = ur := by
  have a4 := args 4 (by decide)
  have a5 := args 5 (by decide)
  have a10 := args 10 (by decide)
  have a11 := args 11 (by decide)
  have a0 := args 0 (by decide)
  have a1 := args 1 (by decide)
  have a2 := args 2 (by decide)
  have a3 := args 3 (by decide)
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (entry_relCT _ _ _ _ _ _
        ⟨sp, a10, (a.stackArgument (by decide : 10 < 12)).readSrc,
          (b.stackArgument (by decide : 10 < 12)).readSrc⟩ e1 f1).1
      obtain ⟨hs, _, ks, os⟩ := wp_result (installed_ok a) e1
      obtain ⟨ht, _, kt, ot⟩ := wp_result (installed_ok b) f1
      have hv : Inputs (caller s) v := by
        refine ht.geoEq (by simp only [caller, argumentPointer, a10]) (by simp only [caller, a11])
          (by simp only [caller, a5]) sp ?_ fun i hi => args i hi
        change s.wr = t.wr
        rw [a.wr, b.wr]
        simp only [caller, CallGeometry.buffer, argumentPointer, argAddr, a0, a1, a2, a3, a10, a11, sp]
      have pair : Pair (caller s) u v :=
        ⟨hs, hv, (ks.1 _ (by decide)).trans (sp.trans (kt.1 _ (by decide)).symm)⟩
      have same : inputBytes (caller s) u.mem 0 = inputBytes (caller s) v.mem 0 := by
        have ns := VG.Proof.Bignum.scratch_bytes os (by have := a.lengths.2; change (arg s 5).toNat ≤ _; omega)
          (a.inApart _ (a.inputMember 0) _ (by simp))
        have nt := VG.Proof.Bignum.scratch_bytes ot (by have := b.lengths.2; change (arg t 5).toNat ≤ _; omega)
          (b.inApart _ (b.inputMember 0) _ (by simp))
        change inputBytes (caller s) u.mem 0 = inputBytes (caller s) s.mem 0 at ns
        change inputBytes (caller t) v.mem 0 = inputBytes (caller t) t.mem 0 at nt
        have align : inputBytes (caller s) v.mem 0 = inputBytes (caller t) v.mem 0 := by
          simp only [inputBytes, caller, CallGeometry.buffer]
          change Spec.Rsa.bytesAt v.mem (byteAddr (arg s 4)) (arg s 5).toNat =
            Spec.Rsa.bytesAt v.mem (byteAddr (arg t 4)) (arg t 5).toNat
          rw [a4, a5]
        exact ns.trans (modulus.trans (align.trans nt).symm)
      have alignCalculated : calculated (caller s) v.mem = calculated (caller t) v.mem := by
        change Spec.Rsa.primesKey
          (Spec.Rsa.bytesAt v.mem (byteAddr (arg s 4)) (arg s 5).toNat)
          (Spec.Rsa.bytesAt v.mem (byteAddr (arg s 6)) (arg s 7).toNat)
          (Spec.Rsa.bytesAt v.mem (byteAddr (arg s 8)) (arg s 9).toNat) =
          Spec.Rsa.primesKey
          (Spec.Rsa.bytesAt v.mem (byteAddr (arg t 4)) (arg t 5).toNat)
          (Spec.Rsa.bytesAt v.mem (byteAddr (arg t 6)) (arg t 7).toNat)
          (Spec.Rsa.bytesAt v.mem (byteAddr (arg t 8)) (arg t 9).toNat)
        rw [args 4 (by decide), args 5 (by decide), args 6 (by decide), args 7 (by decide),
          args 8 (by decide), args 9 (by decide)]
      have sameTries : (calculated (caller s) u.mem).2 = (calculated (caller s) v.mem).2 :=
        (congrArg Prod.snd (calculated_entry a os)).trans
          (attempts.trans (congrArg Prod.snd (alignCalculated.trans (calculated_entry b ot))).symm)
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have apart : ∀ r ∈ narrowW (caller s),
              Region.Disjoint ⟨(caller s).sp.setWidth 64, 52⟩ r := fun r hr =>
            VG.X86.Taint.frame_disjoint (n := 48)
              (by change (s.gpr .esp).toNat + 4 + 48 ≤ _; have := a.stackBound; omega) (a.retApart r hr)
              (a.argsApart r hr)
          have eq2 := (body_relCT (caller s) a.lengths_ok _ _ _ _ _ _ ⟨pair, apart, same, sameTries⟩ e2 f2).1
          obtain ⟨hx, _, _, kx⟩ := wp_result (body_ok hs a.lengths_ok) e2
          obtain ⟨hy, _, _, ky⟩ := wp_result (body_ok hv a.lengths_ok) f2
          have next := pair.after hx hy kx ky (by decide)
          have eq3 := (publicRestore_relCT _ _ _ _ _ _ next.workspace e3 f3).1
          rw [eq1, eq2, eq3]

theorem constantTime : ConstantTime isa (Spec.Rsa.recoverPrimesContract abi 96).pre
    (Spec.Rsa.recoverPrimesContract abi 96).pub VG.Impl.Rsa.X86.RecoverRt.code := by
  intro s t tr ur sf tf hs ht h es et
  have args := arguments_eq h
  obtain ⟨modulus, attempts⟩ := observations_eq h
  exact operation_trace (abi_of hs) (abi_of ht) args.2 args.1 modulus attempts es et

end VG.Proof.Rsa.X86.Recover
