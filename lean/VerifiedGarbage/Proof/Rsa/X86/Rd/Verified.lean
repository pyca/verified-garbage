module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Sized
public import VerifiedGarbage.Proof.Rsa.X86.RvABI
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rsa.X86.RvFailure
import VerifiedGarbage.Proof.Rsa.X86.RvReturn
import VerifiedGarbage.Proof.Rsa.X86.RvBuffers
import VerifiedGarbage.Proof.Rsa.X86.RvInstalled
import VerifiedGarbage.Proof.Rsa.X86.RvResources
import VerifiedGarbage.Proof.Rsa.X86.RvSatisfiable
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Prime recovery by Appendix C.2 on i686: correctness against `recoverPrimesDetContract`

The contract's precondition gives `RvABI`'s `ABI` (its public exponent of
at most 8 bytes is below the modulus's length), so the call's entry and
return are prime recovery's (`installed_ok`, `entryRestore_ok`); between
them, the modulus check and `sizedD_ok` write `primesKeyDet`'s result.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem abiD_of {s : State} (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pre s) :
    ABI s ∧ (arg s 7).toNat ≤ 8 := by
  sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  have rd : s.rd = [(caller s).buffer 4, (caller s).buffer 6, (caller s).buffer 8] := by
    dsimp only [caller, CallGeometry.buffer, byteAddr]
    with_reducible assumption
  have lengths : Spec.Rsa.lenValid (arg s 5).toNat := by with_reducible assumption
  have lo := lengths.1
  have hi := lengths.2
  refine ⟨?_, by omega⟩
  constructor
  all_goals try simp only [rd, bodyRegions, lowR, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)

theorem calculatedD_entry {s t : State} (a : ABI s)
    (o : Outside (caller s).B 0 (caller s).Z s.mem t.mem) :
    calculatedD (caller s) t.mem = calculatedD (caller s) s.mem := by
  have same (i : Fin 3) : inputBytes (caller s) t.mem i = inputBytes (caller s) s.mem i := by
    exact scratch_bytes o (by have := (a.inputLength i).2; have := a.width.2.1; omega)
      (a.inApart _ (a.inputMember i) _ (by simp))
  unfold calculatedD
  rw [same 0, same 1, same 2]

theorem satisfiableD : ∃ s, (Spec.Rsa.recoverPrimesDetContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 16384 := by decide
  have a5 : arg satState 5 = 64 := by decide
  have a6 : arg satState 6 = 20480 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 24576 := by decide
  have a9 : arg satState 9 = 1 := by decide
  have a10 : arg satState 10 = 65536 := by decide
  have a11 : arg satState 11 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes,
    stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, e, esp, satState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using satState

end VG.Proof.Rsa.X86.Recover

section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem bodyD_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (eSmall : (g.buffer 6).len ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.body s fun t => Inputs g t ∧ WrittenD g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.RecoverDetRt.body VG.Impl.Rsa.X86.CrtValues.inputArgs
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 4 (by decide)).readSrc (h.arguments 5 (by decide)).readSrc)
    fun u ⟨p, c, m, k⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u len.lower len.upper
    (by rw [p]; exact h.inputFit 0)
    (by rw [p, k.2.1, k.2.2]; exact h.inputRead 0)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun v ⟨z, mv, kv⟩ => ?_)
  rw [p, m] at z
  have mem : v.mem = s.mem := mv.trans m
  have keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (k.mono (by decide)).trans (kv.mono (by decide))
  have hv := h.after keeps (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (g.args 5).toNat) z ?_ ?_
  · intro accepted
    have modulus : Spec.Rsa.modulusValid (inputValue g v.mem 0)
        (inputBytes g v.mem 0).length = true := by
      rw [mem]
      simp only [inputValue, inputBytes, bytesAt_length, CallGeometry.buffer]
      exact accepted
    have pLen : (g.buffer 0).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.pLen
    have qLen : (g.buffer 2).len = (inputBytes g v.mem 0).length := by
      simp only [inputBytes, bytesAt_length, CallGeometry.buffer]
      exact congrArg BitVec.toNat len.qLen
    refine WP.mono (sizedD_ok hv len modulus pLen qLen eSmall)
      fun t ⟨ht, result, frame, rest⟩ => ?_
    exact ⟨ht, mem ▸ result, mem ▸ frame, keeps.trans rest⟩
  · intro rejected
    have failed : calculatedD g s.mem = none := by
      unfold calculatedD Spec.Rsa.primesKeyDet
      dsimp only
      have ln : (inputBytes g s.mem 0).length = (g.args 5).toNat := bytesAt_length _ _ _
      rw [ln, rejected]
      rfl
    refine WP.mono (failure_ok hv) fun t ⟨ht, p, q, status, frame, rest⟩ => ?_
    exact ⟨ht, writtenD_failure failed p q status, mem ▸ frame, keeps.trans (rest.mono (by decide))⟩

theorem operationD_ok {s : State} (a : ABI s) (eSmall : (arg s 7).toNat ≤ 8) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.code s fun t => WrittenD (caller s) s.mem t ∧ abiPreserved s t := by
  have low : 16 ≤ (caller s).Z := by have := a.used; omega
  have high : (caller s).Z ≤ 2 ^ 64 := by have := a.scratchBound; omega
  unfold VG.Impl.Rsa.X86.RecoverDetRt.code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, k, o⟩ => ?_)
  refine WP.seq (WP.mono (bodyD_ok inputs a.lengths_ok eSmall) fun v ⟨iv, written, frame, kv⟩ => ?_)
  have saveV := bodyFrame_saved inputs frame saved
  have whole : Frame (caller s).writes s.mem v.mem := by
    have start := outside_frame o (by omega)
    simp only [off, BitVec.add_zero] at start
    exact (start.mono (by simp [CallGeometry.writes])).trans (bodyFrame_full low frame)
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    whole.readW (Region.contains_self _ 4) a.retApartW (by decide)
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (k.1 _ (by decide))) ret⟩
  unfold WrittenD at written ⊢
  rw [calculatedD_entry a o] at written
  rw [restored.mem, restored.other .eax (by decide)]
  exact written

theorem correctD (s : State) (h : (Spec.Rsa.recoverPrimesDetContract abi 96).pre s) :
    ∃ trace t, Exec isa VG.Impl.Rsa.X86.RecoverDetRt.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.recoverPrimesDetContract abi 96).post s t := by
  obtain ⟨a, eSmall⟩ := abiD_of h
  obtain ⟨trace, t, run, written, preserved⟩ := operationD_ok a eSmall
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold WrittenD outputBuffersD calculatedD inputBytes CallGeometry.buffer caller at written
  change Spec.Rsa.writtenAll t.mem
    [(VG.Proof.Dsa.X86.argumentPointer s 0, (arg s 1).toNat),
      (VG.Proof.Dsa.X86.argumentPointer s 2, (arg s 3).toNat)] (t.gpr .eax) _ at written
  rw [a.pLen, a.qLen] at written
  exact written

end VG.Proof.Rsa.X86.Recover
end
