module

public import VerifiedGarbage.Proof.Bignum.X86.CrtNarrowBounds
public import VerifiedGarbage.Proof.Bignum.X86.CrtImport
public import VerifiedGarbage.Proof.Bignum.X86.CrtExport
public import VerifiedGarbage.Proof.Bignum.X86.CrtOutputMath
public import VerifiedGarbage.Proof.Bignum.X86.CrtBodyFrame

/-! # Complete private CRT operation for the selected public modulus width -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Bignum.X86.Crt

theorem sized_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    WP isa (sized (Spec.Rsa.modulusWords len)) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if accepted s.mem args then outputValue s.mem args else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (accepted s.mem args)).toNat ∧
      Frame (bodyRegions base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let n := Spec.Rsa.modulusWords len
  have dims := h.dimensions
  have space : size n ≤ bytes := h.space
  have sz := size_eq n
  have nw := h.scratch.nowrap
  have bound := h.modulus_bound
  have facts := h.factor_bounds valid
  have modWordBound : componentValue s.mem args 2 < 2 ^ (64 * n) :=
    Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by dsimp [n]; omega))
  unfold sized
  refine WP.seq (WP.mono (importComponents_ok h) fun u ⟨N, X, P, Q, DP, DQ, QI, O, hu, K⟩ => ?_)
  have Narrow : wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot n modulusSlot) n = componentValue s.mem args 2 := by
    dsimp only [n, modulusSlot]
    rw [VG.Proof.Bignum.wordsVal_low_half, N, Nat.mod_eq_of_lt modWordBound]
  have hn : 2 ≤ n := by have := h.lower; dsimp only [n]; unfold Spec.Rsa.modulusWords; omega
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine WP.seq (WP.mono (checkedCompute_ok hu.scratch hn dims.2.1 h.space (Narrow.trans N.symm)
    hu.room (import_powerArgs h hu P Q DP DQ))
    fun v ⟨A, V, Ov, Kv⟩ => ?_)
  dsimp only [pSlot, qSlot, dpSlot, dqSlot, inverseSlot, inputSlot, modulusSlot] at V
  dsimp only [n, modulusSlot] at Narrow
  simp only [mask32, pSlot, qSlot, modulusSlot, inputSlot, inverseSlot, P, Q, Narrow, X, QI] at A
  rw [P, Q, DP, DQ, QI, X] at V
  have arithmetic := checked_frame Ov h.space
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  rw [espu] at arithmetic
  have Osv : OutsZ base (s.gpr .esp) [(0, bytes)] s.mem v.mem :=
    (OutsZ.of_outside (O.mono (by omega) (by omega)) (List.mem_singleton_self _)).trans
      (body_scratch arithmetic (by omega))
  have hv := h.keepZ Ksv (by decide) (by decide) Osv
  have result := fun (acc : accepted s.mem args) =>
    narrow_result V facts.1 facts.2.1 facts.2.2 acc.1 bound dims.2.2
  refine WP.mono (exportResult_ok hv.scratch dims.1 h.space (by have := h.lower; omega) dims.2.2 rfl
    (decide (accepted s.mem args)) (by intro H; exact (result (of_decide_eq_true H)).2)
    (by
      change v.mem.readW (off base 8) 32 = (if accepted s.mem args then BitVec.allOnes 32 else 0) at A
      by_cases acc : accepted s.mem args
      · simpa only [acc, decide_true, ite_true] using A
      · simpa only [acc, decide_false, Bool.false_eq_true, ite_false] using A)
    (hv.stack 0 (by decide)) (by rw [← h.outLen]; exact hv.stack 1 (by decide))
    h.outFit hv.outWrite h.outApart) fun t ⟨R, B, F, T⟩ => ?_
  refine ⟨?_, B, ?_, Ksv.trans T⟩
  · rw [R]
    by_cases acc : accepted s.mem args
    · simp only [acc, decide_true, ite_true, (result acc).1, outputValue]
    · simp only [acc, decide_false, Bool.false_eq_true, ite_false]
  · have Import := high_frame (base := base) (bytes := bytes) (out := byteAddr (args 0)) (len := len)
      (sp := s.gpr .esp)
      ((VG.Proof.Bignum.outside_frame O (by omega)).mono (by simp)) (by omega) (by omega)
    exact (Import.trans (body_frame arithmetic (by omega))).trans (high_frame F (by omega) (by omega))

end VG.Proof.Bignum.X86.Crt
