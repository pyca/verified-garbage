module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedApplyInput

/-! # Workspace resources and acceptance mask ready for packed-key output -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

/-- The input's import keeps the key, the exponent and the call. -/
theorem precomputedImportInput_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) :
    WP isa (VG.Impl.Bignum.X86.PrecomputedFn.importInput (Spec.Rsa.modulusWords len)) s fun u =>
      PrecomputedInputs base bytes len args u ∧
      wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 6) (Spec.Rsa.modulusWords len) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) ∧
      wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) = wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) ∧
      wordsVal u.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) = wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) ∧
      val32 u.mem base 128 2 = val32 s.mem base 128 2 ∧
      Outside base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 6) (8 * (Spec.Rsa.modulusWords len)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have dims := h.dimensions
  have space := h.space
  have nw := h.scratch.nowrap
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have b6 := slot_bound (n := (Spec.Rsa.modulusWords len)) (i := 6) (by decide)
  have d6 := slot_header (Spec.Rsa.modulusWords len) 6
  have s06 := slot_le (n := (Spec.Rsa.modulusWords len)) (i := 0) (j := 6) (by decide)
  have s56 := slot_le (n := (Spec.Rsa.modulusWords len)) (i := 5) (j := 6) (by decide)
  simp only [stride] at b6 s06 s56
  refine WP.mono (precomputedInput_ok h.scratch dims.1 h.space (by have := h.lower; omega)
    dims.2.2 (h.stack 6 (by decide)) (by rw [← h.inLen]; exact h.stack 7 (by decide))
    h.inFit h.inRead h.inApart) fun u ⟨X, O, K⟩ => ⟨h.keep K (by decide) (by decide)
      (O.mono (by omega) (by omega)), X, ?_, ?_, ?_, O, K⟩
  · rw [wordsVal_eq_val32, O.val32 (.inl (by omega)) (by omega), ← wordsVal_eq_val32]
  · rw [wordsVal_eq_val32, O.val32 (.inl (by omega)) (by omega), ← wordsVal_eq_val32]
  · rw [O.val32 (.inl (by omega)) (by decide)]

theorem precomputedPrepared_ok {s : State} {base : Addr} {bytes len m r e : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s)
    (N : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) = m)
    (R : wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) = r)
    (E : val32 s.mem base 128 2 = e) (gt : 1 < m) (odd : m % 2 = 1) (rb : r < m) :
    WP isa (.seq (VG.Impl.Bignum.X86.PrecomputedFn.importInput (Spec.Rsa.modulusWords len))
      (VG.Impl.Bignum.X86.PrecomputedFn.acceptAndPower (Spec.Rsa.modulusWords len))) s fun t =>
      PrecomputedInputs base bytes len args t ∧ t.gpr .esp = s.gpr .esp ∧
      ∃ accept : Bool, t.mem.readW (off base 144) 32 = if accept then BitVec.allOnes 32 else 0 := by
  have dims := h.dimensions
  have space := h.space
  have nw := h.scratch.nowrap
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have b6 := slot_bound (n := (Spec.Rsa.modulusWords len)) (i := 6) (by decide)
  have d6 := slot_header (Spec.Rsa.modulusWords len) 6
  simp only [stride] at b6
  refine WP.seq (WP.mono (precomputedImportInput_ok h) fun u ⟨hu, X, Nu, Ru, Eu, O, K⟩ => ?_)
  refine WP.mono (precomputedAcceptAndPower_ok hu.scratch dims.1 h.space (Nu.trans N) X (Eu.trans E)
    gt odd (Ru.trans R) rb) fun v ⟨_, _, _, Mask, Ov, Kv⟩ => ?_
  have Os : Outside base 16 (bytes - 16) s.mem v.mem :=
    (O.mono (by omega) (by omega)).trans Ov
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have hv := h.keep Ks (by decide) (by decide) (Os.mono (by omega) (by omega))
  let accept := decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) < m)
  have AM : v.mem.readW (off base 144) 32 = if accept then BitVec.allOnes 32 else 0 := by
    simpa only [accept, decide_eq_true_eq] using Mask
  exact ⟨hv, Ks.1 _ (by decide), accept, AM⟩

end VG.Proof.Bignum.X86.PublicContext
