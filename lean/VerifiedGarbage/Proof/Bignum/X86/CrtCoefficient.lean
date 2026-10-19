module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCoefficient
public import VerifiedGarbage.Proof.Bignum.X86.ReduceOperand
public import VerifiedGarbage.Proof.Bignum.X86.ContextSub
public import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Mont.X86.CallMul

/-! # Correct reduced CRT coefficient after full-width residue reduction -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

def coefficientRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 5, 8 * n), (slot n 7, 8 * n), (slot n 8, 8 * n), (slot n 1, 2 * stride n)]

theorem coefficient_op {n o : Nat} {base : Addr} {s t : State} (sp : BitVec 32)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) (ho : o = 5 ∨ o = 7 ∨ o = 8) :
    OutsZ base sp (coefficientRanges n) s.mem t.mem := by
  refine OutsZ.of_outs (Outs.widen K.mem fun y hy r hr => ?_)
  have s12 : slot n 2 = slot n 1 + stride n := by unfold slot stride; omega
  have eS : stride n = 16 * n + 8 := rfl
  have hA := context_accLen n
  simp only [coefficientRanges, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have eT : (contextMod n).tmp = slot n 1 := rfl
  have eN : (contextMod n).n = n := rfl
  rcases hr with rfl | rfl | rfl <;> dsimp only <;> rcases ho with rfl | rfl | rfl <;> omega

theorem coefficient_call {n o : Nat} {base : Addr} {s t : State}
    (K : CallKeep n base (slot n o) s t) (ho : o = 5 ∨ o = 7 ∨ o = 8) :
    OutsZ base (s.gpr .esp) (coefficientRanges n) s.mem t.mem := by
  refine K.mem.mono fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases ho with rfl | rfl | rfl <;> simp [coefficientRanges]
  · simp [coefficientRanges]

theorem crtCoefficient_ok {s : State} {base : Addr} {bytes n m : Nat} (hn : 2 ≤ n)
    (H : Context n m base bytes s) (R : CallRoom (s.gpr .esp) base bytes)
    (A : wordsVal s.mem base (slot n 6) n < m)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (crtCoefficient n) s fun t =>
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n 7) n =
        ((wordsVal s.mem base (slot n 6) n + m - wordsVal s.mem base (slot n 5) n % m) % m *
          wordsVal s.mem base (slot n 8) n) % m ∧
      OutsZ base (s.gpr .esp) (coefficientRanges n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have positive : 0 < m := by have := H.gt_one; omega
  unfold crtCoefficient
  refine WP.seq (WP.mono (callMul_ok hn H R (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [r2]; exact Nat.mod_lt _ positive))
    fun u₁ ⟨C₁, K₁, L₁, V₁⟩ => ?_)
  have esp₁ : u₁.gpr .esp = s.gpr .esp := K₁.esp
  have Encoded₅ : wordsVal u₁.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n * 2 ^ (64 * n) % m :=
    mont_encode H.coprime L₁ (by rw [V₁, r2])
  have One : wordsVal u₁.mem base (slot n 3) n = 1 := by
    rw [K₁.slot_val H R (i := 3) (by decide) (by decide) (by decide) (by decide), one]
  refine WP.seq (WP.mono (callMul_ok hn C₁ (esp₁ ▸ R) (o := 5) (a := 5) (b := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [One]; exact H.gt_one))
    fun u ⟨C, K₂, L₂, V₂⟩ => ?_)
  have B := VG.Proof.Dsa.mont_decode (A := wordsVal u₁.mem base (slot n 5) n)
    (out := wordsVal u.mem base (slot n 5) n) H.coprime
    (by rw [Encoded₅, Nat.mod_mod]) (by rw [V₂, One])
  rw [Nat.mod_eq_of_lt L₂] at B
  have keep (i : Nat) (hi : i < 9) (h5 : i ≠ 5) (h1 : i ≠ 1) (h2 : i ≠ 2) :
      wordsVal u.mem base (slot n i) n = wordsVal s.mem base (slot n i) n :=
    (K₂.slot_val C₁ (esp₁ ▸ R) hi h5 h1 h2).trans (K₁.slot_val H R hi h5 h1 h2)
  have Au := keep 6 (by decide) (by decide) (by decide) (by decide)
  have Ru := keep 4 (by decide) (by decide) (by decide) (by decide)
  have Iu := keep 8 (by decide) (by decide) (by decide) (by decide)
  have espu : u.gpr .esp = s.gpr .esp := K₂.esp.trans esp₁
  have Z₀ := coefficient_call K₁ (.inl rfl)
  have Z₀' := coefficient_call K₂ (.inl rfl)
  rw [esp₁] at Z₀'
  refine WP.seq (WP.mono (contextSub_ok C (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Au]; exact A) (by rw [B]; exact Nat.mod_lt _ positive)) fun v ⟨Cv, Kv, D⟩ => ?_)
  have espv : v.gpr .esp = s.gpr .esp := (Kv.gpr _ (by decide)).trans espu
  have Rv : wordsVal v.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [context_slot_val C (by decide) (by decide) (by decide) (by decide) Kv, Ru, r2]
  have Iv := context_slot_val C (i := 8) (by decide) (by decide) (by decide) (by decide) Kv
  refine WP.seq (WP.mono (callMul_ok hn Cv (espv ▸ R) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [Rv]; exact Nat.mod_lt _ positive))
    fun w ⟨Cw, Kw, Lw, Vw⟩ => ?_)
  have espw : w.gpr .esp = s.gpr .esp := Kw.esp.trans espv
  have Encoded : wordsVal w.mem base (slot n 8) n =
      wordsVal s.mem base (slot n 8) n * 2 ^ (64 * n) % m :=
    mont_encode H.coprime Lw (by rw [Vw, Rv, Iv, Iu])
  have Dw := Kw.slot_val Cv (espv ▸ R) (i := 7) (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (callMul_ok hn Cw (espw ▸ R) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Lw) fun t ⟨Ct, Kt, Lt, Vt⟩ => ?_
  have Z₁ := coefficient_call Kw (.inr (.inr rfl))
  have Z₂ := coefficient_call Kt (.inr (.inl rfl))
  rw [espv] at Z₁
  rw [espw] at Z₂
  refine ⟨Ct, ?_, (((Z₀.trans Z₀').trans (coefficient_op _ Kv (.inr (.inl rfl)))).trans Z₁).trans Z₂,
    ((((K₁.keeps.mono (by decide)).trans (K₂.keeps.mono (by decide))).trans (OpKeep.keeps Kv)).trans
      (Kw.keeps.mono (by decide))).trans (Kt.keeps.mono (by decide))⟩
  have Eq : wordsVal t.mem base (slot n 7) n * 2 ^ (64 * n) % m =
        (wordsVal v.mem base (slot n 7) n * wordsVal s.mem base (slot n 8) n) * 2 ^ (64 * n) % m := by
    rw [Vt, Encoded, Dw, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have Cancel := VG.Proof.Bignum.mont_cancel H.coprime Eq
  rw [Nat.mod_eq_of_lt Lt, D, Au, B] at Cancel
  exact Cancel

end VG.Proof.Bignum.X86
