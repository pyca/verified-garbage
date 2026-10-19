module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCoreTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtCoefficientTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtCoefficientStage

/-! # The coefficient stage's trace is independent of private components

From what both runs are given (`StageReady`), correctness of the loads and of
the factor's context gives what the coefficient's calls need (`CoefReady`). -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Bignum.X86

/-- What `coefficient_ok` needs, at the stack pointer `sp`. -/
def StageReady (n : Nat) (sp : BitVec 32) (base : Addr) (s : State) : Prop :=
  s.gpr .esp = sp ∧ ∃ bytes, Scr s base bytes ∧ size n ≤ bytes ∧ CallRoom sp base bytes ∧
    wordsVal s.mem base (slot n mpSlot) n < safePrime (wordsVal s.mem base (slot n pSlot) n)

/-- After the residues and the inverse are loaded. -/
def StageLoaded (n : Nat) (sp : BitVec 32) (base : Addr) (s : State) : Prop :=
  s.gpr .esp = sp ∧ ∃ bytes, Scr s base bytes ∧ size n ≤ bytes ∧ CallRoom sp base bytes ∧
    wordsVal s.mem base (slot n 6) n < safePrime (wordsVal s.mem base (slot n 0) n)

theorem stageLoaded_of {n : Nat} (hn : 2 ≤ n) {sp : BitVec 32} {base : Addr} {s : State}
    (h : StageReady n sp base s) : WP isa (loadCoefficient n) s (StageLoaded n sp base) := by
  obtain ⟨hsp, bytes, hs, hz, R, mp⟩ := h
  refine WP.mono (loadCoefficient_ok hs (by omega) hz) fun u ⟨P, _, Mp, _, _, K⟩ => ?_
  exact ⟨(K.1 _ (by decide)).trans hsp, bytes, hs.of_keeps K (by decide), hz, R,
    by rw [Mp, P]; exact mp⟩

theorem coefReady_of {n : Nat} (hn : 2 ≤ n) (hn32 : 128 * n < 2 ^ 32) {sp : BitVec 32} {base : Addr}
    {s : State} (h : StageLoaded n sp base s) :
    WP isa (checkedPreparePrime n) s (CoefReady n sp base) := by
  obtain ⟨hsp, bytes, hs, hz, R, mp⟩ := h
  have fit : contextBytes n ≤ 2 ^ 64 := by have := hs.nowrap; have := context_fits n; omega
  refine WP.mono (checkedPreparePrime_ok hs (by omega) hn32 (Nat.le_trans (context_fits n) hz))
    fun v ⟨C, One, R₂, Ov, Kv⟩ => ?_
  have preserve : wordsVal v.mem base (slot n 6) n = wordsVal s.mem base (slot n 6) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact primeSetup_value Ov (.inr (.inl rfl)) (by omega) fit
  exact ⟨(Kv.1 _ (by decide)).trans hsp, _, bytes, C, R, by rw [preserve]; exact mp, One, R₂⟩

theorem coefficient_relCT {n : Nat} (hn : 2 ≤ n) (hn32 : 128 * n < 2 ^ 32) (sp : BitVec 32) (base : Addr) :
    RelCT isa (fun s t => VG.X86.Taint.Agree (workspaceTaint false) s t ∧ StageReady n sp base s ∧
        StageReady n sp base t) (coefficient n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold coefficient
  refine VG.RelCT.seq (((loadCoefficient_relCT n).mono (fun _ _ h => h.1) fun _ _ h => h).wp
    (F₁ := StageLoaded n sp base) (F₂ := StageLoaded n sp base)
    fun _ _ h => ⟨stageLoaded_of hn h.2.1, stageLoaded_of hn h.2.2⟩) ?_
  refine VG.RelCT.seq ?_ (crtCoefficient_relCT hn sp base)
  have prepare : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (checkedPreparePrime n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    unfold checkedPreparePrime
    exact VG.RelCT.seq (primeMask_relCT n) (preparePrime_relCT n)
  exact (prepare.mono (P' := fun s t => VG.X86.Taint.Agree (workspaceTaint false) s t ∧
      StageLoaded n sp base s ∧ StageLoaded n sp base t) (fun _ _ h => h.1)
    fun _ _ h => h).wp (F₁ := CoefReady n sp base) (F₂ := CoefReady n sp base)
    fun _ _ h => ⟨coefReady_of hn hn32 h.2.1, coefReady_of hn hn32 h.2.2⟩

end VG.Proof.Bignum.X86.Crt
