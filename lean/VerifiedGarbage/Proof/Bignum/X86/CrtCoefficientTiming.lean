module

public import VerifiedGarbage.Proof.Bignum.X86.CrtArithmeticTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtCoefficient
public import VerifiedGarbage.Proof.Mont.X86.CallMulTiming

/-! # The CRT coefficient's trace is independent of private components

Its multiplications are calls, whose traces are the same when both runs are
ready for them (`callMul_ws`): each run's state, from what correctness gives
after each step, is ready for the next (`CoefReady`, `CoefReduced`, …). -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

/-- What `crtCoefficient_ok` needs, at the stack pointer `sp`. -/
def CoefReady (n : Nat) (sp : BitVec 32) (base : Addr) (s : State) : Prop :=
  s.gpr .esp = sp ∧ ∃ m bytes, Context n m base bytes s ∧ CallRoom sp base bytes ∧
    wordsVal s.mem base (slot n 6) n < m ∧ wordsVal s.mem base (slot n 3) n = 1 ∧
    wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m

/-- After the reduction of `m_q`. -/
def CoefReduced (n : Nat) (sp : BitVec 32) (base : Addr) (s : State) : Prop :=
  s.gpr .esp = sp ∧ ∃ m bytes, Context n m base bytes s ∧ CallRoom sp base bytes ∧
    wordsVal s.mem base (slot n 6) n < m ∧ wordsVal s.mem base (slot n 5) n < m ∧
    wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m

/-- Ready for a call multiplying slots `a` and `b` into `o`. -/
def CallAt (n : Nat) (sp : BitVec 32) (base : Addr) (o a b : Nat) (s : State) : Prop :=
  s.gpr .esp = sp ∧ ∃ m bytes, MulReady n m base bytes o a b s

/-- After the multiplication of `m_q` by `R²`. -/
def CoefEncoded (n : Nat) (sp : BitVec 32) (base : Addr) (s : State) : Prop :=
  s.gpr .esp = sp ∧ ∃ m bytes, Context n m base bytes s ∧ CallRoom sp base bytes ∧
    wordsVal s.mem base (slot n 6) n < m ∧ wordsVal s.mem base (slot n 3) n = 1 ∧
    wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m

theorem coefReady_mul {n : Nat} {sp : BitVec 32} {base : Addr} {s : State} (h : CoefReady n sp base s) :
    ∃ m size, MulReady n m base size 5 5 4 s := by
  obtain ⟨hsp, m, bytes, H, R, _, _, r2⟩ := h
  exact ⟨m, bytes, H, hsp ▸ R, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by rw [r2]; exact Nat.mod_lt _ (by have := H.gt_one; omega)⟩

theorem coefEncoded_mul {n : Nat} {sp : BitVec 32} {base : Addr} {s : State} (h : CoefEncoded n sp base s) :
    ∃ m size, MulReady n m base size 5 5 3 s := by
  obtain ⟨hsp, m, bytes, H, R, _, one, _⟩ := h
  exact ⟨m, bytes, H, hsp ▸ R, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by rw [one]; exact H.gt_one⟩

theorem coefEncoded_of {n : Nat} (hn : 2 ≤ n) {sp : BitVec 32} {base : Addr} (s : State)
    (_ : s.gpr .esp = sp) (h : CoefReady n sp base s) :
    WP isa (callMul n (slot n 5) (slot n 5) (slot n 4)) s (CoefEncoded n sp base) := by
  obtain ⟨hsp, m, bytes, H, R, A, one, r2⟩ := h
  refine WP.mono (callMul_ok hn H (hsp ▸ R) (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [r2]; exact Nat.mod_lt _ (by have := H.gt_one; omega)))
    fun u ⟨C, K, _⟩ => ?_
  have keep (i : Nat) (hi : i < 9) (h5 : i ≠ 5) (h1 : i ≠ 1) (h2 : i ≠ 2) :=
    K.slot_val H (hsp ▸ R) hi h5 h1 h2
  exact ⟨K.esp.trans hsp, m, bytes, C, R,
    by rw [keep 6 (by decide) (by decide) (by decide) (by decide)]; exact A,
    by rw [keep 3 (by decide) (by decide) (by decide) (by decide)]; exact one,
    by rw [keep 4 (by decide) (by decide) (by decide) (by decide)]; exact r2⟩

theorem coefReduced_of {n : Nat} (hn : 2 ≤ n) {sp : BitVec 32} {base : Addr} (s : State)
    (_ : s.gpr .esp = sp) (h : CoefEncoded n sp base s) :
    WP isa (callMul n (slot n 5) (slot n 5) (slot n 3)) s (CoefReduced n sp base) := by
  obtain ⟨hsp, m, bytes, H, R, A, one, r2⟩ := h
  refine WP.mono (callMul_ok hn H (hsp ▸ R) (o := 5) (a := 5) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [one]; exact H.gt_one))
    fun u ⟨C, K, L, _⟩ => ?_
  have keep (i : Nat) (hi : i < 9) (h5 : i ≠ 5) (h1 : i ≠ 1) (h2 : i ≠ 2) :=
    K.slot_val H (hsp ▸ R) hi h5 h1 h2
  exact ⟨K.esp.trans hsp, m, bytes, C, R,
    by rw [keep 6 (by decide) (by decide) (by decide) (by decide)]; exact A, L,
    by rw [keep 4 (by decide) (by decide) (by decide) (by decide)]; exact r2⟩

theorem coefSub_of {n : Nat} {sp : BitVec 32} {base : Addr} {s : State} (h : CoefReduced n sp base s) :
    WP isa (subW (contextMod n) (slot n 2) (slot n 7) (slot n 6) (slot n 5)) s (CallAt n sp base 8 8 4) := by
  obtain ⟨hsp, m, bytes, C, R, A, B, R4⟩ := h
  have positive : 0 < m := by have := C.gt_one; omega
  refine WP.mono (contextSub_ok C (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) A B) fun v ⟨Cv, Kv, _⟩ => ?_
  have espv : v.gpr .esp = sp := (Kv.gpr _ (by decide)).trans hsp
  have Rv : wordsVal v.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [context_slot_val C (by decide) (by decide) (by decide) (by decide) Kv, R4]
  exact ⟨espv, m, bytes, ⟨Cv, espv ▸ R, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by rw [Rv]; exact Nat.mod_lt _ positive⟩⟩

theorem coefCall_of {n : Nat} (hn : 2 ≤ n) {sp : BitVec 32} {base : Addr} (σ : State) (m size : Nat)
    (hsp : σ.gpr .esp = sp) (M : MulReady n m base size 8 8 4 σ) :
    WP isa (callMul n (slot n 8) (slot n 8) (slot n 4)) σ (CallAt n sp base 7 7 8) := by
  refine WP.mono (callMul_ok hn M.ctx M.room (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) M.bLt) fun w ⟨Cw, Kw, Lw, _⟩ => ?_
  have espw : w.gpr .esp = σ.gpr .esp := Kw.esp
  exact ⟨espw.trans hsp, m, size, ⟨Cw, espw ▸ M.room, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, Lw⟩⟩

theorem coefCall₂_of {n : Nat} (hn : 2 ≤ n) {base : Addr} (σ : State) (m size : Nat)
    (M : MulReady n m base size 7 7 8 σ) :
    WP isa (callMul n (slot n 7) (slot n 7) (slot n 8)) σ fun t => ∃ m size, Context n m base size t :=
  WP.mono (callMul_ok hn M.ctx M.room (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) M.bLt) fun _ ⟨Ct, _⟩ => ⟨m, size, Ct⟩

theorem crtCoefficient_relCT {n : Nat} (hn : 2 ≤ n) (sp : BitVec 32) (base : Addr) :
    RelCT isa (fun s t => VG.X86.Taint.Agree (workspaceTaint false) s t ∧ CoefReady n sp base s ∧
        CoefReady n sp base t) (crtCoefficient n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold crtCoefficient
  refine VG.RelCT.seq ((callMul_ready hn sp base (Rdy := CoefReady n sp base) (G := CoefEncoded n sp base)
    (fun _ h => coefReady_mul h) (coefEncoded_of hn) fun _ ⟨_, m, size, C, _⟩ => ⟨m, size, C⟩).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁.1, h₂.1, h₁, h₂⟩) fun _ _ h => h) ?_
  refine VG.RelCT.seq ((callMul_ready hn sp base (Rdy := CoefEncoded n sp base) (G := CoefReduced n sp base)
    (fun _ h => coefEncoded_mul h) (coefReduced_of hn) fun _ ⟨_, m, size, C, _⟩ => ⟨m, size, C⟩).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁.1, h₂.1, h₁, h₂⟩) fun _ _ h => h) ?_
  refine VG.RelCT.seq (((subW_relCT _ _ _ _ _).mono (fun _ _ h => h.1) fun _ _ h => h).wp
    (F₁ := CallAt n sp base 8 8 4) (F₂ := CallAt n sp base 8 8 4)
    fun _ _ h => ⟨coefSub_of h.2.1, coefSub_of h.2.2⟩) ?_
  refine VG.RelCT.seq ((callMul_ws hn sp base (G := CallAt n sp base 7 7 8) (coefCall_of hn)
    fun _ ⟨_, m, size, M⟩ => ⟨m, size, M.ctx⟩).mono
    (fun _ _ ⟨_, ⟨h₁, M₁⟩, ⟨h₂, M₂⟩⟩ => ⟨h₁, h₂, M₁, M₂⟩) fun _ _ h => h) ?_
  exact (callMul_ws hn sp base (fun σ m size _ M => coefCall₂_of hn σ m size M) fun _ h => h).mono
    (fun _ _ ⟨_, ⟨h₁, M₁⟩, ⟨h₂, M₂⟩⟩ => ⟨h₁, h₂, M₁, M₂⟩) fun _ _ h => h.1

end VG.Proof.Bignum.X86
