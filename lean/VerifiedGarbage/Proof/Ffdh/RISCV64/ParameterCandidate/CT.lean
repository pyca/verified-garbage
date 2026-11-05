module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.CTTests
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Correct
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Trial
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Trial
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.CTTests
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Correct
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

-- separate module: the taint checks of `main` and the entry, which the round's binding in `Verified` need not re-check

/-!
# An FFDH parameter candidate on RISC-V: constant time

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{CTMain,CT}.lean`):
`main_ct`, p's congruence branches on the generator, pinned once loaded, the
shape checks on `hBad`, which the candidate decides (`MB`); trial division
(`trialSieve_ct`) loops while the entry tested, a function of the candidate
and of how many are left, does not divide it, from the table's address,
which the contract makes public (`taintSym`); the tests are `tests_ct`; `code_ct`, two runs with the same public arguments and tape
(`qOf`) leak the same, whatever the registers they save. The entry loads
`scratch_len` from the stack, pinned once loaded; `zeroOut` and the length
check load `out`, `out_len` and the tape's length from the header, pinned
once loaded; the exit loads `scratch_len` from the header to find the save
area.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.Taint VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_zero_ofNat)
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-! ## `main` -/

/-- The candidate from the tape. -/
def candOf (q : PP) : Nat := Spec.Ffdh.candidateOf q.bits (Spec.Rsa.os2ip (q.r.take q.L))

/-- Code the taint analysis with the table's address public proves constant
time, from states a predicate relates. -/
theorem two_taint_sym {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ →
      s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s₂.syms VG.Impl.RsaKeyGen.TrialTable32.symbol)
    {hc : VG.Taint.Hint T}
    (h : (VG.Taint.check (taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) (fun _ _ ⟨a, h₁, h₂, hsp⟩ =>
    ⟨⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (mem_ofRegs.mp hr)⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂⟩) h

/-- Before `main`: the arguments and tape, and the table's address. -/
def MnI (a : PP × Addr) (s : State) : Prop :=
  ∃ sv, St (a.1.with sv) s ∧ TabIn a.1.B a.1.Z a.2 s ∧ word s.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    a.1.L ≤ a.1.r.length

/-- With p in array 0. -/
def MnA (a : PP × Addr) (t : State) : Prop :=
  (∃ sv, St (a.1.with sv) t ∧ TabIn a.1.B a.1.Z a.2 t ∧ Ph (a.1.with sv) a.1.bits
    (Spec.Ffdh.primeChecks a.1.bits) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    wv t.mem a.1.B (slot (wOf a.1.bits) 0) (wOf a.1.bits) = candOf a.1) ∧ a.1.L ≤ a.1.r.length

/-- In p's working space, `hBad` zero iff `B q`. -/
def MnB (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (t : State) : Prop :=
  (∃ sv, MB (a.1.with sv) a.2 (x a.1) (B a.1) t) ∧ a.1.L ≤ a.1.r.length

theorem pins_MnB {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : Pins Φ [.a7, .s5, .t0, .s6] :=
  pins_ph Prod.fst (fun a => a.1.bits) fun a s hs => let ⟨⟨sv, M⟩, _⟩ := h a s hs; ⟨sv, _, M.st, M.ph⟩

theorem mainA_ct : RelCT isa (Two MnI) (.seq (phase false) shapeP) (Two MnA) :=
  two_post (two_map Prod.fst (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct))
    fun _ _ ⟨sv, h, ht, hU, hL⟩ => WP.mono_syms (mainA_ok h hU hL) fun _ ⟨a, b, c, d, hr, f, rd⟩ sy =>
      ⟨⟨sv, a, ht.step sy f hr rd, b, c, d⟩, hL⟩

/-- After the congruence's first block. -/
def RH (a : PP × Addr) (t : State) : Prop :=
  (t.gpr .t3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2 ∧ (a.1.g = 2 ∨ a.1.g = 5)) ∧
    t.gpr .a7 = off a.1.B (slot (wOf a.1.bits) 0) ∧ t.gpr .t0 = BitVec.ofNat 64 (wOf a.1.bits) ∧ t.gpr .s6 = a.1.B

theorem pins_RH {Φ : PP × Addr → State → Prop} (h : ∀ a s, Φ a s → RH a s) : Pins Φ [.a7, .t0, .s6] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, a7, a0, a6⟩ := h a s₁ h₁
  obtain ⟨_, b7, b0, b6⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a7, b7]
  · rw [a0, b0]
  · rw [a6, b6]

theorem pins_MnA : Pins MnA [.s6] := pins_s6 (fun a : PP × Addr => a.1.B) fun _ _ ⟨⟨_, h, _⟩, _⟩ => h.s6

theorem residue_ct : RelCT isa (Two MnA) residue (Two (MnB candOf fun q => goodRes q.g (candOf q))) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, h, ht, hp, hU, hn⟩, hL⟩ =>
    WP.mono (residue_mb h hp ht hU hn) fun _ M => ⟨⟨sv, M⟩, hL⟩
  unfold residue
  refine RelCT.seq (two_post (two_taint _ pins_MnA (by taint_decide)) (Ψ := RH)
    fun a s ⟨⟨sv, h, _, hp, _⟩, _⟩ => ?_) (two_ite' (fun a => decide (a.1.g = 2)) (fun a s h => ?_)
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide))
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide)))
  · refine WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2) ?_
      (by rfl) (by rfl)) fun t ⟨t3, k⟩ => ⟨⟨t3, h.dims.g⟩, (k.gpr (by decide)).trans hp.a7,
        (k.gpr (by decide)).trans hp.t0, (k.gpr (by decide)).trans h.s6⟩
    simp only [ldh, hGen]
    brun [h.s6, h.ld (d := 128) (by decide), h.al (d := 128) (by decide) (by decide), h.args.gen']
    rfl
  · obtain ⟨⟨h3, hg⟩, _⟩ := h
    rw [eval_zero, h3]
    rcases hg with hg | hg <;> rw [hg] <;> decide

theorem badLoad_ct {x : PP → Nat} {B : PP → Prop} [∀ q, Decidable (B q)] :
    RelCT isa (Two (MnB x B)) (.block [ldh .t3 hBad])
      (Two fun a t => MnB x B a t ∧ isa.eval (.zero .t3) t = some (decide (B a.1))) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, M⟩, hL⟩ =>
    WP.mono M.badLoad fun _ ⟨M', t5⟩ => ⟨⟨⟨sv, M'⟩, hL⟩,
      (by rw [eval_zero, t5]; exact congrArg some (beq_zero_of_iff M.bad))⟩

theorem finMnB_ct {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : RelCT isa (Two Φ) (.block (finish 2)) fun _ _ => True :=
  two_map Prod.fst (fun a s hs => let ⟨⟨_, M⟩, _⟩ := h a s hs; M.st.fs) (finish_ct (.inr (.inr rfl)))

theorem sieve_ct {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) :
    RelCT isa (Two Φ) VG.Impl.Ffdh.RISCV64.ParameterCandidate.sieve
      (Two (MnB x fun q => B q ∧ ∀ d ∈ oddPrimes256, x q % d ≠ 0)) :=
  two_post (two_taint _ (pins_MnB h) (by taint_decide)) fun a s hs =>
    let ⟨⟨sv, M⟩, hL⟩ := h a s hs; WP.mono M.sieve fun _ M' => ⟨⟨sv, M'⟩, hL⟩

theorem halve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) halveQ (Two (MnB (fun q => x q / 2) fun q => B q ∧ x q / 2 % 2 = 1)) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, M⟩, hL⟩ =>
    WP.mono M.halve fun _ M' => ⟨⟨sv, M'⟩, hL⟩

/-! ## Trial division -/

/-- With the count of entries in `hTrialN`. -/
def MnC (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (u : State) : Prop :=
  MnB x B a u ∧ u.mem.readW (a.1.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (trialN a.1.bits)

/-- With the table's address and the count in `s9` and `s10`. -/
def MnT (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (v : State) : Prop :=
  ∃ u, MnC x B a u ∧ ((v.gpr .s9 = a.2 ∧ v.gpr .s10 = BitVec.ofNat 64 (trialN a.1.bits) ∧ v.mem = u.mem) ∧
    Keep [.s9, .s10] u v) ∧ v.sp = u.sp

/-- In the loop, `d.2` entries left. -/
def MnL (x : PP → Nat) (B : PP → Prop) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnT x B d.1 v ∧ VG.Proof.RsaKeyGen.RISCV64.Trial.TInv v d.1.2 (x d.1.1) (trialN d.1.1.bits) d.2 w

/-- After the loop. -/
def MnE (x : PP → Nat) (B : PP → Prop) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnT x B d.1 v ∧ Keep VG.Proof.RsaKeyGen.RISCV64.Trial.entryRegs v w

theorem MnT.base {x : PP → Nat} {B : PP → Prop} {a : PP × Addr} {v : State} (h : MnT x B a v) :
    v.gpr .a7 = off a.1.B (slot (wOf a.1.bits) 0) ∧ v.gpr .t0 = BitVec.ofNat 64 (wOf a.1.bits) ∧
      v.gpr .s6 = a.1.B := by
  obtain ⟨u, ⟨⟨⟨_, M⟩, _⟩, _⟩, ⟨-, kv⟩, -⟩ := h
  exact ⟨(kv.gpr (by decide)).trans M.ph.a7, (kv.gpr (by decide)).trans M.ph.t0,
    (kv.gpr (by decide)).trans M.st.s6⟩

theorem pins_MnL {x : PP → Nat} {B : PP → Prop} : Pins (MnL x B) [.a7, .t0, .s9] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, k₁, hm₁, hk₁, ⟨a9, -⟩, kv₁⟩ ⟨v₂, hv₂, k₂, hm₂, hk₂, ⟨b9, -⟩, kv₂⟩ r hr
  obtain ⟨a7, a0, -⟩ := hv₁.base
  obtain ⟨b7, b0, -⟩ := hv₂.base
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [kv₁.gpr (by decide), kv₂.gpr (by decide), a7, b7]
  · rw [kv₁.gpr (by decide), kv₂.gpr (by decide), a0, b0]
  · rw [a9, b9, show k₁ = k₂ by omega]

theorem pins_MnE {x : PP → Nat} {B : PP → Prop} : Pins (MnE x B) [.s6] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, kv₁⟩ ⟨v₂, hv₂, kv₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [kv₁.gpr (by decide), kv₂.gpr (by decide), hv₁.base.2.2, hv₂.base.2.2]

theorem MnT.init {x : PP → Nat} {B : PP → Prop} {a : PP × Addr} {v : State} (h : MnT x B a v) :
    MnL x B (a, trialN a.1.bits) v := by
  obtain ⟨u, -, ⟨⟨v9, v10, -⟩, -⟩, -⟩ := id h
  have hN : 1 ≤ trialN a.1.bits := by unfold trialN; split <;> decide
  refine ⟨v, h, 0, ?_, ?_, ?_⟩
  · dsimp only; omega
  · dsimp only; omega
  exact ⟨⟨by rw [v9, Nat.mul_zero, BitVec.add_zero], by rw [v10, Nat.sub_zero], rfl, rfl⟩, Keep.refl _ _⟩

/-- The go-on condition of the loop, `d.2` entries left. -/
def trialGo (x : PP → Nat) (d : (PP × Addr) × Nat) : Bool :=
  decide (x d.1.1 % VG.Impl.RsaKeyGen.tabEntry (trialN d.1.1.bits - d.2) ≠ 0 ∧
    trialN d.1.1.bits - d.2 + 1 ≠ trialN d.1.1.bits)

theorem MnL.step {x : PP → Nat} {B : PP → Prop} {d : (PP × Addr) × Nat} {w : State} (h : MnL x B d w) :
    WP isa VG.Impl.RsaKeyGen.RISCV64.Trial.entry w fun t =>
      isa.eval (.nonzero .s10) t = some (trialGo x d) ∧ (trialGo x d = false → MnE x B d t) ∧
        (trialGo x d = true → d.2 - 1 < d.2 ∧ MnL x B (d.1, d.2 - 1) t) := by
  obtain ⟨v, hv, hI⟩ := h
  obtain ⟨u, ⟨⟨⟨sv, M⟩, _⟩, _⟩, ⟨⟨_, _, vm⟩, kv⟩, _⟩ := id hv
  obtain ⟨vs, v7, v0, vc, w1, w2, hZ, ho, _, n2, htab⟩ := M.loopArgs vm kv
  refine WP.mono (VG.Proof.RsaKeyGen.RISCV64.Trial.step_ok vs v7 v0 vc w1 w2 hZ ho n2 htab hI)
    fun t ⟨e, f, g⟩ => ⟨e, fun hg => ⟨v, hv, (f (by rw [e, ← hg]; rfl)).2⟩, fun hg => ?_⟩
  obtain ⟨hm, hI'⟩ := g (by rw [e, ← hg]; rfl)
  exact ⟨by omega, v, hv, hI'⟩

theorem trialLoop_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnT x B)) VG.Impl.RsaKeyGen.RISCV64.Trial.loop (Two (MnE x B)) :=
  two_map (fun a => (a, trialN a.1.bits)) (fun _ _ h => h.init)
    (two_loopD (Φ := MnL x B) (Ψ := MnE x B) Prod.snd (fun d => (d.1, d.2 - 1)) (trialGo x)
      (two_taint _ pins_MnL (by taint_decide)) fun _ _ h => h.step)

/-- Trial division leaks the same from the same candidate and table. -/
theorem trialSieve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) trialSieve
      (Two (MnB x fun q => B q ∧ VG.Proof.RsaKeyGen.trialPrefix (x q) (trialN q.bits) = false)) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, M⟩, hL⟩ => WP.mono (trialSieve_ok M) fun _ M' => ⟨⟨sv, M'⟩, hL⟩
  unfold trialSieve VG.Impl.RsaKeyGen.RISCV64.Trial.trial
  refine RelCT.seq (two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) (Ψ := MnC x B)
    fun _ _ ⟨⟨sv, M⟩, hL⟩ => WP.mono M.count fun _ ⟨M', h208⟩ => ⟨⟨⟨sv, M'⟩, hL⟩, h208⟩) ?_
  refine RelCT.seq (RelCT.seq (two_post (two_taint_sym _ (pins_MnB fun _ _ h => h.1)
      (fun _ _ _ ⟨⟨⟨_, M₁⟩, _⟩, _⟩ ⟨⟨⟨_, M₂⟩, _⟩, _⟩ => M₁.tab.sym.trans M₂.tab.sym.symm) (by taint_decide))
    (Ψ := MnT x B) fun _ u hu => ?_) trialLoop_ct) (two_taint _ pins_MnE (by taint_decide))
  obtain ⟨⟨⟨sv, M⟩, hL⟩, h208⟩ := hu
  exact WP.mono (M.trialA h208) fun v hv => ⟨u, ⟨⟨⟨sv, M⟩, hL⟩, h208⟩, hv⟩

/-! ## The shape checks and the tests -/

/-- The shape checks' conjunction, after both sieves and trial divisions. -/
def allOk (q : PP) : Prop :=
  ((((goodRes q.g (candOf q) ∧ ∀ d ∈ oddPrimes256, candOf q % d ≠ 0) ∧
    VG.Proof.RsaKeyGen.trialPrefix (candOf q) (trialN q.bits) = false) ∧ candOf q / 2 % 2 = 1) ∧
    ∀ d ∈ oddPrimes256, candOf q / 2 % d ≠ 0) ∧
    VG.Proof.RsaKeyGen.trialPrefix (candOf q / 2) (trialN q.bits) = false

instance (q : PP) : Decidable (allOk q) := by unfold allOk; infer_instance

theorem ts_of {a : PP × Addr} {s : State} (h : MnB (fun q => candOf q / 2) allOk a s) (ha : allOk a.1) :
    TS ⟨a.1, candOf a.1, a.1.L⟩ s := by
  obtain ⟨⟨sv, M⟩, hL⟩ := h
  have hb1 : 512 ≤ a.1.bits := M.st.dims.b1
  obtain ⟨ho, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := a.1.bits) (by omega)
    (Spec.Rsa.os2ip (a.1.r.take a.1.L))
  have hq : (candOf a.1 - 1) / 2 = candOf a.1 / 2 := by unfold candOf; omega
  exact ⟨⟨sv, M.st, rfl, M.u, hL, hL⟩, by rw [hq]; exact ha.1.1.2⟩

/-- `main` leaks the same from the same arguments, tape and table. -/
theorem main_ct {R : RoundImpl} (hR : RoundCall R) : RelCT isa (Two MnI) (main R.name R.code) fun _ _ => True := by
  unfold main
  refine RelCT.assoc (RelCT.seq mainA_ct (RelCT.seq residue_ct (RelCT.seq badLoad_ct
    (two_ite' (fun a => decide (goodRes a.1.g (candOf a.1))) (fun _ _ h => h.2) ?_
      (finMnB_ct fun _ _ h => h.1.1)))))
  refine RelCT.seq (sieve_ct fun _ _ h => h.1.1) (RelCT.seq trialSieve_ct (RelCT.seq halve_ct
    (RelCT.seq (sieve_ct fun _ _ h => h) (RelCT.seq trialSieve_ct (RelCT.seq (badLoad_ct (B := allOk))
      (two_ite' (fun a => decide (allOk a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1)))))))
  exact two_map (fun a => (⟨a.1, candOf a.1, a.1.L⟩ : TQD))
    (fun _ _ ⟨⟨h, _⟩, ha⟩ => ts_of h (of_decide_eq_true ha)) (tests_ct hR)

/-! ## The candidate -/

/-- A run's public data: its arguments and tape, without the registers it
saves. -/
def qOf (s : State) : PP := (ppOf s).with fun _ => 0

/-- On entry. -/
def CI (q : PP) (s : State) : Prop := pcPre s ∧ qOf s = q

/-- `scratch_len` from the stack. -/
theorem entryL_ok {s : State} (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (hal : s.sp.toNat % 8 = 0) :
    WP isa (.block [.addSp .t3 0, .load .d .t3 .t3 0]) s fun t => t.gpr .t3 = stackArg s 0 ∧ Keep [.t3] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [stackArgAddr, stackArg, Nat.mul_zero, BitVec.add_zero] at hargs ⊢
  brun [exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, add_ofNat_zero, hargs, hal]

/-- The entry: the header's `out` and `out_len`. -/
theorem entry_ok (s : State) (h : pcPre s) :
    WP isa (.block entry) s fun t => Scr t (s.gpr .a7) (8 * (stackArg s 0).toNat) ∧ t.gpr .s6 = s.gpr .a7 ∧
      word t.mem (s.gpr .a7) 16 = s.gpr .a0 ∧ word t.mem (s.gpr .a7) 24 = s.gpr .a1 := by
  obtain ⟨hsp, hsp16, hspT, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nwS, -, alS, hb1, hb2, hL, hg,
    hsw⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  have hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat _).symm
  have h80 : 104 ≤ 8 * (stackArg s 0).toNat := by omega
  have hscr : Scr s (s.gpr .a7) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega) alS
  have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryA_ok rfl hn hargs (by omega) h80) fun tA ⟨⟨a4, _, _⟩, ka⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a4 h80 (by omega) (fun i hi => by
    rw [ka.2.2]; exact hscr.st (by omega)) fun i hi => hscr.al8 (by omega) (by omega)) fun tS hS => ?_
  have hS7 : tS.gpr .a7 = s.gpr .a7 := by rw [hS.gpr, ka.gpr (by decide)]
  refine WP.mono (header_ok (s := tS) hS7 (fun d hd => by
    rw [hS.wr, ka.2.2]; exact hscr.st (d := d) (by omega)) fun d hd h8 => hscr.al8 (by omega) h8)
    fun t₁ ⟨⟨c6, _, cm⟩, kc⟩ => ?_
  have gS : ∀ r, r ∉ ([.t3, .t4] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr hr
  obtain ⟨-, w16, w24, -⟩ := hdrW_words tS.mem (s.gpr .a7) (tS.gpr .t3)
    (tS.gpr .a0) (tS.gpr .a1) (tS.gpr .a2) (tS.gpr .a3) ((tS.gpr .a4 <<< 32) >>> 32) (tS.gpr .a5) (tS.gpr .a6)
  rw [← cm] at w16 w24
  have hwr₁ : t₁.wr = s.wr := by rw [kc.2.2, hS.wr, ka.2.2]
  exact ⟨hscr.congr hwr₁, c6, w16.trans (gS _ (by decide)), w24.trans (gS _ (by decide))⟩

/-- After `scratch_len`'s load. -/
def EL (q : PP) (t : State) : Prop := t.gpr .a7 = q.B ∧ t.gpr .t3 = BitVec.ofNat 64 q.n

theorem pins_EL : Pins EL [.a7, .t3] := by
  rintro q s₁ s₂ ⟨a7, a3⟩ ⟨b7, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a7, b7]
  · rw [a3, b3]

/-- After the entry. -/
def Z0 (q : PP) (t : State) : Prop :=
  ∃ Z, Scr t q.B Z ∧ 32 ≤ Z ∧ t.gpr .s6 = q.B ∧ t.mem.readW (q.B + BitVec.ofNat 64 16) 64 = q.op ∧
    t.mem.readW (q.B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 q.L

theorem entry_ct : RelCT isa (Two CI) (.block entry) (Two Z0) := by
  refine two_post ?_ fun q s ⟨h, hq⟩ => ?_
  · rw [show entry = [.addSp .t3 0, .load .d .t3 .t3 0] ++ entry.drop 2 from rfl]
    refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_nil _) (by taint_decide)) (Ψ := EL)
      fun q s ⟨h, hq⟩ => ?_) (two_taint _ pins_EL (by taint_decide)))
    subst hq
    have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
      ⟨⟨stackArgAddr s 0, 8⟩, by rw [h.2.2.2.1]; simp, by simp [Region.Contains]⟩
    exact WP.mono (entryL_ok hargs (by have := h.2.1; omega)) fun t ⟨t3, k⟩ =>
      ⟨k.gpr (by decide), t3.trans (ofNat_toNat _).symm⟩
  · subst hq
    have h' := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb1, -, hL, -, hsw⟩ := h'
    have hL' : (s.gpr .a1).toNat = (qOf s).L := hL
    simp only [Spec.Rsa.scratchWords] at hsw
    refine WP.mono (entry_ok s h) fun t ⟨hs, h6, w16, w24⟩ => ⟨_, hs, by omega, h6, w16, ?_⟩
    rw [← hL']; exact w24.trans (ofNat_toNat _).symm

/-- With `out` and `out_len` loaded. -/
def Z1 (q : PP) (t : State) : Prop := t.gpr .t3 = q.op ∧ t.gpr .t4 = BitVec.ofNat 64 q.L

theorem pins_Z1 : Pins Z1 [.t3, .t4] := by
  rintro q s₁ s₂ ⟨a3, a4⟩ ⟨b3, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a4, b4]

theorem zeroOut_ct : RelCT isa (Two Z0) zeroOut fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_post (two_taint _ (pins_s6 PP.B fun _ _ ⟨_, _, _, h6, _⟩ => h6) (by taint_decide))
    (Ψ := Z1) fun q s ⟨Z, hs, hZ, h6, hO, hL⟩ => ?_) (two_taint _ pins_Z1 (by taint_decide))
  exact WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun s₂ => s₂.gpr .t3 = q.op ∧ s₂.gpr .t4 = BitVec.ofNat 64 q.L)
    (by simp only [ldh, hOut, hLen]
        brun [h6, hO, hL, hs.ld (d := 16) (n := 8) (by omega), hs.ld (d := 24) (n := 8) (by omega),
          hs.al8 (d := 16) (by omega) (by decide), hs.al8 (d := 24) (by omega) (by decide),
          exec_li (show imm12 0 by decide)])
    (by rfl) (by rfl)) fun _ ⟨h, _⟩ => h

/-- On entry, with the table's address. -/
def CIT (a : PP × Addr) (s : State) : Prop := CI a.1 s ∧ s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = a.2

/-- After the front. -/
def BI (a : PP × Addr) (t : State) : Prop :=
  ∃ sv, St (a.1.with sv) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧ TabIn a.1.B a.1.Z a.2 t

theorem front_ct : RelCT isa (Two CIT) (.seq (.block entry) zeroOut) (Two BI) :=
  two_post (two_map Prod.fst (fun _ _ h => h.1) (RelCT.seq entry_ct zeroOut_ct)) fun a s ⟨⟨h, hq⟩, hy⟩ => by
    obtain ⟨q, T⟩ := a
    dsimp only at hq hy
    subst hq hy
    exact WP.mono (front_tab s h) fun _ ⟨st, hU, ht⟩ => ⟨_, st, hU, ht⟩

/-- With the tape's length and `out_len` loaded. -/
def L34 (q : PP) (t : State) : Prop :=
  t.gpr .t3 = BitVec.ofNat 64 q.r.length ∧ t.gpr .t4 = BitVec.ofNat 64 q.L

theorem pins_L34 : Pins L34 [.t3, .t4] := by
  rintro q s₁ s₂ ⟨a3, a4⟩ ⟨b3, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a4, b4]

/-- After the length check. -/
def LC (a : PP × Addr) (t : State) : Prop :=
  isa.eval (.zero .t5) t = some (decide ((if a.1.L ≤ a.1.r.length then 1 else 0) = 0)) ∧
    ∃ sv, St (a.1.with sv) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧ TabIn a.1.B a.1.Z a.2 t

theorem lenChk_ct :
    RelCT isa (Two BI) (.block (([ldh .t3 hRandLen, ldh .t4 hLen] : List Instr) ++ geFlag .t5 .t3 .t4)) (Two LC) :=
  two_post (two_map (Φ' := fun q t => ∃ sv, St (q.with sv) t) Prod.fst (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩)
      (RelCT.block_append (RelCT.seq (two_post
      (two_taint _ (pins_s6 PP.B fun _ _ ⟨_, h⟩ => h.s6) (by taint_decide)) (Ψ := L34)
      fun _ _ ⟨_, h⟩ => WP.mono (lenLoad_ok h) fun _ ⟨⟨⟨a3, a4, _⟩, _⟩, _⟩ => ⟨a3, a4⟩)
      (two_taint _ pins_L34 (by taint_decide)))))
    fun _ _ ⟨sv, h, hU, ht⟩ => WP.mono_syms (lenChk_ok h hU) fun _ ⟨he, st, hU', vm, vrd⟩ sy =>
      ⟨he, sv, st, hU', ht.step sy (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vrd⟩

/-- Before the exit. -/
def XE (q : PP) (t : State) : Prop := ∃ sv, ESt (q.with sv) t

theorem body_ct {R : RoundImpl} (hR : RoundCall R) : RelCT isa (Two BI)
    (.seq (.block (([ldh .t3 hRandLen, ldh .t4 hLen] : List Instr) ++ geFlag .t5 .t3 .t4))
      (.ite (.zero .t5) (.block (finish 0)) (main R.name R.code))) (Two fun (a : PP × Addr) => XE a.1) := by
  refine two_post (RelCT.seq lenChk_ct (two_ite'
    (fun a : PP × Addr => decide ((if a.1.L ≤ a.1.r.length then 1 else 0) = 0))
    (fun _ _ h => h.1) ?_ ?_)) fun _ _ ⟨sv, h, hU, ht⟩ => WP.mono (body_ok hR h ht hU) fun _ ht => ⟨sv, ht.1⟩
  · exact two_map Prod.fst (fun _ _ ⟨⟨_, _, h, _⟩, _⟩ => h.fs) (finish_ct (.inl rfl))
  · refine two_mono (fun q _ ⟨⟨_, sv, h, hU, ht⟩, hb⟩ => ⟨sv, h, ht, hU, ?_⟩) (main_ct hR)
    by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega)])

/-- With the save area's word count loaded. -/
def X1 (q : PP) (t : State) : Prop := t.gpr .t3 = BitVec.ofNat 64 q.n ∧ t.gpr .s6 = q.B

theorem pins_X1 : Pins X1 [.t3, .s6] := by
  rintro q s₁ s₂ ⟨a3, a6⟩ ⟨b3, b6⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a6, b6]

theorem exit_ct : RelCT isa (Two XE) (.block exit) fun _ _ => True := by
  rw [show exit = [ldh .t3 hWsLen] ++ exit.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_s6 PP.B fun _ _ ⟨_, h⟩ => h.s6)
    (by taint_decide)) (Ψ := X1) fun q t ⟨sv, h⟩ => ?_) (two_taint _ pins_X1 (by taint_decide)))
  have hdn := h.dims.n
  have hZe : (q.with sv).Z = 8 * (q.with sv).n := rfl
  have l0 : InRegions (t.rd ++ t.wr) (q.B + BitVec.ofNat 64 0) 8 := h.scr.ld (d := 0) (by omega)
  have a0 : (q.B + BitVec.ofNat 64 0).toNat % 8 = 0 := h.scr.al8 (d := 0) (by omega) (by decide)
  exact WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (q.with sv).n)
    (by simp only [ldh, hWsLen]; brun [show t.gpr .s6 = q.B from h.s6, l0, a0, show t.mem.readW (q.B + BitVec.ofNat 64 0) 64 =
      BitVec.ofNat 64 (q.with sv).n from h.len]) (by rfl) (by rfl)) fun _ ⟨u3, k⟩ =>
    ⟨u3, (k.gpr (by decide)).trans h.s6⟩

/-- `vg_ffdh_parameter_candidate_sieved` leaks the same from the same public
arguments and tape. -/
theorem code_rel {R : RoundImpl} (hR : RoundCall R) : RelCT isa (Two CIT) (code R.name R.code) fun _ _ => True := by
  unfold code
  exact RelCT.assoc (RelCT.seq front_ct (RelCT.assoc (RelCT.seq (body_ct hR) (two_map Prod.fst (fun _ _ h => h)
    exit_ct))))

theorem qOf_pub {s t : State} (h : pcPub s t) : qOf s = qOf t := by
  obtain ⟨hsp, hr, h0, -, h2, h3, h4, h5, -, h7, hst, -⟩ := h
  have hr' : pcRand s = pcRand t :=
    (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hr
  simp only [qOf, PP.with, ppOf, hsp, h0, h2, h3, h4, h5, h7, hst, hr']

/-- `vg_ffdh_parameter_candidate_sieved` in constant time, for a round whose call
meets `RoundCall`. -/
theorem code_ct {R : RoundImpl} (hR : RoundCall R) :
    ConstantTime isa pcContract.pre pcContract.pub (code R.name R.code) :=
  RelCT.constantTime ((code_rel hR).mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨(qOf s, s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol), ⟨⟨hs, rfl⟩, rfl⟩,
      ⟨⟨ht, (qOf_pub hp).symm⟩, hp.2.2.2.2.2.2.2.2.2.2.2.symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
