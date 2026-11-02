module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Hyp
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Trial
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Trial
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Hyp
meta import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Trial
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Trial
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Mont.Words32

/-!
# A candidate on RISC-V: the shared trial division meets `DivOk`

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/TrialOk.lean`). `trial_wp`: the
shared `Trial.trial hTrial` (`Impl/RsaKeyGen/RISCV64/Trial.lean`) from a
`DivIn` state: the table's address (`lla`) and the count of entries from
header word `hTrial` (`trialA_ok`), then the loop (`loop_ok`), with `a4` the
flag of a divisor among the first `n` entries. `trial_ct`: two runs whose
candidates the first `n` entries divide alike leak the same trace: whether
the loop goes on (`step_ok`) is a function of the entries tested and of
which of them divide the candidate. `trial_divOk`: both.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand.TrialOk

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Candidate (hTrial)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed TrialTable32.entry)
open VG.Impl.MillerRabin.RISCV64.Search (ldh)
open VG.Proof.Bignum (slot word)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.RISCV64 (Env A)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint)
open VG.Proof.RsaKeyGen.RISCV64.Trial (TInv Tab step_ok loop_ok entryRegs)
open VG.Proof.RsaKeyGen (trialPrefix entryDivides)

/-- The state after `c` has the stack pointer and the addresses of statics
it had before. -/
theorem wp_of_sp_syms {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.sp = s.sp → s'.syms = s.syms → Q s') : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq (Exec.sp he) (Exec.syms he)⟩

/-- The table's address and the count of entries, before the loop. -/
abbrev trialA : List Instr := [.lla .s9 TrialTable32.symbol, ldh .s10 hTrial]

/-- After them, from `s`. -/
def TA (s : State) (n : Nat) (u : State) : Prop :=
  (u.gpr .s9 = s.syms TrialTable32.symbol ∧ u.gpr .s10 = BitVec.ofNat 64 n ∧ u.mem = s.mem) ∧
    (∀ r, r ∉ tdRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.syms = s.syms

theorem trialA_ok {s : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n) :
    WP isa (.block trialA) s (TA s n) := by
  have e := h.env
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine wp_of_sp_syms (WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = s.syms TrialTable32.symbol ∧
      u.gpr .s10 = BitVec.ofNat 64 n ∧ u.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨q, ku⟩ hsp hsy => ⟨q, fun r hr => ku.gpr (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> decide)), ku.2.1, ku.2.2, hsp, hsy⟩)
  refine Steps.WP.cons exec_lla ?_
  have c := h.cnt
  simp only [ldh, hTrial, VG.Proof.Bignum.word] at c ⊢
  brun [e.s6, hs.ld (d := 128) (n := 8) (by omega), hs.al8 (d := 128) (by omega) (by decide), c]

/-- What the loop's start gives each entry. -/
theorem TA.facts {s u : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n) (hu : TA s n u) :
    Scr u B Z ∧ u.gpr .a7 = off B (slot w 0) ∧ u.gpr .t0 = BitVec.ofNat 64 w ∧
      val32 u.mem B (slot w 0) (2 * w) = A s.mem B w 0 ∧ 1 ≤ w ∧ w < 2 ^ 31 ∧ slot w 0 + 8 * w ≤ Z ∧
      slot w 0 % 4 = 0 ∧ Tab u (s.syms TrialTable32.symbol) n := by
  obtain ⟨⟨-, -, um⟩, ug, urd, uwr, -⟩ := hu
  have e := h.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw := e.hw
  have hw' := e.hw'
  have hn' := h.n2
  have hfit := h.fit
  have hal := h.al
  refine ⟨e.hs.congr uwr, (ug _ (by decide)).trans e.a7, (ug _ (by decide)).trans e.t0,
    by rw [um, ← wordsVal_eq_val32], by omega, by omega, by simp only [slot, hdrBytes]; omega,
    by simp only [slot, hdrBytes]; omega, fun i hi => ⟨?_, ⟨_, by rw [urd]; exact List.mem_append_left _ h.tab, ?_⟩, ?_⟩⟩
  · have hl : i < TrialTable32.packed.length := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; omega
    rw [um, h.held i (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
      VG.Proof.RsaKeyGen.TrialTable32.packed_entry (by omega)]
  · simp only [Region.Contains, Offset.add_sub_cancel_left]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · have e8 : (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)).toNat =
        (s.syms TrialTable32.symbol).toNat + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e8]; omega

/-- Trial division of the candidate in array 0 by the table's first `n`
entries. -/
theorem trial_wp {s : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Trial.trial hTrial) s fun t =>
      t.gpr .a4 = BitVec.ofNat 64 (if trialPrefix (A s.mem B w 0) n then 1 else 0) ∧ t.mem = s.mem ∧
        (∀ r, r ∉ tdRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.syms = s.syms := by
  unfold VG.Impl.RsaKeyGen.RISCV64.Trial.trial
  refine WP.seq (WP.mono (trialA_ok h) fun u hu => ?_)
  obtain ⟨hs, h7, ht0, hc, hw, hw', hZ, ho, htab⟩ := hu.facts h
  refine wp_of_sp_syms (WP.mono (loop_ok hs h7 ht0 hc hw hw' hZ ho h.n1 h.n2 hu.1.1 htab hu.1.2.1)
    fun t ⟨⟨t4, tm⟩, kt⟩ hsp hsy => ?_)
  obtain ⟨⟨-, -, um⟩, ug, urd, uwr, usp, usy⟩ := hu
  have sub : ∀ r ∈ entryRegs, r ∈ tdRegs := by decide
  exact ⟨t4, tm.trans um, fun r hr => (kt.gpr (fun hm => hr (sub r hm))).trans (ug r hr),
    kt.2.1.trans urd, kt.2.2.trans uwr, hsp.trans usp, hsy.trans usy⟩

/-! ## Constant time -/

/-- Code the taint analysis with the table's address public proves constant
time, from states a predicate relates. -/
theorem two_taint_sym {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.syms TrialTable32.symbol = s₂.syms TrialTable32.symbol)
    {hc : VG.Taint.Hint VG.RISCV64.Taint.T}
    (h : (VG.Taint.check (taintSym [TrialTable32.symbol]) (VG.RISCV64.Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [TrialTable32.symbol]) (VG.RISCV64.Taint.ofRegs rs) (fun _ _ ⟨a, h₁, h₂⟩ => by
    obtain ⟨hsp, hr⟩ := hpin a _ _ h₁ h₂
    refine ⟨⟨hsp, fun r hr' => hr r (VG.RISCV64.Taint.mem_ofRegs.mp hr')⟩, fun n hn => ?_⟩
    simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂) h

/-- What two runs of trial division share: the working space, the count, the
table's address, the stack pointer, and which of the first `n` entries divide
the candidate. -/
structure TD where
  B : Addr
  T : Addr
  Z : Nat
  w : Nat
  n : Nat
  sp : Addr
  div : Nat → Bool

/-- Trial division's start. -/
def TS (d : TD) (s : State) : Prop :=
  DivIn s d.B d.Z d.w d.n ∧ s.syms TrialTable32.symbol = d.T ∧ s.sp = d.sp ∧
    ∀ i < d.n, entryDivides (A s.mem d.B d.w 0) i = d.div i

/-- The loop's state, with `m` entries left. -/
def TL (m : Nat) (d : TD) (v : State) : Prop :=
  ∃ s u, TS d s ∧ TA s d.n u ∧ TInv u d.T (A s.mem d.B d.w 0) d.n m v ∧ v.sp = d.sp

theorem TS.init {d : TD} {s u : State} (h : TS d s) (hu : TA s d.n u) :
    TInv u d.T (A s.mem d.B d.w 0) d.n d.n u ∧ u.sp = d.sp := by
  obtain ⟨⟨u9, u10, -⟩, -, -, -, usp, -⟩ := hu
  have h1 := h.1.n1
  exact ⟨⟨0, by omega, by omega, ⟨by rw [u9, h.2.1, Nat.mul_zero, BitVec.add_zero], by rw [u10, Nat.sub_zero],
    rfl, rfl⟩, Keep.refl _ _⟩, usp.trans h.2.2.1⟩

theorem TL.regs {m : Nat} {d : TD} {v : State} (h : TL m d v) :
    v.gpr .a7 = off d.B (slot d.w 0) ∧ v.gpr .t0 = BitVec.ofNat 64 d.w ∧
      v.gpr .s9 = d.T + BitVec.ofNat 64 (8 * (d.n - m)) ∧ v.sp = d.sp := by
  obtain ⟨s, u, hs, hu, ⟨k, hm, hk, ⟨v9, -, -, -⟩, kv⟩, vsp⟩ := h
  obtain ⟨-, h7, ht0, -⟩ := hu.facts hs.1
  exact ⟨(kv.gpr (by decide)).trans h7, (kv.gpr (by decide)).trans ht0, by rw [v9]; congr 3; omega, vsp⟩

theorem trial_ct : RelCT isa (Two TS) (VG.Impl.RsaKeyGen.RISCV64.Trial.trial hTrial) fun _ _ => True := by
  have pS : Pins TS [.s6] := by
    rintro d s₁ s₂ ⟨h₁, -, sp₁, -⟩ ⟨h₂, -, sp₂, -⟩
    refine ⟨sp₁.trans sp₂.symm, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.s6, h₂.env.s6]
  have pL : ∀ m, Pins (TL m) [.a7, .t0, .s9] := fun m d s₁ s₂ h₁ h₂ => by
    obtain ⟨a7, a0, a9, asp⟩ := h₁.regs
    obtain ⟨b7, b0, b9, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a7, b7]
    · rw [a0, b0]
    · rw [a9, b9]
  unfold VG.Impl.RsaKeyGen.RISCV64.Trial.trial
  refine RelCT.seq (two_post (Ψ := fun d u => ∃ s, TS d s ∧ TA s d.n u)
    (two_taint_sym _ pS (fun d s₁ s₂ h₁ h₂ => h₁.2.1.trans h₂.2.1.symm) (by taint_decide))
    fun d s h => WP.mono (trialA_ok h.1) fun u hu => ⟨s, h, hu⟩) ?_
  refine (RelCT.exists_ fun m => RelCT.loop (M := isa) (fun m => Two (TL m)) (fun m => ?_) m).mono
    (fun _ _ ⟨d, ⟨a₁, h₁, u₁⟩, ⟨a₂, h₂, u₂⟩⟩ =>
      ⟨d.n, d, ⟨a₁, _, h₁, u₁, h₁.init u₁⟩, ⟨a₂, _, h₂, u₂, h₂.init u₂⟩⟩) fun _ _ h => h
  refine (two_post (Ψ := fun d t => ∃ s u, TS d s ∧ TA s d.n u ∧
      isa.eval (.nonzero .s10) t = some (decide (d.div (d.n - m) = false ∧ d.n - m + 1 ≠ d.n)) ∧
      (isa.eval (.nonzero .s10) t = some true →
        0 < m ∧ TInv u d.T (A s.mem d.B d.w 0) d.n (m - 1) t ∧ t.sp = d.sp))
    (two_taint _ (pL m) (by taint_decide)) fun d v ⟨s, u, hs, hu, hI, vsp⟩ => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨hsc, h7, ht0, hc, hw, hw', hZ, ho, htab⟩ := hu.facts hs.1
    rw [hs.2.1] at htab
    have hk : d.n - m < d.n := by obtain ⟨k, hm, hk, -⟩ := hI; omega
    refine wp_of_sp_syms (WP.mono (step_ok hsc h7 ht0 hc hw hw' hZ ho hs.1.n2 htab hI)
      fun t ⟨e, _, g⟩ tsp _ => ⟨s, u, hs, hu, ?_, fun he => ⟨(g he).1, (g he).2, tsp.trans vsp⟩⟩)
    rw [e, ← hs.2.2.2 _ hk]
    simp only [entryDivides, decide_eq_false_iff_not]
  · rintro s₁ s₂ ⟨d, ⟨a₁, u₁, h₁, hu₁, e₁, g₁⟩, ⟨a₂, u₂, h₂, hu₂, e₂, g₂⟩⟩
    refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun he => ?_⟩
    obtain ⟨hm, i₁, sp₁⟩ := g₁ he
    obtain ⟨-, i₂, sp₂⟩ := g₂ (e₂.trans (e₁.symm.trans he))
    exact ⟨m - 1, by omega, d, ⟨a₁, u₁, h₁, hu₁, i₁, sp₁⟩, ⟨a₂, u₂, h₂, hu₂, i₂, sp₂⟩⟩

/-- The shared trial division is what the candidate's proofs need. -/
theorem trial_divOk : DivOk (VG.Impl.RsaKeyGen.RISCV64.Trial.trial hTrial) where
  ok h := trial_wp h
  ct hP := trial_ct.mono (fun s₁ s₂ hp => by
      obtain ⟨B, Z, w, n, h₁, h₂, hsp, hsy, hdiv⟩ := hP s₁ s₂ hp
      exact ⟨⟨B, s₁.syms TrialTable32.symbol, Z, w, n, s₁.sp, entryDivides (A s₁.mem B w 0)⟩,
        ⟨h₁, rfl, rfl, fun _ _ => rfl⟩, ⟨h₂, hsy.symm, hsp.symm, fun i hi => (hdiv i hi).symm⟩⟩)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.RISCV64.Cand.TrialOk
