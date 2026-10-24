module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Trial
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Trial
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA's probable-prime test on PPC64LE: constant time of trial division

`trial_ct`: two runs of trial division of the same candidate (public, as
DSA's primes are) by the same table leak the same trace. The table's address
is public (`taintSym`, as the contract with the table says); each entry
(`entry`) passes the taint analysis from the table's address, which the loop's
state `TInv` fixes, and whether the loop goes on (`step_ok`) is a function of
the candidate and of the entries tested.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search (ldh)
open VG.Proof.Bignum (word off slot)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)
open VG.Proof.RsaKeyGen.PPC64LE.Trial (TInv step_ok entryRegs)

/-- Code the taint analysis with the table's address public proves constant
time, from states a predicate relates. -/
theorem two_taint_sym {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.syms TrialTable32.symbol = s₂.syms TrialTable32.symbol)
    {hc : VG.Taint.Hint VG.PPC64LE.Taint.T}
    (h : (VG.Taint.check (taintSym [TrialTable32.symbol]) (VG.PPC64LE.Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [TrialTable32.symbol]) (VG.PPC64LE.Taint.ofRegs rs) (fun _ _ ⟨a, h₁, h₂⟩ => by
    obtain ⟨hsp, hr⟩ := hpin a _ _ h₁ h₂
    refine ⟨⟨hsp, fun r hr' => hr r (VG.PPC64LE.Taint.mem_ofRegs.mp hr')⟩, fun n hn => ?_⟩
    simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂) h

/-- The public data of trial division. -/
structure TD where
  B : Addr
  T : Addr
  L : Nat
  w : Nat
  c : Nat
  n : Nat
  sp : Addr

/-- Trial division's start. -/
def TS (d : TD) (s : State) : Prop :=
  Env s d.B (8 * d.L) d.w ∧ arr s.mem d.B d.w 0 = d.c ∧ word s.mem d.B (8 * hCnt) = BitVec.ofNat 64 d.n ∧
    s.syms TrialTable32.symbol = d.T ∧ Tab d.T s.mem ∧ (⟨d.T, 8192⟩ : Region) ∈ s.rd ∧ s.sp = d.sp ∧
    1 ≤ d.n ∧ d.n ≤ 1024

/-- The first block: the table's address and the entries. -/
abbrev trialA : List Instr := [.adrSym .r23 TrialTable32.symbol, ldh .r24 hCnt]

/-- After it. -/
def TA (d : TD) (u : State) : Prop :=
  ∃ s, TS d s ∧ (u.gpr .r23 = d.T ∧ u.gpr .r24 = BitVec.ofNat 64 d.n ∧ u.mem = s.mem ∧ u.syms = s.syms) ∧
    (∀ r, r ∉ trialRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp

theorem trialA_ok {d : TD} {s : State} (h : TS d s) : WP isa (.block trialA) s (TA d) := by
  obtain ⟨e, -, hcnt, hT, -, -, -, -, -⟩ := id h
  have hZ : 256 + 28 * (8 * (d.w + 2)) ≤ 8 * d.L := e.hZ
  refine WP.cons (exec_adrSym (by decide)) ?_
  simp only [ldh, hCnt]
  prun [e.h31, e.hs.ld (d := 40) (n := 8) (by omega)]
  refine ⟨s, h, ⟨hT, hcnt, rfl, rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
  have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
  simp only [State.write, h1, h2, ↓reduceIte]

/-- The loop's state, with `m` entries left. -/
def TL (m : Nat) (d : TD) (v : State) : Prop := ∃ u, TA d u ∧ TInv u d.T d.c d.n m v

/-- What the loop's start gives each iteration. -/
theorem TA.facts {d : TD} {u : State} (h : TA d u) :
    Scr u d.B (8 * d.L) ∧ u.gpr .r10 = off d.B (slot d.w 0) ∧ u.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧
      VG.Proof.Mont.val32 u.mem d.B (slot d.w 0) (2 * d.w) = d.c ∧ 4 ≤ d.w ∧ d.w ≤ 128 ∧
      slot d.w 0 + 8 * d.w ≤ 8 * d.L ∧ d.n ≤ 1024 ∧ u.sp = d.sp ∧
      (∀ i < d.n, u.mem.readW (d.T + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i) ∧
        InRegions (u.rd ++ u.wr) (d.T + BitVec.ofNat 64 (8 * i)) 8) := by
  obtain ⟨s, ⟨e, hc, -, -, htab, hTr, sp, -, hn⟩, ⟨-, -, um, -⟩, ug, urd, uwr, usp⟩ := h
  have hZ : 256 + 28 * (8 * (d.w + 2)) ≤ 8 * d.L := e.hZ
  refine ⟨e.hs.congr uwr, (ug _ (by decide)).trans e.h10, (ug _ (by decide)).trans e.h11, by rw [um]; exact hc,
    e.hw, e.hw', by simp only [slot, hdrBytes]; omega, hn, usp.trans sp, fun i hi => ⟨by rw [um]; exact htab i (by omega),
      ⟨_, by rw [urd]; exact List.mem_append_left _ hTr, ?_⟩⟩⟩
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem TA.init {d : TD} {u : State} (h : TA d u) : TInv u d.T d.c d.n d.n u := by
  obtain ⟨s, ⟨-, -, -, -, -, -, -, h1, -⟩, ⟨u23, u24, -, -⟩, -⟩ := h
  exact ⟨0, by omega, by omega, ⟨by rw [u23, Nat.mul_zero, BitVec.add_zero], by rw [u24, Nat.sub_zero], rfl, rfl⟩,
    Keep.refl _ _⟩

theorem TL.regs {m : Nat} {d : TD} {v : State} (h : TL m d v) :
    v.gpr .r10 = off d.B (slot d.w 0) ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧
      v.gpr .r23 = d.T + BitVec.ofNat 64 (8 * (d.n - m)) ∧ v.sp = d.sp := by
  obtain ⟨u, hu, k, hm, hk, ⟨v23, -, -, -⟩, kv⟩ := h
  obtain ⟨-, h10, h11, -, -, -, -, -, sp, -⟩ := hu.facts
  refine ⟨(kv.gpr _ (by decide)).trans h10, (kv.gpr _ (by decide)).trans h11, by rw [v23]; congr 3; omega,
    kv.sp.trans sp⟩

theorem trial_ct : RelCT isa (Two TS) (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hCnt) fun _ _ => True := by
  have pS : Pins TS [.r31] := by
    rintro d s₁ s₂ ⟨e₁, -, -, -, -, -, sp₁, -⟩ ⟨e₂, -, -, -, -, -, sp₂, -⟩
    refine ⟨sp₁.trans sp₂.symm, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁.h31, e₂.h31]
  have pL : ∀ m, Pins (TL m) [.r10, .r11, .r23] := fun m d s₁ s₂ h₁ h₂ => by
    obtain ⟨a10, a11, a23, asp⟩ := h₁.regs
    obtain ⟨b10, b11, b23, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a10, b10]
    · rw [a11, b11]
    · rw [a23, b23]
  unfold VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  refine RelCT.seq (two_post (Ψ := TA) (two_taint_sym _ pS (fun d s₁ s₂ h₁ h₂ => h₁.2.2.2.1.trans h₂.2.2.2.1.symm)
    (by taint_decide)) fun d s h => trialA_ok h) ?_
  refine (RelCT.exists_ fun m => RelCT.loop (M := isa) (fun m => Two (TL m)) (fun m => ?_) m).mono
    (fun s₁ s₂ ⟨d, h₁, h₂⟩ => ⟨d.n, d, ⟨s₁, h₁, h₁.init⟩, ⟨s₂, h₂, h₂.init⟩⟩) fun _ _ h => h
  refine (two_post (Ψ := fun d t => ∃ u, TA d u ∧
      isa.eval (.nonzero .d .r24) t = some (decide (d.c % tabEntry (d.n - m) ≠ 0 ∧ d.n - m + 1 ≠ d.n)) ∧
      (isa.eval (.nonzero .d .r24) t = some true → 0 < m ∧ TInv u d.T d.c d.n (m - 1) t))
    (two_taint _ (pL m) (by taint_decide)) fun d v ⟨u, hu, hI⟩ => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨hs, h10, h11, hc, hw4, hw128, hZ, hn, -, htab⟩ := hu.facts
    exact WP.mono (step_ok hs h10 h11 hc (by omega) (by omega) hZ hn htab hI) fun t ⟨e, _, g⟩ => ⟨u, hu, e, g⟩
  · rintro s₁ s₂ ⟨d, ⟨u₁, hu₁, e₁, g₁⟩, ⟨u₂, hu₂, e₂, g₂⟩⟩
    refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun he => ?_⟩
    obtain ⟨hm, i₁⟩ := g₁ he
    obtain ⟨-, i₂⟩ := g₂ (e₂.trans (e₁.symm.trans he))
    exact ⟨m - 1, by omega, d, ⟨u₁, hu₁, i₁⟩, ⟨u₂, hu₂, i₂⟩⟩

end VG.Proof.Dsa.PPC64LE.Prime
