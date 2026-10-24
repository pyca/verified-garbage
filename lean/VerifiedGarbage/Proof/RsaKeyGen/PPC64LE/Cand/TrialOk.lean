module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Hyp
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Hyp
meta import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A candidate on PPC64LE: the shared trial division meets `DivOk`

`trial_wp`: the shared `Trial.trial hTrial` (`Impl/RsaKeyGen/PPC64LE/Trial.lean`)
from a `DivIn` state: the table's address (`adrSym`) and the count of entries
from header word `hTrial` (`trialA_ok`), then the loop (`loop_ok`), with `r22`
the flag of a divisor among the first `n` entries. `trial_ct`: two runs whose
candidates the first `n` entries divide alike leak the same trace, as DSA's
`trial_ct` (`Proof/Dsa/PPC64LE/Prime/CTTrial.lean`) for one candidate: whether
the loop goes on (`step_ok`) is a function of the entries tested and of which
of them divide the candidate. `trial_divOk`: both.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand.TrialOk

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (hTrial)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed TrialTable32.entry)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh)
open VG.Proof.Bignum (slot)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint)
open VG.Proof.RsaKeyGen.PPC64LE.Trial (TInv step_ok loop_ok)
open VG.Proof.RsaKeyGen (trialPrefix entryDivides)

/-- The table's address and the count of entries, before the loop. -/
abbrev trialA : List Instr := [.adrSym .r23 TrialTable32.symbol, ldh .r24 hTrial]

/-- After them, from `s`. -/
def TA (s : State) (n : Nat) (u : State) : Prop :=
  (u.gpr .r23 = s.syms TrialTable32.symbol ∧ u.gpr .r24 = BitVec.ofNat 64 n ∧ u.mem = s.mem) ∧
    (∀ r, r ∉ tdRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp

theorem trialA_ok {s : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n) :
    WP isa (.block trialA) s (TA s n) := by
  have e := h.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.cons (exec_adrSym (by decide)) ?_
  simp only [ldh, hTrial]
  prun [e.h31, e.hs.ld (d := 128) (n := 8) (by omega)]
  refine ⟨⟨rfl, h.cnt, rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
  have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
  simp only [State.write, h1, h2, ↓reduceIte]

/-- What the loop's start gives each entry. -/
theorem TA.facts {s u : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n) (hu : TA s n u) :
    Scr u B Z ∧ u.gpr .r10 = off B (slot w 0) ∧ u.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧
      val32 u.mem B (slot w 0) (2 * w) = arr s.mem B w 0 ∧ 1 ≤ w ∧ w < 2 ^ 31 ∧ slot w 0 + 8 * w ≤ Z ∧
      (∀ i < n, u.mem.readW (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
          BitVec.ofNat 64 (TrialTable32.entry i) ∧
        InRegions (u.rd ++ u.wr) (s.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 8) := by
  obtain ⟨⟨-, -, um⟩, ug, urd, uwr, -⟩ := hu
  have e := h.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw := e.hw
  have hw' := e.hw'
  have hn' := h.n2
  have hfit := h.fit
  refine ⟨e.hs.congr uwr, (ug _ (by decide)).trans e.h10, (ug _ (by decide)).trans e.h11, by rw [um], by omega,
    by omega, by simp only [slot, hdrBytes]; omega, fun i hi => ⟨?_, ⟨_, by rw [urd]; exact List.mem_append_left _ h.tab, ?_⟩⟩⟩
  · have hl : i < TrialTable32.packed.length := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; omega
    rw [um, h.held i (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
      VG.Proof.RsaKeyGen.TrialTable32.packed_entry (by omega)]
  · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- Trial division of the candidate in array 0 by the table's first `n`
entries. -/
theorem trial_wp {s : State} {B : Addr} {Z w n : Nat} (h : DivIn s B Z w n) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hTrial) s fun t =>
      t.gpr .r22 = BitVec.ofNat 64 (if trialPrefix (arr s.mem B w 0) n then 1 else 0) ∧ t.mem = s.mem ∧
        (∀ r, r ∉ tdRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  refine WP.seq (WP.mono (trialA_ok h) fun u hu => ?_)
  obtain ⟨hs, h10, h11, hc, hw, hw', hZ, htab⟩ := hu.facts h
  refine WP.mono (loop_ok hs h10 h11 hc hw hw' hZ h.n1 h.n2 hu.1.1 htab hu.1.2.1) fun t ⟨⟨t22, tm⟩, kt⟩ => ?_
  obtain ⟨⟨-, -, um⟩, ug, urd, uwr, usp⟩ := hu
  exact ⟨t22, tm.trans um, fun r hr => (kt.gpr r hr).trans (ug r hr), kt.rd.trans urd, kt.wr.trans uwr,
    kt.sp.trans usp⟩

/-! ## Constant time -/

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
    ∀ i < d.n, entryDivides (arr s.mem d.B d.w 0) i = d.div i

/-- The loop's state, with `m` entries left. -/
def TL (m : Nat) (d : TD) (v : State) : Prop :=
  ∃ s u, TS d s ∧ TA s d.n u ∧ TInv u d.T (arr s.mem d.B d.w 0) d.n m v

theorem TS.init {d : TD} {s u : State} (h : TS d s) (hu : TA s d.n u) :
    TInv u d.T (arr s.mem d.B d.w 0) d.n d.n u := by
  obtain ⟨⟨u23, u24, -⟩, -⟩ := hu
  have h1 := h.1.n1
  exact ⟨0, by omega, by omega, ⟨by rw [u23, h.2.1, Nat.mul_zero, BitVec.add_zero], by rw [u24, Nat.sub_zero], rfl, rfl⟩,
    Keep.refl _ _⟩

theorem TL.regs {m : Nat} {d : TD} {v : State} (h : TL m d v) :
    v.gpr .r10 = off d.B (slot d.w 0) ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧
      v.gpr .r23 = d.T + BitVec.ofNat 64 (8 * (d.n - m)) ∧ v.sp = d.sp := by
  obtain ⟨s, u, hs, hu, k, hm, hk, ⟨v23, -, -, -⟩, kv⟩ := h
  obtain ⟨-, h10, h11, -⟩ := hu.facts hs.1
  refine ⟨(kv.gpr _ (by decide)).trans h10, (kv.gpr _ (by decide)).trans h11, by rw [v23]; congr 3; omega,
    kv.sp.trans (hu.2.2.2.2.trans hs.2.2.1)⟩

theorem trial_ct : RelCT isa (Two TS) (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hTrial) fun _ _ => True := by
  have pS : Pins TS [.r31] := by
    rintro d s₁ s₂ ⟨h₁, -, sp₁, -⟩ ⟨h₂, -, sp₂, -⟩
    refine ⟨sp₁.trans sp₂.symm, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.h31, h₂.env.h31]
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
  refine RelCT.seq (two_post (Ψ := fun d u => ∃ s, TS d s ∧ TA s d.n u)
    (two_taint_sym _ pS (fun d s₁ s₂ h₁ h₂ => h₁.2.1.trans h₂.2.1.symm) (by taint_decide))
    fun d s h => WP.mono (trialA_ok h.1) fun u hu => ⟨s, h, hu⟩) ?_
  refine (RelCT.exists_ fun m => RelCT.loop (M := isa) (fun m => Two (TL m)) (fun m => ?_) m).mono
    (fun _ _ ⟨d, ⟨a₁, h₁, u₁⟩, ⟨a₂, h₂, u₂⟩⟩ =>
      ⟨d.n, d, ⟨a₁, _, h₁, u₁, h₁.init u₁⟩, ⟨a₂, _, h₂, u₂, h₂.init u₂⟩⟩) fun _ _ h => h
  refine (two_post (Ψ := fun d t => ∃ s u, TS d s ∧ TA s d.n u ∧
      isa.eval (.nonzero .d .r24) t = some (!d.div (d.n - m) && decide (d.n - m + 1 ≠ d.n)) ∧
      (isa.eval (.nonzero .d .r24) t = some true → 0 < m ∧ TInv u d.T (arr s.mem d.B d.w 0) d.n (m - 1) t))
    (two_taint _ (pL m) (by taint_decide)) fun d v ⟨s, u, hs, hu, hI⟩ => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨hsc, h10, h11, hc, hw, hw', hZ, htab⟩ := hu.facts hs.1
    rw [hs.2.1] at htab
    have hk : d.n - m < d.n := by obtain ⟨k, hm, hk, -⟩ := hI; omega
    refine WP.mono (step_ok hsc h10 h11 hc hw hw' hZ hs.1.n2 htab hI) fun t ⟨e, _, g⟩ => ⟨s, u, hs, hu, ?_, g⟩
    rw [e, ← hs.2.2.2 _ hk]
    simp only [entryDivides, ne_eq, Bool.decide_and, decide_not]
  · rintro s₁ s₂ ⟨d, ⟨a₁, u₁, h₁, hu₁, e₁, g₁⟩, ⟨a₂, u₂, h₂, hu₂, e₂, g₂⟩⟩
    refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun he => ?_⟩
    obtain ⟨hm, i₁⟩ := g₁ he
    obtain ⟨-, i₂⟩ := g₂ (e₂.trans (e₁.symm.trans he))
    exact ⟨m - 1, by omega, d, ⟨a₁, u₁, h₁, hu₁, i₁⟩, ⟨a₂, u₂, h₂, hu₂, i₂⟩⟩

/-- The shared trial division is what the candidate's proofs need. -/
theorem trial_divOk : DivOk (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hTrial) where
  ok h := trial_wp h
  ct hP := trial_ct.mono (fun s₁ s₂ hp => by
      obtain ⟨B, Z, w, n, h₁, h₂, hsp, hsy, hdiv⟩ := hP s₁ s₂ hp
      exact ⟨⟨B, s₁.syms TrialTable32.symbol, Z, w, n, s₁.sp, entryDivides (arr s₁.mem B w 0)⟩,
        ⟨h₁, rfl, rfl, fun _ _ => rfl⟩, ⟨h₂, hsy.symm, hsp.symm, fun i hi => (hdiv i hi).symm⟩⟩)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.PPC64LE.Cand.TrialOk
