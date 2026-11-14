module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Abi
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Taint
public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Appendix C.2 by words on i686: the timing's pieces and stages

A piece checked by the taint analysis leaks only the arguments and keeps them public (`PubA`); the
others are loops counted in header words, composed with `loopA` from two runs' invariants. Between
the pieces of `det`, each run is at a stage below (`TW0` … `SR1`), which states only what the next
piece's timing needs: the frame (`KS`), the modulus `n` (public: the contract leaks it, so both runs
have the same `n`), and the values its loops' counts depend on.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys (seqs)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys

/-- Code that leaks only what `τA` makes public, and keeps it public. -/
def PubA (c : Prog isa) : Prop :=
  ∃ hint, (VG.Taint.check sseTaint τA c hint).map (sseTaint.le τA ·) = some true

/-- Two runs agreeing on `τA`, each meeting its own predicate. -/
def RA (P Q : State → Prop) (s t : State) : Prop := VG.X86.Taint.Agree τA s t ∧ P s ∧ Q t

theorem PubA.trace {c : Prog isa} (h : PubA c) {s t : State} (ag : VG.X86.Taint.Agree τA s t)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa c s tr sf) (et : Exec isa c t ur tf) :
    tr = ur ∧ VG.X86.Taint.Agree τA sf tf := by
  obtain ⟨hint, hh⟩ := h
  obtain ⟨τ', hc, hle⟩ := Option.map_eq_some_iff.mp hh
  obtain ⟨e, a⟩ := VG.Taint.check_sound hc ag es et
  exact ⟨e, sseTaint.le_sound hle a⟩

theorem PubA.relCT {c : Prog isa} (h : PubA c) {P Q P' Q' : State → Prop}
    (wl : ∀ s, P s → WP isa c s P') (wr : ∀ t, Q t → WP isa c t Q') :
    RelCT isa (RA P Q) c (RA P' Q') := by
  intro s t tr ur sf tf ⟨ag, hp, hq⟩ es et
  obtain ⟨e, a⟩ := h.trace ag es et
  exact ⟨e, a, wp_result (wl s hp) es, wp_result (wr t hq) et⟩

/-- The same, forgetting the runs' stages. -/
theorem PubA.relCT' {c : Prog isa} (h : PubA c) {P Q : State → Prop} :
    RelCT isa (RA P Q) c (RA (fun _ => True) (fun _ => True)) := by
  intro s t tr ur sf tf ⟨ag, _, _⟩ es et
  obtain ⟨e, a⟩ := h.trace ag es et
  exact ⟨e, a, trivial, trivial⟩

/-- Straight pieces, then `last`: each run from where its first pieces leave it. -/
theorem pubs_relCT {last : Prog isa} {P Q : State → Prop} {R : State → State → Prop}
    (hl : RelCT isa (RA P Q) last R) : ∀ {c : Prog isa} {cs : List (Prog isa)}, PubA c → (∀ d ∈ cs, PubA d) →
    RelCT isa (RA (fun s => WP isa (seqs (c :: cs)) s P) (fun t => WP isa (seqs (c :: cs)) t Q))
      (seqs (c :: cs ++ [last])) R
  | _, [], hc, _ => VG.RelCT.seq (hc.relCT (fun _ h => h) (fun _ h => h)) hl
  | _, d :: _, hc, hcs => VG.RelCT.seq (hc.relCT (fun _ h => WP.seq_iff.mp h) (fun _ h => WP.seq_iff.mp h))
      (pubs_relCT hl (hcs d (List.mem_cons_self ..)) (fun e he => hcs e (List.mem_cons_of_mem _ he)))

/-- A loop counted down from `K`, its body checked, from two runs' invariants. -/
theorem loopA {g : Geo} (pg : PubG g) {body : Prog isa} {K : Nat} (I : Nat → State → Prop) (pos : 0 < K)
    (hb : PubA body) (hI : ∀ k s, I k s → MulPost g s)
    (step : ∀ k s, k < K → I k s → WP isa body s fun v => I (k + 1) v ∧ v.zf = some (decide (K - k - 1 = 0))) :
    RelCT isa (RA (I 0) (I 0)) (.loop body .ne) (RA (I K) (I K)) := by
  have L := fixedLoop_relCT (body := body) (c := K) I I pos
    (fun k _ s t _ _ _ _ ⟨hs, ht⟩ es et => by
      obtain ⟨_, _, _, _, _, _, _, h⟩ := hI k s hs
      obtain ⟨_, _, _, _, _, _, _, j⟩ := hI k t ht
      exact ⟨(hb.trace (ks_agree pg h j) es et).1, trivial⟩)
    (fun k s hk h => WP.mono (step k s hk h) fun v ⟨a, b⟩ => ⟨a, by rw [b, Nat.sub_sub]⟩)
    (fun k s hk h => WP.mono (step k s hk h) fun v ⟨a, b⟩ => ⟨a, by rw [b, Nat.sub_sub]⟩)
  refine L.mono (fun s t h => ⟨h.2.1, h.2.2⟩) fun s t ⟨hs, ht⟩ => ?_
  obtain ⟨_, _, _, _, _, _, _, h⟩ := hI K s hs
  obtain ⟨_, _, _, _, _, _, _, j⟩ := hI K t ht
  exact ⟨ks_agree pg h j, hs, ht⟩

/-! ## The stages between `det`'s pieces

Each run's stage: its frame, the modulus `n` in `[aN]`, and what the next piece's loops count by.
`n` is a parameter, the same for both runs. -/

/-- Before `det`: `n` (narrow) and `d e` (wide), and a wide zero. -/
def D0W (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [VG.Impl.Rsa.X86.Recover.aN] AW [VG.Impl.Rsa.X86.Recover.wM,
    VG.Impl.Rsa.X86.Recover.wZ] V [] s ∧ AW VG.Impl.Rsa.X86.Recover.wZ = 0 ∧ A VG.Impl.Rsa.X86.Recover.aN = n

/-- Before `twos`. -/
def TW0 (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aZ0, aX2, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX] V [sOkDE] s ∧ A aZ0 = 0 ∧
    A VG.Impl.Rsa.X86.RecoverDetRt.aN = n

/-- After `twos`: `u` odd. -/
def TW1 (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aU, aX2, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] s ∧ A aU % 2 = 1 ∧
    A VG.Impl.Rsa.X86.RecoverDetRt.aN = n

/-- Before the GCD (after `gcdSet`): its odd input. -/
def GW0 (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aGm, aGx, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] s ∧ A aGm % 2 = 1 ∧
    A VG.Impl.Rsa.X86.RecoverDetRt.aN = n

/-- After the GCD, before the product. -/
def GW1 (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aG, VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wX3] V [sOkDE] s ∧
    A VG.Impl.Rsa.X86.Keys.aZero = 0 ∧ A VG.Impl.Rsa.X86.RecoverDetRt.aN = n

/-- After the product, before `divA`: the product's extra word zero. -/
def PA1 (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wA] V [sOkDE] s ∧
    A VG.Impl.Rsa.X86.Keys.aZero = 0 ∧ A VG.Impl.Rsa.X86.RecoverDetRt.aN = n ∧
    w32 s.mem g.B (arr g.W wA + 4 * g.W) = 0

/-- After `divA`. -/
def DA1 (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wA, wR, wN] V
    [sLt, sOkDE] s ∧ A VG.Impl.Rsa.X86.Keys.aZero = 0 ∧ A VG.Impl.Rsa.X86.RecoverDetRt.aN = n ∧ AW wN = n

/-- After `divB`. -/
def DB1 (g : Geo) (n : Nat) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aD, aOne1, VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] AW [wN] V
    [sExact, sLt, sOkDE] s ∧ A aOne1 = 1 ∧ A VG.Impl.Rsa.X86.Keys.aZero = 0 ∧
    A VG.Impl.Rsa.X86.RecoverDetRt.aN = n ∧ AW wN = n

/-- After `square`. -/
def SQ1 (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aD, VG.Impl.Rsa.X86.Keys.aZero] AW [wA, wN] V [sExact, sLt, sOkDE] s ∧
    A VG.Impl.Rsa.X86.Keys.aZero = 0

/-- After `minus4n`, before `sqrt`. -/
def M41 (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aD, VG.Impl.Rsa.X86.Keys.aZero] AW [wR] V sqSlotsW s ∧ A VG.Impl.Rsa.X86.Keys.aZero = 0

/-- After `sqrt`, before the factors. -/
def SR1 (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aY, aD, VG.Impl.Rsa.X86.Keys.aZero] AW [] V (sOk5 :: sqSlotsW) s ∧
    A VG.Impl.Rsa.X86.Keys.aZero = 0

end VG.Proof.Rsa.X86.Recover
