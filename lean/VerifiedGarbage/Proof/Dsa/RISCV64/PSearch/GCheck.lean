module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.GStep
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Ctl
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.PrimeCall
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter search on RISC-V: the generator and the check

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/GPart.lean`, `CheckCall.lean` and
`CheckPart.lean`), over the window of the tape from the cursor `u`: its
first `generatorAttempts` candidates' octets, or fewer if the tape is
shorter (`GP.win`). `window_vp`: the window's words. `gPart_vp`: `gStep` on
each candidate of the window, until one gives a g above 1 (`fG` := 1, g at
`sG`) or the window has no candidate left (`fG` := 2), and the candidates
read counted as consumed (`fUsed`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Impl.Rsa.RISCV64.Keys (seqs)

/-! ## The window -/

namespace GP
variable (G : GP)

/-- The window's octets from `u`. -/
abbrev win (u : Nat) : Nat := min (G.randLen - u) (Spec.Dsa.generatorAttempts * G.pLen)

/-- The window's address. -/
abbrev hA (u : Nat) : Addr := G.rand + BitVec.ofNat 64 u

/-- Whether the tape held the whole window. -/
abbrev full (u : Nat) : Nat := if Spec.Dsa.generatorAttempts * G.pLen ≤ G.randLen - u then 1 else 0

/-- The window's bytes. -/
abbrev winB (u : Nat) : List Byte := (G.randB.drop u).take (Spec.Dsa.generatorAttempts * G.pLen)

end GP

theorem varOk_fH {G : GP} : VarOk G fH := varOk_of (by decide)
theorem varOk_fHLeft {G : GP} : VarOk G fHLeft := varOk_of (by decide)
theorem varOk_fHStart {G : GP} : VarOk G fHStart := varOk_of (by decide)
theorem varOk_fFull {G : GP} : VarOk G fFull := varOk_of (by decide)

theorem shl7 {x : Nat} (hx : x < 2 ^ 50) :
    BitVec.ofNat 64 x <<< 7 = BitVec.ofNat 64 (Spec.Dsa.generatorAttempts * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Spec.Dsa.generatorAttempts]
  rw [Nat.mod_eq_of_lt (a := x) (by omega)]
  omega

/-- The window's words, as the code stores them. -/
abbrev wCfg (c : Cfg) (G : GP) (u : Nat) : Cfg :=
  (((c.setV fH (G.hA u)).setV fHStart (G.hA u)).setV fHLeft (BitVec.ofNat 64 (G.win u))).setV fFull
    (BitVec.ofNat 64 (G.full u))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The window from the cursor `u`: its start in `fH` and `fHStart`, its
octets in `fHLeft`, and whether the tape held it whole in `fFull`. -/
theorem window_vp {g : Geo} (hg : g.pLen = G.pLen) {u : Nat} (hu : u ≤ G.randLen) (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G c X) g.window (St G (wCfg c G u) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hp : G.pLen < 2048 := by rcases l with e | e | e <;> rw [e] <;> decide
  unfold Geo.window
  rw [hg]
  refine VP.seq (G := fun σ s => St G ((c.setV fH (G.hA u)).setV fHStart (G.hA u)) X σ s ∧
      s.gpr .t4 = BitVec.ofNat 64 (G.randLen - u) ∧
      s.gpr .t5 = BitVec.ofNat 64 (Spec.Dsa.generatorAttempts * G.pLen))
    (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
        (.block [ld .t2 fWit, ld .t3 fUsed, .add .t2 .t2 .t3, st .t2 fH, st .t2 fHStart, ld .t4 fWitLen,
          .sub .t4 .t4 .t3, .li .t5 G.pLen, .shift .sll .d .t5 .t5 7]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · have wl := h.gi.randLt
    refine h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.rand) (by simp [fixedWords]))
      (t := .t2) (by decide) fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.gi.slotV hU).trans hUv) (t := .t3) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine wp_add fun s₃ u₃ => ?_
    have v3 : s₃.gpr .t2 = G.hA u := by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
    have h₃ := h₂.of_upd u₃ (by decide)
    refine h₃.stF varOk_fH fun s₄ h₄ m₄ => ?_
    refine h₄.stF varOk_fHStart fun s₅ h₅ m₅ => ?_
    rw [m₄.gpr, v3] at h₅
    refine h₅.ldK (o := fWitLen) (by decide) (by decide)
      (h₅.gi.fixedV (v := BitVec.ofNat 64 G.randLen) (by simp [fixedWords])) (t := .t4) (by decide)
      fun s₆ h₆ u₆ => ?_
    refine wp_sub fun s₇ u₇ => ?_
    refine wp_li hp fun s₈ u₈ => ?_
    refine wp_sll (by decide) fun s₉ u₉ => WP.block_nil ⟨⟨?_, x⟩, ?_, ?_⟩
    · exact ((h₆.of_upd u₇ (by decide)).of_upd u₈ (by decide)).of_upd u₉ (by decide)
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide),
        m₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.gpr, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    · rw [u₉.gpr, u₈.gpr, shl7 (by omega)]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_ltu, eval_ltu, h₁.2.1, h₂.2.1, h₁.2.2, h₂.2.2]) ?_ ?_
  · refine VP.pub (SS.pub (c := fun _ => (c.setV fH (G.hA u)).setV fHStart (G.hA u)) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block ([st .t4 fHLeft] ++ stImm fFull 0)),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, t4, t5⟩, e⟩ => ?_
    have wl := h.gi.randLt
    rw [eval_ltu, t4, t5] at e
    simp only [Option.some.injEq, decide_eq_true_eq] at e
    rw [ofNat_lt_iff (by omega) (by simp only [Spec.Dsa.generatorAttempts]; omega)] at e
    simp only [stImm, List.cons_append, List.nil_append]
    refine h.stF varOk_fHLeft fun s₁ h₁ m₁ => wp_li (by decide) fun s₂ u₂ => ?_
    refine (h₁.of_upd u₂ (by decide)).stF varOk_fFull fun s₃ h₃ m₃ => WP.block_nil ⟨?_, x⟩
    rw [u₂.gpr, t4] at h₃
    have ew : G.win u = G.randLen - u := Nat.min_eq_left (by omega)
    have ef : G.full u = 0 := by simp only [GP.full]; split <;> omega
    rw [wCfg, ew, ef]
    exact h₃
  · refine VP.pub (SS.pub (c := fun _ => (c.setV fH (G.hA u)).setV fHStart (G.hA u)) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block ([st .t5 fHLeft] ++ stImm fFull 1)),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, t4, t5⟩, e⟩ => ?_
    have wl := h.gi.randLt
    rw [eval_ltu, t4, t5] at e
    simp only [Option.some.injEq, decide_eq_false_iff_not] at e
    rw [ofNat_lt_iff (by omega) (by simp only [Spec.Dsa.generatorAttempts]; omega)] at e
    simp only [stImm, List.cons_append, List.nil_append]
    refine h.stF varOk_fHLeft fun s₁ h₁ m₁ => wp_li (by decide) fun s₂ u₂ => ?_
    refine (h₁.of_upd u₂ (by decide)).stF varOk_fFull fun s₃ h₃ m₃ => WP.block_nil ⟨?_, x⟩
    rw [u₂.gpr, t5] at h₃
    have ew : G.win u = Spec.Dsa.generatorAttempts * G.pLen := Nat.min_eq_right (by omega)
    have ef : G.full u = 1 := by simp only [GP.full]; split <;> omega
    rw [wCfg, ew, ef]
    exact h₃

end

/-! ## Reordered words -/

/-- Simplifies equalities of header words. -/
syntax "v_eq" : tactic
macro_rules
  | `(tactic| v_eq) => `(tactic| (simp only [Cfg.setV, upd]; (repeat' split) <;> first | rfl |
      (subst_vars; simp_all [fH, fHLeft, fHStart, fFull, fG, fUsed, fStatus])))

/-- A stage's words listed and valued as another's. -/
theorem SS.ofV {G : GP} {STK : Nat} {σ s : State} {c c' : Cfg} (h : SS G STK σ c s)
    (hLS : c'.LS ⊆ c.LS) (hV : ∀ o ∈ c'.LS, c.V o = c'.V o) (hcl : ∀ x ∈ c'.cl, x ∈ c.cl)
    (hl : c'.live = c.live) (hA : c'.A = c.A) (hk : c'.kls = c.kls) (hK : c'.KV = c.KV) : SS G STK σ c' s :=
  h.mono (fun o ho => ⟨hLS ho, hV o ho⟩) hcl (fun j hj => ⟨hl ▸ hj, by rw [hA]⟩)
    (fun d hd => ⟨hk ▸ hd, by rw [hK]⟩)

/-- Simplifies inclusions of the header words listed. -/
syntax "ls_sub" : tactic
macro_rules
  | `(tactic| ls_sub) => `(tactic| simp only [Cfg.setV, List.cons_subset, List.mem_cons, true_or, or_true,
      List.Subset.refl, List.subset_cons_of_subset, and_true])

/-! ## The candidates -/

namespace GP
variable (G : GP)

/-- The persistent words of the search for g: the window's start and
whether the tape held it whole. -/
abbrev bCfg (c : Cfg) (u : Nat) : Cfg := (c.setV fHStart (G.hA u)).setV fFull (BitVec.ofNat 64 (G.full u))

/-- The candidates the window holds. -/
abbrev nW (u : Nat) : Nat := G.win u / G.pLen

/-- The candidate at byte `i` of the window. -/
abbrev hAt (u i : Nat) : List Byte := ((G.winB u).drop i).take G.pLen

/-- The candidates from the `k`-th on. -/
abbrev gList (u k : Nat) : List Nat :=
  (Spec.Dsa.generationChunks G.pLen ((G.winB u).drop (k * G.pLen))).map Spec.Dsa.decodeBE

end GP

/-- Whether the candidate at byte `i` of the window gives a g above 1. -/
abbrev gOk (G : GP) (u pv ev i : Nat) : Prop :=
  1 < Spec.Dsa.decodeBE (G.hAt u i) ∧ Spec.Dsa.decodeBE (G.hAt u i) < pv - 1 ∧
    1 < Spec.Dsa.decodeBE (G.hAt u i) ^ ev % pv

/-- The search's iterations from the `k`-th candidate, with `m` left. -/
def gCount (G : GP) (u pv ev : Nat) : Nat → Nat → Nat
  | 0, k => k + 1
  | m + 1, k => if gOk G u pv ev (k * G.pLen) then k + 1 else gCount G u pv ev m (k + 1)

theorem gCount_gt (G : GP) (u pv ev : Nat) : ∀ m k, k < gCount G u pv ev m k
  | 0, k => by simp [gCount]
  | m + 1, k => by
    simp only [gCount]; split
    · omega
    · exact Nat.lt_of_succ_lt (gCount_gt G u pv ev m (k + 1))

/-- The search's words at the `k`-th candidate. -/
abbrev gCfg (c : Cfg) (G : GP) (u k : Nat) : Cfg :=
  (((G.bCfg c u).setV fH (G.hA u + BitVec.ofNat 64 (k * G.pLen))).setV fHLeft
    (BitVec.ofNat 64 (G.win u - k * G.pLen))).setV fG 4

/-- The stage after the search, from its result and the candidates read. -/
def gFin (c : Cfg) (G : GP) (u : Nat) : Option Nat → Nat → Cfg
  | some g, n => (({ G.bCfg c u with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }).setV fH
      (G.hA u + BitVec.ofNat 64 (n * G.pLen))).setV fG 1
  | none, n => ((G.bCfg c u).setV fH (G.hA u + BitVec.ofNat 64 (n * G.pLen))).setV fG 2

/-- The search with `r` iterations left of `N`. -/
abbrev gInv (c : Cfg) (G : GP) (u pv ev qv N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r ≤ G.nW u ∧ gCount G u pv ev (G.nW u - (N - r)) (N - r) = N ∧
    Spec.Dsa.generator pv qv (G.gList u (N - r)) = Spec.Dsa.generator pv qv (G.gList u 0) ∧
    Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0) =
      (N - r) + Proof.Dsa.Generation.generatorCount pv qv (G.gList u (N - r))) ∧
  St G (gCfg c G u (N - r)) X σ s

/-- What `gStep` needs of the stage the search starts from. -/
structure GReq (G : GP) (c : Cfg) (pv ev : Nat) : Prop where
  hM : aPm1 ∈ c.live
  hMv : c.A aPm1 = pv - 1
  hO : aOne ∈ c.live
  hOv : c.A aOne = 1
  hZ : aZero ∈ c.live
  hZv : c.A aZero = 0
  hHl : aH ∉ c.live
  hTl : aTmp ∉ c.live
  hkls : c.kls = []
  hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl
  hpv : pv < 256 ^ G.pLen
  hp2 : 2 ≤ pv
  hpo : pv % 2 = 1
  hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl
  hev : ev < 256 ^ eBytes G.pLen G.qLen
  hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x ∧ Apart sG G.pLen x
  hfH : fH ∉ c.LS
  hfL : fHLeft ∉ c.LS

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Bytes of the tape, in the entry's memory. -/
theorem rand_slice {σ : State} (hG : mkG σ = G) {j n : Nat} (hj : j + n ≤ G.randLen) :
    Spec.Rsa.bytesAt σ.mem (G.rand + BitVec.ofNat 64 j) n = (G.randB.drop j).take n := by
  have hw : G.randB = Spec.Rsa.bytesAt σ.mem G.rand G.randLen := by rw [← hG]; rfl
  obtain ⟨d, hd⟩ : ∃ d, G.randLen = j + (n + d) := ⟨G.randLen - j - n, by omega⟩
  rw [hw, hd, VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (by simp [Spec.Rsa.bytesAt]), List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The `k`-th candidate, read from the entry's memory: what `gStep` needs. -/
theorem cand_src {σ : State} (hσ : CIn STK0 σ) (hG : mkG σ = G) {u k : Nat} (hp0 : 0 < G.pLen)
    (hk : u + (k + 1) * G.pLen ≤ G.randLen) (hkw : (k + 1) * G.pLen ≤ Spec.Dsa.generatorAttempts * G.pLen) :
    (∀ i < G.pLen, InRegions (σ.rd ++ σ.wr) (VG.Proof.Bignum.off (G.hA u + BitVec.ofNat 64 (k * G.pLen)) i) 1) ∧
      Region.Disjoint ⟨G.hA u + BitVec.ofNat 64 (k * G.pLen), G.pLen⟩ G.rScr ∧
      Region.Disjoint ⟨G.hA u + BitVec.ofNat 64 (k * G.pLen), G.pLen⟩ (rBelow σ STK0) ∧
      (G.hA u + BitVec.ofNat 64 (k * G.pLen)).toNat + G.pLen ≤ 2 ^ 64 ∧
      Spec.Rsa.bytesAt σ.mem (G.hA u + BitVec.ofNat 64 (k * G.pLen)) G.pLen = G.hAt u (k * G.pLen) := by
  have fit : G.rand.toNat + G.randLen ≤ 2 ^ 64 := by have := hσ.nR; rw [← hG]; exact this
  have rl : G.randLen < 2 ^ 64 := by rw [← hG]; exact (σ.gpr .a4).isLt
  have eA : G.hA u + BitVec.ofNat 64 (k * G.pLen) = G.rand + BitVec.ofNat 64 (u + k * G.pLen) := by
    rw [GP.hA, BitVec.add_assoc, BitVec.ofNat_add]
  have e1 : (k + 1) * G.pLen = k * G.pLen + G.pLen := Nat.succ_mul _ _
  rw [eA]
  have sub : Region.Sub ⟨G.rand + BitVec.ofNat 64 (u + k * G.pLen), G.pLen⟩ G.rRand :=
    Offset.sub_base _ (by omega)
  have rC := hσ.rC; rw [hG] at rC
  have bR := hσ.bR; rw [hG] at bR
  refine ⟨fun i hi => ⟨G.rRand, ?_, ?_⟩, rC.sub_left sub, bR.symm.sub_left sub, ?_, ?_⟩
  · rw [hσ.rd, hG]; simp
  · rw [VG.Proof.Bignum.off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u + k * G.pLen) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [rand_slice hG (by omega), GP.hAt, GP.winB, List.drop_take, List.drop_drop, List.take_take]
    congr 1
    omega

/-- The next candidate: `fH` := `fH` + `pLen`, `fHLeft` := `fHLeft` − `pLen`. -/
theorem adv_vp {d : Cfg} (hH : fH ∈ d.LS) (hL : fHLeft ∈ d.LS) (hp : G.pLen < 2048) :
    VP (St G d X) (.block [ld .t2 fH, .addi .t2 .t2 G.pLen, st .t2 fH, ld .t2 fHLeft,
        .addi .t2 .t2 (-(G.pLen : Int)), st .t2 fHLeft])
      (St G ((d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)).setV fHLeft (d.V fHLeft - BitVec.ofNat 64 G.pLen)) X) := by
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t2 fH, .addi .t2 .t2 G.pLen,
      st .t2 fH, ld .t2 fHLeft, .addi .t2 .t2 (-(G.pLen : Int)), st .t2 fHLeft]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fH) (by decide) (by decide) (h.gi.slotV hH) (t := .t2) (by decide) fun s₁ h₁ u₁ => ?_
  refine wp_addi hp fun s₂ u₂ => ?_
  refine (h₁.of_upd u₂ (by decide)).stF varOk_fH fun s₃ h₃ m₃ => ?_
  rw [u₂.gpr, u₁.gpr] at h₃
  refine h₃.ldK (o := fHLeft) (v := d.V fHLeft) (by decide) (by decide)
    ((h₃.gi.slotV (List.mem_cons_of_mem _ hL)).trans (by simp [upd, fH, fHLeft])) (t := .t2) (by decide)
    fun s₄ h₄ u₄ => ?_
  refine wp_subi (by omega) fun s₅ u₅ => ?_
  refine (h₄.of_upd u₅ (by decide)).stF varOk_fHLeft fun s₆ h₆ _ => WP.block_nil ⟨?_, x⟩
  rw [u₅.gpr, u₄.gpr] at h₆
  exact h₆

end

/-! ## The search for g -/

/-- A piece from a stage with a fact both runs share. -/
theorem VP.ofPure {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

/-- The stage's call, with the facts of its entry the candidates' reads need. -/
abbrev XE (G : GP) (X : State → Prop) (σ : State) : Prop := X σ ∧ CIn STK0 σ ∧ mkG σ = G

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem winB_length {u : Nat} (hRL : G.randB.length = G.randLen) : (G.winB u).length = G.win u := by
  simp only [GP.winB, GP.win, List.length_take, List.length_drop, hRL]
  exact Nat.min_comm _ _

theorem gBody_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {u pv ev qv N : Nat} (R : GReq G c pv ev) (hu : u ≤ G.randLen) (hRL : G.randB.length = G.randLen)
    (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G u pv ev qv N X (r + 1)) (seqs [.block [ld .t2 fHLeft, .li .t3 g.pLen],
        .ite (.ltu .t2 .t3) (.block (stImm fG 2))
          (seqs [g.gStep, .block [ld .t2 fH, .addi .t2 .t2 g.pLen, st .t2 fH, ld .t2 fHLeft,
            .addi .t2 .t2 (-(g.pLen : Int)), st .t2 fHLeft]]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval (.zero .t2) s = some (decide (0 < r)) ∧
        (r = 0 → St G (gFin c G u (Spec.Dsa.generator pv qv (G.gList u 0))
          (Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0))) X σ s) ∧
        (0 < r → gInv c G u pv ev qv N X r σ s)) := by
  refine VP.ofPure fun ⟨hr, hk, hc, hres, hcnt⟩ => ?_
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hp : G.pLen < 2048 := by rcases l with e | e | e <;> rw [e] <;> decide
  have hpL : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have hfL := R.hfL
  have hfH := R.hfH
  have hWl := winB_length (u := u) hRL
  generalize hMM : G.nW u = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres hcnt ⊢
  have kL : ∀ j, j ≤ M → j * G.pLen ≤ G.win u := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  have hWr : G.win u ≤ Spec.Dsa.generatorAttempts * G.pLen := Nat.min_le_right _ _
  have hW64 : G.win u < 2 ^ 64 := by simp only [Spec.Dsa.generatorAttempts] at hWr; omega
  have hWu : G.win u + u ≤ G.randLen := by
    have := Nat.min_le_left (G.randLen - u) (Spec.Dsa.generatorAttempts * G.pLen); simp only [GP.win]; omega
  rw [hg]
  -- Whether a candidate is left.
  refine VP.seq (G := fun σ s => St G (gCfg c G u k) X σ s ∧
      s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen)
    (VP.pub (SS.pub (c := fun _ => gCfg c G u k) fun σ s h => h.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t2 fHLeft, .li .t3 G.pLen]),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ =>
      h.ldK (o := fHLeft) (v := BitVec.ofNat 64 (G.win u - k * G.pLen)) (by decide) (by decide)
        ((h.gi.slotV (by simp)).trans (by simp [upd, fHLeft, fG])) (t := .t2) (by decide)
        fun s₁ h₁ u₁ => wp_li hp fun s₂ u₂ => WP.block_nil
          ⟨⟨h₁.of_upd u₂ (by decide), x⟩, by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩) ?_
  have hcnd : ∀ σ₁ σ₂ s₁ s₂, (fun σ s => St G (gCfg c G u k) X σ s ∧
      s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen) σ₁ s₁ →
      (fun σ s => St G (gCfg c G u k) X σ s ∧
      s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen) σ₂ s₂ →
      isa.eval (.ltu .t2 .t3) s₁ = isa.eval (.ltu .t2 .t3) s₂ :=
    fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_ltu, eval_ltu, h₁.2.1, h₂.2.1, h₁.2.2, h₂.2.2]
  have evc : ∀ s : State, s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) →
      s.gpr .t3 = BitVec.ofNat 64 G.pLen →
      isa.eval (.ltu .t2 .t3) s = some (decide (G.win u - k * G.pLen < G.pLen)) := fun s a b => by
    rw [eval_ltu, a, b]
    simp only [Option.some.injEq]
    exact decide_eq_decide.mpr (ofNat_lt_iff (by omega) (by omega))
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- A candidate: `gStep`, then the next.
    have hi : (k + 1) * G.pLen ≤ G.win u := kL (k + 1) hkM
    have hi' : k * G.pLen + G.pLen ≤ G.win u := by rw [Nat.succ_mul] at hi; exact hi
    have notLeft : ∀ σ s, ¬((St G (gCfg c G u k) X σ s ∧
        s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen) ∧
        isa.eval (.ltu .t2 .t3) s = some true) := fun σ s ⟨⟨_, a, b⟩, z⟩ => by
      rw [evc s a b] at z; simp only [Option.some.injEq, decide_eq_true_eq] at z; omega
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega⟩
    rw [hm] at hc; simp only [gCount] at hc
    have hlen : G.pLen ≤ ((G.winB u).drop (k * G.pLen)).length := by
      rw [List.length_drop, hWl]; omega
    have hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL hlen
    have hcs := VG.Proof.Dsa.Generation.generatorCount_chunks_step (p := pv) (q := qv) hpL hlen
    simp only [VG.Proof.Dsa.powMod_eq, ← hev', List.drop_drop] at hstep hcs
    have eD : k * G.pLen + G.pLen = (k + 1) * G.pLen := (Nat.succ_mul _ _).symm
    rw [eD] at hstep hcs
    have stepVP := gStep_vp (c := gCfg c G u k) (X := XE G X) (H := G.hA u + BitVec.ofNat 64 (k * G.pLen))
      (hb := G.hAt u (k * G.pLen)) hg hgq cert R.hM R.hMv R.hO R.hOv R.hZ R.hZv R.hHl R.hTl R.hkls R.hPc R.hpv
      R.hp2 R.hpo R.hEc R.hev R.hcl (by simp) (by simp [upd, fH, fHLeft, fG])
      (fun σ ⟨_, hσ, hG⟩ => cand_src hσ hG hpL (by omega) (by omega))
    by_cases hok : gOk G u pv ev (k * G.pLen)
    · -- It gives g: done.
      have r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega
      subst r0
      have some0 : Spec.Dsa.generator pv qv (G.gList u 0) =
          some (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen)) ^ ev % pv) := by
        rw [← hres, GP.gList, hstep]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      have cnt0 : Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0) = k + 1 := by
        rw [hcnt, GP.gList, hcs, ite_eq_left_of_eq_true _ _ (eq_true hok)]
      have hG1 : gOut (gCfg c G u k) G (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen))) pv ev =
          ({ gCfg c G u k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G u k).cl }).setV fG 1 := by
        rw [gOut, ite_eq_left_of_eq_true _ _ (eq_true hok)]
      rw [hG1] at stepVP
      refine VP.seq (VP.ite hcnd (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => ⟨h.1.1.1, h.1.1.2, h.1.1.1.gi.pre, h.1.1.1.gi.hG⟩)
          fun σ s h => ⟨h.1, h.2.1⟩) (adv_vp (by simp) (by simp) hp))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [some0, cnt0]
      have eH : G.hA u + BitVec.ofNat 64 (k * G.pLen) + BitVec.ofNat 64 G.pLen =
          G.hA u + BitVec.ofNat 64 ((k + 1) * G.pLen) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, eD]
      have e1 : ((({ gCfg c G u k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G u k).cl }).setV fG 1).V fH) = G.hA u + BitVec.ofNat 64 (k * G.pLen) := by
        simp [upd, fH, fHLeft, fG]
      rw [e1, eH] at h'
      refine h'.ofV (by simp only [gFin]; ls_sub) (fun o ho => ?_) (fun y hy => hy) rfl rfl rfl rfl
      simp only [gFin, Cfg.setV, List.mem_cons] at ho ⊢
      v_eq
    · -- It does not: the next candidate.
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)] at hc
      have rpos : 0 < r := by have := gCount_gt G u pv ev m (k + 1); omega
      have hNr : N - r = k + 1 := by omega
      have hG1 : gOut (gCfg c G u k) G (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen))) pv ev = gCfg c G u k := by
        rw [gOut, ite_eq_right_of_eq_false _ _ (eq_false hok)]
      rw [hG1] at stepVP
      refine VP.seq (VP.ite hcnd (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => ⟨h.1.1.1, h.1.1.2, h.1.1.1.gi.pre, h.1.1.1.gi.hG⟩)
          fun σ s h => ⟨h.1, h.2.1⟩) (adv_vp (by simp) (by simp) hp))) ?_
      have eH : G.hA u + BitVec.ofNat 64 (k * G.pLen) + BitVec.ofNat 64 G.pLen =
          G.hA u + BitVec.ofNat 64 ((k + 1) * G.pLen) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, eD]
      have eL : BitVec.ofNat 64 (G.win u - k * G.pLen) - BitVec.ofNat 64 G.pLen =
          BitVec.ofNat 64 (G.win u - (k + 1) * G.pLen) := by
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), ← eD, Nat.sub_add_eq]
      have e1 : (gCfg c G u k).V fH = G.hA u + BitVec.ofNat 64 (k * G.pLen) := by simp [upd, fH, fHLeft, fG]
      have e2 : (gCfg c G u k).V fHLeft = BitVec.ofNat 64 (G.win u - k * G.pLen) := by
        simp [upd, fHLeft, fG]
      refine cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega, by omega, by rw [hMM, show M - (k + 1) = m by omega]; exact hc, ?_, ?_⟩, ?_, x⟩
      · rw [← hres, GP.gList, GP.gList, hstep, ite_eq_right_of_eq_false _ _ (eq_false hok)]
      · rw [hcnt, GP.gList, GP.gList, hcs, ite_eq_right_of_eq_false _ _ (eq_false hok)]; omega
      · rw [e1, e2, eH, eL] at h'
        refine h'.ofV (by ls_sub) (fun o ho => ?_) (fun y hy => hy) rfl rfl rfl rfl
        simp only [List.mem_cons] at ho
        v_eq
  · -- The window is done: `fG` := 2.
    have hkM' : k = M := by omega
    subst hkM'
    have r0 : r = 0 := by simp only [Nat.sub_self, gCount] at hc; omega
    subst r0
    have hz : G.win u - k * G.pLen < G.pLen := by
      have h1 := Nat.lt_mul_div_succ (G.win u) hpL
      rw [show G.win u / G.pLen = k from hMM, Nat.mul_succ, Nat.mul_comm] at h1
      omega
    have hdone : ((G.winB u).drop (k * G.pLen)).length < G.pLen := by rw [List.length_drop, hWl]; exact hz
    have none0 : Spec.Dsa.generator pv qv (G.gList u 0) = none := by
      rw [← hres, GP.gList, VG.Proof.Dsa.Generation.generationChunks_done hdone]; rfl
    have cnt0 : Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0) = k := by
      rw [hcnt, GP.gList, VG.Proof.Dsa.Generation.generatorCount_chunks_done hdone, Nat.add_zero]
    refine VP.seq (G := St G ((gCfg c G u k).setV fG (BitVec.ofNat 64 2)) X) (VP.ite hcnd
      (stImm_vp (c := fun _ => gCfg c G u k) (o := fG) (v := 2) (fun σ s h => h.1.1.1) (by decide)
        varOk_fG fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, a, b⟩, z⟩ => by
        rw [evc s a b] at z; simp only [Option.some.injEq, decide_eq_false_iff_not] at z; omega)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G u k).setV fG (BitVec.ofNat 64 2)) (x := BitVec.ofNat 64 2)
      (fun σ s h => h.1) (by decide) (by decide) (by decide) (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    rw [none0, cnt0]
    refine h'.ofV (by simp only [gFin]; ls_sub) (fun o ho => ?_) (fun y hy => hy) rfl rfl rfl rfl
    simp only [gFin, Cfg.setV, List.mem_cons] at ho ⊢
    v_eq

end

end VG.Proof.Dsa.RISCV64.PSearch
