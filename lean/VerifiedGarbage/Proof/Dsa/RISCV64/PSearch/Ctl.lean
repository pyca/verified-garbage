module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Bytes
public import VerifiedGarbage.Proof.Dsa.Generation.RefillTraj
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter search on RISC-V: the controller

The controller runs seeds over the tape from the cursor (`fUsed`) with the
seeds left (`fLeft`), one iteration at a position `p = (k, c)` of the spec's
trajectory (`Proof/Dsa/Generation/RefillTraj.lean`). `iteration_vp`: from a
stage at `p` (`ctlCfg`), an iteration ends at the stage `midCfg p`: the next
position's if the seed was rejected, otherwise the words `finish` reads (the
status `stAt p`, the seed's start, the seeds left, and for parameters the
cursor and the packed parameters). The seed itself is the hypothesis
`AttemptOk`, from `seedCfg p` to `attCfg p (attemptAt …)`. `search_vp`: the
loop, from the start (`pos 0`) to the stage of its last iteration.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.Dsa.Generation (attemptAt iters step pos resAt stAt)

/-- An attempt's status: 0 if the tape ran out, 2 if rejected, 1 for parameters. -/
def stRes : Option (Option Spec.Dsa.Params × List Byte) → Nat
  | none => 0
  | some (none, _) => 2
  | some (some _, _) => 1

section
variable (G : GP) (cl0 : Claims)

/-- The controller's words at a position: the seeds left and the cursor. -/
def ctlCfg (p : Nat × Nat) : Cfg where
  V o := if o = fLeft then BitVec.ofNat 64 p.1 else if o = fUsed then BitVec.ofNat 64 p.2 else 0
  LS := [fLeft, fUsed]
  cl := cl0

/-- The words at the end of an iteration: its status, the seeds left, the
seed's start and, for parameters or a rejected seed, the cursor; the claims
and `extra`. -/
def endCfg (st k c u : Nat) (extra : Claims) : Cfg where
  V o := if o = fStatus then BitVec.ofNat 64 st else if o = fLeft then BitVec.ofNat 64 k
    else if o = fStart then BitVec.ofNat 64 c else if o = fUsed then BitVec.ofNat 64 u else 0
  LS := if st = 1 ∨ st = 2 then [fStatus, fLeft, fStart, fUsed] else [fStatus, fLeft, fStart]
  cl := cl0 ++ extra

/-- After the iteration's first block: the seed's start. -/
abbrev b1Cfg (p : Nat × Nat) : Cfg := (ctlCfg cl0 p).setV fStart (BitVec.ofNat 64 p.2)

/-- A seed's words: its start and address, the cursor past it, status 2. -/
abbrev seedCfg (p : Nat × Nat) : Cfg :=
  (((b1Cfg cl0 p).setV fSeed (G.rand + BitVec.ofNat 64 p.2)).setV fUsed
    (BitVec.ofNat 64 (p.2 + G.qLen))).setV fStatus (BitVec.ofNat 64 2)

/-- After a seed with the result `res`. -/
def attCfg (p : Nat × Nat) : Option (Option Spec.Dsa.Params × List Byte) → Cfg
  | none => endCfg cl0 0 p.1 p.2 0 []
  | some (none, r) => endCfg cl0 2 p.1 p.2 (G.randLen - r.length) []
  | some (some a, r) =>
    endCfg cl0 1 p.1 p.2 (G.randLen - r.length) [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)]

/-- The words at the end of an iteration at `p`, but its status. -/
def midBase (p : Nat × Nat) : Cfg :=
  if stAt G.pLen G.randB p = 2 then ctlCfg cl0 (step G.pLen G.randB p) else
  match p.1 with
  | 0 => endCfg cl0 3 0 p.2 0 []
  | _ + 1 =>
    if G.randB.length - p.2 < G.qLen then endCfg cl0 0 p.1 p.2 0 []
    else attCfg G cl0 p (attemptAt G.pLen G.randB p.2)

/-- The words at the end of an iteration at `p`, its status among them. -/
abbrev midCfg (p : Nat × Nat) : Cfg := (midBase G cl0 p).setV fStatus (BitVec.ofNat 64 (stAt G.pLen G.randB p))

/-- The seed's code from a seed's words, for every position with a seed. -/
def AttemptOk (X : State → Prop) (att : Prog isa) : Prop :=
  ∀ p : Nat × Nat, 0 < p.1 → p.2 + G.qLen ≤ G.randLen →
    VP (St G (seedCfg G cl0 p) X) att (St G (attCfg G cl0 p (attemptAt G.pLen G.randB p.2)) X)

end

/-! ## The words -/

theorem varOk_of {G : GP} {o : Nat}
    (h : o + 8 ≤ fSave ∧ o % 8 = 0 ∧ o ≠ fRA ∧ o ∉ [fOut, fWit, fWitLen, fUsedArg, fState, fScrLen]) :
    VarOk G o := by
  obtain ⟨a, b, c, d⟩ := h
  refine ⟨a, b, c, fun p hp => ?_⟩
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp d
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega)

theorem varOk_fStart {G : GP} : VarOk G fStart := varOk_of (by decide)
theorem varOk_fSeed {G : GP} : VarOk G fSeed := varOk_of (by decide)
theorem varOk_fUsed {G : GP} : VarOk G fUsed := varOk_of (by decide)
theorem varOk_fStatus {G : GP} : VarOk G fStatus := varOk_of (by decide)
theorem varOk_fLeft {G : GP} : VarOk G fLeft := varOk_of (by decide)

theorem ofNat_lt_ofNat {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x < BitVec.ofNat 64 y) = (x < y) := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem ofNat_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this)
    rw [beq_false_of_ne this]; simp [h]

/-- Fewer words and claims, no arrays or slots. -/
theorem SS.mono' {G : GP} {STK : Nat} {σ s : State} {c c' : Cfg} (h : SS G STK σ c s)
    (hV : ∀ o ∈ c'.LS, o ∈ c.LS ∧ c.V o = c'.V o) (hcl : ∀ x ∈ c'.cl, x ∈ c.cl)
    (hl : c'.live = [] := by rfl) (hk : c'.kls = [] := by rfl) : SS G STK σ c' s :=
  h.mono hV hcl (fun j hj => by rw [hl] at hj; cases hj) (fun d hd => by rw [hk] at hd; cases hd)

section
variable {G : GP} {cl0 : Claims} {X : State → Prop}

/-- The iteration's first block: the seed's start := the cursor, into `t2`,
and the seeds left into `t3`. -/
theorem b1_vp (p : Nat × Nat) :
    VP (St G (ctlCfg cl0 p) X) (.block [ld .t2 fUsed, st .t2 fStart, ld .t3 fLeft])
      (fun σ s => St G (b1Cfg cl0 p) X σ s ∧ s.gpr .t2 = BitVec.ofNat 64 p.2 ∧ s.gpr .t3 = BitVec.ofNat 64 p.1) := by
  refine VP.pub (G := G) (SS.pub (c := fun _ => ctlCfg cl0 p) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t2 fUsed, st .t2 fStart, ld .t3 fLeft]),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fUsed) (by decide) (by decide) (h.gi.slotV (by simp [ctlCfg])) (t := .t2) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine h₁.stF varOk_fStart fun s₂ h₂ m₂ => ?_
  rw [u₁.gpr] at h₂
  refine h₂.ldK (o := fLeft) (by decide) (by decide) (h₂.gi.slotV (by simp [ctlCfg])) (t := .t3) (by decide)
    fun s₃ h₃ u₃ => WP.block_nil ⟨⟨h₃, x⟩, ?_, ?_⟩
  · rw [u₃.other _ (by decide), m₂.gpr, u₁.gpr]; simp [ctlCfg, fUsed, fLeft]
  · rw [u₃.gpr]; simp [upd, ctlCfg, fStart, fLeft]

end

section
variable {G : GP} {cl0 : Claims} {X : State → Prop}

/-- The second block: the octets left from the cursor into `t3`, `q_len` into `t4`. -/
theorem b2_vp (p : Nat × Nat) {q : Nat} (hq : q < 2048) (hp2 : p.2 ≤ G.randLen) {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → St G (b1Cfg cl0 p) X σ s ∧ s.gpr .t2 = BitVec.ofNat 64 p.2) :
    VP F (.block [ld .t3 fWitLen, .sub .t3 .t3 .t2, .li .t4 q])
      (fun σ s => St G (b1Cfg cl0 p) X σ s ∧ s.gpr .t2 = BitVec.ofNat 64 p.2 ∧
        s.gpr .t3 = BitVec.ofNat 64 (G.randLen - p.2) ∧ s.gpr .t4 = BitVec.ofNat 64 q) := by
  refine VP.pub (G := G) (SS.pub (c := fun _ => b1Cfg cl0 p) fun σ s h => (hF σ s h).1.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t3 fWitLen, .sub .t3 .t3 .t2, .li .t4 q]),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  obtain ⟨⟨h, x⟩, t2⟩ := hF σ s hs
  refine h.ldK (o := fWitLen) (by decide) (by decide) (h.gi.fixedV (v := BitVec.ofNat 64 G.randLen) (by simp [fixedWords])) (t := .t3) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine wp_sub fun s₂ u₂ => ?_
  refine wp_li hq fun s₃ u₃ => WP.block_nil ⟨⟨(h₁.of_upd u₂ (by decide)).of_upd u₃ (by decide), x⟩, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), t2]
  · have hl : G.randLen < 2 ^ 64 := by
      have := h.gi.pre.nR
      have e : G.randLen = (σ.gpr .a4).toNat := by rw [← h.gi.hG]; rfl
      omega
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), t2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (by omega)]; exact hp2)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (show p.2 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show G.randLen - p.2 < 2 ^ 64 by omega)]
  · rw [u₃.gpr]

/-- The seed's words: its address, the cursor past it, and status 2. -/
theorem b4_vp (p : Nat × Nat) {q : Nat} (hq : q < 2048) (hqq : q = G.qLen) {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → St G (b1Cfg cl0 p) X σ s ∧ s.gpr .t2 = BitVec.ofNat 64 p.2) :
    VP F (.block ([ld .t3 fWit, .add .t3 .t3 .t2, st .t3 fSeed, .addi .t2 .t2 q, st .t2 fUsed] ++ stImm fStatus 2))
      (St G (seedCfg G cl0 p) X) := by
  refine VP.pub (G := G) (SS.pub (c := fun _ => b1Cfg cl0 p) fun σ s h => (hF σ s h).1.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block ([ld .t3 fWit, .add .t3 .t3 .t2, st .t3 fSeed, .addi .t2 .t2 q, st .t2 fUsed] ++ stImm fStatus 2)),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  obtain ⟨⟨h, x⟩, t2⟩ := hF σ s hs
  simp only [stImm, List.cons_append, List.nil_append]
  refine h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.rand) (by simp [fixedWords])) (t := .t3) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  refine (h₁.of_upd u₂ (by decide)).stF varOk_fSeed fun s₃ h₃ m₃ => ?_
  refine wp_addi hq fun s₄ u₄ => ?_
  refine (h₃.of_upd u₄ (by decide)).stF varOk_fUsed fun s₅ h₅ m₅ => ?_
  refine wp_li (by decide) fun s₆ u₆ => ?_
  refine (h₅.of_upd u₆ (by decide)).stF varOk_fStatus fun s₇ h₇ m₇ => WP.block_nil ⟨?_, x⟩
  have v3 : s₂.gpr .t3 = G.rand + BitVec.ofNat 64 p.2 := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), t2]
  have v2 : s₄.gpr .t2 = BitVec.ofNat 64 (p.2 + G.qLen) := by
    rw [u₄.gpr, m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), t2, ← hqq, BitVec.ofNat_add]
  rw [v3, v2, u₆.gpr] at h₇
  exact h₇

end

/-! ## The iteration's cases -/

section
variable {G : GP} {cl0 : Claims} {X : State → Prop}

theorem mid_zero (c : Nat) : midCfg G cl0 (0, c) = (endCfg cl0 3 0 c 0 []).setV fStatus (BitVec.ofNat 64 3) := by
  simp [midCfg, midBase, stAt]

theorem mid_short {k c : Nat} (hs : G.randB.length - c < G.qLen) :
    midCfg G cl0 (k + 1, c) = (endCfg cl0 0 (k + 1) c 0 []).setV fStatus (BitVec.ofNat 64 0) := by
  simp [midCfg, midBase, stAt, hs]

theorem mid_att {k c : Nat} (hs : ¬ G.randB.length - c < G.qLen) :
    midCfg G cl0 (k + 1, c) =
      (match attemptAt G.pLen G.randB c with
        | some (none, r) => ctlCfg cl0 (k, G.randB.length - r.length)
        | res => attCfg G cl0 (k + 1, c) res).setV fStatus
        (BitVec.ofNat 64 (stRes (attemptAt G.pLen G.randB c))) := by
  simp only [midCfg, midBase, stAt, hs, ↓reduceIte]
  rcases e : attemptAt G.pLen G.randB c with _ | ⟨_ | a, r⟩ <;> simp [stRes, step, hs, e]

theorem attCfg_status (p : Nat × Nat) (res : Option (Option Spec.Dsa.Params × List Byte)) :
    fStatus ∈ (attCfg G cl0 p res).LS ∧ (attCfg G cl0 p res).V fStatus = BitVec.ofNat 64 (stRes res) := by
  rcases res with _ | ⟨_ | a, r⟩ <;> simp [attCfg, endCfg, stRes]

/-- No seeds left: status 3. -/
theorem z3_vp {c : Nat} {F : State → State → Prop} (hF : ∀ σ s, F σ s → St G (b1Cfg cl0 (0, c)) X σ s) :
    VP F (.block (stImm fStatus 3)) (St G (midCfg G cl0 (0, c)) X) :=
  stImm_vp (c := fun _ => b1Cfg cl0 (0, c)) (fun σ s h => (hF σ s h).1) (by decide) varOk_fStatus
    fun σ s t hs h _ => ⟨by
      rw [mid_zero]
      exact h.mono' (by simp [endCfg, ctlCfg, upd, fStatus, fLeft, fStart, fUsed])
        (by simp [endCfg, ctlCfg]), (hF σ s hs).2⟩

/-- A tape too short for the next seed: status 0. -/
theorem short_vp {k c : Nat} (hs : G.randB.length - c < G.qLen) {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → St G (b1Cfg cl0 (k + 1, c)) X σ s) :
    VP F (.block (stImm fStatus 0)) (St G (midCfg G cl0 (k + 1, c)) X) :=
  stImm_vp (c := fun _ => b1Cfg cl0 (k + 1, c)) (fun σ s h => (hF σ s h).1) (by decide) varOk_fStatus
    fun σ s t hs' h _ => ⟨by
      rw [mid_short hs]
      exact h.mono' (by simp [endCfg, ctlCfg, upd, fStatus, fLeft, fStart, fUsed])
        (by simp [endCfg, ctlCfg]), (hF σ s hs').2⟩

/-- The rejected seed's count. -/
theorem dec_vp {k c : Nat} {r : List Byte} (hRL : G.randB.length = G.randLen)
    {F : State → State → Prop} (hF : ∀ σ s, F σ s → St G (attCfg G cl0 (k + 1, c) (some (none, r))) X σ s) :
    VP F (.block [ld .t2 fLeft, .addi .t2 .t2 (-1), st .t2 fLeft])
      (St G ((ctlCfg cl0 (k, G.randB.length - r.length)).setV fStatus (BitVec.ofNat 64 2)) X) := by
  refine VP.pub (G := G) (SS.pub (c := fun _ => attCfg G cl0 (k + 1, c) (some (none, r))) fun σ s h => (hF σ s h).1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t2 fLeft, .addi .t2 .t2 (-1), st .t2 fLeft]),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  obtain ⟨h, x⟩ := hF σ s hs
  refine h.ldK (o := fLeft) (by decide) (by decide) (h.gi.slotV (by simp [attCfg, endCfg])) (t := .t2) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine wp_subi (imm := 1) (by decide) fun s₂ u₂ => ?_
  refine (h₁.of_upd u₂ (by decide)).stF varOk_fLeft fun s₃ h₃ _ => WP.block_nil ⟨?_, x⟩
  have v : s₂.gpr .t2 = BitVec.ofNat 64 k := by
    rw [u₂.gpr, u₁.gpr]; simp only [attCfg, endCfg]
    simp [fLeft, fStatus]
    rw [show k + 1 = k + 1 from rfl, BitVec.ofNat_add, BitVec.add_sub_cancel]
  rw [v] at h₃
  exact h₃.mono' (by simp [endCfg, attCfg, ctlCfg, upd, fStatus, fLeft, fStart, fUsed, hRL])
    (by simp [endCfg, attCfg, ctlCfg])

end

/-! ## One iteration -/

section
variable {G : GP} {cl0 : Claims} {X : State → Prop}

theorem ofNat_lt_iff {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x < BitVec.ofNat 64 y ↔ x < y := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem ofNat_beq_zero_false {x : Nat} (h0 : 0 < x) (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = false := by
  have := ofNat_beq (x := x) (y := 0) hx (by decide)
  rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0 from rfl] at this
  rw [this]; simp; omega

theorem eval_ltu (s : State) (a b : Reg) : isa.eval (.ltu a b) s = some (decide (s.gpr a < s.gpr b)) := rfl

theorem stRes_lt (res : Option (Option Spec.Dsa.Params × List Byte)) : stRes res < 3 := by
  rcases res with _ | ⟨_ | _, _⟩ <;> simp [stRes]

theorem iteration_vp (g : Geo) (hgq : g.qLen = G.qLen) (hq : G.qLen < 2048)
    (hatt : AttemptOk G cl0 X g.attempt) (k c : Nat) (hk : k < 2 ^ 63) (hc : c ≤ G.randLen)
    (hRL : G.randB.length = G.randLen) (hR64 : G.randLen < 2 ^ 64) :
    VP (St G (ctlCfg cl0 (k, c)) X) g.iteration (fun σ s => St G (midCfg G cl0 (k, c)) X σ s ∧
      isa.eval (.zero .t2) s = some (BitVec.ofNat 64 (stAt G.pLen G.randB (k, c)) == BitVec.ofNat 64 2)) := by
  simp only [Geo.iteration, Impl.Rsa.RISCV64.Keys.seqs]
  refine VP.seq (b1_vp (k, c)) (VP.seq (G := St G (midCfg G cl0 (k, c)) X) ?_ ?_)
  · refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2, h₂.2.2]) ?_ ?_
    · cases k with
      | zero => exact z3_vp fun σ s h => h.1.1
      | succ k =>
        refine VP.of_false fun σ s ⟨⟨_, _, t3⟩, e⟩ => ?_
        rw [eval_zero, t3, ofNat_beq_zero_false (by simp) (by simp only; omega)] at e
        simp at e
    · cases k with
      | zero =>
        refine VP.of_false fun σ s ⟨⟨_, _, t3⟩, e⟩ => ?_
        rw [eval_zero, t3] at e
        simp at e
      | succ k =>
        refine VP.seq (b2_vp (k + 1, c) (q := g.qLen) (by omega) hc fun σ s h => ⟨h.1.1, h.1.2.1⟩) ?_
        refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_ltu, eval_ltu, h₁.2.2.1, h₂.2.2.1, h₁.2.2.2, h₂.2.2.2]) ?_ ?_
        · by_cases hs : G.randB.length - c < G.qLen
          · exact short_vp hs fun σ s h => h.1.1
          · refine VP.of_false fun σ s ⟨⟨_, _, t3, t4⟩, e⟩ => ?_
            rw [eval_ltu, t3, t4] at e
            simp only [Option.some.injEq, decide_eq_true_eq] at e
            rw [ofNat_lt_iff (by show G.randLen - c < 2 ^ 64; omega) (by omega)] at e
            exact hs (by rw [hRL, ← hgq]; exact e)
        · by_cases hs : G.randB.length - c < G.qLen
          · refine VP.of_false fun σ s ⟨⟨_, _, t3, t4⟩, e⟩ => ?_
            rw [eval_ltu, t3, t4] at e
            simp only [Option.some.injEq, decide_eq_false_iff_not] at e
            rw [ofNat_lt_iff (by show G.randLen - c < 2 ^ 64; omega) (by omega)] at e
            exact e (by rw [← hRL, hgq]; exact hs)
          · refine VP.seq (b4_vp (k + 1, c) (q := g.qLen) (by omega) hgq fun σ s h => ⟨h.1.1, h.1.2.1⟩) ?_
            have H := hatt (k + 1, c) (by omega) (by rw [← hRL]; omega)
            rw [mid_att hs]
            obtain ⟨res, e⟩ : ∃ res, attemptAt G.pLen G.randB c = res := ⟨_, rfl⟩
            rw [e] at H ⊢
            refine VP.seq H (VP.seq (cmpF_vp (c := fun _ => attCfg G cl0 (k + 1, c) res) (fun σ s h => h.1)
              (o := fStatus) (v := 2) (by decide) (by decide) (by decide) (x := BitVec.ofNat 64 (stRes res))
              (fun σ s h => h.1.gi.slotV (attCfg_status (k + 1, c) res).1 |>.trans (attCfg_status (k + 1, c) res).2)
              (Q := fun σ t => St G (attCfg G cl0 (k + 1, c) res) X σ t ∧
                isa.eval (.zero .t2) t = some (BitVec.ofNat 64 (stRes res) == BitVec.ofNat 64 2))
              fun σ s t hs' h' _ ev => ⟨⟨h', hs'.2⟩, ev⟩) ?_)
            refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
            · rcases res with _ | ⟨_ | a, r⟩
              · exact VP.of_false fun σ s ⟨⟨_, ev⟩, e'⟩ => by rw [ev] at e'; simp [stRes] at e'
              · exact dec_vp hRL fun σ s h => h.1.1
              · exact VP.of_false fun σ s ⟨⟨_, ev⟩, e'⟩ => by rw [ev] at e'; simp [stRes] at e'
            · rcases res with _ | ⟨_ | a, r⟩
              · exact VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨h.mono' (by simp [attCfg, endCfg, upd, fStatus, fLeft,
                  fStart, fUsed, stRes]) (by simp [attCfg, endCfg]), x⟩
              · exact VP.of_false fun σ s ⟨⟨_, ev⟩, e'⟩ => by rw [ev] at e'; simp [stRes] at e'
              · exact VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨h.mono' (by simp [attCfg, endCfg, upd, fStatus, fLeft,
                  fStart, fUsed, stRes]) (by simp [attCfg, endCfg]), x⟩
  · exact cmpF_vp (c := fun _ => midCfg G cl0 (k, c)) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => h.1.gi.slotV (by simp) |>.trans (by simp [upd]))
      fun σ s t hs h' _ ev => ⟨⟨h', hs.2⟩, ev⟩

end

/-! ## The loop -/

section
variable {G : GP} {cl0 : Claims} {X : State → Prop}

/-- The iterations the controller runs. -/
abbrev nIt (G : GP) : Nat := iters G.pLen G.randB G.left 0

/-- The position of the last iteration. -/
abbrev lastPos (G : GP) : Nat × Nat := pos G.pLen G.randB G.left (nIt G - 1)

/-- The loop: from the start to the end of its last iteration. -/
theorem loop_vp (g : Geo) (hgq : g.qLen = G.qLen) (hq : G.qLen < 2048)
    (hatt : AttemptOk G cl0 X g.attempt) (hl : G.left ≤ 4096)
    (hRL : G.randB.length = G.randLen) (hR64 : G.randLen < 2 ^ 64) :
    VP (St G (ctlCfg cl0 (G.left, 0)) X) (.loop g.iteration (.zero .t2)) (St G (midCfg G cl0 (lastPos G)) X) := by
  simp only [lastPos, nIt]
  have hN := VG.Proof.Dsa.Generation.iters_pos G.pLen G.randB G.left 0
  let I : Nat → State → State → Prop := fun m σ s => m ≤ iters G.pLen G.randB G.left 0 ∧ St G (ctlCfg cl0 (pos G.pLen G.randB G.left (iters G.pLen G.randB G.left 0 - m))) X σ s
  have hb : ∀ n, VP (I (n + 1)) g.iteration fun σ s =>
      isa.eval (.zero .t2) s = some (decide (0 < n)) ∧ (n = 0 → St G (midCfg G cl0 (pos G.pLen G.randB G.left (iters G.pLen G.randB G.left 0 - 1))) X σ s) ∧
        (0 < n → I n σ s) := by
    intro n
    by_cases hn : n + 1 ≤ iters G.pLen G.randB G.left 0
    · obtain ⟨k, c, e⟩ : ∃ k c, pos G.pLen G.randB G.left (iters G.pLen G.randB G.left 0 - (n + 1)) = (k, c) := ⟨_, _, rfl⟩
      have hit : iters G.pLen G.randB k c = n + 1 := by
        have := VG.Proof.Dsa.Generation.iters_at (pLen := G.pLen) (R := G.randB) (left := G.left) (iters G.pLen G.randB G.left 0 - (n + 1))
          (by omega)
        rw [e] at this; rw [this]; omega
      have hk : k ≤ G.left := by
        have := VG.Proof.Dsa.Generation.pos_fst_le G.pLen G.randB G.left (iters G.pLen G.randB G.left 0 - (n + 1)); rw [e] at this; exact this
      have hc : c ≤ G.randLen := by
        have := VG.Proof.Dsa.Generation.pos_le G.pLen G.randB G.left (iters G.pLen G.randB G.left 0 - (n + 1)); rw [e, hRL] at this; exact this
      refine (iteration_vp g hgq hq hatt k c (by omega) hc hRL hR64).mono (fun σ s ⟨_, h⟩ => by rw [e] at h; exact h)
        fun σ s ⟨h, ev⟩ => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · have hs := VG.Proof.Dsa.Generation.stAt_last hit
        refine ⟨by rw [ev, ofNat_beq (by have := VG.Proof.Dsa.Generation.stAt_le G.pLen G.randB (k, c); omega) (by decide)]; simp [hs], fun _ => ?_, fun h => absurd h (by omega)⟩
        have : pos G.pLen G.randB G.left (iters G.pLen G.randB G.left 0 - 1) = (k, c) := by
          rw [← e]
        rw [this]; exact h
      · have hs := VG.Proof.Dsa.Generation.stAt_more (by omega : 1 < iters G.pLen G.randB k c)
        refine ⟨by rw [ev, hs]; simp [hp], fun h => absurd h (by omega), fun _ => ⟨by omega, ?_⟩⟩
        have hpos : pos G.pLen G.randB G.left (iters G.pLen G.randB G.left 0 - n) = step G.pLen G.randB (k, c) := by
          rw [show iters G.pLen G.randB G.left 0 - n = (iters G.pLen G.randB G.left 0 - (n + 1)) + 1 by omega]; simp only [VG.Proof.Dsa.Generation.pos]; rw [e]
        rw [hpos]
        have hm : midCfg G cl0 (k, c) = (ctlCfg cl0 (step G.pLen G.randB (k, c))).setV fStatus (BitVec.ofNat 64 2) := by
          simp [midCfg, midBase, hs]
        rw [hm] at h
        exact ⟨h.1.mono' (by simp [ctlCfg, upd, fStatus, fLeft, fUsed]) (by simp [ctlCfg]), h.2⟩
    · exact VP.of_false fun σ s ⟨h, _⟩ => hn h
  have := VP.loop (I := I) hb (iters G.pLen G.randB G.left 0 - 1)
  rw [show iters G.pLen G.randB G.left 0 - 1 + 1 = iters G.pLen G.randB G.left 0 by omega] at this
  exact this.mono (fun σ s h => ⟨by omega, by simp only [Nat.sub_self, VG.Proof.Dsa.Generation.pos]; exact h⟩)
    fun _ _ h => h

end

end VG.Proof.Dsa.RISCV64.PSearch
