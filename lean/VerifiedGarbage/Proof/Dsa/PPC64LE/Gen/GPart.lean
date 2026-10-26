module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.GStep
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PPart
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.ToDual

/-! # DSA parameter generation on PPC64LE: the search for g

`gPart_vp`: the h tape read candidate by candidate, `gStep` on each, until
one gives a g above 1 (`fG` := 1, g at `sG`) or the tape runs out
(`fG` := 2), as `Spec.Dsa.generator` searches it.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- The search's header words at the `k`-th h. -/
abbrev gCfg (c : Cfg) (G : GP) (k : Nat) : Cfg :=
  ((c.setV fH (G.hs + BitVec.ofNat 64 (k * G.pLen))).setV fHLeft (BitVec.ofNat 64 (G.hsLen - k * G.pLen))).setV fG 4

/-- Whether the h at byte `i` of the tape gives a g above 1. -/
abbrev gOk (G : GP) (pv ev i : Nat) : Prop :=
  1 < Spec.Dsa.decodeBE (hAt G i) ∧ Spec.Dsa.decodeBE (hAt G i) < pv - 1 ∧
    1 < Spec.Dsa.decodeBE (hAt G i) ^ ev % pv

/-- The search's iterations from the `k`-th h, with `m` left. -/
def gCount (G : GP) (pv ev : Nat) : Nat → Nat → Nat
  | 0, k => k + 1
  | m + 1, k => if gOk G pv ev (k * G.pLen) then k + 1 else gCount G pv ev m (k + 1)

theorem gCount_gt (G : GP) (pv ev : Nat) : ∀ m k, k < gCount G pv ev m k
  | 0, k => by simp [gCount]
  | m + 1, k => by
    simp only [gCount]; split
    · omega
    · exact Nat.lt_of_succ_lt (gCount_gt G pv ev m (k + 1))

/-- The generator the spec finds from the `k`-th h. -/
abbrev gRes (G : GP) (pv qv k : Nat) : Option Nat :=
  Spec.Dsa.generator pv qv ((Spec.Dsa.generationChunks G.pLen (G.hsB.drop (k * G.pLen))).map Spec.Dsa.decodeBE)

/-- The stage after the search. -/
def gFin (c : Cfg) (G : GP) : Option Nat → Cfg
  | some g => ({ c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }).setV fG 1
  | none => c.setV fG 2

/-- The search with `r` iterations left of `N`. -/
abbrev gInv (c : Cfg) (G : GP) (pv ev qv N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r ≤ G.hsLen / G.pLen ∧ gCount G pv ev (G.hsLen / G.pLen - (N - r)) (N - r) = N ∧
    gRes G pv qv (N - r) = gRes G pv qv 0) ∧ St G (gCfg c G (N - r)) X σ s

section
variable {G : GP} {X : State → Prop}

/-- `r3` := `f r3`, from a known `r3`. -/
theorem r3op_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G 176 σ (c σ) s)
    {i : Instr} (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r3]) (.block [i]) hc).isSome = true)
    {f : BitVec 64 → BitVec 64} (he : ∀ s : State, exec i s = some (s.write .r3 (f (s.gpr .r3))))
    {x : BitVec 64} (hx : ∀ σ s, P σ s → s.gpr .r3 = x)
    (k : ∀ σ s t, P σ s → SS G 176 σ (c σ) t → t.gpr .r3 = f x → Q σ t) : VP P (.block [i]) Q := by
  refine VP.pub (SS.pub hF) [.r3] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx _ _ h₁, hx _ _ h₂]) fun σ s hs => ?_
  refine WP.wr (he s) fun t u sp _ => WP.block_nil (k σ s t hs ((hF σ s hs).of_upd u sp (by decide)) ?_)
  rw [u.gpr, hx σ s hs]

/-- The next `h`: `fH` := `fH` + `pLen`, `fHLeft` := `fHLeft` − `pLen`. -/
theorem adv_vp {d : Cfg} (hH : fH ∈ d.LS) (hL : fHLeft ∈ d.LS) :
    VP (St G d X) (.block [ld .r3 fH, .addi .r3 .r3 G.pLen, st .r3 fH, ld .r3 fHLeft, .subi .r3 .r3 G.pLen,
        st .r3 fHLeft])
      (St G ((d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)).setV fHLeft (d.V fHLeft - BitVec.ofNat 64 G.pLen)) X) := by
  by_cases l : G.pLen < 2 ^ 15
  swap
  · exact VP.of_false fun σ s h => l (by rcases h.1.lens with e | e | e <;> rw [e] <;> decide)
  rw [show ([ld .r3 fH, .addi .r3 .r3 G.pLen, st .r3 fH, ld .r3 fHLeft, .subi .r3 .r3 G.pLen, st .r3 fHLeft] :
      List Instr) = [ld .r3 fH] ++ ([.addi .r3 .r3 G.pLen] ++ ([st .r3 fH] ++ ([ld .r3 fHLeft] ++
        ([.subi .r3 .r3 G.pLen] ++ [st .r3 fHLeft])))) from rfl]
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = d.V fH)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => h.1.gi.slotV hH) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = d.V fH + BitVec.ofNat 64 G.pLen)
    (r3op_vp (c := fun _ => d) (f := (· + BitVec.ofNat 64 G.pLen)) (fun σ s h => h.1.1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3]) (.block [.addi .r3 .r3 G.pLen]), rfl⟩ (fun s => exec_addi (d := .r3) (n := .r3) (by decide) l)
      (fun σ s h => h.2) fun σ s t ⟨⟨_, x⟩, _⟩ h' e => ⟨⟨h', x⟩, e⟩) ?_
  have hHL : fHLeft ∈ (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)).LS := List.mem_cons_of_mem _ hL
  refine VP.block_append (G := St G (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) X)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩) ?_
  refine VP.block_append (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) X σ s ∧
      s.gpr .r3 = d.V fHLeft)
    (ld_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) (fun σ s h => h.1) (by decide) (by decide)
      (by decide) (fun σ s h => (h.1.gi.slotV hHL).trans (by simp [upd, fHLeft, fH]))
      fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) X σ s ∧
      s.gpr .r3 = d.V fHLeft - BitVec.ofNat 64 G.pLen)
    (r3op_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) (f := (· - BitVec.ofNat 64 G.pLen))
      (fun σ s h => h.1.1)
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3]) (.block [.subi .r3 .r3 G.pLen]), rfl⟩
      (fun s => exec_subi (d := .r3) (n := .r3) (by decide) (Nat.le_of_lt l)) (fun σ s h => h.2)
      fun σ s t ⟨⟨_, x⟩, _⟩ h' e => ⟨⟨h', x⟩, e⟩) ?_
  exact st_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) (fun σ s h => h.1.1)
    (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩

/-- The search's header words agree with `c`'s but for `fH` and `fHLeft`. -/
theorem gV {c : Cfg} (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) {V : Nat → BitVec 64} {LS : List Nat}
    {v : BitVec 64} (hLS : ∀ o ∈ c.LS, o ∈ LS) (hV : ∀ o, o ≠ fH → o ≠ fHLeft → o ≠ fG → V o = c.V o)
    (hG : fG ∈ LS) (hVG : V fG = v) :
    ∀ o ∈ fG :: c.LS, o ∈ LS ∧ V o = upd c.V fG v o := by
  intro o ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | ho
  · exact ⟨hG, by rw [hVG, upd_self]⟩
  · refine ⟨hLS o ho, ?_⟩
    by_cases e : o = fG
    · subst e; rw [hVG, upd_self]
    · rw [upd_ne _ _ e, hV o (fun h => hfH (h ▸ ho)) (fun h => hfL (h ▸ ho)) e]

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

theorem gBody_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {c : Cfg} {pv ev qv N : Nat} (R : GReq G c pv ev) (hhsb : G.hsB.length = G.hsLen)
    (hmod : G.hsLen % G.pLen = 0) (h64 : G.hsLen < 2 ^ 64) (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G pv ev qv N X (r + 1)) (seqs [.block (cmpF fHLeft 0),
        .ite (.zero .d .r0) (.block (stImm fG 2))
          (seqs [g.gStep, .block [ld .r3 fH, .addi .r3 .r3 g.pLen, st .r3 fH, ld .r3 fHLeft,
            .subi .r3 .r3 g.pLen, st .r3 fHLeft]]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval (.zero .d .r0) s = some (decide (0 < r)) ∧
        (r = 0 → St G (gFin c G (gRes G pv qv 0)) X σ s) ∧ (0 < r → gInv c G pv ev qv N X r σ s)) := by
  refine VP.intro fun ⟨hr, hk, hc, hres⟩ => ?_
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hpL : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  generalize hMM : G.hsLen / G.pLen = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres
  have kL : ∀ j, j ≤ M → j * G.pLen ≤ G.hsLen := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  rw [hg]
  -- Whether an h is left.
  refine VP.seq (G := fun σ s => St G (gCfg c G k) X σ s ∧
      isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (G.hsLen - k * G.pLen) == BitVec.ofNat 64 0))
    (cmpF_vp (c := fun _ => gCfg c G k) (x := BitVec.ofNat 64 (G.hsLen - k * G.pLen)) (fun σ s h => h.1)
      (by decide) (by decide) (by decide) (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fHLeft, fG]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, e⟩) ?_
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- An h: `gStep`, then the next.
    have hi : k * G.pLen + G.pLen ≤ G.hsLen := by have := kL (k + 1) hkM; rwa [Nat.succ_mul] at this
    have e0 : (BitVec.ofNat 64 (G.hsLen - k * G.pLen) == BitVec.ofNat 64 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega⟩
    rw [hm] at hc; simp only [gCount] at hc
    have hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL
      (bytes := G.hsB.drop (k * G.pLen)) (by simp only [List.length_drop, hhsb]; omega)
    simp only [VG.Proof.Dsa.powMod_eq, ← hev', List.drop_drop] at hstep
    have stepVP := gStep_vp (c := gCfg c G k) (X := X) (i := k * G.pLen) hg hgq cert R.hM R.hMv R.hO R.hOv R.hZ
      R.hZv R.hHl R.hTl R.hkls R.hPc R.hpv R.hp2 R.hpo R.hEc R.hev R.hcl (by simp)
      (by simp [upd, fH, fHLeft, fG]) hi
    have notLeft : ∀ σ s, ¬((St G (gCfg c G k) X σ s ∧
        isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (G.hsLen - k * G.pLen) == BitVec.ofNat 64 0)) ∧
        isa.eval (.zero .d .r0) s = some true) := fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    by_cases hok : gOk G pv ev (k * G.pLen)
    · -- It gives g: done.
      have r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega
      subst r0
      have some0 : gRes G pv qv 0 = some (Spec.Dsa.decodeBE (hAt G (k * G.pLen)) ^ ev % pv) := by
        rw [← hres, gRes, hstep]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      have hG1 : gOut (gCfg c G k) G (Spec.Dsa.decodeBE (hAt G (k * G.pLen))) pv ev =
          ({ gCfg c G k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (hAt G (k * G.pLen)) ^ ev % pv) G.pLen) ::
            (gCfg c G k).cl }).setV fG 1 := by
        simp only [gOut]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [some0]
      exact h'.mono (gV R.hfH R.hfL (fun o ho => by simp [ho]) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3])
        (by simp) (by simp [upd, fH, fHLeft, fG])) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · -- It does not: the next h.
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)] at hc
      have rpos : 0 < r := by have := gCount_gt G pv ev m (k + 1); omega
      have hNr : N - r = k + 1 := by omega
      have hG1 : gOut (gCfg c G k) G (Spec.Dsa.decodeBE (hAt G (k * G.pLen))) pv ev = gCfg c G k := by
        simp only [gOut]; exact ite_eq_right_of_eq_false _ _ (eq_false hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      have eH : G.hs + BitVec.ofNat 64 (k * G.pLen) + BitVec.ofNat 64 G.pLen =
          G.hs + BitVec.ofNat 64 ((k + 1) * G.pLen) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
      have eL : BitVec.ofNat 64 (G.hsLen - k * G.pLen) - BitVec.ofNat 64 G.pLen =
          BitVec.ofNat 64 (G.hsLen - (k + 1) * G.pLen) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega
      refine cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega, by omega, by rw [hMM, show M - (k + 1) = m by omega]; exact hc, ?_⟩, ?_, x⟩
      · rw [← hres]; simp only [gRes]
        rw [hstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]
      · refine h'.mono (fun o ho => ⟨?_, ?_⟩) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
        · simp only [List.mem_cons] at ho ⊢
          rcases ho with h' | h' | h' | h' <;> simp [h']
        · simp only [upd]
          by_cases a : o = fHLeft
          · subst a; simp [eL, fHLeft, fG]
          · by_cases b : o = fH
            · subst b; simp [eH, fH, fHLeft, fG]
            · simp [a, b]
  · -- The tape is done: `fG` := 2.
    have hkM' : k = M := by omega
    subst hkM'
    have r0 : r = 0 := by simp only [Nat.sub_self, gCount] at hc; omega
    subst r0
    have hz : G.hsLen - k * G.pLen = 0 := by
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod); rw [hMM] at this; omega
    have none0 : gRes G pv qv 0 = none := by
      rw [← hres, gRes, VG.Proof.Dsa.Generation.generationChunks_done (by simp only [List.length_drop, hhsb]; omega)]
      rfl
    refine VP.seq (G := St G ((gCfg c G k).setV fG (BitVec.ofNat 64 2)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => gCfg c G k) (o := fG) (v := 2) (fun σ s h => h.1.1.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G k).setV fG (BitVec.ofNat 64 2)) (x := BitVec.ofNat 64 2)
      (fun σ s h => h.1) (by decide) (by decide) (by decide) (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    rw [none0]
    exact h'.mono (gV R.hfH R.hfL (by simp_all) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3]) (by simp)
      (by simp [upd])) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)

/-- The search for g. -/
theorem gPart_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {c : Cfg} {pv ev qv : Nat} (R : GReq G c pv ev) (hhsb : G.hsB.length = G.hsLen)
    (hmod : G.hsLen % G.pLen = 0) (h64 : G.hsLen < 2 ^ 64) (hev' : ev = (pv - 1) / qv) :
    VP (St G c X) g.gPart (St G (gFin c G (gRes G pv qv 0)) X) := by
  unfold Geo.gPart
  rw [show ([ld .r3 fHs, st .r3 fH, ld .r3 fHsLen, st .r3 fHLeft] : List Instr) =
    [ld .r3 fHs] ++ ([st .r3 fH] ++ ([ld .r3 fHsLen] ++ [st .r3 fHLeft])) from rfl]
  refine VP.seq (G := St G ((c.setV fH G.hs).setV fHLeft (BitVec.ofNat 64 G.hsLen)) X)
    (VP.block_append (G := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.hs)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => h.1.gi.fixedV (by simp [fixedWords])) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_) ?_
  · refine VP.block_append (G := St G (c.setV fH G.hs) X)
      (st_vp (c := fun _ => c) (fun σ s h => h.1.1) (varOk_of (by decide))
        fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩) ?_
    refine VP.block_append (G := fun σ s => St G (c.setV fH G.hs) X σ s ∧ s.gpr .r3 = BitVec.ofNat 64 G.hsLen)
      (ld_vp (c := fun _ => c.setV fH G.hs) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => h.1.gi.fixedV (by simp [fixedWords])) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
    exact st_vp (c := fun _ => c.setV fH G.hs) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩
  have hN := gCount_gt G pv ev (G.hsLen / G.pLen) 0
  generalize hNN : gCount G pv ev (G.hsLen / G.pLen) 0 = N at hN
  refine VP.seq (G := gInv c G pv ev qv N X N)
    (stImm_vp (c := fun _ => (c.setV fH G.hs).setV fHLeft (BitVec.ofNat 64 G.hsLen)) (o := fG) (v := 4)
      (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ =>
        ⟨⟨Nat.le_refl _, by simp, by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self]⟩,
          by simpa [gCfg] using h', h.2⟩) ?_
  rw [show N = N - 1 + 1 by omega]
  exact VP.loop (I := gInv c G pv ev qv (N - 1 + 1) X) (gBody_vp hg hgq cert R hhsb hmod h64 hev') _

end

end VG.Proof.Dsa.PPC64LE.Gen
