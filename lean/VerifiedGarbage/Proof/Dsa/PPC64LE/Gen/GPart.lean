module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.GStep
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PPart
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: the search for g

`gPart_vp`: the window of `rand` at `w` (`fHs`, of `HL` octets, `fHsLen`) read
candidate by candidate, `gStep` on each, until one gives a g above 1 (`fG`
:= 1, g at `sG`) or fewer than `p_len` octets are left (`fG` := 2), as
`Spec.Dsa.generator` searches its candidates; `fH` then points past the
candidates read (`generatorCount`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- The window's octets. -/
abbrev hsW (G : GP) (w HL : Nat) : List Byte := (G.witB.drop w).take HL

/-- The window's candidates from the `k`-th. -/
abbrev gCands (G : GP) (w HL k : Nat) : List Nat :=
  (Spec.Dsa.generationChunks G.pLen ((hsW G w HL).drop (k * G.pLen))).map Spec.Dsa.decodeBE

/-- The search's header words at the `k`-th h. -/
abbrev gCfg (c : Cfg) (G : GP) (w HL k : Nat) : Cfg :=
  ((c.setV fH (G.wit + BitVec.ofNat 64 (w + k * G.pLen))).setV fHLeft (BitVec.ofNat 64 (HL - k * G.pLen))).setV fG 4

/-- Whether the h at byte `i` of `rand` gives a g above 1. -/
abbrev gOk (G : GP) (pv ev i : Nat) : Prop :=
  1 < Spec.Dsa.decodeBE (hAt G i) ∧ Spec.Dsa.decodeBE (hAt G i) < pv - 1 ∧
    1 < Spec.Dsa.decodeBE (hAt G i) ^ ev % pv

/-- The search's iterations from the `k`-th h, with `m` left. -/
def gCount (G : GP) (w pv ev : Nat) : Nat → Nat → Nat
  | 0, k => k + 1
  | m + 1, k => if gOk G pv ev (w + k * G.pLen) then k + 1 else gCount G w pv ev m (k + 1)

theorem gCount_gt (G : GP) (w pv ev : Nat) : ∀ m k, k < gCount G w pv ev m k
  | 0, k => by simp [gCount]
  | m + 1, k => by
    simp only [gCount]; split
    · omega
    · exact Nat.lt_of_succ_lt (gCount_gt G w pv ev m (k + 1))

/-- The generator the spec finds from the `k`-th h. -/
abbrev gRes (G : GP) (w HL pv qv k : Nat) : Option Nat := Spec.Dsa.generator pv qv (gCands G w HL k)

/-- The candidates the spec reads from the `k`-th h. -/
abbrev gNum (G : GP) (w HL pv qv k : Nat) : Nat :=
  VG.Proof.Dsa.Generation.generatorCount pv qv (gCands G w HL k)

/-- The stage after the search: `fH` past the candidates read. -/
def gFin (c : Cfg) (G : GP) (w HL pv qv : Nat) : Cfg :=
  match gRes G w HL pv qv 0 with
  | some g => ((({ c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }).setV fG 1).setV fH
      (G.wit + BitVec.ofNat 64 (w + gNum G w HL pv qv 0 * G.pLen)))
  | none => (c.setV fG 2).setV fH (G.wit + BitVec.ofNat 64 (w + gNum G w HL pv qv 0 * G.pLen))

/-- The search with `r` iterations left of `N`. -/
abbrev gInv (c : Cfg) (G : GP) (w HL pv ev qv N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r ≤ HL / G.pLen ∧ gCount G w pv ev (HL / G.pLen - (N - r)) (N - r) = N ∧
    gRes G w HL pv qv (N - r) = gRes G w HL pv qv 0 ∧
    N - r + gNum G w HL pv qv (N - r) = gNum G w HL pv qv 0) ∧ St G (gCfg c G w HL (N - r)) X σ s

/-- A candidate of the window is the `h` at its place in `rand`. -/
theorem hsW_take {G : GP} {w HL i : Nat} (hi : i + G.pLen ≤ HL) :
    ((hsW G w HL).drop i).take G.pLen = hAt G (w + i) := by
  simp only [hsW, hAt, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega), Nat.add_comm]

theorem hsW_length {G : GP} {w HL : Nat} (hw : w + HL ≤ G.witLen) (hl : G.witB.length = G.witLen) :
    (hsW G w HL).length = HL := by
  simp only [hsW, List.length_take, List.length_drop, hl]; omega

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

/-- The search's header words agree with `c`'s but for `fH`, `fHLeft` and
`fG`, with `fG` and `fH` as the search leaves them. -/
theorem gV {c : Cfg} (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) {V : Nat → BitVec 64} {LS : List Nat}
    {v x : BitVec 64} (hLS : ∀ o ∈ c.LS, o ∈ LS) (hV : ∀ o, o ≠ fH → o ≠ fHLeft → o ≠ fG → V o = c.V o)
    (hG : fG ∈ LS) (hVG : V fG = v) (hH : fH ∈ LS) (hVH : V fH = x) :
    ∀ o ∈ fH :: fG :: c.LS, o ∈ LS ∧ V o = upd (upd c.V fG v) fH x o := by
  intro o ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | ho
  · exact ⟨hH, by rw [hVH, upd_self]⟩
  · exact ⟨hG, by rw [hVG, upd_ne _ _ (by decide), upd_self]⟩
  · refine ⟨hLS o ho, ?_⟩
    have e1 : o ≠ fH := fun h => hfH (h ▸ ho)
    by_cases e : o = fG
    · subst e; rw [hVG, upd_ne _ _ (by decide), upd_self]
    · rw [upd_ne _ _ e1, upd_ne _ _ e, hV o e1 (fun h => hfL (h ▸ ho)) e]

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
    {c : Cfg} {pv ev qv N w HL : Nat} (R : GReq G c pv ev) (hw : w + HL ≤ G.witLen)
    (hwl : G.witB.length = G.witLen) (h64 : HL < 2 ^ 64) (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G w HL pv ev qv N X (r + 1)) (seqs [.block ([ld .r3 fHLeft, .li .r4 g.pLen] ++ ltR),
        .ite (.zero .d .r0) (.block (stImm fG 2))
          (seqs [g.gStep, .block [ld .r3 fH, .addi .r3 .r3 g.pLen, st .r3 fH, ld .r3 fHLeft,
            .subi .r3 .r3 g.pLen, st .r3 fHLeft]]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval (.zero .d .r0) s = some (decide (0 < r)) ∧
        (r = 0 → St G (gFin c G w HL pv qv) X σ s) ∧ (0 < r → gInv c G w HL pv ev qv N X r σ s)) := by
  refine VP.intro fun ⟨hr, hk, hc, hres, hnum⟩ => ?_
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hpL : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have hp15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  generalize hMM : HL / G.pLen = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres hnum
  have kL : ∀ j, j ≤ M → j * G.pLen ≤ HL := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  have hlen := hsW_length (G := G) hw hwl
  rw [hg]
  -- Whether an h is left.
  refine VP.seq (G := fun σ s => St G (gCfg c G w HL k) X σ s ∧
      isa.eval (.zero .d .r0) s = some (decide (HL - k * G.pLen < G.pLen)))
    (ltF_vp (c := fun _ => gCfg c G w HL k) (x := BitVec.ofNat 64 (HL - k * G.pLen)) (fun σ s h => h.1)
      (by decide) (by decide) hp15 (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fHLeft, fG]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩) ?_
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- An h: `gStep`, then the next.
    have hi : k * G.pLen + G.pLen ≤ HL := by have := kL (k + 1) hkM; rwa [Nat.succ_mul] at this
    have e0 : decide (HL - k * G.pLen < G.pLen) = false := decide_eq_false (by omega)
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega⟩
    rw [hm] at hc; simp only [gCount] at hc
    have hbl : G.pLen ≤ ((hsW G w HL).drop (k * G.pLen)).length := by
      simp only [List.length_drop, hlen]; omega
    have hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL hbl
    have cstep := VG.Proof.Dsa.Generation.generatorCount_chunks_step (p := pv) (q := qv) hpL hbl
    rw [hsW_take hi, List.drop_drop] at hstep cstep
    simp only [VG.Proof.Dsa.powMod_eq, ← hev'] at hstep cstep
    have stepVP := gStep_vp (c := gCfg c G w HL k) (X := X) (i := w + k * G.pLen) hg hgq cert R.hM R.hMv R.hO
      R.hOv R.hZ R.hZv R.hHl R.hTl R.hkls R.hPc R.hpv R.hp2 R.hpo R.hEc R.hev R.hcl (by simp)
      (by simp [upd, fH, fHLeft, fG]) (by omega)
    have notLeft : ∀ σ s, ¬((St G (gCfg c G w HL k) X σ s ∧
        isa.eval (.zero .d .r0) s = some (decide (HL - k * G.pLen < G.pLen))) ∧
        isa.eval (.zero .d .r0) s = some true) := fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    have eH : G.wit + BitVec.ofNat 64 (w + k * G.pLen) + BitVec.ofNat 64 G.pLen =
        G.wit + BitVec.ofNat 64 (w + (k + 1) * G.pLen) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul, Nat.add_assoc]
    by_cases hok : gOk G pv ev (w + k * G.pLen)
    · -- It gives g: done.
      have r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega
      subst r0
      have some0 : gRes G w HL pv qv 0 = some (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen)) ^ ev % pv) := by
        rw [← hres, gRes, hstep]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      have num0 : gNum G w HL pv qv 0 = k + 1 := by
        rw [← hnum, gNum, cstep, ite_eq_left_of_eq_true _ _ (eq_true hok)]
      have hG1 : gOut (gCfg c G w HL k) G (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen))) pv ev =
          ({ gCfg c G w HL k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G w HL k).cl }).setV fG 1 := by
        simp only [gOut]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      simp only [gFin, some0, num0]
      exact h'.mono (gV R.hfH R.hfL (fun o ho => by simp [ho]) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3])
        (by simp) (by simp [upd, fH, fHLeft, fG]) (by simp) (by simp [upd, fH, fHLeft, fG, eH]))
        (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · -- It does not: the next h.
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)] at hc
      have rpos : 0 < r := by have := gCount_gt G w pv ev m (k + 1); omega
      have hNr : N - r = k + 1 := by omega
      have hG1 : gOut (gCfg c G w HL k) G (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen))) pv ev = gCfg c G w HL k := by
        simp only [gOut]; exact ite_eq_right_of_eq_false _ _ (eq_false hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      have eL : BitVec.ofNat 64 (HL - k * G.pLen) - BitVec.ofNat 64 G.pLen =
          BitVec.ofNat 64 (HL - (k + 1) * G.pLen) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega
      refine cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega, by omega, by rw [hMM, show M - (k + 1) = m by omega]; exact hc, ?_, ?_⟩, ?_, x⟩
      · rw [← hres]; simp only [gRes, gCands]
        rw [hstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]
      · rw [← hnum]; simp only [gNum, gCands]
        rw [cstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]; omega
      · refine h'.mono (fun o ho => ⟨?_, ?_⟩) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
        · simp only [List.mem_cons] at ho ⊢
          rcases ho with h' | h' | h' | h' <;> simp [h']
        · simp only [upd]
          by_cases a : o = fHLeft
          · subst a; simp [eL, fHLeft, fG]
          · by_cases b : o = fH
            · subst b; simp [eH, fH, fHLeft, fG]
            · simp [a, b]
  · -- Fewer than `p_len` octets left: `fG` := 2.
    have hkM' : k = M := by omega
    subst hkM'
    have r0 : r = 0 := by simp only [Nat.sub_self, gCount] at hc; omega
    subst r0
    have hz : decide (HL - k * G.pLen < G.pLen) = true := by
      refine decide_eq_true ?_
      rw [← hMM, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]; exact Nat.mod_lt _ hpL
    have hsh : ((hsW G w HL).drop (k * G.pLen)).length < G.pLen := by
      simp only [List.length_drop, hlen]; exact of_decide_eq_true hz
    have none0 : gRes G w HL pv qv 0 = none := by
      rw [← hres]
      show Spec.Dsa.generator pv qv ((Spec.Dsa.generationChunks _ _).map _) = none
      rw [VG.Proof.Dsa.Generation.generationChunks_done hsh]
      rfl
    have num0 : gNum G w HL pv qv 0 = k := by
      rw [← hnum, gNum, VG.Proof.Dsa.Generation.generatorCount_chunks_done hsh, Nat.add_zero]
    refine VP.seq (G := St G ((gCfg c G w HL k).setV fG (BitVec.ofNat 64 2)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => gCfg c G w HL k) (o := fG) (v := 2) (fun σ s h => h.1.1.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G w HL k).setV fG (BitVec.ofNat 64 2)) (x := BitVec.ofNat 64 2)
      (fun σ s h => h.1) (by decide) (by decide) (by decide) (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    simp only [gFin, none0, num0]
    exact h'.mono (gV R.hfH R.hfL (by simp_all) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3]) (by simp)
      (by simp [upd]) (by simp) (by simp [upd, fH, fHLeft, fG])) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)

/-- The search for g over the window of `HL` octets at `w`. -/
theorem gPart_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {c : Cfg} {pv ev qv w HL : Nat} (R : GReq G c pv ev) (hS : fHs ∈ c.LS)
    (hSv : c.V fHs = G.wit + BitVec.ofNat 64 w) (hL : fHsLen ∈ c.LS) (hLv : c.V fHsLen = BitVec.ofNat 64 HL)
    (hw : w + HL ≤ G.witLen) (hwl : G.witB.length = G.witLen) (h64 : HL < 2 ^ 64) (hev' : ev = (pv - 1) / qv) :
    VP (St G c X) g.gPart (St G (gFin c G w HL pv qv) X) := by
  unfold Geo.gPart
  rw [show ([ld .r3 fHs, st .r3 fH, ld .r3 fHsLen, st .r3 fHLeft] : List Instr) =
    [ld .r3 fHs] ++ ([st .r3 fH] ++ ([ld .r3 fHsLen] ++ [st .r3 fHLeft])) from rfl]
  have hHs : fHsLen ∈ (c.setV fH (G.wit + BitVec.ofNat 64 w)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := St G ((c.setV fH (G.wit + BitVec.ofNat 64 w)).setV fHLeft (BitVec.ofNat 64 HL)) X)
    (VP.block_append (G := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.wit + BitVec.ofNat 64 w)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hS).trans hSv) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_) ?_
  · refine VP.block_append (G := St G (c.setV fH (G.wit + BitVec.ofNat 64 w)) X)
      (st_vp (c := fun _ => c) (fun σ s h => h.1.1) (varOk_of (by decide))
        fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩) ?_
    refine VP.block_append (G := fun σ s => St G (c.setV fH (G.wit + BitVec.ofNat 64 w)) X σ s ∧
        s.gpr .r3 = BitVec.ofNat 64 HL)
      (ld_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1) (by decide) (by decide)
        (by decide) (fun σ s h => (h.1.gi.slotV hHs).trans ((upd_ne (o := fH) _ (G.wit + BitVec.ofNat 64 w) (by decide)).trans hLv))
        fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
    exact st_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩
  have hN := gCount_gt G w pv ev (HL / G.pLen) 0
  generalize hNN : gCount G w pv ev (HL / G.pLen) 0 = N at hN
  refine VP.seq (G := gInv c G w HL pv ev qv N X N)
    (stImm_vp (c := fun _ => (c.setV fH (G.wit + BitVec.ofNat 64 w)).setV fHLeft (BitVec.ofNat 64 HL)) (o := fG)
      (v := 4) (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ =>
        ⟨⟨Nat.le_refl _, by simp, by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self],
          by rw [Nat.sub_self, Nat.zero_add]⟩, by simpa [gCfg] using h', h.2⟩) ?_
  rw [show N = N - 1 + 1 by omega]
  exact VP.loop (I := gInv c G w HL pv ev qv (N - 1 + 1) X) (gBody_vp hg hgq cert R hw hwl h64 hev') _

end

end VG.Proof.Dsa.PPC64LE.Gen
