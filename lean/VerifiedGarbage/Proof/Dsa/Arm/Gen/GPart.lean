module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GStep
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the search for g

`gPart_vp`: the h tape read candidate by candidate, `gStep` on each, until
one gives a g above 1 (`fG` := 1, g at `sG`) or the tape runs out
(`fG` := 2), as `Spec.Dsa.generator` searches it.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp wp_movw op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)

/-- A stage's pure facts, as hypotheses. -/
theorem VP.intro {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1


/-- The search's frame words at the `k`-th h. -/
abbrev gCfg (c : Cfg) (G : GP) (k : Nat) : Cfg :=
  ((c.setV fH (G.hs + BitVec.ofNat 32 (k * G.pLen))).setV fHLeft (BitVec.ofNat 32 (G.hsLen - k * G.pLen))).setV fG 4

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

/-- The next `h`: `fH` := `fH` + `pLen`, `fHLeft` := `fHLeft` − `pLen`. -/
theorem adv_vp {d : Cfg} (hH : fH ∈ d.LS) (hL : fHLeft ∈ d.LS) :
    VP (St G d X) (VG.Impl.Rsa.Arm.Keys.seqs [.block [ld .r1 fH],
        .block [.movw .r2 (BitVec.ofNat 16 G.pLen), .dp .add .r1 .r1 (.reg .r2)],
        .block (st .r1 fH), .block [ld .r1 fHLeft], .block [.dp .sub .r1 .r1 (.reg .r2)], .block (st .r1 fHLeft)])
      (St G ((d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)).setV fHLeft (d.V fHLeft - BitVec.ofNat 32 G.pLen)) X) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = d.V fH)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => h.1.slotV hH)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r1 = d.V fH + BitVec.ofNat 32 G.pLen) ∧
      s.gpr .r2 = BitVec.ofNat 32 G.pLen)
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.movw .r2 (BitVec.ofNat 16 1), .dp .add .r1 .r1 (.reg .r2)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_movw fun t u => wp_dp (op2_reg _ _) fun t' u' => WP.block_nil ?_) ?_
  · have l := h.lens
    have r2 : t.gpr .r2 = BitVec.ofNat 32 G.pLen := by rw [u.gpr, setWidth_ofNat16 (by omega)]
    refine ⟨⟨⟨h.of_rest ((u.rest (ws := [.r1, .r2]) (by simp)).trans (u'.rest (ws := [.r1, .r2]) (by simp)))
      (by rw [u'.mem, u.mem]), x⟩, ?_⟩, by rw [u'.other _ (by decide), r2]⟩
    rw [u'.gpr, dpVal, u.other _ (by decide), r1, r2]
  have hHL : fHLeft ∈ (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) X σ s ∧
      s.gpr .r2 = BitVec.ofNat 32 G.pLen)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨h, x⟩, r1⟩, r2⟩ h' R => ⟨⟨r1 ▸ h', x⟩, by rw [R.gpr _ (by decide), r2]⟩) ?_
  refine VP.seq (G := fun σ s => (St G (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) X σ s ∧
      s.gpr .r2 = BitVec.ofNat 32 G.pLen) ∧ s.gpr .r1 = d.V fHLeft)
    (ld_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => (h.1.1.slotV hHL).trans (by simp [upd, fHLeft, fH]))
      fun σ s t ⟨⟨h, x⟩, r2⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r2]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) X σ s ∧
      s.gpr .r1 = d.V fHLeft - BitVec.ofNat 32 G.pLen)
    (VP.taint [.r1, .r2] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1, .r2])
      (.block [.dp .sub .r1 .r1 (.reg .r2)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.2, h₂.2]
        · rw [h₁.1.2, h₂.1.2])
      fun σ s ⟨⟨⟨h, x⟩, r2⟩, r1⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.gpr, dpVal, r1, r2]⟩) ?_
  exact st_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 32 G.pLen)) (fun σ s h => h.1.1) (by decide)
    (varOk_of (by decide)) fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩

/-- The search's frame words agree with `c`'s but for `fH` and `fHLeft`. -/
theorem gV {c : Cfg} (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) {V : Nat → BitVec 32} {LS : List Nat} {v : BitVec 32}
    (hLS : ∀ o ∈ c.LS, o ∈ LS) (hV : ∀ o, o ≠ fH → o ≠ fHLeft → o ≠ fG → V o = c.V o) (hG : fG ∈ LS)
    (hVG : V fG = v) :
    ∀ o ∈ fG :: c.LS, o ∈ LS ∧ V o = upd c.V fG v o := by
  intro o ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | ho
  · exact ⟨hG, by rw [hVG, upd_self]⟩
  · refine ⟨hLS o ho, ?_⟩
    by_cases e : o = fG
    · subst e; rw [hVG, upd_self]
    · rw [upd_ne _ _ e, hV o (fun h => hfH (h ▸ ho)) (fun h => hfL (h ▸ ho)) e]

theorem gBody_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c : Cfg} {pv ev qv N : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG) (hhsb : G.hsB.length = G.hsLen) (hmod : G.hsLen % G.pLen = 0)
    (h32 : G.hsLen < 2 ^ 32) (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G pv ev qv N X (r + 1)) (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fHLeft 0),
        .ite .eq (.block (stImm fG 2)) (VG.Impl.Rsa.Arm.Keys.seqs [g.gStep, .block [ld .r1 fH],
          .block [.movw .r2 (BitVec.ofNat 16 g.pLen), .dp .add .r1 .r1 (.reg .r2)],
          .block (st .r1 fH), .block [ld .r1 fHLeft], .block [.dp .sub .r1 .r1 (.reg .r2)], .block (st .r1 fHLeft)]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval .eq s = some (decide (0 < r)) ∧ (r = 0 → St G (gFin c G (gRes G pv qv 0)) X σ s) ∧
        (0 < r → gInv c G pv ev qv N X r σ s)) := by
  refine VP.intro fun ⟨hr, hk, hc, hres⟩ => ?_
  have hpL : 0 < G.pLen := by omega
  generalize hMM : G.hsLen / G.pLen = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres
  have kL : ∀ j, j ≤ M → j * G.pLen ≤ G.hsLen := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  rw [hp]
  -- Whether an h is left.
  refine VP.seq (G := fun σ s => St G (gCfg c G k) X σ s ∧
      isa.eval .eq s = some (BitVec.ofNat 32 (G.hsLen - k * G.pLen) == BitVec.ofNat 32 0))
    (cmpF_vp (c := fun _ => gCfg c G k) (x := BitVec.ofNat 32 (G.hsLen - k * G.pLen)) (fun σ s h => h.1)
      (by decide) (by decide) (by decide) (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fHLeft, fG]))
      fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, e⟩) ?_
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- An h: `gStep`, then the next.
    have hi : k * G.pLen + G.pLen ≤ G.hsLen := by have := kL (k + 1) hkM; rwa [Nat.succ_mul] at this
    have e0 : (BitVec.ofNat 32 (G.hsLen - k * G.pLen) == BitVec.ofNat 32 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega⟩
    rw [hm] at hc; simp only [gCount] at hc
    have hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL
      (bytes := G.hsB.drop (k * G.pLen)) (by simp only [List.length_drop, hhsb]; omega)
    simp only [VG.Proof.Dsa.powMod_eq, ← hev', List.drop_drop] at hstep
    have stepVP := gStep_vp (c := gCfg c G k) (X := X) (i := k * G.pLen) certs ok hp hlq hn hpm hpb hpe hpr hctx he4
      he0 hP hPv hE hEv hM hMv hO hOv hHl hTl hGl hkls hpodd hp1 hplt hev hcl (by simp)
      (by simp [upd, fH, fHLeft, fG]) hi hhsb
    have notLeft : ∀ σ s, ¬((St G (gCfg c G k) X σ s ∧
        isa.eval .eq s = some (BitVec.ofNat 32 (G.hsLen - k * G.pLen) == BitVec.ofNat 32 0)) ∧
        isa.eval .eq s = some true) := fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    by_cases hok : gOk G pv ev (k * G.pLen)
    · -- It gives g: done.
      have r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega
      subst r0
      have some0 : gRes G pv qv 0 =
          some (Spec.Dsa.decodeBE (hAt G (k * G.pLen)) ^ ev % pv) := by
        rw [← hres, gRes, hstep]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      have hG1 : gOut (gCfg c G k) G (Spec.Dsa.decodeBE (hAt G (k * G.pLen))) pv ev =
          ({ gCfg c G k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (hAt G (k * G.pLen)) ^ ev % pv) G.pLen) ::
            (gCfg c G k).cl }).setV fG 1 := by
        simp only [gOut]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [some0]
      exact (h.of_rest R mm).mono (gV hfH hfL (fun o ho => by simp [ho]) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3])
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
      have eH : G.hs + BitVec.ofNat 32 (k * G.pLen) + BitVec.ofNat 32 G.pLen =
          G.hs + BitVec.ofNat 32 ((k + 1) * G.pLen) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
      have eL : BitVec.ofNat 32 (G.hsLen - k * G.pLen) - BitVec.ofNat 32 G.pLen =
          BitVec.ofNat 32 (G.hsLen - (k + 1) * G.pLen) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega
      refine cmpF_vp (x := BitVec.ofNat 32 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega, by omega, by rw [hMM, show M - (k + 1) = m by omega]; exact hc, ?_⟩, ?_, x⟩
      · rw [← hres]; simp only [gRes]
        rw [hstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]
      · refine (h.of_rest R mm).mono (fun o ho => ⟨?_, ?_⟩) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩)
          (fun d hd => ⟨hd, rfl⟩)
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
    refine VP.seq (G := St G ((gCfg c G k).setV fG (BitVec.ofNat 32 2)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => gCfg c G k) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G k).setV fG (BitVec.ofNat 32 2)) (x := BitVec.ofNat 32 2)
      (fun σ s h => h.1) (by decide)
      (by decide) (by decide) (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    rw [none0]
    exact (h.of_rest R mm).mono (gV hfH hfL (by simp_all) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3]) (by simp)
      (by simp [upd])) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)

/-- The search for g. -/
theorem gPart_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c : Cfg} {pv ev qv : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG) (hhsb : G.hsB.length = G.hsLen) (hmod : G.hsLen % G.pLen = 0)
    (h32 : G.hsLen < 2 ^ 32) (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) (hev' : ev = (pv - 1) / qv) :
    VP (St G c X) g.gPart (St G (gFin c G (gRes G pv qv 0)) X) := by
  unfold Geo.gPart
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r1 = G.hs)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => (h.1.gi.argW (by decide)).trans (by rw [← h.1.gi.hG]; rfl))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := St G (c.setV fH G.hs) X)
    (st_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩) ?_
  refine VP.seq (G := fun σ s => St G (c.setV fH G.hs) X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 G.hsLen)
    (ld_vp (c := fun _ => c.setV fH G.hs) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => (h.1.gi.argW (by decide)).trans (by rw [← h.1.gi.hG]; simp [mkG]))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := St G ((c.setV fH G.hs).setV fHLeft (BitVec.ofNat 32 G.hsLen)) X)
    (st_vp (c := fun _ => c.setV fH G.hs) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩) ?_
  have hN := gCount_gt G pv ev (G.hsLen / G.pLen) 0
  generalize hNN : gCount G pv ev (G.hsLen / G.pLen) 0 = N at hN
  refine VP.seq (G := gInv c G pv ev qv N X N)
    (stImm_vp (c := fun _ => (c.setV fH G.hs).setV fHLeft (BitVec.ofNat 32 G.hsLen)) (fun σ s h => h.1)
      (by decide) (varOk_of (by decide)) fun σ s t h h' _ =>
        ⟨⟨Nat.le_refl _, by simp, by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self]⟩,
          by simpa [gCfg] using h', h.2⟩) ?_
  rw [show N = N - 1 + 1 by omega]
  exact VP.loop (I := gInv c G pv ev qv (N - 1 + 1) X)
    (gBody_vp certs ok hp hlq hn hpm hpb hpe hpr hctx he4 he0 hP hPv hE hEv hM hMv hO hOv hHl hTl hGl hkls hpodd
      hp1 hplt hev hcl hhsb hmod h32 hfH hfL hev') _

end

end VG.Proof.Dsa.Arm.Gen
