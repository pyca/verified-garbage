module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GStep
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Intro
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the search for g

`gPart_vp`: the window of `rand` at `w` (`fHs`, of `HL` octets, `fHsLen`) read
candidate by candidate, `gStep` on each, until one gives a g above 1 (`fG`
:= 1, g at `sG`) or fewer than `p_len` octets are left (`fG` := 2), as
`Spec.Dsa.generator` searches its candidates; `fH` then points past the
candidates read (`generatorCount`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp wp_movw op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)


/-- The window's octets. -/
abbrev hsW (G : GP) (w HL : Nat) : List Byte := (G.witB.drop w).take HL

/-- The window's candidates from the `k`-th. -/
abbrev gCands (G : GP) (w HL k : Nat) : List Nat :=
  (Spec.Dsa.generationChunks G.pLen ((hsW G w HL).drop (k * G.pLen))).map Spec.Dsa.decodeBE

/-- The search's frame words at the `k`-th h. -/
abbrev gCfg (c : Cfg) (G : GP) (w HL k : Nat) : Cfg :=
  ((c.setV fH (G.wit + BitVec.ofNat 32 (w + k * G.pLen))).setV fHLeft (BitVec.ofNat 32 (HL - k * G.pLen))).setV fG 4

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
    · omega_arith
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
      (G.wit + BitVec.ofNat 32 (w + gNum G w HL pv qv 0 * G.pLen)))
  | none => (c.setV fG 2).setV fH (G.wit + BitVec.ofNat 32 (w + gNum G w HL pv qv 0 * G.pLen))

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
    have r2 : t.gpr .r2 = BitVec.ofNat 32 G.pLen := by rw [u.gpr, setWidth_ofNat16 (by omega_arith)]
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

/-- The search's frame words agree with `c`'s but for `fH`, `fHLeft` and
`fG`, with `fG` and `fH` as the search leaves them. -/
theorem gV {c : Cfg} (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) {V : Nat → BitVec 32} {LS : List Nat}
    {v x : BitVec 32} (hLS : ∀ o ∈ c.LS, o ∈ LS) (hV : ∀ o, o ≠ fH → o ≠ fHLeft → o ≠ fG → V o = c.V o)
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

theorem gBody_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c : Cfg} {pv ev qv N w HL : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG) (hw : w + HL ≤ G.witLen) (hwl : G.witB.length = G.witLen)
    (h32 : HL < 2 ^ 32) (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G w HL pv ev qv N X (r + 1)) (VG.Impl.Rsa.Arm.Keys.seqs [.block [ld .r0 fHLeft],
        .block (([.movw .r1 (BitVec.ofNat 16 g.pLen)] : List Instr) ++ less),
        .ite .eq (.block (stImm fG 2)) (VG.Impl.Rsa.Arm.Keys.seqs [g.gStep, .block [ld .r1 fH],
          .block [.movw .r2 (BitVec.ofNat 16 g.pLen), .dp .add .r1 .r1 (.reg .r2)],
          .block (st .r1 fH), .block [ld .r1 fHLeft], .block [.dp .sub .r1 .r1 (.reg .r2)], .block (st .r1 fHLeft)]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval .eq s = some (decide (0 < r)) ∧ (r = 0 → St G (gFin c G w HL pv qv) X σ s) ∧
        (0 < r → gInv c G w HL pv ev qv N X r σ s)) := by
  refine VG.Proof.Dsa.Arm.Gen.VP.intro fun ⟨hr, hk, hc, hres, hnum⟩ => ?_
  have hpL : 0 < G.pLen := by omega_arith
  have hp16 : G.pLen < 2 ^ 16 := by omega_arith
  generalize hMM : HL / G.pLen = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres hnum
  have kL : ∀ j, j ≤ M → j * G.pLen ≤ HL := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  have hlen := hsW_length (G := G) hw hwl
  rw [hp]
  -- Whether an h is left.
  refine VP.assoc (VP.seq (G := fun σ s => St G (gCfg c G w HL k) X σ s ∧
      isa.eval .eq s = some (decide (HL - k * G.pLen < G.pLen)))
    (ltF_vp (c := fun _ => gCfg c G w HL k) (x := BitVec.ofNat 32 (HL - k * G.pLen)) (fun σ s h => h.1)
      (by decide) (by decide) hp16 (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fHLeft, fG]))
      fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by
        rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]⟩) ?_)
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- An h: `gStep`, then the next.
    have hi : k * G.pLen + G.pLen ≤ HL := by have := kL (k + 1) hkM; rwa [Nat.succ_mul] at this
    have e0 : decide (HL - k * G.pLen < G.pLen) = false := decide_eq_false (by omega_arith)
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega_arith⟩
    rw [hm] at hc; simp only [gCount] at hc
    have hbl : G.pLen ≤ ((hsW G w HL).drop (k * G.pLen)).length := by
      simp only [List.length_drop, hlen]; omega_arith
    have hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL hbl
    have cstep := VG.Proof.Dsa.Generation.generatorCount_chunks_step (p := pv) (q := qv) hpL hbl
    rw [hsW_take hi, List.drop_drop] at hstep cstep
    simp only [VG.Proof.Dsa.powMod_eq, ← hev'] at hstep cstep
    have stepVP := gStep_vp (c := gCfg c G w HL k) (X := X) (i := w + k * G.pLen) certs ok hp hlq hn hpm hpb hpe
      hpr hctx he4 he0 hP hPv hE hEv hM hMv hO hOv hHl hTl hGl hkls hpodd hp1 hplt hev hcl (by simp)
      (by simp [upd, fH, fHLeft, fG]) (by omega_arith) hwl
    have notLeft : ∀ σ s, ¬((St G (gCfg c G w HL k) X σ s ∧
        isa.eval .eq s = some (decide (HL - k * G.pLen < G.pLen))) ∧
        isa.eval .eq s = some true) := fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    have eH : G.wit + BitVec.ofNat 32 (w + k * G.pLen) + BitVec.ofNat 32 G.pLen =
        G.wit + BitVec.ofNat 32 (w + (k + 1) * G.pLen) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul, Nat.add_assoc]
    by_cases hok : gOk G pv ev (w + k * G.pLen)
    · -- It gives g: done.
      have r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega_arith
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
      refine cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      simp only [gFin, some0, num0]
      exact (h.of_rest R mm).mono (gV hfH hfL (fun o ho => by simp [ho]) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3])
        (by simp) (by simp [upd, fH, fHLeft, fG]) (by simp) (by simp [upd, fH, fHLeft, fG, eH]))
        (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · -- It does not: the next h.
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)] at hc
      have rpos : 0 < r := by have := gCount_gt G w pv ev m (k + 1); omega_arith
      have hNr : N - r = k + 1 := by omega_arith
      have hG1 : gOut (gCfg c G w HL k) G (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen))) pv ev =
          gCfg c G w HL k := by
        simp only [gOut]; exact ite_eq_right_of_eq_false _ _ (eq_false hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      have eL : BitVec.ofNat 32 (HL - k * G.pLen) - BitVec.ofNat 32 G.pLen =
          BitVec.ofNat 32 (HL - (k + 1) * G.pLen) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega_arith
      refine cmpF_vp (x := BitVec.ofNat 32 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega_arith), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega_arith, by omega_arith, by rw [hMM, show M - (k + 1) = m by omega_arith]; exact hc, ?_, ?_⟩,
        ?_, x⟩
      · rw [← hres]; simp only [gRes, gCands]
        rw [hstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]
      · rw [← hnum]; simp only [gNum, gCands]
        rw [cstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]; omega_arith
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
  · -- Fewer than `p_len` octets left: `fG` := 2.
    have hkM' : k = M := by omega_arith
    subst hkM'
    have r0 : r = 0 := by simp only [Nat.sub_self, gCount] at hc; omega_arith
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
    refine VP.seq (G := St G ((gCfg c G w HL k).setV fG (BitVec.ofNat 32 2)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => gCfg c G w HL k) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G w HL k).setV fG (BitVec.ofNat 32 2)) (x := BitVec.ofNat 32 2)
      (fun σ s h => h.1) (by decide)
      (by decide) (by decide) (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨h, x⟩ R mm e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    simp only [gFin, none0, num0]
    exact (h.of_rest R mm).mono (gV hfH hfL (by simp_all) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3]) (by simp)
      (by simp [upd]) (by simp) (by simp [upd, fH, fHLeft, fG])) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)

/-- The search for g over the window of `HL` octets at `w`. -/
theorem gPart_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c : Cfg} {pv ev qv w HL : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG) (hS : fHs ∈ c.LS) (hSv : c.V fHs = G.wit + BitVec.ofNat 32 w)
    (hL : fHsLen ∈ c.LS) (hLv : c.V fHsLen = BitVec.ofNat 32 HL) (hw : w + HL ≤ G.witLen)
    (hwl : G.witB.length = G.witLen) (h32 : HL < 2 ^ 32) (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS)
    (hev' : ev = (pv - 1) / qv) :
    VP (St G c X) g.gPart (St G (gFin c G w HL pv qv) X) := by
  unfold Geo.gPart
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r1 = G.wit + BitVec.ofNat 32 w)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hS).trans hSv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  have hHs : fHsLen ∈ (c.setV fH (G.wit + BitVec.ofNat 32 w)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := St G (c.setV fH (G.wit + BitVec.ofNat 32 w)) X)
    (st_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩) ?_
  refine VP.seq (G := fun σ s => St G (c.setV fH (G.wit + BitVec.ofNat 32 w)) X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 HL)
    (ld_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 32 w)) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hHs).trans ((upd_ne (o := fH) _ (G.wit + BitVec.ofNat 32 w) (by decide)).trans hLv))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := St G ((c.setV fH (G.wit + BitVec.ofNat 32 w)).setV fHLeft (BitVec.ofNat 32 HL)) X)
    (st_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 32 w)) (fun σ s h => h.1.1) (by decide)
      (varOk_of (by decide)) fun σ s t ⟨⟨h, x⟩, r1⟩ h' _ => ⟨r1 ▸ h', x⟩) ?_
  have hN := gCount_gt G w pv ev (HL / G.pLen) 0
  generalize hNN : gCount G w pv ev (HL / G.pLen) 0 = N at hN
  refine VP.seq (G := gInv c G w HL pv ev qv N X N)
    (stImm_vp (c := fun _ => (c.setV fH (G.wit + BitVec.ofNat 32 w)).setV fHLeft (BitVec.ofNat 32 HL))
      (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ =>
        ⟨⟨Nat.le_refl _, by simp, by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self],
          by rw [Nat.sub_self, Nat.zero_add]⟩, by simpa [gCfg] using h', h.2⟩) ?_
  rw [show N = N - 1 + 1 by omega_arith]
  exact VP.loop (I := gInv c G w HL pv ev qv (N - 1 + 1) X)
    (gBody_vp certs ok hp hlq hn hpm hpb hpe hpr hctx he4 he0 hP hPv hE hEv hM hMv hO hOv hHl hTl hGl hkls hpodd
      hp1 hplt hev hcl hw hwl h32 hfH hfL hev') _

end

end VG.Proof.Dsa.Arm.Gen
