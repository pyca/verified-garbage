module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `MlDsa.PPC64LE.Round.Bits`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`

Both are a comparison of `γ₂` with `(q - 1)/32` (`gSel`), which branches to
the loop for that `γ₂` (`sel_ok`); each loop is proven for any `γ₂` in
`gamma2s` (`loop_ok`), with one symbolic execution of its body for any
pointers (`hbBody_ok`, `lbBody_ok`), and an invariant saying which
coefficients of `out` are done (`Inv`). The values are `hbv_toNat` and, for
`lowBits`, `fixk_diff` with `lowBits_val`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Round.Bits

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Round
open VG.Impl.MlKem.PPC64LE (fixup)
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW polyAt_val polyIs_of_toNat natPolyIs_of_toNat
  map_get coeffAt_frame highBits_eq lowBits_val mem_gamma2s hbF hbM hbF_le hbM_mul reduced_zero)
open VG.Proof.MlDsa.PPC64LE.Round
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ)

/-! ## The loop bodies -/

/-- The registers the loops keep: `r4` and `r7` (`k4`, `k7`) and the
constants of `Decompose`. -/
structure K (g : Nat) (k4 k7 : BitVec 64) (s : State) : Prop where
  r4 : s.gpr .r4 = k4
  r7 : s.gpr .r7 = k7
  r10 : s.gpr .r10 = BitVec.ofNat 64 (dMul g)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (dAdd g)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (dMod g)

/-- What an iteration does, for the value stored. -/
def Step (s : State) (x z c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r3 = x + 4 ∧ s'.gpr .r5 = z + 4 ∧ s'.gpr .r6 = c - 1 ∧
    (∀ r ∈ [Reg.r4, .r7, .r10, .r11, .r12], s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem.writeW z v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem dMod_le (g : Nat) : dMod g ≤ 32768 := by unfold dMod; split <;> decide

section
variable {g : Nat} {s : State} {x z c : BitVec 64} (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = z) (h6 : s.gpr .r6 = c)
  (h10 : s.gpr .r10 = BitVec.ofNat 64 (dMul g)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (dAdd g))
  (h12 : s.gpr .r12 = BitVec.ofNat 64 (dMod g))
  (ia : InRegions (s.rd ++ s.wr) x 4) (oc : InRegions s.wr z 4)
include h3 h5 h6 h10 h11 h12 ia oc

theorem hbBody_ok :
    WP isa (.block (hbBody g)) s (Step s x z c ((hbv g ((s.mem.readW x 32).setWidth 64)).setWidth 32)) := by
  have hS := dShift_lt g
  have hM := dMod_le g
  crun [hbBody, hb, hbRaw, fixup, Step, hbv, hbr, fixk, h3, h5, h6, h10, h11, h12, ia, oc, hS, hM, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem lbBody_ok (h4 : s.gpr .r4 = BitVec.ofNat 64 (2 * g)) (h7 : s.gpr .r7 = 8380417) :
    WP isa (.block (lbBody g)) s (Step s x z c ((fixk 8380417 ((s.mem.readW x 32).setWidth 64 -
      hbv g ((s.mem.readW x 32).setWidth 64) * BitVec.ofNat 64 (2 * g))).setWidth 32)) := by
  have hS := dShift_lt g
  have hM := dMod_le g
  crun [lbBody, hb, hbRaw, fixup, Step, hbv, hbr, fixk, h3, h4, h5, h6, h7, h10, h11, h12, ia, oc, hS, hM,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev R : Addr := s₀.gpr .r3
abbrev O : Addr := s₀.gpr .r5
abbrev G : BitVec 32 := (s₀.gpr .r4).setWidth 32

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (R s₀)]
  wr : s₀.wr = [pR (O s₀)]
  disj : (pR (R s₀)).Disjoint (pR (O s₀))
  fitR : (R s₀).toNat + 1024 ≤ 2 ^ 64
  fitO : (O s₀).toNat + 1024 ≤ 2 ^ 64
  g : (G s₀).toNat ∈ gamma2s
  red : Reduced s₀.mem (R s₀)

/-- After `i` iterations, writing `out j` to coefficient `j` of `out`. -/
structure Inv (g : Nat) (k4 k7 : BitVec 64) (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = R s₀ + BitVec.ofNat 64 (4 * i)
  r5 : s.gpr .r5 = O s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (256 - i)
  k : K g k4 k7 s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (O s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, j < i → coeffAt s.mem (O s₀) j = out j

theorem inv_step {g : Nat} {k4 k7 : BitVec 64} {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < 256) {s : State} (h : Inv g k4 k7 out s₀ i s) {body : List Instr} {f : BitVec 64 → BitVec 32}
    (hb : ∀ {x z c : BitVec 64}, s.gpr .r3 = x → s.gpr .r5 = z → s.gpr .r6 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions s.wr z 4 →
      WP isa (.block body) s (Step s x z c (f ((s.mem.readW x 32).setWidth 64))))
    (hv : f ((coeffAt s₀.mem (R s₀) i).setWidth 64) = out i) :
    WP isa (.block body) s fun s' => Inv g k4 k7 out s₀ (i + 1) s' ∧ (s'.gpr .r6 != 0) = decide (i + 1 ≠ 256) := by
  have cR := coeff_contains (R s₀) (i := i) hi
  have cO := coeff_contains (O s₀) (i := i) hi
  have er : s.mem.readW (R s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (R s₀) i :=
    coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj) hi
  refine WP.mono (hb h.r3 h.r5 h.r6 ?_ ?_)
    fun s' ⟨r3, r5, r6, kp, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cR⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cO⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r5]; exact ptr_succ _ 4 i
  · rw [r6]; exact count_sub hi
  · have := h.k
    exact ⟨(kp .r4 (by simp)).trans this.r4, (kp .r7 (by simp)).trans this.r7, (kp .r10 (by simp)).trans this.r10,
      (kp .r11 (by simp)).trans this.r11, (kp .r12 (by simp)).trans this.r12⟩
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cO
  · intro j hj hji
    rw [m, show O s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (O s₀) i from rfl, coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, er, hv]
    · rw [ite_eq_right e]; exact h.coeff j hj (by omega_using [hji, e])
  · rw [r6, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-- The loop, from the state after its constants are loaded. -/
theorem loop_ok {g : Nat} {k4 k7 : BitVec 64} {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {body : List Instr}
    {f : BitVec 64 → BitVec 32}
    (hb : ∀ i < 256, ∀ s, Inv g k4 k7 out s₀ i s → ∀ {x z c : BitVec 64}, s.gpr .r3 = x → s.gpr .r5 = z →
      s.gpr .r6 = c → InRegions (s.rd ++ s.wr) x 4 → InRegions s.wr z 4 →
      WP isa (.block body) s (Step s x z c (f ((s.mem.readW x 32).setWidth 64))))
    (hv : ∀ i < 256, f ((coeffAt s₀.mem (R s₀) i).setWidth 64) = out i) {s : State} (h0 : Inv g k4 k7 out s₀ 0 s) :
    WP isa (.loop (.block body) (.nonzero .d .r6)) s (Inv g k4 k7 out s₀ 256) :=
  wp_loop_nz (Inv g k4 k7 out s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hb i hi s h) (hv i hi)) (fun _ h => h) h0

/-! ## The selection of `γ₂` -/

theorem g_cases' (x : BitVec 64) :
    ((x - BitVec.ofNat 64 261888).setWidth 32 == 0) = decide ((x.setWidth 32).toNat = g32) := by
  have hiff : (x - BitVec.ofNat 64 261888).setWidth 32 = 0 ↔ (x.setWidth 32).toNat = g32 := by
    rw [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
      show (0 : BitVec 32).toNat = 0 from rfl, BitVec.toNat_setWidth, g32]
    omega_using []
  by_cases hc : (x.setWidth 32).toNat = g32
  · rw [decide_eq_true hc, beq_iff_eq.mpr (hiff.mpr hc)]
  · rw [decide_eq_false hc]
    exact beq_false_of_ne fun e => hc (hiff.mp e)

/-- The registers after `gSel rg`. -/
def selGpr (rg : Reg) (f : Reg → BitVec 64) (r : Reg) : BitVec 64 :=
  if r = .r0 then f rg - BitVec.ofNat 64 261888 else if r = .r7 then BitVec.ofNat 64 261888 else f r

/-- `gSel rg`. -/
theorem gsel_wp {rg : Reg} (hrg : rg ≠ .r0 ∧ rg ≠ .r7) (s₀ : State) :
    WP isa (.block (gSel rg)) s₀ fun s => s.gpr = selGpr rg s₀.gpr ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧
      s.wr = s₀.wr ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr := by
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons exec_sub (wp_nil ⟨?_, rfl, rfl, rfl, rfl, rfl⟩)))
  have e7 : ((BitVec.ofNat 16 (261888 / 65536) ++ (0 : BitVec 16)).signExtend 64 |||
      (BitVec.ofNat 16 (261888 % 65536)).setWidth 64) = BitVec.ofNat 64 261888 :=
    VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val (by decide)
  funext r
  simp only [State.write, selGpr, hrg.2, ite_false, ite_true, e7]
  by_cases h0 : r = .r0
  · subst h0; simp
  · by_cases h7 : r = .r7
    · subst h7; simp
    · simp [h0, h7]

/-- `gSel rg`, then the loop for `γ₂`. -/
theorem sel_ok' {rg : Reg} (hrg : rg ≠ .r0 ∧ rg ≠ .r7) {s₀ : State}
    (hg : ((s₀.gpr rg).setWidth 32).toNat ∈ gamma2s) {th el : Prog isa} {Q : State → Prop}
    (h : ∀ g ∈ gamma2s, ((s₀.gpr rg).setWidth 32).toNat = g → ∀ s, s.gpr = selGpr rg s₀.gpr →
      s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr → s.sp = s₀.sp → s.lr = s₀.lr →
      WP isa (if g = g32 then th else el) s Q) :
    WP isa (.seq (.block (gSel rg)) (.ite (.zero .w .r0) th el)) s₀ Q := by
  refine WP.seq (WP.mono (gsel_wp hrg s₀) fun s ⟨hgpr, hm, hrd, hwr, hsp, hlr⟩ => ?_)
  refine WP.ite (decide (((s₀.gpr rg).setWidth 32).toNat = g32)) ?_ (fun hb => ?_) (fun hb => ?_)
  · show VG.PPC64LE.eval (.zero .w .r0) _ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, hgpr, selGpr, ite_true]
    rw [g_cases']
  · have e : ((s₀.gpr rg).setWidth 32).toNat = g32 := of_decide_eq_true hb
    have := h g32 (by rw [← e]; exact hg) e s hgpr hm hrd hwr hsp hlr
    rwa [ite_eq_left rfl] at this
  · have e : ((s₀.gpr rg).setWidth 32).toNat ≠ g32 := of_decide_eq_false hb
    have e88 : ((s₀.gpr rg).setWidth 32).toNat = g88 := by
      rcases mem_gamma2s hg with e' | e'
      · exact e'
      · exact absurd e' e
    have := h g88 (by rw [← e88]; exact hg) e88 s hgpr hm hrd hwr hsp hlr
    rwa [ite_eq_right (show g88 ≠ g32 by decide)] at this

/-- `gSel .r4`, then the loop for `γ₂`. -/
theorem sel_ok {s₀ : State} (hp : Pre s₀) {th el : Prog isa} {Q : State → Prop}
    (h : ∀ g ∈ gamma2s, (G s₀).toNat = g → ∀ s, s.gpr = selGpr .r4 s₀.gpr →
      s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr → s.sp = s₀.sp → s.lr = s₀.lr →
      WP isa (if g = g32 then th else el) s Q) :
    WP isa (.seq (.block (gSel .r4)) (.ite (.zero .w .r0) th el)) s₀ Q :=
  sel_ok' (by decide) hp.g h

/-! ## Constant time -/

/-- `gSel rg` and the branch to one of two loops are constant time when the
loops are, with the registers `rs` public, and the contract makes `rs`, the
stack pointer and the low word of `rg` (`γ₂`) public. -/
theorem sel_ct {rg : Reg} (hrg : rg ≠ .r0 ∧ rg ≠ .r7) (rs : List Reg) (hrs : Reg.r0 ∉ rs ∧ Reg.r7 ∉ rs)
    {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (s₁.gpr rg).setWidth 32 = (s₂.gpr rg).setWidth 32)
    {th el : Prog isa} {h₁ h₂ : VG.Taint.Hint VG.PPC64LE.taint.T}
    (ht : (VG.PPC64LE.taint.check (Taint.ofRegs rs) th h₁).isSome = true)
    (he : (VG.PPC64LE.taint.check (Taint.ofRegs rs) el h₂).isSome = true)
    {h₀ : VG.Taint.Hint VG.PPC64LE.taint.T}
    (hs : (VG.PPC64LE.taint.check (Taint.ofRegs []) (.block (gSel rg)) h₀).isSome = true) :
    ConstantTime isa pre pub (.seq (.block (gSel rg)) (.ite (.zero .w .r0) th el)) := by
  let F : State → State → Prop := fun σ s => s.gpr = selGpr rg σ.gpr ∧ s.sp = σ.sp
  let P : State → State → Prop := fun s₁ s₂ => pre s₁ ∧ pre s₂ ∧ pub s₁ s₂
  have h1 : RelCT isa P (.block (gSel rg)) fun s₁' s₂' => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ s₁' ∧ F σ₂ s₂' :=
    RelCT.wpDep (RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs []) (fun s₁ s₂ hp =>
        ⟨(hpub _ _ hp.2.2).2.1, fun r hr => absurd (Taint.mem_ofRegs.mp hr) (by simp)⟩) hs)
      (fun s₁ s₂ _ => ⟨WP.mono (gsel_wp hrg s₁) fun s h => ⟨h.1, h.2.2.2.2.1⟩,
        WP.mono (gsel_wp hrg s₂) fun s h => ⟨h.1, h.2.2.2.2.1⟩⟩)
  have agree : ∀ s₁ s₂, (True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ s₁ ∧ F σ₂ s₂) →
      VG.PPC64LE.taint.Agree (Taint.ofRegs rs) s₁ s₂ := by
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨g₁, p₁⟩, ⟨g₂, p₂⟩⟩
    obtain ⟨hr, hsp, -⟩ := hpub _ _ hp.2.2
    refine ⟨by rw [p₁, p₂, hsp], fun r hr' => ?_⟩
    have hr' := Taint.mem_ofRegs.mp hr'
    have : r ≠ .r0 ∧ r ≠ .r7 := ⟨fun e => hrs.1 (e ▸ hr'), fun e => hrs.2 (e ▸ hr')⟩
    rw [g₁, g₂]
    simp only [selGpr, this.1, this.2, ite_false]
    exact hr r hr'
  refine RelCT.constantTime (RelCT.seq h1 (RelCT.ite (fun s₁ s₂ h => ?_)
    ((RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs) (fun s₁ s₂ h => agree _ _ h.1) ht))
    ((RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs) (fun s₁ s₂ h => agree _ _ h.1) he))))
  obtain ⟨-, σ₁, σ₂, hp, ⟨g₁, -⟩, ⟨g₂, -⟩⟩ := h
  obtain ⟨-, -, hg⟩ := hpub _ _ hp.2.2
  show VG.PPC64LE.eval (.zero .w .r0) s₁ = VG.PPC64LE.eval (.zero .w .r0) s₂
  simp only [VG.PPC64LE.eval, State.read, Size.bits, g₁, g₂, selGpr, ite_true]
  rw [g_cases', g_cases', hg]

/-! ## The loops' constants -/

theorem dMul_lt (g : Nat) : dMul g < 2 ^ 31 ∧ dAdd g < 2 ^ 31 ∧ dMod g < 2 ^ 15 := by
  unfold dMul dAdd dMod; split <;> decide

/-- The registers after `hbConsts g`. -/
def kgpr (g : Nat) (f : Reg → BitVec 64) (r : Reg) : BitVec 64 :=
  if r = .r12 then BitVec.ofNat 64 (dMod g) else if r = .r11 then BitVec.ofNat 64 (dAdd g)
  else if r = .r10 then BitVec.ofNat 64 (dMul g) else f r

/-- What `hbConsts g` leaves, before the rest of a loop's head. -/
theorem consts_ok {g : Nat} {rest : List Instr} {s : State} {Q : State → Prop}
    (hx : WP isa (.block rest) ({ s with gpr := kgpr g s.gpr }) Q) :
    WP isa (.block (hbConsts g ++ rest)) s Q := by
  obtain ⟨b1, b2, b3⟩ := dMul_lt g
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons exec_lis (WP.cons exec_ori
    (WP.cons (exec_li b3) ?_))))
  refine (congrArg (fun t => WP isa (.block rest) t Q) ?_).mp hx
  cases s
  simp only [State.write, State.mk.injEq, and_true]
  funext r
  unfold kgpr
  by_cases h12 : r = .r12
  · subst h12; simp
  · by_cases h11 : r = .r11
    · subst h11; simpa using (VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val b2).symm
    · by_cases h10 : r = .r10
      · subst h10; simpa using (VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val b1).symm
      · simp [h12, h11, h10]

/-- What the head of a loop leaves: `hbConsts g`, then `extra`, then the count. -/
theorem head_ok {g : Nat} {extra : List Instr} {s : State} {Q : State → Prop}
    (hx : WP isa (.block (extra ++ [Instr.li .r6 256])) ({ s with gpr := kgpr g s.gpr }) Q) :
    WP isa (.block (hbConsts g ++ extra ++ [Instr.li .r6 256])) s Q := by
  rw [List.append_assoc]; exact consts_ok hx

end VG.Proof.MlDsa.PPC64LE.Round.Bits

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_high_bits` and `vg_mldsa_low_bits` against their contracts

The selection of `γ₂` (`sel_ok`), the head of the loop for it (`head_ok`),
the loop (`loop_ok`) with the values `hbv_toNat` (`highBits_eq`) and
`fixk_diff` (`lowBits_val`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Round.HighLow

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Round
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (polyAt_val natPolyIs_of_toNat polyIs_of_toNat map_get highBits_eq lowBits_val mem_gamma2s
  hbF hbM hbF_le hbM_mul reduced_zero)
open VG.Proof.MlDsa.PPC64LE.Round
open VG.Proof.MlDsa.PPC64LE.Round.Bits

/-! ## Values -/

/-- A reduced coefficient, as loaded: its value. -/
theorem load_toNat {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < 256) :
    ((coeffAt m p i).setWidth 64).toNat = ((polyAt m p)[i]!).val ∧ ((coeffAt m p i).setWidth 64).toNat < q := by
  have := polyAt_val hr (i := i) hi
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (coeffAt m p i).isLt; omega_arith)]
  exact ⟨this.symm, hr i hi⟩

/-- The value `highBits` stores for coefficient `j`. -/
def hbOut (g : Nat) (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (R s₀)).map fun c => (highBits g c).toNat)[j]!)

/-- The value `lowBits` stores for coefficient `j`. -/
def lbOut (g : Nat) (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (R s₀)).map fun c => ofInt (lowBits g c))[j]!).val

theorem hb_lt {g : Nat} (hg : g ∈ gamma2s) (a : Nat) : hbF g a % hbM g < 64 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide))
    (by rcases mem_gamma2s hg with rfl | rfl <;> decide)

theorem hbOut_toNat {g : Nat} (hg : g ∈ gamma2s) (s₀ : State) {j : Nat} (hj : j < 256) :
    (hbOut g s₀ j).toNat = ((polyAt s₀.mem (R s₀)).map fun c => (highBits g c).toNat)[j]! := by
  rw [hbOut, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [map_get _ _ hj, highBits_eq hg, Int.toNat_natCast]
  exact Nat.lt_trans (hb_lt hg _) (by decide)

theorem lbOut_toNat (g : Nat) (s₀ : State) {j : Nat} :
    (lbOut g s₀ j).toNat = (((polyAt s₀.mem (R s₀)).map fun c => ofInt (lowBits g c))[j]!).val := by
  rw [lbOut, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (Fin.isLt _) (by decide)

theorem hb_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    (hbv g ((coeffAt s₀.mem (R s₀) i).setWidth 64)).setWidth 32 = hbOut g s₀ i := by
  obtain ⟨e, hq⟩ := load_toNat hp.red hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, hbv_toNat hg hq, hbOut_toNat hg s₀ hi, map_get _ _ hi, highBits_eq hg,
    Int.toNat_natCast, e]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (hb_lt hg _) (by decide))

theorem lb_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    (fixk 8380417 ((coeffAt s₀.mem (R s₀) i).setWidth 64 -
      hbv g ((coeffAt s₀.mem (R s₀) i).setWidth 64) * BitVec.ofNat 64 (2 * g))).setWidth 32 = lbOut g s₀ i := by
  obtain ⟨e, hq⟩ := load_toNat hp.red hi
  generalize hA : (coeffAt s₀.mem (R s₀) i).setWidth 64 = A at e hq
  have hm := hbM_mul hg
  have hlt : hbF g A.toNat % hbM g < hbM g := Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have hb : (hbv g A * BitVec.ofNat 64 (2 * g)).toNat = hbF g A.toNat % hbM g * (2 * g) := by
    rw [BitVec.toNat_mul, hbv_toNat hg hq, BitVec.toNat_ofNat]
    have : g ≤ 261888 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
    rw [Nat.mod_eq_of_lt (by omega_arith : 2 * g < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hlt))
      (by rw [hm]; rw [VG.Proof.MlDsa.Round.q_eq]; decide))
  have hbq : hbF g A.toNat % hbM g * (2 * g) ≤ q := by
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt hlt); omega_arith
  have := fixk_diff (k := 8380417) (by decide) (a := A) (b := hbv g A * BitVec.ofNat 64 (2 * g))
    (by rw [VG.Proof.MlDsa.Round.q_eq] at hq; omega_arith) (by rw [hb]; rw [VG.Proof.MlDsa.Round.q_eq] at hbq; omega_arith)
    (by rw [hb]; rw [VG.Proof.MlDsa.Round.q_eq] at hbq; omega_arith)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, show (8380417 : BitVec 64) = BitVec.ofNat 64 8380417 from rfl, this, lbOut_toNat,
    map_get _ _ hi, lowBits_val hg, ← e, hb, VG.Proof.MlDsa.Round.q_eq]
  rw [VG.Proof.MlDsa.Round.q_eq] at hbq hq
  split <;> exact Nat.mod_eq_of_lt (by omega_arith)

/-! ## The functions -/

/-- What the functions leave. -/
def Post (out : Nat → BitVec 32) (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧ ∀ j < 256, coeffAt s.mem (O s₀) j = out j

theorem kgpr_pres {g : Nat} {s₀ s : State}
    (hgpr : s.gpr = selGpr .r4 s₀.gpr) :
    ∀ r ∈ preserved, ((({ s with gpr := kgpr g s.gpr } : State).write .r6 (BitVec.ofNat 64 256)).gpr r) = s₀.gpr r := by
  intro r hr
  have : r ≠ .r0 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert r hr; decide
  simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
    this.2.2.2.2.2]

theorem high_correct {s₀ : State} (hp : Pre s₀) : WP isa highBits s₀ (Post (hbOut (G s₀).toNat s₀) s₀) := by
  refine sel_ok hp fun g hg hG s hgpr hm hrd hwr hsp hlr => ?_
  have e : (if g = g32 then hbLoop g32 else hbLoop g88) = hbLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e, hG]
  refine WP.seq (head_ok (extra := []) (WP.cons (exec_li (by decide)) (wp_nil ?_)))
  refine WP.mono (loop_ok (g := g) (k4 := s₀.gpr .r4) (k7 := BitVec.ofNat 64 261888)
    (f := fun a => (hbv g a).setWidth 32) hp
    (fun i hi s h x z c h3 h5 h6 ia oc => hbBody_ok h3 h5 h6 h.k.r10 h.k.r11 h.k.r12 ia oc)
    (fun i hi => hb_val hg hp hi) ?_)
    fun s' h' => ⟨h'.pres, h'.sp, h'.lr, fun j hj => h'.coeff j hj hj⟩
  refine ⟨?_, ?_, by simp [State.write], ⟨?_, ?_, ?_, ?_, ?_⟩, hrd, hwr, hsp, hlr, kgpr_pres hgpr,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega_arith)⟩ <;>
    simp [State.write, kgpr, hgpr, selGpr]

theorem low_correct {s₀ : State} (hp : Pre s₀) : WP isa lowBits s₀ (Post (lbOut (G s₀).toNat s₀) s₀) := by
  refine sel_ok hp fun g hg hG s hgpr hm hrd hwr hsp hlr => ?_
  have e : (if g = g32 then lbLoop g32 else lbLoop g88) = lbLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e, hG]
  have b2 : 2 * g < 2 ^ 31 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold lbLoop
  rw [show hbConsts g ++ loadImm .r4 (2 * g) ++ loadQ .r7 ++ [Instr.li .r6 256] =
    hbConsts g ++ (loadImm .r4 (2 * g) ++ loadQ .r7) ++ [Instr.li .r6 256] by simp]
  refine WP.seq (head_ok (WP.cons exec_lis (WP.cons exec_ori (WP.cons exec_lis (WP.cons exec_ori
    (WP.cons (exec_li (by decide)) (wp_nil ?_)))))))
  refine WP.mono (loop_ok (g := g) (k4 := BitVec.ofNat 64 (2 * g)) (k7 := 8380417)
    (f := fun a => (fixk 8380417 (a - hbv g a * BitVec.ofNat 64 (2 * g))).setWidth 32) hp
    (fun i hi s h x z c h3 h5 h6 ia oc => lbBody_ok h3 h5 h6 h.k.r10 h.k.r11 h.k.r12 ia oc h.k.r4 h.k.r7)
    (fun i hi => lb_val hg hp hi) ?_)
    fun s' h' => ⟨h'.pres, h'.sp, h'.lr, fun j hj => h'.coeff j hj hj⟩
  have e4 := VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val b2
  have e7 := VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val (v := 8380417) (by decide)
  refine ⟨?_, ?_, by simp [State.write], ⟨?_, ?_, ?_, ?_, ?_⟩, hrd, hwr, hsp, hlr, fun r hr => ?_,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega_arith)⟩
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e4
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e7
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · have : r ≠ .r0 ∧ r ≠ .r4 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert r hr; decide
    simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2.1, this.2.2.2.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.highBitsContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pre_of_low {s : State} (h : (Proof.MlDsa.lowBitsContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 95232 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩]

theorem high_verified : Verified PPC64LE.target highBits (Proof.MlDsa.highBitsContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .r4) (by decide) [.r3, .r5] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := high_correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs]
    refine natPolyIs_of_toNat fun j hj => ?_
    rw [h.2.2.2 j hj]
    exact hbOut_toNat hp.g s hj
  · sig_pub [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, h.2.2.1⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

theorem low_verified : Verified PPC64LE.target lowBits (Proof.MlDsa.lowBitsContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .r4) (by decide) [.r3, .r5] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of_low hs
    obtain ⟨t, s', he, h⟩ := low_correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs]
    refine polyIs_of_toNat fun j hj => ?_
    rw [h.2.2.2 j hj]
    exact lbOut_toNat _ s
  · sig_pub [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, h.2.2.1⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Round.HighLow
