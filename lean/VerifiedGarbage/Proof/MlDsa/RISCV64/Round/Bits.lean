module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# ML-DSA on RISC-V: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`

As PPC64LE's (`Proof/MlDsa/PPC64LE/Round/Bits.lean`). Both are a comparison
of `γ₂` with `(q - 1)/32` (`gSel`, a `subw` of the low halves), which
branches to the loop for that `γ₂` (`sel_ok`); each loop is proven for any
`γ₂` in `gamma2s` (`loop_ok`), with one symbolic execution of its body for
any pointers (`hbBody_ok`, `lbBody_ok`), and an invariant saying which
coefficients of `out` are done (`Inv`). The values are `hbv_toNat` and, for
`lowBits`, `fixk_diff` with `lowBits_val`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.Bits

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Impl.MlDsa.RISCV64.Arith (loadImm hi20)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW polyAt_val polyIs_of_toNat natPolyIs_of_toNat
  map_get coeffAt_frame highBits_eq lowBits_val mem_gamma2s hbF hbM hbF_le hbM_mul reduced_zero)
open VG.Proof.MlDsa.RISCV64.Round
open VG.Proof.MlDsa.RISCV64.Arith (loadImm_val loadImm_imm sext32_beq_zero)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add)

/-! ## The loop bodies -/

/-- The registers the loops keep: `a1` and `a4` (`k4`, `k7`) and the
constants of `Decompose`. -/
structure K (g : Nat) (k4 k7 : BitVec 64) (s : State) : Prop where
  r4 : s.gpr .a1 = k4
  r7 : s.gpr .a4 = k7
  r10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)
  r11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g)
  r12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g)

/-- What an iteration does, for the value stored. -/
def Step (s : State) (x z c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a2 = z + 4 ∧ s'.gpr .a3 = c - 1 ∧
    (∀ r ∈ [Reg.a1, .a4, .a7, .t1, .t2], s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem.writeW z v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem dMod_le (g : Nat) : dMod g ≤ 44 := by unfold dMod; split <;> decide

section
variable {g : Nat} {s : State} {x z c : BitVec 64} (h3 : s.gpr .a0 = x) (h5 : s.gpr .a2 = z) (h6 : s.gpr .a3 = c)
  (h10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)) (h11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g))
  (h12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g))
  (ia : InRegions (s.rd ++ s.wr) x 4) (oc : InRegions s.wr z 4) (ax : x.toNat % 4 = 0) (az : z.toNat % 4 = 0)
include h3 h5 h6 h10 h11 h12 ia oc ax az

theorem hbBody_ok :
    WP isa (.block (hbBody g)) s (Step s x z c ((hbv g ((s.mem.readW x 32).setWidth 64)).setWidth 32)) := by
  have hS := dShift_lt g
  crun [hbBody, hb, hbRaw, fixup, Step, hbv, hbr, fixk, h3, h5, h6, h10, h11, h12, ia, oc, ax, az, hS,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem lbBody_ok (h4 : s.gpr .a1 = BitVec.ofNat 64 (2 * g)) (h7 : s.gpr .a4 = 8380417) :
    WP isa (.block (lbBody g)) s (Step s x z c ((fixk 8380417 ((s.mem.readW x 32).setWidth 64 -
      hbv g ((s.mem.readW x 32).setWidth 64) * BitVec.ofNat 64 (2 * g))).setWidth 32)) := by
  have hS := dShift_lt g
  crun [lbBody, hb, hbRaw, fixup, Step, hbv, hbr, fixk, h3, h4, h5, h6, h7, h10, h11, h12, ia, oc, ax, az, hS,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev R : Addr := s₀.gpr .a0
abbrev O : Addr := s₀.gpr .a2
abbrev G : BitVec 32 := (s₀.gpr .a1).setWidth 32

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (R s₀)]
  wr : s₀.wr = [pR (O s₀)]
  disj : (pR (R s₀)).Disjoint (pR (O s₀))
  fitR : (R s₀).toNat + 1024 ≤ 2 ^ 64
  fitO : (O s₀).toNat + 1024 ≤ 2 ^ 64
  g : (G s₀).toNat ∈ gamma2s
  red : Reduced s₀.mem (R s₀)
  alR : (R s₀).toNat % 4 = 0
  alO : (O s₀).toNat % 4 = 0

/-- After `i` iterations, writing `out j` to coefficient `j` of `out`. -/
structure Inv (g : Nat) (k4 k7 : BitVec 64) (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .a0 = R s₀ + BitVec.ofNat 64 (4 * i)
  r5 : s.gpr .a2 = O s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .a3 = BitVec.ofNat 64 (256 - i)
  k : K g k4 k7 s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (O s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, j < i → coeffAt s.mem (O s₀) j = out j

theorem inv_step {g : Nat} {k4 k7 : BitVec 64} {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < 256) {s : State} (h : Inv g k4 k7 out s₀ i s) {body : List Instr} {f : BitVec 64 → BitVec 32}
    (hb : ∀ {x z c : BitVec 64}, s.gpr .a0 = x → s.gpr .a2 = z → s.gpr .a3 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions s.wr z 4 → x.toNat % 4 = 0 → z.toNat % 4 = 0 →
      WP isa (.block body) s (Step s x z c (f ((s.mem.readW x 32).setWidth 64))))
    (hv : f ((coeffAt s₀.mem (R s₀) i).setWidth 64) = out i) :
    WP isa (.block body) s fun s' => Inv g k4 k7 out s₀ (i + 1) s' ∧ (s'.gpr .a3 != 0) = decide (i + 1 ≠ 256) := by
  have cR := coeff_contains (R s₀) (i := i) hi
  have cO := coeff_contains (O s₀) (i := i) hi
  have er : s.mem.readW (R s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (R s₀) i :=
    coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj) hi
  refine WP.mono (hb h.r3 h.r5 h.r6 ?_ ?_ (align4_add hp.alR i)
      (align4_add hp.alO i))
    fun s' ⟨r3, r5, r6, kp, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cR⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cO⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r5]; exact ptr_succ _ 4 i
  · rw [r6]; exact count_sub hi
  · have := h.k
    exact ⟨(kp .a1 (by simp)).trans this.r4, (kp .a4 (by simp)).trans this.r7, (kp .a7 (by simp)).trans this.r10,
      (kp .t1 (by simp)).trans this.r11, (kp .t2 (by simp)).trans this.r12⟩
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cO
  · intro j hj hji
    rw [m, show O s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (O s₀) i from rfl, coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, er, hv]
    · rw [ite_eq_right e]; exact h.coeff j hj (by omega)
  · rw [r6, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-- The loop, from the state after its constants are loaded. -/
theorem loop_ok {g : Nat} {k4 k7 : BitVec 64} {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {body : List Instr}
    {f : BitVec 64 → BitVec 32}
    (hb : ∀ i < 256, ∀ s, Inv g k4 k7 out s₀ i s → ∀ {x z c : BitVec 64}, s.gpr .a0 = x → s.gpr .a2 = z →
      s.gpr .a3 = c → InRegions (s.rd ++ s.wr) x 4 → InRegions s.wr z 4 → x.toNat % 4 = 0 → z.toNat % 4 = 0 →
      WP isa (.block body) s (Step s x z c (f ((s.mem.readW x 32).setWidth 64))))
    (hv : ∀ i < 256, f ((coeffAt s₀.mem (R s₀) i).setWidth 64) = out i) {s : State} (h0 : Inv g k4 k7 out s₀ 0 s) :
    WP isa (.loop (.block body) (.nonzero .a3)) s (Inv g k4 k7 out s₀ 256) :=
  wp_loop_nz (Inv g k4 k7 out s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hb i hi s h) (hv i hi)) (fun _ h => h) h0

/-! ## The selection of `γ₂` -/

/-- `t0` after `subw` of `γ₂`'s low half and `(q - 1)/32`. -/
def selV (x : BitVec 64) : BitVec 64 := sext32 (x.setWidth 32 - (261888 : BitVec 32))

theorem g_cases' (x : BitVec 64) : (selV x == 0) = decide ((x.setWidth 32).toNat = g32) := by
  have hiff : x.setWidth 32 - (261888 : BitVec 32) = 0 ↔ (x.setWidth 32).toNat = g32 := by
    rw [BitVec.toNat_eq, BitVec.toNat_sub, show (261888 : BitVec 32).toNat = 261888 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl, g32]
    have := (x.setWidth 32).isLt
    omega
  unfold selV
  rw [sext32_beq_zero]
  by_cases hc : (x.setWidth 32).toNat = g32
  · rw [decide_eq_true hc, beq_iff_eq.mpr (hiff.mpr hc)]
  · rw [decide_eq_false hc]
    exact beq_false_of_ne fun e => hc (hiff.mp e)

/-- The registers after `gSel rg`. -/
def selGpr (rg : Reg) (f : Reg → BitVec 64) (r : Reg) : BitVec 64 :=
  if r = .t0 then selV (f rg) else if r = .a4 then BitVec.ofNat 64 261888 else f r

theorem loadImm_g32 (r : Reg) : loadImm r 261888 = [.lui r 64, .addi r r (-256)] := by
  simp only [loadImm, hi20]; rfl

/-- `gSel rg`. -/
theorem gsel_wp {rg : Reg} (hrg : rg ≠ .t0 ∧ rg ≠ .a4) (s₀ : State) :
    WP isa (.block (gSel rg)) s₀ fun s => s.gpr = selGpr rg s₀.gpr ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧
      s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  simp only [gSel, loadImm_g32, List.cons_append, List.nil_append]
  refine Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (by decide)) (Steps.WP.cons exec_subw
    (WP.block_nil ⟨?_, rfl, rfl, rfl, rfl⟩)))
  have e7 : sext32 ((64 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 (-256) = BitVec.ofNat 64 261888 := by
    decide
  funext r
  simp only [State.write, selGpr, hrg.2, ite_false, ite_true, e7, selV]
  by_cases h0 : r = .t0
  · subst h0; simp
  · by_cases h7 : r = .a4
    · subst h7; simp
    · simp [h0, h7]

/-- `gSel rg`, then the loop for `γ₂`. -/
theorem sel_ok' {rg : Reg} (hrg : rg ≠ .t0 ∧ rg ≠ .a4) {s₀ : State}
    (hg : ((s₀.gpr rg).setWidth 32).toNat ∈ gamma2s) {th el : Prog isa} {Q : State → Prop}
    (h : ∀ g ∈ gamma2s, ((s₀.gpr rg).setWidth 32).toNat = g → ∀ s, s.gpr = selGpr rg s₀.gpr →
      s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr → s.sp = s₀.sp →
      WP isa (if g = g32 then th else el) s Q) :
    WP isa (.seq (.block (gSel rg)) (.ite (.zero .t0) th el)) s₀ Q := by
  refine WP.seq (WP.mono (gsel_wp hrg s₀) fun s ⟨hgpr, hm, hrd, hwr, hsp⟩ => ?_)
  refine WP.ite (decide (((s₀.gpr rg).setWidth 32).toNat = g32)) ?_ (fun hb => ?_) (fun hb => ?_)
  · show VG.RISCV64.eval (.zero .t0) _ = _
    simp only [VG.RISCV64.eval, hgpr, selGpr, ite_true]
    rw [g_cases']
  · have e : ((s₀.gpr rg).setWidth 32).toNat = g32 := of_decide_eq_true hb
    have := h g32 (by rw [← e]; exact hg) e s hgpr hm hrd hwr hsp
    rwa [ite_eq_left rfl] at this
  · have e : ((s₀.gpr rg).setWidth 32).toNat ≠ g32 := of_decide_eq_false hb
    have e88 : ((s₀.gpr rg).setWidth 32).toNat = g88 := by
      rcases mem_gamma2s hg with e' | e'
      · exact e'
      · exact absurd e' e
    have := h g88 (by rw [← e88]; exact hg) e88 s hgpr hm hrd hwr hsp
    rwa [ite_eq_right (show g88 ≠ g32 by decide)] at this

/-- `gSel .a1`, then the loop for `γ₂`. -/
theorem sel_ok {s₀ : State} (hp : Pre s₀) {th el : Prog isa} {Q : State → Prop}
    (h : ∀ g ∈ gamma2s, (G s₀).toNat = g → ∀ s, s.gpr = selGpr .a1 s₀.gpr →
      s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr → s.sp = s₀.sp →
      WP isa (if g = g32 then th else el) s Q) :
    WP isa (.seq (.block (gSel .a1)) (.ite (.zero .t0) th el)) s₀ Q :=
  sel_ok' (by decide) hp.g h

/-! ## Constant time -/

/-- `gSel rg` and the branch to one of two loops are constant time when the
loops are, with the registers `rs` public, and the contract makes `rs`, the
stack pointer and the low word of `rg` (`γ₂`) public. -/
theorem sel_ct {rg : Reg} (hrg : rg ≠ .t0 ∧ rg ≠ .a4) (rs : List Reg) (hrs : Reg.t0 ∉ rs ∧ Reg.a4 ∉ rs)
    {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (s₁.gpr rg).setWidth 32 = (s₂.gpr rg).setWidth 32)
    {th el : Prog isa} {h₁ h₂ : VG.Taint.Hint VG.RISCV64.taint.T}
    (ht : (VG.RISCV64.taint.check (Taint.ofRegs rs) th h₁).isSome = true)
    (he : (VG.RISCV64.taint.check (Taint.ofRegs rs) el h₂).isSome = true)
    {h₀ : VG.Taint.Hint VG.RISCV64.taint.T}
    (hs : (VG.RISCV64.taint.check (Taint.ofRegs []) (.block (gSel rg)) h₀).isSome = true) :
    ConstantTime isa pre pub (.seq (.block (gSel rg)) (.ite (.zero .t0) th el)) := by
  let F : State → State → Prop := fun σ s => s.gpr = selGpr rg σ.gpr ∧ s.sp = σ.sp
  let P : State → State → Prop := fun s₁ s₂ => pre s₁ ∧ pre s₂ ∧ pub s₁ s₂
  have h1 : RelCT isa P (.block (gSel rg)) fun s₁' s₂' => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ s₁' ∧ F σ₂ s₂' :=
    RelCT.wpDep (RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs []) (fun s₁ s₂ hp =>
        ⟨(hpub _ _ hp.2.2).2.1, fun r hr => absurd (Taint.mem_ofRegs.mp hr) (by simp)⟩) hs)
      (fun s₁ s₂ _ => ⟨WP.mono (gsel_wp hrg s₁) fun s h => ⟨h.1, h.2.2.2.2⟩,
        WP.mono (gsel_wp hrg s₂) fun s h => ⟨h.1, h.2.2.2.2⟩⟩)
  have agree : ∀ s₁ s₂, (True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ s₁ ∧ F σ₂ s₂) →
      VG.RISCV64.taint.Agree (Taint.ofRegs rs) s₁ s₂ := by
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨g₁, p₁⟩, ⟨g₂, p₂⟩⟩
    obtain ⟨hr, hsp, -⟩ := hpub _ _ hp.2.2
    refine ⟨by rw [p₁, p₂, hsp], fun r hr' => ?_⟩
    have hr' := Taint.mem_ofRegs.mp hr'
    have : r ≠ .t0 ∧ r ≠ .a4 := ⟨fun e => hrs.1 (e ▸ hr'), fun e => hrs.2 (e ▸ hr')⟩
    rw [g₁, g₂]
    simp only [selGpr, this.1, this.2, ite_false]
    exact hr r hr'
  refine RelCT.constantTime (RelCT.seq h1 (RelCT.ite (fun s₁ s₂ h => ?_)
    ((RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs) (fun s₁ s₂ h => agree _ _ h.1) ht))
    ((RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs) (fun s₁ s₂ h => agree _ _ h.1) he))))
  obtain ⟨-, σ₁, σ₂, hp, ⟨g₁, -⟩, ⟨g₂, -⟩⟩ := h
  obtain ⟨-, -, hg⟩ := hpub _ _ hp.2.2
  show VG.RISCV64.eval (.zero .t0) s₁ = VG.RISCV64.eval (.zero .t0) s₂
  simp only [VG.RISCV64.eval, g₁, g₂, selGpr, ite_true, selV, hg]

/-! ## The loops' constants -/

theorem dMul_lt (g : Nat) : dMul g < 2 ^ 31 - 2048 ∧ dAdd g < 2 ^ 31 - 2048 ∧ dMod g < 2048 := by
  unfold dMul dAdd dMod; split <;> decide

/-- The registers after `hbConsts g`. -/
def kgpr (g : Nat) (f : Reg → BitVec 64) (r : Reg) : BitVec 64 :=
  if r = .t2 then BitVec.ofNat 64 (dMod g) else if r = .t1 then BitVec.ofNat 64 (dAdd g)
  else if r = .a7 then BitVec.ofNat 64 (dMul g) else f r

/-- What `hbConsts g` leaves, before the rest of a loop's head. -/
theorem consts_ok {g : Nat} {rest : List Instr} {s : State} {Q : State → Prop}
    (hx : WP isa (.block rest) ({ s with gpr := kgpr g s.gpr }) Q) :
    WP isa (.block (hbConsts g ++ rest)) s Q := by
  obtain ⟨b1, b2, b3⟩ := dMul_lt g
  simp only [hbConsts, loadImm, List.cons_append, List.nil_append]
  refine Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (loadImm_imm _)) (Steps.WP.cons exec_lui
    (Steps.WP.cons (exec_addi (loadImm_imm _)) (Steps.WP.cons (exec_li (by unfold imm12; omega)) ?_))))
  refine (congrArg (fun t => WP isa (.block rest) t Q) ?_).mp hx
  cases s
  simp only [State.write, State.mk.injEq, and_true]
  funext r
  unfold kgpr
  by_cases h12 : r = .t2
  · subst h12; simp
  · by_cases h11 : r = .t1
    · subst h11; simpa using (loadImm_val b2).symm
    · by_cases h10 : r = .a7
      · subst h10; simpa using (loadImm_val b1).symm
      · simp [h12, h11, h10]

/-- What the head of a loop leaves: `hbConsts g`, then `extra`, then the count. -/
theorem head_ok {g : Nat} {extra : List Instr} {s : State} {Q : State → Prop}
    (hx : WP isa (.block (extra ++ [Instr.li .a3 256])) ({ s with gpr := kgpr g s.gpr }) Q) :
    WP isa (.block (hbConsts g ++ extra ++ [Instr.li .a3 256])) s Q := by
  rw [List.append_assoc]; exact consts_ok hx

end VG.Proof.MlDsa.RISCV64.Round.Bits
