module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.BitPack
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Unpack
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.BitPack
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on RISC-V: `vg_mldsa_expand_mask_poly`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sample/ExpandMask.lean`). The function
runs in pieces: the prologue (`J0`, with `s7` = `gamma1`), the sponge, whose
output is `H(ρ′, 640)` (`T`), the branch on the low 32 bits of `γ₁`
(`Pack.sel`), and the loop of `vg_mldsa_bit_unpack` for
`c = 1 + bitlen (γ₁ - 1)` on the first `32c` bytes of output
(`Pack.unpackLoop_buFin_ok`, run from the state permitted only those bytes
and `a`, and widened to the function's permissions by
`RegionModel.wp_narrow`), which are `H(ρ′, 32c)` (`H_take`). It is constant
time: the blocks without memory accesses leak nothing, the sponge by
`sponge_ct`, the branch goes the same way in two runs whose `γ₁` agree, and
the loop by `Pack.unpackLoop_ct18` and `Pack.unpackLoop_ct20`, from the same
pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sample.ExpandMask

open VG VG.RISCV64
open VG.Proof.MlDsa.RISCV64.Sample
open VG.Impl.MlDsa.RISCV64.Sample
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.RISCV64.Sample (relct_wp)
open VG.Impl.MlDsa.RISCV64.Pack (unpackLoop buFin loadB sel)
open VG.Proof.MlDsa.RISCV64.Pack (RB loadBVal loadB_ok Shape loopRegs subwV lo_sub_beq selBlk_ok relct_noMem)
open VG.Spec.MlDsa (Zq q H toRq bitUnpack bitlen)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt rates)

/-- The call, from the entry state: `seed = a0`, `gamma1 = a1`, `a = a2`,
`scratch = a3`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .a0, 66, σ.gpr .a3, σ.gpr .a2⟩

/-- `γ₁`, the low 32 bits of `a1`. -/
abbrev gam (σ : State) : Nat := ((σ.gpr .a1).setWidth 32).toNat

/-- What the function writes, for the call `P`. -/
abbrev Out (P : Sp) (σ : State) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (P.msg σ) (32 * (1 + bitlen (gam σ - 1)))) (gam σ - 1) (gam σ))

/-- After the sponge. -/
structure T (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 640 = H (P.msg σ) 640
  s7 : s.gpr .s7 = σ.gpr .a1

/-- Before the loop of `BitUnpack` for `b = Bv`. -/
structure L (Bv : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 640 = H (P.msg σ) 640
  a7 : s.gpr .a7 = P.at' 840
  t1 : s.gpr .t1 = P.a
  rb : RB Bv s

/-- After the loop. -/
structure EDone (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : PolyIs s.mem P.a (Out P σ)

theorem preserved_not_loop : ∀ r ∈ preserved, r ∉ loopRegs := by decide

theorem loadQ_eq : Impl.MlDsa.RISCV64.Pack.loadQ = loadB .a4 8380417 := rfl

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The branch's block keeps `T`, and leaves `subw` of `γ₁` and `v` in `a6`. -/
theorem br_ok {v : Nat} (hl : loadBVal v = BitVec.ofNat 64 v) {s : State} (h : T P σ s) :
    WP isa (.block (loadB .a6 v ++ ([.subw .a6 .s7 .a6] : List Instr))) s fun s' =>
      T P σ s' ∧ s'.gpr .a6 = subwV (σ.gpr .a1) v := by
  refine WP.mono (Pack.WP.withSp (selBlk_ok .s7 (by decide) hl s)) fun s' ⟨⟨g, k, m⟩, sp⟩ => ?_
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    k.gpr (by rw [List.mem_singleton]; rintro rfl; exact absurd hr (by decide))
  exact ⟨⟨h.env.regs hp m gp k.2.1 k.2.2 sp, by rw [m]; exact h.out, (gp _ (by decide)).trans h.s7⟩,
    by rw [g, h.s7]⟩

/-- The loop's setup: the pointers, `q` and `b`. -/
theorem setup_ok {Bv : Nat} (hl : loadBVal Bv = BitVec.ofNat 64 Bv) {s : State} (h : T P σ s) :
    WP isa (.block (([.addi .a7 .s11 840, mov .t1 .s10] : List Instr) ++ Impl.MlDsa.RISCV64.Pack.loadQ ++
      loadB .a1 Bv)) s (L Bv P σ) := by
  have g10 := h.env.s10
  have g11 := h.env.s11
  have hk : WP isa (.block ([.addi .a7 .s11 840, mov .t1 .s10] : List Instr)) s fun s' =>
      s'.gpr .a7 = P.at' 840 ∧ s'.gpr .t1 = P.a ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    mrun [mov, g10, g11, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hk fun s₁ ⟨g7, gt1, gp, m, rd, wr, sp⟩ => ?_
  rw [WP.block_append_iff, loadQ_eq]
  refine WP.mono (Pack.WP.withSp (loadB_ok .a4 (by decide) s₁)) fun s₂ ⟨⟨⟨g4, m₂⟩, k₂⟩, sp₂⟩ => ?_
  refine WP.mono (Pack.WP.withSp (loadB_ok .a1 hl s₂)) fun s' ⟨⟨⟨g1, m'⟩, k⟩, sp'⟩ => ?_
  have m3 : s'.mem = s.mem := m'.trans (m₂.trans m)
  have gp' : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    (k.gpr (by rw [List.mem_singleton]; rintro rfl; exact absurd hr (by decide))).trans
      ((k₂.gpr (by rw [List.mem_singleton]; rintro rfl; exact absurd hr (by decide))).trans (gp r hr))
  refine ⟨h.env.regs hp m3 gp' (k.2.1.trans (k₂.2.1.trans rd)) (k.2.2.trans (k₂.2.2.trans wr))
      (sp'.trans (sp₂.trans sp)), by rw [m3]; exact h.out,
    (k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans g7),
    (k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans gt1), g1, (k.gpr (by decide)).trans g4⟩

omit hp in
/-- After the sponge, from its output and `γ₁` in `s7`. -/
theorem T.of {s₀ s : State} (h : J6 136 640 P σ s₀ s) (s7 : s₀.gpr .s7 = σ.gpr .a1) : T P σ s :=
  ⟨h.j0.env, by rw [h.out]; exact (H_eq _ _).symm, (h.gp .s7 (by decide)).trans s7⟩

/-- The loop of `BitUnpack` for `(Bv, d, c, nb)`, from its setup, run on the
first `32 d` bytes of the output and the polynomial `a` alone. -/
theorem loop_ok {Bv d c nb : Nat} (hs : Shape d c nb) (hB19 : Bv ≤ 2 ^ 19) (hd : bitlen (Bv - 1 + Bv) = d)
    (h32 : 32 * d ≤ 640) {s : State} (h : L Bv P σ s) :
    WP isa (unpackLoop buFin d c nb) s fun s' =>
      Env P σ s' ∧ PolyIs s'.mem P.a (toRq (bitUnpack (H (P.msg σ) (32 * d)) (Bv - 1) Bv)) := by
  have fs := hp.fscr
  have ewr : s.wr = [P.aR, P.scrR] := h.env.wr.trans hp.wr
  refine regionModel.wp_narrow (r := [⟨s.gpr .a7, 32 * d⟩]) (w := [⟨s.gpr .t1, 1024⟩])
    (Pack.unpackLoop_buFin_ok (a := Bv - 1) hs hB19 hd h.rb (List.mem_append_left _ (List.mem_singleton_self _))
      (List.mem_singleton_self _) ?_ (by show (s.gpr .t1).toNat % 4 = 0; rw [h.t1]; exact hp.alA)) ?_ ?_
    (by unfold unpackLoop; rfl) (.inl (by unfold unpackLoop; rfl)) (fun t s' he rd' wr' hf hq => ?_)
  · show Region.Disjoint ⟨s.gpr .a7, 32 * d⟩ ⟨s.gpr .t1, 1024⟩
    rw [h.a7, h.t1]
    exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 32 * d) (by omega))).symm
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨P.scrR, List.mem_append_right _ (by show _ ∈ s.wr; rw [ewr]; simp), 840, h.a7,
        by show 840 + 32 * d ≤ 2048; omega⟩
    · exact ⟨P.aR, List.mem_append_right _ (by show _ ∈ s.wr; rw [ewr]; simp), 0,
        by rw [h.t1]; exact (BitVec.add_zero _).symm, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨P.aR, by show _ ∈ s.wr; rw [ewr]; simp, 0, by rw [h.t1]; exact (BitVec.add_zero _).symm, by simp⟩
  obtain ⟨hpoly, -, hk⟩ := hq
  have sp' := (Exec.rdwr he).2.2
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => hk.1 r (preserved_not_loop r hr)
  refine ⟨h.env.step hp (rs := [P.aR]) (by rw [h.t1] at hf; exact hf) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h)) gp rd' wr' sp', ?_⟩
  have eb : bytesAt s.mem (P.at' 840) (32 * d) = H (P.msg σ) (32 * d) := by
    rw [← MlKem.bytesAt_take _ _ h32, h.out, H_take _ h32]
  have hpoly : PolyIs s'.mem (s.gpr .t1) (toRq (bitUnpack (bytesAt s.mem (s.gpr .a7) (32 * d)) (Bv - 1) Bv)) :=
    hpoly
  rw [h.t1, h.a7, eb] at hpoly
  exact hpoly

/-- The branch on `γ₁` and the loop. -/
theorem tail_ok (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) {s : State} (h : T P σ s) :
    WP isa (sel .s7 131072 (emLoop 18) (emLoop 20)) s (EDone P σ) := by
  unfold sel
  refine WP.seq (WP.mono (br_ok hp (v := 131072) (by decide) h) fun s1 ⟨h1, g6⟩ => ?_)
  refine WP.ite (M := isa) (decide (gam σ = 2 ^ 17)) (by rw [Pack.eval_zero, g6, lo_sub_beq _ (by decide)])
    (fun e => ?_) (fun e => ?_)
  · have hγ : gam σ = 2 ^ 17 := of_decide_eq_true e
    show WP isa (.seq (.block (([.addi .a7 .s11 840, mov .t1 .s10] : List Instr) ++
      Impl.MlDsa.RISCV64.Pack.loadQ ++ loadB .a1 131072)) (unpackLoop buFin 18 4 9)) s1 _
    refine WP.seq (WP.mono (setup_ok hp (Bv := 131072) (by decide) h1) fun s2 h2 => ?_)
    refine WP.mono (loop_ok hp (Bv := 131072) (c := 4) (nb := 9) (by constructor <;> decide) (by decide)
      (by decide) (by decide) h2) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo
  · have hγ : gam σ = 2 ^ 19 := by have := of_decide_eq_false e; omega
    show WP isa (.seq (.block (([.addi .a7 .s11 840, mov .t1 .s10] : List Instr) ++
      Impl.MlDsa.RISCV64.Pack.loadQ ++ loadB .a1 524288)) (unpackLoop buFin 20 2 5)) s1 _
    refine WP.seq (WP.mono (setup_ok hp (Bv := 524288) (by decide) h1) fun s2 h2 => ?_)
    refine WP.mono (loop_ok hp (Bv := 524288) (c := 2) (nb := 5) (by constructor <;> decide) (by decide)
      (by decide) (by decide) h2) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo

/-- The function, from an entry state whose regions are those of the call `P`. -/
theorem correct (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) (h0 : σ.gpr .a0 = P.sd) (h2 : σ.gpr .a2 = P.a)
    (h3 : σ.gpr .a3 = P.scr) (hlen : P.len = 66) :
    WP isa expandMask σ fun s' => PolyIs s'.mem P.a (Out P σ) ∧ abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rb hp h0 h2 h3 hlen) fun _ ⟨j1, s7⟩ =>
    WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := 640) (by decide) (by decide) j1) fun _ h2 =>
      WP.seq (WP.mono (tail_ok hp hg (T.of h2 s7)) fun _ h3 =>
        WP.mono (epi_ok hp h3.env) fun _ ⟨ha, hm, _⟩ => ⟨by rw [hm]; exact h3.out, ha⟩)))

end

/-! ## Constant time -/

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) (hsp : σ₁.sp = σ₂.sp)
include hp₁ hp₂ hsp

/-- The setup and the loop of one branch. -/
theorem em_ct {Bv d c nb : Nat} (hl : loadBVal Bv = BitVec.ofNat 64 Bv)
    (hnm : ((([.addi .a7 .s11 840, mov .t1 .s10] : List Instr) ++ Impl.MlDsa.RISCV64.Pack.loadQ ++
      loadB .a1 Bv).all Pack.noMem) = true)
    (hloop : ∀ {Q : State → State → Prop},
      (∀ a b, Q a b → a.sp = b.sp ∧ a.gpr .a7 = b.gpr .a7 ∧ a.gpr .t1 = b.gpr .t1) →
      RelCT isa Q (unpackLoop buFin d c nb) fun _ _ => True)
    {R : State → State → Prop} (hR : ∀ a b, R a b → T P σ₁ a ∧ T P σ₂ b) :
    RelCT isa R (.seq (.block (([.addi .a7 .s11 840, mov .t1 .s10] : List Instr) ++
      Impl.MlDsa.RISCV64.Pack.loadQ ++ loadB .a1 Bv)) (unpackLoop buFin d c nb)) fun _ _ => True :=
  RelCT.seq (R := fun a b => L Bv P σ₁ a ∧ L Bv P σ₂ b)
    (relct_wp (relct_noMem hnm) fun a b hab => ⟨setup_ok hp₁ hl (hR a b hab).1, setup_ok hp₂ hl (hR a b hab).2⟩)
    (hloop fun a b hab => ⟨by rw [hab.1.env.sp, hab.2.env.sp, hsp], by rw [hab.1.a7, hab.2.a7],
      by rw [hab.1.t1, hab.2.t1]⟩)

/-- The branch on `γ₁` and the loop, from runs whose `γ₁` agree. -/
theorem tail_ct (hg : (σ₁.gpr .a1).setWidth 32 = (σ₂.gpr .a1).setWidth 32) :
    RelCT isa (fun a b => T P σ₁ a ∧ T P σ₂ b) (sel .s7 131072 (emLoop 18) (emLoop 20)) fun _ _ => True := by
  unfold sel
  refine RelCT.seq (R := fun (a b : State) => (T P σ₁ a ∧ a.gpr .a6 = subwV (σ₁.gpr .a1) 131072) ∧
      (T P σ₂ b ∧ b.gpr .a6 = subwV (σ₂.gpr .a1) 131072))
    (relct_wp (relct_noMem (by unfold loadB VG.Impl.MlDsa.RISCV64.Arith.loadImm; rfl)) fun a b hab =>
      ⟨br_ok hp₁ (v := 131072) (by decide) hab.1, br_ok hp₂ (v := 131072) (by decide) hab.2⟩) ?_
  refine RelCT.ite (fun a b hab => by
    rw [Pack.eval_zero, Pack.eval_zero, hab.1.2, hab.2.2, subwV, subwV, hg]) ?_ ?_
  · exact em_ct hp₁ hp₂ hsp (Bv := 131072) (by decide) rfl (fun hQ => Pack.unpackLoop_ct18 hQ)
      fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩
  · exact em_ct hp₁ hp₂ hsp (Bv := 524288) (by decide) rfl (fun hQ => Pack.unpackLoop_ct20 hQ)
      fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩

end

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : SpOk (spOf σ₁) σ₁
  p₂ : SpOk (spOf σ₂) σ₂
  g₁ : gam σ₁ = 2 ^ 17 ∨ gam σ₁ = 2 ^ 19
  g₂ : gam σ₂ = 2 ^ 17 ∨ gam σ₂ = 2 ^ 19
  sp : σ₁.sp = σ₂.sp
  a0 : σ₁.gpr .a0 = σ₂.gpr .a0
  a1 : (σ₁.gpr .a1).setWidth 32 = (σ₂.gpr .a1).setWidth 32
  a2 : σ₁.gpr .a2 = σ₂.gpr .a2
  a3 : σ₁.gpr .a3 = σ₂.gpr .a3

theorem all_ct {σ₁ σ₂ : State} (h : Two σ₁ σ₂) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) expandMask fun _ _ => True := by
  have eP : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.a0, h.a2, h.a3]
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ h.p₂
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .s7 = σ₁.gpr .a1) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .s7 = σ₂.gpr .a1))
    (relct_wp (pro_rb_ct (fun a b hab => by rw [hab.1, hab.2]; exact h.sp)
      fun a b hab => by rw [hab.1, hab.2]; exact h.a3) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_rb h.p₁ rfl rfl rfl rfl
  · rw [hab.2]; exact pro_rb hp₂' h.a0.symm h.a2.symm h.a3.symm rfl
  refine RelCT.seq (R := fun a b => T (spOf σ₁) σ₁ a ∧ T (spOf σ₁) σ₂ b)
    (relct_wp ((sponge_ct h.p₁ hp₂' h.sp (rate := 136) (outlen := 640) (by decide) (by decide)).mono
      (fun a b hab => ⟨hab.1.1, hab.2.1⟩) fun _ _ x => x) fun a b hab =>
      ⟨WP.mono (sponge_ok h.p₁ (by decide) (by decide) hab.1.1) fun _ x => T.of x hab.1.2,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2.1) fun _ x => T.of x hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => EDone (spOf σ₁) σ₁ a ∧ EDone (spOf σ₁) σ₂ b)
    (relct_wp (tail_ct h.p₁ hp₂' h.sp h.a1) fun a b hab => ⟨tail_ok h.p₁ h.g₁ hab.1, tail_ok hp₂' h.g₂ hab.2⟩) ?_
  exact epi_ct (fun a b hab => by rw [hab.1.env.sp, hab.2.env.sp, h.sp])
    fun a b hab => by rw [hab.1.env.s11, hab.2.env.s11]

/-! ## `Verified` -/

theorem pre_of {s : State} (h : (Proof.MlDsa.expandMaskContract RISCV64.abi 1168).pre s) :
    SpOk (spOf s) s ∧ (gam s = 2 ^ 17 ∨ gam s = 2 ^ 19) := by
  sig_pre [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11, h12, hg, h14, h15⟩ := h
  exact ⟨⟨by rw [h2]; exact List.mem_singleton_self _, h3, h4, h5, h6, h7, h8, h9,
    show (66 : Nat) < 2 ^ 64 by decide, h11, h12, h0, h1, h14, h15⟩, hg⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x20000 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.RISCV64.Sample.ExpandMask

namespace VG.Proof.MlDsa.RISCV64.Sample

open VG VG.RISCV64
open ExpandMask

theorem expandMask_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sample.expandMask (Proof.MlDsa.expandMaskContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨hp, hg⟩ := pre_of hs
    obtain ⟨t, s', he, hpoly, ha⟩ := correct hp hg rfl rfl rfl rfl
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, RISCV64.abi, RISCV64.argRegs]
    exact hpoly
  · sig_pub [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, h0, h1, h2, h3⟩ := hpub
    obtain ⟨p₁, g₁⟩ := pre_of h₁
    obtain ⟨p₂, g₂⟩ := pre_of h₂
    exact (all_ct ⟨p₁, p₂, g₁, g₂, hsp, h0, h1, h2, h3⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Sample
