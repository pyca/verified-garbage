module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.ExpandMask
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Contracts
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Loop
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Stream
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.ExpandMask
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Loop
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Stream
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# ML-DSA on PPC64LE: `vg_mldsa_expand_mask_poly`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/ExpandMask.lean`). The function
runs in pieces: the prologue (`J0`, with `r27` the zero-extended `γ₁`), the
sponge, whose output is `H(ρ′, 640)` (`T`), the branch on `γ₁`, and the loop
of `vg_mldsa_bit_unpack` for `c = 1 + bitlen (γ₁ - 1)` on the first `32c`
bytes of output (`Pack.unpackLoop_buFin_ok`, run from the state permitted
only those bytes and `a`, and widened to the function's permissions by
`WP.narrow`), which are `H(ρ′, 32c)` (`H_take`). It is constant time: the
blocks without memory accesses leak nothing, the sponge by `sponge_ct`, the
branch goes the same way in two runs whose `γ₁` agree, and the loop by
`Pack.unpackLoop_ct18` and `Pack.unpackLoop_ct20`, from the same pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.ExpandMask

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Impl.MlDsa.PPC64LE.Pack (unpackLoop buFin loadB)
open VG.Proof.MlDsa.PPC64LE.Pack (RB loadBVal loadB_ok Shape loopRegs)
open VG.Spec.MlDsa (Zq q H toRq bitUnpack bitlen)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt rates)

/-- The call, from the entry state: `seed = r3`, `gamma1 = r4`, `a = r5`,
`scratch = r6`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r3, 66, σ.gpr .r6, σ.gpr .r5⟩

/-- `γ₁`, the low 32 bits of `r4`. -/
abbrev gam (σ : State) : Nat := ((σ.gpr .r4).setWidth 32).toNat

/-- What the function writes, for the call `P`. -/
abbrev Out (P : Sp) (σ : State) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (P.msg σ) (32 * (1 + bitlen (gam σ - 1)))) (gam σ - 1) (gam σ))

/-- After the sponge. -/
structure T (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 640 = H (P.msg σ) 640
  r27 : s.gpr .r27 = zx (σ.gpr .r4)

/-- After the branch's block. -/
structure Br (P : Sp) (σ s : State) : Prop where
  t : T P σ s
  r12 : s.gpr .r12 = zx (σ.gpr .r4) - BitVec.ofNat 64 131072

/-- Before the loop of `BitUnpack` for `b = Bv`. -/
structure L (Bv : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 640 = H (P.msg σ) 640
  r10 : s.gpr .r10 = P.at' 840
  r11 : s.gpr .r11 = P.a
  rb : RB Bv s

/-- After the loop. -/
structure EDone (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : PolyIs s.mem P.a (Out P σ)

theorem zx_eq {x y : BitVec 64} (h : x.setWidth 32 = y.setWidth 32) : zx x = zx y :=
  BitVec.eq_of_toNat_eq (by rw [zx_toNat, zx_toNat, h])

theorem zx_sub_beq (x : BitVec 64) :
    (zx x - BitVec.ofNat 64 131072 == 0) = decide ((x.setWidth 32).toNat = 2 ^ 17) := by
  by_cases h : (x.setWidth 32).toNat = 2 ^ 17
  · have e : zx x = BitVec.ofNat 64 131072 := BitVec.eq_of_toNat_eq (by rw [zx_toNat, h]; rfl)
    rw [e]; simp [h]
  · have e : zx x ≠ BitVec.ofNat 64 131072 := fun e => h (by rw [← zx_toNat, e]; rfl)
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e'
    have h2 := congrArg (· + BitVec.ofNat 64 131072) e'
    simp only [BitVec.sub_add_cancel] at h2
    exact e h2

theorem preserved_not_loop : ∀ r ∈ preserved, r ∉ loopRegs := by decide

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The branch's block. -/
theorem br_ok {s : State} (h : T P σ s) :
    WP isa (.block [.lis .r12 2, .sub .r12 .r27 .r12]) s (Br P σ) := by
  have hk : WP isa (.block [.lis .r12 2, .sub .r12 .r27 .r12]) s fun s' =>
      s'.gpr .r12 = s.gpr .r27 - BitVec.ofNat 64 131072 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    have hv : ((2 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 = BitVec.ofNat 64 131072 := by decide
    prun [exec_lis, hv]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun s' ⟨g12, gp, m, rd, wr, sp⟩ => ⟨⟨h.env.regs hp m gp rd wr sp, by rw [m]; exact h.out,
    (gp _ (by decide)).trans h.r27⟩, by rw [g12, h.r27]⟩

/-- The loop's setup: the pointers, `q` and `b`. -/
theorem setup_ok {Bv : Nat} (hl : loadBVal Bv = BitVec.ofNat 64 Bv) {s : State} (h : T P σ s) :
    WP isa (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 Bv)) s (L Bv P σ) := by
  have g30 := h.env.r30
  have g31 := h.env.r31
  have hk : WP isa (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++
      Impl.MlDsa.PPC64LE.Pack.loadQ)) s fun s' =>
      s'.gpr .r10 = P.at' 840 ∧ s'.gpr .r11 = P.a ∧ s'.gpr .r7 = BitVec.ofNat 64 8380417 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [Impl.MlDsa.PPC64LE.Pack.loadQ, List.cons_append, List.nil_append, exec_lis, exec_ori, loadQ_val, g30,
      g31]
    simp only [true_and, and_true]
    pres_tac
  rw [WP.block_append_iff]
  refine WP.mono hk fun s₁ ⟨g10, g11, g7, gp, m, rd, wr, sp⟩ => ?_
  refine WP.mono (Pack.WP.withSp (loadB_ok .r4 hl s₁)) fun s' ⟨⟨⟨g4, m'⟩, k⟩, sp'⟩ => ?_
  have m2 : s'.mem = s.mem := m'.trans m
  refine ⟨h.env.regs hp m2 (fun r hr => (k.gpr (by
      rw [List.mem_singleton]; rintro rfl; exact absurd hr (by decide))).trans (gp r hr))
      (k.2.1.trans rd) (k.2.2.trans wr) (sp'.trans sp), by rw [m2]; exact h.out,
    (k.gpr (by decide)).trans g10, (k.gpr (by decide)).trans g11, g4, (k.gpr (by decide)).trans g7⟩

omit hp in
/-- After the sponge, from its output and the zero-extended `γ₁` in `r27`. -/
theorem T.of {s₀ s : State} (h : J6 136 640 P σ s₀ s) (r27 : s₀.gpr .r27 = zx (σ.gpr .r4)) : T P σ s :=
  ⟨h.j0.env, by rw [h.out]; exact (H_eq _ _).symm, (h.gp .r27 (by decide)).trans r27⟩

/-- The loop of `BitUnpack` for `(Bv, d, c, nb)`, from its setup, run on the
first `32 d` bytes of the output and the polynomial `a` alone. -/
theorem loop_ok {Bv d c nb : Nat} (hs : Shape d c nb) (hB19 : Bv ≤ 2 ^ 19) (hd : bitlen (Bv - 1 + Bv) = d)
    (h32 : 32 * d ≤ 640) {s : State} (h : L Bv P σ s) :
    WP isa (unpackLoop buFin d c nb) s fun s' =>
      Env P σ s' ∧ PolyIs s'.mem P.a (toRq (bitUnpack (H (P.msg σ) (32 * d)) (Bv - 1) Bv)) := by
  have fs := hp.fscr
  have ewr : s.wr = [P.aR, P.scrR] := h.env.wr.trans hp.wr
  refine WP.narrow (rd := [⟨s.gpr .r10, 32 * d⟩]) (wr := [⟨s.gpr .r11, 1024⟩])
    (Pack.unpackLoop_buFin_ok (a := Bv - 1) hs hB19 hd h.rb (List.mem_append_left _ (List.mem_singleton_self _))
      (List.mem_singleton_self _) ?_) ?_ ?_ (fun s' rd' wr' sp' hf hq => ?_) (by unfold unpackLoop; rfl)
  · show Region.Disjoint ⟨s.gpr .r10, 32 * d⟩ ⟨s.gpr .r11, 1024⟩
    rw [h.r10, h.r11]
    exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 32 * d) (by omega))).symm
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨P.scrR, List.mem_append_right _ (by rw [ewr]; simp), 840, h.r10, by show 840 + 32 * d ≤ 2048; omega⟩
    · exact ⟨P.aR, List.mem_append_right _ (by rw [ewr]; simp), 0, by rw [h.r11]; exact (BitVec.add_zero _).symm,
        by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨P.aR, by rw [ewr]; simp, 0, by rw [h.r11]; exact (BitVec.add_zero _).symm, by simp⟩
  obtain ⟨hpoly, -, hk⟩ := hq
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => hk.1 r (preserved_not_loop r hr)
  refine ⟨h.env.step hp (rs := [P.aR]) (by rw [h.r11] at hf; exact hf) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h)) gp rd' wr' sp', ?_⟩
  have eb : bytesAt s.mem (P.at' 840) (32 * d) = H (P.msg σ) (32 * d) := by
    rw [← MlKem.bytesAt_take _ _ h32, h.out, H_take _ h32]
  simp only [State.withRegions_mem, State.withRegions_gpr] at hpoly
  rw [h.r11, h.r10, eb] at hpoly
  exact hpoly

/-- The branch on `γ₁` and the loop. -/
theorem tail_ok (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) {s : State} (h : T P σ s) :
    WP isa (.seq (.block [.lis .r12 2, .sub .r12 .r27 .r12]) (.ite (.zero .d .r12) (emLoop 18) (emLoop 20))) s
      (EDone P σ) := by
  refine WP.seq (WP.mono (br_ok hp h) fun s1 h1 => ?_)
  refine WP.ite (M := isa) (decide (gam σ = 2 ^ 17)) (by rw [eval_zero, h1.r12, zx_sub_beq]) (fun e => ?_)
    (fun e => ?_)
  · have hγ : gam σ = 2 ^ 17 := of_decide_eq_true e
    show WP isa (.seq (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 131072)) (unpackLoop buFin 18 4 9)) s1 _
    refine WP.seq (WP.mono (setup_ok hp (Bv := 131072) (by decide) h1.t) fun s2 h2 => ?_)
    refine WP.mono (loop_ok hp (Bv := 131072) (c := 4) (nb := 9) (by constructor <;> decide) (by decide)
      (by decide) (by decide) h2) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo
  · have hγ : gam σ = 2 ^ 19 := by have := of_decide_eq_false e; omega
    show WP isa (.seq (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 524288)) (unpackLoop buFin 20 2 5)) s1 _
    refine WP.seq (WP.mono (setup_ok hp (Bv := 524288) (by decide) h1.t) fun s2 h2 => ?_)
    refine WP.mono (loop_ok hp (Bv := 524288) (c := 2) (nb := 5) (by constructor <;> decide) (by decide)
      (by decide) (by decide) h2) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo

/-- The function, from an entry state whose regions are those of the call `P`. -/
theorem correct (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) (h3 : σ.gpr .r3 = P.sd) (h5 : σ.gpr .r5 = P.a)
    (h6 : σ.gpr .r6 = P.scr) (hlen : P.len = 66) :
    WP isa Impl.MlDsa.PPC64LE.Sample.expandMask σ fun s' => PolyIs s'.mem P.a (Out P σ) ∧ abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rb hp h3 h5 h6 hlen) fun _ ⟨j1, r27⟩ =>
    WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := 640) (by decide) (by decide) j1) fun _ h2 =>
      WP.seq (WP.mono (tail_ok hp hg (T.of h2 r27)) fun _ h3 =>
        WP.mono (epi_ok hp h3.env) fun _ ⟨ha, hm, _⟩ => ⟨by rw [hm]; exact h3.out, ha⟩)))

end

/-! ## Constant time -/

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) (hsp : σ₁.sp = σ₂.sp)
include hp₁ hp₂ hsp

/-- The setup and the loop of one branch. -/
theorem em_ct {Bv d c nb : Nat} (hl : loadBVal Bv = BitVec.ofNat 64 Bv)
    (hnm : ((([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 Bv).all VG.Proof.MlKem.PPC64LE.noMem) = true)
    (hloop : ∀ {Q : State → State → Prop},
      (∀ a b, Q a b → a.sp = b.sp ∧ a.gpr .r10 = b.gpr .r10 ∧ a.gpr .r11 = b.gpr .r11) →
      RelCT isa Q (unpackLoop buFin d c nb) fun _ _ => True)
    {R : State → State → Prop} (hR : ∀ a b, R a b → T P σ₁ a ∧ T P σ₂ b) :
    RelCT isa R (.seq (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 Bv)) (unpackLoop buFin d c nb)) fun _ _ => True :=
  RelCT.seq (R := fun a b => L Bv P σ₁ a ∧ L Bv P σ₂ b)
    (relct_wp (relct_noMem hnm) fun a b hab => ⟨setup_ok hp₁ hl (hR a b hab).1, setup_ok hp₂ hl (hR a b hab).2⟩)
    (hloop fun a b hab => ⟨by rw [hab.1.env.sp, hab.2.env.sp, hsp], by rw [hab.1.r10, hab.2.r10],
      by rw [hab.1.r11, hab.2.r11]⟩)

/-- The branch on `γ₁` and the loop, from runs whose `γ₁` agree. -/
theorem tail_ct (hg : (σ₁.gpr .r4).setWidth 32 = (σ₂.gpr .r4).setWidth 32) :
    RelCT isa (fun a b => T P σ₁ a ∧ T P σ₂ b)
      (.seq (.block [.lis .r12 2, .sub .r12 .r27 .r12]) (.ite (.zero .d .r12) (emLoop 18) (emLoop 20)))
      fun _ _ => True := by
  refine RelCT.seq (R := fun a b => Br P σ₁ a ∧ Br P σ₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨br_ok hp₁ hab.1, br_ok hp₂ hab.2⟩) ?_
  refine RelCT.ite (fun a b hab => by rw [eval_zero, eval_zero, hab.1.r12, hab.2.r12, zx_eq hg]) ?_ ?_
  · exact em_ct hp₁ hp₂ hsp (Bv := 131072) (by decide) rfl (fun hQ => Pack.unpackLoop_ct18 hQ)
      fun a b hab => ⟨hab.1.1.t, hab.1.2.t⟩
  · exact em_ct hp₁ hp₂ hsp (Bv := 524288) (by decide) rfl (fun hQ => Pack.unpackLoop_ct20 hQ)
      fun a b hab => ⟨hab.1.1.t, hab.1.2.t⟩

end

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : SpOk (spOf σ₁) σ₁
  p₂ : SpOk (spOf σ₂) σ₂
  g₁ : gam σ₁ = 2 ^ 17 ∨ gam σ₁ = 2 ^ 19
  g₂ : gam σ₂ = 2 ^ 17 ∨ gam σ₂ = 2 ^ 19
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : (σ₁.gpr .r4).setWidth 32 = (σ₂.gpr .r4).setWidth 32
  r5 : σ₁.gpr .r5 = σ₂.gpr .r5
  r6 : σ₁.gpr .r6 = σ₂.gpr .r6

theorem all_ct {σ₁ σ₂ : State} (h : Two σ₁ σ₂) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.expandMask fun _ _ => True := by
  have eP : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r3, h.r5, h.r6]
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ h.p₂
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r4)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₂.gpr .r4)))
    (relct_wp (pro_rb_ct (fun a b hab => by rw [hab.1, hab.2]; exact h.sp)
      fun a b hab => by rw [hab.1, hab.2]; exact h.r6) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_rb h.p₁ rfl rfl rfl rfl
  · rw [hab.2]; exact pro_rb hp₂' h.r3.symm h.r5.symm h.r6.symm rfl
  refine RelCT.seq (R := fun a b => T (spOf σ₁) σ₁ a ∧ T (spOf σ₁) σ₂ b)
    (relct_wp ((sponge_ct h.p₁ hp₂' h.sp (rate := 136) (outlen := 640) (by decide) (by decide)).mono
      (fun a b hab => ⟨hab.1.1, hab.2.1⟩) fun _ _ x => x) fun a b hab =>
      ⟨WP.mono (sponge_ok h.p₁ (by decide) (by decide) hab.1.1) fun _ x => T.of x hab.1.2,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2.1) fun _ x => T.of x hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => EDone (spOf σ₁) σ₁ a ∧ EDone (spOf σ₁) σ₂ b)
    (relct_wp (tail_ct h.p₁ hp₂' h.sp h.r4) fun a b hab => ⟨tail_ok h.p₁ h.g₁ hab.1, tail_ok hp₂' h.g₂ hab.2⟩) ?_
  exact epi_ct (fun a b hab => by rw [hab.1.env.sp, hab.2.env.sp, h.sp])
    fun a b hab => by rw [hab.1.env.r31, hab.2.env.r31]

/-! ## `Verified` -/

theorem pre_of {s : State} (h : (Proof.MlDsa.expandMaskContract PPC64LE.abi 48).pre s) :
    SpOk (spOf s) s ∧ (gam s = 2 ^ 17 ∨ gam s = 2 ^ 19) := by
  sig_pre [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hg⟩ := h
  exact ⟨⟨by rw [h1]; exact List.mem_singleton_self _, h2, h3, h4, h5, h6, h7, h8,
    show (66 : Nat) < 2 ^ 64 by decide, h10, h11, h0⟩, hg⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x20000 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.ExpandMask

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open ExpandMask

theorem expandMask_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.expandMask (Proof.MlDsa.expandMaskContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨hp, hg⟩ := pre_of hs
    obtain ⟨t, s', he, hpoly, ha⟩ := correct hp hg rfl rfl rfl rfl
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hpoly
  · sig_pub [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, h3, h4, h5, h6⟩ := hpub
    obtain ⟨p₁, g₁⟩ := pre_of h₁
    obtain ⟨p₂, g₂⟩ := pre_of h₂
    exact (all_ct ⟨p₁, p₂, g₁, g₂, hsp, h3, h4, h5, h6⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample
