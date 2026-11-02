module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Sponge
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Sponge
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# ML-DSA on RISC-V: the sampling functions' prologue and epilogue

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sample/Pro.lean`). The prologue (`pro`)
saves our caller's `s7`–`s11` and `ra` in the working space and sets up the
layout: from what it leaves, `J0` holds and `s7` holds the parameter
(`pro_ok`, for any registers, and `pro_rn`, `pro_rb`, `pro_ball` for the
three ways the functions call it). The epilogue (`epi`) restores them: with
`Env`, the calling convention's obligations hold at the end (`epi_ok`, and
`retEpi_ok`, which also returns `j >> 8`). `accept_skip` and `accept_store`
are the two ways of `accept`, which stores the next coefficient `a[j]`. Each
of these blocks is constant time from the registers that hold the pointers
(`pro_rn_ct`, …, `epi_ct`, `accept_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sample

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Sample
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Proof.MlKem.RISCV64.Sample (readW_writeW_off taint_block ret_val)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.Sample (coeffAddr coeff_contains Stored stored_snoc zw polyR)

/-! ## The prologue -/

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- Our caller's registers and return address saved. -/
theorem save_ok {scr : Reg} (hs : σ.gpr scr = P.scr) :
    WP isa (.block [.store .d .s7 scr 2000, .store .d .s8 scr 2008, .store .d .s9 scr 2016,
      .store .d .s10 scr 2024, .store .d .s11 scr 2032, .store .d .ra scr 2040]) σ fun s =>
      s.gpr = σ.gpr ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
      s.mem = (((((σ.mem.writeW (P.scr + BitVec.ofNat 64 2000) (σ.gpr .s7)).writeW
        (P.scr + BitVec.ofNat 64 2008) (σ.gpr .s8)).writeW (P.scr + BitVec.ofNat 64 2016) (σ.gpr .s9)).writeW
        (P.scr + BitVec.ofNat 64 2024) (σ.gpr .s10)).writeW (P.scr + BitVec.ofNat 64 2032) (σ.gpr .s11)).writeW
        (P.scr + BitVec.ofNat 64 2040) (σ.gpr .ra) := by
  have w0 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2000) 8 := inScr hp rfl (by decide)
  have w1 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2008) 8 := inScr hp rfl (by decide)
  have w2 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2016) 8 := inScr hp rfl (by decide)
  have w3 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2024) 8 := inScr hp rfl (by decide)
  have w4 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2032) 8 := inScr hp rfl (by decide)
  have w5 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2040) 8 := inScr hp rfl (by decide)
  have a0 := scr_al hp (o := 2000) (by decide)
  have a1 := scr_al hp (o := 2008) (by decide)
  have a2 := scr_al hp (o := 2016) (by decide)
  have a3 := scr_al hp (o := 2024) (by decide)
  have a4 := scr_al hp (o := 2032) (by decide)
  have a5 := scr_al hp (o := 2040) (by decide)
  mrun [hs, w0, w1, w2, w3, w4, w5, a0, a1, a2, a3, a4, a5]

/-- The prologue, given what its moves leave: `J0`, and `s7` = `v7`. -/
theorem pro_ok {scr a msg : Reg} {len prm : List Instr} (hs : σ.gpr scr = P.scr) {v7 : BitVec 64}
    (hmv : ∀ t : State, t.gpr = σ.gpr →
      WP isa (.block (([mov .s11 scr, mov .s10 a, mov .s9 msg] : List Instr) ++ len ++ prm)) t fun t' =>
        t'.gpr .s11 = P.scr ∧ t'.gpr .s10 = P.a ∧ t'.gpr .s9 = P.sd ∧ t'.gpr .s8 = BitVec.ofNat 64 P.len ∧
        t'.gpr .s7 = v7 ∧
        (∀ r ∈ preserved, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp) :
    WP isa (.block (pro scr a msg len prm)) σ fun s => J0 P σ s ∧ s.gpr .s7 = v7 := by
  have fs := hp.fscr
  rw [show pro scr a msg len prm = ([.store .d .s7 scr 2000, .store .d .s8 scr 2008, .store .d .s9 scr 2016,
      .store .d .s10 scr 2024, .store .d .s11 scr 2032, .store .d .ra scr 2040] :
      List Instr) ++ (([mov .s11 scr, mov .s10 a, mov .s9 msg] : List Instr) ++ len ++ prm) from rfl,
    WP.block_append_iff]
  refine WP.mono (save_ok hp hs) fun s1 ⟨g1, rd1, wr1, sp1, m1⟩ => ?_
  refine WP.mono (hmv s1 g1) fun s2 ⟨g11, g10, g9, g8, g7, cs, m2, rd2, wr2, sp2⟩ => ?_
  have fr : Frame [P.aR, P.scrR, STK σ] σ.mem s2.mem := by
    rw [m2, m1]
    refine ((((((Frame.refl _ _).writeW (r := P.scrR) (by simp) _ ?_).writeW (r := P.scrR) (by simp) _ ?_).writeW
      (r := P.scrR) (by simp) _ ?_).writeW (r := P.scrR) (by simp) _ ?_).writeW (r := P.scrR) (by simp) _ ?_).writeW
      (r := P.scrR) (by simp) _ ?_ <;> exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨⟨rd2.trans rd1, wr2.trans wr1, sp2.trans sp1, g10, g11,
    fun r hr a b c d e => by rw [cs r hr a b c d e, g1], ?_, ?_, ?_, ?_, ?_, ?_, fr⟩, g9, g8⟩, g7⟩ <;>
  · rw [m2, m1]
    simp (disch := decide) only [Sp.at', readW_writeW_off, Mem.readW_writeW_self64]

/-- The prologue of `vg_mldsa_rej_ntt_poly`: `seed = a0`, `a = a1`,
`scratch = a2`; `s7` is our caller's. -/
theorem pro_rn (h0 : σ.gpr .a0 = P.sd) (h1 : σ.gpr .a1 = P.a) (h2 : σ.gpr .a2 = P.scr) (hlen : P.len = 34) :
    WP isa (.block (pro .a2 .a1 .a0 [.li .s8 34] [])) σ fun s => J0 P σ s ∧ s.gpr .s7 = σ.gpr .s7 :=
  pro_ok hp h2 fun t ht => by
    have e0 : t.gpr .a0 = P.sd := by rw [ht]; exact h0
    have e1 : t.gpr .a1 = P.a := by rw [ht]; exact h1
    have e2 : t.gpr .a2 = P.scr := by rw [ht]; exact h2
    have e7 : t.gpr .s7 = σ.gpr .s7 := by rw [ht]
    mrun [mov, List.append_nil, e0, e1, e2, e7, hlen]
    intro r hr _ b c d e
    simp only [b, c, d, e, ite_false]

/-- The prologue of `vg_mldsa_rej_bounded_poly` and
`vg_mldsa_expand_mask_poly`: `seed = a0`, the parameter in `a1`, `a = a2`,
`scratch = a3`; `s7` is the parameter. -/
theorem pro_rb (h0 : σ.gpr .a0 = P.sd) (h2 : σ.gpr .a2 = P.a) (h3 : σ.gpr .a3 = P.scr) (hlen : P.len = 66) :
    WP isa (.block (pro .a3 .a2 .a0 [.li .s8 66] [mov .s7 .a1])) σ fun s => J0 P σ s ∧ s.gpr .s7 = σ.gpr .a1 :=
  pro_ok hp h3 fun t ht => by
    have e0 : t.gpr .a0 = P.sd := by rw [ht]; exact h0
    have e1 : t.gpr .a1 = σ.gpr .a1 := by rw [ht]
    have e2 : t.gpr .a2 = P.a := by rw [ht]; exact h2
    have e3 : t.gpr .a3 = P.scr := by rw [ht]; exact h3
    mrun [mov, e0, e1, e2, e3, hlen]
    intro r hr a b c d e
    simp only [a, b, c, d, e, ite_false]

/-- The prologue of `vg_mldsa_sample_in_ball`: `ctilde = a0`, its length in
`a1`, `tau = a2`, `c = a3`, `scratch = a4`; `s7` is `tau`. -/
theorem pro_ball (h0 : σ.gpr .a0 = P.sd) (h1 : σ.gpr .a1 = BitVec.ofNat 64 P.len) (h3 : σ.gpr .a3 = P.a)
    (h4 : σ.gpr .a4 = P.scr) :
    WP isa (.block (pro .a4 .a3 .a0 [mov .s8 .a1] [mov .s7 .a2])) σ fun s => J0 P σ s ∧ s.gpr .s7 = σ.gpr .a2 :=
  pro_ok hp h4 fun t ht => by
    have e0 : t.gpr .a0 = P.sd := by rw [ht]; exact h0
    have e1 : t.gpr .a1 = BitVec.ofNat 64 P.len := by rw [ht]; exact h1
    have e2 : t.gpr .a2 = σ.gpr .a2 := by rw [ht]
    have e3 : t.gpr .a3 = P.a := by rw [ht]; exact h3
    have e4 : t.gpr .a4 = P.scr := by rw [ht]; exact h4
    mrun [mov, e0, e1, e2, e3, e4]
    intro r hr a b c d e
    simp only [a, b, c, d, e, ite_false]

end

/-! ## The epilogue -/

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The epilogue: our caller's registers restored, the memory and the
registers but `ra` and `s7`–`s11` unchanged. -/
theorem epi_ok {s : State} (he : Env P σ s) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ .ra → r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → s'.gpr r = s.gpr r := by
  have i0 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2000) 8 := inScrRd hp he.wr (by decide)
  have i1 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2008) 8 := inScrRd hp he.wr (by decide)
  have i2 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2016) 8 := inScrRd hp he.wr (by decide)
  have i3 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2024) 8 := inScrRd hp he.wr (by decide)
  have i4 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2032) 8 := inScrRd hp he.wr (by decide)
  have i5 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2040) 8 := inScrRd hp he.wr (by decide)
  have a0 := scr_al hp (o := 2000) (by decide)
  have a1 := scr_al hp (o := 2008) (by decide)
  have a2 := scr_al hp (o := 2016) (by decide)
  have a3 := scr_al hp (o := 2024) (by decide)
  have a4 := scr_al hp (o := 2032) (by decide)
  have a5 := scr_al hp (o := 2040) (by decide)
  have v7 : s.mem.readW (P.scr + BitVec.ofNat 64 2000) 64 = σ.gpr .s7 := he.v7
  have v8 : s.mem.readW (P.scr + BitVec.ofNat 64 2008) 64 = σ.gpr .s8 := he.v8
  have v9 : s.mem.readW (P.scr + BitVec.ofNat 64 2016) 64 = σ.gpr .s9 := he.v9
  have v10 : s.mem.readW (P.scr + BitVec.ofNat 64 2024) 64 = σ.gpr .s10 := he.v10
  have v11 : s.mem.readW (P.scr + BitVec.ofNat 64 2032) 64 = σ.gpr .s11 := he.v11
  have vra : s.mem.readW (P.scr + BitVec.ofNat 64 2040) 64 = σ.gpr .ra := he.vra
  have g11 := he.s11
  have hk : WP isa (.block epi) s fun s' => s'.gpr .ra = σ.gpr .ra ∧ s'.gpr .s7 = σ.gpr .s7 ∧
      s'.gpr .s8 = σ.gpr .s8 ∧ s'.gpr .s9 = σ.gpr .s9 ∧ s'.gpr .s10 = σ.gpr .s10 ∧
      s'.gpr .s11 = σ.gpr .s11 ∧
      (∀ r, r ≠ .ra → r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp := by
    mrun [epi, g11, i0, i1, i2, i3, i4, i5, a0, a1, a2, a3, a4, a5, v7, v8, v9, v10, v11, vra]
    intro r h0 a b c d e
    simp only [h0, a, b, c, d, e, ite_false]
  refine WP.mono hk fun s' ⟨ra, r7, r8, r9, r10, r11, g, m, sp⟩ => ⟨⟨fun r hr => ?_, sp.trans he.sp, ra⟩, m, g⟩
  by_cases a : r = .s7
  · subst a; exact r7
  by_cases b : r = .s8
  · subst b; exact r8
  by_cases c : r = .s9
  · subst c; exact r9
  by_cases d : r = .s10
  · subst d; exact r10
  by_cases e : r = .s11
  · subst e; exact r11
  have hra : r ≠ .ra := by rintro rfl; simp [preserved] at hr
  exact (g r hra a b c d e).trans (he.cs r hr a b c d e)

/-- The end of a sampling function that returns whether `j` (in `a2`) is 256. -/
theorem retEpi_ok {s : State} (he : Env P σ s) {j : Nat} (hj : s.gpr .a2 = BitVec.ofNat 64 j) (hj' : j ≤ 256) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .a0 = (if j = 256 then 1 else 0) ∧ s'.mem = s.mem ∧ abiPreserved σ s' := by
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.write .a0 (s.gpr .a2 >>> 8)) (by mrun [retJ]) fun s1 e1 => ?_
  subst e1
  have he1 : Env P σ (s.write .a0 (s.gpr .a2 >>> 8)) := he.regs hp rfl (fun r hr =>
    RegUpd.gpr_write_of_ne (s := s) (r := .a0) (r' := r) _ (by rintro rfl; exact absurd hr (by decide))) rfl rfl rfl
  refine WP.mono (epi_ok hp he1) fun s' ⟨ha, hm, g⟩ => ⟨?_, hm, ha⟩
  rw [g .a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), RegUpd.gpr_write_self, hj,
    ret_val hj']

end

/-! ## Storing a coefficient -/

/-- The next coefficient is `a[j]` for the `j` = `L.length` coefficients `L`
stored so far. -/
structure At (P : Sp) (L : List Zq) (s : State) : Prop where
  a1 : s.gpr .a1 = P.a + BitVec.ofNat 64 (4 * L.length)
  a2 : s.gpr .a2 = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  st : Stored s.mem P.a L

theorem accept_skip {v : Reg} {s : State} (h : s.gpr .t2 = 0) : WP isa (accept v) s fun s' => s' = s :=
  WP.ite _ (Steps.eval_zero _ _) (fun _ => WP.block_nil rfl) fun e => absurd e (by simp [h])

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- `accept v` stores `v` as `a[j]` when `t2 ≠ 0`. -/
theorem accept_store {s : State} (he : Env P σ s) {v : Reg} {L : List Zq}
    (ha : At P L s) (hL : L.length < 256) {x : Zq} (hx : (s.gpr v).setWidth 32 = zw x) (h : s.gpr .t2 ≠ 0) :
    WP isa (accept v) s fun s' => At P (L ++ [x]) s' ∧ Env P σ s' ∧
      (∀ r, r ≠ .a1 → r ≠ .a2 → s'.gpr r = s.gpr r) ∧ Frame [P.aR] s.mem s'.mem := by
  have cA := coeff_contains P.a (i := L.length) hL
  have iA : InRegions s.wr (P.a + BitVec.ofNat 64 (4 * L.length)) 4 :=
    ⟨P.aR, by rw [he.wr, hp.wr]; simp, cA⟩
  have alA : (P.a + BitVec.ofNat 64 (4 * L.length)).toNat % 4 = 0 := by
    have := hp.alA
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have g1 := ha.a1
  have g2 := ha.a2
  refine WP.ite _ (Steps.eval_zero _ _) (fun e => absurd (beq_iff_eq.mp e) h) fun _ => ?_
  have hblk : WP isa (.block [.store .w v .a1 0, .addi .a1 .a1 4, .addi .a2 .a2 1]) s fun t =>
      t.mem = s.mem.writeW (P.a + BitVec.ofNat 64 (4 * L.length)) ((s.gpr v).setWidth 32) ∧
      t.gpr .a1 = P.a + BitVec.ofNat 64 (4 * L.length) + BitVec.ofNat 64 4 ∧
      t.gpr .a2 = BitVec.ofNat 64 L.length + BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a1 → r ≠ .a2 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    mrun [g1, g2, iA, alA]
    intro r h4 h5
    simp only [h4, h5, ite_false]
  refine WP.mono hblk fun t ⟨m, r4, r5, rr, rd, wr, sp⟩ => ?_
  have hf : Frame [P.aR] s.mem t.mem := by rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cA
  refine ⟨⟨?_, ?_, ?_, ?_⟩, he.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (fun r hr => rr r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    rd wr sp, rr, hf⟩
  · rw [r4, List.length_append, List.length_singleton, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (L.length + 1) = 4 * L.length + 4 by omega]
  · rw [r5, List.length_append, List.length_singleton, BitVec.ofNat_add]
  · simp only [List.length_append, List.length_singleton]; omega
  · rw [m, hx]; exact stored_snoc ha.st hL x

end

/-! ## Constant time -/

theorem pro_rn_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h2 : ∀ a b, R a b → a.gpr .a2 = b.gpr .a2) :
    RelCT isa R (.block (pro .a2 .a1 .a0 [.li .s8 34] [])) fun _ _ => True :=
  taint_block [.a2] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h2 a b hab)
    (by taint_decide)

theorem pro_rb_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h3 : ∀ a b, R a b → a.gpr .a3 = b.gpr .a3) :
    RelCT isa R (.block (pro .a3 .a2 .a0 [.li .s8 66] [mov .s7 .a1])) fun _ _ => True :=
  taint_block [.a3] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h3 a b hab)
    (by taint_decide)

theorem pro_ball_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h4 : ∀ a b, R a b → a.gpr .a4 = b.gpr .a4) :
    RelCT isa R (.block (pro .a4 .a3 .a0 [mov .s8 .a1] [mov .s7 .a2])) fun _ _ => True :=
  taint_block [.a4] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h4 a b hab)
    (by taint_decide)

theorem retEpi_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h11 : ∀ a b, R a b → a.gpr .s11 = b.gpr .s11) :
    RelCT isa R (.block (retJ ++ epi)) fun _ _ => True :=
  taint_block [.s11] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h11 a b hab)
    (by taint_decide)

theorem epi_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h11 : ∀ a b, R a b → a.gpr .s11 = b.gpr .s11) :
    RelCT isa R (.block epi) fun _ _ => True :=
  taint_block [.s11] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h11 a b hab)
    (by taint_decide)

/-- A coefficient stored or not, in both runs alike. -/
theorem accept_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (hz : ∀ a b, R a b → a.gpr .t2 = b.gpr .t2) (h1 : ∀ a b, R a b → a.gpr .a1 = b.gpr .a1) :
    RelCT isa R (accept .a7) fun _ _ => True := by
  refine RelCT.ite (fun a b hab => by rw [Steps.eval_zero, Steps.eval_zero, hz a b hab]) ?_ ?_
  · exact taint_block [] (fun a b hab => hsp a b hab.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  · exact taint_block [.a1] (fun a b hab => hsp a b hab.1) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h1 a b hab.1) (by taint_decide)

end VG.Proof.MlDsa.RISCV64.Sample
