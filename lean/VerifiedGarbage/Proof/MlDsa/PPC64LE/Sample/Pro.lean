module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Sponge
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Sponge
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# ML-DSA on PPC64LE: the sampling functions' prologue and epilogue

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/Pro.lean`). The prologue (`pro`)
saves our caller's `r27`–`r31` and `lr` in the working space and sets up the
layout: from what it leaves, `J0` holds and `r27` holds the parameter
(`pro_ok`, for any registers, and `pro_rn`, `pro_rb`, `pro_ball` for the
three ways the functions call it; `zx` is the zero-extended `u32`). The
epilogue (`epi`) restores them: with `Env`, the calling convention's
obligations hold at the end (`epi_ok`, and `retEpi_ok`, which also returns
`j >> 8`). `accept_skip` and `accept_store` are the two ways of `accept`, which
stores the next coefficient `a[j]`. Each of these blocks is constant time
from the registers that hold the pointers (`pro_rn_ct`, …, `epi_ct`,
`accept_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlKem.PPC64LE.Sample (readW_writeW_off taint_block ret_val)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.Sample (coeffAddr coeff_contains Stored stored_snoc zw polyR)

/-- A `u32` argument, zero-extended (`zext32`). -/
abbrev zx (x : BitVec 64) : BitVec 64 := x <<< 32 >>> 32

theorem zx_toNat (x : BitVec 64) : (zx x).toNat = (x.setWidth 32).toNat := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have := x.isLt
  omega

/-- `loadQ`'s `lis` and `ori`: `q`. -/
theorem loadQ_val :
    ((0x7F : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0xE001 : BitVec 16).setWidth 64 =
      BitVec.ofNat 64 8380417 := by decide

/-! ## The prologue -/

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- Our caller's registers and return address saved. -/
theorem save_ok {scr : Reg} (hs : σ.gpr scr = P.scr) (h0 : scr ≠ .r0) :
    WP isa (.block [.mflr .r0, .store .d .r27 scr 2000, .store .d .r28 scr 2008, .store .d .r29 scr 2016,
      .store .d .r30 scr 2024, .store .d .r31 scr 2032, .store .d .r0 scr 2040]) σ fun s =>
      (∀ r, r ≠ .r0 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
      s.mem = ((((((σ.mem.writeW (P.scr + BitVec.ofNat 64 2000) (σ.gpr .r27)).writeW
        (P.scr + BitVec.ofNat 64 2008) (σ.gpr .r28)).writeW (P.scr + BitVec.ofNat 64 2016) (σ.gpr .r29)).writeW
        (P.scr + BitVec.ofNat 64 2024) (σ.gpr .r30)).writeW (P.scr + BitVec.ofNat 64 2032) (σ.gpr .r31)).writeW
        (P.scr + BitVec.ofNat 64 2040) σ.lr) := by
  have w0 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2000) 8 := inScr hp rfl (by decide)
  have w1 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2008) 8 := inScr hp rfl (by decide)
  have w2 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2016) 8 := inScr hp rfl (by decide)
  have w3 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2024) 8 := inScr hp rfl (by decide)
  have w4 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2032) 8 := inScr hp rfl (by decide)
  have w5 : InRegions σ.wr (P.scr + BitVec.ofNat 64 2040) 8 := inScr hp rfl (by decide)
  prun [hs, h0, w0, w1, w2, w3, w4, w5]
  exact ⟨fun r hr => RegUpd.gpr_write_of_ne (s := σ) _ hr, by trivial⟩

/-- The prologue, given what its moves leave: `J0`, and `r27` = `v27`. -/
theorem pro_ok {scr a msg : Reg} {len prm : List Instr} (hs : σ.gpr scr = P.scr) (h0 : scr ≠ .r0)
    {v27 : BitVec 64}
    (hmv : ∀ t : State, (∀ r, r ≠ .r0 → t.gpr r = σ.gpr r) →
      WP isa (.block (([mov .r31 scr, mov .r30 a, mov .r29 msg] : List Instr) ++ len ++ prm)) t fun t' =>
        t'.gpr .r31 = P.scr ∧ t'.gpr .r30 = P.a ∧ t'.gpr .r29 = P.sd ∧ t'.gpr .r28 = BitVec.ofNat 64 P.len ∧
        t'.gpr .r27 = v27 ∧
        (∀ r ∈ preserved, r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp) :
    WP isa (.block (pro scr a msg len prm)) σ fun s => J0 P σ s ∧ s.gpr .r27 = v27 := by
  have fs := hp.fscr
  rw [show pro scr a msg len prm = ([.mflr .r0, .store .d .r27 scr 2000, .store .d .r28 scr 2008,
      .store .d .r29 scr 2016, .store .d .r30 scr 2024, .store .d .r31 scr 2032, .store .d .r0 scr 2040] :
      List Instr) ++ (([mov .r31 scr, mov .r30 a, mov .r29 msg] : List Instr) ++ len ++ prm) from rfl,
    WP.block_append_iff]
  refine WP.mono (save_ok hp hs h0) fun s1 ⟨g1, rd1, wr1, sp1, m1⟩ => ?_
  refine WP.mono (hmv s1 g1) fun s2 ⟨g31, g30, g29, g28, g27, cs, m2, rd2, wr2, sp2⟩ => ?_
  have fr : Frame [P.aR, P.scrR, below σ.sp 48] σ.mem s2.mem := by
    rw [m2, m1]
    refine (((((((Frame.refl _ _).writeW (r := P.scrR) (by simp) _ ?_).writeW (r := P.scrR) (by simp) _ ?_).writeW
      (r := P.scrR) (by simp) _ ?_).writeW (r := P.scrR) (by simp) _ ?_).writeW (r := P.scrR) (by simp) _ ?_).writeW
      (r := P.scrR) (by simp) _ ?_) <;> exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨⟨rd2.trans rd1, wr2.trans wr1, sp2.trans sp1, g30, g31,
    fun r hr a b c d e => (cs r hr a b c d e).trans (g1 r (pres_of hr)), ?_, ?_, ?_, ?_, ?_, ?_, fr⟩, g29, g28⟩,
    g27⟩ <;>
  · rw [m2, m1]
    simp (disch := decide) only [Sp.at', readW_writeW_off, Mem.readW_writeW_self64]

/-- The prologue of `vg_mldsa_rej_ntt_poly`: `seed = r3`, `a = r4`,
`scratch = r5`; `r27` is our caller's. -/
theorem pro_rn (h3 : σ.gpr .r3 = P.sd) (h4 : σ.gpr .r4 = P.a) (h5 : σ.gpr .r5 = P.scr) (hlen : P.len = 34) :
    WP isa (.block (pro .r5 .r4 .r3 [.li .r28 34] [])) σ fun s => J0 P σ s ∧ s.gpr .r27 = σ.gpr .r27 :=
  pro_ok hp h5 (by decide) fun t ht => by
    have e3 := ht .r3 (by decide)
    have e4 := ht .r4 (by decide)
    have e5 := ht .r5 (by decide)
    have e27 := ht .r27 (by decide)
    prun [List.append_nil, List.cons_append, List.nil_append, e3, e4, e5, e27, h3, h4, h5, hlen]
    simp only [true_and, and_true]
    intro r hr a b c d e
    simp only [RegUpd.gpr_write, b, c, d, e, ite_false]

/-- The prologue of `vg_mldsa_rej_bounded_poly` and
`vg_mldsa_expand_mask_poly`: `seed = r3`, the parameter in `r4`, `a = r5`,
`scratch = r6`; `r27` is the parameter, zero-extended. -/
theorem pro_rb (h3 : σ.gpr .r3 = P.sd) (h5 : σ.gpr .r5 = P.a) (h6 : σ.gpr .r6 = P.scr) (hlen : P.len = 66) :
    WP isa (.block (pro .r6 .r5 .r3 [.li .r28 66] (zext32 .r27 .r4))) σ fun s =>
      J0 P σ s ∧ s.gpr .r27 = zx (σ.gpr .r4) :=
  pro_ok hp h6 (by decide) fun t ht => by
    have e3 := ht .r3 (by decide)
    have e4 := ht .r4 (by decide)
    have e5 := ht .r5 (by decide)
    have e6 := ht .r6 (by decide)
    prun [zext32, List.cons_append, List.nil_append, e3, e4, e5, e6, h3, h5, h6, hlen]
    simp only [true_and, and_true]
    intro r hr a b c d e
    simp only [RegUpd.gpr_write, a, b, c, d, e, ite_false]

/-- The prologue of `vg_mldsa_sample_in_ball`: `ctilde = r3`, its length in
`r4`, `tau = r5`, `c = r6`, `scratch = r7`; `r27` is `tau`, zero-extended. -/
theorem pro_ball (h3 : σ.gpr .r3 = P.sd) (h4 : σ.gpr .r4 = BitVec.ofNat 64 P.len) (h6 : σ.gpr .r6 = P.a)
    (h7 : σ.gpr .r7 = P.scr) :
    WP isa (.block (pro .r7 .r6 .r3 [mov .r28 .r4] (zext32 .r27 .r5))) σ fun s =>
      J0 P σ s ∧ s.gpr .r27 = zx (σ.gpr .r5) :=
  pro_ok hp h7 (by decide) fun t ht => by
    have e3 := ht .r3 (by decide)
    have e4 := ht .r4 (by decide)
    have e5 := ht .r5 (by decide)
    have e6 := ht .r6 (by decide)
    have e7 := ht .r7 (by decide)
    prun [zext32, List.cons_append, List.nil_append, e3, e4, e5, e6, e7, h3, h4, h6, h7]
    simp only [true_and, and_true]
    intro r hr a b c d e
    simp only [RegUpd.gpr_write, a, b, c, d, e, ite_false]

end

/-! ## The epilogue -/

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The epilogue: our caller's registers restored, the memory and the
registers but `r0` and `r27`–`r31` unchanged. -/
theorem epi_ok {s : State} (he : Env P σ s) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ .r0 → r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s'.gpr r = s.gpr r := by
  have i0 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2000) 8 := inScrRd hp he.wr (by decide)
  have i1 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2008) 8 := inScrRd hp he.wr (by decide)
  have i2 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2016) 8 := inScrRd hp he.wr (by decide)
  have i3 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2024) 8 := inScrRd hp he.wr (by decide)
  have i4 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2032) 8 := inScrRd hp he.wr (by decide)
  have i5 : InRegions (s.rd ++ s.wr) (P.scr + BitVec.ofNat 64 2040) 8 := inScrRd hp he.wr (by decide)
  have s27 : s.mem.readW (P.scr + BitVec.ofNat 64 2000) 64 = σ.gpr .r27 := he.s27
  have s28 : s.mem.readW (P.scr + BitVec.ofNat 64 2008) 64 = σ.gpr .r28 := he.s28
  have s29 : s.mem.readW (P.scr + BitVec.ofNat 64 2016) 64 = σ.gpr .r29 := he.s29
  have s30 : s.mem.readW (P.scr + BitVec.ofNat 64 2024) 64 = σ.gpr .r30 := he.s30
  have s31 : s.mem.readW (P.scr + BitVec.ofNat 64 2032) 64 = σ.gpr .r31 := he.s31
  have slr : s.mem.readW (P.scr + BitVec.ofNat 64 2040) 64 = σ.lr := he.slr
  have hk : WP isa (.block epi) s fun s' => s'.lr = σ.lr ∧ s'.gpr .r27 = σ.gpr .r27 ∧
      s'.gpr .r28 = σ.gpr .r28 ∧ s'.gpr .r29 = σ.gpr .r29 ∧ s'.gpr .r30 = σ.gpr .r30 ∧
      s'.gpr .r31 = σ.gpr .r31 ∧
      (∀ r, r ≠ .r0 → r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp := by
    prun [epi, he.r31, i0, i1, i2, i3, i4, i5, s27, s28, s29, s30, s31, slr]
    simp only [true_and, and_true]
    intro r h0 a b c d e
    simp only [RegUpd.gpr_write, h0, a, b, c, d, e, ite_false]
  refine WP.mono hk fun s' ⟨lr, r27, r28, r29, r30, r31, g, m, sp⟩ => ⟨⟨fun r hr => ?_, sp.trans he.sp, lr⟩, m, g⟩
  by_cases a : r = .r27
  · subst a; exact r27
  by_cases b : r = .r28
  · subst b; exact r28
  by_cases c : r = .r29
  · subst c; exact r29
  by_cases d : r = .r30
  · subst d; exact r30
  by_cases e : r = .r31
  · subst e; exact r31
  exact (g r (pres_of hr) a b c d e).trans (he.cs r hr a b c d e)

/-- The end of a sampling function that returns whether `j` (in `r5`) is 256. -/
theorem retEpi_ok {s : State} (he : Env P σ s) {j : Nat} (hj : s.gpr .r5 = BitVec.ofNat 64 j) (hj' : j ≤ 256) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .r3 = (if j = 256 then 1 else 0) ∧ s'.mem = s.mem ∧ abiPreserved σ s' := by
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun s1 => s1 = s.write .r3 (s.gpr .r5 >>> 8)) (by prun [retJ]) fun s1 e1 => ?_
  subst e1
  have he1 : Env P σ (s.write .r3 (s.gpr .r5 >>> 8)) := he.regs hp rfl (fun r hr =>
    RegUpd.gpr_write_of_ne (s := s) (r := .r3) (r' := r) _ (by rintro rfl; exact absurd hr (by decide))) rfl rfl rfl
  refine WP.mono (epi_ok hp he1) fun s' ⟨ha, hm, g⟩ => ⟨?_, hm, ha⟩
  rw [g .r3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), RegUpd.gpr_write_self, hj,
    ret_val hj']

end

/-! ## Storing a coefficient -/

/-- The next coefficient is `a[j]` for the `j` = `L.length` coefficients `L`
stored so far. -/
structure At (P : Sp) (L : List Zq) (s : State) : Prop where
  r4 : s.gpr .r4 = P.a + BitVec.ofNat 64 (4 * L.length)
  r5 : s.gpr .r5 = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  st : Stored s.mem P.a L

theorem accept_skip {v : Reg} {s : State} (h : s.gpr .r12 = 0) : WP isa (accept v) s fun s' => s' = s :=
  WP.ite _ (eval_zero _ _) (fun _ => wp_nil rfl) fun e => absurd e (by simp [h])

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- `accept v` stores `v` as `a[j]` when `r12 ≠ 0`. -/
theorem accept_store {s : State} (he : Env P σ s) {v : Reg} {L : List Zq}
    (ha : At P L s) (hL : L.length < 256) {x : Zq} (hx : (s.gpr v).setWidth 32 = zw x) (h : s.gpr .r12 ≠ 0) :
    WP isa (accept v) s fun s' => At P (L ++ [x]) s' ∧ Env P σ s' ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) ∧ Frame [P.aR] s.mem s'.mem := by
  have cA := coeff_contains P.a (i := L.length) hL
  have iA : InRegions s.wr (P.a + BitVec.ofNat 64 (4 * L.length)) 4 :=
    ⟨P.aR, by rw [he.wr, hp.wr]; simp, cA⟩
  refine WP.ite _ (eval_zero _ _) (fun e => absurd (beq_iff_eq.mp e) h) fun _ => ?_
  have hblk : WP isa (.block [.store .w v .r4 0, .addi .r4 .r4 4, .addi .r5 .r5 1]) s fun t =>
      t.mem = s.mem.writeW (P.a + BitVec.ofNat 64 (4 * L.length)) ((s.gpr v).setWidth 32) ∧
      t.gpr .r4 = P.a + BitVec.ofNat 64 (4 * L.length) + BitVec.ofNat 64 4 ∧
      t.gpr .r5 = BitVec.ofNat 64 L.length + BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [exec_store_w, ha.r4, ha.r5, iA]
    simp only [true_and, and_true]
    intro r h4 h5
    simp only [RegUpd.gpr_write, h4, h5, ite_false]
  refine WP.mono hblk fun t ⟨m, r4, r5, rr, rd, wr, sp⟩ => ?_
  have hf : Frame [P.aR] s.mem t.mem := by rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cA
  refine ⟨⟨?_, ?_, ?_, ?_⟩, he.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (fun r hr => rr r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    rd wr sp, rr, hf⟩
  · rw [r4, List.length_append, List.length_singleton]; exact MlKem.PPC64LE.ptr_succ _ 4 _
  · rw [r5, List.length_append, List.length_singleton, BitVec.ofNat_add]
  · simp only [List.length_append, List.length_singleton]; omega
  · rw [m, hx]; exact stored_snoc ha.st hL x

end

/-! ## Constant time -/

theorem pro_rn_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h5 : ∀ a b, R a b → a.gpr .r5 = b.gpr .r5) :
    RelCT isa R (.block (pro .r5 .r4 .r3 [.li .r28 34] [])) fun _ _ => True :=
  taint_block [.r5] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h5 a b hab)
    (by taint_decide)

theorem pro_rb_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h6 : ∀ a b, R a b → a.gpr .r6 = b.gpr .r6) :
    RelCT isa R (.block (pro .r6 .r5 .r3 [.li .r28 66] (zext32 .r27 .r4))) fun _ _ => True :=
  taint_block [.r6] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h6 a b hab)
    (by taint_decide)

theorem pro_ball_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h7 : ∀ a b, R a b → a.gpr .r7 = b.gpr .r7) :
    RelCT isa R (.block (pro .r7 .r6 .r3 [mov .r28 .r4] (zext32 .r27 .r5))) fun _ _ => True :=
  taint_block [.r7] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h7 a b hab)
    (by taint_decide)

theorem retEpi_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h31 : ∀ a b, R a b → a.gpr .r31 = b.gpr .r31) :
    RelCT isa R (.block (retJ ++ epi)) fun _ _ => True :=
  taint_block [.r31] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h31 a b hab)
    (by taint_decide)

theorem epi_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h31 : ∀ a b, R a b → a.gpr .r31 = b.gpr .r31) :
    RelCT isa R (.block epi) fun _ _ => True :=
  taint_block [.r31] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h31 a b hab)
    (by taint_decide)

/-- A coefficient stored or not, in both runs alike. -/
theorem accept_ct {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (hz : ∀ a b, R a b → a.gpr .r12 = b.gpr .r12) (h4 : ∀ a b, R a b → a.gpr .r4 = b.gpr .r4) :
    RelCT isa R (accept .r10) fun _ _ => True := by
  refine RelCT.ite (fun a b hab => by rw [eval_zero, eval_zero, hz a b hab]) ?_ ?_
  · exact taint_block [] (fun a b hab => hsp a b hab.1) (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide)
  · exact taint_block [.r4] (fun a b hab => hsp a b hab.1) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h4 a b hab.1) (by taint_decide)

end VG.Proof.MlDsa.PPC64LE.Sample
