module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptBody
public import VerifiedGarbage.Proof.Ffdh.ContextRows
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Ffdh.Domain

import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_generate_key_cached` on RISC-V: correctness

The context's words (`cx_of_pre`, from `generationContextAt`); then
`Generate.code` runs the front (`cgFront_ok`), loads and checks p
(`loadP_X`), runs the body (`bodyC_ok`) and restores the callee-saved
registers (`cg_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.GenerateKey (XR)
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

/-- The public scalar width of an attempt. -/
abbrev cgBits (s : State) : Nat := Spec.Ffdh.generationScalarBits (cgA s)

theorem ctxWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = ctxWords ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords,
    ctxWords]
  omega_arith

/-- A row of the context holding `toWords V w`. -/
theorem row_val {m : Mem} {C : Addr} {w j V : Nat} (h : ContextRows.row m C w j = Spec.Rsa.toWords V w)
    (hV : V < 2 ^ (64 * w)) : wordsVal m C (rowOff w j) w = V := by
  rw [Pub.wsv_wv, rowOff, ← Nat.mul_assoc]
  exact ContextRows.value_of_row h hV

/-- The context's words, from the precondition. -/
theorem ctxw_of_pre {s : State} (h : cgContract.pre s) :
    let a := cgA s
    let bits := cgBits s
    let w := ((s.gpr .a6).toNat + 7) / 8
    word s.mem (stackArg s 3) 0 = BitVec.ofNat 64 bits ∧
      word s.mem (stackArg s 3) 8 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      word s.mem (stackArg s 3) 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      wordsVal s.mem (stackArg s 3) (rowOff w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % a.p ∧
      ∀ e < 32, ent s.mem (stackArg s 3) w e = combM a.g a.p w (Spec.Rsa.FixedBaseComb.exponent bits e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, hL, -, -, -, -, hdv, hctx,
    -⟩ := h
  have hLk : 2 * (s.gpr .a6).toNat ≤ (s.gpr .a5).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have hmod := Proof.Ffdh.domainValid_mod hdv
  have heq := Proof.Ffdh.generationPrecompute_eq (pLen := (s.gpr .a6).toNat) (dom := cgDom s)
    (by simp only [cgDom, VG.Proof.Bignum.bytesAt_length]; omega_arith) hmod
  have hw := hctx.2
  rw [heq, hctx.1, Option.some.injEq] at hw
  have hv := ContextRows.ctx_of_values (m := s.mem) (cp := stackArg s 3) (len := (s.gpr .a6).toNat)
    (dom := cgDom s) (by rw [show 3 + 34 * Spec.Rsa.modulusWords (s.gpr .a6).toNat =
      Spec.Ffdh.generationPrecomputedWords (s.gpr .a6).toNat by rw [ctxWords_eq]; rfl]; exact hw.symm)
  obtain ⟨e0, e8, e16, _, r1, re⟩ := hv
  simp only [Spec.Rsa.modulusWords] at r1 re
  have hP : 0 < (cgA s).p := Nat.lt_trans Nat.zero_lt_one (VG.Proof.Bignum.valid_facts hmod hk).2.1
  have hp64 : (cgA s).p < 2 ^ (64 * (((s.gpr .a6).toNat + 7) / 8)) := by
    have h1 := VG.Proof.Bignum.os2ip_lt ((cgDom s).take (s.gpr .a6).toNat)
    have h2 : 256 ^ ((cgDom s).take (s.gpr .a6).toNat).length ≤ 2 ^ (64 * (((s.gpr .a6).toNat + 7) / 8)) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega_arith)
    change Spec.Rsa.os2ip ((cgDom s).take (s.gpr .a6).toNat) < _
    omega_arith
  refine ⟨e0, e8, e16, ?_, fun e he => ?_⟩
  · rw [row_val r1 (Nat.lt_of_lt_of_le (Nat.mod_lt _ hP) (Nat.le_of_lt hp64)), ← Nat.pow_add]
    congr 2; omega_arith
  · have := row_val (re e he) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hP) (Nat.le_of_lt hp64))
    rw [Nat.add_comm 2 e] at this
    exact this

theorem cgx_p {s : State} : (cgx s).p = (cgA s).p := rfl

/-- `CX` after the front, from the precondition. -/
theorem cx_of_pre {s u : State} (h : cgContract.pre s) (hrd : u.rd = s.rd)
    (ho : Outside (stackArg s 1) 0 ((stackArg s 2).toNat * 8) s.mem u.mem)
    (hch : CH (stackArg s 1) (stackArg s 3) s.mem u.mem) :
    CX (cgx s) (stackArg s 3) (cgBits s) (cgA s).g u := by
  have hw := ctxw_of_pre h
  obtain ⟨hrd0, hwr0, dXY, dXD, dXR, dXS, dXC, dXA, dYD, dYR, dYS, dYC, dYA, dDS, dRS, dSC, dSA, nwX, nwY, nwD,
    nwR, nwS, nwC, ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, hdv, hctx, alS, alC, alsp⟩ := h
  obtain ⟨e0, e8, e16, r1, re⟩ := hw
  have hLk : 2 * (s.gpr .a6).toNat ≤ (s.gpr .a5).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have hCl : (stackArg s 4).toNat = ctxWords (((s.gpr .a6).toNat + 7) / 8) := by rw [hctx.1, ctxWords_eq]
  have sepC : ∀ y, ofs (stackArg s 3) y < 8 * ctxWords (((s.gpr .a6).toNat + 7) / 8) →
      (stackArg s 2).toNat * 8 ≤ ofs (stackArg s 1) y := fun y hy =>
    Pub.sep_of_disjoint dSC.symm y (by
      have h' : (y - stackArg s 3).toNat < 8 * ctxWords (((s.gpr .a6).toNat + 7) / 8) := hy
      show (y - stackArg s 3).toNat < _
      rw [hCl]; omega_arith)
  have hctxO : Outside (stackArg s 3) (8 * ctxWords (((s.gpr .a6).toNat + 7) / 8)) (2 ^ 64) s.mem u.mem :=
    ctx_of_scr ho (by omega_arith) sepC
  have hcn : (stackArg s 3).toNat + 8 * ctxWords (((s.gpr .a6).toNat + 7) / 8) ≤ 2 ^ 64 := by rw [← hCl]; omega_arith
  have hgb := ContextRows.genBits_facts hdv
  refine ⟨hch.ctx, hch.bits.trans e0, hch.bytes.trans e8, hch.rows.trans e16,
    ⟨hcn, fun d hd => by
      have hd' : d + 8 ≤ 8 * ctxWords (((s.gpr .a6).toNat + 7) / 8) := hd
      exact ⟨⟨stackArg s 3, (stackArg s 4).toNat * 8⟩, List.mem_append_left _ (by rw [hrd, hrd0]; simp),
        Offset.contains_base _ (show d + 8 ≤ (stackArg s 4).toNat * 8 by rw [hCl]; omega_arith)
          (by omega_arith)⟩, alC, sepC⟩,
    fun y hy => by
      have h' : (y - stackArg s 3).toNat < 8 * ctxWords (((s.gpr .a6).toNat + 7) / 8) := hy
      have := Pub.sep_of_disjoint dXC.symm y (by show (y - stackArg s 3).toNat < _; rw [hCl]; omega_arith)
      rw [hxl] at this; exact this,
    fun y hy => by
      have h' : (y - stackArg s 3).toNat < 8 * ctxWords (((s.gpr .a6).toNat + 7) / 8) := hy
      have := Pub.sep_of_disjoint dYC.symm y (by show (y - stackArg s 3).toNat < _; rw [hCl]; omega_arith)
      rw [hyl] at this; exact this,
    fun a ha => by
      show ent u.mem _ (((s.gpr .a6).toNat + 7) / 8) a = _
      rw [ent_keep hctxO hcn ha]; exact re a ha,
    by
      show wordsVal u.mem _ (rowOff (((s.gpr .a6).toNat + 7) / 8) 1) (((s.gpr .a6).toNat + 7) / 8) = _
      have hr1 := row_fits (w := ((s.gpr .a6).toNat + 7) / 8) (j := 1) (by decide)
      rw [Outside.wordsVal hctxO (Or.inl hr1) (by omega_arith)]; exact r1,
    ?_, hgb.1, hgb.2⟩
  show Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (off (s.gpr .a4) (s.gpr .a6).toNat) (s.gpr .a6).toNat) = _
  rw [Pub.bytes_apart (o := 0) (Z := (stackArg s 2).toNat * 8) ho (by omega_arith) fun i hi y hy => by
      have h' := Pub.ne_of_disjoint dDS (Nat.le_of_lt (s.gpr .a5).isLt) ((s.gpr .a6).toNat + i) (by omega_arith) y hy
      intro e; apply h'; rw [← e]; exact (Derive.off_off _ _ _).symm,
    Proof.Ffdh.domainOf_g _ _ hLk]

/-- x's and `rand`'s facts, from the precondition. -/
theorem cgXR {s t : State} (h : cgContract.pre s) (r3 : t.rd = s.rd) (w3 : t.wr = s.wr) :
    XR (cgx s) (s.gpr .a7) t := by
  obtain ⟨hrd, hwr, dXY, dXD, dXR, dXS, dXC, dXA, dYD, dYR, dYS, dYC, dYA, dDS, dRS, dSC, dSA, nwX, nwY, nwD,
    nwR, nwS, nwC, ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, hdv, hctx, alS, alC, alsp⟩ := h
  refine ⟨fun i hi => ?_, by change (s.gpr .a0).toNat + (s.gpr .a6).toNat ≤ _; omega_arith,
    fun y hy => by
      change ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 at hy
      change (s.gpr .a6).toNat ≤ ofs (s.gpr .a0) y
      have := Pub.sep_of_disjoint dXS.symm y hy
      rw [hxl] at this; exact this,
    fun i hi y hy => Pub.ne_of_disjoint dXD.symm (Nat.le_of_lt (s.gpr .a5).isLt) i hi y (by rw [hxl]; exact hy),
    fun i hi => ?_, fun i hi y hy => Pub.ne_of_disjoint dXR.symm (Nat.le_of_lt (stackArg s 0).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith) y (by rw [hxl]; exact hy),
    fun i hi => Pub.ne_of_disjoint dRS (Nat.le_of_lt (stackArg s 0).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith), rfl,
    fun i hi y hy => Pub.ne_of_disjoint dXY (Nat.le_of_lt (s.gpr .a1).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith) y (by rw [hyl]; exact hy),
    fun y hy => by
      change ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 at hy
      change (s.gpr .a6).toNat ≤ ofs (s.gpr .a2) y
      have := Pub.sep_of_disjoint dYS.symm y hy
      rw [hyl] at this; exact this,
    fun i hi y hy => Pub.ne_of_disjoint dXY.symm (Nat.le_of_lt (s.gpr .a3).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith) y (by rw [hxl]; exact hy)⟩
  · change i < (s.gpr .a6).toNat at hi
    rw [w3, hwr]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · change i < (s.gpr .a6).toNat at hi
    rw [r3, w3]
    exact rd_of_mem (L := (stackArg s 0).toNat) (by rw [hrd]; simp) (by omega_arith) (BitVec.isLt _) i hi

theorem ret_status (n : Nat) (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- Every register but `ra`. -/
def cgNotRa : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10,
    .s11, .t3, .t4, .t5, .t6]

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem cg_correct (s : State) (h : cgContract.pre s) :
    ∃ tr t, Exec isa Generate.code s tr t ∧ abiPreserved s t ∧ cgContract.post s t := by
  show WP isa Generate.code s fun t => abiPreserved s t ∧ cgContract.post s t
  suffices main : WP isa Generate.code s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ cgContract.post s t from
    WP.mono (WP.rdwr (WP.keep cgNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dXY, dXD, dXR, dXS, dXC, dXA, dYD, dYR, dYS, dYC, dYA, dDS, dRS, dSC, dSA, nwX, nwY, nwD,
    nwR, nwS, nwC, ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, hdv, hctx, alS, alC, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : 2 * (s.gpr .a6).toNat ≤ (s.gpr .a5).toNat ∧ (s.gpr .a5).toNat ≤ 3 * (s.gpr .a6).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  unfold Generate.code
  refine WP.seq (WP.mono (WP.rdwr (cgFront_ok hpre)) fun s₃ ⟨⟨hb3, ha3, ht1, hsv, hch3, k3, o3⟩, r3, w3, _⟩ => ?_)
  have hx3 : XR (cgx s) (s.gpr .a7) s₃ := cgXR hpre r3 w3
  have hc := hb3.ctx
  have hnS := hc.scr.nowrap
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  have hOZ3 : Outside (stackArg s 1) 0 ((stackArg s 2).toNat * 8) s.mem s₃.mem :=
    o3.mono (Nat.le_refl _) (by omega_arith)
  have hcx3 := cx_of_pre hpre r3 hOZ3 hch3
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadP_X hb3) (by rfl)))
    fun s₄ ⟨⟨⟨h4, a4⟩, k4⟩, r4, w4, _⟩ => ?_)
  have hcx4 := hcx3.keep hc r4 w4 a4
  have hx4 := hx3.keep r4 w4
  have ha4 := ha3.keep k4
  have h14 : s₄.gpr .t1 = s.gpr .a7 := (k4.gpr (by decide)).trans ht1
  have hv := Proof.Ffdh.domainValid_mod hdv
  have hz4 : s₄.gpr .s0 = 0 := h4.2.2.mpr hv
  refine WP.seq (WP.mono (WP.rdwr (show WP isa (.ite (.zero .s0) body (.block [.li .a0 0])) s₄
      (GPost (cgx s) (s.gpr .a7) (cgBits s) (cgA s).g s₄) from
    WP.ite (s₄.gpr .s0 == 0) (Steps.eval_zero _ _) (fun _ => bodyC_ok h4 hz4 ha4 hx4 h14 rfl hcx4)
      (fun hb => absurd hz4 (by simpa using hb)))) fun t₅ ⟨⟨tpost, t6, tw⟩, r5, w5, _⟩ => ?_)
  change Outside (stackArg s 1) 256 ((stackArg s 2).toNat * 8 - 256) s₃.mem s₄.mem at a4
  change (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 at hnS
  -- The saved registers' words.
  have hin : ∀ i < 12, InRegions t₅.wr (off (savW (stackArg s 1)) (8 * i)) 8 := fun i hi => by
    rw [w5, w4, w3, hwr]
    show InRegions _ (stackArg s 1 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t₅.mem.readW (off (savW (stackArg s 1)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
      fun i hi => by
    have e : off (savW (stackArg s 1)) (8 * i) = off (stackArg s 1) (128 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [← hsv i hi, e]
    show word t₅.mem (stackArg s 1) (128 + 8 * i) = word s₃.mem (stackArg s 1) (128 + 8 * i)
    exact (tw (128 + 8 * i) (by omega_arith)).trans (Outside.word a4 (Or.inl (by omega_arith)) (by omega_arith))
  refine WP.mono (Pub.restore_ok t₅ (S := stackArg s 1) (v := fun i => s.gpr (PublicChecked.saved i)) t6 hin
    (fun i hi => Pub.sav_al alS (by omega_arith) hi) hsav) fun u ⟨urs, uot, um, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact urs i hi
  -- The postcondition.
  have hOZ : Outside (stackArg s 1) 0 ((stackArg s 2).toNat * 8) s.mem s₄.mem :=
    hOZ3.trans (a4.mono (by omega_arith) (by omega_arith))
  have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₄.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq =>
    Pub.bytes_apart (o := 0) hOZ (by omega_arith) hq
  have hsepD : ∀ j n, j + n ≤ (s.gpr .a5).toNat →
      Spec.Rsa.bytesAt s₄.mem (off (s.gpr .a4) j) n = Spec.Rsa.bytesAt s.mem (off (s.gpr .a4) j) n :=
    fun j n hjn => hsep _ _ fun i hi => by
      have h' := hc.sepD (j + i) (by change _ < (s.gpr .a5).toNat; omega_arith); rw [← Derive.off_off] at h'; exact h'
  have bR : Spec.Rsa.bytesAt s₄.mem (s.gpr .a7) (s.gpr .a6).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat := by
    rw [hrl]; exact hsep _ _ fun i hi => Pub.ne_of_disjoint dRS (Nat.le_of_lt (stackArg s 0).isLt) i (by omega_arith)
  have bB : bnd s₄.mem (cgx s).D (cgx s).k (cgx s).L (cgx s).p =
      bnd s.mem (s.gpr .a4) (s.gpr .a6).toNat (s.gpr .a5).toNat (cgx s).p := by
    unfold bnd
    by_cases hq : (cgx s).L = 3 * (cgx s).k
    · have hq' : (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hq
      rw [ite_eq_left hq, ite_eq_left hq']
      exact congrArg Spec.Rsa.os2ip (hsepD (2 * (s.gpr .a6).toNat) (s.gpr .a6).toNat (by omega_arith))
    · rw [ite_eq_right hq, ite_eq_right (show ¬ (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat from hq)]
  have hpe : (cgA s).p = (cgx s).p := rfl
  have hpD : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a6).toNat) = (cgx s).p := by
    rw [← hpe, Proof.Ffdh.domainOf_p _ _ hLk.1]
  have hgD : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (s.gpr .a4) (s.gpr .a6).toNat) (s.gpr .a6).toNat) =
      (cgA s).g := by rw [Proof.Ffdh.domainOf_g _ _ hLk.1]
  obtain ⟨ta, tO, tX⟩ := tpost hv
  have hL' : (s.gpr .a5).toNat = 2 * (s.gpr .a6).toNat ∨ (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hL
  -- The scalar.
  have hsc : Spec.Rsa.os2ip (xoOf s₄.mem (s.gpr .a7) (cgx s).k (cgBits s)) = cgScalar s := by
    show Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt s₄.mem (s.gpr .a7) (s.gpr .a6).toNat) _ _) = _
    rw [scalarC_value (by simp [Spec.Rsa.bytesAt]; rfl) hcx4.b1 hcx4.bk, bR]
    rfl
  have hst : stat (cgx s) s₄.mem (cgA s).g (Spec.Rsa.os2ip (xoOf s₄.mem (s.gpr .a7) (cgx s).k (cgBits s))) =
      Spec.Ffdh.keyStatus (cgA s) (cgScalar s) := by
    rw [show cgA s = Spec.Ffdh.domainOf (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      from rfl, Derive.keyStatus_dom (by omega_arith) hL' hdv, hsc, hpD, hgD]
    unfold stat
    rw [bB]
  rw [hst] at ta tO tX
  show _ ∧ _
  rw [um, uot .a0 (by decide), ta, ret_status _ (by
    have := stat_lt (cgx s) s₄.mem (cgA s).g (Spec.Rsa.os2ip (xoOf s₄.mem (s.gpr .a7) (cgx s).k (cgBits s)))
    rw [hst] at this; omega_arith)]
  refine ⟨rfl, ?_⟩
  rw [hsc, show (cgx s).O = s.gpr .a2 from rfl, show (cgx s).k = (s.gpr .a6).toNat from rfl] at tO
  rw [show (cgx s).X = s.gpr .a0 from rfl, show (cgx s).k = (s.gpr .a6).toNat from rfl] at tX
  rw [tO, tX]
  split
  · refine ⟨?_, by rw [VG.Proof.Bignum.powMod_eq]; rfl⟩
    rw [← hsc]
    have := VG.Proof.Rsa.i2osp_os2ip (xoOf s₄.mem (s.gpr .a7) (s.gpr .a6).toNat (cgBits s))
    have hb1 := hcx4.b1
    have hbk : cgBits s ≤ 8 * (s.gpr .a6).toNat := hcx4.bk
    rw [VG.Proof.Ffdh.KeyScalar.cut_length _ (by simp [Spec.Rsa.bytesAt]; omega_arith)] at this
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this.symm
  · exact ⟨rfl, rfl⟩

end VG.Proof.Ffdh.RISCV64.Cached
