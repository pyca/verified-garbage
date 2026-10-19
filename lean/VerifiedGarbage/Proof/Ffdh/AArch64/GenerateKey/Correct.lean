module

public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Finish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_ffdh_generate_key` on AArch64: correctness

From `gkContract`'s precondition, `GenerateKey.code` returns the attempt's
status and writes its key, or zeros (`gk_correct`), by its stages.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Ffdh

/-- A step that keeps the caller's registers and the outputs' regions. -/
theorem dk {p : GkP} {s₀ t : State} {c : Prog isa} {P Q : State → Prop} (hk : KX s₀ t) (hd : Dst p t)
    (h : WP isa c t fun u => P u ∧ KX t u) (k : ∀ u, P u → KX s₀ u → Dst p u → Q u) : WP isa c t Q :=
  WP.mono h fun u ⟨hp, k'⟩ => k u hp (keep_trans hk k') (hd.keep k')

theorem scalar_eq : GenerateKey.scalar = GenerateKey.bound ++ ([.block (GenerateKey.smear ++ [mov .x12 .x3,
    ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, ldh .x1 sRand, movi .x13 255, movi .x7 0,
    movi .x10 0, ldh .x14 sK]), countLoop .x14 GenerateKey.cutBody] : List (Prog isa)) := rfl

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    GenerateKey.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++ (.block [leave] ::
      (GenerateKey.scalar ++ (.block [enter] :: (Crt.loadArr aXm sX sK ++ (CheckPrivate.scalarRange ++
        ([.ite (.zero .x .x9) (.seq (.block [leave]) (GenerateKey.fail 2))
          (seqs (GenerateKey.tail W.code S.code M.mm))] : List (Prog isa)))))))) := by
  simp only [GenerateKey.main, List.append_assoc]
  rfl

/-- The block that points `sEp` at the scalar's significant octets. -/
abbrev epBlk : List Instr :=
  [ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, .add .x .x3 .x2 .x11, sth .x3 sEp, enter]

/-- The q branch. -/
abbrev qBr (W : Window) (M : Mont) (S : Selector) : Prog isa :=
  seqs (scan sQ ++ [.block [enter]] ++ pow W.code S.code M.mm sY sK sEp sEl ++ isOne aY ++
    [.block [leave, ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]])

theorem tail_eq (W : Window) (M : Mont) (S : Selector) :
    GenerateKey.tail W.code S.code M.mm = r2Steps M.mm ++ (.block [leave] :: (GenerateKey.bound ++
      (.block epBlk :: (pow W.code S.code M.mm sG sK sEp sEl ++ (range aY ++
        (.block yBlk :: storeBE :: .block [ldh .x9 sF, leave, sth .x9 sF] :: .block qTest ::
          [.ite (.zero .x .x3) (.block []) (qBr W M S), .block [ldh .x9 sF, movi .x7 0, .sub .x .x15 .x7 .x9],
            GenerateKey.maskOut sX, GenerateKey.maskOut sY,
            .block [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]])))))) := by
  simp only [GenerateKey.tail, List.append_assoc]
  rfl

theorem scalarRange_eq : CheckPrivate.scalarRange = isNonzero aXm ++ (.block [sth .x9 sF, leave] ::
    .block qTest :: [.ite (.zero .x .x3) (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY)), .block andF]) := rfl

/-- The public data of a state. -/
def gkOf (s : State) : GkP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .x6).toNat, (s.gpr .x5).toNat, s.gpr .x4, gkDom s, s.gpr .x0,
    s.gpr .x2, s.gpr .x7, privateValid (gkA s) (gkS s), s.sp⟩

theorem cr_of (s : State) (h : gkPre s) : CR (gkOf s) (gkRand s) s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Octets from their values. -/
theorem bytesAt_of {m : Mem} {ptr : Addr} {n : Nat} {l : List Byte} (hl : l.length = n)
    (h : ∀ i < n, m (ptr + BitVec.ofNat 64 i) = l.getD i 0) : Spec.Rsa.bytesAt m ptr n = l := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt, hl])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [h i (by simpa [Spec.Rsa.bytesAt] using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

/-- The postcondition, from the results. -/
theorem gk_post {p : GkP} {rb : List Byte} {s₀ u : State} (hc : CR p rb s₀) (hk : KX s₀ u) {r : Nat}
    (hr : r < 2 ^ 32) (h0 : u.gpr .x0 = BitVec.ofNat 64 r) {c : Bool} (hX : Xm p rb c u.mem) (hY : Ym p rb c u.mem)
    (hxl : (p.xo rb).length = p.k) (hyl : (p.yo rb).length = p.k)
    (hv : Spec.Ffdh.domainValid p.k p.dom = true → r = keyStatus p.a (p.s rb) ∧
      (c = true ↔ keyStatus p.a (p.s rb) = 1) ∧
      (c = true → p.xo rb = Spec.Rsa.i2osp (p.s rb) p.k ∧
        p.yo rb = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g (p.s rb) p.a.p) p.k)) :
    abiPreserved s₀ u ∧ gkContract.post s₀ u := by
  obtain ⟨-, -, -, -, hk', -, -, hdom, hxp, hyp, -, hrb, -⟩ := hc
  refine ⟨abiPreserved_of_keep hk, fun hd => ?_⟩
  show ((u.gpr .x0).setWidth 32).toNat = keyStatus (gkA s₀) (gkS s₀) ∧ _
  have ha : gkA s₀ = p.a := by simp only [gkA, GkP.a, hk', hdom]
  have hs : gkS s₀ = p.s rb := by simp only [gkS, ha, hrb, GkP.s]
  rw [ha, hs, hk', hxp, hyp]
  rw [hk', hdom] at hd
  obtain ⟨hr', hc', hb⟩ := hv hd
  refine ⟨by rw [h0, setWidth32_ofNat hr, hr'], ?_⟩
  by_cases h1 : keyStatus p.a (p.s rb) = 1
  · rw [ite_eq_left h1]
    have hct := hc'.mpr h1
    obtain ⟨ex, ey⟩ := hb hct
    refine ⟨?_, ?_⟩
    · rw [← ex]; exact bytesAt_of hxl fun i hi => by rw [hX i hi, hct]; rfl
    · rw [← ey]; exact bytesAt_of hyl fun i hi => by rw [hY i hi, hct]; rfl
  · rw [ite_eq_right h1]
    have hcf : c = false := by cases hcc : c <;> simp_all
    refine ⟨bytesAt_of (by simp) fun i hi => ?_, bytesAt_of (by simp) fun i hi => ?_⟩
    · rw [hX i hi, hcf]; simp [List.getD_eq_getElem?_getD, hi]
    · rw [hY i hi, hcf]; simp [List.getD_eq_getElem?_getD, hi]

/-- The key's flag is y's validity. -/
theorem F_iff {p : GkP} {rb : List Byte} {D : FD} {t : State} (hb : Base D t) (hm : D.mv = true) (hD : D.k = p.k)
    (hdom : D.dom = p.dom) (hdl : D.dl = p.dl) :
    p.F rb ↔ publicValid ⟨p.a, p.y rb⟩ = true := by
  have hodd : (p.D₁ rb).P % 2 = 1 := by
    have := (valid_facts hm hb.k1).1
    simp only [FD.P, hD, hdom] at this
    exact this
  have hl : p.dom.length = p.dl := by rw [← hdom, ← hdl]; exact hb.doml
  rw [publicValid_eq]
  have e1 : p.a.p = (p.D₁ rb).P := rfl
  have e2 : p.a.q = if p.dl = 3 * p.k then some (Spec.Rsa.os2ip (p.D₁ rb).qb) else none := by
    simp only [GkP.a, domainOf, hl]; rfl
  rw [e1, ← lt_pm1 hodd, e2]
  constructor
  · rintro ⟨hf, hq⟩
    refine ⟨hf, fun q hq' => ?_⟩
    by_cases h3 : p.dl = 3 * p.k
    · rw [ite_eq_left h3, Option.some.injEq] at hq'
      subst hq'
      exact hq h3
    · rw [ite_eq_right h3] at hq'; exact absurd hq' (by simp)
  · rintro ⟨hf, hq⟩
    exact ⟨hf, fun h3 => hq _ (by rw [ite_eq_left h3])⟩

/-- y is `g^x mod p` of the attempt's scalar. -/
theorem y_eq {p : GkP} {rb : List Byte} {t : State} (hb : Base (p.D₁ rb) t) (hm : (p.D₁ rb).mv = true)
    (ho : Ok p rb) : p.y rb = p.a.g ^ p.s rb % p.a.p := by
  rw [GkP.y, x_eq hb hm ho]; rfl

/-- The results' status. -/
theorem fin_status (F : Prop) [Decidable F] :
    ((BitVec.ofNat 64 3 - (bit F <<< 1)) = BitVec.ofNat 64 (if F then 1 else 3)) := by
  by_cases h : F <;> simp [bit, h] <;> decide

/-- The tail: with the scalar in range. -/
theorem tail_ok (W : Window) (M : Mont) (S : Selector) {p : GkP} {rb : List Byte} {s₀ t : State} (hc : CR p rb s₀)
    (hk : KX s₀ t) (hd : Dst p t) (h : T0 p rb t) :
    WP isa (seqs (GenerateKey.tail W.code S.code M.mm)) t fun u => abiPreserved s₀ u ∧ gkContract.post s₀ u := by
  have hb₁ := h.1.choose_spec.1
  have hm₁ := h.1.choose_spec.2.2.2.2.2
  have ho := h.2.1
  have hpv := h.2.2
  have hxl := xo_length p rb hb₁.bl_lt ho
  rw [tail_eq]
  refine wp_seqs_append (by simp [r2Steps]) (by simp) (dk hk hd (t0_t1 M p rb t h) fun t₁ h₁ k₁ hd₁ => ?_)
  refine wp_seqs_cons (by simp [GenerateKey.bound]) (dk k₁ hd₁ (t1_t2 p rb t₁ h₁) fun t₂ h₂ k₂ hd₂ => ?_)
  refine wp_seqs_append (by simp [GenerateKey.bound]) (by simp) (dk k₂ hd₂ (t2_t3 p rb t₂ h₂)
    fun t₃ h₃ k₃ hd₃ => ?_)
  refine wp_seqs_cons (by simp [pow]) (dk k₃ hd₃ (t3_t4 p rb t₃ h₃) fun t₄ h₄ k₄ hd₄ => ?_)
  refine wp_seqs_append (by simp [pow]) (by simp [range]) (dk k₄ hd₄ (t4_t5 W M S p rb t₄ h₄)
    fun t₅ h₅ k₅ hd₅ => ?_)
  refine wp_seqs_append (by simp [range]) (by simp) (dk k₅ hd₅ (t5_t6 p rb t₅ h₅) fun t₆ h₆ k₆ hd₆ => ?_)
  refine wp_seqs_cons (by simp) (dk k₆ hd₆ (t6_t7 p rb t₆ h₆) fun t₇ h₇ k₇ hd₇ => ?_)
  refine wp_seqs_cons (by simp) (dk k₇ hd₇ (t7_t8 p rb t₇ h₇ hd₇) fun t₈ h₈ k₈ hd₈ => ?_)
  have hb₂ := h₈.1.choose_spec.1.1
  have hm₂ := h₈.1.choose_spec.1.2.2.2.2.2
  obtain ⟨hyl, -, -⟩ := yo_facts hb₂ hm₂
  refine wp_seqs_cons (by simp) (dk k₈ hd₈ (t8_t9 p rb t₈ h₈) fun t₉ h₉ k₉ hd₉ => ?_)
  refine wp_seqs_cons (by simp) (dk k₉ hd₉ (t9_t10 p rb t₉ h₉) fun t₁₀ h₁₀ k₁₀ hd₁₀ => ?_)
  refine wp_seqs_cons (by simp) (WP.ite (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) (t10_eval h₁₀)
    (fun he => dk k₁₀ hd₁₀ (t10_t11n p rb t₁₀ h₁₀ (by rw [t10_eval h₁₀, he])) fun u hu ku hdu => ?_)
    (fun he => dk k₁₀ hd₁₀ (t10_t11q W M S p rb t₁₀ h₁₀ (by rw [t10_eval h₁₀, he])) fun u hu ku hdu => ?_))
  all_goals
    refine wp_seqs_cons (by simp) (dk ku hdu (t11_t12 p rb u hu) fun t₁₂ h₁₂ k₁₂ hd₁₂ => ?_)
    refine wp_seqs_cons (by simp) (dk k₁₂ hd₁₂ (t12_t13 p rb t₁₂ h₁₂ hd₁₂) fun t₁₃ h₁₃ k₁₃ hd₁₃ => ?_)
    refine wp_seqs_cons (by simp) (dk k₁₃ hd₁₃ (t13_t14 p rb t₁₃ h₁₃ hd₁₃) fun t₁₄ h₁₄ k₁₄ hd₁₄ => ?_)
    rw [seqs_one]
    obtain ⟨hz, hF, hX, hY, -, -⟩ := h₁₄
    refine WP.mono (fBlk_ok hz.x0 hF (hz.scr.ld (by have := hz.hZ; simp only [sF, sFn]; omega)))
      fun v ⟨⟨h0, hmv⟩, k⟩ => gk_post hc (keep_trans k₁₄ (k.mono (by decide))) (r := if p.F rb then 1 else 3)
        (by split <;> decide) (by rw [h0, fin_status]) (by rw [hmv]; exact hX) (by rw [hmv]; exact hY) hxl hyl ?_
    intro hdv
    have hpar : parametersValid p.a = true := by
      unfold domainValid at hdv; simp only [Bool.and_eq_true] at hdv; exact hdv.1
    have hpv' : privateValid p.a (p.s rb) = true := by rw [← ho.2.2]; exact hpv
    have hF' := F_iff (D := p.D₁ rb) (rb := rb) hb₁ hm₁ rfl rfl rfl
    have hy := y_eq hb₁ hm₁ ho
    have key : keyStatus p.a (p.s rb) = if p.F rb then 1 else 3 := by
      rw [KeyScalar.keyStatus_eq hpar, ite_eq_right (by rw [hpv']; decide), ← hy]
      by_cases hf : p.F rb
      · rw [ite_eq_left hf, ite_eq_left (hF'.mp hf)]
      · rw [ite_eq_right hf, ite_eq_right (fun h => hf (hF'.mpr h))]
    refine ⟨key.symm, ⟨fun h => by rw [key, ite_eq_left (of_decide_eq_true h)], fun h => ?_⟩, fun hf => ⟨?_, ?_⟩⟩
    · rw [key] at h
      by_cases hf : p.F rb
      · exact decide_eq_true hf
      · rw [ite_eq_right hf] at h; exact absurd h (by decide)
    · have := VG.Proof.Rsa.i2osp_os2ip (p.xo rb)
      rw [hxl, show Spec.Rsa.os2ip (p.xo rb) = p.s rb from x_eq hb₁ hm₁ ho] at this
      exact this.symm
    · rw [VG.Proof.Bignum.powMod_eq, ← hy]

/-- The scalar's bound. -/
theorem g6_g7 (p : GkP) (rb : List Byte) (t : State) (h : G6 p rb t) :
    WP isa (.ite (.zero .x .x3) (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY))) t fun u => G7 p rb u ∧ KX t u :=
  WP.ite (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) (g6_eval h) (fun hb => g6_g7n p rb t h (by rw [g6_eval h, hb]))
    (fun hb => g6_g7q p rb t h (by rw [g6_eval h, hb]))

/-- The postcondition after an invalid p. -/
theorem gk_post0 {p : GkP} {rb : List Byte} {s₀ u : State} (hc : CR p rb s₀) (hk : KX s₀ u)
    (hm : (p.D₀ rb).mv = false) : abiPreserved s₀ u ∧ gkContract.post s₀ u := by
  obtain ⟨-, -, -, -, hk', -, -, hdom, -⟩ := hc
  refine ⟨abiPreserved_of_keep hk, fun hd => ?_⟩
  rw [hk', hdom] at hd
  have := domainValid_mod hd
  exact absurd this (by show ¬ (p.D₀ rb).mv = true; rw [hm]; decide)

/-- `vg_ffdh_generate_key`. -/
theorem gk_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : gkContract.pre s) :
    ∃ t s', Exec isa (GenerateKey.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      gkContract.post s s' := by
  suffices hwp : WP isa (GenerateKey.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ gkContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  generalize gkOf s = p at hCR
  generalize gkRand s = rb at hCR
  have hok := cr_ok hCR
  have hb₀ := cr_base p rb s hCR
  unfold GenerateKey.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_g1 p rb s hCR) fun t₁ ⟨g1, k₁⟩ => ?_
  refine dk k₁ g1.2.1 (g1_gc p rb t₁ g1) fun t₂ gc k₂ hd₂ => ?_
  refine WP.ite (BitVec.ofNat 64 (p.D₀ rb).mv.toNat == 0) (ce_eval gc.1) (fun hb => ?_) (fun hb => ?_)
  · refine WP.mono (ret_ok t₂ (by decide)) fun u ⟨_, k⟩ => gk_post0 hCR (keep_trans k₂ (k.mono (by decide))) ?_
    cases hm : (p.D₀ rb).mv
    · rfl
    · rw [hm] at hb; exact absurd hb (by decide)
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval gc.1, hb]
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp) (dk k₂ hd₂ (gc_gi p rb t₂ gc he) fun t₃ h₃ k₃ hd₃ => ?_)
  refine wp_seqs_cons (by simp [GenerateKey.scalar]) (dk k₃ hd₃ (gi_gp p rb t₃ h₃) fun t₄ h₄ k₄ hd₄ => ?_)
  rw [scalar_eq, List.append_assoc]
  refine wp_seqs_append (by simp [GenerateKey.bound]) (by simp) (dk k₄ hd₄ (gp_gs p rb t₄ h₄)
    fun t₅ h₅ k₅ hd₅ => ?_)
  simp only [List.cons_append]
  refine wp_seqs_cons (by simp) (dk k₅ hd₅ (gs_gb p rb t₅ h₅) fun t₆ h₆ k₆ hd₆ => ?_)
  refine wp_seqs_cons (by simp) (dk k₆ hd₆ (gb_gx p rb t₆ h₆) fun t₇ h₇ k₇ hd₇ => ?_)
  refine wp_seqs_cons (by simp [Crt.loadArr]) (dk k₇ hd₇ (gx_g2 p rb t₇ h₇) fun t₈ h₈ k₈ hd₈ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange])
    (dk k₈ hd₈ (g2_g3 p rb t₈ h₈) fun t₉ h₉ k₉ hd₉ => ?_)
  rw [scalarRange_eq, List.append_assoc]
  refine wp_seqs_append (by simp [isNonzero, geArr, cmpArr]) (by simp) (dk k₉ hd₉ (g3_g4 p rb t₉ h₉)
    fun t₁₀ h₁₀ k₁₀ hd₁₀ => ?_)
  refine wp_seqs_cons (by simp) (dk k₁₀ hd₁₀ (g4_g5 p rb t₁₀ h₁₀) fun t₁₁ h₁₁ k₁₁ hd₁₁ => ?_)
  refine wp_seqs_cons (by simp) (dk k₁₁ hd₁₁ (g5_g6 p rb t₁₁ h₁₁) fun t₁₂ h₁₂ k₁₂ hd₁₂ => ?_)
  simp only [List.cons_append]
  refine wp_seqs_cons (by simp) (dk k₁₂ hd₁₂ (g6_g7 p rb t₁₂ h₁₂) fun t₁₃ h₁₃ k₁₃ hd₁₃ => ?_)
  refine wp_seqs_cons (by simp) (dk k₁₃ hd₁₃ (g7_g8 p rb t₁₃ h₁₃) fun t₁₄ h₁₄ k₁₄ hd₁₄ => ?_)
  simp only [List.append_eq, List.nil_append]
  rw [seqs_one]
  refine WP.ite (bit (p.pv = true) == 0) (g8_eval h₁₄) (fun hb => ?_) (fun hb => ?_)
  · -- The scalar out of range.
    have hpv : p.pv = false := by
      cases hp : p.pv
      · rfl
      · simp [bit, hp] at hb
    obtain ⟨⟨mi, hI, -⟩, ho⟩ := h₁₄
    have hb₁ := hI.1
    have hxl := xo_length p rb hb₁.bl_lt ho
    refine WP.seq (WP.mono (leave_ok hI.2.1) fun t₁₅ ⟨⟨h0, hm⟩, k₁₅⟩ => ?_)
    have hP := hI.pa hm k₁₅ h0
    refine WP.mono (fail_ok p rb (r := 2) (by decide) t₁₅ (Fz.of_pa (rb := rb) hP) (hd₁₄.keep k₁₅) ho)
      fun u ⟨⟨h0', hX, hY⟩, k⟩ => gk_post hCR (keep_trans k₁₄ (keep_trans (k₁₅.mono (by decide)) k)) (by decide)
        h0' hX hY hxl (by simp [GkP.yo, Spec.Rsa.i2osp]) fun hdv => ?_
    have hpar : parametersValid p.a = true := by
      unfold domainValid at hdv; simp only [Bool.and_eq_true] at hdv; exact hdv.1
    have hpv' : privateValid p.a (p.s rb) = false := by rw [← ho.2.2]; exact hpv
    rw [KeyScalar.keyStatus_eq hpar, ite_eq_left hpv']
    exact ⟨rfl, by simp, fun h => absurd h (by decide)⟩
  have he₁₄ : isa.eval (.zero .x .x9) t₁₄ = some false := by rw [g8_eval h₁₄, hb]
  exact tail_ok W M S hCR k₁₄ hd₁₄ (g8_t0 h₁₄ he₁₄)

end VG.Proof.Ffdh.AArch64.GenerateKey
