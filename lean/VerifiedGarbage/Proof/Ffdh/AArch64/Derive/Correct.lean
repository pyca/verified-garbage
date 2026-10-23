module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_ffdh_derive_public` on AArch64: correctness

From `dvContract`'s precondition, `DerivePublic.code` returns `keyStatus`
of the imported x and writes y, or zeros (`dv_correct`), by its stages: a
power of the checked generator is in its subgroup (`publicValid_power`), so
y's range is its validity.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Ffdh

/-- A step that keeps the caller's registers. -/
theorem kstep {s₀ t : State} {c : Prog isa} {P Q : State → Prop} (hk : KX s₀ t)
    (h : WP isa c t fun u => P u ∧ KX t u) (k : ∀ u, P u → KX s₀ u → Q u) : WP isa c t Q :=
  WP.mono h fun u ⟨hp, k'⟩ => k u hp (keep_trans hk k')

/-- The final block. -/
abbrev statusBlk : List Instr := [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]

theorem tail_eq (W : Window) (M : Mont) (S : Selector) :
    DerivePublic.tail W.code S.code M.mm = r2Steps M.mm ++ (pow W.code S.code M.mm sG sK sX sXl ++
      (OutMask.outMask ++ ([.block statusBlk] : List (Prog isa)))) := by
  simp only [DerivePublic.tail, List.append_assoc]
  rfl

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    DerivePublic.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++
      (Crt.loadArr aXm sX sXl ++ (CheckPrivate.scalarRange ++
        ([.ite (.zero .x .x9) DerivePublic.fail (seqs (DerivePublic.tail W.code S.code M.mm))] :
          List (Prog isa))))) := by
  simp only [DerivePublic.main, List.append_assoc]

/-- The public data of a state. -/
def dvOf (s : State) : DvP :=
  ⟨s.gpr .x7, (stackArg s 0).toNat * 8, (s.gpr .x4).toNat, (s.gpr .x3).toNat, s.gpr .x2, dvDom s, s.gpr .x0,
    s.gpr .x5, (s.gpr .x6).toNat, privateValid (dvA s) (Spec.Rsa.os2ip (dvX s)), s.sp⟩

theorem cr_of (s : State) (h : dvPre s) : CR (dvOf s) (dvX s) s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The postcondition, from the results. -/
theorem dv_post {p : DvP} {xb : List Byte} {s₀ u : State} (hc : CR p xb s₀) (hk : KX s₀ u) {r : Nat}
    (hr : r < 2 ^ 32) (h0 : u.gpr .x0 = BitVec.ofNat 64 r)
    (hv : domainValid p.k p.dom = true → r = keyStatus p.a (X xb) ∧
      if keyStatus p.a (X xb) = 1 then
        Spec.Rsa.bytesAt u.mem p.op p.k = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g (X xb) p.a.p) p.k
      else Spec.Rsa.bytesAt u.mem p.op p.k = List.replicate p.k 0) :
    abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  obtain ⟨-, -, -, -, hk', -, -, hdom, hop, -, -, hxb, -⟩ := hc
  refine ⟨abiPreserved_of_keep hk, fun hd => ?_⟩
  show ((u.gpr .x0).setWidth 32).toNat = keyStatus (dvA s₀) (Spec.Rsa.os2ip (dvX s₀)) ∧ _
  have ha : dvA s₀ = p.a := by simp only [dvA, DvP.a, hk', hdom]
  rw [ha, hxb, hop, hk']
  rw [hk', hdom] at hd
  obtain ⟨hr', hb⟩ := hv hd
  exact ⟨by rw [h0, setWidth32_ofNat hr, hr'], hb⟩

/-- The postcondition after an invalid p. -/
theorem dv_post0 {p : DvP} {xb : List Byte} {s₀ u : State} (hc : CR p xb s₀) (hk : KX s₀ u)
    (hm : (p.D xb).mv = false) : abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  obtain ⟨-, -, -, -, hk', -, -, hdom, -⟩ := hc
  refine ⟨abiPreserved_of_keep hk, fun hd => ?_⟩
  rw [hk', hdom] at hd
  have := domainValid_mod hd
  exact absurd this (by show ¬ (p.D xb).mv = true; rw [hm]; decide)

/-- x out of range: zeros to y, and 2 returned. -/
theorem fail_ok {p : DvP} {xb : List Byte} {s₀ t : State} (hc : CR p xb s₀) (hk : KX s₀ t) (h : V3 p xb t)
    (hpv : p.pv = false) :
    WP isa DerivePublic.fail t fun u => abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  have ho := h.2.2
  unfold DerivePublic.fail
  simp only [seqs]
  refine WP.seq (kstep hk (v3_o p xb t h) fun t₁ h₁ k₁ => ?_)
  refine WP.seq (kstep k₁ (o_z p t₁ h₁) fun t₂ h₂ k₂ => ?_)
  refine WP.mono (ret_ok t₂ (by decide)) fun u ⟨⟨h0, hm⟩, k⟩ =>
    dv_post hc (keep_trans k₂ (k.mono (by decide))) (r := 2) (by decide) h0 fun hdv => ?_
  have hpar : parametersValid p.a = true := by
    unfold domainValid at hdv; simp only [Bool.and_eq_true] at hdv; exact hdv.1
  have hpv' : privateValid p.a (X xb) = false := by rw [← ho.2.2.2]; exact hpv
  rw [KeyScalar.keyStatus_eq hpar, ite_eq_left hpv', hm]
  exact ⟨rfl, h₂.1⟩

/-- x in range: y and its status. -/
theorem tail_ok (W : Window) (M : Mont) (S : Selector) {p : DvP} {xb : List Byte} {s₀ t : State}
    (hc : CR p xb s₀) (hk : KX s₀ t) (h : T0 p xb t) :
    WP isa (seqs (DerivePublic.tail W.code S.code M.mm)) t fun u => abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  have hb₁ := h.1.choose_spec.1
  have hm₁ := h.1.choose_spec.2.2.2.2.2
  rw [tail_eq]
  refine wp_seqs_append (by simp [r2Steps]) (by simp) (kstep hk (t0_t1 M p xb t h) fun t₁ h₁ k₁ => ?_)
  refine wp_seqs_append (by simp [pow]) (by simp) (kstep k₁ (t1_t2 W M S p xb t₁ h₁) fun t₂ h₂ k₂ => ?_)
  refine wp_seqs_append (by simp [range]) (by simp) (kstep k₂ (t2_t3 p xb t₂ h₂) fun t₃ h₃ k₃ => ?_)
  rw [seqs_one]
  obtain ⟨⟨hy, h0, hF, hl⟩, ho, hpv⟩ := h₃
  refine WP.mono (fBlk_ok h0 hF hl) fun u ⟨⟨h0', hmu⟩, k⟩ =>
    dv_post hc (keep_trans k₃ (k.mono (by decide))) (r := if OutMask.fl (p.D xb) (yv p xb) then 1 else 3)
      (by split <;> decide) (by rw [h0', fin_status]) fun hdv => ?_
  have hpar : parametersValid p.a = true := by
    unfold domainValid at hdv; simp only [Bool.and_eq_true] at hdv; exact hdv.1
  have hpv' : privateValid p.a (X xb) = true := by rw [← ho.2.2.2]; exact hpv
  have hodd := (valid_facts hm₁ hb₁.k1).1
  have hpw := publicValid_power hpar (X xb)
  have ey : p.a.g ^ X xb % p.a.p = yv p xb := rfl
  rw [ey] at hpw
  have hfl : OutMask.fl (p.D xb) (yv p xb) ↔ publicValid ⟨p.a, yv p xb⟩ = true :=
    ⟨fun ⟨a, b⟩ => hpw.mpr ⟨a, (lt_pm1 hodd _).mp b⟩, fun e => ⟨(hpw.mp e).1, (lt_pm1 hodd _).mpr (hpw.mp e).2⟩⟩
  rw [KeyScalar.keyStatus_eq hpar, ite_eq_right (show ¬ privateValid p.a (X xb) = false by rw [hpv']; decide), ey, hmu,
    powMod_eq, ey]
  by_cases hf : OutMask.fl (p.D xb) (yv p xb)
  · rw [ite_eq_left hf] at hy
    rw [ite_eq_left hf, ite_eq_left (hfl.mp hf), ite_eq_left rfl]
    exact ⟨rfl, hy⟩
  · rw [ite_eq_right hf, i2osp_zero'] at hy
    rw [ite_eq_right hf, ite_eq_right (fun e => hf (hfl.mpr e)), ite_eq_right (by decide)]
    exact ⟨rfl, hy⟩

/-- `vg_ffdh_derive_public`. -/
theorem dv_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : dvContract.pre s) :
    ∃ t s', Exec isa (DerivePublic.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      dvContract.post s s' := by
  suffices hwp : WP isa (DerivePublic.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ dvContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  generalize dvOf s = p at hCR
  generalize dvX s = xb at hCR
  have hok := cr_ok hCR
  unfold DerivePublic.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_e1 p xb s hCR) fun t₁ ⟨⟨e1, _⟩, k₁⟩ => ?_
  refine kstep k₁ (e1_ce _ _ e1) fun t₂ ce k₂ => ?_
  refine WP.ite (BitVec.ofNat 64 (p.D xb).mv.toNat == 0) (ce_eval ce) (fun hb => ?_) (fun hb => ?_)
  · refine WP.mono (ret_ok t₂ (by decide)) fun u ⟨_, k⟩ => dv_post0 hCR (keep_trans k₂ (k.mono (by decide))) ?_
    cases hm : (p.D xb).mv
    · rfl
    · rw [hm] at hb; exact absurd hb (by decide)
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval ce, hb]
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (kstep k₂ (ce_in _ _ ce he) fun t₃ h₃ k₃ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange])
    (kstep k₃ (v1_v2 p xb t₃ ⟨h₃, OutMask.Dst.keep (cr_dst p xb s hCR) k₃, hok⟩) fun t₄ h₄ k₄ => ?_)
  refine wp_seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (kstep k₄ (v2_v3 p xb t₄ h₄)
    fun t₅ h₅ k₅ => ?_)
  rw [seqs_one]
  refine WP.ite (bit (p.pv = true) == 0) (v3_eval h₅) (fun hb => ?_) (fun hb => ?_)
  · have hpv : p.pv = false := by
      cases hp : p.pv
      · rfl
      · simp [bit, hp] at hb
    exact fail_ok hCR k₅ h₅ hpv
  exact tail_ok W M S hCR k₅ (v3_t0 h₅ (by rw [v3_eval h₅, hb]))

end VG.Proof.Ffdh.AArch64.Derive
