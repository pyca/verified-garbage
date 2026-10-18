module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SFrame
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the checks

`n₀` (`sn0_step`), `emLen` (`sem_step`) and the salt's room (`sfit_step`),
each failing with zeros to `out` and 0 (`sfail_ok`); `signBody_ok` runs the
frame, the prologues and the checks, then `signMain` if they pass.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sOut sN sK sE sEl oRsa argSlot arg selPrologueWith zeroOut)
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Proof.RsaOaep.X86_64 (decStack stkD fb frR frame_subD ret_subD Lay Rep upd ea_sp selW fnW lenOf
  StepW cs_disj outR wp_good block_good keep_cs3 zeroOut_good zeroOut_ok)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {s : State}

/-- `V₀`: the working space's bytes on entry. -/
abbrev sv0 (s : State) : Nat → Byte := fun o => s.mem (off (stackArg s 14) o)

/-- `n₀`, `k` and the salt's length. -/
abbrev sn0v (s : State) : Nat := (s.mem (s.gpr .rdx)).toNat
abbrev sk (s : State) : Nat := (s.gpr .rcx).toNat
abbrev ssl (s : State) : Nat := (stackArg s 13).toNat

theorem signW_21 : signW s 21 = s.gpr .rdi := by simp [signW, fnW, selW, signPW, upd]
theorem signW_22 : signW s 22 = s.gpr .rdx := by simp [signW, fnW, selW, signPW, upd]
theorem signW_23 : signW s 23 = s.gpr .rcx := by simp [signW, fnW, selW, signPW, upd]
theorem signW_39 : signW s 39 = BitVec.ofNat 64 (lenOf (sselH s)) := by simp [signW, fnW, selW, upd]

/-- The slots after the checks: the mask (30) and `lo` (31). -/
def scW (s : State) : Nat → BitVec 64 :=
  upd (upd (signW s) 30 (maskV (sn0v s))) 31 (BitVec.ofNat 64 (loV (sn0v s)))

/-- Zeros to `out` and 0, from a state in the frame. -/
theorem sfail_ok (hp : SPre s) {t : State} (he : SEnv s t) (L : Lay t (fb s) (stackArg s 14)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 14) V W) (w21 : W 21 = s.gpr .rdi)
    (w23 : W 23 = s.gpr .rcx) :
    WP isa signFail t fun t' => SEnv s t' ∧ t'.gpr .rax = 0 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hsi := hp.hsi
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) = outR s := by simp [outR, hsi]
  refine WP.mono (wp_good zeroOut_good (zeroOut_ok L R w21 (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega) hk2 (by rw [hout, he.wr]; simp) (by rw [← hsi]; exact hp.wO)
    ⟨by rw [hout]; exact (hp.dKO.sub_left (frame_subD s)),
      by rw [hout]; exact (hp.dOs.symm.sub_left (Region.sub_prefix (by unfold oRsa; have := hp.hsl; omega))),
      by rw [hout]; exact hp.dKO.sub_left (ret_subD s)⟩))
    fun t' ⟨⟨L', k', R', hax, hz, _⟩, sp', mx', f'⟩ => ⟨he.step k'.2.1 k'.2.2 sp' (keep_cs3 k' (by decide)) mx' f',
      hax, hz⟩

/-- After `n0`. -/
def SN (s t : State) : Prop :=
  SEnv s t ∧ Lay t (fb s) (stackArg s 14) ∧ Rep t.mem (fb s) (stackArg s 14) (sv0 s) (signW s) ∧
    t.gpr .rax = BitVec.ofNat 64 (sn0v s) ∧ t.zf = some (decide (sn0v s = 0))

theorem sn0_step (hp : SPre s) {t : State} (h : JPS signW s t) : WP isa (.block n0) t (SN s) := by
  have hk1 := hp.k1
  have he2 := h.env hp
  obtain ⟨-, L2, R2, f12, -⟩ := h
  have hc : (snR s).Contains (s.gpr .rdx) 1 := by
    have h := Offset.contains_base (s.gpr .rdx) (d := 0) (n := 1) (k := (s.gpr .rcx).toNat) (by omega) (by decide)
    rwa [BitVec.add_zero] at h
  have hn0 : t.mem (s.gpr .rdx) = s.mem (s.gpr .rdx) := f12 _ fun r hr hc' => by
    rw [List.mem_singleton.mp hr] at hc'
    exact (hp.dKn.sub_left (frame_subD s)) _ hc' hc
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdx) 1 := by
    rw [he2.rd, hp.hrd]
    exact ⟨snR s, List.mem_append_left _ (by simp [srd]), hc⟩
  refine WP.mono (wp_good (block_good _ rfl rfl) (n0_ok L2 R2 signW_22 hin))
    fun t3 ⟨⟨k3, hm3, hax3, hz3⟩, sp3, mx3, f3⟩ => ?_
  rw [hn0] at hax3 hz3
  exact ⟨he2.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3,
    L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), hm3 ▸ R2, hax3, hz3⟩

/-- After `emLen`: `rax = emLen`, CF set if it is less than `hLen + 2`. -/
def SE (s t : State) : Prop :=
  SEnv s t ∧ Lay t (fb s) (stackArg s 14) ∧ Rep t.mem (fb s) (stackArg s 14) (sv0 s) (scW s) ∧
    t.gpr .rax = BitVec.ofNat 64 (sk s - loV (sn0v s)) ∧
    t.cf = some (decide (sk s - loV (sn0v s) < lenOf (sselH s) + 2)) ∧ sn0v s ≠ 0

theorem sem_step (hp : SPre s) {t : State} (h : SN s t) (hn0 : sn0v s ≠ 0) :
    WP isa (.seq (.block smear) emLen) t (SE s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD64 : lenOf (sselH s) ≤ 64 := pssLensOK.le _ (mem_pssLens hp.iH)
  obtain ⟨he3, L3, R3, hax3, -⟩ := h
  have hx256 : sn0v s < 256 := (s.mem (s.gpr .rdx)).isLt
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (smear_ok t hx256 hn0 hax3))
    fun t4 ⟨⟨k4, hm4, hdx4, hz4⟩, sp4, mx4, f4⟩ => ?_)
  have he4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  have L4 : Lay t4 (fb s) (stackArg s 14) := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  refine WP.mono (wp_good emLen_good (emLen_ok L4 (hm4 ▸ R3) (k := (s.gpr .rcx).toNat) (by rw [signW_23,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]) signW_39 hD64 (by omega) (by omega) hdx4 hz4))
    fun t5 ⟨⟨L5, k5, R5, hax5, hcf5⟩, sp5, mx5, f5⟩ =>
      ⟨he4.step k5.2.1 k5.2.2 sp5 (keep_cs3 k5 (by decide)) mx5 f5, L5, R5, hax5, hcf5, hn0⟩

/-- After the salt's check. -/
def SF (s t : State) : Prop :=
  SEnv s t ∧ Lay t (fb s) (stackArg s 14) ∧ Rep t.mem (fb s) (stackArg s 14) (sv0 s) (scW s) ∧
    t.gpr .rax = BitVec.ofNat 64 (sk s - loV (sn0v s) - (lenOf (sselH s) + 2)) ∧
    t.cf = some (decide (sk s - loV (sn0v s) - (lenOf (sselH s) + 2) < ssl s)) ∧ sn0v s ≠ 0 ∧
    lenOf (sselH s) + 2 ≤ sk s - loV (sn0v s)

theorem scW_eq {k : Nat} (h1 : k ≠ 30) (h2 : k ≠ 31) : scW s k = signW s k := by
  simp only [scW, upd, ifn h1, ifn h2]

theorem sfit_step (hp : SPre s) {t : State} (h : SE s t) (hfit : lenOf (sselH s) + 2 ≤ sk s - loV (sn0v s)) :
    WP isa (.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFits)) t (SF s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlo := loV_le (sn0v s)
  obtain ⟨he6, L6, R6, hax6, -, hn0⟩ := h
  have w29 : scW s 29 = stackArg s 13 := by rw [scW_eq (by decide) (by decide)]; simp [signW, fnW, selW, signPW, upd]
  have w39 : scW s 39 = BitVec.ofNat 64 (lenOf (sselH s)) := (scW_eq (by decide) (by decide)).trans signW_39
  rw [WP.block_append_iff]
  refine WP.mono (wp_good (block_good _ rfl rfl) (WP.keep [.rdx] (Q := fun v => v.mem = t.mem ∧
      v.gpr .rdx = stackArg s 13) ?_ rfl))
    fun t7 ⟨⟨⟨hm7, hdx7⟩, k7⟩, sp7, mx7, f7⟩ => ?_
  · xrun [ea_sp, L6.rsp, L6.ld (d := sSaltLen) (by decide), R6.rd (d := sSaltLen) 29 rfl (by decide), w29]
  have he7 := he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7
  have L7 : Lay t7 (fb s) (stackArg s 14) := L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7])
  have R7 := hm7 ▸ R6
  refine WP.mono (wp_good (block_good _ rfl rfl) (saltFits_ok L7 R7 w39 (a := (s.gpr .rcx).toNat - loV (sn0v s))
      (by unfold sk at hfit; omega) (by omega) ((k7.gpr (by decide)).trans hax6) hdx7))
    fun t8 ⟨⟨k8, hm8, hax8, hcf8⟩, sp8, mx8, f8⟩ => ?_
  exact ⟨he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8,
    L7.congr (k8.gpr (by decide)) k8.2.2 (by rw [hm8]), hm8 ▸ R7, hax8, hcf8, hn0, hfit⟩

/-- The checks passed. -/
def SFit (s : State) : Prop := sn0v s ≠ 0 ∧ lenOf (sselH s) + 2 + ssl s ≤ sk s - loV (sn0v s)

variable (privN : String) (privC : Prog isa)

/-- The frame, the prologues and the checks, then `signMain` if they pass. -/
theorem signBody_ok (hp : SPre s) {Q : State → Prop}
    (hfail : ∀ t, SEnv s t → t.gpr .rax = 0 →
      Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 →
      ¬ SFit s → Q t)
    (hmain : ∀ t, SEnv s t → Lay t (fb s) (stackArg s 14) → Rep t.mem (fb s) (stackArg s 14) (sv0 s) (scW s) →
      t.gpr .rax = BitVec.ofNat 64 (sk s - loV (sn0v s) - (lenOf (sselH s) + 2)) → SFit s →
      WP isa (signMain privN privC) t Q) :
    WP isa (signBody privN privC) (allocState frameBytes s) Q := by
  unfold signBody seqs seqs seqs
  refine WP.seq (WP.mono (spro_step hp) fun t1 h1 => ?_)
  refine WP.seq (WP.mono (ssel_step hp h1) fun t2 h2 => ?_)
  refine WP.seq (WP.mono (sn0_step hp h2) fun t3 h3 => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .e t3 = _ from h3.2.2.2.2) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    obtain ⟨he3, L3, R3, -⟩ := h3
    exact WP.mono (sfail_ok hp he3 L3 R3 signW_21 signW_23) fun t' ⟨he', hax, hz⟩ =>
      hfail t' he' hax hz fun h => h.1 hb
  rw [decide_eq_false_iff_not] at hb
  unfold seqs seqs
  refine VG.Proof.RsaOaep.X86_64.WP.seq_assoc (WP.seq (WP.mono (sem_step hp h3 hb) fun t5 h5 => ?_))
  have w21 : scW s 21 = s.gpr .rdi := (scW_eq (by decide) (by decide)).trans signW_21
  have w23 : scW s 23 = s.gpr .rcx := (scW_eq (by decide) (by decide)).trans signW_23
  refine WP.ite (M := isa) _ (show isa.eval .b t5 = _ from h5.2.2.2.2.1) (fun hb' => ?_) (fun hb' => ?_)
  · rw [decide_eq_true_eq] at hb'
    obtain ⟨he5, L5, R5, -⟩ := h5
    exact WP.mono (sfail_ok hp he5 L5 R5 w21 w23) fun t' ⟨he', hax, hz⟩ =>
      hfail t' he' hax hz fun h => by unfold SFit sk at h; unfold sk at hb'; omega
  rw [decide_eq_false_iff_not] at hb'
  unfold seqs
  refine WP.seq (WP.mono (sfit_step hp h5 (by omega)) fun t8 h8 => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .b t8 = _ from h8.2.2.2.2.1) (fun hb'' => ?_) (fun hb'' => ?_)
  · rw [decide_eq_true_eq] at hb''
    obtain ⟨he8, L8, R8, -⟩ := h8
    exact WP.mono (sfail_ok hp he8 L8 R8 w21 w23) fun t' ⟨he', hax, hz⟩ =>
      hfail t' he' hax hz fun h => by unfold SFit sk at h; unfold sk at hb''; omega
  rw [decide_eq_false_iff_not] at hb''
  obtain ⟨he8, L8, R8, hax8, -, hn0, hfit⟩ := h8
  exact hmain t8 he8 L8 R8 hax8 ⟨hn0, by omega⟩

end VG.Proof.RsaPss.X86_64
