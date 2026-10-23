module

public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH public-value derivation on x86-64: correctness and ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base)
open VG.Spec.Ffdh

theorem dvStatus_eq {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s)
    (hm : p.mv = true) (ha : parametersValid p.params = true) :
    dvStatus p xb = keyStatus p.params (Spec.Rsa.os2ip xb) := by
  cases hsv : p.sv with
  | false =>
    have hx : privateValid p.params (Spec.Rsa.os2ip xb) = false := h.valid.trans hsv
    have hr := (VG.Proof.Ffdh.keyStatus_scalar p.params (Spec.Rsa.os2ip xb)).mpr hx
    simpa only [dvStatus, hsv, Bool.false_eq_true, ↓reduceIte] using hr.symm
  | true =>
    have hx : privateValid p.params (Spec.Rsa.os2ip xb) = true := h.valid.trans hsv
    rw [VG.Proof.Ffdh.keyStatus_power ha _ hx]
    simp only [dvStatus, hsv, ↓reduceIte]
    congr 1
    apply propext
    change (1 < p.z xb ∧ 2 * (p.z xb / 2) + 1 < p.P) ↔ _
    rw [lt_pm1 (valid_facts hm h.k1).1]
    rfl

theorem dvStatus_lt (p : KpP) (xb : List Byte) : dvStatus p xb < 2 ^ 32 := by
  unfold dvStatus
  split
  · split <;> decide
  · decide

theorem main_spec {p : KpP} {xb : List Byte} {s u t : State} (hb : Base p xb u)
    (hm : p.mv = true) (ha : parametersValid p.params = true) (h : MainPost p xb s t) :
    ((t.gpr .rax).setWidth 32).toNat = keyStatus p.params (Spec.Rsa.os2ip xb) ∧
      if keyStatus p.params (Spec.Rsa.os2ip xb) = 1 then
        Spec.Rsa.bytesAt t.mem p.yp p.k =
          Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (Spec.Rsa.os2ip xb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hy, _⟩ := h
  have hst := dvStatus_eq hb hm ha
  have hlt := dvStatus_lt p xb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : dvStatus p xb = 1
    · simp only [ite_eq_left hs] at hy ⊢
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hy ⊢
      rw [hy, i2osp_zero']

theorem body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (hpre : dvPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => dvPost s t ∧ t.gpr .rdi = (dvOf s).B ∧ DvFrame (dvOf s) s.mem t.mem ∧
        (∀ i < 6, word t.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have c := dvCtx_of hpre
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body
  refine WP.seq (WP.mono (entry_pre0 c) fun u ⟨h0, hd, hi, hs, k⟩ => ?_)
  refine WP.seq (WP.mono (zero_base h0 hd) fun u' ⟨hb, hy, hd', hf', hs', k'⟩ => ?_)
  refine WP.seq (WP.mono (CheckPrivate.dom_base hb hd') fun v ⟨hb', hz, hd'', hG, hQ, hi'', hs'', k''⟩ => ?_)
  have H : DvFrame (dvOf s) s.mem v.mem :=
    ((DvFrame.of_scr hi).trans (DvFrame.of_y hf')).trans (DvFrame.of_scr hi'')
  have K := keep_trans (keep_trans k k') k''
  have hS : ∀ i < 6, word v.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs'' i hi).trans ((hs' i hi).trans (hs i hi))
  have hyv : YOut (dvOf s) v := hy.of_wr k''.2.2
  refine WP.ite (!(dvOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun hf => ?_)
  · have hm : (dvOf s).mv = false := by simpa only [Bool.not_eq_true'] using hf
    refine WP.mono (ret_ok v (r := 0) (by decide)) fun t ⟨_, hmem, kk⟩ =>
      ⟨?_, (kk.gpr (by decide)).trans hd'', fun a ha hn => by rw [hmem]; exact H a ha hn,
        (fun i hi => by rw [hmem]; exact hS i hi), keep_trans K (kk.mono (by decide))⟩
    intro hv
    have hm' := domainValid_mod hv
    change (dvOf s).mv = true at hm'
    rw [hm] at hm'
    contradiction
  · have hm : (dvOf s).mv = true := by simpa only [Bool.not_eq_false'] using hf
    refine WP.mono (main_ok M E R hb' hyv rfl hd'' hG hQ hm) fun t hh => ?_
    have hmain := hh
    obtain ⟨_, hdt, _, hsave, hframe, kk⟩ := hh
    refine ⟨?_, hdt, H.trans hframe, (fun i hi => (hsave i hi).trans (hS i hi)), keep_trans K kk⟩
    intro hv
    have hp : parametersValid (dvOf s).params = true := by
      unfold domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    exact main_spec hb' hm hp hmain

theorem dv_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : dvContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ dvContract.post s t := by
  have hpre := h
  have c := dvCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRetY, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ dvContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code
  refine WP.seq (WP.mono (body_ok M E R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    refine hf _ (out_scr hRetScr hbyte) ?_
    intro j hj he
    exact hRetY _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.yl]; exact hj) (by have := c.k2; omega))
  · change dvPost s t
    unfold dvPost
    rw [kk.gpr (show .rax ∉ saved by decide), hm]
    exact hp

end VG.Proof.Ffdh.X86_64.DerivePublic
