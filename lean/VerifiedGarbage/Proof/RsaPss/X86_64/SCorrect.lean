module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SCall
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.VFinal
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: correctness

The frame, the prologues, the checks, the encoding and the private-key
operation, for the hash functions the selectors name: the registers the ABI
keeps, and `Spec.RsaPss.sign`'s outcome written to `out` (`sign_body`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes oEm)
open VG.Impl.Mgf1.X86_64 (seqs)
open VG.Proof.RsaOaep.X86_64 (decStack stkD fb frR wp_alloc freed lenOf FnsD wp_good block_good keep_cs3
  off_plus outR Lay Rep)
open VG.Proof.MlKem.X86_64 (ifp ifn)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)
open VG.Proof.HashFns (StreamingOK)

variable {s : State}

/-- What the function's caller sees of the registers and the stack, from a
state in the frame. -/
theorem sEnd_abi (hp : SPre s) {s₂ : State} (he : SEnv s s₂) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧ abiPreserved s (freed frameBytes s₂) := by
  refine ⟨he.rsp, by rw [he.wr, hp.wr], fun r hr => ?_, ?_, he.mx⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show s₂.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else s₂.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      exact he.cs r hr hr'
  · have hsp2 := hp.sp2
    refine Frame.readW he.fr (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := Offset.disjoint_below (s.gpr .rsp) (n := decStack) (d := 0) (k := 8)
        (by unfold decStack VG.Proof.RsaPkcs1Enc.X86_64.privStack frameBytes at *; omega)
      simpa only [stkD, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · exact hp.dRO
    · exact hp.dRs

variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh)

include hTH hTG in
/-- After the checks: the encoding, its private-key operation, and its
outcome written to `out`. -/
theorem signMain_ok (v : PrivImpl) (hp : SPre s) (fH : FnsD s TH 18) (fG : FnsD s TG 19)
    (eH : Spec.HashId.mgf1 (sselH s) = some Hh) (eG : Spec.HashId.mgf1 (sselG s) = some Gh) {t : State}
    (he : SEnv s t) (L : Lay t (fb s) (stackArg s 14)) (R : Rep t.mem (fb s) (stackArg s 14) (sv0 s) (scW s))
    (hax : t.gpr .rax = BitVec.ofNat 64 (sk s - loV (sn0v s) - (lenOf (sselH s) + 2))) (hfit : SFit s) :
    WP isa (signMain v.name v.code) t fun t' => SEnv s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (privOutS s ((List.range (sk s)).map (RsaPss.emT (loV (sn0v s)) (sk s - loV (sn0v s) - Hh.len - 1) (ssl s)
          (Spec.Rsa.bytesAt s.mem (stackArg s 12) (ssl s))
          (Hh.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) Hh.len ++
            Spec.Rsa.bytesAt s.mem (stackArg s 12) (ssl s)))
          (Spec.Mgf1.mgf1 Gh (Hh.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (stackArg s 10) Hh.len ++
            Spec.Rsa.bytesAt s.mem (stackArg s 12) (ssl s))) (sk s - loV (sn0v s) - Hh.len - 1))
          ((maskV (sn0v s)).setWidth 8)))) := by
  unfold signMain seqs seqs
  refine WP.seq (WP.mono (signEnc_ok hTH hTG hp fH fG eH eG he L R hax hfit) fun t1 h1 => ?_)
  obtain ⟨he1, L1, V, W, R1, hW, hEM⟩ := h1
  simp only [sKs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hW
  obtain ⟨w14, w21, w22, w23, w24, w25, w26⟩ := hW
  obtain ⟨-, x21, x22, x23, x24, x25, x26, -⟩ := scW_w s
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (privArgsS_ok hp L1 he1.rd he1.fr R1
      (w21.trans x21) (w23.trans x23) (w22.trans x22) (w24.trans x24) (w25.trans x25) (w26.trans x26)))
    fun t2 ⟨⟨k2, L2, f2, ⟨W2, R2, hW2, _⟩, h1, h2, h3, h4, h5, h6⟩, sp2, mx2, fs2⟩ => ?_)
  have he2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 fs2
  have hlt : ∀ i < 14, i < VG.Proof.RsaOaep.X86_64.nW := fun i hi => by
    unfold VG.Proof.RsaOaep.X86_64.nW frameBytes; omega
  refine WP.mono (privS_call v hp ⟨he2, L2, fun i hi => (R2.fr i (hlt i hi)).trans (hW2 i hi), h1, h2, h3, h4, h5,
    h6⟩) fun t3 ⟨he3, hw3⟩ => ⟨he3, ?_⟩
  have hb : Spec.Rsa.bytesAt t2.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat =
      (List.range (s.gpr .rcx).toNat).map (fun i => V (oEm + i)) :=
    List.map_congr_left fun i hi => by
      have hi := List.mem_range.mp hi
      rw [off_plus, R2.scr _ (by have := hp.k2; unfold oEm VG.Impl.RsaOaep.X86_64.oRsa; omega)]
  rw [hb, List.map_congr_left fun i hi => hEM i (List.mem_range.mp hi)] at hw3
  exact hw3

include hTH hTG in
/-- For the hash functions `Hh` and `Gh` that the selectors name. -/
theorem sign_body (v : PrivImpl) (hp : SPre s) (fH : FnsD s TH 18) (fG : FnsD s TG 19)
    (eH : Spec.HashId.mgf1 (sselH s) = some Hh) (eG : Spec.HashId.mgf1 (sselG s) = some Gh) :
    WP isa (sign v.name v.code) s fun s' => abiPreserved s s' ∧ sPostH Hh Gh s s' := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDH : TH.S.digestBytes = lenOf (sselH s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTH eH
  have hHl : Hh.len = lenOf (sselH s) := hTH.len.trans hDH
  have hdl : (stackArg s 11).toNat = Hh.len := hp.dl Hh eH
  have hsl : (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat).length = ssl s := by
    simp [Spec.Rsa.bytesAt]
  obtain ⟨k', hk'⟩ : ∃ k', (s.gpr .rcx).toNat = k' + 1 := ⟨(s.gpr .rcx).toNat - 1, by omega⟩
  have hnB := bytesAt_cons s.mem (s.gpr .rdx) k'
  rw [← hk'] at hnB
  have hlen : ((List.range k').map fun i => s.mem (s.gpr .rdx + BitVec.ofNat 64 (i + 1))).length = k' := by simp
  refine wp_alloc (by
    have := hp.sp1; unfold decStack VG.Proof.RsaPkcs1Enc.X86_64.privStack at this; unfold frameBytes at *; omega) ?_
  refine signBody_ok v.name v.code hp (fun t he hax hz hb => ?_) fun t he L R hax hfit => ?_
  · obtain ⟨h1, h2, h3⟩ := sEnd_abi hp he
    refine ⟨h1, h2, h3, ?_⟩
    show Spec.Rsa.writtenOutcome t.mem _ _ ((t.gpr .rax).setWidth 32) _
    rw [hnB]
    by_cases h0 : s.mem (s.gpr .rdx) = 0
    · rw [h0, Any.sign_zero]
      exact ⟨by rw [hax]; rfl, hz⟩
    · rw [Any.sign_long]
      · exact ⟨by rw [hax]; rfl, hz⟩
      have hn0 : sn0v s ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      rw [VG.Proof.RsaPss.emLength_eq _ h0, hlen, hsl]
      have hb' : ¬ lenOf (sselH s) + 2 + ssl s ≤ (s.gpr .rcx).toNat - loV (sn0v s) := fun h => hb ⟨hn0, h⟩
      unfold loV sn0v at hb'
      rw [hHl]
      by_cases h1 : (s.mem (s.gpr .rdx)).toNat = 1
      · rw [ifp h1] at hb' ⊢; omega
      · rw [ifn h1] at hb' ⊢; omega
  · refine WP.mono (signMain_ok hTH hTG v hp fH fG eH eG he L R hax hfit) fun t' ⟨he', hw⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := sEnd_abi hp he'
    refine ⟨h1, h2, h3, ?_⟩
    show Spec.Rsa.writtenOutcome t'.mem _ _ ((t'.gpr .rax).setWidth 32) _
    obtain ⟨hn0, hfit⟩ := hfit
    have h0 : s.mem (s.gpr .rdx) ≠ 0 := fun h => hn0 (by unfold sn0v; rw [h]; rfl)
    have hlo := loV_le (sn0v s)
    have hE : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .rdx) ::
        (List.range k').map fun i => s.mem (s.gpr .rdx + BitVec.ofNat 64 (i + 1)))) - 1) = sk s - loV (sn0v s) := by
      rw [VG.Proof.RsaPss.emLength_eq _ h0, hlen]
      unfold sk loV sn0v
      by_cases h1 : (s.mem (s.gpr .rdx)).toNat = 1
      · rw [ifp h1, ifp h1]; omega
      · rw [ifn h1, ifn h1]; omega
    rw [hnB, hdl, Any.sign_eq Hh Gh hTH.valid hTG.valid h0 (by simp [Spec.Rsa.bytesAt]) rfl hE
      (lo := loV (sn0v s)) (db := sk s - loV (sn0v s) - Hh.len - 1)
      (by simp only [List.length_cons, hlen]; unfold sk at hE ⊢; omega) rfl (by rw [hsl, hHl]; omega)]
    have hc := VG.Proof.RsaPss.X86_64.maskV_eq ((List.range k').map fun i => s.mem (s.gpr .rdx + BitVec.ofNat 64 (i + 1))) h0
    rw [hE] at hc
    rw [← hc, hsl, List.length_cons, hlen, ← hk', ← hnB]
    exact hw

end VG.Proof.RsaPss.X86_64
