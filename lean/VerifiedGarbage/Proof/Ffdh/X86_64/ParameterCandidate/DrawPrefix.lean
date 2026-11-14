module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead

/-! ### `Ffdh.X86_64.ParameterCandidate.LoadWitness`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: load a masked witness into Xm -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem loadWitness_ok {p : WitnessParams} {s : State}
    (h : ModulusReady s p.I p.IZ p.w p.mi p.N)
    (ho : OutOk s p.I p.IZ p.op p.len)
    (hsi : s.gpr .rsi = p.op) (hcx : s.gpr .rcx = BitVec.ofNat 64 p.len)
    (hv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.len) < 2 ^ (64 * p.w)) :
    WP isa (loadNumber aXm) s fun t =>
      ModulusReady t p.I p.IZ p.w p.mi p.N ∧
      wv t.mem p.I (slot p.w aXm) p.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.len) ∧
      Frm p.I [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  let bs := Spec.Rsa.bytesAt s.mem p.op p.len
  have hlen : bs.length = p.len := bytesAt_length _ _ _
  have hw : p.w = (bs.length + 7) / 8 := by rw [hlen]; exact p.width
  have hb := p.width_bounds
  have hcx' : s.gpr .rcx = BitVec.ofNat 64 bs.length := by rw [hlen]; exact hcx
  refine WP.mono (loadNumber_ok (by decide : aXm < 8) h.good p.dims.z hsi hcx'
    (by omega_using [hlen, hb.2.2.1]) (by omega_using [hlen, hb.2.2.2.1])
    (by omega_using [hw]) (by omega_using [hw]) hv
    (fun i hi => by
      obtain ⟨r, hr, hc⟩ := ho.wr i (by omega_using [hlen, hi])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun i hi => bytesAt_read _ _ (by omega_using [hlen, hi] : i < p.len))
    (fun i hi => Or.inr (by
      have hs := ho.sep i (by omega_using [hlen, hi])
      change p.IZ ≤ ofs p.I (off p.op i) at hs
      have hf := slot_le (w := p.w) (show aXm < 8 by decide)
      omega_using [hs, hf, hw, p.dims.z]))) fun t ⟨hv', hg, hf, k⟩ => ?_
  have hf' : Frm p.I [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem :=
    Frm.of_outside (hf.mono (o' := slot p.w aXm) (n' := 8 * (p.w + 2)) (Nat.le_refl _) (by omega_using [hw])) (by simp)
  refine ⟨h.of_frm p.dims hf' k hg.rdi (by rng_disj) (by rng_disj) (by rng_disj), hv', hf',
    k.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: consume, mask and load one draw -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem drawPrefix_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (havail : p.len ≤ bs.length) :
    WP isa drawPrefix s fun t =>
      DrawState p (off rp p.len) (used + p.len) (bs.drop p.len) t ∧
      wv t.mem p.I (slot p.w aXm) p.w = Spec.Rsa.os2ip (bs.take p.len) % 2 ^ p.bits ∧
      (∀ j < 32, word t.mem p.O (8 * j) =
        word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j)) ∧
      DrawFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  have hl64 : p.len < 2 ^ 64 := by omega_using [p.width_bounds.2.2.2.1]
  unfold drawPrefix cutLoad
  refine WP.seq (WP.mono (drawSetup_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
    h.link h.outPtr h.ptr h.left h.usedWord h.len h.bits hl64 havail)
    fun u ⟨hm, hsi, hdi, hbp, hcx, hdx, k⟩ => ?_)
  have hmem : u.mem = advanceMem s.mem p.O rp p.len bs.length used := hm
  have hfa : Frm p.O [(8 * oRandPtr, 24)] s.mem u.mem := by rw [hmem]; exact advanceMem_frame _ _ _ _ _ _
  have hfai : InScr p.O p.Z s.mem u.mem :=
    InScr.of_frm hfa (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      change 120 ≤ p.Z
      omega_using [p.space_bounds.1])
  have hwI : ∀ d, d + 8 ≤ p.IZ → word u.mem p.I d = word s.mem p.I d :=
    outer_words hfa (by simp [oRandPtr]) (by omega_using [p.space_bounds.2.2, hz64])
  have hstatic : ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 → word u.mem p.O (8 * j) = word s.mem p.O (8 * j) := by
    intro j hj h12 h13 h14
    apply hfa.word_eq
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      change 8 * j + 8 ≤ 96 ∨ 120 ≤ 8 * j
      omega_using [h12, h13, h14]
    · omega_using [hj]
  have hsrc := source_take (h.rand.congrK hfai k) p.len
  have ho : OutOk u p.O p.Z p.op p.len :=
    ⟨fun i hi => by rw [k.2.2]; exact h.out.wr i hi, h.out.sep⟩
  refine WP.seq (WP.mono (cutRestore_ok h.ready k.2.2 hwI (h.scr.congr k.2.2)
    ((hwI _ p.space_bounds.2.1).trans h.link)
    ((hstatic _ (by decide) (by decide) (by decide) (by decide)).trans h.outPtr)
    ((hstatic _ (by decide) (by decide) (by decide) (by decide)).trans h.len)
    hdi hsi hbp hcx hdx hsrc ho
    (fun i hi j hj => h.apart i hi j (by rw [List.length_take] at hj; omega_using [hj]))
    (by rw [List.length_take, Nat.min_eq_left havail]))
    fun v ⟨hrv, hsiv, hcxv, hv, hwO, hwIv, hfv, kv⟩ => ?_)
  have hkov := k.trans kv
  have hov : OutOk v p.O p.Z p.op p.len :=
    ⟨fun i hi => by rw [hkov.2.2]; exact h.out.wr i hi, h.out.sep⟩
  have hval : Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem p.op p.len) < 2 ^ (64 * p.w) := by
    rw [hv]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) p.width_bounds.2.2.2.2)
  refine WP.mono (loadWitness_ok hrv (output_inner hov hz64) hsiv hcxv hval)
    fun t ⟨hrt, hxm, hft, kt⟩ => ?_
  have hfit : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))], r.1 + r.2 ≤ p.IZ := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact Nat.le_trans (slot_le (w := p.w) (show aXm < 8 by decide)) p.dims.z
  have hh : ∀ j < 32, word t.mem p.O (8 * j) =
      word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j) := by
    intro j hj
    rw [inner_header hft hfit hz64 j hj, hwO _ (by omega_using [hj, p.space_bounds.1]), hmem]
  have hl : word t.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O := by
    rw [inner_link hft (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      unfold slot VG.Impl.Bignum.hdrBytes aXm
      omega_using []), hwIv (8 * VG.Impl.Rsa.X86_64.Crt.sLink) p.space_bounds.2.1,
      hwI (8 * VG.Impl.Rsa.X86_64.Crt.sLink) p.space_bounds.2.1]
    exact h.link
  have hf : DrawFrame p s.mem t.mem :=
    ((DrawFrame.of_scr hfai).trans hfv).trans (DrawFrame.of_inner hft hfit hz64)
  have kk : Keep (.rdi :: mmRegs) s t := ((k.trans kv).trans kt).mono (by decide)
  have kk' : Keep mmRegs s t := keep_modulus kk (hrt.good.rdi.trans h.ready.good.rdi.symm)
  refine ⟨h.after_sample havail hrt hl (fun j hj _ => hh j hj) hf kk', ?_, hh, hf, kk'⟩
  rw [hxm, hv]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
