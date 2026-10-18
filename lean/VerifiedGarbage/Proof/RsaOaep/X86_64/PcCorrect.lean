module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: correctness

`EM` built and masked (`encMask_ok`), then the call with `pre`
(`encMain_ok`), after the prologues and the checks (`encBodyWith_ok`), for
the hash functions the selectors name, whose streaming functions the tables
hold: memory safety and the registers the ABI keeps whatever `pre` holds,
and, if `pre` holds the values for `n`, `encK`'s postcondition for those
hash functions (`code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.HashFns (StreamingOK)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- `encK`'s postcondition for the hash functions the selectors name, if
`pre` holds the values for `n`. -/
def post (s u : State) : Prop :=
  Consistent s → ∀ H G, Spec.HashId.mgf1 (selH s) = some H → Spec.HashId.mgf1 (selG s) = some G →
    (encK H G).post s u

/-- What the function's caller sees of the registers and the stack, from a
state in the frame. -/
theorem encEnd_abi {H : Spec.Mgf1.Hash} {s s₂ : State} (hp : EPre H s) (he : EnvE s s₂) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧ abiPreserved s (freed frameBytes s₂) := by
  refine ⟨he.rsp, by rw [he.wr, EPre.wr hp], fun r hr => ?_, ?_, he.mx⟩
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
    · have := Offset.disjoint_below (s.gpr .rsp) (n := encStack) (d := 0) (k := 8) (by unfold encStack; omega)
      simpa only [stkR, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · exact hp.d_ret_out
    · exact hp.d_ret_scr

variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh)

include hTH hTG in
theorem encMain_ok (v : PublicImpl) {s t : State} (fH : FnsOf s TH 12) (fG : FnsOf s TG 13)
    (eH : Spec.HashId.mgf1 (selH s) = some Hh) (eG : Spec.HashId.mgf1 (selG s) = some Gh)
    (hp : PPre Hh s) (he : EnvE s t)
    (L : Lay t (fb s) (stackArg s 6)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem (fb s) (stackArg s 6) V W) (hW : ArgsW s W)
    (hk : 2 * TH.S.digestBytes + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    WP isa (Impl.RsaOaep.X86_64.Precomputed.encMain v.name v.code) t fun t' => EnvE s t' ∧
      (Consistent s → Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (emOf Gh TH.S.digestBytes (s.gpr .rcx).toNat (stackArg s 3).toNat
            (Spec.Rsa.bytesAt s.mem (stackArg s 4) Hh.len)
            (Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
            (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)))) := by
  unfold Impl.RsaOaep.X86_64.Precomputed.encMain seqs seqs seqs seqs seqs seqs
  refine encMask_ok hTH hTG fH fG eH eG hp.toEPre he L R hW hk fun t9 V9 W9 he9 L9 R9 W9e hlist => ?_
  refine WP.seq ?_
  rw [Impl.RsaOaep.X86_64.Precomputed.pubArgs, WP.block_append_iff]
  refine WP.mono (wp_good pubArgs_good (pubArgs_ok L9 R9 W9e))
    fun t10 ⟨⟨L10, k10, R10, hdi, hsi, _, _, h8, h9⟩, sp10, mx10, f10⟩ => ?_
  have he10 : EnvE s t10 := he9.step k10.2.1 k10.2.2 sp10 (keep_cs3 k10 (by decide)) mx10 f10
  refine WP.mono (wp_good (block_good _ rfl rfl) (load_pre hp he10.rsp he10.rd he10.fr))
    fun t11 ⟨⟨k11, hm11, hdx, hcx⟩, sp11, mx11, f11⟩ => ?_
  have he11 : EnvE s t11 := he10.step k11.2.1 k11.2.2 sp11 (keep_cs3 k11 (by decide)) mx11 f11
  have L11 : Lay t11 (fb s) (stackArg s 6) := L10.congr (k11.gpr (by decide)) k11.2.2 (by rw [hm11])
  refine WP.mono (call_ok v hp L11 (hm11 ▸ R10) he11.rd he11.wr he11.fr (by simp [upd]) (by simp [upd])
    (by simp [upd]) (by simp [upd]) ((k11.gpr (by decide)).trans hdi) ((k11.gpr (by decide)).trans hsi) hdx hcx
    ((k11.gpr (by decide)).trans h8) ((k11.gpr (by decide)).trans h9))
    fun t12 ⟨hout, rd12, wr12, cs12, mx12, f12⟩ => ?_
  refine ⟨he11.step rd12 wr12 (cs12 .rsp (by decide)) (fun r hr _ => cs12 r hr) mx12 f12, fun hq => ?_⟩
  have := hout hq
  rw [hlist] at this
  exact this

include hTH hTG in
/-- For the hash functions `Hh` and `Gh` that the selectors name, whose
streaming functions are `TH` and `TG`. -/
theorem body_ok (v : PublicImpl) {s : State} (fH : FnsOf s TH 12) (fG : FnsOf s TG 13)
    (eH : Spec.HashId.mgf1 (selH s) = some Hh) (eG : Spec.HashId.mgf1 (selG s) = some Gh)
    (iH : selH s ∈ Spec.RsaOaep.hashIds) (iG : selG s ∈ Spec.RsaOaep.hashIds) (hp : PPre Hh s) :
    WP isa (Impl.RsaOaep.X86_64.Precomputed.encrypt v.name v.code) s
      fun s' => abiPreserved s s' ∧ (Consistent s → (encK Hh Gh).post s s') := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlen : Hh.len = TH.S.digestBytes := hTH.len
  have hnl : (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length = (s.gpr .rcx).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hml : (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat).length = (stackArg s 3).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hsl : (Spec.Rsa.bytesAt s.mem (stackArg s 4) Hh.len).length = Hh.len := by simp [Spec.Rsa.bytesAt]
  refine wp_alloc (by have := hp.sp1; unfold encStack at this; unfold frameBytes; omega) ?_
  refine encBodyWith_ok iH iG (lenOf_eq hTH eH).symm (by have := hTH.digest; have := hTH.out; omega) hp.toEPre
    (fun t' he' hw' hb => ?_) fun t he L R hk => ?_
  · obtain ⟨h1, h2, h3, h4⟩ := encEnd_ok hp.toEPre he' hw'
    refine ⟨h1, h2, h3, fun _ => ?_⟩
    show Spec.Rsa.written _ _ _ _ _
    rw [encrypt_none (by rw [hnl, hlen, hml]; omega)]; exact h4
  · refine WP.mono (encMain_ok hTH hTG v fH fG eH eG hp he L R (fun _ _ => rfl) hk) fun t' ⟨he', hw'⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := encEnd_abi hp.toEPre he'
    refine ⟨h1, h2, h3, fun hq => ?_⟩
    show Spec.Rsa.written _ _ _ _ _
    have hw'' := hw' hq
    rw [encrypt_some (by rw [hsl]) (by rw [hnl, hlen, hml]; omega), hnl, hml, hlen]
    rw [hlen] at hw''
    exact hw''

/-- The hash functions the selectors of an entry state name, their
streaming functions in the tables, and the precondition. -/
theorem sel_of {s : State} (h : (Spec.RsaOaep.encryptAnyContract abi encStack).pre s) :
    ∃ TH TG Hh Gh, Spec.HashFns.streaming (selH s) = some TH ∧ Spec.HashFns.streaming (selG s) = some TG ∧
      Spec.HashId.mgf1 (selH s) = some Hh ∧ Spec.HashId.mgf1 (selG s) = some Gh ∧ StreamingOK TH Hh ∧
      StreamingOK TG Gh ∧ FnsOf s TH 12 ∧ FnsOf s TG 13 ∧ selH s ∈ Spec.RsaOaep.hashIds ∧
      selG s ∈ Spec.RsaOaep.hashIds ∧ PPre Hh s := by
  obtain ⟨iH, iG, hpp⟩ := pre_of h
  obtain ⟨Hh, eH⟩ : ∃ Hh, Spec.HashId.mgf1 (selH s) = some Hh := by
    simp only [Spec.RsaOaep.hashIds, List.mem_cons, List.not_mem_nil, or_false] at iH
    rcases iH with e | e | e | e | e | e | e <;> rw [e] <;> exact ⟨_, rfl⟩
  have hp := hpp Hh eH
  obtain ⟨TH, Hh', sH, eH', oH, fH⟩ := fns_of_tab hp.fH
  obtain ⟨TG, Gh, sG, eG, oG, fG⟩ := fns_of_tab hp.fG
  rw [eH, Option.some.injEq] at eH'
  subst eH'
  exact ⟨TH, TG, Hh, Gh, sH, sG, eH, eG, oH, oG, fH, fG, iH, iG, hp⟩

/-- `vg_rsa_oaep_encrypt_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`. -/
theorem code_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaOaep.encryptAnyContract abi encStack).pre s) :
    ∃ t' s', Exec isa (Impl.RsaOaep.X86_64.Precomputed.encrypt v.name v.code) s t' s' ∧
      abiPreserved s s' ∧ post s s' := by
  obtain ⟨TH, TG, Hh, Gh, -, -, eH, eG, oH, oG, fH, fG, iH, iG, hp⟩ := sel_of h
  obtain ⟨t', s', he, ha, hq⟩ := body_ok oH oG v fH fG eH eG iH iG hp
  refine ⟨t', s', he, ha, fun hc H G eH' eG' => ?_⟩
  rw [eH] at eH'
  rw [eG] at eG'
  cases eH'; cases eG'
  exact hq hc

end VG.Proof.RsaOaep.X86_64.Pc
