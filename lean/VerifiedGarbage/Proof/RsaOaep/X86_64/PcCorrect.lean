module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCall
public import VerifiedGarbage.Impl.RsaOaep.X86_64.Precomputed
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: correctness

`EM` built and masked as `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` does
(`encMask_ok`), then the call with `pre` (`encMain_ok`), after the
prologue and the checks (`encBodyWith_ok`): memory safety and the registers
the ABI keeps whatever `pre` holds, and, if `pre` holds the values for `n`,
`encK`'s postcondition (`code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- `encK`'s postcondition, if `pre` holds the values for `n`. -/
def post (H G : Spec.Mgf1.Hash) (s u : State) : Prop := Consistent s → (encK H G).post s u

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

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

include hH KH hG KG mH mG in
theorem encMain_ok (v : PublicImpl) {s t : State} (hp : PPre mH.G s) (he : EnvE s t)
    (L : Lay t (fb s) (stackArg s 5)) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem (fb s) (stackArg s 5) V W) (hW : ArgsW s W)
    (hk : 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    WP isa (Impl.RsaOaep.X86_64.Precomputed.encMain Hl.stream Gm.stream v.name v.code) t fun t' => EnvE s t' ∧
      (Consistent s → Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (emOf mG.G Hl.D (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
            (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
            (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)))) := by
  unfold Impl.RsaOaep.X86_64.Precomputed.encMain seqs seqs seqs seqs seqs seqs
  refine encMask_ok hH KH hG KG mH mG hp.toEPre he L R hW hk fun t9 V9 W9 he9 L9 R9 W9e hlist => ?_
  refine WP.seq ?_
  rw [Impl.RsaOaep.X86_64.Precomputed.pubArgs, WP.block_append_iff]
  refine WP.mono (wp_good pubArgs_good (pubArgs_ok L9 R9 W9e))
    fun t10 ⟨⟨L10, k10, R10, hdi, hsi, _, _, h8, h9⟩, sp10, mx10, f10⟩ => ?_
  have he10 : EnvE s t10 := he9.step k10.2.1 k10.2.2 sp10 (keep_cs3 k10 (by decide)) mx10 f10
  refine WP.mono (wp_good (block_good _ rfl) (load_pre hp he10.rsp he10.rd he10.fr))
    fun t11 ⟨⟨k11, hm11, hdx, hcx⟩, sp11, mx11, f11⟩ => ?_
  have he11 : EnvE s t11 := he10.step k11.2.1 k11.2.2 sp11 (keep_cs3 k11 (by decide)) mx11 f11
  have L11 : Lay t11 (fb s) (stackArg s 5) := L10.congr (k11.gpr (by decide)) k11.2.2 (by rw [hm11])
  refine WP.mono (call_ok v hp L11 (hm11 ▸ R10) he11.rd he11.wr he11.fr (by simp [upd]) (by simp [upd])
    (by simp [upd]) (by simp [upd]) ((k11.gpr (by decide)).trans hdi) ((k11.gpr (by decide)).trans hsi) hdx hcx
    ((k11.gpr (by decide)).trans h8) ((k11.gpr (by decide)).trans h9))
    fun t12 ⟨hout, rd12, wr12, cs12, mx12, f12⟩ => ?_
  refine ⟨⟨(cs12 .rsp (by decide)).trans he11.rsp, rd12.trans he11.rd, wr12.trans he11.wr,
    fun r hr h => (cs12 r hr).trans (he11.cs r hr h), mx12.trans he11.mx, f12⟩, fun hq => ?_⟩
  have := hout hq
  rw [hlist] at this
  exact this

include hH KH hG KG mH mG in
theorem code_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaOaep.encryptPrecomputedContract mH.G mG.G abi encStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaOaep.X86_64.Precomputed.encrypt Hl.stream Gm.stream v.name v.code) s t s' ∧
      abiPreserved s s' ∧ post mH.G mG.G s s' := by
  have hp : PPre mH.G s := pre_of h
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlen : mH.G.len = Hl.D := mH.len
  have hnl : (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length = (s.gpr .rcx).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hml : (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat).length = (stackArg s 3).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hsl : (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len).length = mH.G.len := by simp [Spec.Rsa.bytesAt]
  suffices hw : WP isa (Impl.RsaOaep.X86_64.Precomputed.encrypt Hl.stream Gm.stream v.name v.code) s
      fun s' => abiPreserved s s' ∧ post mH.G mG.G s s' by
    obtain ⟨t, s', he, hq⟩ := hw; exact ⟨t, s', he, hq⟩
  refine wp_alloc (by have := hp.sp1; unfold encStack at this; unfold frameBytes; omega) ?_
  refine encBodyWith_ok hH hp.toEPre (fun t' he' hw' hb => ?_) fun t he L R hk => ?_
  · obtain ⟨h1, h2, h3, h4⟩ := encEnd_ok hp.toEPre he' hw'
    refine ⟨h1, h2, h3, fun _ => ?_⟩
    show Spec.Rsa.written _ _ _ _ _
    rw [encrypt_none (by rw [hnl, hlen, hml]; omega)]; exact h4
  · refine WP.mono (encMain_ok hH KH hG KG mH mG v hp he L R (fun _ _ => rfl) hk) fun t' ⟨he', hw'⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := encEnd_abi hp.toEPre he'
    refine ⟨h1, h2, h3, fun hq => ?_⟩
    show Spec.Rsa.written _ _ _ _ _
    have hw'' := hw' hq
    rw [encrypt_some (by rw [hsl]) (by rw [hnl, hlen, hml]; omega), hnl, hml, hlen]
    rw [hlen] at hw''
    exact hw''

end VG.Proof.RsaOaep.X86_64.Pc
