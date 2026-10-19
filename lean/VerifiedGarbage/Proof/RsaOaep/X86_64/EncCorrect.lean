module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCtx
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

/-!
# RSAES-OAEP encryption on x86-64: correctness

The frame, the prologue and the checks of `k` and the message's length
(zeros to `out` if either fails, then the rest of the function):
`encBodyWith_ok`, for `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`
(`PcCorrect`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked)

/-! ## The frame -/

/-- The state after the frame's pop. -/
def freed (bytes : Nat) (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s₂.wr.tail }

theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ Q (freed frameBytes s₂)) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc frameBytes) s = some (allocState frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free frameBytes) (allocState frameBytes s) s₂ = some (freed frameBytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

/-! ## The end -/

/-- What the function's caller sees: from a state in the frame with `out`
written as `o` says. -/
theorem encEnd_ok {H : Spec.Mgf1.Hash} {s s₂ : State} (hp : EPre H s) (he : EnvE s s₂) {o : Option (List Byte)}
    (hw : Spec.Rsa.written s₂.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s₂.gpr .rax).setWidth 32) o) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧
      (abiPreserved s (freed frameBytes s₂) ∧
        Spec.Rsa.written (freed frameBytes s₂).mem (s.gpr .rdi) (s.gpr .rcx).toNat
          (((freed frameBytes s₂).gpr .rax).setWidth 32) o) := by
  refine ⟨he.rsp, by rw [he.wr, EPre.wr hp], ⟨fun r hr => ?_, ?_, he.mx⟩, hw⟩
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

/-- Zeros to `out` and 0, from a state in the frame. -/
theorem encFail_ok {H : Spec.Mgf1.Hash} {s t : State} (hp : EPre H s) (he : EnvE s t) (L : Lay t (fb s) (stackArg s 5))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 5) V W) (hW : ArgsW s W) :
    WP isa zeroOut t fun t' => EnvE s t' ∧
      Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32) none := by
  obtain ⟨w14, w21, w22, w23, -⟩ := hW.w
  have hk1 := hp.k1; have hk2 := hp.k2; have hsi := hp.hsi
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) = outR s := by simp [outR, hsi]
  refine WP.mono (wp_good zeroOut_good (zeroOut_ok L R w21 (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega) hk2 (by rw [hout, he.wr]; simp) (by rw [← hsi]; exact hp.wO)
    ⟨by rw [hout]; exact (hp.d_stk_out.sub_left (frame_sub s)),
      by rw [hout]; exact (hp.d_out_scr.symm.sub_left (Region.sub_prefix (by unfold oRsa; have := hp.hsl; omega))),
      by rw [hout]; exact hp.d_stk_out.sub_left (ret_sub s)⟩))
    fun t' ⟨⟨L', k', R', hax, hz, _⟩, sp', mx', f'⟩ => ⟨he.step k'.2.1 k'.2.2 sp' (keep_cs3 k' (by decide)) mx' f', ?_, hz⟩
  rw [hax]; rfl

/-- `k` against `2 hLen + 2`. -/
theorem chkK_ok {Hm : Impl.Pbkdf2.Md.X86_64.Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hk1 : k < 2 ^ 32)
    (hD : Hm.D < 2 ^ 20) :
    WP isa (.block (chkK Hm)) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧ u'.gpr .rax = BitVec.ofNat 64 k ∧
      u'.cf = some (decide (k < 2 * Hm.D + 2)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = BitVec.ofNat 64 k ∧
    u'.cf = some (decide (k < 2 * Hm.D + 2))) ?_ rfl) fun u' ⟨⟨a, b, c⟩, kk⟩ => ⟨kk, a, b, c⟩
  xrun [chkK, im, ea_sp, L.rsp, L.ld (d := sK) (by decide), R.slot (d := sK) (k := 23) rfl (by decide) hk,
    VG.Proof.MlKem.X86_64.sx_ofNat (show 2 * Hm.D + 2 < 2 ^ 31 by omega)]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `msg_len` against `k - 2 hLen - 2`, from `rax = k`. -/
theorem chkMsg_ok {Hm : Impl.Pbkdf2.Md.X86_64.Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k mLen : Nat} (hml : W 30 = BitVec.ofNat 64 mLen)
    (hax : u.gpr .rax = BitVec.ofNat 64 k) (hk1 : k < 2 ^ 32) (hD : 2 * Hm.D + 2 ≤ k) (hm : mLen < 2 ^ 64)
    (hD' : Hm.D < 2 ^ 20) :
    WP isa (.block (chkMsg Hm)) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.cf = some (decide (k - (2 * Hm.D + 2) < mLen)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧
    u'.cf = some (decide (k - (2 * Hm.D + 2) < mLen))) ?_ rfl) fun u' ⟨⟨a, b⟩, kk⟩ => ⟨kk, a, b⟩
  xrun [chkMsg, im, ea_sp, L.rsp, L.ld (d := sMsgLen) (by decide), R.slot (d := sMsgLen) (k := 30) rfl (by decide) hml,
    hax, VG.Proof.MlKem.X86_64.sx_ofNat (show 2 * Hm.D + 2 < 2 ^ 31 by omega),
    VG.Offset.ofNat_sub_ofNat (show 2 * Hm.D + 2 ≤ k by omega)]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The prologue and the check of `k`: in the frame, with the argument
slots, `rax = k` and CF set if `k < 2 hLen + 2`. -/
theorem encHead_ok {H : Spec.Mgf1.Hash} {Hm : Impl.Pbkdf2.Md.X86_64.Stream} {s : State} (hp : EPre H s)
    (hD : Hm.D < 2 ^ 20) :
    WP isa (.block (encPrologue ++ chkK Hm)) (allocState frameBytes s) fun t2 => EnvE s t2 ∧
      Lay t2 (fb s) (stackArg s 5) ∧
      Rep t2.mem (fb s) (stackArg s 5) (fun o => s.mem (off (stackArg s 5) o)) (encW s) ∧
      t2.gpr .rax = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧
      t2.cf = some (decide ((s.gpr .rcx).toNat < 2 * Hm.D + 2)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  rw [WP.block_append_iff]
  refine WP.mono (wp_good (block_good _ rfl) (encPro_ok hp)) fun t1 ⟨⟨k1, L1, R1, f1⟩, sp1, mx1, _⟩ => ?_
  have hW : ArgsW s (encW s) := fun _ _ => rfl
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  have w23' : encW s 23 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (wp_good (block_good _ rfl) (chkK_ok (Hm := Hm) L1 R1 w23' (by omega) hD))
    fun t2 ⟨⟨k2, hm2, hax2, hcf2⟩, sp2, mx2, _⟩ => ?_
  have he2 : EnvE s t2 :=
    { rsp := (k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans rfl)
      rd := k2.2.1.trans k1.2.1
      wr := k2.2.2.trans (k1.2.2.trans (EPre.wr hp))
      cs := fun r hr h => by
        rw [k2.gpr (cs_disj [.rax] (by decide) r hr), k1.gpr (cs_disj [.rax] (by decide) r hr)]
        show (if r = .rsp then _ else s.gpr r) = s.gpr r
        simp only [h, ↓reduceIte]
      mx := by rw [mx2, mx1]; rfl
      fr := by
        rw [hm2]
        exact Frame.sub f1 fun r hr => by
          rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩ }
  exact ⟨he2, L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), hm2 ▸ R1, hax2, hcf2⟩

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

include hH in
/-- The prologue and the checks, then `main` from a state in the frame if
they pass: `Q`, if failing them leads to `Q` and `main` does. -/
theorem encBodyWith_ok {Hs : Spec.Mgf1.Hash} {main : Prog isa} {s : State} (hp : EPre Hs s) {Q : State → Prop}
    (hfail : ∀ t', EnvE s t' → Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
      none → ¬ 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat → Q t')
    (hmain : ∀ t, EnvE s t → Lay t (fb s) (stackArg s 5) →
      Rep t.mem (fb s) (stackArg s 5) (fun o => s.mem (off (stackArg s 5) o)) (encW s) →
      2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat → WP isa main t Q) :
    WP isa (encBodyWith Hl.stream main) (allocState frameBytes s) Q := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD := hH.hD0; have hDN := hH.hDN; have hN := hH.N_le
  have hsD : Hl.stream.D = Hl.D := rfl
  unfold encBodyWith seqs seqs seqs
  have hW : ArgsW s (encW s) := fun _ _ => rfl
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  refine WP.seq (WP.mono (encHead_ok (Hm := Hl.stream) hp (by omega)) fun t2 ⟨he2, L2, R2, hax2, hcf2⟩ => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .b t2 = _ from hcf2) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    exact WP.mono (encFail_ok hp he2 L2 R2 hW) fun t' ⟨he', hw'⟩ => hfail t' he' hw' (by omega)
  · rw [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (wp_good (block_good _ rfl) (chkMsg_ok (Hm := Hl.stream) L2 R2 (k := (s.gpr .rcx).toNat)
      (mLen := (stackArg s 3).toNat) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hax2 (by omega)
      (by omega) (stackArg s 3).isLt (by omega)))
      fun t3 ⟨⟨k3, hm3, hcf3⟩, sp3, mx3, f3⟩ => ?_)
    have he3 : EnvE s t3 := he2.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3
    have L3 : Lay t3 (fb s) (stackArg s 5) := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
    have R3 : Rep t3.mem (fb s) (stackArg s 5) (fun o => s.mem (off (stackArg s 5) o)) (encW s) := hm3 ▸ R2
    refine WP.ite (M := isa) _ (show isa.eval .b t3 = _ from hcf3) (fun hb' => ?_) (fun hb' => ?_)
    · rw [decide_eq_true_eq] at hb'
      exact WP.mono (encFail_ok hp he3 L3 R3 hW) fun t' ⟨he', hw'⟩ => hfail t' he' hw' (by omega)
    · rw [decide_eq_false_iff_not] at hb'
      exact hmain t3 he3 L3 R3 (by omega)

end VG.Proof.RsaOaep.X86_64
