module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

/-!
# RSAES-OAEP encryption on x86-64: correctness

The frame, the prologue and the checks of `k` and the message's length
(zeros to `out` if either fails, then the rest of the function):
`encBodyWith_ok`, for `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`
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
theorem encFail_ok {H : Spec.Mgf1.Hash} {s t : State} (hp : EPre H s) (he : EnvE s t) (L : Lay t (fb s) (stackArg s 6))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 6) V W) (hW : ArgsW s W) :
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

/-- The prologue: in the frame, with the argument slots. -/
theorem encHead_ok {H : Spec.Mgf1.Hash} {s : State} (hp : EPre H s) :
    WP isa (.block encPrologue) (allocState frameBytes s) fun t1 => EnvE s t1 ∧
      Lay t1 (fb s) (stackArg s 6) ∧
      Rep t1.mem (fb s) (stackArg s 6) (fun o => s.mem (off (stackArg s 6) o)) (encW s) := by
  refine WP.mono (wp_good (block_good _ rfl) (encPro_ok hp)) fun t1 ⟨⟨k1, L1, R1, f1⟩, sp1, mx1, _⟩ => ?_
  have he1 : EnvE s t1 :=
    { rsp := (k1.gpr (by decide)).trans rfl
      rd := k1.2.1
      wr := k1.2.2.trans (EPre.wr hp)
      cs := fun r hr h => by
        rw [k1.gpr (cs_disj [.rax] (by decide) r hr)]
        show (if r = .rsp then _ else s.gpr r) = s.gpr r
        simp only [h, ↓reduceIte]
      mx := by rw [mx1]; rfl
      fr := Frame.sub f1 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩ }
  exact ⟨he1, L1, R1⟩

/-- The checks, for the digest length the code uses only. -/
theorem encChecks_D {G G' : Impl.Pbkdf2.Md.X86_64.Stream} (h : G.D = G'.D) (main : Prog isa) :
    encChecks G main = encChecks G' main := by
  simp only [encChecks, chkK, chkMsg, h]

theorem ArgsW_35 {s : State} {p : Addr} : ArgsW s (upd (encW s) 35 p) := fun k hk => by
  simp only [upd]; rw [ifn (by omega)]

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

include hH mH in
/-- The prologue, the table of the label's hash function to its slot, the
branch on its digest length and the checks, then `main` from a state in the
frame if they pass: `Q`, if failing them leads to `Q` and `main` does. -/
theorem encBodyWith_ok {Hs : Spec.Mgf1.Hash} {f : Impl.Mgf1.X86_64.Table.Fns} {main : Nat → Prog isa} {s : State}
    (hp : EPre Hs s)
    (hTL : ∀ t, EnvE s t → t.syms = s.syms → Table.Tab Hl.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t)
    {Q : State → Prop}
    (hfail : ∀ t', EnvE s t' → Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
      none → ¬ 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat → Q t')
    (hmain : ∀ t, EnvE s t → t.syms = s.syms → Lay t (fb s) (stackArg s 6) →
      Rep t.mem (fb s) (stackArg s 6) (fun o => s.mem (off (stackArg s 6) o)) (upd (encW s) 35 (stackArg s 10)) →
      2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat → WP isa (main Hl.D) t Q) :
    WP isa (encBodyWith main) (allocState frameBytes s) Q := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD := hH.hD0; have hDN := hH.hDN; have hN := hH.N_le
  have hsD : Hl.stream.D = Hl.D := rfl
  have hDl : Hl.stream.D ∈ lens := by rw [hsD, ← mH.len]; exact mem_lens mH.mem
  unfold encBodyWith seqs seqs seqs
  have hW : ArgsW s (upd (encW s) 35 (stackArg s 10)) := ArgsW_35
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  refine WP.seq (WP.mono_syms (encHead_ok hp) fun t1 ⟨he1, L1, R1⟩ sy1 => ?_)
  have TL := hTL t1 he1 sy1
  refine WP.seq (WP.mono_syms (wp_good (block_good _ rfl) (tabSlot_ok L1 R1 TL))
    fun ta ⟨⟨ka, La, Ra, sya⟩, spa, mxa, fa⟩ _ => ?_)
  have hea : EnvE s ta := he1.step ka.2.1 ka.2.2 spa (keep_cs3 ka (by decide)) mxa fa
  have hDa : ta.mem.readW (off (stackArg s 10) 32) 64 = BitVec.ofNat 64 Hl.stream.D :=
    (TL.mem ta.mem (by have := fa; rwa [L1.rsp] at this)).2.1
  refine WP.seq (WP.mono_syms (wp_good (block_good _ rfl) (lenLoad_ok La Ra (by simp [upd])
      (by rw [ka.2.1, ka.2.2]; exact TL.rdD) hDa))
    fun tb ⟨⟨kb, h11b, hmb, syb⟩, spb, mxb, fb'⟩ _ => ?_)
  have heb : EnvE s tb := hea.step kb.2.1 kb.2.2 spb (keep_cs3 kb (by decide)) mxb fb'
  refine byLen_ok hDl (by decide) (mem_lens_lt hDl) h11b fun t1' kc hmc syc mxc => ?_
  rw [encChecks_D (G := ofLen Hl.stream.D) (G' := Hl.stream) rfl]
  have he1' : EnvE s t1' := heb.step kc.2.1 kc.2.2 (kc.gpr (by simp)) (keep_cs3 kc rfl) mxc
    (by rw [hmc]; exact Frame.refl _ _)
  have hm1' : t1'.mem = ta.mem := hmc.trans hmb
  have L1' : Lay t1' (fb s) (stackArg s 6) := La.congr ((kc.gpr (by simp)).trans (kb.gpr (by decide)))
    (kc.2.2.trans kb.2.2) (by rw [hm1'])
  have R1' := hm1' ▸ Ra
  have sy1' : t1'.syms = s.syms := syc.trans (syb.trans (sya.trans sy1))
  unfold encChecks seqs seqs seqs
  have w23' : upd (encW s) 35 (stackArg s 10) 23 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono_syms (wp_good (block_good _ rfl) (chkK_ok (Hm := Hl.stream) L1' R1' w23' (by omega)
      (by omega)))
    fun t2 ⟨⟨k2, hm2, hax2, hcf2⟩, sp2, mx2, f2⟩ sy2 => ?_)
  have he2 : EnvE s t2 := he1'.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  have L2 : Lay t2 (fb s) (stackArg s 6) := L1'.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 := hm2 ▸ R1'
  refine WP.ite (M := isa) _ (show isa.eval .b t2 = _ from hcf2) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    exact WP.mono (encFail_ok hp he2 L2 R2 hW) fun t' ⟨he', hw'⟩ => hfail t' he' hw' (by omega)
  · rw [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono_syms (wp_good (block_good _ rfl) (chkMsg_ok (Hm := Hl.stream) L2 R2 (k := (s.gpr .rcx).toNat)
      (mLen := (stackArg s 3).toNat) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hax2 (by omega)
      (by omega) (stackArg s 3).isLt (by omega)))
      fun t3 ⟨⟨k3, hm3, hcf3⟩, sp3, mx3, f3⟩ sy3 => ?_)
    have he3 : EnvE s t3 := he2.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3
    have L3 : Lay t3 (fb s) (stackArg s 6) := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
    have R3 := hm3 ▸ R2
    refine WP.ite (M := isa) _ (show isa.eval .b t3 = _ from hcf3) (fun hb' => ?_) (fun hb' => ?_)
    · rw [decide_eq_true_eq] at hb'
      exact WP.mono (encFail_ok hp he3 L3 R3 hW) fun t' ⟨he', hw'⟩ => hfail t' he' hw' (by omega)
    · rw [decide_eq_false_iff_not] at hb'
      exact hmain t3 he3 (sy3.trans (sy2.trans sy1')) L3 R3 (by omega)

end VG.Proof.RsaOaep.X86_64
