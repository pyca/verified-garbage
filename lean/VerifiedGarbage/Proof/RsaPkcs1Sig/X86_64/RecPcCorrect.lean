module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcTail
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: correctness

The length check, the frame's push, the call with `pre` (`pubArgs_ok`,
`call_ok`), what follows it whatever it left (`afterPub_ok`) and the pop:
memory safety and the registers the ABI keeps whatever `pre` holds, and, if
`pre` holds the values for `n`, `recContract`'s postcondition, since `relOut`
of what the call then leaves is `recOut` (`code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 Rec
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR allocState_gpr freed wp_alloc)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.WriteBytes

/-- `recContract`'s postcondition, if `pre` holds the values for `n`. -/
def post (s u : State) : Prop := Consistent s → recContract.post s u

/-- Recovery's result from the public operation's result `o`. -/
def recOf (k : Nat) (h : Spec.RsaPkcs1Sig.Hash) : Option (List Byte) → Option (List Byte)
  | some em => if Spec.RsaPkcs1Sig.encode h (em.drop (k - h.len)) k = some em then some (em.drop (k - h.len))
      else none
  | none => none

theorem relOut_written {m : Mem} {p : Addr} {k : Nat} {h : Spec.RsaPkcs1Sig.Hash} {st : BitVec 64}
    {o : Option (List Byte)} (hw : Spec.Rsa.written m p k (st.setWidth 32) o) :
    relOut k h st (Spec.Rsa.bytesAt m p k) = recOf k h o := by
  cases o with
  | none => simp only [relOut, hw.1, ne_eq, not_true_eq_false, false_and, ↓reduceIte, recOf]
  | some em =>
    obtain ⟨h1, h2⟩ := hw
    rw [relOut, h1, h2, recOf]
    exact if_congr ⟨fun h => h.2, fun h => ⟨by decide, h⟩⟩ rfl rfl

theorem recOut_eq (nB eB sig : List Byte) (h : Spec.RsaPkcs1Sig.Hash) :
    recOut nB eB h sig = recOf nB.length h (Spec.Rsa.publicOpChecked nB eB sig) := by
  unfold recOut; cases Spec.Rsa.publicOpChecked nB eB sig <;> rfl

theorem code_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) s t s' ∧
      abiPreserved s s' ∧ post s s' := by
  have hp := pre_of h
  have hk2 := hp.k2
  have ol := hp.ol
  obtain ⟨hh, hid, hol⟩ := hp.hash
  suffices hw : WP isa (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) s fun s' =>
      abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  have hpost : ∀ (u : State) (o : Option (List Byte)), Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32) o →
      (o = Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) hh
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)) → recContract.post s u := by
    intro u o hw ho h' hid'
    rw [hid] at hid'; cases hid'
    rw [← ho]; exact hw
  unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code
  refine WP.seq (WP.mono_mx (by decide) (lenCheck_ok hp.toPreR) fun t₀ ⟨k₀, hm₀, hz₀⟩ hmx₀ => ?_)
  have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
  by_cases hsig : stackArg s 2 = s.gpr .rcx
  · refine WP.ite false (by simp [eval, hz₀, hsig]) (by simp) (fun _ => ?_)
    have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
    have hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
      ⟨fun r hr => by
        simp only [allocState_gpr, fb, hsp₀]
        split
        · rfl
        · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
    have hfb : fb t₀ = fb s := by simp only [fb, hsp₀]
    refine wp_alloc (s := t₀) (by rw [hsp₀]; have := hp.sp1; unfold verStack at this; unfold frameBytes; omega_arith) ?_
    unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.body
    refine WP.seq (WP.mono_mx (by decide) (pubArgs_ok hp hsig hA hm₀) fun t₁ ⟨hj, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (call_ok v hp hj) fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (afterPub_ok hp.toPreR he₂ hid) (by decide +kernel)) fun t₃ ⟨⟨he₃, hwu⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2],
      ⟨fun r hr => ?_, ret_frame hp.toPreR he₃.mem, ?_⟩, fun hq => hpost _ _ hwu ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
        rw [he₃.rsp, BitVec.sub_add_cancel]
      · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
        simp only [hr', ↓reduceIte]
        have hr'' : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
          simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | simp_all
        rw [k₃.gpr hr'', hcs₂ r hr, hcs₁ r hr hr']
    · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
      rw [hmx₃, hmx₂, hmx₁]; exact congrArg _ hmx₀
    · rw [relOut_written (hw hq), hsig, recover_eq_recOut _ (by simp only [bytesAt_length])]
      rw [recOut_eq, bytesAt_length]
  · refine WP.ite true (by simp [eval, hz₀, hsig]) (fun _ => ?_) (by simp)
    have hwr : outR s ∈ t₀.wr := by rw [k₀.2.2, hp.hwr]; simp [outR]
    refine WP.mono_mx (by decide) (zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega_arith) (by omega_arith)
      (by rw [g₀ _ (by decide), Rec.ofNat_toNat64]) (by rw [g₀ _ (by decide)]; exact out_wr hwr))
      fun u ⟨hK, hm, hax⟩ hmx => ⟨⟨fun r hr => ?_, ?_, by rw [hmx, hmx₀]⟩, fun _ => hpost u none ⟨by rw [hax]; rfl, ?_⟩ ?_⟩
    · rw [hK.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        k₀.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    · rw [hm, g₀ _ (by decide)]
      refine ((frame_writeBytes t₀.mem _ _).readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)).trans (by rw [hm₀])
      rw [List.mem_singleton.mp hr, List.length_replicate]; exact hp.dRo
    · rw [hm, g₀ _ (by decide)]
      have := bytesAt_writeBytes t₀.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega_arith)
      rwa [List.length_replicate] at this
    · rw [recover_len _ (by simp only [bytesAt_length]; intro h'; exact hsig (BitVec.eq_of_toNat_eq h'))]

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc
