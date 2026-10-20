module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCall

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcTail
import Mathlib.Tactic.SplitIfs

/-!
# `vg_rsa_pkcs1_recover_precomputed` on AArch64: correctness

As `vg_rsa_pkcs1_recover`'s (`Rec.code_ok`), with the call of the
precomputed public operation (`callP_ok`) and the masked release
(`afterPub_ok`): the calling convention whatever `pre` holds, and
recovery's result if it holds the modulus' values.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.RecPc

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Sig.AArch64.Pc (stackArgs_five)

/-- What `vg_rsa_pkcs1_recover_precomputed` returns and writes if `pre`
holds the modulus' values, and the calling convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (Consistent s → ∀ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h →
    Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)))

theorem code_ok (c : PdChecked) {s : State} (hp : PrePR c.stack s) :
    WP isa (code c.name c.code) s (Post s) := by
  have hv := hp.r
  obtain ⟨h, hh, hol⟩ := hv.hh
  have hof : ∀ h', Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h' → h' = h :=
    fun h' e => Option.some.inj (e.symm.trans hh)
  unfold code
  refine WP.seq (WP.mono (Rec.lenCheck_ok hv) fun t₁ ⟨o₁, e₁⟩ => ?_)
  have hne := Rec.eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .x3
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.alloc (by decide) (by rw [o₁.sp]; have := hv.sp1; unfold stk at this; omega) ?_
    unfold body
    refine WP.seq (WP.mono (pubArgs_okP hp (by simp [allocated, o₁.sp]) (by simp [allocated, o₁.rd])
      (by simp [allocated, o₁.sp, o₁.wr]) (by simp [allocated, o₁.mem]) (fun r hr => by
        simp only [allocated]; exact o₁.gpr r (by simpa using hr)) (fun r hr => o₁.vcs r hr))
      fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (callP_ok c hp h₂ hsig) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (afterPub_ok hv hh hol h₃) fun t₄ ⟨m₄, r₄⟩ => ?_)
    refine WP.mono (Rec.restore_ok m₄) fun w ⟨habi, hx0, hmem⟩ => ⟨habi, fun hq h' e => ?_⟩
    rw [hof h' e, Rec.recover_eq h hsig, hx0, hmem]; exact r₄ hq
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => WP.mono (Rec.zeroArgs_ok hv o₁) fun w ⟨o, r⟩ =>
      ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, fun _ h' _ => ?_⟩) (by simp)
    · have h8 : r ∉ [Reg.x8, .x14, .x13, .x15, .x13, .x14, .x0] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      exact o.gpr r h8
    · rw [o.sp]
    · rw [o.vcs r hr]
    · rw [Rec.recover_none h' hsig]; exact r

theorem code_correct (c : PdChecked) (s : State)
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi (stk c.stack)).pre s) :
    ∃ t s', Exec isa (code c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi (stk c.stack)).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c (prePR_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Sig.AArch64.RecPc
