module

-- separate module: the unfolding of the callee's contract builds in parallel with `RndScan`

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncPre
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: the callee's contract

`vg_rsa_pkcs1_encrypt_precomputed`'s contract (with its stack,
`Impl.RsaPkcs1Sig.PPC64LE.frameBytes`) by name: its precondition from `PreE`
(`enc_pre`), its postcondition (`enc_post`) and its public data
(`enc_pub`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

/-- The callee's contract. -/
abbrev encK : Contract isa :=
  Spec.RsaPkcs1Enc.encryptPrecomputedContract abi Impl.RsaPkcs1Sig.PPC64LE.frameBytes

theorem enc_pre {x : State} (h : PreE x) : encK.pre x := by
  have e : Impl.RsaPkcs1Sig.PPC64LE.frameBytes = 2223 + 1 := rfl
  have h1 := h.sp1
  show (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi Impl.RsaPkcs1Sig.PPC64LE.frameBytes).pre x
  rw [e] at h1 ⊢
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq, List.range, List.range.loop]
  exact ⟨h1, by have := h.sp2; omega, h.hrd, h.hwr, h.on, h.oe, h.om, h.ops, h.osc, h.op, h.oa, h.ns, h.es, h.ms,
    h.pss, h.sp, h.sa, h.ko, h.kn, h.ke, h.km, h.kps, h.ksc, h.kp, h.ka, h.wo, h.wn, h.we, h.wm, h.wps, h.wsc,
    h.wp, ⟨h.k1, h.k2⟩, h.ok, h.e1, h.e2, h.ml, h.pl, h.hs, h.hp⟩

theorem enc_post {x x' : State} (h : encK.post x x') :
    Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt x.mem (x.gpr .r5) (x.gpr .r6).toNat) =
        some (Spec.Rsa.wordsAt x.mem (stackArg x 4) (stackArg x 5).toNat) →
      Spec.Rsa.written x'.mem (x.gpr .r3) (x.gpr .r6).toNat ((x'.gpr .r3).setWidth 32)
        (Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt x.mem (x.gpr .r5) (x.gpr .r6).toNat)
          (Spec.Rsa.bytesAt x.mem (x.gpr .r7) (x.gpr .r8).toNat)
          (Spec.Rsa.bytesAt x.mem (x.gpr .r9) (x.gpr .r10).toNat)
          (Spec.Rsa.bytesAt x.mem (stackArg x 0) (stackArg x 1).toNat)) := by
  sig_post [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq, List.range, List.range.loop] at h
  exact h

theorem enc_pub {x₁ x₂ : State} (hsp : x₁.sp = x₂.sp) (hg : ∀ r ∈ argRegs, x₁.gpr r = x₂.gpr r)
    (ha : ∀ i < 6, stackArg x₁ i = stackArg x₂ i)
    (hn : Spec.Rsa.bytesAt x₁.mem (x₁.gpr .r5) (x₁.gpr .r6).toNat =
      Spec.Rsa.bytesAt x₂.mem (x₂.gpr .r5) (x₂.gpr .r6).toNat)
    (he : Spec.Rsa.bytesAt x₁.mem (x₁.gpr .r7) (x₁.gpr .r8).toNat =
      Spec.Rsa.bytesAt x₂.mem (x₂.gpr .r7) (x₂.gpr .r8).toNat)
    (hw : Spec.Rsa.wordsAt x₁.mem (stackArg x₁ 4) (stackArg x₁ 5).toNat =
      Spec.Rsa.wordsAt x₂.mem (stackArg x₂ 4) (stackArg x₂ 5).toNat) :
    encK.pub x₁ x₂ := by
  sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨hsp, by rw [hn, he, hw], hg _ (by decide), hg _ (by decide), hg _ (by decide), hg _ (by decide),
    hg _ (by decide), hg _ (by decide), hg _ (by decide), hg _ (by decide), ha 0 (by decide), ha 1 (by decide),
    ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide)⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
