module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTFront
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedContract
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCall
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTCode
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTCode
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Primes
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KTail
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTResult
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedKMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedRanges
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedTail
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KTail
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop

/-! # Constant time of the complete RSA candidate with the shared call -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

private structure SharedCPub extends CPub where
  z28 : slot f.w 28 ≤ f.Z

private abbrev SharedCPub.fp (p : SharedCPub) : SharedFPub := ⟨p.f, p.rsp, p.z28⟩

private structure SharedCRel (p : SharedCPub) (s : State) : Prop extends CRel p.toCPub s where
  env : SharedEnv p.f.B p.f.Z p.rsp s

/-- After `kEntry`'s first instruction. -/
private def SharedC1 (p : SharedCPub) (t : State) : Prop :=
  ∃ s, SharedCRel p s ∧ t.gpr .r11 = p.f.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block (kEntry.drop 1)) t (EntryPost s · (arg s 3))

/-- After `kEntry`. -/
private def SharedC2 (p : SharedCPub) (t : State) : Prop := ∃ s, SharedCRel p s ∧ EntryPost s t (arg s 3)

/-- After the zeros to `out` and the length check. -/
private def SharedC3 (p : SharedCPub) (t : State) : Prop := ∃ s t₁, SharedCRel p s ∧ EntryPost s t₁ (arg s 3) ∧ Front s t₁ t

private theorem SharedC3.cf {p : SharedCPub} {t : State} (h : SharedC3 p t) : t.cf = some (decide (p.f.rl < 8 * p.f.w)) := by
  obtain ⟨s, t₁, hs, -, hf⟩ := h
  rw [hf.cf, hs.rl, hs.w]

private theorem SharedC3.k0 {p : SharedCPub} {t : State} (h : SharedC3 p t)
    (hlt : 8 * p.f.w ≤ p.f.rl) : SharedK0 p.fp t := by
  obtain ⟨s, t₁, hs, he, hf⟩ := h
  exact ⟨(show C3 p.toCPub t from ⟨s, t₁, hs.toCRel, he, hf⟩).k0 (by omega_arith),
    hs.env.kept (he.keep.trans hf.keep) (by decide)⟩

private theorem sharedCode_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedCRel) (VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith mm R.run) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.X86_64.Candidate.codeWith
  simp only [seqs]
  refine RelCT.seq (R := Two SharedC2) ?_ (RelCT.assoc (RelCT.seq (R := Two SharedC3) ?_ ?_))
  · -- The entry: the scratch space's base from the stack, then the header.
    rw [kEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := SharedC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := kctx_of hs.pre
    have hn := c.hs.nowrap
    have hZ := c.hZ
    have hk1 := c.k1
    have hhw : ∀ i < 32, InRegions s.wr (off (arg s 3) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 32 })] ++ kEntry.drop 1)) s
        (EntryPost s · (arg s 3)) := by
      rw [← kEntry_split]; exact kEntry_ok rfl hhw c.ha c.hsep
    have e3 : s.gpr .rsp + BitVec.ofInt 64 32 = stackArgAddr s 3 := rfl
    have hB' : s.mem.readW (stackArgAddr s 3) 64 = stackArg s 3 := rfl
    refine WP.mono (WP.and' (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 3)
      (by xrun [State.ea, e3, c.ha 3 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.B, (k.gpr (by decide)).trans hs.rsp, hw⟩
  · -- The zeros to `out` and the length check.
    refine kt_piece (fun p : SharedCPub => p.f.B) (fun p => p.f.wr) [kOut, kLen, kRandLen]
      (fun p => [(kOut, p.f.op), (kLen, BitVec.ofNat 64 (8 * p.f.w)), (kRandLen, BitVec.ofNat 64 p.f.rl)]) []
      (by decide) (fun _ => rfl) ?_ (pins_nil _) (by taint_decide) ?_
    · rintro p t ⟨s, hs, he⟩
      refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, by rw [he.rdi, hs.B], by rw [he.keep.2.2, hs.wr],
        fun e he' => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl
      · rw [← hs.B, he.out, hs.op]
      · rw [← hs.B, he.len, ← hs.w, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [← hs.B, he.rlen, ← hs.rl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rintro p t ⟨s, hs, he⟩
      exact WP.mono (front_ok (kctx_of hs.pre) he) fun t' hf => ⟨s, t, hs, he, hf⟩
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.cf, h₂.cf]) ?_ ?_
  · -- Too few octets.
    refine kt_ct (fun p : SharedCPub => p.f.B) (fun p => p.f.wr) [kUsedP] (fun p => [(kUsedP, p.f.up)]) [] (by decide)
      (fun _ => rfl) ?_ (pins_nil _) (by taint_decide)
    rintro p t ⟨⟨s, t₁, hs, he, hf⟩, -⟩
    have c := kctx_of hs.pre
    refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, by rw [hf.keep.gpr (by decide), he.rdi, hs.B],
      by rw [hf.keep.2.2, he.keep.2.2, hs.wr], fun e he' => ?_⟩
    simp only [List.mem_singleton] at he'
    subst he'
    show word t.mem p.f.B (8 * kUsedP) = p.f.up
    rw [← hs.B, hf.word c (i := kUsedP) (by decide), he.usedP, hs.up]
  · exact (sharedKMain_ct M hmc R).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.fp, h₁.1.k0 (by have := h₁.2; simpa [eval, h₁.1.cf] using this),
        h₂.1.k0 (by have := h₂.2; simpa [eval, h₂.1.cf] using this)⟩) h) fun _ _ h => h

private def sharedCpubOf (s : State) (h : candPre s) : SharedCPub :=
  ⟨cpubOf s, by
    have c := kctx_of h
    have hz := c.hZ
    have hk := c.k8
    have h1 := c.k1
    change slot ((s.gpr .rsi).toNat / 8) 28 ≤ (arg s 4).toNat * 8
    simp only [slot, hdrBytes]
    omega_arith⟩

private theorem shared_crel_self {s : State} (h : sharedCandPre s) :
    SharedCRel (sharedCpubOf s h.1) s := ⟨crel_self h.1, h.2⟩

private theorem shared_crel_of {s t : State} (hs : sharedCandPre s) (ht : sharedCandPre t) (hp : candPub s t) :
    SharedCRel (sharedCpubOf s hs.1) t := by
  have hc := crel_of hs.1 ht.1 hp
  refine ⟨hc, ?_⟩
  change SharedEnv (cpubOf s).f.B (cpubOf s).f.Z (cpubOf s).rsp t
  rw [← hc.B, ← hc.Z, ← hc.rsp]
  exact ht.2

theorem sharedCode_constantTime (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    ConstantTime isa sharedCandPre candPub (codeWith mm R.run) :=
  RelCT.constantTime ((sharedCode_ct M hmc R).mono (fun s _t ⟨hs, ht, hp⟩ =>
    ⟨sharedCpubOf s hs.1, shared_crel_self hs, shared_crel_of hs ht hp⟩) (fun _ _ h => h))

end VG.Proof.RsaKeyGen.X86_64
