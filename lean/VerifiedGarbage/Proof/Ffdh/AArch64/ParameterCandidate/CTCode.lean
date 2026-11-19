module

import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Test
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Test
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.AArch64.ParameterCandidate.Code`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on AArch64: correctness

`code`, from a state `pcContract` allows, ends as
`Spec.Ffdh.sievedParameterCandidate` (`code_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The postcondition, from how the candidate ended after the entry and the
zeros to `out` (at `t₃`). -/
theorem pcEnd_post {s t₃ t : State} (c : PCtx s)
    (hz : ∀ i < (s.gpr .x1).toNat, t₃.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0)
    (kk : Keep (.x0 :: mmRegs) s t₃)
    (h : PEnd t₃ t (ppOf s) (Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r)) :
    abiPreserved s t ∧ pcPost s t := by
  have hL := c.len
  have key : ∀ {st u : Nat} {outv : Option Nat}, st < 4 →
      KEnd t₃ t (s.gpr .x0) (s.gpr .x2) (ppOf s).L st u outv →
      abiPreserved s t ∧ ((t.gpr .x0).setWidth 32).toNat = st ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat = (match outv with
        | some c => Spec.Rsa.i2osp c (s.gpr .x1).toNat
        | none => List.replicate (s.gpr .x1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 u] := by
    intro st u outv hst hk
    rw [← hL] at hk
    refine ⟨abiPreserved_of_keep ((kk.trans hk.keep).mono (by decide)), ?_, ?_, ?_⟩
    · rw [hk.x0, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hst]
    · show outBytes t.mem _ _ = _
      have := hk.out
      cases outv
      · rw [this]
        show List.map _ _ = _
        rw [List.map_congr_left fun i hi => hz i (List.mem_range.mp hi)]; simp [List.map_const']
      · exact this
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
        hk.used]
  unfold pcPost pcResult
  change PEnd t₃ t (ppOf s) (Spec.Ffdh.sievedParameterCandidate (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32).toNat
    (pcRand s)) at h
  have hrl : (pcRand s).length = (s.gpr .x6).toNat := pcRand_length s
  rcases hres : Spec.Ffdh.sievedParameterCandidate (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32).toNat (pcRand s) with
    _ | ⟨_ | _, rest⟩ <;> rw [hres] at h <;> simp only [PEnd] at h
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, hw⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw]; simp only [ppOf, hrl]⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw]; simp only [ppOf, hrl]⟩

/-- After the zeros to `out`. -/
structure Zeroed (s t₁ t : State) : Prop where
  zero : ∀ i < (s.gpr .x1).toNat, t.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ j < (s.gpr .x1).toNat, x ≠ s.gpr .x0 + BitVec.ofNat 64 j) → t.mem x = t₁.mem x
  keep : Keep [.x1, .x2, .x3] t₁ t

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem zeros_ok {s t₁ : State} (c : PCtx s) (he : EntryPost s t₁) :
    WP isa (zeroOut kOut kLen) t₁ (Zeroed s t₁) := by
  have hs := c.hs
  have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := c.dims.z
  have hb1 : 512 ≤ (s.gpr .x3).toNat := c.dims.b1
  have hb2 : (s.gpr .x3).toNat ≤ 8192 := c.dims.b2
  have hL : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 := c.len
  exact WP.mono (zeroOut_ok (len := (s.gpr .x1).toNat) (hs.congr he.keep.wr) he.x0 (by omega_using [hZ]) (sPtr := kOut)
    (sLen := kLen) (by decide) (by decide) he.args.out (by rw [he.args.len, ofNat_toNat64]) (by omega_using [hb1, hL]) (by omega_using [hb2, hL])
    ⟨fun j hj => by rw [he.keep.wr]; exact c.ou.outw j (by rw [← c.len]; exact hj),
      fun j hj => c.ou.outZ j (by rw [← c.len]; exact hj)⟩) fun _ ⟨a, b, d⟩ => ⟨a, b, d⟩

/-- The header words survive the zeros to `out`. -/
theorem Zeroed.word {s t₁ t : State} (c : PCtx s) (h : Zeroed s t₁ t) {i : Nat} (hi : i < 32) :
    word t.mem (s.gpr .x7) (8 * i) = word t₁.mem (s.gpr .x7) (8 * i) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := c.dims.z
  exact Mem.readW_congr fun b hb => h.frame _ fun j hj he' => by
    have : (stackArg s 0).toNat * 8 ≤ ofs (s.gpr .x7) (s.gpr .x0 + BitVec.ofNat 64 j) :=
      c.ou.outZ j (by rw [← c.len]; exact hj)
    rw [← he', ofs_off _ (by omega_using [hi, hb])] at this; omega_using [hi, hZ, hb, this]

/-- After the length check, from the state `s` on entry. -/
structure Front (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x7
  x5 : t.gpr .x5 = BitVec.ofNat 64 (decide ((s.gpr .x1).toNat ≤ (s.gpr .x6).toNat)).toNat
  zero : ∀ i < (s.gpr .x1).toNat, t.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0
  args : EArgs t.mem (s.gpr .x7) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3)
    (BitVec.ofNat 64 ((s.gpr .x4).setWidth 32).toNat) (s.gpr .x5) (s.gpr .x6)
  hi : ∀ x, 8 * 32 ≤ ofs (s.gpr .x7) x → (∀ j < (s.gpr .x1).toNat, x ≠ s.gpr .x0 + BitVec.ofNat 64 j) →
    t.mem x = s.mem x
  keep : Keep (.x0 :: mmRegs) s t

theorem EArgs.congr {m m' : Mem} {B : Addr} {v0 v1 v2 v3 v4 v5 v6 : BitVec 64} (h : EArgs m B v0 v1 v2 v3 v4 v5 v6)
    (hw : ∀ i < 32, word m' B (8 * i) = word m B (8 * i)) : EArgs m' B v0 v1 v2 v3 v4 v5 v6 :=
  ⟨(hw _ (by decide)).trans h.out, (hw _ (by decide)).trans h.len, (hw _ (by decide)).trans h.flen,
    (hw _ (by decide)).trans h.used, (hw _ (by decide)).trans h.usedP, (hw _ (by decide)).trans h.bits,
    (hw _ (by decide)).trans h.gen, (hw _ (by decide)).trans h.rand, (hw _ (by decide)).trans h.rlen⟩

theorem lenCheck_ok {s t₁ t₂ : State} (c : PCtx s) (he : EntryPost s t₁) (hz : Zeroed s t₁ t₂) :
    WP isa (.block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag)) t₂ (Front s) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.dims.z
  simp only [ppOf, PP.L] at hZ
  have hs₂ := (hs.congr he.keep.wr).congr hz.keep.wr
  have h0₂ : t₂.gpr .x0 = s.gpr .x7 := (hz.keep.gpr .x0 (by decide)).trans he.x0
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (s.gpr .x7) (8 * i)) 8 := fun i hi => hs₂.ld (by omega_using [hZ, hi])
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = s.gpr .x6 ∧
      t.gpr .x4 = s.gpr .x1 ∧ t.mem = t₂.mem) (by
    brun [h0₂, hdr_enc (show kRandLen < 32 by decide), hdr_enc (show kLen < 32 by decide), hl₂ kRandLen (by decide),
      hl₂ kLen (by decide), hz.word c (show kRandLen < 32 by decide), hz.word c (show kLen < 32 by decide),
      he.args.rlen, he.args.len])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h3₃, h4₃, hm₃⟩, k₃⟩ =>
    WP.mono (geFlag_ok t₃) fun t₄ ⟨⟨h5₄, hm₄⟩, k₄⟩ => ?_)
  rw [h3₃, h4₃] at h5₄
  have hm4 : t₄.mem = t₂.mem := hm₄.trans hm₃
  exact ⟨((k₃.trans k₄).gpr .x0 (by decide)).trans h0₂, h5₄, fun i hi => by rw [hm4]; exact hz.zero i hi,
    he.args.congr fun i hi => by rw [hm4]; exact hz.word c hi,
    fun x hx hx' => by rw [hm4, hz.frame x hx', he.out x (Or.inr (by omega_using [hx]))],
    (((he.keep.trans hz.keep).trans k₃).trans k₄).mono (by decide)⟩

/-- What `main` needs, after the front with enough octets. -/
theorem ph_of {s t : State} (c : PCtx s) (h : Front s t) : PH (ppOf s) t := by
  have hZ := c.dims.z
  have hrl := pcRand_length s
  refine ⟨c.hs.congr h.keep.wr, h.x0, ⟨h.args.out, h.args.usedP, ?_, ?_, h.args.gen, h.args.rand, ?_⟩,
    ?_, c.ou.congr h.keep.wr, c.dims⟩
  · show word t.mem (s.gpr .x7) _ = _
    rw [h.args.flen, ← c.len, ofNat_toNat64]
  · show word t.mem (s.gpr .x7) _ = _
    rw [h.args.bits]; exact (ofNat_toNat64 _).symm
  · show word t.mem (s.gpr .x7) _ = BitVec.ofNat 64 (pcRand s).length
    rw [h.args.rlen, hrl, ofNat_toNat64]
  · have hm : ∀ i < (pcRand s).length, t.mem (s.gpr .x5 + BitVec.ofNat 64 i) = s.mem (s.gpr .x5 + BitVec.ofNat 64 i) :=
      fun i hi => h.hi _ (by
        have := c.rsrc.out i hi
        have hZ' : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := c.dims.z
        omega) (fun j hj => c.dor i (by rw [← hrl]; exact hi) j (by rw [← c.len]; exact hj))
    exact ⟨fun i hi => by rw [h.keep.rd, h.keep.wr]; exact c.rsrc.rd i hi,
      fun i hi => by show t.mem (s.gpr .x5 + _) = (pcRand s)[i]; rw [hm i hi]; exact c.rsrc.val i hi, c.rsrc.out⟩

/-- `vg_ffdh_parameter_candidate_sieved` ends as the specification says. -/
theorem code_correct (M : Mont) (R : Kernel) (s : State) (h : pcContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) s t s' ∧ abiPreserved s s' ∧ pcContract.post s s' := by
  have c := pctx_of h
  suffices hwp : WP isa (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) s fun s' => abiPreserved s s' ∧ pcPost s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold VG.Impl.Ffdh.AArch64.ParameterCandidate.code
  simp only [seqs]
  refine WP.seq (WP.mono (entry_ok c) fun t₁ he => ?_)
  refine WP.seq (WP.mono (zeros_ok c he) fun t₂ hz => ?_)
  refine WP.seq (WP.mono (lenCheck_ok c he hz) fun t₄ hf => ?_)
  have hrl := pcRand_length s
  have hph := ph_of c hf
  refine WP.ite (!decide ((s.gpr .x1).toNat ≤ (s.gpr .x6).toNat))
    (by rw [eval_zero, hf.x5]; cases decide ((s.gpr .x1).toNat ≤ (s.gpr .x6).toNat) <;> rfl)
    (fun hlt => ?_) (fun hlt => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hlt
    have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := c.dims.z
    have hL : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 := c.len
    refine WP.mono (finNone_ok (up := s.gpr .x2) hph.scr hph.x0 (show 8 * 32 ≤ (stackArg s 0).toNat * 8 by omega_using [hZ])
      hf.args.usedP hph.ou.upw)
      fun t ht => pcEnd_post c hf.zero hf.keep ?_
    have hnone : Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = none := by
      show Spec.Ffdh.sievedParameterCandidate (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32).toNat (pcRand s) = none
      unfold Spec.Ffdh.sievedParameterCandidate
      have hs : (pcRand s).length < ((s.gpr .x3).toNat + 7) / 8 := by rw [hrl]; omega_using [hlt, hL]
      rw [VG.Proof.Ffdh.ParameterCandidate.draw_of_short hs]
      rfl
    rw [hnone]
    exact KEnd.of_fin hph.ou ht
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hlt
    have hL : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 := c.len
    refine WP.mono (main_ok M R hph (by
        show word t₄.mem (s.gpr .x7) _ = BitVec.ofNat 64 (((s.gpr .x3).toNat + 7) / 8)
        rw [hf.args.used, ← hL, ofNat_toNat64])
      (by show ((s.gpr .x3).toNat + 7) / 8 ≤ (pcRand s).length; rw [hrl]; omega_using [hlt, hL]))
      fun t ht => pcEnd_post c hf.zero hf.keep ht

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-! ### `Ffdh.AArch64.ParameterCandidate.CTMain`, which only this module used -/

section

/-! ### `Ffdh.AArch64.ParameterCandidate.CTTest`, which only this module used -/

section

/-! ### `Ffdh.AArch64.ParameterCandidate.CTMont`, which only this module used -/

section

/-!
# An FFDH parameter candidate on AArch64: constant time of the Montgomery setup

`montPrep_ct` and `expSetup_ct'`, for runs that agree on the working space
and the modulus `N` (public here): RSA's pieces (`CTMs.lean`) for a modulus
of `w` words whose top word is not zero, `R² mod N` by `r2_ct`, and
`expSetup` from the registers `lowWord` leaves.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The public data of the setup: the working space and the modulus. -/
structure MQ where
  L : WsP
  N : Nat

/-- Before `montPrep`. -/
def MP0 (q : MQ) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ 4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ wv s.mem q.L.B (slot q.L.w aN) q.L.w = q.N ∧
    q.N % 2 = 1 ∧ 2 ^ (64 * (q.L.w - 1)) ≤ q.N

/-- With `-N⁻¹`. -/
def MPc (q : MQ) (s : State) : Prop :=
  MP0 q s ∧ ((word s.mem q.L.B (slot q.L.w aN)).toNat * (word s.mem q.L.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0

/-- After `-N⁻¹`'s block. -/
def MPa (q : MQ) (s : State) : Prop :=
  MPc q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.L.w ∧ s.gpr .x9 = 1 ∧ s.gpr .x13 = BitVec.ofNat 64 0

/-- With the number 1. -/
def MPb (q : MQ) (s : State) : Prop := MPc q s ∧ wv s.mem q.L.B (slot q.L.w aOne) q.L.w = 1

theorem MPc.frm {q : MQ} {s t : State} (h : MPc q s) {rs : List (Nat × Nat)} (hf : Frm q.L.B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dN : ∀ r ∈ rs, slot q.L.w aN + 8 * q.L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.L.w aN)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv) : MPc q t := by
  obtain ⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩ := h
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have eN := hw.sl (show aN < 16 by decide)
  refine ⟨⟨hw.congr' hf hm k hr, h4, h128, by rw [hf.wv_eq dN (by omega_arith)]; exact hn, hodd, hlo⟩, ?_⟩
  rw [hf.word_eq (d := slot q.L.w aN) (fun r hr => by have := dN r hr; omega_arith) (by omega_arith),
    hf.word_eq (d := 8 * sMinv) dI (by simp only [sMinv] at *; have := hw.h256; omega_arith)]
  exact hinv

theorem MPb.frm {q : MQ} {s t : State} (h : MPb q s) {rs : List (Nat × Nat)} (hf : Frm q.L.B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dN : ∀ r ∈ rs, slot q.L.w aN + 8 * q.L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.L.w aN)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dO : ∀ r ∈ rs, slot q.L.w aOne + 8 * q.L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.L.w aOne) : MPb q t := by
  have hnw := h.1.1.1.scr.nowrap
  have hZ := h.1.1.1.hZ
  have eO := h.1.1.1.sl (show aOne < 16 by decide)
  exact ⟨h.1.frm hf hm k hr dN dI, by rw [hf.wv_eq dO (by omega_arith)]; exact h.2⟩

theorem mpH_ok {q : MQ} {s : State} (h : MP0 q s) :
    WP isa (.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
      movi .x13 0])) s (MPa q) := by
  obtain ⟨hw, h4, h128, hn, hodd, hlo⟩ := h
  have hnw := hw.scr.nowrap
  have hw1 := hw.w1
  have hodd0 : (word s.mem q.L.B (slot q.L.w aN)).toNat % 2 = 1 := by
    have e := wv_add s.mem q.L.B (slot q.L.w aN) 1 (q.L.w - 1)
    rw [show 1 + (q.L.w - 1) = q.L.w by omega_arith, hn] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e
    omega_arith
  refine WP.mono (msHead_ok hw hodd0) fun t ⟨⟨hinv, hm, h12, h9, h13⟩, k⟩ => ?_
  have o₁ : Outside q.L.B (8 * sMinv) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by simp only [sMinv]; omega_arith)
  have f₁ : Frm q.L.B [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside o₁ (List.mem_singleton_self _)
  have hw₁ : word t.mem q.L.B (slot q.L.w aN) = word s.mem q.L.B (slot q.L.w aN) :=
    o₁.word (by simp only [slot, hdrBytes, aN, sMinv]; omega_arith) (by simp only [slot, hdrBytes, aN]; omega_arith)
  refine ⟨⟨⟨hw.congr' f₁ (by msb_mut) k (by decide), h4, h128, ?_, hodd, hlo⟩, by rw [hw₁]; exact hinv⟩, h12, h9,
    h13⟩
  rw [o₁.wv (by simp only [slot, hdrBytes, aN, sMinv]; omega_arith) (by simp only [slot, hdrBytes, aN]; omega_arith)]; exact hn

theorem mpOne_ok {q : MQ} {s : State} (h : MPa q s) : WP isa (setWord aOne) s (MPb q) := by
  obtain ⟨hc, h12, h9, h13⟩ := h
  have hw := hc.1.1
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  obtain ⟨g, hZ8⟩ := hw.good
  refine WP.mono (setWord_ok g.scr g.x0 g.hdr hZ8 h12 (by omega_arith) (o := aOne) (by decide) (i := 0)
    (by omega_arith) h13) fun t ⟨hv, o, k⟩ => ?_
  rw [h9] at hv
  have f : Frm q.L.B [(slot q.L.w aOne, 8 * (q.L.w + 2))] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  exact ⟨hc.frm f (by msb_mut) k (by decide) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl), hv⟩

/-- `r2_ok`'s hypotheses, for the run's `-N⁻¹`. -/
theorem mpb_r2pre {q : MQ} {s : State} (h : MPb q s) :
    R2Pre ⟨⟨q.L.B, q.L.Z, q.L.w, word s.mem q.L.B (8 * sMinv)⟩, q.N⟩ s := by
  obtain ⟨⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩, -⟩ := h
  exact ⟨hw.good, show 2 ≤ q.L.w by omega_arith, show q.L.w < 2 ^ 30 by omega_arith, hn, hinv, hodd, hlo⟩

theorem mpR2_ok (M : Mont) {q : MQ} {s : State} (h : MPb q s) : WP isa (seqs (r2Steps M.mm)) s (MPb q) := by
  obtain ⟨hg, hw2, hw', hn, hinv, hodd, hlo⟩ := mpb_r2pre h
  have hZ := h.1.1.1.hZ
  refine WP.mono (r2_ok M hg.1 hg.2 hw2 hw' hn hinv hodd hlo) fun t ⟨_, _, _, fr, k⟩ =>
    h.frm fr (by msb_mut) k (by decide) (by msb_disj) (by msb_disj) (by msb_disj)

theorem mpY_ok (M : Mont) {q : MQ} {s : State} (h : MPb q s) : WP isa (M.mm aY aR2 aOne) s (MPb q) := by
  obtain ⟨⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩, hone⟩ := h
  obtain ⟨g, hZ8⟩ := hw.good
  have hN1 : 1 < q.N := by
    have : 2 ≤ 2 ^ (64 * (q.L.w - 1)) := by
      rw [show 64 * (q.L.w - 1) = (64 * (q.L.w - 1) - 1) + 1 by omega_arith, Nat.pow_succ]
      have := Nat.two_pow_pos (64 * (q.L.w - 1) - 1); omega_arith
    omega_arith
  refine WP.mono (M.mm_ok g hZ8 hw.w1 (by have := hw.w2; omega_arith) (o := aY) (a := aR2) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hinv (by rw [hone, hn]; exact hN1))
    fun t ⟨_, _, _, ha, k⟩ => ?_
  exact MPb.frm (s := s) ⟨⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩, hone⟩ (Frm.of_arrays ha (rs := [(slot q.L.w aAcc,
    8 * (q.L.w + 2)), (slot q.L.w aTmp, 8 * (q.L.w + 2)), (slot q.L.w aY, 8 * (q.L.w + 2))]) (by simp)) (by msb_mut) k
    (by decide) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)

theorem mpR1_ok {q : MQ} {s : State} (h : MPb q s) : WP isa (copyA aR1 aY) s (MPb q) := by
  have hw := h.1.1.1
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  refine WP.mono (copyA_ok hw (o := aR1) (a := aY) (by decide) (by decide) (by decide)) fun t ⟨_, o, _, _, k⟩ =>
    h.frm (Frm.of_outside o (List.mem_singleton_self _)) (by msb_mut) k (by decide) (by msb_disj) (by msb_disj)
      (by msb_disj)

theorem mpRm_ok {q : MQ} {s : State} (h : MPb q s) :
    WP isa (seqs (subA aRm1 aN aR1)) s fun t => Ws t q.L.B q.L.Z q.L.w := by
  have hw := h.1.1.1
  exact WP.mono (subA_ok hw (o := aRm1) (a := aN) (b := aR1) (by decide) (by decide) (by decide) (.inr (by decide))
    (by decide)) fun t ⟨_, o, _, _, _, k⟩ =>
    hw.congr' (Frm.of_outside o (List.mem_singleton_self _)) (by msb_mut) k (by decide)

theorem mpH_ct : RelCT isa (Two MP0) (.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])) (Two MPa) := by
  have e : ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0] :
      List Instr) = [ldh .x8 (sArr aN)] ++ ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
        movi .x13 0]) := rfl
  rw [e]
  refine blk_pin _ _ [.x0] [.x0, .x8] (fun q r => match r with | .x0 => q.L.B | _ => off q.L.B (slot q.L.w aN))
    (pins_ws' (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w) fun _ _ h => h.1)
    (by taint_decide) (fun q s h => ?_) (by taint_decide)
    fun q s h => by rw [← e]; exact mpH_ok h
  have hw := h.1
  have hnw := hw.scr.nowrap
  have sN := hw.sl (show aN < 16 by decide)
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = off q.L.B (slot q.L.w aN)) (by
    brun [hw.x0, hdr_enc (show sArr aN < 32 by decide), hw.scr.ld (d := 8 * sArr aN) (by simp only [sArr, aN]; omega_arith),
      hw.harr aN (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨h8, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (k.gpr .x0 (by decide)).trans hw.x0
  · exact h8

theorem mpOne_ct : RelCT isa (Two MPa) (setWord aOne) (Two MPb) :=
  two_post (setWord_ct (by decide) (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w) (fun _ => 0)
    (fun _ _ h => ⟨⟨_, h.1.1.1.good⟩, h.2.1, h.2.2.2⟩)
    (by taint_decide) (by taint_decide)) fun _ _ h => mpOne_ok h

theorem mpR2_ct (M : Mont) : RelCT isa (Two MPb) (seqs (r2Steps M.mm)) (Two MPb) := by
  refine two_post ((r2_ct M).mono (fun s₁ s₂ h => two_bind (fun q t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h)
    fun _ _ h => mpR2_ok M h
  have e₁ := mpb_r2pre h₁
  have e₂ := mpb_r2pre h₂
  refine ⟨_, e₁, ?_⟩
  have hm : word t₁.mem q.L.B (8 * sMinv) = word t₂.mem q.L.B (8 * sMinv) := by
    have e : ∀ {t : State}, MPb q t → ((q.N % 2 ^ 64) * (word t.mem q.L.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 :=
      fun {t} h => by
        obtain ⟨⟨⟨hw, h4, _, hn, _, _⟩, hinv⟩, _⟩ := h
        rwa [← wv_mod64 _ _ _ (show 1 ≤ q.L.w by omega_arith), hn] at hinv
    exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.1.1.2.2.2.2.1) (e h₁) (e h₂)
  rw [hm]; exact e₂

theorem mpY_ct (M : Mont) : RelCT isa (Two MPb) (M.mm aY aR2 aOne) (Two MPb) :=
  two_post (two_map (fun q : MQ => q.L) (fun _ _ h => ⟨_, h.1.1.1.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))) fun _ _ h => mpY_ok M h

theorem mpR1_ct : RelCT isa (Two MPb) (copyA aR1 aY) (Two MPb) := by
  have e : copyA aR1 aY = .seq (.block (ws ++ (base aY .x16 ++ base aR1 .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w) (fun _ _ h => h.1.1.1)
    (by taint_decide) fun _ _ h => by rw [← e]; exact mpR1_ok h

theorem montPrep_eq (mul : Nat → Nat → Nat → Prog isa) : montPrep mul =
    ([.block (([ldh .x8 (sArr aN), ld .x3 .x8] : List Instr) ++ minv ++ ([sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
      movi .x13 0] : List Instr)), setWord aOne] : List (Prog isa)) ++ (r2Steps mul ++
      (([mul aY aR2 aOne, copyA aR1 aY] : List (Prog isa)) ++ subA aRm1 aN aR1)) := by
  simp only [montPrep, List.append_assoc]

/-- `montPrep` leaks the same in runs that agree on the working space and the
modulus. -/
theorem montPrep_ct (M : Mont) : RelCT isa (Two MP0) (seqs (montPrep M.mm)) fun _ _ => True := by
  rw [montPrep_eq]
  refine ct_app' (by simp) (by simp [r2Steps]) (RelCT.seq mpH_ct mpOne_ct)
    (ct_app' (by simp [r2Steps]) (by simp) (mpR2_ct M)
      (ct_app' (by simp) (by simp [subA]) (RelCT.seq (mpY_ct M) mpR1_ct) ?_))
  rw [subA_eq']
  exact (ws_ct (Φ := MPb) (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w)
    (Ψ := fun _ _ => True) (fun _ _ h => h.1.1.1) (by taint_decide)
    fun _ _ h => by rw [← subA_eq']; exact WP.mono (mpRm_ok h) fun _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial

/-! ## `expSetup` -/

/-- Before `expSetup`. -/
def EQ (q : MQ) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ wv s.mem q.L.B (slot q.L.w aN) q.L.w = q.N ∧ q.N % 2 = 1 ∧ 1 < q.N

/-- `lowWord`'s registers. -/
def lwVal' (q : MQ) : Reg → BitVec 64
  | .x0 => q.L.B
  | .x12 => BitVec.ofNat 64 q.L.w
  | _ => BitVec.ofNat 64 (8 * (q.L.w + 2))

/-- `expSetup` leaks the same in runs that agree on the working space and the
modulus. -/
theorem expSetup_ct' : RelCT isa (Two EQ) (seqs expSetup) fun _ _ => True := by
  rw [expSetup_eq]
  refine ct_app' (by simp [lowWord]) (by simp) (Ψ := fun q t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = lwVal' q r)
    ?_ ((two_taint [.x0, .x12, .x11] (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm)
      (by taint_decide)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  have e : seqs lowWord = Code.seq _ _ := rfl
  rw [e]
  refine ws_ct (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w)
    (fun _ _ h => h.1) (by taint_decide) fun q s ⟨hw, hn, hodd, h1⟩ => ?_
  refine (?_ : WP isa (seqs lowWord) s _)
  exact WP.mono (lowWord_ok hw hn hodd h1) fun t ⟨_, _, _, _, h11, h12, k⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans hw.x0
    · exact h12
    · exact h11

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-! ### `Ffdh.AArch64.ParameterCandidate.CTMr`, which only this module used -/

section

/-! ### `Ffdh.AArch64.ParameterCandidate.CTDraw`, which only this module used -/

section

/-!
# An FFDH parameter candidate on AArch64: constant time of a draw

Every value of the candidate is public, so two runs with the same public
data follow the same path: each piece is checked by the taint analysis from
registers that correctness pins (`round_ct`, `drawHead_ct`, `draw_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-! ## A round -/

/-- The public data of a round: the working space, `N` and the witness. -/
structure RQ where
  L : WsP
  N : Nat
  a : Nat

/-- Before a round. -/
def RA (q : RQ) (s : State) : Prop :=
  4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ slot q.L.w aE + 8 * (q.L.w + 2) ≤ q.L.Z ∧ q.N % 2 = 1 ∧ 3 ≤ q.N ∧ q.a < q.N ∧
    (∃ bm, MrCtx s q.L.B q.L.Z q.L.w q.N bm) ∧ ECtx s.mem q.L.B q.L.w q.N ∧
    wv s.mem q.L.B (slot q.L.w aR2) q.L.w = 2 ^ (64 * q.L.w) * 2 ^ (64 * q.L.w) % q.N ∧
    wv s.mem q.L.B (slot q.L.w aX) q.L.w = q.a

/-- Before the kernel. -/
def RB (q : RQ) (s : State) : Prop :=
  4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ slot q.L.w aE + 8 * (q.L.w + 2) ≤ q.L.Z ∧ q.N % 2 = 1 ∧ 3 ≤ q.N ∧
    (∃ bm, MrCtx s q.L.B q.L.Z q.L.w q.N bm) ∧ ECtx s.mem q.L.B q.L.w q.N ∧
    wv s.mem q.L.B (slot q.L.w aXm) q.L.w = q.a % q.N * 2 ^ (64 * q.L.w) % q.N

/-- After the kernel. -/
def RF (q : RQ) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ word s.mem q.L.B (8 * kFlag) = mask (Proof.MillerRabin.Round.round q.N q.a)

theorem roundMm_ok (M : Mont) {q : RQ} {s : State} (h : RA q s) : WP isa (M.mm aXm aX aR2) s (RB q) := by
  obtain ⟨h4, h128, hEZ, hodd, hc3, ha, ⟨bm, hc⟩, he, hR2, hx⟩ := h
  have hn := hc.ws.scr.nowrap
  have hw' : q.L.w < 2 ^ 31 := by omega_arith
  have hRc : Nat.Coprime (2 ^ (64 * q.L.w)) q.N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < q.N := by omega_arith
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hR2, hc.n]; exact Nat.mod_lt _ hc0)) fun t ⟨_, hlt, hy, ha₁, k⟩ => ?_
  rw [hc.n] at hlt hy
  rw [hx, hR2] at hy
  have hXm : wv t.mem q.L.B (slot q.L.w aXm) q.L.w = q.a % q.N * 2 ^ (64 * q.L.w) % q.N := by
    rw [← Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt ha]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₁ : Frm q.L.B [(slot q.L.w aAcc, 8 * (q.L.w + 2)), (slot q.L.w aTmp, 8 * (q.L.w + 2)),
      (slot q.L.w aXm, 8 * (q.L.w + 2))] s.mem t.mem := Frm.of_arrays ha₁ (by simp)
  refine ⟨h4, h128, hEZ, hodd, hc3, ⟨bm, hc.of_frm f₁ (by kmut) k (by decide)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
    he.of_frm f₁ (fun r hr => Or.inr (rdRanges_lt q.L.w r (by
      simp only [rdRanges]; exact List.mem_append_left _ (List.mem_append_left _ hr)))) (by omega_arith), hXm⟩

theorem roundMm_ct (M : Mont) : RelCT isa (Two RA) (M.mm aXm aX aR2) (Two RB) :=
  two_post (two_map (fun q : RQ => q.L) (fun _ _ ⟨_, _, _, _, _, _, ⟨_, hc⟩, _⟩ => ⟨_, hc.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) fun _ _ h => roundMm_ok M h

theorem roundKernel_ct (R : Kernel) : RelCT isa (Two RB) (seqs R.run) (Two RF) :=
  two_post (two_map (fun q : RQ => q.L)
    (fun q _ ⟨h4, h128, hEZ, hodd, hc3, ⟨bm, hc⟩, he, hx⟩ => ⟨h4, h128, hEZ, q.N, bm, q.a, hc, he, hodd, hc3, hx⟩)
    R.ct) fun _ _ ⟨h4, h128, hEZ, hodd, hc3, ⟨_, hc⟩, he, hx⟩ =>
      WP.mono (R.ok hc he h4 h128 hEZ hodd hc3 hx) fun _ ⟨⟨_, hct⟩, _, hf, _⟩ => ⟨hct.ws, hf⟩

/-- The end of a round. -/
theorem roundEnd_ct : RelCT isa (Two RF) (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 2, sth .x3 kStat])
        (.block [ldh .x3 fIdx, ldh .x4 fChecks, .addImm .x .x3 .x3 1, .subs .x .x5 .x3 .x4, movi .x6 4, movi .x7 1,
          .csel .x .x5 .x7 .x6, sth .x3 fIdx, sth .x5 kStat])]) fun _ _ => True := by
  have pw : ∀ {Φ : RQ → State → Prop}, (∀ q s, Φ q s → Ws s q.L.B q.L.Z q.L.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun q : RQ => q.L.B) (fun q : RQ => q.L.Z) (fun q : RQ => q.L.w) h
  refine RelCT.seq (two_piece (Ψ := fun q t => Ws t q.L.B q.L.Z q.L.w ∧
      isa.eval (.zero .x .x3) t = some (!Proof.MillerRabin.Round.round q.N q.a)) [.x0] (pw fun _ _ h => h.1)
      (by taint_decide) fun q s ⟨hw, hF⟩ => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide))
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide)))
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask (Proof.MillerRabin.Round.round q.N q.a) ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show kFlag < 32 by decide),
      hw.scr.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega_arith), hF])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · exact hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)
  · rw [eval_zero, h3, mask_beq]

/-- A round leaks the same in runs with the same public data. -/
theorem round_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two RA) (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.round M.mm R.run)) fun _ _ => True := by
  simp only [VG.Impl.Ffdh.AArch64.ParameterCandidate.round]
  refine ct_app' (by simp) (by simp) ?_ roundEnd_ct
  refine ct_app' (a := [M.mm aXm aX aR2]) (by simp) R.nonempty ?_ (roundKernel_ct R)
  rw [seqs_one]; exact roundMm_ct M

/-! ## A draw -/

/-- The public data of a draw: the candidate's, the modulus's, and the
octets read before it. -/
structure DD where
  p : PP
  w : Nat
  N : Nat
  mb : Nat
  K : Nat
  u : Nat

/-- Before a draw. -/
def DA (d : DD) (s : State) : Prop :=
  MrDims d.p d.w d.N d.mb d.K ∧ MrFix d.p d.w d.N d.mb d.K s ∧
    word s.mem d.p.B (8 * kUsed) = BitVec.ofNat 64 d.u ∧ (∃ i, word s.mem d.p.B (8 * fIdx) = BitVec.ofNat 64 i ∧
    i < 2 ^ 62) ∧ d.u + mLen d.mb ≤ d.p.r.length

/-- The working space of a draw. -/
def DW (d : DD) (s : State) : Prop := Ws s d.p.B d.p.Z d.w

/-- Before the cut. -/
def DC (d : DD) (s : State) : Prop :=
  Ws s d.p.B d.p.Z d.w ∧ mK d.mb ≤ 64 ∧ word s.mem d.p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK d.mb - 1)

/-- Before the octets' block. -/
def DL (d : DD) (s : State) : Prop :=
  Ws s d.p.B d.p.Z d.w ∧ word s.mem d.p.B (8 * kRand) = d.p.rp ∧
    word s.mem d.p.B (8 * kUsed) = BitVec.ofNat 64 d.u ∧ word s.mem d.p.B (8 * kLen) = BitVec.ofNat 64 (mLen d.mb)

/-- The registers `loadBE` needs. -/
def dbVal (B rp : Addr) (w u len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => off B (slot w aX)
  | .x1 => rp + BitVec.ofNat 64 u
  | _ => BitVec.ofNat 64 len

/-- The block before `loadBE`. -/
theorem drawBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rp : Addr} {u len : Nat}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3,
      ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed])) s fun t =>
      ∀ r ∈ [Reg.x0, .x8, .x1, .x2], t.gpr r = dbVal B rp w u len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok aX .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x3, .x2] (Q := fun t => t.gpr .x1 = rp + BitVec.ofNat 64 u ∧
        t.gpr .x2 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_arith)
          brun [h0₃, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
            hdr_enc (show kLen < 32 by decide), m₃, m₂, hl₃ kRand (by decide), hl₃ kUsed (by decide),
            hl₃ kLen (by decide), hs₃.st (d := 8 * kUsed) (by have := h.h256; simp only [kUsed, sFn]; omega_arith),
            hR, hU, hK])
        (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h1, h2⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h2))

theorem zeroAD_ct : RelCT isa (Two DL) (zeroA aX) (Two DL) := by
  have e : zeroA aX = .seq (.block (ws ++ (base aX .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  rw [e]
  refine ws_ct (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) (fun _ _ h => h.1)
    (by taint_decide) fun d s h => ?_
  rw [← e]
  obtain ⟨hw, hR, hU, hK⟩ := h
  have hn := hw.scr.nowrap
  refine WP.mono (zeroA_ok hw (show aX < 16 by decide)) fun t ⟨_, o, _, _, _, k⟩ => ?_
  have f : Frm d.p.B [(slot d.w aX, 8 * (d.w + 2))] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  have hh : ∀ i < 32, word t.mem d.p.B (8 * i) = word s.mem d.p.B (8 * i) := fun i hi =>
    f.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot d.w aX hi)) (by omega_arith)
  exact ⟨hw.congr' f (by msb_mut) k (by decide), (hh _ (by decide)).trans hR, (hh _ (by decide)).trans hU,
    (hh _ (by decide)).trans hK⟩

/-- The octets into `aX`. -/
theorem drawLoad_ct : RelCT isa (Two DL) (seqs [zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand,
    ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE])
    fun _ _ => True :=
  RelCT.seq zeroAD_ct (RelCT.seq (two_piece (Ψ := fun d t => ∀ r ∈ [Reg.x0, .x8, .x1, .x2],
      t.gpr r = dbVal d.p.B d.p.rp d.w d.u (mLen d.mb) r) [.x0]
      (pins_ws' (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) fun _ _ h => h.1)
      (by taint_decide)
      fun _ _ ⟨hw, hR, hU, hK⟩ => drawBlk_ok hw hR hU hK)
    (two_taint _ (pins_of _ (fun d => dbVal d.p.B d.p.rp d.w d.u (mLen d.mb)) fun _ _ h => h) (by taint_decide)))

/-- The range's pieces, from the working space. -/
theorem drawRange_ct : RelCT isa (Two DW)
    (seqs [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) fun _ _ => True := by
  refine two_map (Φ' := fun (q : WPub) t => Ws t q.L.B q.L.Z q.L.w)
    (fun d : DD => (⟨⟨d.p.B, d.p.Z, d.w⟩, d.p.rp, d.u⟩ : WPub)) (fun _ _ h => h) ?_
  have e : ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa)) =
      [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
        countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]] ++
      ([.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop] ++
      [.block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) := rfl
  rw [e]
  exact ct_app' (by simp) (by simp) witLow_ct (ct_app' (by simp) (by simp) witCmp_ct
    (two_taint _ (pins_of _ (fun p : WPub => wsVal p.L.B p.L.w) fun _ _ h => h) (by taint_decide)))

theorem drawHead_eq : drawHead = ([zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand,
    ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE] : List (Prog isa)) ++
    (([.block (ws ++ base aX .x16 ++ ([.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8, ldh .x4 fTop,
      ld .x3 .x5, .logic .and .x .x3 .x3 .x4, st .x3 .x5] : List Instr))] : List (Prog isa)) ++
    ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa))) := rfl

/-- After `drawHead`. -/
def DM (d : DD) (s : State) : Prop :=
  MrDims d.p d.w d.N d.mb d.K ∧ ∃ i s₀, DrawMid d.p d.w d.N d.mb d.K i d.u s₀ s ∧ i < 2 ^ 62

/-- `drawHead` leaks the same in runs with the same public data. -/
theorem drawHead_ct : RelCT isa (Two DA) (seqs drawHead) (Two DM) := by
  refine two_post ?_ fun d s ⟨hd, h, hU, ⟨i, hI, hi⟩, hroom⟩ =>
    WP.mono (drawHead_ok hd h hU hI hroom) fun t ht => ⟨hd, i, s, ht, hi⟩
  rw [drawHead_eq]
  refine ct_app' (by simp) (by simp) (Ψ := DC) (two_post (two_map (Φ' := DL) id (fun d s ⟨_, h, hU, _⟩ =>
    ⟨h.st.ws, h.st.args.rand, hU, h.len⟩) drawLoad_ct) fun d s ⟨hd, h, hU, _, hroom⟩ => ?_) ?_
  · have hmb1 := hd.mb1
    have hw := hd.hw
    have hn := h.st.ws.scr.nowrap
    exact WP.mono (drawLoad_ok h.st.ws h.st.args.rand hU h.len (by simp only [mLen]; omega_arith)
      (by rw [hw]; simp only [mLen, mW]; omega_arith) (src_take (src_drop h.st.src d.u) (mLen d.mb))
      (by simp only [List.length_take, List.length_drop]; omega_arith)) fun t ⟨_, _, f, hw', _⟩ =>
        ⟨hw', by simp only [mK, mW]; omega_arith, by
          rw [f.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fTop]; omega_arith)]; exact h.top⟩
  refine ct_app' (by simp) (by simp) (Ψ := DW) ?_ drawRange_ct
  rw [seqs_one]
  exact ws_block_ct (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) (fun _ _ h => h.1)
    (by taint_decide) fun d s ⟨hw, hk, hT⟩ => WP.mono (drawCut_ok hw hk hT) fun t ⟨_, f, k⟩ =>
      hw.congr' f (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

theorem mask_decide_beq (P : Prop) [Decidable P] : (mask (decide P) == 0) = !decide P := by
  cases decide P <;> decide

/-- A draw leaks the same in runs with the same public data. -/
theorem draw_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two DA) (seqs (draw M.mm R.run)) fun _ _ => True := by
  rw [draw_eq]
  refine ct_app' (by simp [drawHead, draw]) (by simp) drawHead_ct ?_
  rw [seqs_one]
  have hz : ∀ d s, DM d s → isa.eval (.zero .x .x9) s =
      some (!decide (2 ≤ wA d.mb d.p.r d.u ∧ wA d.mb d.p.r d.u < d.N - 1)) := fun d s ⟨_, i, s₀, h, _⟩ => by
    rw [eval_zero, h.x9, mask_decide_beq]
  refine two_ite (fun d s₁ s₂ h₁ h₂ => by rw [hz d s₁ h₁, hz d s₂ h₂]) ?_ ?_
  · exact two_taint [.x0] (pins_ws' (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w)
      fun _ _ ⟨⟨_, _, _, h, _⟩, _⟩ => h.fix.st.ws) (by taint_decide)
  · refine two_map (Φ' := RA) (fun d : DD => (⟨⟨d.p.B, d.p.Z, d.w⟩, d.N, wA d.mb d.p.r d.u⟩ : RQ)) ?_ (round_ct M R)
    rintro d s ⟨hm, hb⟩
    have hz' := hz d s hm
    obtain ⟨hd, i, s₀, h, _⟩ := hm
    rw [hz'] at hb
    have hacc : 2 ≤ wA d.mb d.p.r d.u ∧ wA d.mb d.p.r d.u < d.N - 1 := by
      simpa using hb
    have hw := hd.hw
    have hmb1 := hd.mb1
    have hmb2 := hd.mb2
    exact ⟨by rw [hw]; simp only [mW]; omega_arith, by rw [hw]; simp only [mW]; omega_arith, hd.eZ, hd.odd, hd.n3,
      show wA d.mb d.p.r d.u < d.N by omega_arith, h.fix.ctx, h.fix.ex, h.fix.r2, h.ax⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on AArch64: constant time of Miller–Rabin

`millerRabin_ct`: the loop runs `mrIters` times, which the public data
fixes, the `j`-th iteration from `u₀ + j ⌈mb / 8⌉` octets read.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The public data of the witnesses of a modulus: the candidate's, the
modulus's, and the octets read before them. -/
structure TQ where
  p : PP
  w : Nat
  N : Nat
  mb : Nat
  K : Nat
  u : Nat

/-- The result. -/
abbrev TQ.res (q : TQ) : Option (Bool × List Byte) := checkWitnesses q.N q.K (q.p.r.drop q.u)

/-- The octets read before iteration `j`. -/
abbrev TQ.uj (q : TQ) (j : Nat) : Nat := q.u + j * mLen q.mb

/-- The iterations. -/
abbrev TQ.n (q : TQ) : Nat := mrIters q.N q.K q.mb q.p.r (q.p.r.length + 1) 0 q.u

/-- At the head of iteration `j`. -/
def TL (q : TQ) (j : Nat) (s : State) : Prop :=
  MrDims q.p q.w q.N q.mb q.K ∧ ∃ s₀ i, MrSt q.p q.w q.N q.mb q.K s₀ q.res i (q.uj j) s ∧
    mrIters q.N q.K q.mb q.p.r (q.p.r.length + 1 - j) i (q.uj j) = q.n - j

/-- After the loop. -/
def TE (q : TQ) (s : State) : Prop := MrDims q.p q.w q.N q.mb q.K ∧ ∃ s₀, MrEnd q.p q.w q.N q.mb q.K s₀ q.res s

theorem MrSt.same {p : PP} {w N mb K : Nat} {s₀ : State} {res : Option (Bool × List Byte)} {i u : Nat}
    {s t : State} (h : MrSt p w N mb K s₀ res i u s) (hEZ : slot w aE + 8 * (w + 2) ≤ p.Z) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : ∀ r ∈ regs, r ∈ mmRegs) : MrSt p w N mb K s₀ res i u t :=
  ⟨h.fix.same hEZ hm k (fun h' => by have := hr _ h'; simp [mmRegs] at this), by rw [hm]; exact h.used,
    by rw [hm]; exact h.idx, h.ul, h.ik, h.rest, by rw [hm]; exact h.isc, (h.keep.trans k).mono fun r hr' => by
      rcases List.mem_append.mp hr' with h' | h'
      · exact h'
      · exact hr r h'⟩

theorem tl_ws {q : TQ} {j : Nat} {s : State} (h : TL q j s) : Ws s q.p.B q.p.Z q.w := by
  obtain ⟨-, s₀, i, hs, -⟩ := h
  exact hs.fix.st.ws

/-- Before the branch on `rand`'s length. -/
def TR (a : TQ × Nat) (s : State) : Prop :=
  TL a.1 a.2 s ∧ isa.eval (.zero .x .x5) s = some (decide (a.1.p.r.length < a.1.uj a.2 + mLen a.1.mb))

/-- The short end. -/
theorem shortEnd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block [movi .x3 0, sth .x3 kStat]) s fun t => Ws t B Z w := by
  have hs := h.scr
  have h256 := h.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), hs.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith)]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have ft : Frm B [(8 * kStat, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  exact h.congr' ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide)) k (by decide)

/-- An iteration leaks the same in runs with the same public data. -/
theorem mrBody_ct (M : Mont) (R : Kernel) : RelCT isa (Two fun (a : TQ × Nat) s => a.2 < a.1.n ∧ TL a.1 a.2 s)
    (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (draw M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) fun _ _ => True := by
  have pw : ∀ {Φ : TQ × Nat → State → Prop}, (∀ a s, Φ a s → Ws s a.1.p.B a.1.p.Z a.1.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun a : TQ × Nat => a.1.p.B) (fun a : TQ × Nat => a.1.p.Z) (fun a : TQ × Nat => a.1.w) h
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := TR) [.x0] (pw fun _ _ h => tl_ws h.2) (by taint_decide) ?_)
    (RelCT.seq (R := Two fun (a : TQ × Nat) t => Ws t a.1.p.B a.1.p.Z a.1.w)
      (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
        (two_piece [.x0] (pw fun _ _ h => tl_ws h.1.1) (by taint_decide) fun _ _ h => shortEnd_ok (tl_ws h.1.1))
        (two_post (two_map (Φ' := DA) (fun a : TQ × Nat =>
            (⟨a.1.p, a.1.w, a.1.N, a.1.mb, a.1.K, a.1.uj a.2⟩ : DD)) ?_ (draw_ct M R)) ?_))
      (two_taint [.x0] (pw fun _ _ h => h) (by taint_decide)))
  · rintro ⟨q, j⟩ s ⟨hj, hd, s₀, i, hs, hit⟩
    have hEZ := hd.eZ
    have hmb2 : q.mb ≤ 8192 := hd.mb2
    exact WP.mono (roomHead_ok (len := mLen q.mb) hs.fix.st.ws (by simp only [mLen]; omega_arith)
      hs.fix.st.dims.rl hs.ul hs.fix.len hs.fix.st.args.rlen hs.used)
      fun t ⟨hz, hm, k⟩ => ⟨⟨hd, s₀, i, hs.same hEZ hm k (by decide), hit⟩, hz⟩
  · rintro ⟨q, j⟩ s ⟨⟨⟨hd, s₀, i, hs, hit⟩, hz⟩, hb⟩
    have hb' : ¬ q.p.r.length < q.uj j + mLen q.mb := by
      intro h'; rw [hz] at hb; simp only [h', decide_true, Option.some.injEq] at hb; cases hb
    have hK : q.K < 2 ^ 62 := hd.k
    have hik : i < q.K := hs.ik
    exact ⟨hd, hs.fix, hs.used, ⟨i, hs.idx, (by omega_arith : i < 2 ^ 62)⟩,
      (by omega_arith : q.uj j + mLen q.mb ≤ q.p.r.length)⟩
  · rintro ⟨q, j⟩ s ⟨⟨⟨hd, s₀, i, hs, hit⟩, hz⟩, hb⟩
    have hb' : ¬ q.p.r.length < q.uj j + mLen q.mb := by
      intro h'; rw [hz] at hb; simp only [h', decide_true, Option.some.injEq] at hb; cases hb
    have hK : q.K < 2 ^ 62 := hd.k
    have hik : i < q.K := hs.ik
    exact WP.mono (draw_ok (i := i) (u := q.uj j) M R hd hs.fix hs.used hs.idx (by omega_arith : i < 2 ^ 62)
      (by omega_arith : q.uj j + mLen q.mb ≤ q.p.r.length))
      fun t ⟨hf, _⟩ => hf.st.ws

theorem mrIters_pos (N K mb : Nat) (r : List Byte) (f i u : Nat) : 1 ≤ mrIters N K mb r f i u := by
  cases f with
  | zero => simp only [mrIters]; omega_arith
  | succ f => simp only [mrIters]; split <;> (try split) <;> (try split) <;> omega_arith

/-- The loop leaks the same in runs with the same public data. -/
theorem mrLoop_ct (M : Mont) (R : Kernel) : RelCT isa (Two fun (q : TQ) s => 0 < q.n ∧ TL q 0 s)
    (.loop (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (draw M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) (.zero .x .x3)) (Two TE) := by
  refine two_loop (Φ := TL) TQ.n (mrBody_ct M R) ?_
  rintro q j s hj ⟨hd, s₀, i, hs, hit⟩
  have hul : q.u + j * mLen q.mb ≤ q.p.r.length := hs.ul
  have hl1 : 1 ≤ mLen q.mb := by have : 511 ≤ q.mb := hd.mb1; simp only [mLen]; omega_arith
  have hjl : j ≤ q.p.r.length := by
    have : j * 1 ≤ j * mLen q.mb := Nat.mul_le_mul_left _ hl1
    omega_arith
  obtain ⟨f, hf⟩ : ∃ f, q.p.r.length + 1 - j = f + 1 := ⟨q.p.r.length - j, by omega_arith⟩
  rw [hf] at hit
  refine WP.mono (mrIter_ok M R hd hs) fun t ht => ?_
  rcases ht with ⟨he, hend, h1⟩ | ⟨he, i', hs', hstep⟩
  · rw [h1 f] at hit
    have hn1 : ¬ j + 1 < q.n := by omega_arith
    refine ⟨by rw [he]; exact congrArg some (decide_eq_false hn1).symm, fun h => absurd h hn1,
      fun _ => ⟨hd, s₀, hend⟩⟩
  · rw [hstep f] at hit
    have hpos := mrIters_pos q.N q.K q.mb q.p.r f i' (q.uj j + mLen q.mb)
    have hn1 : j + 1 < q.n := by omega_arith
    refine ⟨by rw [he]; exact congrArg some (decide_eq_true hn1).symm, fun _ => ?_,
      fun h => absurd h (by omega_arith)⟩
    have hu : q.uj j + mLen q.mb = q.uj (j + 1) := by simp only [TQ.uj, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [hu] at hs'
    refine ⟨hd, s₀, i', hs', ?_⟩
    rw [show q.p.r.length + 1 - (j + 1) = f by omega_arith, ← hu]
    omega_arith

/-- Before `millerRabin`. -/
def TP (q : TQ) (s : State) : Prop :=
  MrDims q.p q.w q.N q.mb q.K ∧ MrFix q.p q.w q.N q.mb q.K s ∧
    word s.mem q.p.B (8 * kUsed) = BitVec.ofNat 64 q.u ∧ q.u ≤ q.p.r.length ∧ 1 ≤ q.K

/-- `millerRabin` leaks the same in runs with the same public data. -/
theorem millerRabin_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two TP) (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run)) (Two TE) := by
  unfold VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin
  simp only [seqs]
  refine RelCT.seq (two_piece [.x0] (pins_ws' (fun q : TQ => q.p.B) (fun q : TQ => q.p.Z) (fun q : TQ => q.w)
    fun _ _ h => h.2.1.st.ws) (by taint_decide) ?_) (mrLoop_ct M R)
  rintro q s ⟨hd, h, hU, hul, hK1⟩
  have hEZ := hd.eZ
  have hs := h.st.ws.scr
  have h256 := h.st.ws.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off q.p.B (8 * fIdx)) (BitVec.ofNat 64 0))
    (by
      brun [h.st.ws.x0, hdr_enc (show fIdx < 32 by decide), hs.st (d := 8 * fIdx) (by simp only [fIdx]; omega_arith)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have ft : Frm q.p.B [(8 * fIdx, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have ht : MrFix q.p q.w q.N q.mb q.K t := h.of_frm hEZ ft (by kmut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fIdx]; omega_arith)
    k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
  have hst : MrSt q.p q.w q.N q.mb q.K s q.res 0 (q.uj 0) t :=
    ⟨ht, by
      rw [ft.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_arith)]
      simpa only [TQ.uj, Nat.zero_mul, Nat.add_zero] using hU,
      by rw [hm, word_writeW_self], by simpa only [TQ.uj, Nat.zero_mul, Nat.add_zero] using hul, by omega_arith,
      by simp only [TQ.res, TQ.uj, Nat.sub_zero, Nat.zero_mul, Nat.add_zero],
      InScr.of_frm ft fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fIdx]; omega_arith, k.mono (by decide)⟩
  have hn : 0 < q.n := by
    simp only [TQ.n]
    cases q.p.r.length + 1 with
    | zero => simp only [mrIters]; omega_arith
    | succ f => simp only [mrIters]; split <;> (try split) <;> (try split) <;> omega_arith
  exact ⟨hn, hd, s, 0, hst, by simp only [TQ.uj, Nat.sub_zero, Nat.zero_mul, Nat.add_zero]⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on AArch64: constant time of a test

The working space for a modulus (`phase_ct`), `p` loaded again
(`shapeP_ct`), the Montgomery setup, the exponent and the witnesses
(`testTail_ct`), and the results (`pResult_ct`, `qResult_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-! ## The working space -/

theorem phase_ct' (q : Bool) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (phaseHead q ++ Keys.head ++ [movi .x9 0])) hc).isSome = true) :
    RelCT isa (Two PH) (seqs (phase q)) fun _ _ => True := by
  have e : seqs (phase q) = .seq (.block (phaseHead q ++ Keys.head ++ [movi .x9 0]))
      (.seq (countLoop .x6 [.add .x .x9 .x9 .x9, .addImm .x .x9 .x9 1]) (.block [sth .x9 fTop])) := rfl
  rw [e]
  refine (pin_ct (Ψ := fun _ _ => True) [.x0] [.x0, .x6, .x9] (fun p r => match r with
      | .x0 => p.B | .x6 => BitVec.ofNat 64 (mK (p.mb q)) | _ => 0)
    (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.x0, h₂.x0])
    ht (fun p s h => phaseBlk_ok h q) (by taint_decide) fun p s h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rw [← e]
  exact WP.mono (phase_ok h q) fun _ _ => trivial

/-- `phase q` leaks the same in runs with the same public data. -/
theorem phase_ct (q : Bool) : RelCT isa (Two PH) (seqs (phase q)) fun _ _ => True := by
  cases q
  · exact phase_ct' false (by taint_decide)
  · exact phase_ct' true (by taint_decide)

/-- Before `shapeP`. -/
def SP (p : PP) (s : State) : Prop :=
  PSt p (mW p.bits) s ∧ word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.L ∧ p.L ≤ p.r.length

/-- `shapeP` leaks the same in runs with the same public data. -/
theorem shapeP_ct : RelCT isa (Two SP) (seqs shapeP) fun _ _ => True := by
  unfold shapeP
  refine ct_app' (by simp [loadA]) (by simp) (Ψ := fun p t => Ws t p.B p.Z (mW p.bits))
    (two_post (loadA_ct0 (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits) (j := aN)
      (sPtr := kRand) (sLen := kLen) (by decide) (by decide) (by decide) (fun p => p.rp) (fun p => p.L)
      (fun p s h => ⟨h.1.ws, h.1.args.rand, h.2.1⟩) (by taint_decide) (by taint_decide) (by taint_decide))
      fun p s ⟨h, hK, hr⟩ => ?_) ?_
  · have hb1 := h.dims.b1
    have hb2 := h.dims.b2
    exact WP.mono (loadA_ok h.ws (j := aN) (sPtr := kRand) (sLen := kLen) (len := p.L) (bs := p.r.take p.L)
      (by decide) (by decide) (by decide) h.args.rand hK (src_take h.src p.L) (by rw [List.length_take]; omega_using [hr])
      (by simp only [PP.L]; omega_using [hb1]) (by simp only [PP.L, mW]; omega_using [])) fun t ⟨_, o, _, _, k⟩ =>
        h.ws.congr' (Frm.of_outside o (List.mem_singleton_self _))
          (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)
  · rw [seqs_one]
    exact (ws_block_ct0 (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits) (fun _ _ h => h)
      (by taint_decide))

/-! ## The test's tail -/

/-- The public data of a test: the candidate's, the modulus's bits, the
modulus, the octets read before it and the witnesses needed. -/
structure TD where
  p : PP
  mb : Nat
  N : Nat
  u : Nat
  K : Nat

/-- The witnesses' public data of a test. -/
abbrev TD.tq (d : TD) : TQ := ⟨d.p, mW d.mb, d.N, d.mb, d.K, d.u⟩

/-- The setup's public data of a test. -/
abbrev TD.mq (d : TD) : MQ := ⟨⟨d.p.B, d.p.Z, mW d.mb⟩, d.N⟩

theorem tt_mp0 {d : TD} {s : State} (h : TT d.p d.mb d.N d.u d.K s) : MP0 d.mq s := by
  have hmb1 := h.mb1
  have hmb2 := h.mb2
  exact ⟨h.st.ws, by simp only [mW]; omega_using [hmb1], by simp only [mW]; omega_using [hmb2], h.n, h.odd,
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by simp only [mW]; omega_using [])) h.lo⟩

/-- The Montgomery setup, the exponent and the witnesses. -/
theorem testTail_ct (M : Mont) (R : Kernel) : RelCT isa (Two fun (d : TD) s => TT d.p d.mb d.N d.u d.K s)
    (seqs (montPrep M.mm ++ expSetup ++ VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run))
    (Two TE) := by
  refine ct_app' (by simp [montPrep]) (by simp [VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin])
    (Ψ := fun d s => TP d.tq s) (two_post (ct_app' (by simp [montPrep]) (by simp [expSetup, lowWord])
      (Ψ := fun d s => EQ d.mq s)
      (two_post (two_map TD.mq (fun _ _ h => tt_mp0 h) (montPrep_ct M)) fun d s h => ?_)
      (two_map TD.mq (fun _ _ h => h) expSetup_ct')) fun d s h => ?_)
    (two_map TD.tq (fun _ _ h => h) (millerRabin_ct M R))
  · have hN3 := h.dims.n3
    exact WP.mono (montPrep_ok M h.st.ws (by have := h.mb1; simp only [mW]; omega_using [this]) h.n h.odd (tt_mp0 h).2.2.2.2.2)
      fun t ⟨hw, _, hn, _⟩ => ⟨hw, hn, h.odd, show 1 < d.N by omega_using [hN3]⟩
  · exact WP.mono (testPre_ok M h) fun t ⟨fix, hU, _⟩ => ⟨h.dims, fix, hU, h.ul, h.k1⟩

/-! ## The results -/

/-- The public data of a result: the working space, `out` and `used`, and
the status. -/
structure FQ where
  B : Addr
  Z : Nat
  w : Nat
  op : Addr
  up : Addr
  L : Nat
  st : Nat

/-- Before a result. -/
def EndF (q : FQ) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kLen) = BitVec.ofNat 64 q.L ∧
    word s.mem q.B (8 * kUsedP) = q.up ∧ OutUp s q.B q.Z q.op q.up q.L ∧
    word s.mem q.B (8 * kStat) = BitVec.ofNat 64 q.st ∧ q.st < 4

theorem pins_endf {Φ : FQ → State → Prop} (h : ∀ q s, Φ q s → EndF q s) : Pins Φ [.x0] :=
  pins_ws' (fun q : FQ => q.B) (fun q : FQ => q.Z) (fun q : FQ => q.w) fun _ _ hx => (h _ _ hx).1

/-- The working space and `used`'s pointer. -/
def UpF (q : FQ) (s : State) : Prop := Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kUsedP) = q.up

theorem EndF.up {q : FQ} {s : State} (h : EndF q s) : UpF q s := ⟨h.1, h.2.2.2.1⟩

theorem upLoadF_ok {s : State} {q : FQ} (h : UpF q s) {l : List Instr} (hl : l = [movi .x3 0] ∨ l = [ldh .x3 kUsed]) :
    WP isa (.block (l ++ [ldh .x2 kUsedP])) s fun t => ∀ r ∈ [Reg.x2], t.gpr r = q.up := by
  obtain ⟨hw, hU⟩ := h
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega_using [h256, hi])
  refine WP.mono (Q := fun (t : State) => t.gpr .x2 = q.up) ?_ fun t h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h
  rcases hl with rfl | rfl
  · brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hl' kUsedP (by decide), hU]
  · brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hdr_enc (show kUsed < 32 by decide), hl' kUsedP (by decide),
      hl' kUsed (by decide), hU]

/-- `finNone` and `finUsed r`. -/
theorem finStoreF_ct {Φ : FQ → State → Prop} (hE : ∀ q s, Φ q s → UpF q s) {l : List Instr} (r : Nat)
    (hl : l = [movi .x3 0] ∨ l = [ldh .x3 kUsed]) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (l ++ [ldh .x2 kUsedP])) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht' : (taint.check (Taint.ofRegs [.x2]) (.block ([st .x3 .x2, movi .x0 r] : List Instr)) hc').isSome = true) :
    RelCT isa (Two Φ) (.block ((l ++ [ldh .x2 kUsedP]) ++ ([st .x3 .x2, movi .x0 r] : List Instr)))
      fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => ∀ r ∈ [Reg.x2], t.gpr r = q.up) [.x0]
    (pins_ws' (fun q : FQ => q.B) (fun q : FQ => q.Z) (fun q : FQ => q.w) fun _ _ hx => (hE _ _ hx).1) ht
    fun _ _ h => upLoadF_ok (hE _ _ h) hl) (two_taint [.x2] (pins_of _ (fun q _ => q.up) fun _ _ h => h) ht'))

/-- After `used` is written. -/
def EndFO (q : FQ) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kLen) = BitVec.ofNat 64 q.L

theorem finPrimeF_ct {Φ : FQ → State → Prop} (hE : ∀ q s, Φ q s → EndF q s) :
    RelCT isa (Two Φ) finPrime fun _ _ => True := by
  rw [finPrime_eq]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧ t.gpr .x2 = q.up) [.x0]
    (pins_endf hE) (by taint_decide) fun q s h => ?_) (two_piece (Ψ := EndFO) [.x2] (pins_of _ (fun q _ => q.up)
      fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)
      fun q s h => ?_))) (RelCT.seq (two_piece [.x0] (pins_ws' (fun q : FQ => q.B) (fun q : FQ => q.Z)
        (fun q : FQ => q.w) fun _ _ h => h.1) (by taint_decide) fun q s h =>
          storeBlk_ok' h.1 (show kOut < 32 by decide) (show kLen < 32 by decide) h.2.1 h.2.2)
      (two_taint _ (pins_of _ (fun q => soVal' q.B (off q.B (slot q.w aN)) q.op q.L) fun _ _ h => h)
        (by taint_decide)))
  · have he := hE q s h
    refine WP.mono (WP.keep [.x3, .x2] (Q := fun t => t.gpr .x2 = q.up ∧ t.mem = s.mem)
      (WP.and (WP.mono (upLoadF_ok he.up (.inr rfl)) fun t h => h .x2 (by simp)) (by
        have hw := he.1
        have hn := hw.scr.nowrap
        have h256 := hw.h256
        brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hdr_enc (show kUsed < 32 by decide),
          hw.scr.ld (d := 8 * kUsedP) (by simp only [kUsedP, sFn]; omega_using [h256]),
          hw.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega_using [h256])]))
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h2, hm⟩, k⟩ => ⟨?_, h2⟩
    obtain ⟨hw, hO, hK, hU, ho, hS, hst⟩ := he
    exact ⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
      by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS, hst⟩
  · obtain ⟨⟨hw, hO, hK, hU, ho, -⟩, h2⟩ := h
    have h256 := hw.h256
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW q.up (s.gpr .x3)) (by
      have hup : q.up + BitVec.ofNat 64 0 = q.up := off_zero q.up
      brun [h2, hup, ho.upw]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
    have f : Frm q.B [(q.Z, 2 ^ 64)] s.mem t.mem := by rw [hm]; exact frm_up ho.upZ _ _
    have hw' : ∀ i < 32, word t.mem q.B (8 * i) = word s.mem q.B (8 * i) := fun i hi =>
      f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega_using [hi])
    exact ⟨hw.congr' f (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.past h256 _) k (by decide),
      (hw' _ (by decide)).trans hO, (hw' _ (by decide)).trans hK⟩

theorem endF_load {q : FQ} {s : State} (h : EndF q s) :
    WP isa (.block [ldh .x3 kStat]) s fun t => EndF q t ∧ t.gpr .x3 = BitVec.ofNat 64 q.st := by
  obtain ⟨hw, hO, hK, hU, ho, hS, hst⟩ := h
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 q.st ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show kStat < 32 by decide), hw.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using [h256]),
      hS]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ =>
    ⟨⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
      by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS, hst⟩, h3⟩

/-- `pResult` leaks the same in runs with the same public data. -/
theorem pResult_ct : RelCT isa (Two EndF) pResult fun _ _ => True := by
  unfold pResult
  refine RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧ t.gpr .x3 = BitVec.ofNat 64 q.st) [.x0]
    (pins_endf fun _ _ h => h) (by taint_decide) fun q s h => endF_load h)
    (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
      (finStoreF_ct (fun _ _ h => h.1.1.up) 0 (.inl rfl) (by taint_decide) (by taint_decide))
      (RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧
          t.gpr .x3 = BitVec.ofNat 64 q.st - BitVec.ofNat 64 1) [] (pins_nil' _) (by taint_decide)
        fun q s h => ?_)
        (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
          (finPrimeF_ct fun _ _ h => h.1.1)
          (finStoreF_ct (fun _ _ h => h.1.1.up) 2 (.inr rfl) (by taint_decide) (by taint_decide)))))
  obtain ⟨⟨⟨hw, hO, hK, hU, ho, hS, hst⟩, h3⟩, -⟩ := h
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 q.st - BitVec.ofNat 64 1 ∧
    t.mem = s.mem) (by brun [h3]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3', hm⟩, k⟩ =>
    ⟨⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
      by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS, hst⟩, h3'⟩

/-- `qResult` leaks the same in runs with the same public data. -/
theorem qResult_ct : RelCT isa (Two EndF) qResult fun _ _ => True := by
  unfold qResult
  exact RelCT.seq (two_piece (Ψ := fun q t => EndF q t ∧ t.gpr .x3 = BitVec.ofNat 64 q.st) [.x0]
    (pins_endf fun _ _ h => h) (by taint_decide) fun q s h => endF_load h)
    (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
      (finStoreF_ct (fun _ _ h => h.1.1.up) 0 (.inl rfl) (by taint_decide) (by taint_decide))
      (finStoreF_ct (fun _ _ h => h.1.1.up) 2 (.inr rfl) (by taint_decide) (by taint_decide)))

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-! ### `Ffdh.AArch64.ParameterCandidate.CTPieces`, which only this module used -/

section

/-!
# An FFDH parameter candidate on AArch64: constant time of the shape's checks

The congruence (`residue_ct`), RSA's table (`tableWrite_ct`), the sieve
(`sieve_ct`, by the table's first words or by all of the division's:
RSA's `trialEntry_ct` for the words it reads, `stopN`, which the number in
`aN` fixes) and `q` (`halveQ_ct`), each from the working space and what it
reads.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The working space of `p`'s words. -/
def WQ (L : WsP) (s : State) : Prop := Ws s L.B L.Z L.w

theorem residue_ct : RelCT isa (Two WQ) (seqs residue) fun _ _ => True :=
  ws_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)

theorem tableWrite_ct : RelCT isa (Two WQ) tableWrite fun _ _ => True :=
  ws_block_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)

/-! ## The sieve -/

/-- RSA's public data, for the working space alone. -/
def fpubOf (L : WsP) : VG.Proof.RsaKeyGen.AArch64.FPub := ⟨L.B, L.Z, L.w, [], 0, 0, 0, [], 0, 0, 0, 0, ⟨false, false, false, none⟩⟩

/-- Before the sieve of the number `a.2` in `aN`. -/
def SV (a : WsP × Nat) (s : State) : Prop :=
  Ws s a.1.B a.1.Z a.1.w ∧ slot a.1.w aTab + 2048 ≤ a.1.Z ∧ TabOk s.mem a.1.B a.1.w ∧
    wv s.mem a.1.B (slot a.1.w aN) a.1.w = a.2

/-- Before word `k` of the table. -/
def SI (first : Bool) (a : WsP × Nat) (k : Nat) (s : State) : Prop :=
  Ws s a.1.B a.1.Z a.1.w ∧ slot a.1.w aTab + 2048 ≤ a.1.Z ∧ s.gpr .x9 = off a.1.B (slot a.1.w aTab + 8 * k) ∧
    s.gpr .x10 = BitVec.ofNat 64 (sieveWords first a.1.w - k) ∧ s.gpr .x7 = 0 ∧ s.gpr .x8 = mask true ∧
    TabOk s.mem a.1.B a.1.w ∧ wv s.mem a.1.B (slot a.1.w aN) a.1.w = a.2 ∧ s.gpr .x1 = mask (anyPre a.2 (4 * k))

/-- After the loop. -/
def SIE (a : WsP × Nat) (s : State) : Prop := Ws s a.1.B a.1.Z a.1.w

/-- The words the sieve reads. -/
abbrev sieveN (first : Bool) (a : WsP × Nat) : Nat := stopN a.2 (sieveWords first a.1.w)

theorem sieveIter_ok {first : Bool} {a : WsP × Nat} {k : Nat} {s : State}
    (hk : k < stopN a.2 (sieveWords first a.1.w)) (h : SI first a k s) :
    WP isa (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)) ++
      ([sieveStop] : List (Prog isa)))) s fun t =>
      isa.eval (.nonzero .x .x10) t = some (decide (k + 1 < stopN a.2 (sieveWords first a.1.w))) ∧
        (k + 1 < stopN a.2 (sieveWords first a.1.w) → SI first a (k + 1) t) ∧
        (k + 1 = stopN a.2 (sieveWords first a.1.w) → SIE a t) := by
  obtain ⟨hw, hT, h9, h10, h7, h8, htab, hc, h1⟩ := h
  have hN := (sieveWords_le first a.1.w).symm
  have hle : stopN a.2 (sieveWords first a.1.w) ≤ sieveWords first a.1.w := stopN_le _ _
  obtain ⟨nxt, nxf⟩ := stopN_next hk
  have e10 : BitVec.ofNat 64 (sieveWords first a.1.w - k) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (sieveWords first a.1.w - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hk, hle, hN.1]
  refine WP.mono (sieveWord_ok (s₀ := s) hc hT (by omega_using [hk, hle, hN.1]) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩
    h9 h1) fun t ⟨hI, h9', h1', h10'⟩ => ⟨?_, fun hlt => ⟨hI.ws, hT, h9', ?_, hI.x7, hI.x8, fun i hi => by
      rw [hI.mem]; exact htab i hi, by rw [hI.mem]; exact hc, h1'⟩, fun _ => hI.ws⟩
  · rw [eval_nonzero, h10']
    rcases Bool.eq_false_or_eq_true (anyPre a.2 (4 * (k + 1))) with hd | hd
    · have e := nxt hd
      rw [ite_eq_left hd]
      exact congrArg some ((decide_eq_false (by omega_using [e])).symm)
    · have hi := nxf hd
      rw [ite_eq_right (by rw [hd]; exact Bool.false_ne_true), h10,
        sub1_bne (by omega_using [hk, hle]) (by omega_using [hN.1])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hi]))
  · rw [h10', ite_eq_right (by rw [stopN_before _ _ (k + 1) hlt]; exact Bool.false_ne_true), h10, e10]

theorem sieveBody_ct (first : Bool) :
    RelCT isa (Two fun (a : (WsP × Nat) × Nat) s => a.2 < sieveN first a.1 ∧ SI first a.1 a.2 s)
    (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)) ++
      ([sieveStop] : List (Prog isa)))) fun _ _ => True := by
  simp only [List.append_assoc, List.singleton_append]
  have ne : ∀ j, trialEntry j ≠ [] := fun j => by unfold trialEntry; exact List.cons_ne_nil _ _
  refine seqs_cons_ct (by simp [ne]) (RelCT.seq (two_post (Ψ := fun a s => TBI (fpubOf a.1.1, a.2) s)
    (two_taint [.x9] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide))
    (fun p s h => ?_)) ?_)
  · obtain ⟨hk, hw, hT, h9, -, h7, h8, htab, -, -⟩ := h
    have hN := (sieveWords_le first p.1.1.w).symm
    have hle : stopN p.1.2 (sieveWords first p.1.1.w) ≤ sieveWords first p.1.1.w := stopN_le _ _
    replace hk : p.2 < stopN p.1.2 (sieveWords first p.1.1.w) := hk
    exact WP.mono (tlLoad_ok hT (by omega_using [hk, hN, hle]) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9) fun t ⟨⟨h17, _, hm⟩, k⟩ =>
      ⟨hw.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide), by omega_using [hk, hN, hle], h17,
        (k.gpr .x7 (by decide)).trans h7, (k.gpr .x8 (by decide)).trans h8⟩
  refine two_map (Φ' := TBI) (fun a : (WsP × Nat) × Nat => (fpubOf a.1.1, a.2)) (fun _ _ h => h) ?_
  refine RelCT.seqs_append (ne 0) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 1) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 2) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 3) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  exact two_taint [] (pins_nil₀ _) (by taint_decide)

/-- `sieve_ct`, from its first block's. -/
theorem sieve_ct' (first : Bool) (hinit : RelCT isa (Two SV)
    (.block (ws ++ base aTab .x9 ++ sieveCount first ++ [movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1]))
      fun _ _ => True) : RelCT isa (Two SV) (seqs (sieve first)) fun _ _ => True := by
  rw [sieve_eq]
  simp only [seqs]
  refine RelCT.seq (two_post hinit (Ψ := fun a s => 0 < sieveN first a ∧ SI first a 0 s)
      fun a s ⟨hw, hT, htab, hc⟩ => ?_)
    (RelCT.seq (two_loop (Φ := SI first) (Ψ := SIE) (sieveN first) (sieveBody_ct first)
        fun _ _ _ hk h => sieveIter_ok hk h)
      (two_taint [.x0] (pins_ws' (fun a : WsP × Nat => a.1.B) (fun a : WsP × Nat => a.1.Z)
        (fun a : WsP × Nat => a.1.w) fun _ _ h => h) (by taint_decide)))
  refine WP.mono (sieveInit_ok first hw) fun t ⟨⟨h9, h10, h1, h7, h8, hm⟩, k⟩ =>
    ⟨stopN_pos _ (sieveWords_le first a.1.w).1, ?_⟩
  exact ⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), hT, h9,
    by rw [h10, Nat.sub_zero], h7, h8, fun i hi => by rw [hm]; exact htab i hi, by rw [hm]; exact hc,
    by rw [h1, Nat.mul_zero, anyPre_zero]; rfl⟩

/-- The sieve leaks the same in runs with the same working space and the
same number in `aN`, which fixes the word it stops at. -/
theorem sieve_ct (first : Bool) : RelCT isa (Two SV) (seqs (sieve first)) fun _ _ => True := by
  cases first
  · exact sieve_ct' false (ws_block_ct0 (fun a : WsP × Nat => a.1.B) (fun a : WsP × Nat => a.1.Z)
      (fun a : WsP × Nat => a.1.w) (fun _ _ h => h.1) (by taint_decide))
  · exact sieve_ct' true (ws_block_ct0 (fun a : WsP × Nat => a.1.B) (fun a : WsP × Nat => a.1.Z)
      (fun a : WsP × Nat => a.1.w) (fun _ _ h => h.1) (by taint_decide))

/-! ## `q` -/

theorem halvePass_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (seqs (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1]) :: halfPass))
      s fun t => Ws t B Z w := by
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have e : seqs (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1]) :: halfPass) =
      .seq (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1])) (seqs halfPass) := rfl
  rw [e]
  refine WP.seq (WP.mono (halveHead_ok h) fun s₁ ⟨⟨h16, h17, h15, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (halfPass_ok (mb := true) (h.scr.congr k₁.wr) h16 h17 h15 h12 hw1 (by omega_using [hw2]) (by omega_using [sN]) (by omega_using [sN])
    (.inl rfl)) fun t ⟨_, o, k₂⟩ => ?_
  rw [hm₁] at o
  exact h.congr' (Frm.of_outside (o.mono (o' := slot w aN) (n' := 8 * (w + 2)) (by omega_using []) (by omega_using []))
    (List.mem_singleton_self _)) (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _)
    (k₁.trans k₂) (by decide)

/-- `halveQ` leaks the same in runs with the same working space. -/
theorem halveQ_ct : RelCT isa (Two WQ) (seqs halveQ) fun _ _ => True := by
  unfold halveQ
  rw [List.cons_append]
  refine ct_app' (a := _ :: halfPass) (by simp) (by simp) (Ψ := WQ) (two_post ?_ fun L s h => halvePass_ok h) ?_
  · exact ws_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)
  · rw [seqs_one]
    exact ws_block_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h)
      (by taint_decide)

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on AArch64: constant time of `main`

`main`'s stages (`Stg`, `Main.lean`), each piece from the stage before it
(`CTPieces.lean`, `CTTest.lean`), the branches on the flag so far
(`check_ct`: after the congruence, `p`'s sieve by the table's first words,
`q`'s oddness, `q`'s sieve and `p`'s whole sieve), which the public data
fixes, and the tests (`tests_ct`), whose branches the results of
Miller–Rabin fix.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The working space of `p`'s words. -/
abbrev PP.ws (p : PP) : WsP := ⟨p.B, p.Z, mW p.bits⟩

/-- Before `main`. -/
def M0 (p : PP) (s : State) : Prop :=
  PH p s ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L ∧ p.L ≤ p.r.length

/-! ## The tests -/

/-- The status `millerRabin` leaves. -/
def statF (res : Option (Bool × List Byte)) : Nat :=
  match res with
  | none => 0
  | some (b, _) => if b then 1 else 2

/-- The octets read after `millerRabin`. -/
def uOfRes (r : List Byte) (res : Option (Bool × List Byte)) : Nat :=
  match res with
  | none => 0
  | some (_, rest) => r.length - rest.length

theorem OutUp.mono' {s : State} {B : Addr} {Z : Nat} {op up : Addr} {k k' : Nat} (h : OutUp s B Z op up k)
    (hk : k' ≤ k) : OutUp s B Z op up k' :=
  ⟨h.upw, h.upZ, fun j hj => h.outw j (by omega_arith), fun j hj => h.outZ j (by omega_arith), fun j hj => h.ou j (by omega_arith)⟩

theorem te_stat {q : TQ} {s : State} (h : TE q s) :
    word s.mem q.p.B (8 * kStat) = BitVec.ofNat 64 (statF q.res) := by
  obtain ⟨_, s₀, he⟩ := h
  have st := MrEnd.stat he
  rcases hr : q.res with _ | ⟨b, rest⟩
  · exact st.1 hr
  · exact (st.2 b rest hr).1

theorem te_fix {q : TQ} {s : State} (h : TE q s) : MrFix q.p q.w q.N q.mb q.K s := by
  obtain ⟨_, s₀, he⟩ := h; exact he.1

/-- The result's public data after a test. -/
abbrev endFOf (q : TQ) : FQ := ⟨q.p.B, q.p.Z, q.w, q.p.op, q.p.up, mLen q.mb, statF q.res⟩

theorem te_endF {q : TQ} {s : State} (h : TE q s) : EndF (endFOf q) s := by
  have hd := h.1
  have fix := te_fix h
  have hmbb := hd.mbb
  refine ⟨fix.st.ws, fix.st.args.out, fix.len, fix.st.args.usedP, OutUp.mono' fix.st.ou (by simp only [mLen, PP.L]; omega_arith),
    te_stat h, ?_⟩
  show statF q.res < 4
  unfold statF; split <;> (try split) <;> decide

/-- Before the tests. -/
def TQd (p : PP) (s : State) : Prop := Stg p (cOf p) s ∧ ((cOf p - 1) / 2) % 2 = 1

/-- The first test's public data: `p`'s first witness. -/
abbrev d1 (p : PP) : TD := ⟨p, p.bits, cOf p, p.L, 1⟩

/-- The second's: `q`'s witnesses. -/
abbrev d2 (p : PP) : TD :=
  ⟨p, p.bits - 1, (cOf p - 1) / 2, uOfRes p.r (d1 p).tq.res, Spec.Ffdh.primeChecks (p.bits - 1)⟩

/-- The third's: `p`'s others. -/
abbrev d3 (p : PP) : TD := ⟨p, p.bits, cOf p, uOfRes p.r (d2 p).tq.res, Spec.Ffdh.primeChecks p.bits - 1⟩

/-- `q` is odd. -/
abbrev QOdd (p : PP) : Prop := ((cOf p - 1) / 2) % 2 = 1

/-- The Montgomery setup, the exponent and the witnesses of a test of
`N p` of `mb p` bits by `K p` witnesses from octet `u p`. -/
theorem tail_ct (M : Mont) (R : Kernel) (mb N u K : PP → Nat) :
    RelCT isa (Two fun p t => TT p (mb p) (N p) (u p) (K p) t ∧ QOdd p)
      (seqs (montPrep M.mm ++ expSetup ++ VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run))
      (Two fun p t => TE (⟨p, mb p, N p, u p, K p⟩ : TD).tq t ∧ QOdd p) :=
  two_post ((two_map (fun p => (⟨p, mb p, N p, u p, K p⟩ : TD)) (fun _ _ h => h.1) (testTail_ct M R)).mono
    (fun _ _ h => h) fun _ _ _ => trivial) fun _ s h =>
      WP.mono (testTail_ok M R h.1) fun _ he => ⟨⟨h.1.dims, s, he⟩, h.2⟩

/-- Before a test of `p` from octet `u p`. -/
def PStart (u : PP → Nat) (p : PP) (s : State) : Prop :=
  (∃ w, PSt p w s) ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u p) ∧ u p ≤ p.r.length ∧ p.L ≤ p.r.length ∧
    QOdd p

/-- A test of `p` from octet `u p`, its witness count changed by `adjust` to
`K p`, leaks the same in runs with the same public data. -/
theorem testP_ct (M : Mont) (R : Kernel) (u K : PP → Nat) {adjust : Prog isa} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) adjust hc).isSome = true)
    (hadj : ∀ p s, TT p p.bits (cOf p) (u p) (Spec.Ffdh.primeChecks p.bits) s →
      WP isa adjust s fun t => TT p p.bits (cOf p) (u p) (K p) t) :
    RelCT isa (Two (PStart u)) (seqs (test false [adjust] M.mm R.run))
      (Two fun p t => TE (⟨p, p.bits, cOf p, u p, K p⟩ : TD).tq t ∧ QOdd p) := by
  rw [test_false']
  refine ct_app' (by simp [phase]) (by simp) (Ψ := fun p t => TT p p.bits (cOf p) (u p)
    (Spec.Ffdh.primeChecks p.bits) t ∧ QOdd p) ?_ ?_
  · refine two_post (ct_app' (by simp [phase]) (by simp [shapeP, loadA]) (Ψ := fun p t => SP p t)
      (two_post (two_map id (fun _ _ h => h.1.choose_spec.ph) (phase_ct false)) fun p s h => ?_)
      (two_map id (fun _ _ h => h) shapeP_ct)) fun p s h => ?_
    · refine WP.mono (phase_ok h.1.choose_spec.ph false) fun t ht => ?_
      have hmb : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
      have st := ht.st
      rw [hmb] at st
      exact ⟨st, by have := ht.len; rw [hmb] at this; exact this, h.2.2.2.1⟩
    · exact WP.mono (pPhase_ok h.1.choose_spec.ph rfl h.2.1 h.2.2.1 h.2.2.2.1) fun t ⟨ht', _⟩ => ⟨ht', h.2.2.2.2⟩
  refine ct_app' (a := [adjust]) (by simp) (by simp [montPrep])
    (Ψ := fun p t => TT p p.bits (cOf p) (u p) (K p) t ∧ QOdd p) ?_
    (tail_ct M R (fun p => p.bits) cOf u K)
  rw [seqs_one]
  exact two_piece [.x0] (pins_ws' (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits)
    fun _ _ h => h.1.st.ws) ht fun p s h => WP.mono (hadj p s h.1) fun t ht => ⟨ht, h.2⟩

/-- Before the test of `q` from octet `u p`. -/
def QStart (u : PP → Nat) (p : PP) (s : State) : Prop :=
  PSt p (mW p.bits) s ∧ wv s.mem p.B (slot (mW p.bits) aN) (mW p.bits) = (cOf p - 1) / 2 ∧
    QOdd p ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u p) ∧ u p ≤ p.r.length ∧ p.L ≤ p.r.length

theorem testQ_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two (QStart fun p => (d2 p).u)) (seqs (test true [] M.mm R.run))
      (Two fun p t => TE (d2 p).tq t ∧ QOdd p) := by
  rw [test_true]
  refine ct_app' (by simp [phase]) (by simp [montPrep])
    (Ψ := fun p t => TT p (d2 p).mb (d2 p).N (d2 p).u (d2 p).K t ∧ QOdd p)
    (two_post (two_map id (fun _ _ h => h.1.ph) (phase_ct true)) fun p s h =>
      WP.mono (qPhase_ok h.1 rfl h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun _ ⟨ht, _⟩ =>
        ⟨ht, h.2.2.1⟩)
    (tail_ct M R (fun p => (d2 p).mb) (fun p => (d2 p).N) (fun p => (d2 p).u) (fun p => (d2 p).K))

/-- After a test whose public data are `f p`: `qResult` unless it passed,
else `cont`. -/
theorem stage_ct (f : PP → TQ) {cont : Prog isa}
    (hc : RelCT isa (Two fun p t => (TE (f p) t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (f p).res = 1)) ∧ isa.eval (.zero .x .x3) t = some true) cont
      fun _ _ => True) :
    RelCT isa (Two fun p t => TE (f p) t ∧ QOdd p)
      (seqs [.block [ldh .x3 kStat, .subImm .x .x3 .x3 1], .ite (.zero .x .x3) cont qResult]) fun _ _ => True := by
  simp only [seqs]
  have pw : ∀ {Φ : PP → State → Prop}, (∀ p s, Φ p s → TE (f p) s) → Pins Φ [.x0] := fun h =>
    pins_ws' (fun p => (f p).p.B) (fun p => (f p).p.Z) (fun p => (f p).w) fun _ _ hx => (te_fix (h _ _ hx)).st.ws
  refine RelCT.seq (two_piece (Ψ := fun p t => (TE (f p) t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (f p).res = 1))) [.x0] (pw fun _ _ h => h.1) (by taint_decide)
      fun p s h => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_)
  · have fix := te_fix h.1
    refine WP.mono (stat1_ok fix.st.ws (v := statF (f p).res) (by unfold statF; split <;> (try split) <;> decide)
      (te_stat h.1)) fun t ⟨hz, hm, k⟩ => ⟨⟨?_, h.2⟩, hz⟩
    obtain ⟨⟨hd, s₀, he⟩, -⟩ := h
    have hEZ := hd.eZ
    exact ⟨hd, s₀, he.1.same hEZ hm k (by decide), by rw [hm]; exact he.2.1, fun b rest h' => by
      rw [hm]; exact he.2.2.1 b rest h', by rw [hm]; exact he.2.2.2.1, (he.2.2.2.2.trans k).mono (by decide)⟩
  · exact hc.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) h) fun _ _ h => h
  · exact two_map (fun p => endFOf (f p)) (fun _ _ h => te_endF h.1.1.1) qResult_ct

/-- A test that passed. -/
def PQ (q : TQ) (s : State) : Prop := TE q s ∧ isa.eval (.zero .x .x3) s = some true

theorem pq_res {q : TQ} {s : State} (h : PQ q s) (h3 : isa.eval (.zero .x .x3) s = some (decide (statF q.res = 1))) :
    ∃ rest, q.res = some (true, rest) := by
  have h2 := h.2
  rw [h3] at h2
  have h1 : statF q.res = 1 := by simpa using h2
  unfold statF at h1
  rcases hr : q.res with _ | ⟨b, rest⟩ <;> rw [hr] at h1
  · cases h1
  · cases b
    · cases h1
    · exact ⟨rest, rfl⟩

/-- What a test that passed leaves: the octets it read. -/
theorem te_passed {q : TQ} {s : State} (h : TE q s) (h3 : isa.eval (.zero .x .x3) s = some (decide (statF q.res = 1)))
    (ht : isa.eval (.zero .x .x3) s = some true) :
    MrFix q.p q.w q.N q.mb q.K s ∧ word s.mem q.p.B (8 * kUsed) = BitVec.ofNat 64 (uOfRes q.p.r q.res) ∧
      uOfRes q.p.r q.res ≤ q.p.r.length := by
  obtain ⟨rest, hr⟩ := pq_res ⟨h, ht⟩ h3
  obtain ⟨hd, s₀, he⟩ := h
  obtain ⟨u, hu, hrest, hU⟩ := (he.2.2.1 true rest hr).2
  have hu' : uOfRes q.p.r q.res = u := by
    rw [hr]; simp only [uOfRes]; rw [hrest, List.length_drop]; omega_arith
  exact ⟨he.1, by rw [hu']; exact hU, by rw [hu']; exact hu⟩

/-- `p`'s other witnesses, after `q` passed. -/
theorem testRest_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two fun p t => (TE (d2 p).tq t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (d2 p).tq.res = 1)) ∧ isa.eval (.zero .x .x3) t = some true)
      (testRest M.mm R.run) fun _ _ => True := by
  unfold testRest
  refine ct_app' (by simp [test, phase]) (by simp) (Ψ := fun p t => TE (d3 p).tq t ∧ QOdd p) ?_
    (by rw [seqs_one]; exact two_map (fun p => endFOf (d3 p).tq) (fun _ _ h => te_endF h.1) pResult_ct)
  refine two_map id (Φ' := PStart fun p => (d3 p).u) (fun p s h => ?_)
    (testP_ct M R (fun p => (d3 p).u) (fun p => (d3 p).K) (adjust := restChecks) (by taint_decide)
      fun p s h => WP.mono (restChecks_ok h (by unfold Spec.Ffdh.primeChecks; split <;> decide)) fun t ⟨ht, _⟩ => ht)
  obtain ⟨⟨hte, hqo⟩, h3, ht⟩ := h
  obtain ⟨fix, hU, hu⟩ := te_passed hte h3 ht
  exact ⟨⟨_, fix.st⟩, hU, hu, hte.1.hL, hqo⟩

/-- `q` and its test, after `p`'s first witness passed. -/
theorem testQS_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two fun p t => (TE (d1 p).tq t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (d1 p).tq.res = 1)) ∧ isa.eval (.zero .x .x3) t = some true)
      (testQ M.mm R.run) fun _ _ => True := by
  unfold testQ
  simp only [List.append_assoc]
  refine ct_app' (by simp [halveQ]) (by simp [test, phase]) (Ψ := QStart fun p => (d2 p).u) ?_ ?_
  · refine two_post (two_map PP.ws (fun _ _ h => (te_fix h.1.1).st.ws) halveQ_ct) fun p s h => ?_
    obtain ⟨⟨hte, hqo⟩, h3, ht⟩ := h
    obtain ⟨fix, hU, hu⟩ := te_passed hte h3 ht
    obtain ⟨_, hc⟩ := fix.ctx
    have hws := fix.st.ws
    have hn := hws.scr.nowrap
    have h256 := hws.h256
    have hb1 : 512 ≤ p.bits := fix.st.dims.b1
    obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits)
      (by omega_arith) (Spec.Rsa.os2ip (p.r.take p.L))
    refine WP.mono (halveQ_ok fix.st hc.n rfl) fun t ⟨st, hq, _, f, _⟩ => ⟨st, by
      rw [hq]; simp only [cOf] at hpo ⊢; omega_arith, hqo, ?_, hu, hte.1.hL⟩
    rw [f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega_arith)
      · exact .inr (by decide)) (by simp only [kUsed, sFn]; omega_arith)]
    exact hU
  exact ct_app' (by simp [test, phase]) (by simp) (Ψ := fun p t => TE (d2 p).tq t ∧ QOdd p) (testQ_ct M R)
    (stage_ct (fun p => (d2 p).tq) (testRest_ct M R))

/-- The tests leak the same in runs with the same public data. -/
theorem tests_ct (M : Mont) (R : Kernel) : RelCT isa (Two TQd) (tests M.mm R.run) fun _ _ => True :=
  ct_app' (by simp [test, phase]) (by simp) (Ψ := fun p t => TE (d1 p).tq t ∧ QOdd p)
    (two_map id (Φ' := PStart fun p => (d1 p).u) (fun p s h => ⟨⟨_, h.1.st⟩, h.1.used, h.1.hl, h.1.hl, h.2⟩)
      (testP_ct M R (fun p => (d1 p).u) (fun p => (d1 p).K) (adjust := firstCheck) (by taint_decide)
        fun p s h => WP.mono (firstCheck_ok h) fun t ⟨ht, _⟩ => ht))
    (stage_ct (fun p => (d1 p).tq) (testQS_ct M R))

/-! ## `main` -/

theorem main_eq (M : Mont) (R : Kernel) : main M.mm R.run = seqs ((phase false ++ shapeP) ++ (residue ++
    ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
      (seqs ([tableWrite] ++ (sieve true ++ ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
        (seqs (halveQ ++ ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
          (seqs (sieve false ++ ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
            (seqs (shapeP ++ (sieve false ++ ([.block [ldh .x5 fBad],
              .ite (.zero .x .x5) (tests M.mm R.run) (finUsed 2)] : List (Prog isa)))))
            (finUsed 2)] : List (Prog isa))))
          (finUsed 2)] : List (Prog isa))))
        (finUsed 2)] : List (Prog isa)))))
      (finUsed 2)] : List (Prog isa)))) := by
  simp only [main, mainQ, mainP, List.append_assoc]

/-- A check of the flag so far, `v p`, which the public data fixes: `cont`
when it is zero, else the candidate ends. `T` is what else the stage has
of the memory (the table, once it is written). -/
theorem check_ct (T : PP → Mem → Prop) (n : PP → Nat) (v : PP → BitVec 64) {cont : Prog isa}
    (hc : RelCT isa (Two fun p t => (StgF p (n p) (v p) t ∧ T p t.mem) ∧ v p = 0) cont fun _ _ => True) :
    RelCT isa (Two fun p t => StgF p (n p) (v p) t ∧ T p t.mem)
      (seqs [.block [ldh .x5 fBad], .ite (.zero .x .x5) cont (finUsed 2)]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p t => (StgF p (n p) (v p) t ∧ T p t.mem) ∧ t.gpr .x5 = v p) [.x0]
    (pins_ws' (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits) fun _ _ h => h.1.1.st.ws)
    (by taint_decide) fun p s h => WP.mono (stgFlag_ok h.1) fun t' ⟨⟨g, h5⟩, hm, _⟩ =>
      ⟨⟨g, by rw [hm]; exact h.2⟩, h5⟩)
    (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_)
  · refine hc.mono (fun _ _ h => two_mono (fun p t ⟨⟨hg, h5⟩, hz⟩ => ⟨hg, ?_⟩) h) fun _ _ h => h
    rw [eval_zero, h5] at hz
    simpa using hz
  · rw [finUsed_split]
    exact two_map (Φ' := UpF) (fun p : PP => (⟨p.B, p.Z, mW p.bits, p.op, p.up, p.L, 0⟩ : FQ))
      (fun p s h => ⟨h.1.1.1.1.st.ws, h.1.1.1.1.st.args.usedP⟩)
      (finStoreF_ct (fun _ _ h => h) 2 (.inr rfl) (by taint_decide) (by taint_decide))

/-- The table, as `check_ct`'s `T`. -/
abbrev tabOf (p : PP) (m : Mem) : Prop := TabOk m p.B (mW p.bits)

/-- `main` leaks the same in runs with the same public data. -/
theorem main_ct (M : Mont) (R : Kernel) : RelCT isa (Two M0) (main M.mm R.run) fun _ _ => True := by
  rw [main_eq]
  -- `p` and its working space.
  refine ct_app' (by simp [phase]) (by simp [residue]) (Ψ := fun p t => Stg p (cOf p) t)
    (two_post (ct_app' (by simp [phase]) (by simp [shapeP, loadA]) (Ψ := SP)
      (two_post (two_map id (fun _ _ h => h.1) (phase_ct false)) fun p s h => ?_) shapeP_ct)
      fun p s h => WP.mono (stgA_ok h.1 h.2.1 h.2.2) fun _ h => h.1) ?_
  · refine WP.mono (phase_ok h.1 false) fun t ht => ?_
    have hmb : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
    have st := ht.st
    rw [hmb] at st
    exact ⟨st, by have := ht.len; rw [hmb] at this; exact this, h.2.2⟩
  -- The congruence, rejected at once.
  refine ct_app' (by simp [residue]) (by simp) (Ψ := fun p t => StgF p (cOf p) (scr1 p.g (cOf p)) t ∧ True)
    (two_post (two_map PP.ws (fun _ _ h => h.st.ws) residue_ct) fun p s h =>
      WP.mono (stgB_ok h) fun _ h => ⟨h.1, trivial⟩) ?_
  refine check_ct (fun _ _ => True) cOf (fun p => scr1 p.g (cOf p)) ?_
  -- The table, and the sieve of `p` by its first words.
  refine ct_app' (a := [tableWrite]) (by simp) (by simp [sieve])
    (Ψ := fun p t => StgT p (cOf p) (scr1 p.g (cOf p)) t)
    (two_post (by rw [seqs_one]; exact two_map PP.ws (fun _ _ h => h.1.1.1.st.ws) tableWrite_ct)
      fun p s h => by rw [seqs_one]; exact WP.mono (stgTab_ok h.1.1) fun _ h => h.1) ?_
  refine ct_app' (by simp [sieve]) (by simp) (Ψ := fun p t => StgT p (cOf p) (scr2 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map (fun p : PP => (p.ws, cOf p))
      (fun _ _ h => ⟨h.1.1.st.ws, pTab h.1.1.st.dims, h.2, h.1.1.an⟩) (sieve_ct true))
      fun p s h => WP.mono (stgSieve_ok true h) fun _ h => h.1) ?_
  refine check_ct tabOf cOf (fun p => scr2 p.g (mW p.bits) (cOf p))
    (two_map id (Φ' := fun p t => StgT p (cOf p) (scr2 p.g (mW p.bits) (cOf p)) t) (fun _ _ h => h.1) ?_)
  -- `q`, rejected at once if it is even.
  refine ct_app' (by simp [halveQ]) (by simp)
    (Ψ := fun p t => StgT p (cOf p / 2) (scr3 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map PP.ws (fun _ _ h => h.1.1.st.ws) halveQ_ct) fun p s h =>
      WP.mono (stgHalve_ok h) fun _ h => h.1) ?_
  refine check_ct tabOf (fun p => cOf p / 2) (fun p => scr3 p.g (mW p.bits) (cOf p))
    (two_map id (Φ' := fun p t => StgT p (cOf p / 2) (scr3 p.g (mW p.bits) (cOf p)) t) (fun _ _ h => h.1) ?_)
  -- The sieve of `q`.
  refine ct_app' (by simp [sieve]) (by simp)
    (Ψ := fun p t => StgT p (cOf p / 2) (scr4 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map (fun p : PP => (p.ws, cOf p / 2))
      (fun _ _ h => ⟨h.1.1.st.ws, pTab h.1.1.st.dims, h.2, h.1.1.an⟩) (sieve_ct false))
      fun p s h => WP.mono (stgSieve_ok false h) fun _ h => h.1) ?_
  refine check_ct tabOf (fun p => cOf p / 2) (fun p => scr4 p.g (mW p.bits) (cOf p))
    (two_map id (Φ' := fun p t => StgT p (cOf p / 2) (scr4 p.g (mW p.bits) (cOf p)) t) (fun _ _ h => h.1) ?_)
  -- `p` again, and its whole sieve.
  refine ct_app' (by simp [shapeP, loadA]) (by simp [sieve])
    (Ψ := fun p t => StgT p (cOf p) (scr4 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map id (fun _ _ h => ⟨h.1.1.st, h.1.1.len, h.1.1.hl⟩) shapeP_ct) fun p s h =>
      WP.mono (stgShape_ok h) fun _ h => h.1) ?_
  refine ct_app' (by simp [sieve]) (by simp) (Ψ := fun p t => StgT p (cOf p) (scr5 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map (fun p : PP => (p.ws, cOf p))
      (fun _ _ h => ⟨h.1.1.st.ws, pTab h.1.1.st.dims, h.2, h.1.1.an⟩) (sieve_ct false))
      fun p s h => WP.mono (stgSieve_ok false h) fun _ h => h.1) ?_
  refine check_ct tabOf cOf (fun p => scr5 p.g (mW p.bits) (cOf p)) ?_
  -- The tests.
  exact (tests_ct M R).mono (fun _ _ h => two_mono (fun p t ⟨hg, hz⟩ =>
    ⟨hg.1.1, qOdd_of_shape hg.1.1.st.dims (scr5_zero.mp hz)⟩) h) fun _ _ h => h

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on AArch64: constant time, and `Verified`

Every value of the candidate is public (`pcPub` fixes the arguments and the
octets of `rand`), so runs that agree on them agree on `ppOf`, and leak the
same (`code_constantTime`): the entry, the zeros to `out` and the length
check from the arguments, then `main` (`main_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A state the contract allows, with the public data `p`. -/
def P0 (p : PP) (s : State) : Prop := pcPre s ∧ ppOf s = p

/-- After the entry. -/
def P2 (p : PP) (t : State) : Prop := ∃ s, P0 p s ∧ EntryPost s t

/-- After the zeros to `out`. -/
def P2' (p : PP) (t : State) : Prop := ∃ s t₁, P0 p s ∧ EntryPost s t₁ ∧ Zeroed s t₁ t

/-- After the length check. -/
def P3 (p : PP) (t : State) : Prop := ∃ s, P0 p s ∧ Front s t

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal' (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

theorem entry_ct : RelCT isa (Two P0) (.block entry) (Two P2) :=
  two_piece [.x7] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (congrArg PP.B h₁.2).trans (congrArg PP.B h₂.2).symm)
    (by taint_decide) fun p s h => WP.mono (entry_ok (pctx_of h.1)) fun t he => ⟨s, h, he⟩

theorem zeros_ct : RelCT isa (Two P2) (zeroOut kOut kLen) (Two P2') :=
  pin_ct [.x0] [.x1, .x2] (fun p => zoVal' p.op p.L)
    (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.x0, h₂.x0, show σ₁.gpr .x7 = p.B from congrArg PP.B c₁.2, show σ₂.gpr .x7 = p.B from congrArg PP.B c₂.2])
    (by taint_decide)
    (fun p t ⟨s, c, he⟩ => by
      have k := pctx_of c.1
      have hs := k.hs.congr he.keep.wr
      have hn := hs.nowrap
      have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := k.dims.z
      have hL : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 := k.len
      have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (s.gpr .x7) (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hi])
      have hop : s.gpr .x0 = p.op := congrArg PP.op c.2
      have hpL : BitVec.ofNat 64 p.L = s.gpr .x1 := by
        rw [← c.2]; show BitVec.ofNat 64 (((s.gpr .x3).toNat + 7) / 8) = _; rw [← hL, ofNat_toNat64]
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.op ∧
          t'.gpr .x2 = BitVec.ofNat 64 p.L) (by
        brun [he.x0, hdr_enc (show kOut < 32 by decide), hdr_enc (show kLen < 32 by decide), hl kOut (by decide),
          hl kLen (by decide), he.args.out, he.args.len, hop, hpL]) (by decide) (by decide) (by decide +kernel))
        fun t' ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p t ⟨s, c, he⟩ => WP.mono (zeros_ok (pctx_of c.1) he) fun t' hz => ⟨s, t, c, he, hz⟩

theorem lenCheck_ct : RelCT isa (Two P2') (.block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag)) (Two P3) :=
  two_piece [.x0] (fun p s₁ s₂ ⟨σ₁, _, c₁, e₁, z₁⟩ ⟨σ₂, _, c₂, e₂, z₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [(z₁.keep.gpr .x0 (by decide)).trans e₁.x0, (z₂.keep.gpr .x0 (by decide)).trans e₂.x0,
      show σ₁.gpr .x7 = p.B from congrArg PP.B c₁.2, show σ₂.gpr .x7 = p.B from congrArg PP.B c₂.2])
    (by taint_decide) fun p t ⟨s, t₁, c, he, hz⟩ => WP.mono (lenCheck_ok (pctx_of c.1) he hz) fun t' hf => ⟨s, c, hf⟩

theorem P3.x5 {p : PP} {t : State} (h : P3 p t) :
    t.gpr .x5 = BitVec.ofNat 64 (decide (p.L ≤ p.r.length)).toNat := by
  obtain ⟨s, c, hf⟩ := h
  rw [hf.x5, ← c.2]
  have hL := (pctx_of c.1).len
  show _ = BitVec.ofNat 64 (decide ((ppOf s).L ≤ (pcRand s).length)).toNat
  rw [← hL, pcRand_length]

theorem P3.m0 {p : PP} {t : State} (h : P3 p t) (hb : isa.eval (.zero .x .x5) t = some false) : M0 p t := by
  have hx := h.x5
  obtain ⟨s, c, hf⟩ := h
  have k := pctx_of c.1
  rw [eval_zero, hx] at hb
  have hle : p.L ≤ p.r.length := by
    revert hb; cases hd : decide (p.L ≤ p.r.length)
    · intro hb; cases hb
    · intro _; simpa using hd
  have hL : (s.gpr .x1).toNat = (ppOf s).L := k.len
  rw [← c.2] at hle ⊢
  exact ⟨ph_of k hf, by show word t.mem (s.gpr .x7) _ = _; rw [hf.args.used, ← hL, ofNat_toNat64], hle⟩

/-- `vg_ffdh_parameter_candidate` leaks the same in runs with the same
public data. -/
theorem code_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two P0) (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) fun _ _ => True := by
  unfold VG.Impl.Ffdh.AArch64.ParameterCandidate.code
  simp only [seqs]
  refine RelCT.seq entry_ct (RelCT.seq zeros_ct (RelCT.seq lenCheck_ct ?_))
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.x5, h₂.x5]) ?_ ?_
  · have e : finNone = .block (([movi .x3 0, ldh .x2 kUsedP] : List Instr) ++ [st .x3 .x2, movi .x0 0]) := rfl
    rw [e]
    refine (RelCT.block_append (pin_ct (Ψ := fun _ _ => True) [.x0] [.x2] (fun p _ => p.up)
      (fun p s₁ s₂ ⟨⟨σ₁, c₁, f₁⟩, _⟩ ⟨⟨σ₂, c₂, f₂⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [f₁.x0, f₂.x0]; exact (congrArg PP.B c₁.2).trans (congrArg PP.B c₂.2).symm)
      (by taint_decide) ?_ (by taint_decide) ?_)).mono (fun _ _ h => h) fun _ _ _ => trivial
    · rintro p t ⟨⟨s, c, hf⟩, _⟩
      have k := pctx_of c.1
      have hph := ph_of k hf
      rw [c.2] at hph
      have hs := hph.scr
      have hn := hs.nowrap
      have hZ := hph.dims.z
      have hl : InRegions (t.rd ++ t.wr) (off p.B (8 * kUsedP)) 8 := hs.ld (by simp only [kUsedP, sFn, PP.L] at *; omega_using [hZ])
      refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = p.up) (by
        brun [hph.x0, hdr_enc (show kUsedP < 32 by decide), hl, hph.args.usedP]) (by decide) (by decide)
        (by decide +kernel)) fun t' h2 r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; exact h2.1
    · rintro p t ⟨⟨s, c, hf⟩, hb⟩
      have k := pctx_of c.1
      have hlt : (pcRand s).length < (s.gpr .x1).toNat := by
        have hx := (show P3 p t from ⟨s, c, hf⟩).x5
        rw [eval_zero, hx] at hb
        have hL := k.len
        rw [← c.2] at hb
        revert hb
        cases hd : decide ((ppOf s).L ≤ (ppOf s).r.length)
        · intro _; simp only [decide_eq_false_iff_not, Nat.not_le] at hd; rw [hL]; exact hd
        · intro hb; cases hb
      have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := k.dims.z
      exact WP.seq_iff.mpr (WP.block_append_iff.mp (WP.mono (finNone_ok (up := s.gpr .x2) (k.hs.congr hf.keep.wr)
        hf.x0 (show 8 * 32 ≤ (stackArg s 0).toNat * 8 by omega_using [hZ]) hf.args.usedP (k.ou.congr hf.keep.wr).upw)
        fun _ _ => trivial))
  · exact two_map id (fun p t h => h.1.m0 h.2) (main_ct M R)

theorem P0.self {s : State} (h : pcPre s) : P0 (ppOf s) s := ⟨h, rfl⟩

/-- Runs that agree on the public data agree on `ppOf`. -/
theorem ppOf_eq {s₁ s₂ : State} (hp : pcPub s₁ s₂) : ppOf s₂ = ppOf s₁ := by
  obtain ⟨_, hr, h0, h1, h2, h3, h4, h5, h6, h7, ha⟩ := hp
  have hrr : pcRand s₁ = pcRand s₂ := VG.Proof.RsaKeyGen.map_toNat_inj hr
  simp only [ppOf, ← h0, ← h2, ← h3, ← h4, ← h5, ← h7, ← ha, ← hrr]

/-- `vg_ffdh_parameter_candidate` is constant time: its leak depends only
on the public data. -/
theorem code_constantTime (M : Mont) (R : Kernel) :
    ConstantTime isa pcPre pcPub (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) :=
  RelCT.constantTime ((code_ct M R).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨ppOf s₁, P0.self h₁, ⟨h₂, ppOf_eq hp⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.ParameterCandidate
