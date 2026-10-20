module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# An FFDH parameter candidate on AArch64: correctness

`code`, from a state `pcContract` allows, ends as `parameterCandidate`
(`code_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkedCandidate)

/-- The postcondition, from how the candidate ended after the entry and the
zeros to `out` (at `t₃`). -/
theorem pcEnd_post {s t₃ t : State} (c : PCtx s)
    (hz : ∀ i < (s.gpr .x1).toNat, t₃.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0)
    (kk : Keep (.x0 :: mmRegs) s t₃)
    (h : PEnd t₃ t (ppOf s) (checkedCandidate (ppOf s).bits (ppOf s).g (ppOf s).r)) :
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
    · rw [hk.x0, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
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
  rw [← VG.Proof.Ffdh.ParameterCandidate.checkedCandidate_eq]
  change PEnd t₃ t (ppOf s) (checkedCandidate (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32).toNat (pcRand s)) at h
  have hrl : (pcRand s).length = (s.gpr .x6).toNat := pcRand_length s
  rcases hres : checkedCandidate (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32).toNat (pcRand s) with
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
  exact WP.mono (zeroOut_ok (len := (s.gpr .x1).toNat) (hs.congr he.keep.wr) he.x0 (by omega) (sPtr := kOut)
    (sLen := kLen) (by decide) (by decide) he.args.out (by rw [he.args.len, ofNat_toNat64]) (by omega) (by omega)
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
    rw [← he', ofs_off _ (by omega)] at this; omega

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
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (s.gpr .x7) (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
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
    fun x hx hx' => by rw [hm4, hz.frame x hx', he.out x (Or.inr (by omega))],
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

/-- `vg_ffdh_parameter_candidate` ends as the specification says. -/
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
    refine WP.mono (finNone_ok (up := s.gpr .x2) hph.scr hph.x0 (show 8 * 32 ≤ (stackArg s 0).toNat * 8 by omega)
      hf.args.usedP hph.ou.upw)
      fun t ht => pcEnd_post c hf.zero hf.keep ?_
    have hnone : checkedCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = none := by
      show checkedCandidate (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32).toNat (pcRand s) = none
      unfold checkedCandidate
      have hs : (pcRand s).length < ((s.gpr .x3).toNat + 7) / 8 := by rw [hrl]; omega
      rw [VG.Proof.Ffdh.ParameterCandidate.draw_of_short hs]
      rfl
    rw [hnone]
    exact KEnd.of_fin hph.ou ht
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hlt
    have hL : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 := c.len
    refine WP.mono (main_ok M R hph (by
        show word t₄.mem (s.gpr .x7) _ = BitVec.ofNat 64 (((s.gpr .x3).toNat + 7) / 8)
        rw [hf.args.used, ← hL, ofNat_toNat64])
      (by show ((s.gpr .x3).toNat + 7) / 8 ≤ (pcRand s).length; rw [hrl]; omega))
      fun t ht => pcEnd_post c hf.zero hf.keep ht

end VG.Proof.Ffdh.AArch64.ParameterCandidate
