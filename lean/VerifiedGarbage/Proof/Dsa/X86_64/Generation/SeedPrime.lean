module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBody
import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInvariant
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeIteration
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.X86_64.Generation.SeedGenerator`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.Generation.SeedValidate`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.Generation.SeedPack`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.Generation.Pack`, which only this module used -/

section

/-! # Pack all three generated parameters into p || q || g -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PackInto.lean`, which only this module imported.
section

/-! # Pack a component into a bounded domain buffer, preserving all sources -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem packInto_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src d total : Nat} {bs : List Byte}
    (hs : src < 2 ^ 31) (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (ht : total ≤ 1024) (hroom : d + bs.length ≤ total)
    (source : Src s (off (W 5) packed) total (off (W 5) src) bs)
    (hwr : ∀ i < total, InRegions s.wr (off (off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨off (W 5) packed, total⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨off (W 5) packed, total⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.packPart src (packed + d) bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (off (off (W 5) packed) d) bs.length = bs ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨off (off (W 5) packed) d, bs.length⟩] s.mem t.mem ∧
      InScr (off (W 5) packed) total s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hd : packed + d < 2 ^ 31 := by unfold packed; omega
  have sub : Region.Sub ⟨off (off (W 5) packed) d, bs.length⟩ ⟨off (W 5) packed, total⟩ :=
    Offset.sub_base _ hroom
  refine WP.mono (packPart_ok L R hs hd hl source.rd
    (fun i hi => by rw [← off_off, off_off]; exact hwr (d + i) (by omega))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using source.val i hi)
    (by
      intro i hi j hj he
      have hout := source.out i hi
      change total ≤ ofs (off (W 5) packed) (off (off (W 5) src) i) at hout
      rw [he, ← off_off, off_off] at hout
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : d + j < 2 ^ 64)] at hout
      omega)
    (by rw [← off_off]; exact hF.sub_right sub)
    (by rw [← off_off]; exact hS.sub_right sub)) fun t ⟨result, Lt, Rt, ft, kt⟩ => ?_
  have frame : Frame [⟨off (off (W 5) packed) d, bs.length⟩] s.mem t.mem := by
    simpa only [off_off] using ft
  refine ⟨by simpa only [off_off] using result, Lt, Rt, frame, ?_, kt⟩
  intro a ha
  apply frame a
  intro r hr hc
  rcases List.mem_singleton.mp hr with rfl
  have inside := sub a hc
  change ofs (off (W 5) packed) a + 1 ≤ total at inside
  omega

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem pack_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {pb qb gb : List Byte} {pLen qLen : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hp : pb.length = pLen) (hq : qb.length = qLen) (hg : gb.length = pLen)
    (hl : 2 ≤ pLen ∧ 2 ≤ qLen ∧ 2 * pLen + qLen ≤ 1024)
    (sp : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sq : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) q) qb)
    (sg : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) g) gb)
    (hwr : ∀ i < 2 * pLen + qLen, InRegions s.wr (off (off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.pack pLen qLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (off (W 5) packed) (2 * pLen + qLen) = pb ++ qb ++ gb ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨off (W 5) packed, 2 * pLen + qLen⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.pack
  change WP isa (.seq _ (.seq _ _)) s _
  have first := packInto_ok (d := 0) L R (by decide : Impl.Dsa.Generation.Layout.p < 2 ^ 31)
    (by omega_using [hp, hl]) hl.2.2 (by omega_using [hp]) sp hwr hF hS
  simp only [Nat.add_zero, hp] at first
  refine WP.seq (WP.mono first fun u ⟨bu, Lu, Ru, _, fu, ku⟩ => ?_)
  have second := packInto_ok (d := pLen) Lu Ru (by decide : q < 2 ^ 31)
    (by omega_using [hq, hl]) hl.2.2 (by omega_using [hq]) (sq.congrK fu ku)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi) hF hS
  simp only [hq] at second
  refine WP.seq (WP.mono second fun v ⟨bv, Lv, Rv, fv, iv, kv⟩ => ?_)
  have third := packInto_ok (d := pLen + qLen) Lv Rv (by decide : g < 2 ^ 31)
    (by omega_using [hg, hl]) hl.2.2 (by omega_using [hg]) (sg.congrK (fu.trans iv) (ku.trans kv))
    (fun i hi => by rw [kv.2.2, ku.2.2]; exact hwr i hi) hF hS
  simp only [hg] at third
  simp only [Impl.Bignum.X86_64.seqs, Nat.add_assoc]
  refine WP.mono third fun t ⟨bt, Lt, Rt, ft, it, kt⟩ => ?_
  have keep := (ku.trans kv).trans kt
  have inside := (fu.trans iv).trans it
  refine ⟨?_, Lt, Rt, ?_, keep.mono (by decide)⟩
  · have preserveP : Spec.Rsa.bytesAt t.mem (off (W 5) packed) pLen = pb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])) (by omega_using [hl]),
        VG.Proof.Dsa.Generation.frame_bytesAt fv (by
          intro r hr; rcases List.mem_singleton.mp hr with rfl
          exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])) (by omega_using [hl])]
      simpa [off] using bu
    have preserveQ : Spec.Rsa.bytesAt t.mem (off (off (W 5) packed) pLen) qLen = qb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.disjoint _ (Or.inl (by omega_using [])) (by omega_using [hl]) (by omega_using [hl])) (by omega_using [hl])]
      exact bv
    rw [show 2 * pLen + qLen = (pLen + qLen) + pLen by omega_using [],
      VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
      preserveP, preserveQ, bt]
  · intro a ha
    apply inside a
    have hn := ha ⟨off (W 5) packed, 2 * pLen + qLen⟩ (by simp)
    change ¬ ofs (off (W 5) packed) a < 2 * pLen + qLen at hn
    omega_using [hn]

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Pack the accepted native buffers while preserving the seed-search state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem seedPack_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (pb qb gb : List Byte)
    (hp : pb.length = p.geo.pLen) (hq : qb.length = p.geo.qLen) (hg : gb.length = p.geo.pLen)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = pb)
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = qb)
    (bg : Spec.Rsa.bytesAt s.mem (off p.geo.B g) p.geo.pLen = gb) :
    WP isa (Impl.Dsa.X86_64.Generation.pack p.geo.pLen p.geo.qLen) s fun t =>
      GenerationMemory p W t ∧
      Spec.Rsa.bytesAt t.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = pb ++ qb ++ gb ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : 2 ≤ p.geo.qLen ∧ p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have packedBound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have src (d : Nat) (bs : List Byte) (hd : d + bs.length ≤ packed)
      (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B d) bs.length = bs) :
      Src s (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) (off p.geo.B d) bs := by
    have bound : d + bs.length ≤ usedBytes p.geo.pLen := by omega_using [packedBound, hd]
    apply arena_source h.scratch bound (by unfold packed at hd; omega_using [hd]) bytes
    exact p.geo.parts_disjoint bound packedBound (Or.inl hd)
  obtain ⟨V, R⟩ := h.rep
  have call := pack_ok h.layout R hp hq hg ⟨pn.1, qn.1, by omega_using [pn, qn]⟩
  rw [h5] at call
  refine WP.mono (call
    (src VG.Impl.Dsa.Generation.Layout.p pb (by rw [hp]; unfold VG.Impl.Dsa.Generation.Layout.p packed; omega_using [pn]) (by simpa only [hp] using bp))
    (src q qb (by rw [hq]; unfold q packed; omega_using [qn]) (by simpa only [hq] using bq))
    (src g gb (by rw [hg]; unfold g packed; omega_using [pn]) (by simpa only [hg] using bg))
    (by intro i hi; rw [off_off]; exact h.scratch.region (by omega_using [packedBound, hi]) (by decide))
    (p.geo.frame_part packedBound) (p.geo.parts_disjoint hh packedBound (Or.inl (by decide))))
    fun t ⟨bytes, Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_parts ft
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub packedBound⟩
  exact ⟨h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) ff kt.2.1 kt.2.2, bytes, ff, kt.2.1, kt.2.2⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Apply the final domain check without leaving the native seed controller -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Validate.lean`, which only this module imported.
section

/-! # Domain-check results control native seed retry or acceptance -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

theorem validate_ok (M : Mont) (Sq : MontS) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 32) (hq : p.qLen < 2 ^ 32)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hstack : (below F 8).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hparams : (below F 8).Disjoint ⟨off (W 5) packed, p.params.length⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.validate (checkName := checkName) Sq.mm M.mm p.pLen p.qLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd W 19 (BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 3))) ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.validate
  refine WP.seq (WP.mono (validateCore_ok (checkName := checkName) M Sq p L R hbase hp hq hs src hF hS hstack hparams)
    fun u ⟨hr, Lu, Ru, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (validateTest_ok hr) fun v ⟨hz, hm, kv⟩ => ?_)
  have Rv : Rep v.mem F S V W := hm ▸ Ru
  have Lv := lay_of_rep Lu Ru Rv rfl (kv.gpr (by decide)) kv.2.2
  have fv : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8, ⟨F, frameBytes⟩] s.mem v.mem := by
    rw [hm]
    exact fu.mono (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)
  have finish (status : Nat) (hstatus : status < 2 ^ 32) :
      WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) v fun t =>
        Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) ∧
        Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, below F 8, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
    refine WP.mono (stackStatus_ok Lv Rv status hstatus) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    refine ⟨Lt, Rt, fv.trans ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
    intro a ha
    apply ft a
    right
    have hn := ha ⟨F, frameBytes⟩ (by simp)
    change ¬ ofs F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  cases hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params with
  | false =>
    refine WP.ite true (by simp [eval, hz, hc]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hc, Bool.false_eq_true, ite_false] using finish 3 (by decide)
  | true =>
    refine WP.ite false (by simp [eval, hz, hc]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simpa only [hc, ite_true] using finish 1 (by decide)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

theorem GenerationGeometry.validLengths (p : GenerationGeometry) : Spec.Dsa.lengthsValid p.pLen p.qLen := by
  rcases p.lengths with h | h | h <;> simp [Spec.Dsa.lengthsValid, h.1, h.2]

def GenerationGeometry.parametersInput (p : GenerationGeometry) (params : List Byte)
    (hlen : params.length = 2 * p.pLen + p.qLen) : ParametersInput :=
  ⟨off p.B domainCheck, p.pLen, p.qLen, params, p.validLengths, hlen⟩

theorem seedValidate_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (params : List Byte) (hlen : params.length = 2 * p.geo.pLen + p.geo.qLen)
    (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = params) :
    WP isa (Impl.Dsa.X86_64.Generation.validate (checkName := checkName) Sq.mm M.mm p.geo.pLen p.geo.qLen) s fun t =>
      GenerationMemory p (upd W 19 (BitVec.ofNat 64
        (if Spec.Dsa.checkParametersBytes p.geo.pLen p.geo.qLen params then 1 else 3))) t ∧
      Spec.Rsa.bytesAt t.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = params ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have arena : domainCheck + Impl.Dsa.Layout.usedBytes ≤ usedBytes p.geo.pLen := by
    rcases p.geo.width with hh | hh | hh <;> rw [hh] <;> decide
  have packedBound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have sep := p.geo.parts_disjoint packedBound arena (Or.inl (by unfold packed domainCheck; omega_using [pn, qn]))
  have source : Src s (off p.geo.B domainCheck) Impl.Dsa.Layout.usedBytes (off p.geo.B packed) params := by
    apply arena_source h.scratch
    · simpa only [hlen] using packedBound
    · rw [hlen]; omega_using [pn, qn]
    · simpa only [hlen] using bytes
    · simpa only [hlen, GenerationGeometry.part] using sep
  obtain ⟨V, R⟩ := h.rep
  have call := validate_ok (checkName := checkName) M Sq (p.geo.parametersInput params hlen) h.layout R
    (by change off p.geo.B domainCheck = off (W 5) domainCheck; rw [h5])
    (by change p.geo.pLen < 2 ^ 32; omega_using [pn]) (by change p.geo.qLen < 2 ^ 32; omega_using [qn])
    (h.scratch.sub (n := Impl.Dsa.Layout.usedBytes) arena (by decide))
  rw [h5] at call
  refine WP.mono (call source (p.geo.frame_part arena) (p.geo.parts_disjoint hh arena (Or.inl (by decide)))
    ((p.geo.stack_part arena).sub_left (below_sub (by decide) (by decide)))
    (by change (below p.geo.F 8).Disjoint ⟨off p.geo.B packed, params.length⟩
        rw [hlen]
        exact (p.geo.stack_part packedBound).sub_left (below_sub (by decide) (by decide))))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_parts ft
    intro r hr
    change r ∈ [⟨off p.geo.B domainCheck, Impl.Dsa.Layout.usedBytes⟩, below p.geo.F 8, ⟨p.geo.F, frameBytes⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub arena⟩
    · exact ⟨below p.geo.F 192, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
    · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩
  refine ⟨h.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2, ?_, ff, kt.2.1, kt.2.2⟩
  · intro k hk
    have hn : k ≠ 19 := by simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
    simp [upd, hn]
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr
      change r ∈ [⟨off p.geo.B domainCheck, Impl.Dsa.Layout.usedBytes⟩, below p.geo.F 8, ⟨p.geo.F, frameBytes⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sep
      · exact ((p.geo.stack_part packedBound).sub_left (below_sub (by decide) (by decide))).symm
      · exact (p.geo.frame_part packedBound).symm) (by omega_using [pn, qn])]
    exact bytes

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.TapeLoop`, which only this module used -/

section

/-! # Termination of native seed and generator tape searches -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

/-- The body provides algorithm-specific progress; the tape controller
owns complete-chunk selection, cursor advancement, and loop termination. -/
structure TapeDriver (slots : TapeSlots) (F S : Addr) (width total : Nat)
    (body : Prog isa) (I : Nat → State → Prop) (Q : State → Prop) : Prop where
  baseBound : slots.base < 37
  totalBound : slots.total < 37
  usedBound : slots.used < 37
  pointerBound : slots.pointer < 37
  usedNotScratch : slots.used ≠ 14
  pointerNotScratch : slots.pointer ≠ 14
  widthBound : width < 2 ^ 31
  widthPositive : 0 < width
  totalFits : total < 2 ^ 64
  stable : ∀ n, TapeStable (I n)
  finish : TapeStable Q
  view : ∀ n s, I n s → TapeView slots F S n total s
  done : ∀ used s t V W, I used s → total - used < width →
    Lay s F S → Rep s.mem F S V W →
    Lay t F S → Rep t.mem F S V (upd W 19 3) →
    Outside F 152 8 s.mem t.mem → Keep [.rax] s t → Q t
  step : ∀ used s t V W, I used s → width ≤ total - used →
    Lay s F S → Rep s.mem F S V W → W slots.used = BitVec.ofNat 64 used →
    Lay t F S → Rep t.mem F S V
      (upd (upd W slots.pointer (off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) →
    Frame [⟨F, frameBytes⟩] s.mem t.mem → Keep [.rax, .rcx] s t →
    WP isa body t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧
      (if W' 19 = 3 then I (used + width) u else Q u)

theorem TapeDriver.loop_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {used : Nat} (hle : used ≤ total) (hi : I used s) :
    WP isa (.loop (tapeIteration slots width body) .e) s Q := by
  exact WP.loop
    (fun n t => ∃ used, n = total - used + 1 ∧ used ≤ total ∧ I used t)
    (fun n t ⟨u, hn, hu, hit⟩ =>
      WP.mono (tapeIteration_ok d.baseBound d.totalBound d.usedBound d.pointerBound
        d.usedNotScratch d.pointerNotScratch d.widthBound d.totalFits
        d.stable d.finish d.view (d.done u) (d.step u) hu hit)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hbound⟩ =>
          ⟨hz, total - (u + width) + 1, by omega_using [d.widthPositive, hn, hu, hbound],
            u + width, rfl, hbound, hi'⟩)
    (total - used + 1) s ⟨used, rfl, hle, hi⟩

/-- Resetting the cursor makes each generator search reuse the original h
tape, and each top-level call begin at the first seed. -/
theorem TapeDriver.run_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (start : ∀ t, Lay t F S → Rep t.mem F S V (upd W slots.used 0) →
      Outside F (8 * slots.used) 8 s.mem t.mem → Keep [.rax] s t → I 0 t) :
    WP isa (tapeLoop slots width body) s Q := by
  unfold tapeLoop
  refine WP.seq (WP.mono (tapeReset_ok L R slots d.usedBound d.usedNotScratch)
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_)
  exact d.loop_ok (Nat.zero_le _) (start t Lt Rt ft kt)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Complete generator search on an accepted native p candidate -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ContextGeneratorFrame.lean`, which only this module imported.
section

/-! # Generator writes preserve the outer seed state and saved q -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem GenerationContext.generator_frame {p : GenerationContext} {m m' : Mem}
    (hf : Frame p.geo.gWork m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_parts hf
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with h | h | h <;> omega
  have part (d n : Nat) (bound : d + n ≤ usedBytes p.geo.pLen) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub bound⟩
  intro r hr
  simp only [GenerationGeometry.gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact part arithmetic arithmeticBytes (p.geo.small_bound (by decide) (by rfl))
  · simpa [GenerationGeometry.part, off] using part 0 Impl.Dsa.Layout.activeBytes (by simpa using p.geo.parentRoom)
  · exact part g p.geo.pLen (p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

theorem GenerationGeometry.generator_q {p : GenerationGeometry} {m m' : Mem}
    (hf : Frame p.gWork m m') :
    Spec.Rsa.bytesAt m' (off p.B q) p.qLen = Spec.Rsa.bytesAt m (off p.B q) p.qLen := by
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  exact VG.Proof.Dsa.Generation.frame_bytesAt hf
    (p.gWork_separate (d := q) (n := p.qLen) (by rfl) (by unfold q g; omega)) (by omega)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorBody.lean`, which only this module imported.
section

/-! # A consumed h chunk either finishes or advances the exact generator search -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generator_body_ok (M : Mont) (Sq : MontS)
    {p : GeneratorSearchPlan} {expected : Option Nat} {final : Nat} {initial : State}
    {used : Nat} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (hi : GeneratorInvariant p expected final initial used s) (room : used + p.core.len ≤ p.tape.length)
    (R : Rep s.mem p.core.F p.core.S V W)
    (Lt : Lay t p.core.F p.core.S)
    (Rt : Rep t.mem p.core.F p.core.S V
      (upd (upd W 21 (off (W 11) used)) 20 (BitVec.ofNat 64 (used + p.core.len))))
    (ft : Frame [⟨p.core.F, frameBytes⟩] s.mem t.mem) (kt : Keep [.rax, .rcx] s t) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorStep Sq.mm M.mm p.core.len) t fun u =>
      ∃ V' W', Lay u p.core.F p.core.S ∧ Rep u.mem p.core.F p.core.S V' W' ∧
        (if W' 19 = 3 then GeneratorInvariant p expected final initial (used + p.core.len) u
          else GeneratorFinished p expected final initial u) := by
  obtain ⟨Wi, h, _, he, hcount, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 37, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  let Wt := upd (upd W 21 (off (W 11) used)) 20 (BitVec.ofNat 64 (used + p.core.len))
  have ff : Frame p.core.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  have ht : GeneratorSearchMemory p Wt t := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Wt, upd] <;> exact words _ (by decide)) ff kt.2.1 kt.2.2
  have hc := ht.chunk room (by
    change Wt 21 = off p.tapePtr used
    simp [Wt, upd, words 11 (by decide), h.tapeBase])
  refine WP.mono (generatorStep_ok M Sq (p := p.chunk used room) hc) fun u ⟨hu, hg, fu, ku⟩ => ?_
  let Wu := upd Wt 19 (if (p.chunk used room).accepts then 1 else 3)
  have mem : GeneratorSearchMemory p Wu u := ht.frame hu.layout hu.rep (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) fu ku.2.1 ku.2.2
  have frame := (fi.trans ff).trans fu
  have rd := ku.2.1.trans (kt.2.1.trans ri)
  have wr := ku.2.2.trans (kt.2.2.trans wi)
  have rem := he.trans (p.remaining_step room)
  have cnt := hcount.trans (congrArg (used + p.core.len * ·) (p.count_step room))
  have h20 : Wu 20 = BitVec.ofNat 64 (used + p.core.len) := by simp [Wu, Wt, upd]
  obtain ⟨Vu, Ru⟩ := mem.rep
  refine ⟨Vu, Wu, mem.layout, Ru, ?_⟩
  by_cases accepted : (p.chunk used room).accepts
  · have h19 : Wu 19 = 1 := by simp [Wu, upd, accepted]
    rw [ite_eq_right (by rw [h19]; decide)]
    rw [ite_eq_left accepted, Nat.mul_one] at cnt
    exact ⟨Wu, mem, cnt ▸ h20, Or.inr ⟨(p.chunk used room).value, h19,
      by simpa only [accepted, ite_true] using rem, hg accepted⟩, frame, rd, wr⟩
  · have h19 : Wu 19 = 3 := by simp [Wu, upd, accepted]
    rw [ite_eq_left h19]
    rw [ite_eq_right accepted, Nat.mul_succ] at cnt
    exact ⟨Wu, mem, h20,
      by simpa only [accepted, ite_false] using rem, by omega, frame, rd, wr⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/NativeGenerator.lean`, which only this module imported.
section

/-! # Complete native generator search against the byte-tape specification -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86_64.Generation (generatorTape)

theorem nativeGenerator_ok (M : Mont) (Sq : MontS)
    {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorSearchMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.core.len) s
      (GeneratorFinished p (p.remaining 0) (p.core.len * p.count 0) s) := by
  let I := GeneratorInvariant p (p.remaining 0) (p.core.len * p.count 0) s
  let Q := GeneratorFinished p (p.remaining 0) (p.core.len * p.count 0) s
  have hw : 0 < p.core.len ∧ p.core.len < 2 ^ 31 := by
    rcases p.core.width with hh | hh | hh <;> omega
  have driver : TapeDriver generatorTape p.core.F p.core.S p.core.len p.tape.length
      (Impl.Dsa.X86_64.Generation.generatorStep Sq.mm M.mm p.core.len) I Q :=
    { baseBound := by decide
      totalBound := by decide
      usedBound := by decide
      pointerBound := by decide
      usedNotScratch := by decide
      pointerNotScratch := by decide
      widthBound := hw.2
      widthPositive := hw.1
      totalFits := p.tapeFits
      stable := generatorInvariant_stable p (p.remaining 0) _ s
      finish := generatorFinished_stable p (p.remaining 0) _ s
      view := by
        rintro used t ⟨Wt, ht, h20, _, _, _, _, _⟩
        obtain ⟨Vt, Rt⟩ := ht.rep
        exact ⟨Vt, Wt, ht.layout, Rt, h20, ht.tapeLength⟩
      done := by
        intro used u v Vt Wt hi hex _ R Lu Ru fu ku
        exact generator_done hi hex R Lu Ru fu ku
      step := by
        intro used u v Vt Wt hi hav _ R _ Lv Rv fv kv
        exact generator_body_ok M Sq hi (by omega) R Lv Rv fv kv }
  obtain ⟨V, R⟩ := h.rep
  apply driver.run_ok h.layout R
  intro t Lt Rt ft kt
  have ff : Frame p.core.changed s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.core.F, frameBytes⟩ (by simp [GeneratorPlan.changed])
    change ¬ ofs p.core.F a < frameBytes at hn
    change 168 ≤ ofs p.core.F a
    unfold frameBytes at hn
    omega
  refine ⟨upd W 20 0, h.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2,
    by simp [upd], rfl, (Nat.zero_add _).symm, ff, kt.2.1, kt.2.2⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem seedGenerator_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.geo.pLen) s fun t =>
      let result := Spec.Dsa.generator value qval
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE)
      ∃ W', GenerationMemory p W' t ∧ (∀ k ∈ generatorSlots, W' k = W k) ∧
        W' 20 = BitVec.ofNat 64 (p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE)) ∧
        Spec.Rsa.bytesAt t.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value ∧
        Spec.Rsa.bytesAt t.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval ∧
        ((W' 19 = 3 ∧ result = none) ∨
         ∃ gv, W' 19 = 1 ∧ result = some gv ∧ 1 < gv ∧ gv < value ∧
           Spec.Rsa.bytesAt t.mem (off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen gv) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  have decode := VG.Proof.Dsa.decodeBE_encodeBE fit
  have expFit : (value - 1) / qval < 256 ^ p.geo.pLen :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) fit
  have expDecode := VG.Proof.Dsa.decodeBE_encodeBE expFit
  have positive : 1 < Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value) := by
    rw [decode]; omega_using [domain.large]
  have odd : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value) % 2 = 1 := by rw [decode]; exact domain.odd
  have exponentValue : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval)) =
      (Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value) - 1) / qval := by rw [decode, expDecode]
  let a := p.generatorPlan W _ _ (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) positive odd qval exponentValue
  have state := h.generatorState _ _ (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _)
    positive odd qval exponentValue bp be
  have remaining : a.remaining 0 = Spec.Dsa.generator value qval
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) := by
    change Spec.Dsa.generator (Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value)) qval
      ((Spec.Dsa.generationChunks p.geo.pLen (p.hs.bytes.drop 0)).map Spec.Dsa.decodeBE) = _
    rw [decode, List.drop_zero]
  have count : a.core.len * a.count 0 = p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) := by
    change p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount
      (Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value)) qval
      ((Spec.Dsa.generationChunks p.geo.pLen (p.hs.bytes.drop 0)).map Spec.Dsa.decodeBE) = _
    rw [decode, List.drop_zero]
  refine WP.mono (nativeGenerator_ok M Sq state) fun t ⟨Wt, mt, h20, result, ft, rd, wr⟩ => ?_
  have fg : Frame p.geo.gWork s.mem t.mem := ft
  have ff := p.generator_frame fg
  have slots : ∀ k ∈ generatorSlots, Wt k = W k := mt.slots
  have mem := h.frame mt.layout mt.rep (fun k hk => slots k (by
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [generatorSlots])) ff rd wr
  refine ⟨Wt, mem, slots, count ▸ h20, ?_, (p.geo.generator_q fg).trans bq, ?_, ff, rd, wr⟩
  · have bytes := source_octets mt.pArithmetic
    change Spec.Rsa.bytesAt t.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p)
      (Spec.Dsa.encodeBE p.geo.pLen value).length = Spec.Dsa.encodeBE p.geo.pLen value at bytes
    simpa only [VG.Proof.Dsa.encodeBE_length] using bytes
  · rcases result with fail | ⟨gv, h19, hr, bg⟩
    · exact Or.inl ⟨fail.1, remaining ▸ fail.2⟩
    · have hr' := remaining ▸ hr
      have bounds := VG.Proof.Dsa.Generation.generator_bounds (by omega_using [domain.large]) _ hr'
      exact Or.inr ⟨gv, h19, hr', bounds.1, bounds.2, bg⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.HashChoice`, which this module and modules that import it used -/

section

/-! # One hash selection shared by the subgroup and prime searches -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Pbkdf2.Md.X86_64

def GenerationHashes.streamOK (H : GenerationHashes) (len : Nat) :
    Calls.StreamOK (if len = 20 then H.sha1 else H.sha256) where
  SH := if len = 20 then H.h1.SH else H.h256.SH
  Wb := if len = 20 then H.h1.Wb else H.h256.Wb
  hS := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hS
    · simpa [h] using H.h256.hS
  hD := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hD
    · simpa [h] using H.h256.hD
  hB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hB
    · simpa [h] using H.h256.hB
  hDF := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hDF
    · simpa [h] using H.h256.hDF
  hF := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hF
    · simpa [h] using H.h256.hF
  hD0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hD0
    · simpa [h] using H.h256.hD0
  hS0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hS0
    · simpa [h] using H.h256.hS0
  hSB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hSB
    · simpa [h] using H.h256.hSB
  hB0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hB0
    · simpa [h] using H.h256.hB0
  hBB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hBB
    · simpa [h] using H.h256.hBB
  hWb := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hWb
    · simpa [h] using H.h256.hWb
  hW := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hW
    · simpa [h] using H.h256.hW
  repr := by
    by_cases h : len = 20
    · simpa [h] using H.h1.repr
    · simpa [h] using H.h256.repr
  init := by
    by_cases h : len = 20
    · simpa [h] using H.h1.init
    · simpa [h] using H.h256.init
  upd := by
    by_cases h : len = 20
    · simpa [h] using H.h1.upd
    · simpa [h] using H.h256.upd
  fin := by
    by_cases h : len = 20
    · simpa [h] using H.h1.fin
    · simpa [h] using H.h256.fin
  initDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.initDepth
    · simpa [h] using H.h256.initDepth
  updDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.updDepth
    · simpa [h] using H.h256.updDepth
  finDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.finDepth
    · simpa [h] using H.h256.finDepth
  initSp := by
    by_cases h : len = 20
    · simpa [h] using H.h1.initSp
    · simpa [h] using H.h256.initSp
  updSp := by
    by_cases h : len = 20
    · simpa [h] using H.h1.updSp
    · simpa [h] using H.h256.updSp
  finSp := by
    by_cases h : len = 20
    · simpa [h] using H.h1.finSp
    · simpa [h] using H.h256.finSp

def generationHash (len : Nat) : Spec.Mgf1.Hash :=
  if len = 20 then Spec.Mgf1.sha1 else Spec.Mgf1.sha256

theorem GenerationHashes.hash_matches (H : GenerationHashes) (len : Nat) :
    ∀ x, (generationHash len).hash x = (H.streamOK len).SH.H.hash x := by
  intro x
  by_cases h : len = 20
  · simpa [generationHash, GenerationHashes.streamOK, h] using H.hash1 x
  · simpa [generationHash, GenerationHashes.streamOK, h] using H.hash256 x

theorem GenerationHashes.hash_size (H : GenerationHashes) (len : Nat) :
    ∀ x, ((generationHash len).hash x).length = (if len = 20 then H.sha1 else H.sha256).D := by
  intro x
  unfold generationHash
  split
  · exact H.size1 x
  · exact H.size256 x

theorem GenerationHashes.hash_width (H : GenerationHashes) {len : Nat} (hw : len = 20 ∨ len = 32) :
    (if len = 20 then H.sha1 else H.sha256).D = len := by
  rcases hw with rfl | rfl
  · simpa using H.width1
  · simpa using H.width256

theorem generationHash_seed {len : Nat} (hw : len = 20 ∨ len = 32) (bs : List Byte) :
    (generationHash len).hash bs = Spec.Dsa.seedHash (8 * len) bs := by
  rcases hw with rfl | rfl <;> rfl

theorem GenerationHashes.seed_size (H : GenerationHashes) {len : Nat} (hw : len = 20 ∨ len = 32)
    (bs : List Byte) : 8 * (Spec.Dsa.seedHash (8 * len) bs).length = 8 * len := by
  rw [← generationHash_seed hw, H.hash_size, H.hash_width hw]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The full p search returns to the persistent seed-search state -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ContextSearchFrame.lean`, which only this module imported.
section

/-! # Lift the bounded prime search back to the persistent generation state -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem GenerationMemory.search_frame {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h1 : W 1 = seed.ptr) {m m' : Mem}
    (hf : Frame (searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C) m m') :
    Frame p.changed m m' := by
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have writes : searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C =
      p.geo.part VG.Impl.Dsa.Generation.Layout.control 24 :: ⟨p.geo.F, frameBytes⟩ :: p.geo.pWork := by
    dsimp only [searchWrites, GenerationMemory.searchPlan, GenerationGeometry.searchPlan,
      PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed,
      HashPlan.changed, GenerationGeometry.primalityPlan, GenerationGeometry.constructPlan,
      GenerationGeometry.hashPlan, searchWords, upd]
    rw [h5]
    rfl
  rw [writes] at hf
  apply GenerationContext.frame_parts hf
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have part (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed],
      p.geo.part_sub (p.geo.small_bound hd hn)⟩
  intro r hr
  simp only [GenerationGeometry.pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part VG.Impl.Dsa.Generation.Layout.control 24 (by decide) (by decide)
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact part shaped p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part hashes ((p.geo.count + 1) * p.geo.qLen) (by decide)
      (by have := p.geo.hashSizes.2.1; unfold arithmeticBytes; omega)
  · exact part wrappedSeed p.geo.qLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part VG.Impl.Dsa.Generation.Layout.hash oRsa (by decide) (by decide)
  · exact ⟨below p.geo.F 192, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part VG.Impl.Dsa.Generation.Layout.p p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part exponent p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part witness p.geo.pLen (by decide) (by unfold arithmeticBytes; omega)
  · exact ⟨below p.geo.F 192, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SearchSemantics.lean`, which only this module imported.
section

/-! # Match each native body result to the reviewed p-search recursion -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

def SearchPlan.remaining (p : SearchPlan) (counter used : Nat) : Option (Option Nat × List Byte) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * p.attempt.construct.len) (8 * p.attempt.construct.hash.len)
    (Spec.Rsa.os2ip p.attempt.construct.qb) p.attempt.construct.hash.seed counter (p.attempt.rand.drop used)

theorem SearchPlan.stepCursor {p : SearchPlan} {counter used : Nat} {b : Bool} {rest : List Byte}
    (h : p.stepResult counter used = some (b, rest)) :
    p.attempt.rand.drop (p.attempt.rand.length - rest.length) = rest := by
  unfold SearchPlan.stepResult at h
  split at h
  · cases h
    apply VG.Proof.Dsa.Generation.suffix_drop_length
    exact List.drop_suffix _ _
  · exact VG.Proof.Dsa.Generation.probablePrime_cursor h

theorem SearchPlan.remaining_step {p : SearchPlan} {counter used : Nat}
    (hc : counter < 32 * p.attempt.construct.len) :
    p.remaining counter used =
      match p.stepResult counter used with
      | none => none
      | some (true, rest) => some (some (p.candidate counter), rest)
      | some (false, rest) => p.remaining (counter + 1) (p.attempt.rand.length - rest.length) := by
  have hc' : counter < 4 * (8 * p.attempt.construct.len) := by omega
  unfold SearchPlan.remaining
  rw [VG.Proof.Dsa.Generation.primeSearch_step _ _ hc']
  rw [← p.attempt.construct.hashCount]
  change (if p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1) then _ else _) = _
  by_cases hs : p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1)
  · simp only [hs, ite_true, SearchPlan.stepResult]
    rw [VG.Proof.Dsa.Generation.suffix_drop_length (List.drop_suffix used p.attempt.rand)]
  · simp only [hs, ite_false, SearchPlan.stepResult]
    rcases hp : Spec.Dsa.probablePrime (p.candidate counter) (p.attempt.rand.drop used) with _ | ⟨b, rest⟩
    · simp only [SearchPlan.candidate] at hp
      rw [hp]
    · have hp' := hp
      simp only [SearchPlan.candidate] at hp'
      rw [hp']
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        rw [VG.Proof.Dsa.Generation.probablePrime_cursor hp]
      · rfl

theorem SearchPlan.remaining_done (p : SearchPlan) (used : Nat) :
    p.remaining (32 * p.attempt.construct.len) used = some (none, p.attempt.rand.drop used) :=
  VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SearchInvariant.lean`, which only this module imported.
section

/-! # The p-search invariant retains its exact specification result -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def SearchOutcome (p : SearchPlan) (res : Option (Option Nat × List Byte))
    (W : Nat → BitVec 64) (used : Nat) (t : State) : Prop :=
  (W 19 = BitVec.ofNat 64 0 ∧ res = none) ∨
  (W 19 = BitVec.ofNat 64 1 ∧ ∃ value,
    res = some (some value, p.attempt.rand.drop used) ∧
    Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len value ∧
    Spec.Rsa.bytesAt t.mem (off (p.attempt.construct.hash.W 5) exponent) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len ((value - 1) / Spec.Rsa.os2ip p.attempt.construct.qb)) ∨
  (W 19 = BitVec.ofNat 64 3 ∧ res = some (none, p.attempt.rand.drop used))

def SearchInvariant (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State)
    (counter : Nat) (t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (0 < counter → W 19 = BitVec.ofNat 64 3) ∧ res = p.remaining counter used ∧
    Frame (searchWrites p.attempt p.C) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

def SearchFinished (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    SearchOutcome p res W used t ∧ Frame (searchWrites p.attempt p.C) s.mem t.mem ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem controller_frame {C : Addr} {m m' : Mem} (hf : Outside C 0 24 m m') : Frame [⟨C, 24⟩] m m' := by
  intro a ha
  apply hf a
  right
  have hn := ha ⟨C, 24⟩ (by simp)
  change ¬ ofs C a < 24 at hn
  omega

theorem searchInvariant_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) (c : Nat) :
    SearchPayload p.C (SearchInvariant p res s c) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  exact ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, h19, hr,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.2.1.trans rd, hk.2.2.trans wr⟩

theorem searchFinished_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) :
    SearchPayload p.C (SearchFinished p res s) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, ho, ff, rd, wr⟩ := h
  refine ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, ?_,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.2.1.trans rd, hk.2.2.trans wr⟩
  rcases ho with ho | ⟨h19, value, hr, hp, he⟩ | ho
  · exact Or.inl ho
  · refine Or.inr (Or.inl ⟨h19, value, hr, ?_, ?_⟩)
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.pControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega), hp]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.exponentControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega), he]
  · exact Or.inr (Or.inr ho)

theorem searchInvariant_done {p : SearchPlan} {res : Option (Option Nat × List Byte)} {s t : State}
    (h : SearchInvariant p res s (32 * p.attempt.construct.len) t) : SearchFinished p res s t := by
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  refine ⟨W, used, hm, hu, h16, Or.inr (Or.inr ⟨h19 ?_, ?_⟩), ff, rd, wr⟩
  · rcases p.attempt.construct.width with hh | hh | hh <;> omega
  · exact hr.trans (p.remaining_done used)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/NativeSearch.lean`, which only this module imported.
section

/-! # Complete native bounded p search against the specification -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64

theorem nativeSearch_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream} {p : SearchPlan}
    (hG : Calls.StreamOK (if p.attempt.construct.hash.len = 20 then G1 else G256))
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.attempt.construct.hash.len = 20 then G1 else G256).D)
    (T : PrimeTest)
    (hd : (if p.attempt.construct.hash.len = 20 then G1 else G256).D = p.attempt.construct.hash.len)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs).length = 8 * p.attempt.construct.hash.len)
    {s : State} {W : Nat → BitVec 64} {used : Nat} (h : SearchMemory p W s)
    (hC : Scr s p.C 24) (hused : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.attempt.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSearch G1 G256 T.run
      p.attempt.construct.len p.attempt.construct.hash.len) s
      (SearchFinished p (p.remaining 0 used) s) := by
  have hlimit : 0 < 32 * p.attempt.construct.len ∧ 32 * p.attempt.construct.len ≤ 12288 := by
    rcases p.attempt.construct.width with hh | hh | hh <;> omega
  have hstride : p.attempt.construct.hash.count + 1 ≤ 12 := by
    have := p.attempt.construct.hash.count_le; omega
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.X86_64.Generation.primeSearch
  rw [← p.attempt.construct.hashCount]
  refine WP.seq (WP.mono (controlBase_ok (B := p.C) h.layout R (by
    rw [h.slots 5 (by simp [searchSlots])]; exact p.controlBase)) fun u ⟨udi, um, ku⟩ => ?_)
  have Ru : Rep u.mem p.attempt.construct.hash.F p.attempt.construct.hash.S V W := um ▸ R
  have Lu := lay_of_rep h.layout R Ru rfl (ku.gpr (by decide)) ku.2.2
  have fu : Frame (searchWrites p.attempt p.C) s.mem u.mem := by rw [um]; exact Frame.refl _ _
  have mu := h.frame Lu ⟨V, Ru⟩ (fun _ _ => rfl) fu ku.2.1 ku.2.2
  apply pSearch_ok hlimit.2 hlimit.1 hstride
    (searchInvariant_stable p (p.remaining 0 used) s) (searchFinished_stable p (p.remaining 0 used) s)
    (fun t ht _ _ => searchInvariant_done ht)
    (fun c v hc hi ctrl => ?_)
    (show SearchInvariant p (p.remaining 0 used) s 0 u from
      ⟨W, used, mu, hu, hused, by omega, rfl, fu, ku.2.1, ku.2.2⟩)
    (hC.congr ku.2.2) udi
  obtain ⟨Wv, usedv, mv, huv, h16v, _, hremaining, fv, rdv, wrv⟩ := hi
  refine WP.mono (searchBody_ok hG hHh hsize T hd hhash hseedsize mv ctrl hc h16v huv)
    fun t ⟨ct, Wt, usedt, status, mt, hut, h16t, h19t, hct, bp, be, he, hr, ft, rdt, wrt⟩ => ?_
  have frame := fv.trans ft
  have rd := rdt.trans rdv
  have wr := wrt.trans wrv
  have step := hremaining.trans (p.remaining_step hc)
  rcases result : p.stepResult c usedv with _ | ⟨b, rest⟩
  · have hs := he result
    rw [result] at step
    refine ⟨ct, 0, by decide, hct.trans hs, ?_⟩
    change SearchFinished p (p.remaining 0 used) s t
    exact ⟨Wt, usedt, mt, hut, h16t, Or.inl ⟨h19t.trans hs, step⟩, frame, rd, wr⟩
  · obtain ⟨hs, hcursor⟩ := hr b rest result
    rw [result] at step
    cases b with
    | false =>
      refine ⟨ct, 3, by decide, hct.trans hs, ?_⟩
      change SearchInvariant p (p.remaining 0 used) s (c + 1) t
      refine ⟨Wt, usedt, mt, hut, h16t, fun _ => h19t.trans hs, ?_, frame, rd, wr⟩
      rw [hcursor]
      exact step
    | true =>
      refine ⟨ct, 1, by decide, hct.trans hs, ?_⟩
      change SearchFinished p (p.remaining 0 used) s t
      refine ⟨Wt, usedt, mt, hut, h16t, Or.inr (Or.inl ⟨h19t.trans hs, p.candidate c, ?_, bp, be⟩), frame, rd, wr⟩
      rw [hcursor, p.stepCursor result]
      exact step

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64

theorem GenerationGeometry.qDecode (p : GenerationGeometry) (seed : List Byte) :
    Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.qLen (Spec.Dsa.qCandidate (8 * p.qLen) seed)) =
      Spec.Dsa.qCandidate (8 * p.qLen) seed := by
  rw [← VG.Proof.Dsa.decodeBE_os2ip]
  apply VG.Proof.Dsa.decodeBE_encodeBE
  have h := (VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases p.qWidth with hh | hh <;> omega_using [hh] : 2 ≤ 8 * p.qLen) seed).2.2
  simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using h

theorem seedPrime_ok (H : GenerationHashes) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSearch H.sha1 H.sha256 T.run p.geo.pLen p.geo.qLen) s fun t =>
      let res := Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
        (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes (p.rand.bytes.drop used)
      ∃ W' used', used' ≤ p.rand.bytes.length ∧ GenerationMemory p W' t ∧
        W' 16 = BitVec.ofNat 64 used' ∧
        (∀ k ∈ searchSlots, W' k = W k) ∧
        Spec.Rsa.bytesAt t.mem (off p.geo.B q) p.geo.qLen =
          Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) ∧
        ((W' 19 = 0 ∧ res = none) ∨
         (W' 19 = 1 ∧ ∃ value, res = some (some value, p.rand.bytes.drop used') ∧
           VG.Proof.Dsa.Generation.PDomain p.geo.pLen value ∧
           Spec.Rsa.bytesAt t.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value ∧
           Spec.Rsa.bytesAt t.mem (off p.geo.B exponent) p.geo.pLen =
             Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)) ∨
         (W' 19 = 3 ∧ res = some (none, p.rand.bytes.drop used'))) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let a := h.searchPlan seed hlen h1
  have state := h.searchState seed hlen hseed h1 hq
  have hw : a.attempt.construct.hash.len = 20 ∨ a.attempt.construct.hash.len = 32 := p.geo.qWidth
  have hc := h.scratch.sub (n := 24) (p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.control)
    (n := 24) (by decide) (by decide)) (by decide)
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have qdecode := p.geo.qDecode seed.bytes
  have remaining : a.remaining 0 used = Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
      (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes (p.rand.bytes.drop used) := by
    change VG.Proof.Dsa.Generation.primeSearch _ _ _ _ 0 _ = _
    rw [VG.Proof.Dsa.Generation.primeSearch_start]
    change Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
      (Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)))
      seed.bytes (p.rand.bytes.drop used) = _
    rw [qdecode]
  refine WP.mono (nativeSearch_ok (H.streamOK _) (H.hash_matches _) (H.hash_size _) T
    (H.hash_width hw) (generationHash_seed hw) (H.seed_size hw) state hc h16 hu)
    fun t ⟨Wt, usedt, mt, hut, h16t, outcome, ft, rd, wr⟩ => ?_
  have ff := h.search_frame seed hlen h1 ft
  have slots : ∀ k ∈ searchSlots, Wt k = W k := by
    intro k hk
    have he := mt.slots k hk
    change Wt k = searchWords p.geo.B W k at he
    have hn : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 27 := by simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
    simpa [searchWords, upd, hn.1, hn.2.1, hn.2.2] using he
  have mem := h.frame mt.layout mt.rep (fun k hk => slots k (by
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [searchSlots])) ff rd wr
  refine ⟨Wt, usedt, hut, mem, h16t, slots, ?_, ?_, ff, rd, wr⟩
  · have bytes := source_octets mt.qSource
    change Spec.Rsa.bytesAt t.mem (off (W 5) q) (Spec.Dsa.encodeBE p.geo.qLen
      (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)).length =
        Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) at bytes
    simpa only [h5, VG.Proof.Dsa.encodeBE_length] using bytes
  · rcases outcome with ⟨h19, hr⟩ | ⟨h19, value, hr, bp, be⟩ | ⟨h19, hr⟩
    · exact Or.inl ⟨h19, remaining ▸ hr⟩
    · refine Or.inr (Or.inl ⟨h19, value, remaining ▸ hr, ?_, ?_, ?_⟩)
      · apply VG.Proof.Dsa.Generation.primeSearch_domain p.geo.width (H.seed_size p.geo.qWidth) seed.bytes
          (List.range (4 * (8 * p.geo.pLen))) (p.rand.bytes.drop used) (p.rand.bytes.drop usedt)
        exact remaining ▸ hr
      · change Spec.Rsa.bytesAt t.mem (off (W 5) VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value at bp
        simpa only [h5] using bp
      · change Spec.Rsa.bytesAt t.mem (off (W 5) exponent) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.geo.qLen
            (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))) at be
        simpa only [h5, qdecode] using be
    · exact Or.inr (Or.inr ⟨h19, remaining ▸ hr⟩)
end VG.Proof.Dsa.X86_64.Generation
