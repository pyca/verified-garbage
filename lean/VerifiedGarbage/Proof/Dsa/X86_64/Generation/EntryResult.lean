module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInitial
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Generate
import VerifiedGarbage.Proof.Dsa.Generation.ByteResult
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeParameters
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryReady
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Dispatch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIContext
/-! # Byte-level results at the public parameter-generation boundary -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/OutputZero.lean`, which only this module imported.
section

/-! # Every failed search zeros the complete output and returns zero -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

theorem outputZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {len : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 len)
    (hl : 0 < len ∧ len ≤ 1024) (hw : (⟨W 6, len⟩ : Region) ∈ s.wr)
    (hb : (W 6).toNat + len ≤ 2 ^ 64) (ha : Apart F S ⟨W 6, len⟩) :
    WP isa Impl.Dsa.X86_64.Generation.outputZero s fun t =>
      t.gpr .rax = 0 ∧ Spec.Rsa.bytesAt t.mem (W 6) len = List.replicate len 0 ∧
      Frame [⟨F, frameBytes⟩, ⟨W 6, len⟩] s.mem t.mem ∧ Keep [.rdi, .r10, .rax, .r8] s t := by
  unfold Impl.Dsa.X86_64.Generation.outputZero
  refine WP.seq (WP.mono (zeroArgs_ok L R) fun u ⟨Lu, Ru, fu, ku⟩ => ?_)
  refine WP.mono (zeroOut_ok Lu Ru (by simp [upd]) (by simpa [upd] using hlen) hl.1 hl.2
    (by rw [ku.2.2]; exact hw) hb ha) fun t ⟨_, kt, _, hr, bytes, ft⟩ => ?_
  refine ⟨hr, bytes, ?_, (ku.trans kt).mono (by decide)⟩
  exact (fu.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp)).trans
    (ft.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp))

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FinishOutput.lean`, which only this module imported.
section

/-! # Normalize every search outcome to the public output and status convention -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem finishOutput_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (expected : Option Spec.Dsa.Params)
    (result : (((W 19 = 0 ∨ W 19 = 3) ∧ expected = none) ∨
      (W 19 = 1 ∧ ∃ a, expected = some a ∧
        Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a))) :
    WP isa Impl.Dsa.X86_64.Generation.finishOutput s fun t =>
      t.gpr .rax = (if expected.isSome then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        (expected.map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen)).getD
          (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame [⟨p.geo.F, frameBytes⟩, ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧
      Keep (.rdi :: mmRegs) s t := by
  have pn : 0 < p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.X86_64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok h.layout R) fun u ⟨hz, hm, ku⟩ => ?_)
  have mu := h.congr hm ku
  have hwu : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ u.wr := by rw [ku.2.2]; exact hw
  rcases result with ⟨h19, he⟩ | ⟨h19, a, he, bytes⟩
  · have hn : W 19 ≠ 1 := by rcases h19 with hh | hh <;> rw [hh] <;> decide
    refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr hn])
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    obtain ⟨Vu, Ru⟩ := mu.rep
    have h6 := mu.slots 6 (by simp [generationSlots])
    have h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    have call := outputZero_ok mu.layout Ru h7 ⟨by omega, by omega⟩
    rw [h6] at call
    refine WP.mono (call hwu o.bound o.apart) fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    exact ⟨hr, bt, by simpa only [hm] using ft, (ku.trans kt).mono (by decide)⟩
  · refine WP.ite true (by simp only [eval, hz, h19, beq_self_eq_true])
      (fun _ => ?_) (fun impossible => Bool.noConfusion impossible)
    have bytesu : Spec.Rsa.bytesAt u.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := hm ▸ bytes
    refine WP.mono (output_copy_context mu o hwu _ (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytesu)
      fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    refine ⟨hr, bt, ?_, (ku.trans kt).mono (by decide)⟩
    rw [hm] at ft
    exact ft.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Generate.lean`, which only this module imported.
section

/-! # The native search and output implement the reviewed byte-level generator -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem generate_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (h16 : W 16 = 0) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (seedLength : p.seeds.bytes.length % p.geo.qLen = 0)
    (hLength : p.hs.bytes.length % p.geo.pLen = 0) :
    WP isa (Impl.Dsa.X86_64.Generation.generate (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run p.geo.pLen p.geo.qLen) s fun t =>
      let result := Spec.Dsa.generateParametersBytes p.geo.pLen p.geo.qLen p.seeds.bytes p.hs.bytes p.rand.bytes
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        result.getD (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame (p.changed ++ [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩]) s.mem t.mem ∧
      t.gpr .rsp = s.gpr .rsp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have specification : Spec.Dsa.generateParametersBytes p.geo.pLen p.geo.qLen p.seeds.bytes p.hs.bytes p.rand.bytes =
      (p.remaining 0 0).map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen) := by
    rw [VG.Proof.Dsa.Generation.generateParametersBytes_attempt p.geo.lengths _ _ _ seedLength hLength]
    simp only [GenerationContext.remaining, List.drop_zero]
  unfold Impl.Dsa.X86_64.Generation.generate
  refine WP.seq (WP.mono (nativeParameters_ok (checkName := checkName) H M Sq T h (randUsed := 0) h16 (Nat.zero_le _))
    fun u ⟨Wu, mu, result, fu, ru, wu⟩ => ?_)
  refine WP.mono (finishOutput_ok mu o (by rw [wu]; exact hw) (p.remaining 0 0) result)
    fun t ⟨status, bytes, ft, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, kt.2.1.trans ru, kt.2.2.trans wu⟩
  · rw [specification]
    cases he : p.remaining 0 0 <;> simpa [he, Spec.Dsa.signStatus] using status
  · rw [specification]
    exact bytes
  · exact (fu.mono (by intro r hr; exact List.mem_append_left _ hr)).trans (ft.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_append_left _ (by simp [GenerationContext.changed])
      · exact List.mem_append_right _ (by simp)))
  · exact (kt.gpr (by decide)).trans (mu.layout.rsp.trans h.layout.rsp.symm)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryBody.lean`, which only this module imported.
section

/-! # The initialized and size-dispatched ABI body implements parameter generation -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem entryBody_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {s : State} (h : EntryState p s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (seedLength : p.seeds.bytes.length % p.geo.qLen = 0)
    (hLength : p.hs.bytes.length % p.geo.pLen = 0) :
    WP isa (Impl.Dsa.X86_64.Generation.entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) s fun t =>
      let result := Spec.Dsa.generateParametersBytes p.geo.pLen p.geo.qLen p.seeds.bytes p.hs.bytes p.rand.bytes
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        result.getD (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame (p.changed ++ [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩]) s.mem t.mem ∧
      t.gpr .rsp = s.gpr .rsp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.entryBody
  refine WP.seq (WP.mono (entryReady_ok h) fun u ⟨W, mu, h16, fu, ku⟩ => ?_)
  apply dispatch_ok (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run mu
  intro v mv hm kv
  refine WP.mono (generate_ok (checkName := checkName) H M Sq T mv h16 o (by rw [kv.2.2, ku.2.2]; exact hw) seedLength hLength)
    fun t ⟨status, bytes, ft, rsp, rd, wr⟩ => ?_
  refine ⟨status, bytes, ?_, ?_, rd.trans (kv.2.1.trans ku.2.1), wr.trans (kv.2.2.trans ku.2.2)⟩
  · have fv : Frame p.changed s.mem v.mem := by rw [hm]; exact fu
    exact (fv.mono (by intro r hr; exact List.mem_append_left _ hr)).trans ft
  · exact rsp.trans ((kv.gpr (by decide)).trans (ku.gpr (by decide)))

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntrySavedFrame.lean`, which only this module imported.
section

/-! # Search workspaces cannot overwrite the saved calling-convention registers -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem savedBase_eq (s : State) : savedBase s = off (generationBase s) 296 := by
  simp only [savedBase, generationBase, off]
  bv_omega

theorem saved_disjoint {s : State} (h : GenerationABI s) :
    ∀ r ∈ (contextOf h).changed ++ [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩],
      (⟨savedBase s, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [GenerationContext.changed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact (h.stackScratch.sub_left (saved_frame_sub s)).sub_right (generation_scratch_sub h)
  · change (⟨savedBase s, 48⟩ : Region).Disjoint ⟨generationBase s, frameBytes⟩
    rw [savedBase_eq]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · change (⟨savedBase s, 48⟩ : Region).Disjoint (below (generationBase s) 192)
    rw [savedBase_eq]
    exact Offset.disjoint_below _ (by decide)
  · exact h.stackOut.sub_left (saved_frame_sub s)

theorem saved_across_generator {s u t : State} (h : GenerationABI s)
    (saved : Saved u.mem (savedBase s) s.gpr spillSlots)
    (hf : Frame ((contextOf h).changed ++ [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]) u.mem t.mem) :
    Saved t.mem (savedBase s) s.gpr spillSlots := by
  apply saved.frame hf
  intro p hp r hr
  exact (saved_disjoint h r hr).sub_left (Offset.sub_base _ (spillSlots_fit p hp))

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

def abiResult (s : State) : Option (List Byte) :=
  Spec.Dsa.generateParametersBytes (s.gpr .rdx).toNat (s.gpr .rcx).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)

structure EntryResult (s t : State) : Prop where
  status : t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus (abiResult s))
  bytes : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    (abiResult s).getD (List.replicate (s.gpr .rsi).toNat 0)

theorem EntryResult.congr {s t u : State} (h : EntryResult s t)
    (hr : u.gpr .rax = t.gpr .rax) (hm : u.mem = t.mem) : EntryResult s u :=
  ⟨hr.trans h.status, by rw [hm]; exact h.bytes⟩

theorem EntryResult.free {s t : State} (h : EntryResult s t) (n : Nat) :
    EntryResult s (freeState n t) := h.congr rfl rfl

theorem entryBody_abi (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {s u : State} (h : GenerationABI s)
    (hg : u.gpr = (allocState 48 s).gpr) (hr : u.rd = s.rd)
    (hw : u.wr = (allocState 48 s).wr)
    (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem)
    (saved : Saved u.mem (savedBase s) s.gpr spillSlots) :
    WP isa (Impl.Dsa.X86_64.Generation.entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run)
      (allocState 296 u) fun t =>
      EntryResult s t ∧ Saved t.mem (savedBase s) s.gpr spillSlots ∧
      t.gpr .rsp = (allocState 296 u).gpr .rsp ∧ t.rd = u.rd ∧ t.wr = (allocState 296 u).wr := by
  have init := entryInitial h hg hr hw hf
  have output : (⟨(contextOf h).saved 6, 2 * (contextOf h).geo.pLen + (contextOf h).geo.qLen⟩ : Region)
      ∈ (allocState 296 u).wr := by
    change (⟨s.gpr .rdi, 2 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat⟩ : Region) ∈ _
    rw [← h.outLength]
    change _ ∈ _ :: u.wr
    apply List.mem_cons_of_mem
    rw [hw]
    change _ ∈ _ :: s.wr
    apply List.mem_cons_of_mem
    rw [h.wr]; simp
  have seeds : (contextOf h).seeds.bytes.length % (contextOf h).geo.qLen = 0 := by
    simpa only [contextOf, tapeOf, geometryOf, bytesAt_length] using h.seedsLength
  have hs : (contextOf h).hs.bytes.length % (contextOf h).geo.pLen = 0 := by
    simpa only [contextOf, tapeOf, geometryOf, bytesAt_length] using h.hsLength
  apply WP.mono (entryBody_ok (checkName := checkName) H M Sq T init (outputPlanOf h) output seeds hs)
  intro t ⟨status, bytes, ft, sp, rd, wr⟩
  have outlen : 2 * (contextOf h).geo.pLen + (contextOf h).geo.qLen = (s.gpr .rsi).toNat := h.outLength.symm
  rw [outlen] at bytes ft
  exact ⟨⟨status, bytes⟩, saved_across_generator h saved ft, sp, rd, wr⟩

end VG.Proof.Dsa.X86_64.Generation
