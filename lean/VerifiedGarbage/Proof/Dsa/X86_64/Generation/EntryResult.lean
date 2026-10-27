module
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryBody
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySavedFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInitial
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc

/-! # Byte-level results at the public parameter-generation boundary -/

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
