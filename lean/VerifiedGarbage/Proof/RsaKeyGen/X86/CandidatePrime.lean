module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # Accepted candidates export their prime and exact entropy consumption -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext

structure PrimeInput (base : Addr) (size w candidate : Nat) (out usedPtr count : BitVec 32) (s : State) : Prop where
  scratch : Scr s base size
  positive : 0 < w
  space : slot w 0 + 8 * w ≤ size
  header : 156 ≤ size
  outEq : s.mem.readW (off base 0) 32 = out
  lengthEq : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)
  usedEq : s.mem.readW (off base 44) 32 = usedPtr
  countEq : s.mem.readW (off base 152) 32 = count
  candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate
  outFit : out.toNat + 8 * w ≤ 2 ^ 32
  outWrite : InRegions s.wr (out.setWidth 64) (8 * w)
  usedWrite : Ws s (usedPtr.setWidth 64) 8
  workspaceFar : (⟨base, size⟩ : Region).Disjoint ⟨out.setWidth 64, 8 * w⟩
  usedFar : (⟨out.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨usedPtr.setWidth 64, 8⟩

theorem prime_ok {s : State} {base : Addr} {size w candidate : Nat} {out usedPtr count : BitVec 32}
    (S : PrimeInput base size w candidate out usedPtr count s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.prime w) s fun t =>
      t.gpr .eax = 1#32 ∧ Spec.Rsa.bytesAt t.mem (out.setWidth 64) (8 * w) = Spec.Rsa.i2osp candidate (8 * w) ∧
      t.mem.readW (usedPtr.setWidth 64) 64 = BitVec.ofNat 64 count.toNat ∧
      Frame [⟨out.setWidth 64, 8 * w⟩, ⟨usedPtr.setWidth 64, 8⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.prime
  refine WP.seq (wp_movS (readSrc_sc S.scratch (d := 0) (by have := S.header; omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.scratch.of_keeps A.keeps (by decide)) (d := 4) (by have := S.header; omega)) fun b B _ => WP.block_nil ?_)
  have Kb : Keeps [.ebx, .ecx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have outB : b.gpr .ebx = out := by rw [B.other .ebx (by decide), A.gpr, S.outEq]
  have lenB : b.gpr .ecx = BitVec.ofNat 32 (8 * w) := by rw [B.gpr, A.mem, S.lengthEq]
  have valueB : wordsVal b.mem base (slot w 0) w = candidate := by
    rw [wordsVal_eq_val32, Mb]; exact S.candidateEq
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.storeBE_ok (S.scratch.of_keeps Kb (by decide))
    (by have := S.positive; omega) (by rfl) S.space lenB
    (by rw [wordsVal_eq_val32, show 8 * (8 * w) = 32 * (2 * w) by omega]; exact val32_lt _ _ _ _)
    (by rw [outB]; exact S.outFit) (by rw [Kb.2.2, outB]; exact S.outWrite)
    (by
      rw [outB]
      exact Region.Disjoint.sub_left S.workspaceFar (Offset.sub_base base S.space)))
    fun c ⟨bytesC, Fc, Kc⟩ => ?_)
  rw [outB, valueB] at bytesC
  rw [outB, Mb] at Fc
  have Ksc : Keeps [.eax, .ebx, .ecx, .esi] s c := (Kb.mono (by decide)).widen Kc
  have readHeader (d : Nat) (fit : d + 4 ≤ size) : c.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
    Fc.readW (r := ⟨base, size⟩) (Offset.contains_base _ fit (by have := S.scratch.nowrap; omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.workspaceFar) (by decide)
  refine WP.mono (used_ok (status := 1) (S.scratch.of_keeps Ksc (by decide)) S.header
    (S.usedWrite.of_keeps Ksc) ((readHeader 44 (by have := S.header; omega)).trans S.usedEq)
    ((readHeader 152 (by have := S.header; omega)).trans S.countEq)) fun t ⟨result, memory, O, Kt⟩ => ?_
  have Ft : Frame [⟨usedPtr.setWidth 64, 8⟩] c.mem t.mem := by
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame O (by decide)
  refine ⟨result, ?_, ?_, ?_, (Ksc.mono (by decide)).trans (Kt.mono (by decide))⟩
  · rw [VG.Proof.RsaKeyGen.frame_bytesAt Ft (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.usedFar)
      (by have := S.outFit; omega)]
    exact bytesC
  · rw [memory, Mem.readW_writeW_self64]
  · exact (Fc.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans
      (Ft.mono (fun _ mem => List.mem_cons_of_mem _ mem))

end VG.Proof.RsaKeyGen.X86.CandidateFinish
