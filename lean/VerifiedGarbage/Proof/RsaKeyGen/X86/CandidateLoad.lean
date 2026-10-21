module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadCount
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateImport
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateLoad

/-! # Candidate entry imports exactly the first entropy block and records its length -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateLoad
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

theorem code_ok {s : State} {base : Addr} {size w : Nat} {rand : BitVec 32}
    (S : Scr s base size) (positive : 0 < w) (header : 160 ≤ size)
    (space : slot w 0 + 8 * w ≤ size) (sourceFit : rand.toNat + 8 * w ≤ 2 ^ 32)
    (sourceEq : s.mem.readW (off base 28) 32 = rand)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) (8 * w))
    (separate : (⟨rand.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨base, size⟩) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateLoad.code w) s fun t =>
      val32 t.mem base (slot w 0) (2 * w) = Spec.RsaKeyGen.candidate (64 * w)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (rand.setWidth 64) (8 * w))) ∧
      word t.mem base 152 = BitVec.ofNat 64 (8 * w) ∧
      Frame [⟨off base (slot w 0), 8 * w⟩, ⟨off base 152, 8⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateLoad.code
  refine WP.seq (wp_movS (readSrc_sc S (d := 28) (by omega)) fun a A _ => WP.block_nil ?_)
  have Sa := S.of_keeps A.keeps (by decide)
  have context : Import.Context ⟨rand, a.gpr .edi + BitVec.ofNat 32 (slot w 0), 2 * w⟩ a :=
    Import.context_workspace Sa (by omega) (by omega) (by omega)
      (by rw [A.keeps.2.1, A.keeps.2.2, show 4 * (2 * w) = 8 * w by omega]; exact readable)
      (by rw [show 4 * (2 * w) = 8 * w by omega]; exact separate)
  refine WP.seq (WP.mono (CandidateImport.code_ok Sa positive space context rfl
    (by rw [A.gpr, sourceEq]) rfl) fun b ⟨candidate, Fb, Kb⟩ => ?_)
  rw [A.mem] at candidate Fb
  have Sb := Sa.of_keeps Kb (by decide)
  have slotLo : 256 ≤ slot w 0 := by change 256 ≤ 256 + 0 * stride w; omega
  refine WP.mono (count_ok Sb header (by have := S.nowrap; omega)) fun t ⟨count, O, Kt⟩ => ?_
  have kept : val32 t.mem base (slot w 0) (2 * w) = val32 b.mem base (slot w 0) (2 * w) :=
    O.val32 (Or.inr (by omega)) (by have := S.nowrap; omega)
  have Ft := VG.Proof.Bignum.outside_frame O (by decide)
  refine ⟨kept.trans candidate, count, ?_, (A.keeps.mono (by decide)).trans (Kb.widen Kt)⟩
  exact (Fb.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans
    (Ft.mono (fun _ mem => List.mem_cons_of_mem _ mem))

end VG.Proof.RsaKeyGen.X86.CandidateLoad
