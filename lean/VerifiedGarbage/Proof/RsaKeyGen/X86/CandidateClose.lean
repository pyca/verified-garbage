module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateCloseOther
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClose
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # The optional-prime branch performs exactly the specified distance check -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateClose
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

theorem code_ok {s : State} {base : Addr} {size w candidate : Nat} {p plen : BitVec 32}
    (S : Scr s base size) (width : 4 ≤ w) (header : 28 ≤ size)
    (space : slot w 4 + 8 * w ≤ size)
    (candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate)
    (pointer : s.mem.readW (off base 20) 32 = p)
    (lengthEq : s.mem.readW (off base 24) 32 = plen)
    (source : plen ≠ 0#32 → p.toNat + 8 * w ≤ 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w) ∧
      (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨base, size⟩) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateClose.code w) s fun t =>
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * w)
        (if plen = 0#32 then none else some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w)))) candidate) ∧
      Outs base [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateClose.code
  refine WP.seq (wp_movS (readSrc_sc S (d := 24) (by omega)) fun a A _ =>
    wp_cmpS rfl fun b B Z => WP.block_nil ?_)
  have K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have M : b.mem = s.mem := B.mem.trans A.mem
  have condition : isa.eval .e b = some (decide (plen = 0#32)) := by
    change b.zf = _
    rw [Z, A.gpr, lengthEq]
    change some (plen - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]
    rfl
  by_cases absent : plen = 0#32
  · refine WP.ite true (by rw [condition, decide_eq_true absent]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    refine ⟨?_, ?_, (K.mono (by decide)).widen T.keeps⟩
    · rw [T.gpr]
      simp only [absent, ↓reduceIte, Spec.RsaKeyGen.tooClose, Near.bit, Bool.toNat_false]
      rfl
    · rw [T.mem, M]
      exact Outs.refl _ _ _
  · refine WP.ite false (by rw [condition, decide_eq_false absent]) (fun impossible => nomatch impossible) (fun _ => ?_)
    obtain ⟨fit, readable, separate⟩ := source absent
    refine WP.mono (other_ok (candidate := candidate) (S.of_keeps K (by decide)) width (by omega) space
      (by rw [M]; exact candidateEq) (by rw [M]; exact pointer) fit
      (by rw [K.2.1, K.2.2]; exact readable) separate) fun t ⟨result, O, Kt⟩ => ?_
    rw [M] at result O
    exact ⟨by simpa only [absent, ↓reduceIte] using result, O, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.CandidateClose
