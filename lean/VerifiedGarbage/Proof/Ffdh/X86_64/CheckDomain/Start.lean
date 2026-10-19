module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Context
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH domain validation on x86-64: save arguments and check p -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem entry_base {s : State} (c : CdCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry) s fun t =>
      Base (cdOf s) t ∧ t.gpr .rdi = (cdOf s).B ∧ InScr (cdOf s).B (cdOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (cdOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (cdEntry_ok rfl (fun i hi => c.scr.st (by omega)))
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (cdOf s).B (cdOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [cdOf]; omega)
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, c.hZ, c.scr.congr k.2.2, c.dom.congrK hi k,
    ?_⟩, hd, hi, hs, k.mono (by decide)⟩
  change Slots t.mem (s.gpr .rcx) (cdOf s).headers
  simp only [CdP.headers, cdOf, ofNat_toNat64]
  exact hh

theorem dom_base {p : CdP} {s : State} (h : Base p s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [CdP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) (h.dom.take p.k) h.plen)
    fun t ⟨hz, hG, hQ, hf, hd, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega)
  have hh : ∀ i < 32, i ≠ sG → i ≠ sQ → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hg hq => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega) (by omega)
  refine ⟨h.keep hi k ?_, hz, hd, hG, hQ, hi, ?_, k.mono (by decide)⟩
  · intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega) (by unfold sG sFn; omega) (by unfold sQ sFn; omega)

end VG.Proof.Ffdh.X86_64.CheckDomain
