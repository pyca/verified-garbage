module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Context
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Data
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange

import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH exchange on x86-64: entry and modulus validation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def exOf (s : State) : ExP :=
  ⟨stackArg s 3, (stackArg s 4).toNat * 8, (s.gpr .r8).toNat, (s.gpr .rcx).toNat, s.gpr .rdx,
    exDom s, s.gpr .rdi, s.gpr .r9, (stackArg s 0).toNat, stackArg s 1, exY s, s.gpr .rsp⟩

theorem entry_base {s : State} (c : ExCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.entry) s fun t =>
      Base (exOf s) (exX s) t ∧ t.gpr .rdi = (exOf s).B ∧
      InScr (exOf s).B (exOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (exOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exEntry_ok rfl (fun i hi => c.hs.st (by omega)) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (exOf s).B (exOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [exOf]; omega)
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, ?_, bytesAt_length _ _ _,
    c.xl1, c.xl2, c.hZ, c.hs.congr k.2.2, c.dom.congrK hi k, c.x.congrK hi k, c.y.congrK hi k,
    ?_, (fun i hi => by rw [k.2.2]; exact c.out i hi), c.sep⟩, hd, hi, hs, k.mono (by decide)⟩
  · change (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat).length = (s.gpr .r8).toNat
    rw [bytesAt_length, c.yl]
  · change Slots t.mem (stackArg s 3) (exOf s).headers
    simp only [ExP.headers, exOf, ofNat_toNat64]
    intro e he
    apply hh e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem dom_base {p : ExP} {xb : List Byte} {s : State} (h : Base p xb s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p xb t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [ExP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers])) (h.dom.take p.k) h.plen)
    fun t ⟨hz, _, _, hf, hd, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega)
  have hh : ∀ i < 32, i ≠ sG → i ≠ sQ → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hg hq => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega) (by omega)
  refine ⟨h.keep hi k ?_, hz, hd, hi, ?_, k.mono (by decide)⟩
  · intro e he
    simp only [ExP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega) (by unfold sG sFn; omega) (by unfold sQ sFn; omega)

end VG.Proof.Ffdh.X86_64.Exchange
