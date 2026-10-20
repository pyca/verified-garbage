module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH key-generation attempts on x86-64: entry and modulus checks -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def gkOf (s : State) : GkP :=
  ⟨stackArg s 3, (stackArg s 4).toNat * 8, (stackArg s 0).toNat, (s.gpr .r9).toNat,
    s.gpr .r8, gkDom s, s.gpr .rdi, s.gpr .rdx, stackArg s 1, s.gpr .rsp,
    Spec.Ffdh.privateValid (gkA s) (gkS s)⟩

theorem entry_base {s : State} (c : GkCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) s fun t =>
      Base (gkOf s) (gkRand s) t ∧ t.gpr .rdi = (gkOf s).B ∧
      InScr (gkOf s).B (gkOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (gkOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (gkEntry_ok rfl (fun i hi => c.hs.st (by omega)) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (gkOf s).B (gkOf s).Z s.mem t.mem :=
    InScr.of_outside hf (by dsimp only [gkOf]; omega)
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, ?_, c.hZ, c.hs.congr k.2.2,
    c.dom.congrK hi k, c.rand.congrK hi k,
    ⟨fun i hi => by rw [k.2.2]; exact c.x.wr i hi, c.x.sep⟩,
    ⟨fun i hi => by rw [k.2.2]; exact c.y.wr i hi, c.y.sep⟩,
    c.xy, c.xd, c.xr, c.yd, c.yr, ?_, rfl⟩, hd, hi, hs, k.mono (by decide)⟩
  · change (gkRand s).length = (stackArg s 0).toNat
    rw [bytesAt_length, c.rl]
  · change Slots t.mem (stackArg s 3) (gkOf s).headers
    simp only [GkP.headers, gkOf, ofNat_toNat64]
    exact hh

theorem dom_base {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p rb t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [GkP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers])) (h.dom.take p.k) h.plen)
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
    simp only [GkP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega) (by unfold sG sFn; omega) (by unfold sQ sFn; omega)

end VG.Proof.Ffdh.X86_64.GenerateKey
