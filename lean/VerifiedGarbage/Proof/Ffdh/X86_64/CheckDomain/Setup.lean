module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Data

import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: initialize p's workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The p workspace, retaining its public domain pointers. -/
structure Work (p : CdP) (mi : BitVec 64) (s : State) : Prop where
  base : Base p s
  mem : SubMem s p.B p.Z (inner p.w) p.w p.w mi
  xv : XVals s p.B (inner p.w) p.w mi p.P
  ws : word s.mem p.B (8 * sWs) = off p.B (inner p.w)
  g : word s.mem p.B (8 * sG) = off p.dp p.k
  q : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

/-- Each arithmetic stage changes only scratch and preserves the six saved registers. -/
def StepPost (p : CdP) (s : State) (P : State → Prop) (t : State) : Prop :=
  P t ∧ InScr p.B p.Z s.mem t.mem ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t

theorem StepPost.trans {p : CdP} {P Q : State → Prop} {s t u : State}
    (h : StepPost p s P t) (h' : StepPost p t Q u) : StepPost p s Q u :=
  ⟨h'.1, h.2.1.trans h'.2.1, fun i hi => (h'.2.2.1 i hi).trans (h.2.2.1 i hi),
    keep_trans h.2.2.2 h'.2.2.2⟩

theorem setup_work {p : CdP} {s : State} (h : Base p s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      (StepPost p s fun t => ∃ mi, Work p mi t ∧ t.gpr .rdi = off p.B (inner p.w)) := by
  have hk := h.k1
  have hZ := h.hZ
  refine WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb)
    h.scr hd h.k1 h.k2 h.hZ (h.hdr (sDom, p.dp) (by simp [CdP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) (h.dom.take p.k) h.plen
    (valid_facts hm hk).1) fun t ⟨mi, hc, hv, hWs, hf, k⟩ => ?_
  change Frm p.B (setupR p.w) s.mem t.mem at hf
  have hw := room_k hk hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hw
  have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega
  have hh : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 h3 =>
    hf.word_eq (fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega) (by omega)
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [setupR, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega)
  have hb : Base p t := h.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide))
  refine ⟨⟨mi, ⟨hb, hc.toMem, hv, hWs, ?_, ?_⟩, hc.rdi⟩, hi, ?_, k⟩
  · rw [hh _ (by decide) (by decide) (by decide) (by decide)]; exact hG
  · rw [hh _ (by decide) (by decide) (by decide) (by decide)]; exact hQ
  · intro i hi
    exact hh i (by omega) (by unfold sW; omega) (by unfold sWs sFn; omega) (by unfold sArr; omega)

end VG.Proof.Ffdh.X86_64.CheckDomain
