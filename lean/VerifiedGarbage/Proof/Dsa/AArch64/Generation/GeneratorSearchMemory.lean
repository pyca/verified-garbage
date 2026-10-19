module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
import VerifiedGarbage.Proof.Framework.Omega

/-! # Preserve the whole h tape while testing successive complete chunks -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def generatorSlots : List Nat := [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 26]

structure GeneratorSearchMemory (p : GeneratorSearchPlan) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.core.F p.core.S
  rep : ∃ V, Rep s.mem p.core.F p.core.S V W
  base : W 5 = p.core.B
  tapeBase : W 11 = p.tapePtr
  tapeLength : W 13 = BitVec.ofNat 64 p.tape.length
  slots : ∀ k ∈ generatorSlots, W k = p.saved k
  arithmetic : Scr s p.core.A p.core.Z
  parent : Scr s p.core.B Impl.Dsa.Layout.activeBytes
  pArithmetic : Src s p.core.A p.core.Z (VG.Proof.Bignum.off p.core.B Impl.Dsa.Generation.Layout.p) p.core.pb
  tapeArithmetic : Src s p.core.A p.core.Z p.tapePtr p.tape
  eArithmetic : Src s p.core.A p.core.Z (VG.Proof.Bignum.off p.core.B exponent) p.core.eb
  pParent : Src s p.core.B Impl.Dsa.Layout.activeBytes (VG.Proof.Bignum.off p.core.B Impl.Dsa.Generation.Layout.p) p.core.pb
  tapeParent : Src s p.core.B Impl.Dsa.Layout.activeBytes p.tapePtr p.tape
  eParent : Src s p.core.B Impl.Dsa.Layout.activeBytes (VG.Proof.Bignum.off p.core.B exponent) p.core.eb
  gWrite : ∀ i < p.core.len, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.core.B g) i) 1

theorem GeneratorSearchMemory.frame {p : GeneratorSearchPlan} {W W' : Nat → BitVec 64} {s t : State}
    (h : GeneratorSearchMemory p W s) (L : Lay t p.core.F p.core.S)
    (R : ∃ V, Rep t.mem p.core.F p.core.S V W')
    (hw : ∀ k ∈ generatorSlots, W' k = W k)
    (hf : Frame p.core.changed s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    GeneratorSearchMemory p W' t := by
  have hn : p.core.len < 2 ^ 64 := by rcases p.core.width with hh | hh | hh <;> omega
  have fp : ∀ r ∈ p.core.changed, (⟨VG.Proof.Bignum.off p.core.B Impl.Dsa.Generation.Layout.p, p.core.pb.length⟩ : Region).Disjoint r := by
    rw [p.core.pLength]; exact p.core.pSeparate
  have fe : ∀ r ∈ p.core.changed, (⟨VG.Proof.Bignum.off p.core.B exponent, p.core.eb.length⟩ : Region).Disjoint r := by
    rw [p.core.eLength]; exact p.core.eSeparate
  exact ⟨L, R, (hw 5 (by simp [generatorSlots])).trans h.base, (hw 11 (by simp [generatorSlots])).trans h.tapeBase,
    (hw 13 (by simp [generatorSlots])).trans h.tapeLength,
    fun k hk => (hw k hk).trans (h.slots k hk), h.arithmetic.congr hwr, h.parent.congr hwr,
    source_of_frame h.pArithmetic hf fp (p.core.pLength ▸ hn) hrd hwr,
    source_of_frame h.tapeArithmetic hf p.tapeSeparate p.tapeFits hrd hwr,
    source_of_frame h.eArithmetic hf fe (p.core.eLength ▸ hn) hrd hwr,
    source_of_frame h.pParent hf fp (p.core.pLength ▸ hn) hrd hwr,
    source_of_frame h.tapeParent hf p.tapeSeparate p.tapeFits hrd hwr,
    source_of_frame h.eParent hf fe (p.core.eLength ▸ hn) hrd hwr,
    fun i hi => by rw [hwr]; exact h.gWrite i hi⟩

theorem GeneratorSearchMemory.chunk {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorSearchMemory p W s) {used : Nat} (room : used + p.core.len ≤ p.tape.length)
    (ptr : W 21 = VG.Proof.Bignum.off p.tapePtr used) : GeneratorMemory (p.chunk used room) W s :=
  ⟨h.layout, h.rep, h.base, ptr, h.arithmetic, h.parent,
    h.pArithmetic, VG.Proof.Dsa.AArch64.source_slice h.tapeArithmetic room, h.eArithmetic,
    h.pParent, VG.Proof.Dsa.AArch64.source_slice h.tapeParent room, h.eParent, h.gWrite⟩

end VG.Proof.Dsa.AArch64.Generation
