module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.Offset

/-! # The stage's working space and frame, and the generator search's plan in them

`B` is the working space, laid out as the generation's scratch space, and
`F` the stage's frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (GeneratorPlan GeneratorSearchPlan)

structure Arena where
  B : Addr
  F : Addr
  pLen : Nat
  width : pLen = 128 ∨ pLen = 256 ∨ pLen = 384
  arenaBound : B.toNat + usedBytes pLen ≤ 2 ^ 64
  frameArena : (⟨F, frameBytes⟩ : Region).Disjoint ⟨B, usedBytes pLen⟩

namespace Arena
variable (a : Arena)

/-- The `n` bytes at offset `d` of the working space. -/
def part (d n : Nat) : Region := ⟨off a.B d, n⟩

theorem small {d n : Nat} (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) : d + n ≤ usedBytes a.pLen := by
  rcases a.width with h | h | h <;> rw [h] <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega

theorem pLe : a.pLen ≤ 384 := by rcases a.width with h | h | h <;> omega

theorem parentRoom : Impl.Dsa.Layout.activeBytes ≤ usedBytes a.pLen := by
  rcases a.width with h | h | h <;> rw [h] <;> decide

theorem part_sub {d n : Nat} (h : d + n ≤ usedBytes a.pLen) : Region.Sub (a.part d n) ⟨a.B, usedBytes a.pLen⟩ :=
  Offset.sub_base a.B h

theorem parts_disjoint {d n e k : Nat} (hd : d + n ≤ usedBytes a.pLen) (he : e + k ≤ usedBytes a.pLen)
    (h : d + n ≤ e ∨ e + k ≤ d) : (a.part d n).Disjoint (a.part e k) :=
  Offset.disjoint a.B h (by have := a.arenaBound; omega) (by have := a.arenaBound; omega)

theorem frame_part {d n : Nat} (h : d + n ≤ usedBytes a.pLen) : (⟨a.F, frameBytes⟩ : Region).Disjoint (a.part d n) :=
  a.frameArena.sub_right (a.part_sub h)

theorem parent_eq : (⟨a.B, Impl.Dsa.Layout.activeBytes⟩ : Region) = a.part 0 Impl.Dsa.Layout.activeBytes := by
  simp [part, off]

/-- The generator search's regions: the arithmetic workspace, the DSA
workspace of the exponentiation, g and the frame. -/
def gWork : List Region :=
  [a.part arithmetic arithmeticBytes, ⟨a.B, Impl.Dsa.Layout.activeBytes⟩, a.part g a.pLen, ⟨a.F, frameBytes⟩]

theorem gWork_separate {d n : Nat} (hd : q ≤ d) (hn : d + n ≤ g) : ∀ r ∈ a.gWork, (a.part d n).Disjoint r := by
  have pn := a.pLe
  have hb : d + n ≤ usedBytes a.pLen := by have := a.small (d := g) (n := 0) (by decide) (by decide); omega
  have ha := a.small (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hg := a.small (d := g) (n := a.pLen) (by decide) (by unfold arithmeticBytes; omega)
  intro r hr
  simp only [gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a.parts_disjoint hb ha (Or.inl (by unfold g arithmetic at *; omega))
  · rw [a.parent_eq]
    exact a.parts_disjoint hb (by simpa using a.parentRoom) (Or.inr (by unfold q Impl.Dsa.Layout.activeBytes at *; omega))
  · exact a.parts_disjoint hb hg (Or.inl hn)
  · exact (a.frame_part hb).symm

/-- The generator search's plan over the bytes `pb` of p and `eb` of the
exponent (its h input is a placeholder, which each chunk replaces). -/
def generatorPlan (pb eb : List Byte) (hp : pb.length = a.pLen) (he : eb.length = a.pLen)
    (positive : 1 < Spec.Dsa.decodeBE pb) (odd : Spec.Dsa.decodeBE pb % 2 = 1) : GeneratorPlan := by
  have pn := a.pLe
  have ha := a.small (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := a.small (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hg := a.small (d := g) (n := a.pLen) (by decide) (by unfold arithmeticBytes; omega)
  have parent : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes a.pLen := by simpa using a.parentRoom
  have gp : (a.part g a.pLen).Disjoint ⟨a.B, Impl.Dsa.Layout.activeBytes⟩ := by
    rw [a.parent_eq]; exact a.parts_disjoint hg parent (Or.inr (by decide))
  have ga := a.parts_disjoint hg ha (Or.inl (by unfold g arithmetic; omega))
  have ps := a.gWork_separate (d := VG.Impl.Dsa.Generation.Layout.p) (n := a.pLen)
    (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega)
  have es := a.gWork_separate (d := exponent) (n := a.pLen) (by decide) (by unfold exponent g; omega)
  have fa := a.frame_part ha
  refine {
    B := a.B
    A := off a.B arithmetic
    F := a.F
    S := off a.B VG.Impl.Dsa.Generation.Layout.hash
    hp := off a.B VG.Impl.Dsa.Generation.Layout.p
    Z := arithmeticBytes
    len := a.pLen
    pb := pb
    hb := pb
    eb := eb
    width := a.width
    arithmeticBase := rfl
    workspaceRoom := by rcases a.width with h | h | h <;> rw [h] <;> decide
    pLength := hp
    hLength := hp
    eLength := he
    pPositive := positive
    pOdd := odd
    frameHeaders := fun k hk j hj => fa.sep (Offset.contains_base _ (by unfold frameBytes; omega) (by omega))
      (Offset.contains_base _ (by unfold arithmeticBytes; omega) (by omega))
    frameOutside := fun k hk i hi => by
      rw [off_off]
      exact out_scr fa (Offset.contains_base _ (by unfold frameBytes; omega) (by omega))
    frameSeparate := ?_
    hashSeparate := ?_
    pSeparate := ps
    hSeparate := ps
    eSeparate := es
    gArithmeticSeparate := ga
    gParentOutside := fun i hi => out_scr gp (Offset.contains_base _ (by omega) (by omega))
    gArithmeticOutside := fun i hi => out_scr ga (Offset.contains_base _ (by omega) (by omega)) }
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fa
    · rw [a.parent_eq]; exact a.frame_part parent
    · exact a.frame_part hg
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a.parts_disjoint hh ha (Or.inl (by decide))
    · rw [a.parent_eq]; exact a.parts_disjoint hh parent (Or.inr (by decide))
    · exact a.parts_disjoint hh hg (Or.inl (by decide))

end Arena

end VG.Proof.Dsa.AArch64.Generator
