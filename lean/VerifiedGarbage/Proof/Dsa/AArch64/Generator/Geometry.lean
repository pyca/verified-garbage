module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
public import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.AArch64.Generator.Arena`, which only this module used -/

section

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
  rcases a.width with h | h | h <;> rw [h] <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega_using [hd, hn]

theorem pLe : a.pLen ≤ 384 := by rcases a.width with h | h | h <;> omega_using [h]

theorem parentRoom : Impl.Dsa.Layout.activeBytes ≤ usedBytes a.pLen := by
  rcases a.width with h | h | h <;> rw [h] <;> decide

theorem part_sub {d n : Nat} (h : d + n ≤ usedBytes a.pLen) : Region.Sub (a.part d n) ⟨a.B, usedBytes a.pLen⟩ :=
  Offset.sub_base a.B h

theorem parts_disjoint {d n e k : Nat} (hd : d + n ≤ usedBytes a.pLen) (he : e + k ≤ usedBytes a.pLen)
    (h : d + n ≤ e ∨ e + k ≤ d) : (a.part d n).Disjoint (a.part e k) :=
  Offset.disjoint a.B h (by have := a.arenaBound; omega_using [hd, this]) (by have := a.arenaBound; omega_using [he, this])

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
  have hb : d + n ≤ usedBytes a.pLen := by have := a.small (d := g) (n := 0) (by decide) (by decide); omega_using [hn, this]
  have ha := a.small (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hg := a.small (d := g) (n := a.pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn])
  intro r hr
  simp only [gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a.parts_disjoint hb ha (Or.inl (by unfold g arithmetic at *; omega_using [hn]))
  · rw [a.parent_eq]
    exact a.parts_disjoint hb (by simpa using a.parentRoom) (Or.inr (by unfold q Impl.Dsa.Layout.activeBytes at *; omega_using [hd]))
  · exact a.parts_disjoint hb hg (Or.inl hn)
  · exact (a.frame_part hb).symm

/-- The generator search's plan over the bytes `pb` of p and `eb` of the
exponent (its h input is a placeholder, which each chunk replaces). -/
def generatorPlan (pb eb : List Byte) (hp : pb.length = a.pLen) (he : eb.length = a.pLen)
    (positive : 1 < Spec.Dsa.decodeBE pb) (odd : Spec.Dsa.decodeBE pb % 2 = 1) : GeneratorPlan := by
  have pn := a.pLe
  have ha := a.small (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := a.small (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hg := a.small (d := g) (n := a.pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn])
  have parent : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes a.pLen := by simpa using a.parentRoom
  have gp : (a.part g a.pLen).Disjoint ⟨a.B, Impl.Dsa.Layout.activeBytes⟩ := by
    rw [a.parent_eq]; exact a.parts_disjoint hg parent (Or.inr (by decide))
  have ga := a.parts_disjoint hg ha (Or.inl (by unfold g arithmetic; omega_using [pn]))
  have ps := a.gWork_separate (d := VG.Impl.Dsa.Generation.Layout.p) (n := a.pLen)
    (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega_using [pn])
  have es := a.gWork_separate (d := exponent) (n := a.pLen) (by decide) (by unfold exponent g; omega_using [pn])
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
    frameHeaders := fun k hk j hj => fa.sep (Offset.contains_base _ (by unfold frameBytes; omega_using [hk]) (by omega_using [hk]))
      (Offset.contains_base _ (by unfold arithmeticBytes; omega_using [hj]) (by omega_using [hj]))
    frameOutside := fun k hk i hi => by
      rw [off_off]
      exact out_scr fa (Offset.contains_base _ (by unfold frameBytes; omega_using [hk, hi]) (by omega_using [hk, hi]))
    frameSeparate := ?_
    hashSeparate := ?_
    pSeparate := ps
    hSeparate := ps
    eSeparate := es
    gArithmeticSeparate := ga
    gParentOutside := fun i hi => out_scr gp (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, hi]))
    gArithmeticOutside := fun i hi => out_scr ga (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, hi])) }
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

end

end

/-! # The stage's frame and working space, from its arguments

The frame is at `frameBase s`, the stack pointer less 272, and the stage's
288 bytes of stack hold it and the 16 bytes below it. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

/-- The frame's base. -/
abbrev frameBase (s : State) : Addr := s.sp - BitVec.ofNat 64 272

/-- The working space's region. -/
abbrev wsRegion (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩

/-- The h tape's region. -/
abbrev tapeRegion (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩

/-- The hash workspace the frame's layout names. -/
abbrev hashBase (s : State) : Addr := off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.hash

theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ 272) :
    Region.Sub ⟨off (frameBase s) d, n⟩ (below s.sp stack) := by
  have e : off (frameBase s) d = s.sp - BitVec.ofNat 64 (272 - d) := by
    simp only [off, frameBase]
    rw [Offset.sub_ofNat_eq s.sp (show 272 - d ≤ 272 by omega_using []), Nat.sub_sub_self (by omega_using [h])]
  rw [e]
  exact Offset.sub_below s.sp (by unfold stack; omega_using []) (by unfold stack; omega_using [h])

theorem frame_sub0 (s : State) {n : Nat} (h : n ≤ 272) :
    Region.Sub ⟨frameBase s, n⟩ (below s.sp stack) := by
  simpa only [off, BitVec.add_zero] using frame_sub s (d := 0) (n := n) (by omega_using [h])

theorem retR_sub (s : State) : Region.Sub (below (frameBase s) 16) (below s.sp stack) := by
  have e : frameBase s - BitVec.ofNat 64 16 = s.sp - BitVec.ofNat 64 288 := by
    simp only [frameBase, BitVec.sub_sub]; rfl
  change Region.Sub ⟨_, 16⟩ ⟨_, 288⟩
  rw [e]
  simpa only [off, BitVec.add_zero] using Offset.sub_base (s.sp - BitVec.ofNat 64 288) (d := 0) (n := 16) (k := 288) (by decide)

variable {pLen : Nat} {s : State}

theorem StageABI.base_toNat (A : StageABI pLen s) : (frameBase s).toNat = s.sp.toNat - 272 := by
  have hl := A.stackLower
  have hb := s.sp.isLt
  unfold stack at hl
  simp only [frameBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [hl]

theorem StageABI.used_sub (A : StageABI pLen s) : Region.Sub ⟨s.gpr .x0, usedBytes pLen⟩ (wsRegion s) := by
  have := A.size
  simpa only [off, BitVec.add_zero] using Offset.sub_base (s.gpr .x0) (d := 0) (n := usedBytes pLen) (by omega_using [this])

theorem StageABI.part_sub (A : StageABI pLen s) {d n : Nat} (h : d + n ≤ usedBytes pLen) :
    Region.Sub ⟨off (s.gpr .x0) d, n⟩ (wsRegion s) := fun x hx =>
  A.used_sub x (Offset.sub_base (s.gpr .x0) h x hx)

/-- The stage's working space and frame. -/
def arena (hb : Supported pLen) (A : StageABI pLen s) : Arena where
  B := s.gpr .x0
  F := frameBase s
  pLen := pLen
  width := hb
  arenaBound := by have := A.wsBound; have := A.size; omega_arith
  frameArena := (A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega_using []))).sub_right A.used_sub

theorem StageABI.geo (hb : Supported pLen) (A : StageABI pLen s) : VG.Proof.RsaOaep.AArch64.Geo (frameBase s) (hashBase s) where
  F16 := by rw [A.base_toNat]; have := A.stackLower; unfold stack at this; omega_using [this]
  Fw := by rw [A.base_toNat]; have := s.sp.isLt; unfold frameBytes; omega_using []
  Sw := by
    have ha := (arena hb A).arenaBound
    have hs := (arena hb A).small (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
    simp only [arena] at ha hs
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : VG.Impl.Dsa.Generation.Layout.hash < 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt this]
    have := Nat.mod_le ((s.gpr .x0).toNat + VG.Impl.Dsa.Generation.Layout.hash) (2 ^ 64)
    omega_using [ha, hs]
  dFS := (arena hb A).frame_part ((arena hb A).small (by decide) (by decide))
  dRS := (A.stackWs.sub_left (retR_sub s)).sub_right
    (A.part_sub ((arena hb A).small (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))
  dRF := (Offset.base_disjoint_below (frameBase s) (n := 16) (k := frameBytes) (by decide)).symm

end VG.Proof.Dsa.AArch64.Generator
