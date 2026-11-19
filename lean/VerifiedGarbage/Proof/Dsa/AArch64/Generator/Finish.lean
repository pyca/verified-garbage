module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
public import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInvariant
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeIteration
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! ### `Dsa.AArch64.Generation.ValidateCore`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.ValidateArgs`, which this module and modules that import it used -/

section

/-! # Set the packed-domain checker's arguments from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem validateArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {pLen qLen : Nat}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.validateArgs pLen qLen)) s fun t =>
      t.gpr .x0 = VG.Proof.Bignum.off (W 5) packed ∧ t.gpr .x4 = VG.Proof.Bignum.off (W 5) domainCheck ∧
      t.gpr .x2 = BitVec.ofNat 64 pLen ∧ t.gpr .x3 = BitVec.ofNat 64 qLen ∧
      t.mem = s.mem ∧ Keep [.x0, .x4, .x2, .x3] s t := by
  have cast (n : Nat) (hn : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hn]
  refine WP.mono (WP.keep [.x0, .x4, .x2, .x3] (Q := fun t =>
      t.gpr .x0 = VG.Proof.Bignum.off (W 5) packed ∧ t.gpr .x4 = VG.Proof.Bignum.off (W 5) domainCheck ∧
      t.gpr .x2 = BitVec.ofNat 64 pLen ∧ t.gpr .x3 = BitVec.ofNat 64 qLen ∧ t.mem = s.mem) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
    brun [Impl.Dsa.AArch64.Generation.validateArgs, exec_ldrSp (off := 40) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), hw,
      cast packed (by decide), cast domainCheck (by decide), cast pLen hp, cast qLen hq]) rfl rfl rfl)
    fun t ⟨⟨hdi, h8, hdx, hcx, hm⟩, hk⟩ => ⟨hdi, h8, hdx, hcx, hm, hk⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Reuse the complete verified domain checker inside parameter generation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem validateCore_ok (M : Mont) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = VG.Proof.Bignum.off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 16) (hq : p.qLen < 2 ^ 16)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩) :
    WP isa (.seq (.block (Impl.Dsa.AArch64.Generation.validateArgs p.pLen p.qLen))
      (Impl.Dsa.AArch64.Generate.checkParameters M.mm)) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  refine WP.seq (WP.mono (validateArgs_ok L R hp hq) fun u ⟨hdi, h8, hdx, hcx, hm, ku⟩ => ?_)
  have pre : ParametersPre p u := ⟨hs.congr ku.wr, h8.trans hbase.symm, hdx, hcx,
    hdi ▸ src.congrK (fun a _ => by rw [hm]) ku⟩
  refine WP.mono (parametersMain_ok M pre) fun t ⟨result, ft, kt⟩ => ?_
  have frame : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩] s.mem t.mem := by
    intro a ha
    have hn := ha ⟨p.base, Impl.Dsa.Layout.usedBytes⟩ (by simp)
    change ¬ ofs p.base a < Impl.Dsa.Layout.usedBytes at hn
    rw [ft a (by omega_using [hn]), hm]
  have Rt := rep_of_disjoint_frame R frame
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl keep.sp keep.wr, Rt, frame, keep.mono (by decide)⟩

theorem validateTest_ok {s : State} {valid : Bool}
    (hr : s.gpr .x0 = BitVec.ofNat 64 (if valid then 1 else 0)) :
    eval (.zero .x .x0) s = some (!valid) := by
  cases valid <;> simp only [eval, State.read, hr, Size.bits, BitVec.setWidth_eq] <;> rfl

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PackPart`, which this module and modules that import it used -/

section

/-! # Copy one generated domain component while retaining the search frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem packArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src dst len : Nat}
    (hs : src < 2 ^ 16) (hd : dst < 2 ^ 16) (hl : len ≤ 1024) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.packArgs src dst len)) s fun t =>
      t.gpr .x12 = VG.Proof.Bignum.off (W 5) src ∧ t.gpr .x2 = VG.Proof.Bignum.off (W 5) dst ∧
      t.gpr .x9 = BitVec.ofNat 64 len ∧
      t.mem = s.mem ∧ Keep [.x12, .x2, .x9, .x3] s t := by
  have cast (n : Nat) (hn : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hn]
  refine WP.mono (WP.keep [.x12, .x2, .x9, .x3] (Q := fun t =>
      t.gpr .x12 = VG.Proof.Bignum.off (W 5) src ∧ t.gpr .x2 = VG.Proof.Bignum.off (W 5) dst ∧
      t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
    brun [Impl.Dsa.AArch64.Generation.packArgs, exec_ldrSp (off := 40) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), hw,
      cast src hs, cast dst hd, cast len (by omega_using [hl])]) rfl rfl rfl)
    fun t ⟨⟨hsi, hdi, hcx, hm⟩, hk⟩ => ⟨hsi, hdi, hcx, hm, hk⟩

theorem packPart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src dst : Nat} {bs : List Byte}
    (hs : src < 2 ^ 16) (hd : dst < 2 ^ 16) (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) dst) i) 1)
    (hb : ∀ i < bs.length, s.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) dst) j)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.packPart src dst bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) dst) bs.length = bs ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.packPart
  refine WP.seq (WP.mono (packArgs_ok L R hs hd hl.2) fun u ⟨hsi, hdi, hcx, hm, ku⟩ => ?_)
  refine WP.mono (copyBytes_ok (by omega_using [hl]) hsi hdi hcx
    (fun i hi => by rw [ku.rd, ku.wr]; exact hrd i hi)
    (fun i hi => by rw [ku.wr]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) hsep) fun t ⟨result, ft, kt⟩ => ?_
  have ff : Frame [⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩] s.mem t.mem := by
    intro a ha
    rw [ft a (by
      intro i hi he
      apply ha ⟨VG.Proof.Bignum.off (W 5) dst, bs.length⟩ (by simp)
      rw [he]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])), hm]
  have Rt := rep_of_disjoint_frame R ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl keep.sp keep.wr, Rt, ff, keep.mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generator.Prepared`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generator.Entry`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generator.Geometry`, which the modules that import this one used -/

section

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

end

end

/-! # The generator stage's arguments in the generation's frame slots -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generator

/-- The frame words the entry sets: the working space `B`, the h tape `hp`
of `n` bytes, the hash workspace, and zero. -/
def entryWords (B hp n : Addr) (k : Nat) : BitVec 64 :=
  if k = 5 then B else if k = 11 then hp else if k = 12 then off B Impl.Dsa.Generation.Layout.hash
  else if k = 13 then n else 0

/-- The memory after the entry's stores. -/
def entryMem (s : State) (F : Addr) : Mem :=
  zeroSlots.foldl (fun m k => m.writeW (off F (8 * k)) (0 : BitVec 64))
    ((((s.mem.writeW (off F 40) (s.gpr .x0)).writeW (off F 88) (s.gpr .x2)).writeW (off F 104) (s.gpr .x3)).writeW
      (off F 96) (off (s.gpr .x0) Impl.Dsa.Generation.Layout.hash))

theorem word_writeW_frame (m : Mem) (F : Addr) (v : BitVec 64) {d e : Nat}
    (hd : d % 8 = 0 ∧ d + 8 ≤ 448) (he : e % 8 = 0 ∧ e + 8 ≤ 448) :
    word (m.writeW (off F d) v) F e = if d = e then v else word m F e := by
  split
  · subst e; exact word_writeW_self _ _ _ _
  · exact (writeW_outside m F v (by omega_using [hd])).word (by omega_arith) (by omega_using [he])

theorem word_foldl_zero (F : Addr) {e : Nat} (he : e < 34) :
    ∀ (l : List Nat), (∀ k ∈ l, k < 34) → ∀ m : Mem,
      word (l.foldl (fun m k => m.writeW (off F (8 * k)) (0 : BitVec 64)) m) F (8 * e) =
        if e ∈ l then 0 else word m F (8 * e)
  | [], _, m => by simp
  | k :: l, hl, m => by
    rw [List.foldl_cons, word_foldl_zero F he l (fun j hj => hl j (List.mem_cons_of_mem _ hj)),
      word_writeW_frame _ F _ (by have := hl k List.mem_cons_self; omega_using [this]) (by omega_using [he])]
    by_cases hk : k = e
    · subst hk; simp
    · by_cases hel : e ∈ l
      · simp [hel]
      · have : 8 * k ≠ 8 * e := by omega_using [hk]
        simp [hel, this, Ne.symm hk]

/-- The words the entry sets. -/
theorem entryMem_word (s : State) (F : Addr) {k : Nat}
    (hk : k = 5 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k ∈ zeroSlots) :
    word (entryMem s F) F (8 * k) = entryWords (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) k := by
  have bound : k < 34 := by
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
  unfold entryMem
  rw [word_foldl_zero F bound zeroSlots (by decide),
    word_writeW_frame _ F _ (d := 96) (by decide) (by omega_using [bound]),
    word_writeW_frame _ F _ (d := 104) (by decide) (by omega_using [bound]),
    word_writeW_frame _ F _ (d := 88) (by decide) (by omega_using [bound]),
    word_writeW_frame _ F _ (d := 40) (by decide) (by omega_using [bound])]
  simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [entryWords, zeroSlots]

theorem foldl_zero_frame (F : Addr) :
    ∀ (l : List Nat), (∀ k ∈ l, k < 34) → ∀ {m₀ m : Mem}, Frame [⟨F, 272⟩] m₀ m →
      Frame [⟨F, 272⟩] m₀ (l.foldl (fun m k => m.writeW (off F (8 * k)) (0 : BitVec 64)) m)
  | [], _, _, _, h => h
  | k :: l, hl, _, _, h => by
    rw [List.foldl_cons]
    exact foldl_zero_frame F l (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      (h.writeW List.mem_cons_self _ (Offset.contains_base F (n := 8) (by have := hl k List.mem_cons_self; omega_using [this])
        (by have := hl k List.mem_cons_self; omega_using [this])))

/-- The entry writes only the frame words. -/
theorem entryMem_frame (s : State) (F : Addr) : Frame [⟨F, 272⟩] s.mem (entryMem s F) := by
  unfold entryMem
  have c (d : Nat) (hd : d + 8 ≤ 272) : (⟨F, 272⟩ : Region).Contains (off F d) (64 / 8) :=
    Offset.contains_base F hd (by omega_using [hd])
  exact foldl_zero_frame F zeroSlots (by decide)
    (((((Frame.refl _ _).writeW List.mem_cons_self _ (c 40 (by decide))).writeW List.mem_cons_self _
      (c 88 (by decide))).writeW List.mem_cons_self _ (c 104 (by decide))).writeW List.mem_cons_self _ (c 96 (by decide)))

theorem entry_ok {s : State} {F : Addr} (hsp : s.sp = F)
    (hw : ∀ d, d + 8 ≤ 272 → InRegions s.wr (off F d) 8) :
    WP isa (.block entry) s fun t => t.mem = entryMem s F ∧ Keep [.x4] s t := by
  have run : WP isa (.block entry) s fun t => t.mem = entryMem s F := by
    simp only [entry, zeroSlots, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    have hh : BitVec.setWidth 64 (BitVec.ofNat 16 Impl.Dsa.Generation.Layout.hash) =
        BitVec.ofNat 64 Impl.Dsa.Generation.Layout.hash := by decide
    have h0 : BitVec.setWidth 64 (0#16) = (0 : BitVec 64) := by decide
    brun [State.write, hh, h0, exec_storeSp (off := 40) (by decide), exec_storeSp (off := 88) (by decide),
      exec_storeSp (off := 104) (by decide), exec_storeSp (off := 96) (by decide),
      exec_storeSp (off := 8) (by decide), exec_storeSp (off := 24) (by decide), exec_storeSp (off := 32) (by decide),
      exec_storeSp (off := 48) (by decide), exec_storeSp (off := 56) (by decide), exec_storeSp (off := 64) (by decide),
      exec_storeSp (off := 72) (by decide), exec_storeSp (off := 80) (by decide), exec_storeSp (off := 112) (by decide),
      exec_storeSp (off := 120) (by decide), exec_storeSp (off := 128) (by decide), exec_storeSp (off := 136) (by decide),
      exec_storeSp (off := 144) (by decide), exec_storeSp (off := 208) (by decide),
      hsp, hw 40 (by decide), hw 88 (by decide), hw 104 (by decide), hw 96 (by decide),
      hw 8 (by decide), hw 24 (by decide), hw 32 (by decide), hw 48 (by decide), hw 56 (by decide), hw 64 (by decide),
      hw 72 (by decide), hw 80 (by decide), hw 112 (by decide), hw 120 (by decide), hw 128 (by decide),
      hw 136 (by decide), hw 144 (by decide), hw 208 (by decide), off]
    simp only [entryMem, zeroSlots, List.foldl_cons, List.foldl_nil, Nat.reduceMul]

  exact WP.mono (WP.keep [.x4] run (by decide)) fun t ⟨hm, k⟩ => ⟨hm, k⟩

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! # The generator search's plan and memory, once the entry has filled the frame

The plan is the generation's: p and the exponent at their offsets of the
working space, the h tape, and q; it depends on nothing but the arguments
and these values, which are public. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (GeneratorSearchPlan GeneratorSearchMemory generatorSlots)

variable {pLen : Nat} {s : State}

/-- p's bytes. -/
abbrev pBytes (pLen : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.p) pLen

/-- q's bytes. -/
abbrev qBytes (pLen : Nat) (s : State) : List Byte :=
  Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.q) (Impl.Dsa.AArch64.Generator.qLen pLen)

/-- The exponent's bytes. -/
abbrev eBytes (pLen : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.exponent) pLen

/-- The h tape. -/
abbrev tape (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

theorem Supported.pos {pLen : Nat} (hb : Supported pLen) : 0 < 8 * pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem used_small (hb : Supported pLen) {d n : Nat} (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
    d + n ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> unfold usedBytes domainCheck arithmeticBytes at * <;> omega_using [hd, hn]

theorem used_parent (hb : Supported pLen) : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem used_lt (hb : Supported pLen) : usedBytes pLen < 2 ^ 64 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem pow256 (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

theorem StageABI.p_bounds (hb : Supported pLen) (A : StageABI pLen s) :
    2 ^ (8 * pLen - 1) ≤ pOf pLen s.mem (s.gpr .x0) ∧ pOf pLen s.mem (s.gpr .x0) < 256 ^ pLen := by
  rw [pow256]
  exact (bitLength_iff_bounds hb.pos).mp A.bits

theorem StageABI.positive (hb : Supported pLen) (A : StageABI pLen s) : 1 < Spec.Dsa.decodeBE (pBytes pLen s) :=
  Nat.lt_of_lt_of_le (Nat.one_lt_two_pow (by rcases hb with rfl | rfl | rfl <;> decide)) (A.p_bounds hb).1

theorem StageABI.exponentValue (hb : Supported pLen) (A : StageABI pLen s) :
    Spec.Dsa.decodeBE (eBytes pLen s) = (Spec.Dsa.decodeBE (pBytes pLen s) - 1) / qOf pLen s.mem (s.gpr .x0) := by
  have e := A.exponent
  change Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.exponent) pLen = _ at e
  rw [eBytes, e, VG.Proof.Dsa.decodeBE_encodeBE]
  · rfl
  · exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) (A.p_bounds hb).2

/-- The generator search's plan. -/
def plan (hb : Supported pLen) (A : StageABI pLen s) : GeneratorSearchPlan where
  core := (arena hb A).generatorPlan (pBytes pLen s) (eBytes pLen s) (bytesAt_length _ _ _) (bytesAt_length _ _ _)
    (A.positive hb) A.odd
  saved := entryWords (s.gpr .x0) (s.gpr .x2) (s.gpr .x3)
  tape := tape s
  tapePtr := s.gpr .x2
  tapeFits := by rw [bytesAt_length]; exact (s.gpr .x3).isLt
  tapeSeparate := by
    rw [bytesAt_length]
    have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
    intro r hr
    simp only [Generation.GeneratorPlan.changed, Arena.generatorPlan, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.wsTape.symm.sub_right (A.part_sub (used_small hb (by decide) (by rfl)))
    · have h := A.part_sub (used_parent hb)
      simp only [off, BitVec.add_zero] at h
      exact A.wsTape.symm.sub_right h
    · exact A.wsTape.symm.sub_right (A.part_sub (used_small hb (d := VG.Impl.Dsa.Generation.Layout.g) (n := pLen)
        (by decide) (by unfold arithmeticBytes; omega_using [pn])))
    · exact A.stackTape.symm.sub_right (frame_sub0 s (by unfold frameBytes; omega_using []))
  q := qOf pLen s.mem (s.gpr .x0)
  exponentValue := A.exponentValue hb

/-- The state the entry leaves: the frame words set, the memory changed in
the frame alone. -/
structure Entered (pLen : Nat) (s u : State) : Prop where
  sp : u.sp = frameBase s
  rd : u.rd = s.rd
  wr : u.wr = ⟨frameBase s, 272⟩ :: s.wr
  frame : Frame [⟨frameBase s, 272⟩, ⟨off (s.gpr .x0) Impl.Dsa.AArch64.Generator.spill,
    Impl.Dsa.AArch64.Generator.spillBytes⟩] s.mem u.mem
  words : ∀ k, (k = 5 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k ∈ Impl.Dsa.AArch64.Generator.zeroSlots) →
    word u.mem (frameBase s) (8 * k) = entryWords (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) k

/-- The frame words, as the generation's search reads them. -/
abbrev frameWords (s u : State) (k : Nat) : BitVec 64 := word u.mem (frameBase s) (8 * k)

theorem StageABI.scr (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    Scr u (s.gpr .x0) (usedBytes pLen) := by
  refine ⟨⟨s.gpr .x0, 0, (s.gpr .x1).toNat * 8, ?_, by simp [off], by have := A.size; omega_using [this], ?_⟩, ?_⟩
  · rw [E.wr, A.wr]; simp
  · have := A.wsBound; omega_using [this]
  · have := A.wsBound; have := A.size; omega_arith

theorem spill_used (hb : Supported pLen) :
    Impl.Dsa.AArch64.Generator.spill + Impl.Dsa.AArch64.Generator.spillBytes ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem StageABI.ws_frame (hb : Supported pLen) (A : StageABI pLen s) {d n : Nat}
    (h : d + n ≤ Impl.Dsa.AArch64.Generator.spill) :
    ∀ r ∈ [(⟨frameBase s, 272⟩ : Region), ⟨off (s.gpr .x0) Impl.Dsa.AArch64.Generator.spill,
      Impl.Dsa.AArch64.Generator.spillBytes⟩], Region.Disjoint ⟨off (s.gpr .x0) d, n⟩ r := by
  have hs := spill_used hb
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (A.stackWs.sub_left (frame_sub0 s (Nat.le_refl _))).symm.sub_left (A.part_sub (by omega_using [h, hs]))
  · exact (arena hb A).parts_disjoint (d := d) (n := n) (show d + n ≤ usedBytes pLen by omega_using [h, hs]) hs (Or.inl h)

/-- Bytes of the working space below the saved registers are as they were. -/
theorem StageABI.bytes_entered (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u)
    {d n : Nat} (h : d + n ≤ Impl.Dsa.AArch64.Generator.spill) :
    Spec.Rsa.bytesAt u.mem (off (s.gpr .x0) d) n = Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) d) n :=
  VG.Proof.Dsa.Generation.frame_bytesAt E.frame (A.ws_frame hb h)
    (by have := spill_used hb; have := A.wsBound; have := A.size; omega_arith)

theorem StageABI.arenaSrc (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u)
    {d n : Nat} (h : d + n ≤ Impl.Dsa.AArch64.Generator.spill) {work : Addr} {Z : Nat}
    (sep : (⟨off (s.gpr .x0) d, n⟩ : Region).Disjoint ⟨work, Z⟩) :
    Src u work Z (off (s.gpr .x0) d) (Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) d) n) := by
  have hl := bytesAt_length s.mem (off (s.gpr .x0) d) n
  have hs := spill_used hb
  apply VG.Proof.Dsa.AArch64.Generation.arena_source (A.scr E) (by rw [hl]; omega_using [h, hs])
    (by rw [hl]; have := used_lt hb; omega_using [h, hs, this])
  · rw [hl, A.bytes_entered hb E h]
  · rw [hl]; exact sep

theorem StageABI.tapeSrc (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) {work : Addr} {Z : Nat}
    (sep : (tapeRegion s).Disjoint ⟨work, Z⟩) : Src u work Z (s.gpr .x2) (tape s) := by
  have hl := bytesAt_length s.mem (s.gpr .x2) (s.gpr .x3).toNat
  have tf : ∀ r ∈ [(⟨frameBase s, 272⟩ : Region), ⟨off (s.gpr .x0) Impl.Dsa.AArch64.Generator.spill,
      Impl.Dsa.AArch64.Generator.spillBytes⟩], (tapeRegion s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (A.stackTape.sub_left (frame_sub0 s (Nat.le_refl _))).symm
    · exact A.wsTape.symm.sub_right (A.part_sub (spill_used hb))
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hl] at hi
    exact ⟨_, List.mem_append_left _ (by rw [E.rd, A.rd]; exact List.mem_singleton_self _),
      contains_byte _ hi (by have := A.tapeBound; omega_using [])⟩
  · have hi' : i < (s.gpr .x3).toNat := by rw [hl] at hi; exact hi
    rw [E.frame.bytes tf (R := tapeRegion s) (by change (s.gpr .x3).toNat ≤ 2 ^ 64; have := A.tapeBound; omega_using []) hi']
    simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
  · rw [hl] at hi
    exact out_scr sep (contains_byte _ hi (by have := A.tapeBound; omega_using []))

/-- The search's memory, once the entry has filled the frame. -/
theorem prepared (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    GeneratorSearchMemory (plan hb A) (frameWords s u) u := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have ha := used_small hb (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hp : VG.Impl.Dsa.Generation.Layout.p + pLen ≤ Impl.Dsa.AArch64.Generator.spill := by
    unfold VG.Impl.Dsa.Generation.Layout.p Impl.Dsa.AArch64.Generator.spill VG.Impl.Dsa.Generation.Layout.control; omega_using [pn]
  have he : VG.Impl.Dsa.Generation.Layout.exponent + pLen ≤ Impl.Dsa.AArch64.Generator.spill := by
    unfold VG.Impl.Dsa.Generation.Layout.exponent Impl.Dsa.AArch64.Generator.spill VG.Impl.Dsa.Generation.Layout.control; omega_using [pn]
  have ps := (plan hb A).core.pSeparate
  have es := (plan hb A).core.eSeparate
  have ts := (plan hb A).tapeSeparate
  simp only [plan, Arena.generatorPlan, arena, bytesAt_length] at ps es ts
  have w := fun k hk => E.words k hk
  refine {
    layout := ⟨E.sp, ?_, ?_, ?_, A.geo hb⟩
    rep := ⟨fun o => u.mem (off (hashBase s) o), fun o _ => rfl, fun k _ => rfl⟩
    base := w 5 (by decide)
    tapeBase := w 11 (by decide)
    tapeLength := ?_
    slots := ?_
    arithmetic := by
      change Scr u (off (s.gpr .x0) arithmetic) arithmeticBytes
      exact (A.scr E).sub ha (by decide)
    parent := by
      change Scr u (s.gpr .x0) Impl.Dsa.Layout.activeBytes
      simpa [off] using (A.scr E).sub (used_parent hb) (by decide)
    pArithmetic := A.arenaSrc hb E hp (ps _ List.mem_cons_self)
    tapeArithmetic := A.tapeSrc hb E (ts _ List.mem_cons_self)
    eArithmetic := A.arenaSrc hb E he (es _ List.mem_cons_self)
    pParent := A.arenaSrc hb E hp (ps _ (List.mem_cons_of_mem _ List.mem_cons_self))
    tapeParent := A.tapeSrc hb E (ts _ (List.mem_cons_of_mem _ List.mem_cons_self))
    eParent := A.arenaSrc hb E he (es _ (List.mem_cons_of_mem _ List.mem_cons_self))
    gWrite := fun i hi => by
      rw [off_off]
      have hg := used_small hb (d := VG.Impl.Dsa.Generation.Layout.g) (n := pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn])
      exact (A.scr E).region (by change i < pLen at hi; omega_using [hg, hi]) (by decide) }
  · rw [E.wr]
    exact Covers.of_sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, 0, by simp; rfl, by unfold frameBytes; simp⟩
  · rw [E.wr]
    show Covers _ ([⟨frameBase s, 272⟩] ++ s.wr)
    refine Covers.right (Covers.of_sub fun r hr => ?_)
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨wsRegion s, by rw [A.wr]; exact List.mem_singleton_self _, Impl.Dsa.Generation.Layout.hash, rfl, ?_⟩
    have := A.size; have := used_small hb (d := Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
    simp only; omega_arith
  · exact w 12 (by decide)
  · change frameWords s u 13 = BitVec.ofNat 64 (tape s).length
    rw [bytesAt_length, ofNat_toNat64]; exact w 13 (by decide)
  · intro k hk
    apply w k
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    simp only [Impl.Dsa.AArch64.Generator.zeroSlots, List.mem_cons, List.not_mem_nil, or_false]
    omega_using [hk]

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.Generation.NativeGenerator`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorBody`, which only this module used -/

section

/-! # A consumed h chunk either finishes or advances the exact generator search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem generator_body_ok (M : Mont)
    {p : GeneratorSearchPlan} {expected : Option Nat} {final : Nat} {initial : State}
    {used : Nat} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (hi : GeneratorInvariant p expected final initial used s) (room : used + p.core.len ≤ p.tape.length)
    (R : Rep s.mem p.core.F p.core.S V W)
    (Lt : Lay t p.core.F p.core.S)
    (Rt : Rep t.mem p.core.F p.core.S V
      (upd (upd W 21 (VG.Proof.Bignum.off (W 11) used)) 20 (BitVec.ofNat 64 (used + p.core.len))))
    (ft : Frame [⟨p.core.F, frameBytes⟩] s.mem t.mem) (kt : Keep [.x3, .x4, .x5, .x15] s t) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorStep M.mm p.core.len) t fun u =>
      ∃ V' W', Lay u p.core.F p.core.S ∧ Rep u.mem p.core.F p.core.S V' W' ∧
        (if W' 19 = 3 then GeneratorInvariant p expected final initial (used + p.core.len) u
          else GeneratorFinished p expected final initial u) := by
  obtain ⟨Wi, h, _, he, hcount, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 34, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  let Wt := upd (upd W 21 (VG.Proof.Bignum.off (W 11) used)) 20 (BitVec.ofNat 64 (used + p.core.len))
  have ff : Frame p.core.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  have ht : GeneratorSearchMemory p Wt t := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Wt, upd] <;> exact words _ (by decide)) ff kt.rd kt.wr
  have hc := ht.chunk room (by
    change Wt 21 = VG.Proof.Bignum.off p.tapePtr used
    simp [Wt, upd, words 11 (by decide), h.tapeBase])
  refine WP.mono (generatorStep_ok M (p := p.chunk used room) hc) fun u ⟨hu, hg, fu, ku⟩ => ?_
  let Wu := upd Wt 19 (if (p.chunk used room).accepts then 1 else 3)
  have mem : GeneratorSearchMemory p Wu u := ht.frame hu.layout hu.rep (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) fu ku.rd ku.wr
  have frame := (fi.trans ff).trans fu
  have rd := ku.rd.trans (kt.rd.trans ri)
  have wr := ku.wr.trans (kt.wr.trans wi)
  have rem := he.trans (p.remaining_step room)
  have cnt := hcount.trans (congrArg (used + p.core.len * ·) (p.count_step room))
  have h20 : Wu 20 = BitVec.ofNat 64 (used + p.core.len) := by simp [Wu, Wt, upd]
  obtain ⟨Vu, Ru⟩ := mem.rep
  refine ⟨Vu, Wu, mem.layout, Ru, ?_⟩
  by_cases accepted : (p.chunk used room).accepts
  · have h19 : Wu 19 = 1 := by simp [Wu, upd, accepted]
    rw [ite_eq_right (by rw [h19]; decide)]
    rw [ite_eq_left accepted, Nat.mul_one] at cnt
    exact ⟨Wu, mem, cnt ▸ h20, Or.inr ⟨(p.chunk used room).value, h19,
      by simpa only [accepted, ite_true] using rem, hg accepted⟩, frame, rd, wr⟩
  · have h19 : Wu 19 = 3 := by simp [Wu, upd, accepted]
    rw [ite_eq_left h19]
    rw [ite_eq_right accepted, Nat.mul_succ] at cnt
    exact ⟨Wu, mem, h20,
      by simpa only [accepted, ite_false] using rem, by omega_using [cnt], frame, rd, wr⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.TapeLoop`, which only this module used -/

section

/-! # Termination of native seed and generator tape searches -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Dsa.AArch64.Generation

/-- The body provides algorithm-specific progress; the tape controller
owns complete-chunk selection, cursor advancement, and loop termination. -/
structure TapeDriver (slots : TapeSlots) (F S : Addr) (width total : Nat)
    (body : Prog isa) (I : Nat → State → Prop) (Q : State → Prop) : Prop where
  baseBound : slots.base < 34
  totalBound : slots.total < 34
  usedBound : slots.used < 34
  pointerBound : slots.pointer < 34
  usedNotScratch : slots.used ≠ 12
  pointerNotScratch : slots.pointer ≠ 12
  widthBound : width < 65536
  widthPositive : 0 < width
  totalFits : total < 2 ^ 64
  stable : ∀ n, TapeStable (I n)
  finish : TapeStable Q
  view : ∀ n s, I n s → TapeView slots F S n total s
  done : ∀ used s t V W, I used s → total - used < width →
    Lay s F S → Rep s.mem F S V W →
    Lay t F S → Rep t.mem F S V (upd W 19 3) →
    Outside F 152 8 s.mem t.mem → Keep [.x0, .x15] s t → Q t
  step : ∀ used s t V W, I used s → width ≤ total - used →
    Lay s F S → Rep s.mem F S V W → W slots.used = BitVec.ofNat 64 used →
    Lay t F S → Rep t.mem F S V
      (upd (upd W slots.pointer (VG.Proof.Bignum.off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) →
    Frame [⟨F, frameBytes⟩] s.mem t.mem → Keep [.x3, .x4, .x5, .x15] s t →
    WP isa body t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧
      (if W' 19 = 3 then I (used + width) u else Q u)

theorem TapeDriver.loop_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {used : Nat} (hle : used ≤ total) (hi : I used s) :
    WP isa (.loop (tapeIteration slots width body) (.zero .x .x0)) s Q := by
  exact WP.loop
    (fun n t => ∃ used, n = total - used + 1 ∧ used ≤ total ∧ I used t)
    (fun n t ⟨u, hn, hu, hit⟩ =>
      WP.mono (tapeIteration_ok d.baseBound d.totalBound d.usedBound d.pointerBound
        d.usedNotScratch d.pointerNotScratch d.widthBound d.totalFits
        d.stable d.finish d.view (d.done u) (d.step u) hu hit)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hbound⟩ =>
          ⟨hz, total - (u + width) + 1, by omega_using [d.widthPositive, hn, hu, hbound],
            u + width, rfl, hbound, hi'⟩)
    (total - used + 1) s ⟨used, rfl, hle, hi⟩

/-- Resetting the cursor makes each generator search reuse the original h
tape, and each top-level call begin at the first seed. -/
theorem TapeDriver.run_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (start : ∀ t, Lay t F S → Rep t.mem F S V (upd W slots.used 0) →
      Outside F (8 * slots.used) 8 s.mem t.mem → Keep [.x0, .x15] s t → I 0 t) :
    WP isa (tapeLoop slots width body) s Q := by
  unfold tapeLoop
  refine WP.seq (WP.mono (tapeReset_frame_ok L R slots d.usedBound d.usedNotScratch)
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_)
  exact d.loop_ok (Nat.zero_le _) (start t Lt Rt ft kt)

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Complete native generator search against the byte-tape specification -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.AArch64.Generation (generatorTape)

theorem nativeGenerator_ok (M : Mont)
    {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorSearchMemory p W s) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorSearch M.mm p.core.len) s
      (GeneratorFinished p (p.remaining 0) (p.core.len * p.count 0) s) := by
  let I := GeneratorInvariant p (p.remaining 0) (p.core.len * p.count 0) s
  let Q := GeneratorFinished p (p.remaining 0) (p.core.len * p.count 0) s
  have hw : 0 < p.core.len ∧ p.core.len < 65536 := by
    rcases p.core.width with hh | hh | hh <;> omega_using [hh]
  have driver : TapeDriver generatorTape p.core.F p.core.S p.core.len p.tape.length
      (Impl.Dsa.AArch64.Generation.generatorStep M.mm p.core.len) I Q :=
    { baseBound := by decide
      totalBound := by decide
      usedBound := by decide
      pointerBound := by decide
      usedNotScratch := by decide
      pointerNotScratch := by decide
      widthBound := hw.2
      widthPositive := hw.1
      totalFits := p.tapeFits
      stable := generatorInvariant_stable p (p.remaining 0) _ s
      finish := generatorFinished_stable p (p.remaining 0) _ s
      view := by
        rintro used t ⟨Wt, ht, h20, _, _, _, _, _⟩
        obtain ⟨Vt, Rt⟩ := ht.rep
        exact ⟨Vt, Wt, ht.layout, Rt, h20, ht.tapeLength⟩
      done := by
        intro used u v Vt Wt hi hex _ R Lu Ru fu ku
        exact generator_done hi hex R Lu Ru fu ku
      step := by
        intro used u v Vt Wt hi hav _ R _ Lv Rv fv kv
        exact generator_body_ok M hi (by omega_using [hw, hav]) R Lv Rv fv kv }
  obtain ⟨V, R⟩ := h.rep
  apply driver.run_ok h.layout R
  intro t Lt Rt ft kt
  have ff : Frame p.core.changed s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.core.F, frameBytes⟩ (by simp [GeneratorPlan.changed])
    change ¬ ofs p.core.F a < frameBytes at hn
    change 168 ≤ ofs p.core.F a
    unfold frameBytes at hn
    omega_using [hn]
  refine ⟨upd W 20 0, h.frame Lt ⟨V, Rt⟩ ?_ ff kt.rd kt.wr,
    by simp [upd], rfl, (Nat.zero_add _).symm, ff, kt.rd, kt.wr⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.Pack`, which only this module used -/

section

/-! # Pack all three generated parameters into p || q || g -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PackInto.lean`, which only this module imported.
section

/-! # Pack a component into a bounded domain buffer, preserving all sources -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem packInto_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src d total : Nat} {bs : List Byte}
    (hs : src < 2 ^ 16) (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (ht : total ≤ 1024) (hroom : d + bs.length ≤ total)
    (source : Src s (VG.Proof.Bignum.off (W 5) packed) total (VG.Proof.Bignum.off (W 5) src) bs)
    (hwr : ∀ i < total, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) packed, total⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) packed, total⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.packPart src (packed + d) bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d) bs.length = bs ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d, bs.length⟩] s.mem t.mem ∧
      InScr (VG.Proof.Bignum.off (W 5) packed) total s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have hd : packed + d < 2 ^ 16 := by unfold packed; omega
  have sub : Region.Sub ⟨VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d, bs.length⟩ ⟨VG.Proof.Bignum.off (W 5) packed, total⟩ :=
    Offset.sub_base _ hroom
  refine WP.mono (packPart_ok L R hs hd hl source.rd
    (fun i hi => by rw [← VG.Proof.Bignum.off_off, VG.Proof.Bignum.off_off]; exact hwr (d + i) (by omega))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using source.val i hi)
    (by
      intro i hi j hj he
      have hout := source.out i hi
      change total ≤ ofs (VG.Proof.Bignum.off (W 5) packed) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i) at hout
      rw [he, ← VG.Proof.Bignum.off_off, VG.Proof.Bignum.off_off] at hout
      simp only [ofs, VG.Proof.Bignum.off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : d + j < 2 ^ 64)] at hout
      omega)
    (by rw [← VG.Proof.Bignum.off_off]; exact hF.sub_right sub)
    (by rw [← VG.Proof.Bignum.off_off]; exact hS.sub_right sub)) fun t ⟨result, Lt, Rt, ft, kt⟩ => ?_
  have frame : Frame [⟨VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d, bs.length⟩] s.mem t.mem := by
    simpa only [VG.Proof.Bignum.off_off] using ft
  refine ⟨by simpa only [VG.Proof.Bignum.off_off] using result, Lt, Rt, frame, ?_, kt⟩
  intro a ha
  apply frame a
  intro r hr hc
  rcases List.mem_singleton.mp hr with rfl
  have inside := sub a hc
  change ofs (VG.Proof.Bignum.off (W 5) packed) a + 1 ≤ total at inside
  omega

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem pack_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {pb qb gb : List Byte} {pLen qLen : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hp : pb.length = pLen) (hq : qb.length = qLen) (hg : gb.length = pLen)
    (hl : 2 ≤ pLen ∧ 2 ≤ qLen ∧ 2 * pLen + qLen ≤ 1024)
    (sp : Src s (VG.Proof.Bignum.off (W 5) packed) (2 * pLen + qLen) (VG.Proof.Bignum.off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sq : Src s (VG.Proof.Bignum.off (W 5) packed) (2 * pLen + qLen) (VG.Proof.Bignum.off (W 5) q) qb)
    (sg : Src s (VG.Proof.Bignum.off (W 5) packed) (2 * pLen + qLen) (VG.Proof.Bignum.off (W 5) g) gb)
    (hwr : ∀ i < 2 * pLen + qLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) packed, 2 * pLen + qLen⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) packed, 2 * pLen + qLen⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.pack pLen qLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) packed) (2 * pLen + qLen) = pb ++ qb ++ gb ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨VG.Proof.Bignum.off (W 5) packed, 2 * pLen + qLen⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.pack
  change WP isa (.seq _ (.seq _ _)) s _
  have first := packInto_ok (d := 0) L R (by decide : Impl.Dsa.Generation.Layout.p < 2 ^ 16)
    (by omega_using [hp, hl]) hl.2.2 (by omega_using [hp]) sp hwr hF hS
  simp only [Nat.add_zero, hp] at first
  refine WP.seq (WP.mono first fun u ⟨bu, Lu, Ru, _, fu, ku⟩ => ?_)
  have second := packInto_ok (d := pLen) Lu Ru (by decide : q < 2 ^ 16)
    (by omega_using [hq, hl]) hl.2.2 (by omega_using [hq]) (sq.congrK fu ku)
    (fun i hi => by rw [ku.wr]; exact hwr i hi) hF hS
  simp only [hq] at second
  refine WP.seq (WP.mono second fun v ⟨bv, Lv, Rv, fv, iv, kv⟩ => ?_)
  have third := packInto_ok (d := pLen + qLen) Lv Rv (by decide : g < 2 ^ 16)
    (by omega_using [hg, hl]) hl.2.2 (by omega_using [hg]) (sg.congrK (fu.trans iv) (ku.trans kv))
    (fun i hi => by rw [kv.wr, ku.wr]; exact hwr i hi) hF hS
  simp only [hg] at third
  simp only [Impl.Bignum.AArch64.seqs, Nat.add_assoc]
  refine WP.mono third fun t ⟨bt, Lt, Rt, ft, it, kt⟩ => ?_
  have keep := (ku.trans kv).trans kt
  have inside := (fu.trans iv).trans it
  refine ⟨?_, Lt, Rt, ?_, keep.mono (by decide)⟩
  · have preserveP : Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) packed) pLen = pb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])) (by omega_using [hl]),
        VG.Proof.Dsa.Generation.frame_bytesAt fv (by
          intro r hr; rcases List.mem_singleton.mp hr with rfl
          exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])) (by omega_using [hl])]
      simpa [VG.Proof.Bignum.off] using bu
    have preserveQ : Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) pLen) qLen = qb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.disjoint _ (Or.inl (by omega_using [])) (by omega_using [hl]) (by omega_using [hl])) (by omega_using [hl])]
      exact bv
    rw [show 2 * pLen + qLen = (pLen + qLen) + pLen by omega_using [],
      VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
      preserveP, preserveQ, bt]
  · intro a ha
    apply inside a
    have hn := ha ⟨VG.Proof.Bignum.off (W 5) packed, 2 * pLen + qLen⟩ (by simp)
    change ¬ ofs (VG.Proof.Bignum.off (W 5) packed) a < 2 * pLen + qLen at hn
    omega_using [hn]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The stage, from the generator search to the domain check

The generation's own search, then, once it finds a g, the packing of
p ‖ q ‖ g and the domain check, leave the status of `Proof.Dsa.GeneratorStage.stage`
in the generation's status slot, and the packed domain when it is valid. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Validate.lean`, which only this module imported.
section

/-! # Domain-check results control native seed retry or acceptance -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem validate_ok (M : Mont) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = VG.Proof.Bignum.off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 16) (hq : p.qLen < 2 ^ 16)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.validate M.mm p.pLen p.qLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd W 19 (BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 2))) ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.validate
  refine WP.seq (WP.mono (validateCore_ok M p L R hbase hp hq hs src hF hS)
    fun u ⟨hr, Lu, Ru, fu, ku⟩ => ?_)
  have hz := validateTest_ok hr
  have fv : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem u.mem :=
    fu.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)
  have finish (status : Nat) (hstatus : status < 2 ^ 16) :
      WP isa (.block (Impl.Dsa.AArch64.Generation.stackStatus status)) u fun t =>
        Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) ∧
        Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
    refine WP.mono (stackStatus_ok Lu Ru status hstatus) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    refine ⟨Lt, Rt, fv.trans ?_, (ku.trans kt).mono (by decide)⟩
    intro a ha
    apply ft a
    right
    have hn := ha ⟨F, frameBytes⟩ (by simp)
    change ¬ ofs F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  cases hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params with
  | false =>
    refine WP.ite true (by simp [hz, hc]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hc, Bool.false_eq_true, ite_false] using finish 2 (by decide)
  | true =>
    refine WP.ite false (by simp [hz, hc]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simpa only [hc, ite_true] using finish 1 (by decide)

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (GeneratorSearchPlan GeneratorSearchMemory)
open VG.Proof.RsaOaep.AArch64 (Lay Rep upd)

variable {pLen : Nat} {s : State}

/-- q's bytes, for p's. -/
abbrev qLen (pLen : Nat) : Nat := Impl.Dsa.AArch64.Generator.qLen pLen

/-- What the stage computes. -/
abbrev result (pLen : Nat) (s : State) : Option Spec.Dsa.Params :=
  Proof.Dsa.GeneratorStage.stage (pOf pLen s.mem (s.gpr .x0)) (qOf pLen s.mem (s.gpr .x0))
    (Proof.Dsa.GeneratorStage.candidates pLen (tape s))

/-- How the stage ends (`Proof.Dsa.GeneratorStage.code`). -/
abbrev endCode (pLen : Nat) (s : State) : Nat :=
  Proof.Dsa.GeneratorStage.code (pOf pLen s.mem (s.gpr .x0)) (qOf pLen s.mem (s.gpr .x0))
    (Proof.Dsa.GeneratorStage.candidates pLen (tape s))

/-- The h candidates the search reads. -/
abbrev readCount (pLen : Nat) (s : State) : Nat :=
  VG.Proof.Dsa.Generation.generatorCount (pOf pLen s.mem (s.gpr .x0)) (qOf pLen s.mem (s.gpr .x0))
    (Proof.Dsa.GeneratorStage.candidates pLen (tape s))

/-- The memory the stage writes. -/
def stageChanged (pLen : Nat) (s : State) : List Region :=
  [⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩, ⟨s.gpr .x0, Impl.Dsa.Layout.activeBytes⟩,
    ⟨off (s.gpr .x0) g, pLen⟩, ⟨off (s.gpr .x0) packed, 2 * pLen + qLen pLen⟩,
    ⟨off (s.gpr .x0) domainCheck, Impl.Dsa.Layout.usedBytes⟩, ⟨frameBase s, frameBytes⟩]

/-- What the stage leaves. -/
structure Staged (pLen : Nat) (s u t : State) : Prop where
  lay : Lay t (frameBase s) (hashBase s)
  rep : ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0 ∧
    W 19 = BitVec.ofNat 64 (endCode pLen s) ∧ W 20 = BitVec.ofNat 64 (pLen * readCount pLen s)
  packed : ∀ a, result pLen s = some a →
    Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) = Spec.Dsa.encodeParams pLen (qLen pLen) a
  frame : Frame (stageChanged pLen s) u.mem t.mem
  rd : t.rd = u.rd
  wr : t.wr = u.wr

theorem Supported.lengths {pLen : Nat} (hb : Supported pLen) : Spec.Dsa.lengthsValid pLen (qLen pLen) := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem Supported.q_le {pLen : Nat} (hb : Supported pLen) : 2 ≤ qLen pLen ∧ qLen pLen ≤ 32 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem StageABI.parts (hb : Supported pLen) (A : StageABI pLen s) {d n e k : Nat}
    (hd : d + n ≤ usedBytes pLen) (he : e + k ≤ usedBytes pLen) (h : d + n ≤ e ∨ e + k ≤ d) :
    (⟨off (s.gpr .x0) d, n⟩ : Region).Disjoint ⟨off (s.gpr .x0) e, k⟩ :=
  (arena hb A).parts_disjoint hd he h

theorem StageABI.framePart (hb : Supported pLen) (A : StageABI pLen s) {d n : Nat} (h : d + n ≤ usedBytes pLen) :
    (⟨frameBase s, frameBytes⟩ : Region).Disjoint ⟨off (s.gpr .x0) d, n⟩ :=
  (arena hb A).frame_part h

/-- The search's result is the generator `Proof.Dsa.GeneratorStage.stage` starts from. -/
theorem plan_remaining (hb : Supported pLen) (A : StageABI pLen s) :
    (plan hb A).remaining 0 = Spec.Dsa.generator (pOf pLen s.mem (s.gpr .x0)) (qOf pLen s.mem (s.gpr .x0))
      (Proof.Dsa.GeneratorStage.candidates pLen (tape s)) := by
  simp only [GeneratorSearchPlan.remaining, plan, Arena.generatorPlan, arena, List.drop_zero,
    Proof.Dsa.GeneratorStage.candidates]
  rfl

/-- The candidates the search reads are those `count` names. -/
theorem plan_count (hb : Supported pLen) (A : StageABI pLen s) :
    (plan hb A).count 0 = readCount pLen s := by
  simp only [GeneratorSearchPlan.count, plan, Arena.generatorPlan]
  rfl

theorem StageABI.packed_sep (hb : Supported pLen) (A : StageABI pLen s) {d n : Nat} (hd : d + n ≤ packed) :
    (⟨off (s.gpr .x0) d, n⟩ : Region).Disjoint ⟨off (s.gpr .x0) packed, 2 * pLen + qLen pLen⟩ := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have := hb.q_le
  have hp0 := used_small hb (d := packed) (n := 0) (by decide) (by decide)
  exact A.parts hb (by omega_using [hd, hp0])
    (used_small hb (by decide) (by unfold arithmeticBytes; omega_using [pn, this])) (Or.inl hd)

/-- The search's status: 1 when it finds a g, 3 when it does not. -/
def statusOf (pl : GeneratorSearchPlan) : BitVec 64 := if (pl.remaining 0).isSome then 1 else 3

/-- The g the search finds. -/
abbrev gOf (pl : GeneratorSearchPlan) : Nat := (pl.remaining 0).getD 0

/-- The domain the stage checks. -/
abbrev domainOf (pLen : Nat) (s : State) (pl : GeneratorSearchPlan) : Spec.Dsa.Params :=
  ⟨pOf pLen s.mem (s.gpr .x0), qOf pLen s.mem (s.gpr .x0), gOf pl⟩

/-- What the generator search leaves. -/
structure Searched (hb : Supported pLen) (A : StageABI pLen s) (u t : State) : Prop where
  lay : Lay t (frameBase s) (hashBase s)
  rep : ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0 ∧ W 19 = statusOf (plan hb A) ∧
    W 20 = BitVec.ofNat 64 (pLen * (plan hb A).count 0)
  scr : Scr t (s.gpr .x0) (usedBytes pLen)
  bytes : (plan hb A).remaining 0 ≠ none →
    Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.p) pLen =
        Spec.Dsa.encodeBE pLen (pOf pLen s.mem (s.gpr .x0)) ∧
      Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.q) (qLen pLen) =
        Spec.Dsa.encodeBE (qLen pLen) (qOf pLen s.mem (s.gpr .x0)) ∧
      Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) g) pLen = Spec.Dsa.encodeBE pLen (gOf (plan hb A))
  frame : Frame (stageChanged pLen s) u.mem t.mem
  rd : t.rd = u.rd
  wr : t.wr = u.wr

theorem Searched.congr {hb : Supported pLen} {A : StageABI pLen s} {u t t' : State} (h : Searched hb A u t)
    (hm : t'.mem = t.mem) (hk : Keep [.x3, .x4] t t') : Searched hb A u t' := by
  obtain ⟨V, W, R, h5, h19, h20⟩ := h.rep
  exact ⟨h.lay.congr hk.sp hk.wr (by rw [hm]), ⟨V, W, hm ▸ R, h5, h19, h20⟩, h.scr.congr hk.wr,
    fun hs => by rw [hm]; exact h.bytes hs, hm ▸ h.frame, hk.rd.trans h.rd, hk.wr.trans h.wr⟩

theorem search_ok (M : Mont) (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorSearch M.mm pLen) u (Searched hb A u) := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have coreCh : (plan hb A).core.changed = [⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩,
      ⟨s.gpr .x0, Impl.Dsa.Layout.activeBytes⟩, ⟨off (s.gpr .x0) g, pLen⟩, ⟨frameBase s, frameBytes⟩] := rfl
  have keepPart : ∀ {d n : Nat}, VG.Impl.Dsa.Generation.Layout.q ≤ d → d + n ≤ g →
      ∀ r ∈ (plan hb A).core.changed, Region.Disjoint ⟨off (s.gpr .x0) d, n⟩ r := fun h1 h2 r hr => by
    rw [coreCh] at hr
    have := (arena hb A).gWork_separate h1 h2 r (by simpa [Arena.gWork, arena, Arena.part] using hr)
    simpa [arena, Arena.part] using this
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.nativeGenerator_ok M (prepared hb A E))
    fun t ⟨W', mt, h20, outcome, ft, rdt, wrt⟩ => ?_
  obtain ⟨V, R⟩ := mt.rep
  have bytesT : ∀ {d n : Nat}, VG.Impl.Dsa.Generation.Layout.q ≤ d → d + n ≤ g →
      Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) d) n = Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) d) n := fun h1 h2 => by
    have g0 := used_small hb (d := g) (n := 0) (by decide) (by decide)
    have gl : g ≤ 2 ^ 64 := by decide
    rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (keepPart h1 h2) (by omega_using [h2, gl]), A.bytes_entered hb E (by unfold Impl.Dsa.AArch64.Generator.spill VG.Impl.Dsa.Generation.Layout.control g at *; omega_using [h2])]
  refine ⟨mt.layout, ⟨V, W', R, mt.base, ?_, h20⟩, (A.scr E).congr wrt, fun hs => ?_, ft.mono ?_, rdt, wrt⟩
  · rcases outcome with ⟨h3, hn⟩ | ⟨gv, h1, hgv, _⟩
    · rw [h3]; simp [statusOf, ← hn]
    · rw [h1]; simp [statusOf, hgv]
  · rcases outcome with ⟨_, hn⟩ | ⟨gv, _, hgv, bg⟩
    · exact absurd hn hs
    refine ⟨?_, ?_, ?_⟩
    rotate_left 2
    · change Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) g) pLen = Spec.Dsa.encodeBE pLen gv at bg
      simpa [gOf, hgv] using bg
    · rw [bytesT (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega_using [pn])]
      have := VG.Proof.Dsa.encodeBE_decodeBE (pBytes pLen s)
      rw [bytesAt_length] at this
      exact this.symm
    · rw [bytesT (Nat.le_refl _) (by unfold VG.Impl.Dsa.Generation.Layout.q g; omega_using [qn])]
      have := VG.Proof.Dsa.encodeBE_decodeBE (qBytes pLen s)
      rw [bytesAt_length] at this
      exact this.symm
  · intro r hr; rw [coreCh] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [stageChanged]

/-- What packing leaves. -/
structure Packed (hb : Supported pLen) (A : StageABI pLen s) (u t : State) : Prop where
  lay : Lay t (frameBase s) (hashBase s)
  rep : ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0 ∧
    W 20 = BitVec.ofNat 64 (pLen * (plan hb A).count 0)
  scr : Scr t (s.gpr .x0) (usedBytes pLen)
  bytes : Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) =
    Spec.Dsa.encodeParams pLen (qLen pLen) (domainOf pLen s (plan hb A))
  frame : Frame (stageChanged pLen s) u.mem t.mem
  rd : t.rd = u.rd
  wr : t.wr = u.wr

theorem pack_stage_ok (hb : Supported pLen) (A : StageABI pLen s) {u t : State} (S : Searched hb A u t)
    (h19 : statusOf (plan hb A) = 1) :
    WP isa (Impl.Dsa.AArch64.Generation.pack pLen (qLen pLen)) t (Packed hb A u) := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have c1 : packed = 27008 := rfl
  have c2 : g = 26240 := rfl
  have c3 : VG.Impl.Dsa.Generation.Layout.p = 25472 := rfl
  have c4 : VG.Impl.Dsa.Generation.Layout.q = 25408 := rfl
  have c5 : arithmeticBytes = 12288 := rfl
  have c6 : domainCheck = 40960 := rfl
  have c12 : usedBytes pLen = domainCheck + 128 * pLen := rfl
  have p128 : 128 ≤ pLen := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hpk := used_small hb (d := packed) (n := 2 * pLen + qLen pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have hs : (plan hb A).remaining 0 ≠ none := by
    intro hn; simp [statusOf, hn] at h19
  obtain ⟨pE, qE, gE⟩ := S.bytes hs
  obtain ⟨V, W, R, h5, _, h20⟩ := S.rep
  have src (d n : Nat) (bs : List Byte) (hl : bs.length = n) (hd : d + n ≤ packed)
      (hbs : Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) d) n = bs) :
      Src t (off (W 5) packed) (2 * pLen + qLen pLen) (off (W 5) d) bs := by
    rw [h5]
    subst hl
    exact VG.Proof.Dsa.AArch64.Generation.arena_source S.scr (by unfold packed at hd; omega_using [c6, c12, hd])
      (by have := used_lt hb; unfold packed at hd; omega_using [hd]) hbs (A.packed_sep hb hd)
  have hS : (⟨hashBase s, oRsa⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen pLen⟩ := by
    rw [h5]; exact A.packed_sep hb (d := VG.Impl.Dsa.Generation.Layout.hash) (by decide)
  have hF : (⟨frameBase s, frameBytes⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen pLen⟩ := by
    rw [h5]; exact A.framePart hb hpk
  refine WP.mono (VG.Proof.Dsa.AArch64.Generation.pack_ok S.lay R (VG.Proof.Dsa.encodeBE_length _ _)
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) ⟨by omega_using [p128], qn.1, by omega_using [pn, qn]⟩
    (src _ _ _ (VG.Proof.Dsa.encodeBE_length _ _) (by unfold VG.Impl.Dsa.Generation.Layout.p packed; omega_using [pn]) pE)
    (src _ _ _ (VG.Proof.Dsa.encodeBE_length _ _) (by unfold VG.Impl.Dsa.Generation.Layout.q packed; omega_using [qn]) qE)
    (src _ _ _ (VG.Proof.Dsa.encodeBE_length _ _) (by unfold g packed; omega_using [pn]) gE)
    (fun i hi => by rw [h5, off_off]; exact S.scr.region (by omega_using [hpk, hi]) (by decide)) hF hS)
    fun t₁ ⟨bytes₁, L₁, R₁, f₁, k₁⟩ => ⟨L₁, ⟨V, W, R₁, h5, h20⟩, S.scr.congr k₁.wr, by rw [← h5]; exact bytes₁,
      S.frame.trans (f₁.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; rw [h5]; simp [stageChanged])),
      k₁.rd.trans S.rd, k₁.wr.trans S.wr⟩

/-- The domain check's inputs. -/
def checkInput (hb : Supported pLen) (s : State) (pl : GeneratorSearchPlan) : Proof.Dsa.AArch64.ParametersInput :=
  ⟨off (s.gpr .x0) domainCheck, pLen, qLen pLen, Spec.Dsa.encodeParams pLen (qLen pLen) (domainOf pLen s pl),
    hb.lengths, VG.Proof.Dsa.Generation.encodeParams_length _ _ _⟩

theorem StageABI.domainCheck_room (hb : Supported pLen) : domainCheck + Impl.Dsa.Layout.usedBytes ≤ usedBytes pLen := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem StageABI.packed_domain (hb : Supported pLen) (A : StageABI pLen s) :
    (⟨off (s.gpr .x0) packed, 2 * pLen + qLen pLen⟩ : Region).Disjoint
      ⟨off (s.gpr .x0) domainCheck, Impl.Dsa.Layout.usedBytes⟩ := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  exact A.parts hb (used_small hb (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])) (StageABI.domainCheck_room hb)
    (Or.inl (by unfold packed domainCheck; omega_using [pn, qn]))

theorem Packed.check_src {hb : Supported pLen} {A : StageABI pLen s} {u t : State} (P : Packed hb A u t) :
    Src t (checkInput hb s (plan hb A)).base Impl.Dsa.Layout.usedBytes (off (s.gpr .x0) packed)
      (checkInput hb s (plan hb A)).params := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hpk := used_small hb (d := packed) (n := 2 * pLen + qLen pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have := VG.Proof.Dsa.AArch64.Generation.arena_source (bs := Spec.Dsa.encodeParams pLen (qLen pLen) (domainOf pLen s (plan hb A)))
    P.scr (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; exact hpk)
    (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; have := used_lt hb; omega_using [pn, qn])
    (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; exact P.bytes)
    (by rw [VG.Proof.Dsa.Generation.encodeParams_length]; exact A.packed_domain hb)
  exact this

theorem Packed.check_scr {hb : Supported pLen} {A : StageABI pLen s} {u t : State} (P : Packed hb A u t) :
    Scr t (checkInput hb s (plan hb A)).base Impl.Dsa.Layout.usedBytes :=
  P.scr.sub (StageABI.domainCheck_room hb) (by decide)

theorem stage_ok (M : Mont) (hb : Supported pLen) (A : StageABI pLen s) {u : State} (E : Entered pLen s u) :
    WP isa (Impl.Dsa.AArch64.Generator.stage M.mm pLen) u (Staged pLen s u) := by
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hhash := used_small hb (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hpk := used_small hb (d := packed) (n := 2 * pLen + qLen pLen) (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have rem := plan_remaining hb A
  have cnt := plan_count hb A
  unfold Impl.Dsa.AArch64.Generator.stage
  refine WP.seq (WP.mono (search_ok M hb A E) fun t S => ?_)
  obtain ⟨V, W, R, h5, h19, h20⟩ := S.rep
  apply VG.Proof.Dsa.AArch64.Generation.onSuccess_ok S.lay R
  · intro t' hm' kt h1
    have S' := S.congr hm' kt
    have hst : statusOf (plan hb A) = 1 := h19.symm.trans h1
    obtain ⟨gv, hgv⟩ : ∃ gv, (plan hb A).remaining 0 = some gv := by
      cases h : (plan hb A).remaining 0 with
      | none => simp [statusOf, h] at hst
      | some gv => exact ⟨gv, rfl⟩
    unfold Impl.Dsa.AArch64.Generation.finishDomain
    refine WP.seq (WP.mono (pack_stage_ok hb A S' hst) fun t₁ P => ?_)
    obtain ⟨V₁, W₁, R₁, h5₁, h20₁⟩ := P.rep
    have pfit := (A.p_bounds hb).2
    have bounds := VG.Proof.Dsa.Generation.generator_bounds (Nat.lt_trans Nat.zero_lt_one (A.positive hb)) _
      (rem ▸ hgv)
    have qfit : qOf pLen s.mem (s.gpr .x0) < 256 ^ qLen pLen :=
      Nat.lt_of_lt_of_eq (VG.Proof.Dsa.decodeBE_lt _) (by rw [bytesAt_length]; rfl)
    have gdef : gOf (plan hb A) = gv := by simp [gOf, hgv]
    have check := VG.Proof.Dsa.Generation.check_encodedParams (a := domainOf pLen s (plan hb A)) hb.lengths pfit qfit
      (by show gOf (plan hb A) < _; rw [gdef]; exact Nat.lt_trans bounds.2 pfit)
    refine WP.mono (VG.Proof.Dsa.AArch64.Generation.validate_ok M (checkInput hb s (plan hb A)) P.lay R₁
      (by rw [h5₁]; rfl) (by change pLen < 2 ^ 16; omega_using [pn]) (by change qLen pLen < 2 ^ 16; omega_using [qn])
      P.check_scr (by rw [h5₁]; exact P.check_src)
      (A.framePart hb (StageABI.domainCheck_room hb))
      (A.parts hb hhash (StageABI.domainCheck_room hb) (Or.inl (by decide))))
      fun t₂ ⟨L₂, R₂, f₂, k₂⟩ => ?_
    have res : result pLen s = if Spec.Dsa.parametersValid (domainOf pLen s (plan hb A))
        then some (domainOf pLen s (plan hb A)) else none := by
      rw [rem] at hgv
      simp only [result, Proof.Dsa.GeneratorStage.stage, hgv, Option.bind_eq_bind, Option.bind_some, domainOf, gdef]
    refine ⟨L₂, ⟨V₁, _, R₂, by simpa [VG.Proof.RsaOaep.AArch64.upd] using h5₁, ?_,
      by simpa [VG.Proof.RsaOaep.AArch64.upd, cnt] using h20₁⟩, fun a' ha' => ?_, ?_, k₂.rd.trans P.rd, k₂.wr.trans P.wr⟩
    · rw [rem] at hgv
      have hd : domainOf pLen s (plan hb A) = ⟨pOf pLen s.mem (s.gpr .x0), qOf pLen s.mem (s.gpr .x0), gv⟩ := by
        simp only [domainOf, gdef]
      simp only [VG.Proof.RsaOaep.AArch64.upd, ite_true, checkInput, check]
      simp only [endCode, Proof.Dsa.GeneratorStage.code, hgv, hd, decide_eq_true_eq]
    · rw [res] at ha'
      split at ha'
      · obtain rfl := Option.some.inj ha'
        rw [VG.Proof.Dsa.Generation.frame_bytesAt f₂ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact A.packed_domain hb
          · exact (A.framePart hb hpk).symm) (by omega_using [pn, qn])]
        exact P.bytes
      · exact absurd ha' (by simp)
    · refine P.frame.trans (f₂.mono ?_)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [stageChanged, checkInput]
  · intro t' hm' kt h1
    have S' := S.congr hm' kt
    have hn : (plan hb A).remaining 0 = none := by
      cases h : (plan hb A).remaining 0 with
      | none => rfl
      | some gv => exact absurd (h19.trans (by simp [statusOf, h])) h1
    have res : result pLen s = none := by
      rw [rem] at hn
      simp only [result, Proof.Dsa.GeneratorStage.stage, hn, Option.bind_eq_bind, Option.bind_none]
    obtain ⟨V', W', R', h5', h19', h20'⟩ := S'.rep
    refine ⟨S'.lay, ⟨V', W', R', h5', by
      rw [h19']; simp only [statusOf, endCode, Proof.Dsa.GeneratorStage.code, ← rem, hn]; rfl,
      by rw [h20', cnt]⟩, fun a ha => absurd ha (by rw [res]; simp),
      S'.frame, S'.rd, S'.wr⟩

end VG.Proof.Dsa.AArch64.Generator
