module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFromFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorEvaluate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! # Shared memory plan for native generator filtering and exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure GeneratorPlan where
  B : Addr
  A : Addr
  F : Addr
  S : Addr
  hp : Addr
  Z : Nat
  len : Nat
  pb : List Byte
  hb : List Byte
  eb : List Byte
  width : len = 128 ∨ len = 256 ∨ len = 384
  arithmeticBase : B + BitVec.ofNat 64 arithmetic = A
  workspaceRoom : slot (len / 8) 16 ≤ Z
  pLength : pb.length = len
  hLength : hb.length = len
  eLength : eb.length = len
  pPositive : 1 < Spec.Dsa.decodeBE pb
  pOdd : Spec.Dsa.decodeBE pb % 2 = 1
  frameHeaders : ∀ k < 34, ∀ j < 32, Mem.Sep (VG.Proof.Bignum.off F (8 * k)) 8 (VG.Proof.Bignum.off A (8 * j)) 8
  frameOutside : ∀ k < 34, ∀ i < 8, Z ≤ ofs A (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) i)
  frameSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨VG.Proof.Bignum.off B g, len⟩],
    (⟨F, frameBytes⟩ : Region).Disjoint r
  hashSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨VG.Proof.Bignum.off B g, len⟩],
    (⟨S, oRsa⟩ : Region).Disjoint r
  pSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨VG.Proof.Bignum.off B g, len⟩, ⟨F, frameBytes⟩],
    (⟨VG.Proof.Bignum.off B p, len⟩ : Region).Disjoint r
  hSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨VG.Proof.Bignum.off B g, len⟩, ⟨F, frameBytes⟩],
    (⟨hp, len⟩ : Region).Disjoint r
  eSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨VG.Proof.Bignum.off B g, len⟩, ⟨F, frameBytes⟩],
    (⟨VG.Proof.Bignum.off B exponent, len⟩ : Region).Disjoint r
  gArithmeticSeparate : (⟨VG.Proof.Bignum.off B g, len⟩ : Region).Disjoint ⟨A, Z⟩
  gParentOutside : ∀ i < len, Impl.Dsa.Layout.activeBytes ≤ ofs B (VG.Proof.Bignum.off (VG.Proof.Bignum.off B g) i)
  gArithmeticOutside : ∀ i < len, Z ≤ ofs A (VG.Proof.Bignum.off (VG.Proof.Bignum.off B g) i)

def GeneratorPlan.changed (p : GeneratorPlan) : List Region :=
  [⟨p.A, p.Z⟩, ⟨p.B, Impl.Dsa.Layout.activeBytes⟩, ⟨VG.Proof.Bignum.off p.B g, p.len⟩, ⟨p.F, frameBytes⟩]

def GeneratorPlan.value (p : GeneratorPlan) : Nat :=
  Spec.Dsa.powMod (Spec.Dsa.decodeBE p.hb) (Spec.Dsa.decodeBE p.eb) (Spec.Dsa.decodeBE p.pb)

structure GeneratorMemory (p : GeneratorPlan) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.F p.S
  rep : ∃ V, Rep s.mem p.F p.S V W
  base : W 5 = p.B
  input : W 21 = p.hp
  arithmetic : Scr s p.A p.Z
  parent : Scr s p.B Impl.Dsa.Layout.activeBytes
  pArithmetic : Src s p.A p.Z (VG.Proof.Bignum.off p.B Impl.Dsa.Generation.Layout.p) p.pb
  hArithmetic : Src s p.A p.Z p.hp p.hb
  eArithmetic : Src s p.A p.Z (VG.Proof.Bignum.off p.B exponent) p.eb
  pParent : Src s p.B Impl.Dsa.Layout.activeBytes (VG.Proof.Bignum.off p.B Impl.Dsa.Generation.Layout.p) p.pb
  hParent : Src s p.B Impl.Dsa.Layout.activeBytes p.hp p.hb
  eParent : Src s p.B Impl.Dsa.Layout.activeBytes (VG.Proof.Bignum.off p.B exponent) p.eb
  gWrite : ∀ i < p.len, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.B g) i) 1

theorem GeneratorMemory.frame {p : GeneratorPlan} {W W' : Nat → BitVec 64} {s t : State}
    (h : GeneratorMemory p W s) (L : Lay t p.F p.S) (R : ∃ V, Rep t.mem p.F p.S V W')
    (hb : W' 5 = p.B) (hh : W' 21 = p.hp)
    (hf : Frame p.changed s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    GeneratorMemory p W' t := by
  have hn : p.len < 2 ^ 64 := by rcases p.width with hh | hh | hh <;> omega
  have fp : ∀ r ∈ p.changed, (⟨VG.Proof.Bignum.off p.B Impl.Dsa.Generation.Layout.p, p.pb.length⟩ : Region).Disjoint r := by
    rw [p.pLength]; exact p.pSeparate
  have fh : ∀ r ∈ p.changed, (⟨p.hp, p.hb.length⟩ : Region).Disjoint r := by
    rw [p.hLength]; exact p.hSeparate
  have fe : ∀ r ∈ p.changed, (⟨VG.Proof.Bignum.off p.B exponent, p.eb.length⟩ : Region).Disjoint r := by
    rw [p.eLength]; exact p.eSeparate
  exact ⟨L, R, hb, hh, h.arithmetic.congr hwr, h.parent.congr hwr,
    source_of_frame h.pArithmetic hf fp (p.pLength ▸ hn) hrd hwr,
    source_of_frame h.hArithmetic hf fh (p.hLength ▸ hn) hrd hwr,
    source_of_frame h.eArithmetic hf fe (p.eLength ▸ hn) hrd hwr,
    source_of_frame h.pParent hf fp (p.pLength ▸ hn) hrd hwr,
    source_of_frame h.hParent hf fh (p.hLength ▸ hn) hrd hwr,
    source_of_frame h.eParent hf fe (p.eLength ▸ hn) hrd hwr,
    fun i hi => by rw [hwr]; exact h.gWrite i hi⟩

end VG.Proof.Dsa.AArch64.Generation
