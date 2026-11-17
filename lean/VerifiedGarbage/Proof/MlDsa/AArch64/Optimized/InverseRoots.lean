module

public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

/-! ### `MlDsa.AArch64.Optimized.InverseTableMemory`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTable
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

/-- The immutable inverse table's actual packed artifact data. -/
def Artifact (m : Mem) (p : Addr) : Prop :=
  ∀ i<488, m.readW (p+BitVec.ofNat 64 (8*i)) 64=expandedWords[i]!

def Words (m : Mem) (p : Addr) : Prop :=
  ∀ k<976, m.readW (p+BitVec.ofNat 64 (4*k)) 32=BitVec.ofNat 32 expandedVals[k]!

theorem Artifact.words {m : Mem} {p : Addr} (h : Artifact m p) : Words m p := by
  intro k hk
  have hi : k/2<488 := by omega_using [hk]
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega_using []
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,expandedWords_low hi] at hx
    simpa only [show 8*(k/2)=4*k by omega_using [hr],← he] using hx
  · have he : k=2*(k/2)+1 := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,expandedWords_high hi,BitVec.add_assoc,
      ← BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega_using [hr],← he] using hx

theorem Words.vector {m : Mem} {p : Addr} (h : Words m p)
    {k e : Nat} (hk : k+4≤976) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (4*k)) 16) e=BitVec.ofNat 32 expandedVals[k+e]! := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,
    BitVec.add_assoc,← BitVec.ofNat_add,← Nat.mul_add]
  exact h _ (by omega_using [hk, he])

/-- A pair of SIMD loads selects a root and its reciprocal from one row. -/
theorem Words.row {m : Mem} {p : Addr} (h : Words m p)
    {u off g e root : Nat} (ho : off%4=0) (he : e<4)
    (hb : 480*u+off+32*g+32≤3904)
    (hv : expandedVals[120*u+off/4+8*g+e]! = z root ∧
      expandedVals[120*u+off/4+8*g+e+4]! = bar (z root)) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+off+32*g)) 16) e=BitVec.ofNat 32 (z root) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+off+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z root)) := by
  have h0 : 480*u+off+32*g=4*(120*u+off/4+8*g) := by omega_using [ho]
  have h1 : 480*u+off+32*g+16=4*(120*u+off/4+8*g+4) := by omega_using [ho]
  constructor
  · rw [h0,h.vector (by omega_using [hb]) he,hv.1]
  · rw [h1,h.vector (by omega_using [hb]) he]
    rw [show 120*u+off/4+8*g+4+e=120*u+off/4+8*g+e+4 by omega_using [],hv.2]

end VG.Proof.MlDsa.AArch64.Optimized.InverseTable

end

end

/-! ## From `InverseTableDecode.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTable
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem Words.layer1 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g)) 16) e=BitVec.ofNat 32 (z (255-16*u-4*g-e)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (255-16*u-4*g-e))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer1_values hu hg he)

theorem Words.layer2 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g)) 16) e=BitVec.ofNat 32 (z (127-8*u-2*g-e/2)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (127-8*u-2*g-e/2))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer2_values hu hg he)

theorem Words.layer4 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g)) 16) e=BitVec.ofNat 32 (z (63-4*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (63-4*u-g))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer4_values hu hg he)

theorem Words.layer8 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g)) 16) e=BitVec.ofNat 32 (z (31-2*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (31-2*u-g))) := by
  exact h.row (by decide) he (by omega_using [hu, hg]) (layer8_values hu hg he)

theorem Words.layer16 {m : Mem} {p : Addr} (h : Words m p)
    {u e : Nat} (hu : u<8) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+448)) 16) e=BitVec.ofNat 32 (z (15-u)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+464)) 16) e=BitVec.ofNat 32 (bar (z (15-u))) := by
  exact h.row (g := 0) (off := 448) (by decide) he (by omega_using [hu]) (layer16_values hu he)

theorem Words.tail {m : Mem} {p : Addr} (h : Words m p)
    {j e : Nat} (hj : j<2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (3840+16*j)) 16) e=BitVec.ofNat 32 (z (7-(4*j+e))) ∧
    vword (m.read (p+BitVec.ofNat 64 (3872+16*j)) 16) e=BitVec.ofNat 32 (bar (z (7-(4*j+e)))) := by
  have hv := tail_values (j := 4*j+e) (by omega_using [hj, he])
  have h0 : 3840+16*j=4*(960+4*j) := by omega_using []
  have h1 : 3872+16*j=4*(968+4*j) := by omega_using []
  constructor
  · rw [h0,h.vector (by omega_using [hj]) he,show 960+4*j+e=960+(4*j+e) by omega_using [],hv.1]
  · rw [h1,h.vector (by omega_using [hj]) he,show 968+4*j+e=968+(4*j+e) by omega_using [],hv.2]

end VG.Proof.MlDsa.AArch64.Optimized.InverseTable

end

/-! ## From `InverseRoots.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

/-- Static table root and reciprocal, loaded without touching the live bank. -/
theorem rootLoads_ok (off : Nat) (ha : off%16=0) (hi : off+16<65536)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16)
    (k : ∀ t, VChg [.v20,.v21] s t →
      t.v .v20=s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16 →
      t.v .v21=s.mem.read (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16 → WP isa (.block rest) t Q) :
    WP isa (.block (.ldrq .v20 .x1 off :: .ldrq .v21 .x1 (off+16) :: rest)) s Q := by
  refine wp_ldrq (by omega_using [ha, hi]) rfl hr fun a h₁ => ?_
  refine wp_ldrq (by omega_using [ha, hi]) rfl ?_ fun t h₂ => ?_
  · simpa only [h₁.rd,h₁.wr,h₁.gpr] using hb
  · refine k t (h₁.chg.trans h₂.chg) ?_ ?_
    · rw [h₂.get .v20,h₁.v]
    · rw [h₂.v,h₁.mem,h₁.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
