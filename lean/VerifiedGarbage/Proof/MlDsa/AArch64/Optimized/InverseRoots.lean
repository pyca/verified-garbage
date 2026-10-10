import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableMemory
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun

/-! ## From `InverseTableDecode.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTable
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem Words.layer1 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g)) 16) e=BitVec.ofNat 32 (z (255-16*u-4*g-e)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (255-16*u-4*g-e))) := by
  exact h.row (by decide) he (by omega) (layer1_values hu hg he)

theorem Words.layer2 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g)) 16) e=BitVec.ofNat 32 (z (127-8*u-2*g-e/2)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (127-8*u-2*g-e/2))) := by
  exact h.row (by decide) he (by omega) (layer2_values hu hg he)

theorem Words.layer4 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g)) 16) e=BitVec.ofNat 32 (z (63-4*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (63-4*u-g))) := by
  exact h.row (by decide) he (by omega) (layer4_values hu hg he)

theorem Words.layer8 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g)) 16) e=BitVec.ofNat 32 (z (31-2*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (31-2*u-g))) := by
  exact h.row (by decide) he (by omega) (layer8_values hu hg he)

theorem Words.layer16 {m : Mem} {p : Addr} (h : Words m p)
    {u e : Nat} (hu : u<8) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+448)) 16) e=BitVec.ofNat 32 (z (15-u)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+464)) 16) e=BitVec.ofNat 32 (bar (z (15-u))) := by
  exact h.row (g := 0) (off := 448) (by decide) he (by omega) (layer16_values hu he)

theorem Words.tail {m : Mem} {p : Addr} (h : Words m p)
    {j e : Nat} (hj : j<2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (3840+16*j)) 16) e=BitVec.ofNat 32 (z (7-(4*j+e))) ∧
    vword (m.read (p+BitVec.ofNat 64 (3872+16*j)) 16) e=BitVec.ofNat 32 (bar (z (7-(4*j+e)))) := by
  have hv := tail_values (j := 4*j+e) (by omega)
  have h0 : 3840+16*j=4*(960+4*j) := by omega
  have h1 : 3872+16*j=4*(968+4*j) := by omega
  constructor
  · rw [h0,h.vector (by omega) he,show 960+4*j+e=960+(4*j+e) by omega,hv.1]
  · rw [h1,h.vector (by omega) he,show 968+4*j+e=968+(4*j+e) by omega,hv.2]

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
  refine wp_ldrq (by omega) rfl hr fun a h₁ => ?_
  refine wp_ldrq (by omega) rfl ?_ fun t h₂ => ?_
  · simpa only [h₁.rd,h₁.wr,h₁.gpr] using hb
  · refine k t (h₁.chg.trans h₂.chg) ?_ ?_
    · rw [h₂.get .v20,h₁.v]
    · rw [h₂.v,h₁.mem,h₁.gpr]

/-- Hoisted roots and reciprocals occupy separate vectors in the inverse pass. -/
theorem rootDup_ok (src recip : VReg) (i : Nat) (hi : i<4) (hr : recip≠.v20)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v20,.v21] s t →
      (∀ e<4, vword (t.v .v20) e=vword (s.v src) i) →
      (∀ e<4, vword (t.v .v21) e=vword (s.v recip) i) → WP isa (.block rest) t Q) :
    WP isa (.block (.vop (.dupE .s4 .v20 src i) :: .vop (.dupE .s4 .v21 recip i) :: rest)) s Q := by
  have he (t : State) (d a : VReg) : (VOp.dupE .s4 d a i).eval t=some (d,
      VArr.s4.map2 (fun w _ _ => (t.v a).extractLsb' (w*i) w) 0 0) := by
    simp only [VOp.eval,VArr.esize,show 128/32=4 by decide,hi,ite_true]
  refine wp_vop (he s .v20 src) fun a h₁ => wp_vop (he a .v21 recip) fun t h₂ => ?_
  refine k t (h₁.chg.trans h₂.chg) ?_ ?_
  · intro e h4
    rw [h₂.get .v20,h₁.v,VG.AArch64.vword_map2 _ _ _ h4]
    rfl
  · intro e h4
    rw [h₂.v,VG.AArch64.vword_map2 _ _ _ h4,h₁.get recip hr]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
