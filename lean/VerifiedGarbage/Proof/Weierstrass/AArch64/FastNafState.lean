import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

structure FastPrepCore (base : Addr) (size bits w k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=FastNaf.residual w k j
  mask : s.gpr .x10=BitVec.ofNat 64 (2^w-1)
  sign : s.gpr .x11=BitVec.ofNat 64 (2^(w-1))
  zero : s.gpr .x12=0
  one : s.gpr .x13=1
  ptr : s.gpr .x20=off base (bits+j)

structure FastPrepState (base : Addr) (size bits w k j : Nat) (s : State) : Prop
    extends FastPrepCore base size bits w k j s where
  digits : ∀ i<257,s.mem (off base (bits+i))=if i<j then FastNaf.byte w k i else 0

theorem fastByte_word (w k j : Nat) :
    BitVec.ofNat 8 (BitVec.ofInt 64 (FastNaf.digit w k j)).toNat=FastNaf.byte w k j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,fastWord_toNat,FastNaf.byte_toNat]
  have hb := fastMagnitude_bound w k j
  cases hn : FastNaf.negative w k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := FastNaf.negative_magnitude_pos w k j hn
    simp only [ite_true]; omega

theorem fastStore_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hs : Scr s base size) (hb : bits+264≤size) (hj : j<257)
    (hp : s.gpr .x20=off base (bits+j))
    (hd : s.gpr .x2=BitVec.ofInt 64 (FastNaf.digit w k j)) :
    WP isa (.block [.strb .x2 .x20 0]) s fun t =>
      t.mem=s.mem.writeW (off base (bits+j)) (FastNaf.byte w k j) ∧ KeepRegs [] s t := by
  have hw : InRegions s.wr (s.gpr .x20+BitVec.ofNat 64 0) 1 := by
    rw [hp]; simp only [BitVec.add_zero]
    exact ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  refine WP.mono (strb_ok s (by decide) hw) fun t ht => ?_
  subst t
  refine ⟨?_,fun _ _ => rfl,rfl,rfl,rfl⟩
  simp only [hp,BitVec.add_zero,hd,fastByte_word]

theorem fastRemain_ok (s : State) :
    WP isa (.block Impl.Weierstrass.AArch64.FastNaf.remain) s fun t =>
      (t.gpr .x19=0 ↔ nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=0) ∧
      Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [Impl.Weierstrass.AArch64.FastNaf.remain,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · change (s.gpr .x5 ||| s.gpr .x6 ||| s.gpr .x7 ||| s.gpr .x8 ||| s.gpr .x9)=(0#64) ↔ _
    simp only [BitVec.or_eq_zero_iff]
    simp only [←BitVec.toNat_inj,BitVec.toNat_zero]
    dsimp only [nafVal5]
    omega
  · intro r hr
    have h : r≠.x19 := by simpa using hr
    simp only [RegUpd.gpr_write,h,ite_false]

theorem fastAdvance_ok (s : State) {base : Addr} {bits j d : Nat}
    (hd : d<4096) (hp : s.gpr .x20=off base (bits+j)) :
    WP isa (.block [.addImm .x .x20 .x20 d]) s fun t =>
      t.gpr .x20=off base (bits+(j+d)) ∧ Keeps [.x20] s t := by
  refine WP.mono (addImm_ok s hd) fun t ⟨ht,kt⟩ => ⟨?_,kt⟩
  rw [ht,hp]
  unfold off
  rw [Offset.add_add]
  simp only [Nat.add_assoc]

end VG.Proof.Weierstrass.AArch64
