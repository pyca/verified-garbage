module

import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! The generator's digit `j` of width nine as the joint loop reads it, from its two bytes alone,
for any number of digits (`jointFixedRead_ok` and `jointSignRead_ok` assume P-256's 257). -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- Digit `j`'s low byte in `x2`, where it is in `x16`, and its high byte in `x3`. -/
theorem fixedRead9_ok {c : Joint.Cfg} (h9 : c.gw=9) {s : State} {base : Addr} {size u j : Nat}
    (hs : Scr s base size) (hB : c.gBits+1<4096) (hl : c.gBits+2*j+2≤size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (g : s.mem (off base (c.gBits+2*j))=FastNaf.wbyte u (2*j))
    (g1 : s.mem (off base (c.gBits+(2*j+1)))=FastNaf.wbyte u (2*j+1)) :
    WP isa (.block (Joint.fixedRead c)) s fun t =>
      t.gpr .x2=(FastNaf.wbyte u (2*j)).setWidth 64 ∧ t.gpr .x16=off base (2*j) ∧
      t.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64 ∧ Keeps [.x2,.x3,.x16] s t := by
  rw [Joint.fixedRead,ite_eq_left h9,
    show ([.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x2 .x16 c.gBits,
      .ldrb .x3 .x16 (c.gBits+1)] : List Instr)=[.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,
      .ldrb .x2 .x16 c.gBits]++[.ldrb .x3 .x16 (c.gBits+1)] from rfl,WP.block_append_iff]
  refine WP.mono (nafRead2_ok hs (by omega) (by omega) h19 g .x2 (by decide)) fun a ⟨a2,a16,ka⟩ => ?_
  refine WP.mono (nafHiByte_ok (hs.of_keeps ka (by decide)) hB (by omega) a16 (by rw [ka.mem]; exact g1))
    fun t ⟨t3,kt⟩ => ⟨?_,?_,t3,(ka.mono (by simp)).trans (kt.mono (by simp))⟩
  · rw [kt.gpr _ (by decide),a2]
  · rw [kt.gpr _ (by decide),a16]

/-- Digit `j`'s sign, from its high byte. -/
theorem signRead9_ok {c : Joint.Cfg} (h9 : c.gw=9) {s : State} {base : Addr} {size u j : Nat}
    (hs : Scr s base size) (hB : c.gBits+1<4096) (hl : c.gBits+2*j+2≤size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (g : s.mem (off base (c.gBits+(2*j+1)))=FastNaf.wbyte u (2*j+1)) :
    WP isa (.block (Joint.signRead c)) s fun t =>
      t.gpr .x3=BitVec.ofNat 64 (FastNaf.negative 9 u j).toNat ∧ Keeps [.x3,.x16] s t := by
  rw [Joint.signRead,ite_eq_left h9,
    show ([.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x3 .x16 (c.gBits+1),
      .lsr .x .x3 .x3 7] : List Instr)=[.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19]++
      [.ldrb .x3 .x16 (c.gBits+1),.lsr .x .x3 .x3 7] from rfl,WP.block_append_iff]
  refine WP.mono (nafAdd2_ok hs h19) fun a ⟨a16,ka⟩ => ?_
  exact WP.mono (fixedSignByte_ok (u:=u) (hs.of_keeps ka (by decide)) hB (by omega) a16
    (by rw [ka.mem]; exact g)) fun t ⟨t3,kt⟩ => ⟨t3,(ka.mono (by simp)).trans (kt.mono (by simp))⟩

end VG.Proof.Weierstrass.AArch64
