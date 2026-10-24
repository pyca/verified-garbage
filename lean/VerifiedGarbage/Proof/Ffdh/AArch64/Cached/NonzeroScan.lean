module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! The scalar's nonzero test scans every limb without branching on its value. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure NonzeroInv (s : State) (B : Addr) (e j : Nat) (t : State) : Prop where
 mem : t.mem=s.mem
 keep : Keep [.x3,.x8,.x9,.x12] s t
 pointer : t.gpr .x8=off B (e+8*j)
 value : t.gpr .x9=0#64 ↔ ∀ i<j,word s.mem B (e+8*i)=0#64

theorem nonzeroScanStep_ok {s t : State} {B : Addr} {Z e w j : Nat}
 (scratch : Scr s B Z) (fit : e+8*w≤Z) (inside : j<w) (inv : NonzeroInv s B e j t) :
 WP isa (.block ([ld .x3 .x8,.logic .orr .x .x9 .x9 .x3,next .x8]++([.subImm .x .x12 .x12 1] : List Instr))) t fun u =>
 NonzeroInv s B e (j+1) u ∧ u.gpr .x12=t.gpr .x12-1#64 := by
 rw [WP.block_append_iff]
 refine WP.mono (WP.keep [.x3,.x8,.x9] (Q:=fun a =>a.mem=t.mem ∧
  a.gpr .x9=t.gpr .x9 ||| word t.mem B (e+8*j) ∧ a.gpr .x8=off B (e+8*j+8)) ?_ rfl rfl rfl) ?_
 · brun [inv.pointer,(scratch.congr inv.keep.wr).ld (d:=e+8*j) (by omega)]
 · rintro a ⟨⟨memA,valueA,ptrA⟩,restA⟩
   refine WP.mono (dec_ok a .x12) ?_
   rintro u ⟨⟨count,memU,_⟩,restU⟩
   refine ⟨⟨memU.trans (memA.trans inv.mem),((inv.keep.trans restA).trans restU).mono (by simp),?_,?_⟩,?_⟩
   · rw [restU.gpr .x8 (by decide),ptrA]
     rw [show e+8*j+8=e+8*(j+1) by omega]
   · rw [restU.gpr .x9 (by decide),valueA,BitVec.or_eq_zero_iff,inv.value,inv.mem]
     constructor
     · rintro ⟨low,top⟩ i hi
       rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
       · exact low i hi
       · exact top
     · intro h
       exact ⟨fun i hi =>h i (by omega),h j (by omega)⟩
   · rw [count,restA.gpr .x12 (by decide)]

theorem nonzeroScan_ok {s : State} {B : Addr} {Z e w : Nat}
 (scratch : Scr s B Z) (fit : e+8*w≤Z) (positive : 0<w) (size : w<2^31)
 (pointer : s.gpr .x8=off B e) (zero : s.gpr .x9=0#64) (count : s.gpr .x12=BitVec.ofNat 64 w) :
 WP isa (countLoop .x12 [ld .x3 .x8,.logic .orr .x .x9 .x9 .x3,next .x8]) s fun t =>
 (t.gpr .x9=0#64 ↔ wv s.mem B e w=0) ∧ t.mem=s.mem ∧ Keep [.x3,.x8,.x9,.x12] s t := by
 refine WP.mono (wp_countdown (N:=w) (by omega) (by omega) (NonzeroInv s B e)
  (fun j hj t h _ =>nonzeroScanStep_ok scratch fit hj h) ?_ count) ?_
 · exact ⟨rfl,Keep.refl _ _,by simpa using pointer,by rw [zero];simp⟩
 · intro t h
   refine ⟨?_,h.mem,h.keep⟩
   rw [h.value,wv_eq_zero_iff]
   rfl

end VG.Proof.Ffdh.AArch64.Cached
