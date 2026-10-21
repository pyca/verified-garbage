module
import VerifiedGarbage.Proof.Rsa.Divstep.InvCorrect

import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Correction
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Ring.Abs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Defs
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Count
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Init

/-! # Complete functional correctness of the active-width RSA inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch VG.Impl.Weierstrass.X86
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem body_ok_proof {s : State} {base : Addr} {size w n m x : Nat}
    (hs : Scr s base size) (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (hm : val32 s.mem base (offset w 8) n=m) (hx : val32 s.mem base (offset w 0) n=x) (odd : m%2=1) :
    WP isa (body w n) s fun z =>
      val32 z.mem base (offset w 1) w=Nat.gcd (virtualMod m) x ∧
      (virtualMod m : Int)∣(val32 z.mem base (offset w 3) w : Int)*x-(Nat.gcd (virtualMod m) x : Int) ∧
      val32 z.mem base (offset w 3) w<virtualMod m ∧
      Keeps wordClob s z ∧ Unch base (initWrites w) s.mem z.mem := by
  have nw := hs.nowrap
  let p := virtualMod m
  have po : p%2=1 := virtualMod_odd odd
  have pl : 1<p := by dsimp only [p,virtualMod]; split_ifs <;> omega
  have mp : m<2^(32*n) := hm ▸ val32_lt _ _ _ _
  have pc : p<2^(32*n) := by
    have four : 4≤2^(32*n) := Nat.pow_le_pow_right (n:=2) (by decide) (show 2≤32*n by omega)
    dsimp only [p,virtualMod]; split_ifs <;> omega
  have xc : x<2^(32*n) := hx ▸ val32_lt _ _ _ _
  unfold body
  simp only [seqs,VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (init_ok hs hn nl hw hz hm hx odd) fun s1 ⟨iv,I1,inv,C1,K1,O1⟩ => ?_)
  have hs1 := hs.of_keeps K1 (by decide)
  have il : iv<2^32 := by rw [←I1.inverse]; exact (s1.mem.readW _ 32).isLt
  change WP isa (.seq (.loop (batchCode w n) .ne) (correctionCode w n)) s1 _
  refine WP.seq (WP.mono (loop_ok hs1 hn nl hw he hz I1 C1 il po pl inv pc xc) fun s2 ⟨I2,C2,K2,O2⟩ => ?_)
  have hs2 := hs1.of_keeps K2 (by decide)
  let st := VG.Proof.Divstep.W32.invRun 30 p iv (VG.Proof.Rsa.Divstep.oddInput p x) (3*(n+1))
  have result := VG.Proof.Rsa.Divstep.invRun_result (iv:=iv) po pl inv pc xc
  change st.f.natAbs=Nat.gcd p x ∧ (p : Int)∣(VG.Proof.Rsa.Divstep.corrected p st (3*(n+1))).toNat*(x : Int)-(Nat.gcd p x : Int) ∧
    (VG.Proof.Rsa.Divstep.corrected p st (3*(n+1))).toNat<p at result
  have bounds := VG.Proof.Rsa.Divstep.invRun_bounds (inv:=iv) (cap:=p+x) po pl inv (by omega)
    (show VG.Proof.Rsa.Divstep.oddInput p x≤p+x by unfold VG.Proof.Rsa.Divstep.oddInput; split_ifs <;> omega) (3*(n+1))
  have fg : |st.f|<(2:Int)^(32*n) := by
    have gBound : Nat.gcd p x<2^(32*n) := (Nat.gcd_le_left x (by omega : 0<p)).trans_lt pc
    have : st.f.natAbs<2^(32*n) := result.1 ▸ gBound
    have cast : (st.f.natAbs : Int)<(2:Int)^(32*n) := by exact_mod_cast this
    simpa only [Int.natCast_natAbs] using cast
  refine WP.mono (correction_ok hs2 hn nl hw he hz I2 (by omega) bounds.2.2.2.2.1 bounds.2.2.2.2.2.1 fg)
    fun z ⟨G3,A3,K3,O3⟩ => ?_
  refine ⟨G3.trans result.1,?_,A3 ▸ result.2.2,(K1.trans K2).trans K3,?_⟩
  · rw [A3]; exact result.2.1
  · intro y hy
    have h0 := hy (offset w 0,8*(4*w+8)) (by simp [initWrites])
    have h11 := hy (offset w 11,4*(4*w+8)) (by simp [initWrites])
    have h100 := hy (100,4) (by simp [initWrites])
    rw [O3 y hy,O2 y (by
      intro r hr
      simp only [countedWrites,batchWrites,updateWrites,rowWrites,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> apart),O1 y hy]

end VG.Proof.Rsa.X86.InvBatch
