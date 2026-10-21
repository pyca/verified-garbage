module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvSetWord
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Mont.Words

/-! # Coefficient and Montgomery-inverse initialization -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem coefficients_ok {s : State} {base : Addr} {size w n : Nat}
    (hs : Scr s base size) (_hn : 16≤n) (hw : w=2*n) (hz : offset w 15≤size) :
    WP isa (.block (coefficients w n)) s fun z =>
      val32 z.mem base (offset w 6) (n+1)=0 ∧ val32 z.mem base (offset w 7) (n+1)=1 ∧
      Keeps [.eax] s z ∧ Outside base (offset w 6) (2*(4*w+8)) s.mem z.mem := by
  have nw := hs.nowrap
  unfold coefficients
  refine WP.block_append (WP.block_append (WP.mono
    (zeros_ok hs (acc:=offset w 6) (k:=n+1) (by apart)) fun s1 ⟨O1,V1,K1⟩ => ?_))
  refine WP.mono (zeros_ok (hs.of_keeps K1 (by decide)) (acc:=offset w 7) (k:=n+1) (by apart)) fun s2 ⟨O2,V2,K2⟩ => ?_
  refine WP.mono (setWord_ok (dst:=offset w 7) 1 ((hs.of_keeps K1 (by decide)).of_keeps K2 (by decide)) (by apart)) fun z ⟨V3,K3,O3⟩ => ?_
  refine ⟨?_,?_,(K1.trans K2).trans K3,?_⟩
  · rw [O3.val32 (by apart) (by apart),O2.val32 (by apart) (by apart),V1]
  · have tail : val32 s2.mem base (offset w 7+4) n=0 := by rw [val32] at V2; omega
    rw [val32,V3,O3.val32 (by apart) (by apart),tail]; rfl
  · intro x hx
    rw [O3 x (by apart),O2 x (by apart),O1 x (by apart)]

 theorem inverseSetup_ok {s : State} {base : Addr} {size w n p : Nat}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (hz : offset w 15≤size)
    (hm : val32 s.mem base (offset w 2) n=p) (odd : p%2=1) :
    WP isa (.block (inverseSetup w)) s fun z =>
      (p*w32 z.mem base (offset w 3+28)+1)%2^32=0 ∧
      Keeps [.eax,.ebx,.ecx,.edx,.ebp] s z ∧ Outside base (offset w 3+28) 4 s.mem z.mem := by
  have nw := hs.nowrap
  have low : p%2^32=w32 s.mem base (offset w 2) := by
    have e : n=(n-1)+1 := by omega
    have v := congrArg (fun k => k%2^32) hm
    rw [e,val32] at v
    have bound : w32 s.mem base (offset w 2)<2^32 := (s.mem.readW _ 32).isLt
    omega
  unfold inverseSetup
  refine WP.block_append (WP.block_append ?_)
  refine wp_movS (readSrc_sc hs (by apart)) fun s1 U1 _ => WP.block_nil ?_
  have odd1 : (s1.gpr .ebx).toNat%2=1 := by
    rw [U1.gpr]
    change w32 s.mem base (offset w 2)%2=1
    rw [←low,Nat.mod_mod_of_dvd _ (by decide),odd]
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.inverse_ok s1 odd1) fun s2 ⟨iv,K2,M2⟩ => ?_
  have k2 : Keeps [.eax,.ebx,.ecx,.edx,.ebp] s s2 := (U1.keeps.mono (by decide)).trans (K2.mono (by decide))
  have hs2 := hs.of_keeps k2 (by decide)
  refine wp_storeS (hs2.ea (by apart)) (hs2.write (by apart)) fun z Z => WP.block_nil ?_
  refine ⟨?_,k2.trans (Z.keeps _),?_⟩
  · rw [Z.mem,w32_write_self]
    rw [U1.gpr] at iv
    have product : p*(s2.gpr .eax).toNat%2^32=w32 s.mem base (offset w 2)*(s2.gpr .eax).toNat%2^32 := by
      calc
        _ = (p%2^32)*((s2.gpr .eax).toNat%2^32)%2^32 := Nat.mul_mod _ _ _
        _ = _ := by rw [low,Nat.mod_eq_of_lt (s2.gpr .eax).isLt]
    rw [Nat.add_mod,product,←Nat.add_mod]
    exact iv
  · rw [Z.mem,M2,U1.mem]
    exact writeW32_outside _ _ _ (by apart)

end VG.Proof.Rsa.X86.InvBatch
