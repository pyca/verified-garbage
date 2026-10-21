module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombTbl
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass Spec.Weierstrass
/-- The table's words, in `p384`'s Montgomery radix. -/
theorem p384v_words : P384Joint.p384v.combWords = tcombWords p384.n p384.R p384.C.p P384Joint.p384v.tbl := by
  simp only [Cfg.combWords, P384Joint.p384v, Cfg.R]

namespace FixedGenerator
theorem coordinates (hc : CfgOk p384)
    (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
    {s : State} {T : Addr} (ht : TblMem s T P384Joint.p384v.combWords)
    (a : Nat) (ha : 1≤a) (ha32 : a≤128) :
    wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6=p384.mont (combAt P384Joint.p384v.tbl 0 (2*a-2)).1 ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6=p384.mont (combAt P384Joint.p384v.tbl 0 (2*a-2)).2 := by
  rw [p384v_words] at ht
  have he := tbl_entry (n:=6) (R:=p384.R) (p:=p384.C.p) (H:=256) (J:=1)
    ht hT.len hT.lenH (j:=0) (m:=2*a-2) (by decide) (by omega)
    (Nat.lt_trans (mont_lt hc _) (by decide +kernel)) (Nat.lt_trans (mont_lt hc _) (by decide +kernel))
  simp only [Nat.zero_mul,BitVec.add_zero,Nat.reduceMul] at he
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  rw [show 192*(a-1)=96*(2*a-2) from by omega]
  exact he

theorem of_table (hc : CfgOk p384) (hC : Law p384.C)
    (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
    {s : State} {T base : Addr} (ht : TblMem s T P384Joint.p384v.combWords)
    (hout : ∀ i<P384Joint.p384v.combWords.length,∀ b<8,
      8192≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms "VG_P384_GTAB"=T) :
    FixedGenerator p384.C base 8192 (G p384.C) T s := by
  have hlen : P384Joint.p384v.combWords.length=3072 := by
    rw [p384v_words]; exact tcombWords_length (n:=6) (R:=p384.R) (p:=p384.C.p) hT.len hT.lenH
  refine ⟨hsym,?_,?_,?_,?_⟩
  · intro a ha ha32 i hi
    rw [Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by rw [hlen]; omega)⟩
  · intro a ha ha32 i hi b hb
    rw [Offset.add_add T (192*(a-1)) (8*i)]
    have hd : 192*(a-1)+8*i=8*(24*(a-1)+i) := by omega
    rw [hd]
    exact hout _ (by rw [hlen]; omega) b hb
  · intro a ha ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    exact ⟨mont_lt hc _,mont_lt hc _⟩
  · intro a ha ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    have hx := toM_cmont hc.toBaseCfgOk (combAt P384Joint.p384v.tbl 0 (2*a-2)).1
    have hy := toM_cmont hc.toBaseCfgOk (combAt P384Joint.p384v.tbl 0 (2*a-2)).2
    have radix : (2^(64*p384.n):Nat)=(@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*6)) := by decide +kernel
    rw [radix] at hx hy
    rw [hx,hy]
    have hp := hT.entry 0 (by decide) (2*a-2) (by omega)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one,show 2*a-2+1=2*a-1 from by omega] at hp
    rw [hp]
    exact InvJ.affine hC _ _

theorem of_pre (hc : CfgOk p384) (hC : Law p384.C)
    (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
    {s : State} {T base : Addr} (ht : TblPre P384Joint.p384v s T base)
    (hsym : s.syms "VG_P384_GTAB"=T) :
    FixedGenerator p384.C base 8192 (G p384.C) T s := by
  obtain ⟨hm,ho⟩ := tbl_of ht rfl (Unch.refl _ _ _)
  exact of_table hc hC hT hm ho hsym

end FixedGenerator
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
