import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass Spec.Weierstrass

namespace JointGenerator

theorem coordinates (hc : CfgOk p256)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s : State} {T : Addr} (ht : TblMem s T p256.combWords)
    (a : Nat) (ha : 1≤a) (ha32 : a≤32) :
    wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4=p256.mont (combAt p256.tbl 0 (2*a-2)).1 ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4=p256.mont (combAt p256.tbl 0 (2*a-2)).2 := by
  have he := tbl_entry (n:=4) (R:=p256.R) (p:=p256.C.p) (H:=64) (J:=37)
    ht hT.len hT.lenH (j:=0) (m:=2*a-2) (by decide) (by omega)
    (Nat.lt_trans (mont_lt hc _) hc.p_lt) (Nat.lt_trans (mont_lt hc _) hc.p_lt)
  simp only [Nat.zero_mul,BitVec.add_zero,Nat.reduceMul] at he
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  rw [show 128*(a-1)=64*(2*a-2) from by omega]
  exact he

theorem of_table (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s : State} {T base : Addr} (ht : TblMem s T p256.combWords)
    (hout : ∀ i<p256.combWords.length,∀ b<8,
      8192≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms P256Joint.cfg.tsym=T) :
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base 8192 (G p256.C) T s := by
  have hlen : p256.combWords.length=18944 :=
    tcombWords_length (n:=4) (R:=p256.R) (p:=p256.C.p) hT.len hT.lenH
  refine ⟨hsym,?_,?_,?_,?_⟩
  · intro a ha ha32 i hi
    rw [Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by rw [hlen]; omega)⟩
  · intro a ha ha32 i hi b hb
    rw [Offset.add_add T (128*(a-1)) (8*i)]
    have hd : 128*(a-1)+8*i=8*(16*(a-1)+i) := by omega
    rw [hd]
    exact hout _ (by rw [hlen]; omega) b hb
  · intro a ha ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    exact ⟨mont_lt hc _,mont_lt hc _⟩
  · intro a ha ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    have hx := toM_cmont hc.toBaseCfgOk (combAt p256.tbl 0 (2*a-2)).1
    have hy := toM_cmont hc.toBaseCfgOk (combAt p256.tbl 0 (2*a-2)).2
    change toM p256.C.p (2^256) _=_ at hx hy
    rw [hx,hy]
    have hp := hT.entry 0 (by decide) (2*a-2) (by omega)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one,show 2*a-2+1=2*a-1 from by omega] at hp
    rw [hp]
    exact InvJ.affine hC _ _

theorem of_pre (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s : State} {T base : Addr} (ht : TblPre p256 s T base)
    (hsym : s.syms P256Joint.cfg.tsym=T) :
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base 8192 (G p256.C) T s := by
  obtain ⟨hm,ho⟩ := tbl_of ht rfl (Unch.refl _ _ _)
  exact of_table hc hC hT hm ho hsym

end JointGenerator
end VG.Proof.Ecdsa.Verify.AArch64
