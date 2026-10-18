module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSource
public import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass Spec.Weierstrass
namespace FixedGenerator
theorem coordinates (hc : CfgOk p521)
    (hT : CombOkW p521.C 7 83 p521.tbl p521.start)
    {s : State} {T : Addr} (ht : TblMem s T p521.combWords)
    (a : Nat) (ha : 1≤a) (ha32 : a≤32) :
    wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 0 9=p521.mont (combAt p521.tbl 0 (2*a-2)).1 ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (288*(a-1))) 72 9=p521.mont (combAt p521.tbl 0 (2*a-2)).2 := by
  have he := tbl_entry (n:=9) (R:=p521.R) (p:=p521.C.p) (H:=64) (J:=83)
    ht hT.len hT.lenH (j:=0) (m:=2*a-2) (by decide) (by omega)
    (Nat.lt_trans (mont_lt hc _) (by decide +kernel)) (Nat.lt_trans (mont_lt hc _) (by decide +kernel))
  simp only [Nat.zero_mul,BitVec.add_zero,Nat.reduceMul] at he
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  rw [show 288*(a-1)=144*(2*a-2) from by omega]
  exact he

theorem of_table (hc : CfgOk p521) (hC : Law p521.C)
    (hT : CombOkW p521.C 7 83 p521.tbl p521.start)
    {s : State} {T base : Addr} (ht : TblMem s T p521.combWords)
    (hout : ∀ i<p521.combWords.length,∀ b<8,
      8192≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms "VG_P521_COMB"=T) :
    FixedGenerator p521.C base 8192 (G p521.C) T s := by
  have hlen : p521.combWords.length=95616 :=
    tcombWords_length (n:=9) (R:=p521.R) (p:=p521.C.p) hT.len hT.lenH
  refine ⟨hsym,?_,?_,?_,?_⟩
  · intro a ha ha32 i hi
    rw [Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by rw [hlen]; omega)⟩
  · intro a ha ha32 i hi b hb
    rw [Offset.add_add T (288*(a-1)) (8*i)]
    have hd : 288*(a-1)+8*i=8*(36*(a-1)+i) := by omega
    rw [hd]
    exact hout _ (by rw [hlen]; omega) b hb
  · intro a ha ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    exact ⟨mont_lt hc _,mont_lt hc _⟩
  · intro a ha ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    have hx := toM_cmont hc.toBaseCfgOk (combAt p521.tbl 0 (2*a-2)).1
    have hy := toM_cmont hc.toBaseCfgOk (combAt p521.tbl 0 (2*a-2)).2
    have radix : (2^(64*p521.n):Nat)=(@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*9)) := by decide +kernel
    rw [radix] at hx hy
    rw [hx,hy]
    have hp := hT.entry 0 (by decide) (2*a-2) (by omega)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one,show 2*a-2+1=2*a-1 from by omega] at hp
    rw [hp]
    exact InvJ.affine hC _ _

theorem of_pre (hc : CfgOk p521) (hC : Law p521.C)
    (hT : CombOkW p521.C 7 83 p521.tbl p521.start)
    {s : State} {T base : Addr} (ht : TblPre p521 s T base)
    (hsym : s.syms "VG_P521_COMB"=T) :
    FixedGenerator p521.C base 8192 (G p521.C) T s := by
  obtain ⟨hm,ho⟩ := tbl_of ht rfl (Unch.refl _ _ _)
  exact of_table hc hC hT hm ho hsym

end FixedGenerator
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
