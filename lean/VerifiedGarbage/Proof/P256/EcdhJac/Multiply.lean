import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
import VerifiedGarbage.Proof.P256.EcdhJac.Extra

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.AArch64 Spec.Weierstrass

/-- The multiplication has restored its temporary ABI saves. The existing
fixed-count inversion can now finish the internal multiplication contract. -/
structure MulReady (base : Addr) (g : Reg → BitVec 64) (P : Point C) (k : Nat)
    (s t : State) : Prop where
  scr : Scr t base 8192
  fixed : VG.Proof.Ecdsa.AArch64.Fixed p256 base g t.mem
  extra : ∀ r∈[Reg.x26,.x27,.x28],t.gpr r=s.gpr r
  x20 : t.gpr .x20=s.gpr .x20
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  flag : word t.mem base (p256.sl FLAG)=word s.mem base (p256.sl FLAG)
  d : sv p256 base t D=sv p256 base s D
  q : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)
  rz_lt : sv p256 base t RZ<C.p

theorem finishPow_ok (hc : CfgOk p256) {base : Addr} {g : Reg → BitVec 64}
    {P : Point C} {k : Nat} {s t : State} (hw : MulReady base g P k s t)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ u,MulPost p256 base g P k s u → WP isa rest u R) :
    WP isa (.seq p256.pPow rest) t R := by
  refine WP.seq (WP.mono (pPow_ok hc hw.scr (modP_of hc hw.fixed.mp) hw.rz_lt)
    fun u ⟨ku,hu,lu,vu⟩=>h u ?_)
  have keep : ∀ {i},i<45 → i∉[ACC,TMP] → sv p256 base u i=sv p256 base t i :=
    fun hi hn=>sv_unch hu hc.n10 hw.scr.nowrap hi (apart_chainWc hi hn)
  refine ⟨hw.scr.of_keepRegs ku (x0_not_powClob hc.n10),
    hw.fixed.unch hc.n10 hw.scr.nowrap fixedOk_chainWc hu,?_,?_,
    ku.rd.trans hw.rd,ku.wr.trans hw.wr,?_,?_,?_,lu,?_,?_⟩
  · intro r hr
    rw [ku.gpr r (by
      have hh : ∀ r∈[Reg.x26,.x27,.x28],r∉powClob 4 := by decide
      exact hh r hr),hw.extra r hr]
  · rw [ku.gpr .x20 (x20_not_powClob hc.n10),hw.x20]
  · exact (hu.word (by decide) (by decide)).trans hw.flag
  · exact (keep (by decide) (by decide)).trans hw.d
  · intro hk hn
    change Rep C (toM _ _ (sv p256 base u RX)) (toM _ _ (sv p256 base u RY))
      (toM _ _ (sv p256 base u RZ)) _
    rw [keep (i:=RX) (by decide) (by decide),keep (i:=RY) (by decide) (by decide),
      keep (i:=RZ) (by decide) (by decide)]
    exact hw.q hk hn
  · change _=toM _ _ (sv p256 base u RZ) ^ _
    rw [keep (i:=RZ) (by decide) (by decide)]
    exact vu
  · rw [keep (i:=RZ) (by decide) (by decide)]
    exact hw.rz_lt

end VG.Proof.P256.EcdhJac
