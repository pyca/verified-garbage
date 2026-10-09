import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (zHat w1Row)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlDsa.AArch64.Call (Ptr)

/-- Canonical before the forward transform; positive-lazy after it. -/
def Stored (done : Bool) (m : Mem) (a : Addr) (f : Poly) : Prop :=
  if done then PosPolyIs m a f else PolyIs m a f

theorem stored_keep {S : Nat} {rbs wbs : List (Reg×Nat)} {s t : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr×Nat)} {p : Ptr} {f : Poly} {done : Bool}
    (hp : PPostB S s t ws) (hc : keepB rbs wbs ws p 1024=true)
    (h : Stored done s.mem (pa s p) f) : Stored done t.mem (pa t p) f := by
  cases done
  · exact L.keepPoly hp hc h
  · exact Sign.keepPosPoly L hp hc h

/-- The original verification semantics, with representation-specific bounds
and immutable root-table contents tracked independently. -/
structure SC (p : Params) (S : Nat) (σ : State) (h : List (Vector Bool n))
    (A' : Nat→Nat→Poly) (c0 : Poly) (q : Bool) (j : Nat) (cn : Bool) (r : Nat) (s : State) : Prop where
  vc : VC p σ s
  roots : Sign.StaticRoots S s
  hh : hintOf p σ=some h
  hint : HintIs s.mem (pa s (hP p 0)) p.k h
  nok : normOk p σ p.ℓ
  gd : Gd p σ A' c0 q
  a : ∀r'<p.k,∀c<p.ℓ,PolyIs s.mem (pa s (aP (p.ℓ*r'+c))) (A' r' c)
  z : ∀i<p.ℓ,Stored (decide (i<j)) s.mem (pa s (zP p i))
    (if i<j then zHat p (vSig p σ) i else toRq (zOf p σ i))
  c : Stored cn s.mem (pa s (cP p)) (if cn then ntt c0 else c0)
  rows : ∀r'<r,bytesAt s.mem (pa s (rowP p r')) (w1Len p)=
    simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' (ntt c0) h r') (w1Max p)
  x24 : s.gpr .x24=flag (q=true)

theorem SC.keep {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {j r : Nat} {cn : Bool}
    {s t : State} (hs : SC p S σ h A' c0 q j cn r s) {ws : List (Ptr×Nat)}
    (hP : PPostB S s t ws) (hc : SCChk p r ws) (hy : t.syms=s.syms)
    (hw : ∀w∈ws,inB (vW p) w.1 w.2=true) (h24 : t.gpr .x24=s.gpr .x24) :
    SC p S σ h A' c0 q j cn r t := by
  have L := hs.vc.lay hF hp
  exact ⟨hs.vc.step hF hp hP hc.vc,hs.roots.step_layout L hP hy hw,hs.hh,
    L.keepHint hP hc.hint hs.hint,hs.nok,hs.gd,
    fun r' hr' c hcc=>L.keepPoly hP (hc.a r' hr' c hcc) (hs.a r' hr' c hcc),
    fun i hi=>stored_keep L hP (hc.z i hi) (hs.z i hi),stored_keep L hP hc.c hs.c,
    fun r' hr'=>by rw [L.keepBytes hP (hc.rows r' hr')];exact hs.rows r' hr',
    by rw [h24];exact hs.x24⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
