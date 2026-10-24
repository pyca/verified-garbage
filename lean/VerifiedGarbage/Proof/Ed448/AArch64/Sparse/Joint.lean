module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointDigits
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.BufferFrame
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.RecodePair
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits
import VerifiedGarbage.Proof.X448.AArch64.Base.Digit
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Iter
public import VerifiedGarbage.Proof.Ed448.WnafWide.Bits

/-! Recode both complete public scalars and run the shared sparse multiplier. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.AArch64 (KB bitsAt)
open VG.Impl.Ed448.WnafWide (digitAt scalarLimit)
open VG.Impl.X448.AArch64 (BITS ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.EdwardsLaw (EPoint)
open VG.Proof.X448.AArch64.Base (pt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- All mutable regions used by recoding and joint point arithmetic. -/
def FullJointFrame (base:Addr) (m m':Mem) : Prop :=
  ∀ x,(ofs base x<64 ∨ 2880≤ofs base x) →
    (ofs base x<ACC ∨ ACC+1152≤ofs base x) →
    (ofs base x<GSAVE ∨ GSAVE+64≤ofs base x) →
    (ofs base x<BITS ∨ BITS+464≤ofs base x) →
    (ofs base x<SDIG ∨ SDIG+464≤ofs base x) → m' x=m x

theorem FullJointFrame.word {base:Addr} {m m':Mem} (h:FullJointFrame base m m') {d:Nat}
    (h1:d+8≤64 ∨ 2880≤d) (h2:d+8≤ACC ∨ ACC+1152≤d)
    (h3:d+8≤GSAVE ∨ GSAVE+64≤d) (h4:d+8≤BITS ∨ BITS+464≤d)
    (h5:d+8≤SDIG ∨ SDIG+464≤d) (hd:d+8≤8192) :
    VG.Proof.X448.AArch64.word m' base d=VG.Proof.X448.AArch64.word m base d:=by
  apply Mem.readW_congr
  intro i hi
  exact h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)

structure FullJointOut (s:State) (base:Addr) (P:Spec.Ed448.Point) (S K:Nat) (t:State) : Prop where
  core : Core base t
  rep : ∀ a:EPoint dZ,Rep P a → Rep (pt (EV t.mem base) 3 4 5) ((S:Int) • baseAff+(K:Int) • a)
  chk : t.gpr .x20=s.gpr .x20
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  mem : FullJointFrame base s.mem t.mem

theorem joint_ok (hA:AffineOk) {s:State} {base:Addr} {P:Spec.Ed448.Point} {S K:Nat}
    (hs:Scr s base) (hb:BEnv s.mem base) (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb)
    (hbt:BaseTableAt s base (s.syms baseSym)) (hS:S<scalarLimit) (hK:K<scalarLimit)
    (hsd:∀ i<456,s.mem (off base (BITS+i))=BitVec.ofNat 8 (WnafWide.bit S i))
    (hkv:Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (off base KB) 57)=K) :
    WP isa joint s (FullJointOut s base P S K):=by
  unfold joint
  refine WP.seq (WP.mono (recodePair_ok hs hb ht hxb hbt hS hK hsd hkv) fun d hd => ?_)
  refine WP.mono (jointDigits_ok hA hd.scr hd.bnd hd.tab hd.xb hd.bt hS hK hd.sd hd.kd) fun t jt => ?_
  refine ⟨jt.core,jt.rep,jt.chk.trans hd.chk,jt.rd.trans hd.rd,jt.wr.trans hd.wr,?_⟩
  intro x hx hy hz hbits hsig
  rw [jt.mem x hx hy hz,hd.mem x hbits hsig]

end VG.Proof.Ed448.AArch64.Sparse
