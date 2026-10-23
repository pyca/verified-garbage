module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AffineSpec
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectBase
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.X448.AArch64.Iter
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode

/-! Frames shared by every sparse multiplication round. Digits, table entries,
R, and the outer verifier's saved registers are outside these write regions. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Proof.X448.AArch64 (Scr Keeps ofs word)
open VG.Proof.X448.AArch64.Fast (FKeep fclob)

abbrev pointClob : List Reg := .x30::fclob

def JointFrame (base:Addr) (m m':Mem) : Prop :=
  ∀ a,(ofs base a<64 ∨ 2880≤ofs base a) →
    (ofs base a<ACC ∨ ACC+1152≤ofs base a) →
    (ofs base a<GSAVE ∨ GSAVE+64≤ofs base a) → m' a=m a

structure PointKeep (base:Addr) (s t:State) : Prop where
  regs : Keeps pointClob s t
  mem : JointFrame base s.mem t.mem

theorem PointKeep.refl (base:Addr) (s:State) : PointKeep base s s:=
  ⟨Keeps.refl _ _,fun _ _ _ _ => rfl⟩

theorem PointKeep.trans {base:Addr} {s t u:State} (h:PointKeep base s t) (g:PointKeep base t u) :
    PointKeep base s u:=⟨h.regs.trans g.regs,fun x a b c => (g.mem x a b c).trans (h.mem x a b c)⟩

theorem PointKeep.scr {base:Addr} {s t:State} (h:PointKeep base s t) (hs:Scr s base) : Scr t base:=
  hs.of_keeps h.regs (by decide)

theorem PointKeep.of_field {base:Addr} {s t:State} (h:FKeep base s t) : PointKeep base s t:=
  ⟨h.regs.mono (by decide),fun x a b _ => h.mem x a b⟩

theorem PointKeep.of_call {base:Addr} {s t:State} (h:Point56.CKeep base s t) : PointKeep base s t:=
  ⟨h.regs,fun x a b _ => h.mem x a b⟩

theorem PointKeep.of_affine {base:Addr} {s t:State} (h:AffineKeep base s t) : PointKeep base s t:=
  ⟨h.regs.mono (by decide),h.mem⟩

theorem PointKeep.of_keeps {base:Addr} {s t:State} {rs:List Reg} (h:Keeps rs s t)
    (hm:t.mem=s.mem) (hr:∀ r∈rs,r∈pointClob) : PointKeep base s t:=
  ⟨h.mono hr,fun _ _ _ _ => by rw [hm]⟩

theorem JointFrame.word {base:Addr} {m m':Mem} (h:JointFrame base m m') {d:Nat}
    (h1:d+8≤64 ∨ 2880≤d) (h2:d+8≤ACC ∨ ACC+1152≤d)
    (h3:d+8≤GSAVE ∨ GSAVE+64≤d) (hd:d+8≤8192) : word m' base d=word m base d := by
  apply Mem.readW_congr
  intro i hi
  exact h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)

theorem BaseTableAt.of_frame {base p:Addr} {s t:State} (ht:BaseTableAt s base p)
    (hrw:t.rd++t.wr=s.rd++s.wr) (h:JointFrame base s.mem t.mem) : BaseTableAt t base p:=by
  refine ⟨?_,ht.far,fun i hi => ?_⟩
  · rw [hrw]
    exact ht.read
  · rw [←ht.val i hi]
    apply Mem.readW_congr
    intro j hj
    have he:p+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j=p+BitVec.ofNat 64 (8*i+j):=
      VG.Offset.add_add _ _ _
    rw [he]
    have hf:=ht.far (8*i+j) (by omega)
    exact h _ (Or.inr (by omega)) (Or.inr (by simp only [ACC];omega))
      (Or.inr (by simp only [GSAVE];omega))

theorem JointFrame.keyDigit {base:Addr} {m m':Mem} (h:JointFrame base m m') {i:Nat} (hi:i<464) :
    m' (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i))=
      m (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i)):=by
  apply h
  all_goals rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [VG.Impl.X448.AArch64.BITS];omega)]
  all_goals simp only [VG.Impl.X448.AArch64.BITS,ACC,GSAVE];omega

theorem JointFrame.baseDigit {base:Addr} {m m':Mem} (h:JointFrame base m m') {i:Nat} (hi:i<464) :
    m' (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i))=
      m (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i)):=by
  apply h
  all_goals rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [VG.Impl.Ed448.AArch64.Sparse.SDIG];omega)]
  all_goals simp only [VG.Impl.Ed448.AArch64.Sparse.SDIG,ACC,GSAVE];omega

theorem PointKeep.keyDigit {base:Addr} {s t:State} (h:PointKeep base s t) {i:Nat} (hi:i<464) :
    t.mem (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i))=
      s.mem (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i)):=h.mem.keyDigit hi

theorem PointKeep.baseDigit {base:Addr} {s t:State} (h:PointKeep base s t) {i:Nat} (hi:i<464) :
    t.mem (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i))=
      s.mem (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i)):=h.mem.baseDigit hi

theorem PointKeep.baseTable {base p:Addr} {s t:State} (h:PointKeep base s t)
    (ht:BaseTableAt s base p) : BaseTableAt t base p:=
  ht.of_frame (by rw [h.regs.2.1,h.regs.2.2]) h.mem

theorem BaseTableAt.of_far {base p:Addr} {s t:State} (ht:BaseTableAt s base p)
    (hrw:t.rd++t.wr=s.rd++s.wr)
    (hm:∀ a,8192≤ofs base a → t.mem a=s.mem a) : BaseTableAt t base p:=by
  refine ⟨hrw ▸ ht.read,ht.far,fun i hi => ?_⟩
  rw [←ht.val i hi]
  apply Mem.readW_congr
  intro j hj
  have he:p+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j=p+BitVec.ofNat 64 (8*i+j):=Offset.add_add _ _ _
  rw [he]
  exact hm _ (ht.far _ (by omega))

end VG.Proof.Ed448.AArch64.Sparse
