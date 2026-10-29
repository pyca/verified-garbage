module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AffineSpec
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectBase
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode

import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.X448.AArch64.Iter
/-! Bounded point arithmetic invariants and immutable sparse tables. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Frame.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Proof.X448.AArch64 (Scr limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure Core (base:Addr) (s:State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w<8,limbs s.mem base (slot (19:Index).val) w=0
  one : EV s.mem base 20=1
  zbound : Bnd Mb s.mem base (slot 5)

theorem Core.after {base:Addr} {s t:State} (h:Core base s) (k:PointKeep base s t)
    (hb:BEnv t.mem base) {os:List Index} (sm:Same base os s.mem t.mem)
    (h19:(19:Index)∉os) (h20:(20:Index)∉os) (hz:Bnd Mb t.mem base (slot 5)) : Core base t:=by
  refine ⟨k.scr h.scr,hb,fun w hw => ?_,?_,hz⟩
  · rw [sm 19 h19 w hw]
    exact h.zero w hw
  · rw [Same.env sm h20]
    exact h.one

theorem Core.unchanged {base:Addr} {s t:State} (h:Core base s) (k:PointKeep base s t)
    (hb:BEnv t.mem base) {os:List Index} (sm:Same base os s.mem t.mem)
    (h19:(19:Index)∉os) (h20:(20:Index)∉os) (h5:(5:Index)∉os) : Core base t:=
  h.after k hb sm h19 h20 (fun j hj => by
    change limbs t.mem base (slot (5:Index).val) j<Mb
    rw [sm 5 h5 j hj]
    exact h.zbound j hj)

theorem Core.of_keeps {base:Addr} {s t:State} (h:Core base s) (k:PointKeep base s t)
    (hm:t.mem=s.mem) : Core base t:=by
  refine ⟨k.scr h.scr,?_,?_,?_,?_⟩ <;> rw [hm]
  exacts [h.env,h.zero,h.one,h.zbound]

theorem Core.regsOnly {base:Addr} {s t:State} {rs:List Reg} (h:Core base s)
    (k:VG.Proof.X448.AArch64.Keeps rs s t) (hm:t.mem=s.mem) (hr:.x3∉rs ∧ .x12∉rs) : Core base t:=by
  refine ⟨h.scr.of_keeps k hr,?_,?_,?_,?_⟩ <;> rw [hm]
  exacts [h.env,h.zero,h.one,h.zbound]

theorem JointFrame.oddTable {base:Addr} {m m':Mem} {P:Spec.Ed448.Point}
    (k:JointFrame base m m') (ht:OddTabOk m base P 8) : OddTabOk m' base P 8:=by
  have hm:∀ e<8,∀ w<24,Window.tw m' base e w=Window.tw m base e w:=fun e he w hw =>
    k.word (Or.inr (by simp only [TAB];omega)) (Or.inr (by simp only [ACC,TAB];omega))
      (Or.inl (by simp only [TAB,GSAVE];omega)) (by simp only [TAB];omega)
  intro e he
  refine ⟨?_,fun w hw => ?_⟩
  · rw [Window.TPt_of_tw (hm e he)]
    exact (ht e he).1
  · rw [hm e he w hw]
    exact (ht e he).2 w hw

theorem JointFrame.xbounds {base:Addr} {m m':Mem} (k:JointFrame base m m')
    (hxb:∀ e<8,∀ w<8,(Window.tw m base e w).toNat<Mb) :
    ∀ e<8,∀ w<8,(Window.tw m' base e w).toNat<Mb:=by
  intro e he w hw
  rw [Window.tw,k.word (Or.inr (by simp only [TAB];omega)) (Or.inr (by simp only [ACC,TAB];omega))
    (Or.inl (by simp only [TAB,GSAVE];omega)) (by simp only [TAB];omega)]
  exact hxb e he w hw

theorem acc_of_same {base:Addr} {m m':Mem} {os:List Index} (h:Same base os m m')
    (h3:(3:Index)∉os) (h4:(4:Index)∉os) (h5:(5:Index)∉os) :
    VG.Proof.X448.AArch64.Base.pt (EV m' base) 3 4 5=
      VG.Proof.X448.AArch64.Base.pt (EV m base) 3 4 5:=by
  simp only [VG.Proof.X448.AArch64.Base.pt]
  rw [Same.env h h3,Same.env h h4,Same.env h h5]

theorem PointKeep.oddTable {base:Addr} {s t:State} {P:Spec.Ed448.Point}
    (k:PointKeep base s t) (ht:OddTabOk s.mem base P 8) : OddTabOk t.mem base P 8:=k.mem.oddTable ht

theorem PointKeep.xbounds {base:Addr} {s t:State} (k:PointKeep base s t)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb) :
    ∀ e<8,∀ w<8,(Window.tw t.mem base e w).toNat<Mb:=k.mem.xbounds hxb

end VG.Proof.Ed448.AArch64.Sparse
