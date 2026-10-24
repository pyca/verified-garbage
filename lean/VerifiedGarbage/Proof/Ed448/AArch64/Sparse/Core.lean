module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Frame
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Table
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs

/-! Bounded point arithmetic invariants and immutable sparse tables. -/

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
