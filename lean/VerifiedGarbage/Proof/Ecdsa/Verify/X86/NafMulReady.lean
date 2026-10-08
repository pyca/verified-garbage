import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafSetupTiming

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 Spec.Weierstrass

structure NafMulInput (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (x y : Fe c.C) (s : State) : Prop where
  scr : Scr s base size
  fixed : ∃ g,Fixed c base g s.mem
  px_lt : sv c base s PX<c.C.p
  py_lt : sv c base s PY<c.C.p
  point : Rep c.C (tmv c.C c.n base s (c.sl PX))
    (tmv c.C c.n base s (c.sl PY)) (tmv c.C c.n base s (c.sl ONEP)) P
  px : tmv c.C c.n base s (c.sl PX)=x
  py : tmv c.C c.n base s (c.sl PY)=y
  scalar : sv c base s V=k

structure NafMulReady (base : Addr) (P : Point p256Comb.C) (k : Nat) (x y : Fe p256Comb.C) (s : State) : Prop where
  fixed : ∃ g,Fixed p256Comb base g s.mem
  field : Inv nafK.M base size p256Comb.C.p (·∈nafSlots nafK) (winRo nafK) (tmv p256Comb.C p256Comb.n base s) s
  input : NafInput nafK p256Comb.C base P k s
  px : tmv p256Comb.C p256Comb.n base s (p256Comb.sl PX)=x
  py : tmv p256Comb.C p256Comb.n base s (p256Comb.sl PY)=y
  b : sv p256Comb base s EM=p256Comb.mont p256Comb.C.b
  count : s.gpr .esi=257

theorem nafMulReady_ok (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    {base : Addr} {P : Point p256Comb.C} {k : Nat} {x y : Fe p256Comb.C} {s : State}
    (h : NafMulInput p256Comb base P k x y s) :
    WP isa (.seq nafSetB (Naf.prep 3580 (p256Comb.sl V) 3520)) s fun t =>
      Keeps powClob s t ∧ NafMulReady base P k x y t := by
  obtain ⟨g,hg⟩ := h.fixed
  refine WP.mono (windowMulQ_setup_ok hc rfl hC h.scr hg h.px_lt h.py_lt h.point)
    fun t ⟨kt,_,ft,it,pt,px,py,bt,ct⟩ => ?_
  rw [h.scalar] at pt
  refine ⟨kt,⟨g,ft⟩,it,pt,?_,?_,bt,ct⟩
  · change toM _ _ (sv p256Comb base t PX)=x
    rw [px]; exact h.px
  · change toM _ _ (sv p256Comb base t PY)=y
    rw [py]; exact h.py

theorem nafMulReady_pair {base : Addr} {P : Point p256Comb.C} {k : Nat} {x y : Fe p256Comb.C}
    {s t : State} (hs : NafMulReady base P k x y s) (ht : NafMulReady base P k x y t)
    (hp : NafPublic s t) :
    FieldPair nafK.M base size p256Comb.C.p (·∈nafSlots nafK) (winRo nafK)
      (tmv p256Comb.C p256Comb.n base s) 257 s t := by
  obtain ⟨_,fs⟩ := hs.fixed
  obtain ⟨_,ft⟩ := ht.fixed
  refine ⟨hs.field,⟨ht.field.scr,ht.field.mod,ht.field.sl,ht.field.lt,?_⟩,hp,hs.count,ht.count⟩
  intro a ha
  change a∈[p256Comb.sl AP,p256Comb.sl EM,p256Comb.sl ZERO,p256Comb.sl PX,p256Comb.sl PY,p256Comb.sl ONEP] at ha
  change tmv p256Comb.C p256Comb.n base t a=tmv p256Comb.C p256Comb.n base s a
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
  · change toM _ _ (sv p256Comb base t AP)=toM _ _ (sv p256Comb base s AP)
    exact congrArg (fun z => toM p256Comb.C.p (2^(64*p256Comb.n)) z) (ft.ap.trans fs.ap.symm)
  · change toM _ _ (sv p256Comb base t EM)=toM _ _ (sv p256Comb base s EM)
    rw [ht.b,hs.b]
  · change toM _ _ (sv p256Comb base t ZERO)=toM _ _ (sv p256Comb base s ZERO)
    exact congrArg (fun z => toM p256Comb.C.p (2^(64*p256Comb.n)) z) (ft.zero.trans fs.zero.symm)
  · exact ht.px.trans hs.px.symm
  · exact ht.py.trans hs.py.symm
  · change toM _ _ (sv p256Comb base t ONEP)=toM _ _ (sv p256Comb base s ONEP)
    exact congrArg (fun z => toM p256Comb.C.p (2^(64*p256Comb.n)) z) (ft.onep.trans fs.onep.symm)

end VG.Proof.Ecdsa.Verify.X86
