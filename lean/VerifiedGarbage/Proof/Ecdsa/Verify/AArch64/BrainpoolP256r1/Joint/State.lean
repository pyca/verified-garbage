module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Sum
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Math
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP256r1.AArch64.Joint
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP256r1.AArch64.Joint
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! Frames and live point representations for the joint verification loop. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (UX UY UZ)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

abbrev C := cfg.C
abbrev coordinates (p : Pt) : List Nat := [p.x,p.y,p.z]
abbrev num (base : Addr) (s : State) (o : Nat) := wordsVal s.mem base o cfg.n
abbrev val (base : Addr) (s : State) (o : Nat) := tmv cfg.C cfg.n base s o

def PointAt (base : Addr) (s : State) (p : Pt) (P : Point C) : Prop :=
  (∀ o ∈ coordinates p,num base s o < C.p) ∧
  Rep C (val base s p.x) (val base s p.y) (val base s p.z) P

abbrev addWork : List (Nat × Nat) := slW cfg sumW
abbrev entryWork : List (Nat × Nat) := (coordinates entry).map (·,32)
abbrev loopWork : List (Nat × Nat) := addWork ++ entryWork
abbrev work : List (Nat × Nat) := loopWork ++ [(cfg.sl EXPP,32),(bitsU,512),(tableAt,1440)]

structure Changes (base : Addr) (W : List (Nat × Nat)) (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x0
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Unch base W s.mem t.mem

theorem Changes.scr {base : Addr} {W : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t) (hs : Scr s base 8192) : Scr t base 8192 :=
  ⟨h.x0.trans hs.x0,h.wr ▸ hs.wr,hs.nowrap,hs.enc⟩

theorem Changes.trans {base : Addr} {W : List (Nat × Nat)} {s t u : State}
    (h : Changes base W s t) (k : Changes base W t u) : Changes base W s u :=
  ⟨k.x0.trans h.x0,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp,(h.mem.trans k.mem).mono (fun _ h => (List.mem_append.mp h).elim id id)⟩

theorem Changes.mono {base : Addr} {W W' : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t) (hs : ∀ w ∈ W,w ∈ W') : Changes base W' s t :=
  ⟨h.x0,h.rd,h.wr,h.sp,h.mem.mono hs⟩

theorem Changes.point {base : Addr} {W : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t) (hs : Scr s base 8192) {p : Pt} {P : Point C}
    (hp : PointAt base s p P) (hle : ∀ x ∈ coordinates p,x+32 ≤ 8192)
    (hsep : ∀ x ∈ coordinates p,∀ w ∈ W,x+32 ≤ w.1 ∨ w.1+w.2 ≤ x) :
    PointAt base t p P := by
  have e (x : Nat) (hx : x ∈ coordinates p) : num base t x = num base s x :=
    h.mem.wordsVal (hsep x hx) (by have := hs.nowrap; have := hle x hx; have hn8 : cfg.n = 4 := rfl; omega)
  refine ⟨fun x hx => (e x hx) ▸ hp.1 x hx,?_⟩
  change Rep C (toM _ _ (num base t p.x)) (toM _ _ (num base t p.y))
    (toM _ _ (num base t p.z)) P
  rw [e _ (by simp),e _ (by simp),e _ (by simp)]
  exact hp.2

materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.addPoints

/-- Complete addition preserves the public loop counter, including through the field calls. -/
theorem sum_counter : ∀ i ∈ instrs (sum cfg),clobbers i .x19 = false := by
  change ∀ i ∈ instrs addPoints,clobbers i .x19 = false
  have h : addPoints.allInstrs (fun i => decide (clobbers i .x19 = false)) = true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

/-- Complete addition in the three live slots, with the same existing field and curve contracts. -/
theorem sum_points {base : Addr} {s : State} (hc : BaseCfgOk cfg) (hC : Law C)
    (hs : Scr s base 8192) (hm : ModOkA cfg.MP' 8192 C.p s.mem base)
    (ha : val base s (cfg.sl AP) = Fin.ofNat C.p C.a)
    (hb : val base s (cfg.sl EXPP) = Fin.ofNat C.p (3*C.b))
    (hal : num base s (cfg.sl AP) < C.p) (hbl : num base s (cfg.sl EXPP) < C.p)
    {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hp : PointAt base s entry P) (hq : PointAt base s resultPt Q) :
    WP isa (sum cfg) s fun t =>
      Changes base addWork s t ∧ PointAt base t resultPt (Spec.Weierstrass.add P Q) ∧
      t.gpr .x19 = s.gpr .x19 := by
  have hi : ∀ i ∈ sumR,sv cfg base s i < C.p := by
    intro i hi
    simp only [sumR,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hal
    · exact hbl
    · exact hp.1 _ (by decide)
    · exact hp.1 _ (by decide)
    · exact hp.1 _ (by decide)
    · exact hq.1 _ (by decide)
    · exact hq.1 _ (by decide)
    · exact hq.1 _ (by decide)
  obtain ⟨trace,t,he,ht,rd,wr,unch,_,bounds,result⟩ := sum_full_ok hc hs hm hi
  refine ⟨trace,t,he,⟨ht.x0.trans hs.x0.symm,rd,wr,VG.AArch64.Exec.sp he,unch⟩,⟨?_,?_⟩,Exec.gpr sum_counter he⟩
  · intro o ho
    simp only [coordinates,resultPt,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact bounds.2.1
    · exact bounds.2.2
    · exact bounds.1
  · change (val base t resultPt.x,val base t resultPt.y,val base t resultPt.z) =
      rcbAdd (val base s (cfg.sl AP)) (val base s (cfg.sl EXPP))
        (val base s entry.x) (val base s entry.y) (val base s entry.z)
        (val base s resultPt.x) (val base s resultPt.y) (val base s resultPt.z) at result
    rw [ha,hb] at result
    exact Rep.add hC hP hQ hp.2 hq.2 result.symm
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
