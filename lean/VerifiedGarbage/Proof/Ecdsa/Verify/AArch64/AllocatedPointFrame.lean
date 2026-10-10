import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedField
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointPairedTiming

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- The full point-loop work includes lookup negation and cached entry fields. -/
def work : List (Nat × Nat) := [(128,32),(512,544),(5400,64),(7104,576)]

theorem work_bounds : ∀ w∈work,w.1+w.2≤8192 := by decide

theorem work_stable : ∀ r∈jointStableRanges cfg,∀ w∈work,
    r.1+r.2≤w.1 ∨ w.1+w.2≤r.1 := by decide +kernel

theorem work_cover : ∀ w∈(jointWork cfg).map (·,8*K.M.n)++[(K.M.tmp,8*K.M.n)],
    ∃ r∈work,r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem liftArithmetic {base : Addr} {s t : State}
    (h : Frame base Proof.P256.VerifyAllocated.work s t) : Frame base work s t :=
  h.mono (fun _ hr => hr) (by decide)

theorem liftProg {base : Addr} {W : List Nat} {s t : State}
    (h : ProgKeep K.M base W s t) (hw : ∀ x∈W,x∈jointWork cfg) : Frame base work s t :=
  AllocatedFrame.of_prog (h.mono hw) clob4_allocatedRegs work_cover

/-- Point results expose only their initialized field slots and wide frame. -/
def PointPost (base : Addr) (V : List Nat) (o : Pt) (P : Point C) (s t : State) : Prop :=
  ∃ E,Frame base work s t ∧ Inv K.M base 8192 C.p Sl ([o.x,o.y,o.z]++V) E t ∧
    InvJ C (E o.x) (E o.y) (E o.z) P

theorem PointPost.prefix {base : Addr} {V : List Nat} {o : Pt} {P : Point C} {s a t : State}
    (h : PointPost base V o P a t) (hk : Frame base work s a) : PointPost base V o P s t := by
  obtain ⟨E,kt,hi,hp⟩ := h
  exact ⟨E,hk.trans kt,hi,hp⟩

theorem PointPost.sub {base : Addr} {V V' : List Nat} {o : Pt} {P : Point C} {s t : State}
    (h : PointPost base V o P s t) (hv : ∀ x∈V',x∈V) : PointPost base V' o P s t := by
  obtain ⟨E,hk,hi,hp⟩ := h
  exact ⟨E,hk,hi.sub (fun x hx => (List.mem_append.mp hx).elim
    (List.mem_append_left _) (fun hx => List.mem_append_right _ (hv x hx))),hp⟩

theorem PointPost.of_jac {base : Addr} {V : List Nat} {P : Point C} {s t : State}
    (h : JacPost K.M K.S base 8192 C Sl V K.D P s t) : PointPost base V K.D P s t := by
  obtain ⟨E,hk,hi,hp⟩ := h
  exact ⟨E,liftProg hk (by decide +kernel),hi,hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.Allocated
