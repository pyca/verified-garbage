module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
import VerifiedGarbage.Proof.Rc4.AArch64.Vec


/-! # Clear the unwritten suffix after bounded rejection failure -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Sample (cv cvW)

def zeroBody (w16 : Bool := false) : List Instr := [.movz .x .x13 0 0,.str .w .x13 .x3 0,
  .addImm .x .x3 .x3 (if w16 then 2 else 4),.subImm .x .x4 .x4 1]
def zeroSuffix (w16 : Bool := false) : Prog isa := .ite (.zero .x .x4) (.block [])
  (.loop (.block (zeroBody w16)) (.nonzero .x .x4))

def PrefixZero (w16 : Bool) (m : Mem) (aP : Addr) (L : List Zq) (j : Nat) : Prop :=
  ∀i<j,coeffAtW (cw w16) m aP i=if i<L.length then cvW w16 L i else 0

structure ZInv (w16 : Bool) (aP : Addr) (L : List Zq) (s : State) (j : Nat) (u : State) : Prop where
  keep : Keep [.x3,.x4,.x13] s u
  frame : Frame [polyRegion aP] s.mem u.mem
  x3 : u.gpr .x3=cAddr w16 aP j
  x4 : (u.gpr .x4).toNat=256-j
  coeffs : PrefixZero w16 u.mem aP L j

theorem zeroBody_ok {w16 : Bool} {aP : Addr} {L : List Zq} {s u : State} {j : Nat}
    (hina : ∀i<256,InRegions s.wr (cAddr w16 aP i) 4)
    (hl : L.length≤j) (hj : j<256) (h : ZInv w16 aP L s j u) :
    WP isa (.block (zeroBody w16)) u (ZInv w16 aP L s (j+1)) := by
  refine wp_movz fun a ha ea => wp_strw (a := cAddr w16 aP j) (by decide)
    (by rw [ha.gpr .x3 (by decide),h.x3,ptr_zero])
    (by rw [ha.wr,h.keep.wr]; exact hina _ hj) fun b hb =>
    wp_addImm (by cases w16 <;> decide) fun c hc ec => wp_subImm (by decide) fun v hv ev => wp_nil ?_
  have hk := (((ha.keep.trans hb.keep).trans hc.keep).trans hv.keep).mono (rs' := [.x3,.x4,.x13]) (by decide)
  have hm : v.mem=u.mem.writeW (cAddr w16 aP j) (0 : BitVec 32) := by
    rw [hv.mem,hc.mem,hb.mem,ea,ha.mem]
    rfl
  refine ⟨(h.keep.trans hk).mono (by decide),?_,?_,?_,?_⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (cAddr_contains4 w16 _ hj)
  · rw [hv.gpr .x3 (by decide),ec,hb.gpr,ha.gpr .x3 (by decide),h.x3,← cAddr_add w16 aP j 1]
    cases w16 <;> rfl
  · rw [ev,toNat_sub_n (by rw [hc.gpr .x4 (by decide),hb.gpr,ha.gpr .x4 (by decide),h.x4]; change 1≤256-j; omega),
      hc.gpr .x4 (by decide),hb.gpr,ha.gpr .x4 (by decide),h.x4]
    change 256-j-1=256-(j+1)
    omega
  · intro i hi
    rw [hm,coeffAtW_writeW32 _ _ (show i<256 by omega) hj _ (by decide)]
    by_cases he : j=i
    · rw [ite_eq_left he,ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right he,ite_eq_right (by omega),h.coeffs i (by omega)]

theorem zeroSuffix_ok {w16 : Bool} {aP : Addr} {L : List Zq} {s₀ s : State}
    (hina : ∀i<256,InRegions s₀.wr (cAddr w16 aP i) 4)
    (h : Scalar.AccW w16 aP s₀ L s) : WP isa (zeroSuffix w16) s fun u =>
      Keep [.x3,.x4,.x13] s u ∧ Frame [polyRegion aP] s₀.mem u.mem ∧
        CoeffsUpToW w16 u.mem aP L.length (cvW w16 L) (fun _ => 0) := by
  have hl := h.len
  have zi : ZInv w16 aP L s L.length s :=
    ⟨Keep.refl _ _,Frame.refl _ _,h.x3,h.x4,fun i hi => by rw [ite_eq_left hi]; exact h.coeffs i hi⟩
  refine WP.ite (s.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · rw [eq_zero_iff,decide_eq_true_eq,h.x4] at hz
    have he : L.length=256 := by omega
    exact wp_nil ⟨Keep.refl _ _,h.frame,fun i hi => zi.coeffs i (by omega)⟩
  · rw [eq_zero_iff,decide_eq_false_iff_not,h.x4] at hz
    have hn : 0<256-L.length := by omega
    refine WP.mono (count_loop hn (fun k u => ZInv w16 aP L s (L.length+k) u)
      (fun k hk u hu => WP.mono (zeroBody_ok (by intro i hi; rw [h.wr]; exact hina i hi)
        (by omega) (by omega) hu) fun v hv => ⟨hv,by rw [hv.x4]; omega⟩) zi) fun u hu => ?_
    refine ⟨hu.keep,h.frame.trans hu.frame,?_⟩
    intro i hi
    exact hu.coeffs i (by omega)


theorem zeroSuffix_prefix {w16 : Bool} {aP : Addr} {L : List Zq} {s : State}
    (hina : ∀i<256,InRegions s.wr (cAddr w16 aP i) 4)
    (hl : L.length≤256) (hc : Scalar.CoeffsW w16 s.mem aP L)
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (h4 : (s.gpr .x4).toNat=256-L.length) :
    WP isa (zeroSuffix w16) s fun u => Keep [.x3,.x4,.x13] s u ∧
      Frame [polyRegion aP] s.mem u.mem ∧
        CoeffsUpToW w16 u.mem aP L.length (cvW w16 L) (fun _ => 0) := by
  have zi : ZInv w16 aP L s L.length s :=
    ⟨Keep.refl _ _,Frame.refl _ _,h3,h4,fun i hi => by rw [ite_eq_left hi]; exact hc i hi⟩
  refine WP.ite (s.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · rw [eq_zero_iff,decide_eq_true_eq,h4] at hz
    have he : L.length=256 := by omega
    exact wp_nil ⟨Keep.refl _ _,Frame.refl _ _,fun i hi => zi.coeffs i (by omega)⟩
  · rw [eq_zero_iff,decide_eq_false_iff_not,h4] at hz
    have hn : 0<256-L.length := by omega
    refine WP.mono (count_loop hn (fun k u => ZInv w16 aP L s (L.length+k) u)
      (fun k hk u hu => WP.mono (zeroBody_ok hina (by omega) (by omega) hu)
        fun v hv => ⟨hv,by rw [hv.x4]; omega⟩) zi) fun u hu => ?_
    exact ⟨hu.keep,hu.frame,fun i hi => hu.coeffs i (by omega)⟩

end VG.Proof.MlKem.AArch64.Rej8
