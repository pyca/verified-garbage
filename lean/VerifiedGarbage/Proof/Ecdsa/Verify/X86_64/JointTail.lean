module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.Proof.Ecdh.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
public import VerifiedGarbage.Proof.Weierstrass.Jac

import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Weierstrass.JacAdd
/-! The measured Jacobian denominator square and projective check satisfy verification. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/JointSquare.lean`, which only this module imported.
section

/-! Square the Jacobian denominator before the existing projective comparison. -/

section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass

theorem jointSquare_ok {c : Cfg} (hc : BaseCfgOk c)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (h : ProjectiveInput c s₀ base g s) :
    WP isa (ForwardField.programB c.MP' [.mul (c.sl RZ) (c.sl RZ) (c.sl RZ)]).inline s fun t =>
      ProjectiveInput c s₀ base g t ∧
      tmv c.C c.n base t (c.sl RX)=tmv c.C c.n base s (c.sl RX) ∧
      tmv c.C c.n base t (c.sl RZ)=tmv c.C c.n base s (c.sl RZ)*tmv c.C c.n base s (c.sl RZ) := by
  have lay : Lay c.MP' size (·∈[c.sl RX,c.sl RZ]) := lay_map hc rfl rfl rfl (l:=[RX,RZ]) (by decide)
  have hi : Inv c.MP' base size c.C.p (·∈[c.sl RX,c.sl RZ]) [c.sl RX,c.sl RZ] (tmv c.C c.n base s) s := by
    refine ⟨h.scr,modP_of hc h.fixed.mp,fun _ hx => hx,?_,fun _ _ => rfl⟩
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact h.rx_lt
    · exact h.rz_lt
  refine WP.mono (ForwardField.programB_ok lay
    (unitMod_pow_two hc.p_odd _) [.mul (c.sl RZ) (c.sl RZ) (c.sl RZ)] hi
    (by intro op hop x hx; simp only [List.mem_singleton] at hop; subst op; simpa only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] using Or.inr hx)
    (by simp [readsOk,FOp.ins])) fun t ⟨kt,it⟩ => ?_
  have un := kt.unch
  change Unch base (slW c [RZ,TMP]) s.mem t.mem at un
  have rx : sv c base t RX=sv c base s RX :=
    sv_unch un hc.n10 h.scr.nowrap (by decide) (apart_slW (by decide))
  have flag : word t.mem base (c.sl FLAG)=word s.mem base (c.sl FLAG) := by
    apply un.word
    · intro w hw
      have hh := apart_slW (c:=c) (i:=FLAG) (l:=[RZ,TMP]) (by decide) w hw
      have := hc.n0
      omega
    · have := sl_le c hc.n10 (i:=FLAG) (by decide)
      have := h.scr.nowrap
      have := hc.n0
      omega
  have rzv := it.val (c.sl RZ) (by simp [validAfter,FOp.out])
  have rzlt := it.lt (c.sl RZ) (by simp [validAfter,FOp.out])
  refine ⟨⟨it.scr,h.fixed.unch hc.n10 h.scr.nowrap (fixedOk_slW (by decide)) un,
    (sv_unch un hc.n10 h.scr.nowrap (by decide) (apart_slW (by decide))).trans h.k,
    flag.trans h.flag,rx ▸ h.rx_lt,rzlt⟩,?_,?_⟩
  · exact congrArg (fun x => toM c.C.p (2^(64*c.n)) x) rx
  · simpa only [MP'_n,tmv,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_self] using rzv

end VG.Proof.Ecdsa.Verify.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/VerifyJacobian.lean`, which only this module imported.
section

/-! Verification can compare a Jacobian X against the square of its Z coordinate. -/

section

namespace VG.Proof.Ecdsa
open Spec.Weierstrass Spec.EcKey Spec.Ecdsa VG.Proof.Weierstrass VG.Proof.Ecdh

theorem verify_eq_jacobian {C : Curve} (hC : Law C)
    {bs : List Byte} (hlen : bs.length=2*C.len+1) {b0 : Byte} (hb0 : bs.head?=some b0)
    {x y : Nat} (hxv : ofBytes ((bs.drop 1).take C.len)=x) (hyv : ofBytes (bs.drop (C.len+1))=y)
    {P : Point C} (hP : ∀ h : Valid C b0 x y,P=.affine ⟨x,h.2.1⟩ ⟨y,h.2.2.1⟩)
    {e r s : Nat} {sig : List Byte} (hr : ofBytes (sig.take C.len)=r) (hs : ofBytes (sig.drop C.len)=s)
    {u v : Nat} (hu : u<C.n) (hv : v<C.n)
    (hue : Fin.ofNat C.n u=Fin.ofNat C.n e*Fin.ofNat C.n s^(C.n-2))
    (hve : Fin.ofNat C.n v=Fin.ofNat C.n r*Fin.ofNat C.n s^(C.n-2))
    {X Y Z : Fe C} (hR : InvJ C X Y Z (add (mul u (G C)) (mul v P)))
    {xo : Nat} (hxo : xo<C.p) (hx : Fin.ofNat C.p xo=X*(Z*Z)^(C.p-2)) :
    verify C bs e sig=decide (Valid C b0 x y ∧ (1≤r ∧ r<C.n) ∧ (1≤s ∧ s<C.n) ∧
      Z*Z≠0 ∧ Fin.ofNat C.n xo=Fin.ofNat C.n r) := by
  by_cases hz : Z=0
  · have hinf := (hR.z_zero_iff hC).mp hz
    have rep : Rep C 0 1 0 (add (mul u (G C)) (mul v P)) := by
      rw [hinf]
      exact rep_infinity' hC
    have out := verify_eq hC hlen hb0 hxv hyv hP hr hs hu hv hue hve rep
      (Nat.pos_of_ne_zero (NeZero.ne C.p)) (by simp only [Fin.ofNat_zero,Lean.Grind.Semiring.zero_mul])
    simpa only [hz,Lean.Grind.Semiring.zero_mul,ne_eq,not_true_eq_false,false_and,and_false,decide_false] using out
  · have rep : ∃ Y',Rep C X Y' (Z*Z) (add (mul u (G C)) (mul v P)) := by
      generalize he : add (mul u (G C)) (mul v P)=Q at hR ⊢
      cases Q with
      | infinity => exact False.elim (hz ((hR.z_zero_iff hC).mpr rfl))
      | affine x y => exact ⟨y*(Z*Z),hC.mul_ne_zero hz hz,(hR.affine_coords hC).1,rfl⟩
    obtain ⟨Y',hrep⟩ := rep
    exact verify_eq hC hlen hb0 hxv hyv hP hr hs hu hv hue hve hrep hxo hx

end VG.Proof.Ecdsa
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

theorem jointTail_ok {c : Cfg} (hc : BaseCfgOk c) (hC : Law c.C)
    (hpub : c.pubVerify=true) (hnp : c.C.n<c.C.p) (hpn : c.C.p≤2*c.C.n)
    {s₀ sM s : State} {g : Reg → BitVec 64} (hM : Mid c s₀ (s₀.gpr .rcx) g sM)
    (hInput : ProjectiveInput c s₀ (s₀.gpr .rcx) g s)
    (hR : InvJ c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RX))
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ))
      (add (mul (sv c (s₀.gpr .rcx) sM U) (G c.C))
        (mul (sv c (s₀.gpr .rcx) sM V) (peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀))))) :
    WP isa (Code.seq (ForwardField.programB c.MP' [.mul (c.sl RZ) (c.sl RZ) (c.sl RZ)])
      (Impl.Ecdsa.Verify.X86_64.Cfg.tail c)).inline s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧ VPost c s₀ t := by
  have hpR := unitMod_pow_two hc.p_odd (64*c.n)
  apply WP.seq
  refine WP.mono (jointSquare_ok hc hInput) fun a ⟨ha,ax,az⟩ => ?_
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.tail,ite_eq_left (show c.pubVerify=true ∧ c.C.n<c.C.p ∧ c.C.p≤2*c.C.n from ⟨hpub,hnp,hpn⟩)]
  refine WP.mono (projectiveFinal_fields_ok hc hC hnp hpn ha) fun t ⟨saved,xo,hxo,hx,rax⟩ => ⟨saved,?_⟩
  rw [ax,az] at hx
  let P := peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀)
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .rdi)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdi)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq_jacobian hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz : (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)*tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)≠0) ↔
      sv c (s₀.gpr .rcx) a RZ≠0 := by
    rw [←az]
    exact not_congr (toM_eq_zero_iff hpR ha.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdi)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)*tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .rcx) a RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, rax]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .rcx) a RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.X86_64
