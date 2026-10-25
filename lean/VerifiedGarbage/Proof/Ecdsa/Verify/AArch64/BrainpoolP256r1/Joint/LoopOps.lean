module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Fetch
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Digit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.TableLayout
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.State

/-! A public digit addition, including the zero-pair case. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem Changes.of_keeps {base : Addr} {W : List (Nat × Nat)} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (h0 : .x0 ∉ rs) : Changes base W s t :=
  ⟨h.gpr _ h0,h.rd,h.wr,h.sp,fun _ _ => congrFun h.mem _⟩

theorem PointAt.of_mem {base : Addr} {s t : State} {p : Pt} {P : Point C}
    (hp : PointAt base s p P) (he : t.mem=s.mem) : PointAt base t p P := by
  simpa only [PointAt,num,val,tmv,he] using hp

theorem Table.of_changes {base : Addr} {s t : State} {P Q : Point C}
    (ht : Table base P Q 15 s) (hs : Scr s base 8192) (h : Changes base loopWork s t) :
    Table base P Q 15 t := fun d h1 h15 => h.table hs h1 h15 (ht d h1 h15)

theorem zero_test {s : State} {d : Nat} (hd : d < 16) (h2 : s.gpr .x2=BitVec.ofNat 64 d) :
    eval (.zero .x .x2) s=some (decide (d=0)) := by
  change some (s.read .x .x2 == 0)=_
  rw [read_x,h2]
  by_cases hz : d=0
  · rw [hz]; rfl
  · have hn : BitVec.ofNat 64 d ≠ 0 := by
      intro he
      have h := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h
      exact hz h
    rw [decide_eq_false hz,beq_eq_false_iff_ne.mpr hn]

theorem addDigit_ok {base : Addr} {P Q A : Point C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hA : onCurve C A=true) (hi : Inputs base P Q s) (hb : Bits base u v s)
    (ht : Table base P Q 15 s) (hp : PointAt base s resultPt A) (hj : j < 128)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa addDigit s fun t => Changes base loopWork s t ∧ Inputs base P Q t ∧
      Bits base u v t ∧ Table base P Q 15 t ∧
      PointAt base t resultPt (add (pair P Q ((u >>> (2*j))%4) ((v >>> (2*j))%4)) A) ∧
      t.gpr .x19=s.gpr .x19 := by
  rw [addDigit, digitTail]
  refine WP.seq (WP.mono (digit_ok hi.scr hb hj h19) fun s₁ ⟨d₁,k₁⟩ => ?_)
  have W₁ : Changes base loopWork s s₁ := Changes.of_keeps k₁ (by decide)
  have I₁ := hi.unch (W₁.mono loopWork_sub)
  have B₁ := (W₁.mono loopWork_sub).bits hb
  have T₁ := ht.of_changes hi.scr W₁
  have R₁ := hp.of_mem k₁.mem
  let d := digitPair u v j
  have hd : d < 16 := digitPair_lt u v j
  have hda : d%4=(u >>> (2*j))%4 := by dsimp only [d,digitPair]; omega
  have hdb : d/4=(v >>> (2*j))%4 := by dsimp only [d,digitPair]; omega
  refine WP.ite (decide (d=0)) (zero_test hd d₁) (fun hz => ?_) (fun hn => ?_)
  · have hz' : d=0 := of_decide_eq_true hz
    have ha0 : (u >>> (2*j))%4=0 := by rw [hz'] at hda; omega
    have hb0 : (v >>> (2*j))%4=0 := by rw [hz'] at hdb; omega
    have ep : pair P Q ((u >>> (2*j))%4) ((v >>> (2*j))%4)=.infinity := by
      rw [ha0,hb0]; exact pair_zero P Q
    rw [ep]
    exact WP.block_nil ⟨W₁,I₁,B₁,T₁,R₁,k₁.gpr _ (by decide)⟩
  · have hn' : d≠0 := of_decide_eq_false hn
    refine WP.seq (WP.mono (fetch_ok I₁.scr (by omega) (by omega) d₁ (T₁ d (by omega) (by omega)))
      fun s₂ ⟨k₂,E₂,c₂⟩ => ?_)
    have W₂ := W₁.trans (k₂.mono entryWork_sub)
    have I₂ := hi.unch (W₂.mono loopWork_sub)
    have R₂ := k₂.point I₁.scr R₁ (by decide) (by decide)
    rw [hda,hdb] at E₂
    refine WP.mono (sum_points hc hC I₂.scr I₂.mod I₂.a I₂.b I₂.a_lt I₂.b_lt
      (pair_curve hC hP hQ _ _) hA E₂ R₂) fun t ⟨k₃,R₃,c₃⟩ => ?_
    have W := W₂.trans (k₃.mono addWork_sub)
    exact ⟨W,hi.unch (W.mono loopWork_sub),(W.mono loopWork_sub).bits hb,
      ht.of_changes hi.scr W,R₃,c₃.trans (c₂.trans (k₁.gpr _ (by decide)))⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
