module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Digit
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.State

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.TableLayout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Copy
/-! A public digit addition, including the zero-pair case. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/BrainpoolP256r1/Joint/Fetch.lean`, which only this module imported.
section

/-! Public lookup of a nonzero digit pair, with all pointer bounds checked. -/

section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem fetchHead_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d) :
    WP isa (.block fetchHead) s fun t =>
      t.gpr .x16 = off base (tablePt d).x ∧ Keeps [.x2,.x16,.x17] s t := by
  have hsub : BitVec.ofNat 64 d - 1 = BitVec.ofNat 64 (d-1) := by
    apply BitVec.eq_of_toNat_eq
    change (2^64-1+d%(2^64))%(2^64)=(d-1)%(2^64)
    omega
  apply WP.of_runBlock
  simp only [fetchHead,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1 : Nat) < 4096 by decide,show 16*0 < Size.x.bits by decide,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,h2,hs.x0,
    Nat.mul_zero,BitVec.shiftLeft_zero,
    show (96 : BitVec 16).setWidth 64 = BitVec.ofNat 64 96 from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change base+BitVec.ofNat 64 5280+(BitVec.ofNat 64 d-1)*BitVec.ofNat 64 96 = off base (tablePt d).x
    rw [hsub,←BitVec.ofNat_mul]
    change base+BitVec.ofNat 64 5280+BitVec.ofNat 64 ((d-1)*96)=
      base+BitVec.ofNat 64 (5280+96*(d-1))
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact congrArg (base+·) (congrArg (BitVec.ofNat 64) (by omega))
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem fetch_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    WP isa (.block fetch) s fun t =>
      Changes base entryWork s t ∧ PointAt base t entry P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have ex_bound : entry.x+32 ≤ 8192 := by decide
  have ey_bound : entry.y+32 ≤ 8192 := by decide
  have htab := table_coord_bounds h1 h15
  have ha : (tablePt d).x+96 ≤ 8192 := by
    have hb := (htab (tablePt d).z (by simp)).2.1
    change _+32 ≤ 6720 at hb
    dsimp only [tablePt] at hb ⊢; omega
  have hab : (tablePt d).x ≤ 8192 := by omega
  have hsep : ∀ e ∈ coordinates entry,e+32 ≤ (tablePt d).x := by
    have hh : ∀ e ∈ coordinates entry,e+32 ≤ tableAt := by decide
    intro e he; exact Nat.le_trans (hh e he) (htab _ (by simp)).1
  have sepX := hsep entry.x (by decide)
  have sepY := hsep entry.y (by decide)
  have sepZ := hsep entry.z (by decide)
  rw [fetch]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs h1 h15 h2) fun s₁ ⟨p₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₁ p₁ (a:=(tablePt d).x) (src:=0) (dst:=entry.x)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by simpa using hsep _ (by simp))))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₂ p₂ (a:=(tablePt d).x) (src:=32) (dst:=entry.y)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok 4 hs₃ p₃ (a:=(tablePt d).x) (src:=64) (dst:=entry.z)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun t ⟨z,k₄,u₄⟩ => ?_
  have e_x : num base t entry.x = num base s (tablePt d).x := by
    change wordsVal t.mem base entry.x 4 = wordsVal s.mem base (tablePt d).x 4
    rw [u₄.wordsVal (by decide) (by omega),
      u₃.wordsVal (by decide) (by omega),x,k₁.mem]
    rfl
  have e_y : num base t entry.y = num base s (tablePt d).y := by
    change wordsVal t.mem base entry.y 4 = wordsVal s.mem base (tablePt d).y 4
    rw [u₄.wordsVal (by decide) (by omega),y]
    rw [u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  have e_z : num base t entry.z = num base s (tablePt d).z := by
    change wordsVal t.mem base entry.z 4 = wordsVal s.mem base (tablePt d).z 4
    rw [z,u₃.wordsVal (Or.inr (by omega)) (by omega),
      u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  have kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))
  have u : Unch base entryWork s.mem t.mem := by
    rw [←k₁.mem]
    exact (u₂.unch.trans (u₃.unch.trans u₄.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> decide)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,u⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro e he
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [e_x]; exact hp.1 _ (by simp)
    · rw [e_y]; exact hp.1 _ (by simp)
    · rw [e_z]; exact hp.1 _ (by simp)
  · have ex := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_x
    have ey := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_y
    have ez := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_z
    change val base t entry.x = val base s (tablePt d).x at ex
    change val base t entry.y = val base s (tablePt d).y at ey
    change val base t entry.z = val base s (tablePt d).z at ez
    rw [ex,ey,ez]; exact hp.2
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
end

end

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
