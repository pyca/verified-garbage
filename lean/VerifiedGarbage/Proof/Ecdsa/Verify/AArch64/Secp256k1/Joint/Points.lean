module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Scalars
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.State
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.CombDigitW
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Inputs`, which only this module used -/

section

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Moves`, which this module and modules that import it used -/

section

/-! Moving projective triples without changing their representatives. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

structure CopyLayout (o a : Pt) : Prop where
  end_le : ∀ x ∈ coordinates o ++ coordinates a,x+32 ≤ 8192
  aligned : ∀ x ∈ coordinates o ++ coordinates a,x % 8 = 0
  apart : ∀ x ∈ coordinates o,∀ y ∈ coordinates o ++ coordinates a,x ≠ y →
    x+32 ≤ y ∨ y+32 ≤ x
  different : ∀ x ∈ coordinates o,x ∉ coordinates a
  nodup : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z

theorem copy_point {base : Addr} {s : State} (hs : Scr s base 8192) {a o : Pt}
    (hL : CopyLayout o a) {P : Point C} (hp : PointAt base s a P) :
    WP isa (.block (copyPt 4 o a)) s fun t =>
      Changes base ((coordinates o).map (·,32)) s t ∧ PointAt base t o P ∧
      t.gpr .x19 = s.gpr .x19 := by
  have hle : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x+8*4 ≤ 8192 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.end_le
  have hal : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x % 8 = 0 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.aligned
  have hap : ∀ x ∈ [o.x,o.y,o.z],∀ y ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x ≠ y →
      x+8*4 ≤ y ∨ y+8*4 ≤ x := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.apart
  refine WP.mono (copyPt_ok hs hle hal hap hL.different hL.nodup) fun t ⟨x,y,z,k,u⟩ => ?_
  refine ⟨⟨k.gpr _ (by decide),k.rd,k.wr,k.sp,u⟩,⟨?_,?_⟩,k.gpr _ (by decide)⟩
  · intro p hp'
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · rw [show num base t o.x = num base s a.x from x]; exact hp.1 _ (by simp)
    · rw [show num base t o.y = num base s a.y from y]; exact hp.1 _ (by simp)
    · rw [show num base t o.z = num base s a.z from z]; exact hp.1 _ (by simp)
  · have vx : val base t o.x = val base s a.x := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) x
    have vy : val base t o.y = val base s a.y := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) y
    have vz : val base t o.z = val base s a.z := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) z
    rw [vx,vy,vz]; exact hp.2

theorem entry_from_result : CopyLayout entry resultPt := ⟨by decide,by decide,by decide,by decide,by decide⟩

/-- The all-zero scalar pair starts from the standard projective infinity. -/
theorem infinity_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (hc : BaseCfgOk cfg) (hC : Law C) :
    WP isa (.block infinity) s fun t =>
      Changes base ((coordinates resultPt).map (·,32)) s t ∧
      PointAt base t resultPt .infinity ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have hn8 : cfg.n = 4 := rfl
  have hex : resultPt.x+32 ≤ 8192 := by decide
  have hey : resultPt.y+32 ≤ 8192 := by decide
  have hm0 : 0 < C.p := by change 0 < cfg.C.p; have := hc.p_ge; omega_using [this]
  have hm1 : cfg.mont 1 < C.p := Nat.mod_lt _ hm0
  have hm1r : cfg.mont 1 < 2 ^ (64*cfg.n) := Nat.lt_trans hm1 hc.p_lt
  rw [infinity,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n:=cfg.n) (o:=resultPt.x) (x:=0) (by decide) (by decide) (Nat.pow_pos (by decide)))
    fun s₁ ⟨x,k₁,u₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (setConst_ok hs₁ (n:=cfg.n) (o:=resultPt.y) (by decide) (by decide) hm1r)
    fun s₂ ⟨y,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n:=cfg.n) (o:=resultPt.z) (x:=0) (by decide) (by decide) (Nat.pow_pos (by decide)))
    fun t ⟨z,k₃,u₃⟩ => ?_
  have kt := (k₁.trans k₂).trans k₃
  have xt : num base t resultPt.x = 0 := by
    unfold num
    rw [u₃.wordsVal (by decide) (by have := hs.nowrap; omega_using [hn8, hex]),
      u₂.wordsVal (by decide) (by have := hs.nowrap; omega_using [hn8, hex])]; exact x
  have yt : num base t resultPt.y = cfg.mont 1 := by
    unfold num
    rw [u₃.wordsVal (by decide) (by have := hs.nowrap; omega_using [hn8, hey])]; exact y
  have zt : num base t resultPt.z = 0 := z
  have ut : Unch base ((coordinates resultPt).map (·,32)) s.mem t.mem :=
    (u₁.unch.trans (u₂.unch.trans u₃.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> decide)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,ut⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro p hp
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rw [xt]; exact hm0
    · rw [yt]; exact hm1
    · rw [zt]; exact hm0
  · have vx : val base t resultPt.x = 0 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) xt).trans (toM_zero _ _)
    have vy : val base t resultPt.y = 1 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) yt).trans (toM_cmont hc 1)
    have vz : val base t resultPt.z = 0 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) zt).trans (toM_zero _ _)
    rw [vx,vy,vz]; exact rep_infinity' hC

end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! The constants and affine input points remain unchanged during joint multiplication. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

abbrev gSource : Pt := cfg.pt GX GY ONEP
abbrev qSource : Pt := cfg.pt PX PY ONEP
abbrev arithmeticWork := loopWork ++ [(tableAt,1440)]

theorem Changes.cover {base : Addr} {W W' : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t)
    (hs : ∀ w ∈ W,∃ w' ∈ W',w'.1 ≤ w.1 ∧ w.1+w.2 ≤ w'.1+w'.2) : Changes base W' s t :=
  ⟨h.x0,h.rd,h.wr,h.sp,h.mem.cover hs⟩

structure Inputs (base : Addr) (P Q : Point C) (s : State) : Prop where
  scr : Scr s base 8192
  mod : ModOkA cfg.MP' 8192 C.p s.mem base
  a_lt : num base s (cfg.sl AP) < C.p
  b_lt : num base s (cfg.sl EXPP) < C.p
  a : val base s (cfg.sl AP) = Fin.ofNat C.p C.a
  b : val base s (cfg.sl EXPP) = Fin.ofNat C.p (3*C.b)
  generator : PointAt base s gSource P
  peer : PointAt base s qSource Q

theorem Inputs.unch {base : Addr} {P Q : Point C} {s t : State} (h : Inputs base P Q s)
    (k : Changes base arithmeticWork s t) : Inputs base P Q t := by
  have hn8 : cfg.n = 4 := rfl
  have en (o : Nat) (hl : o+32 ≤ 8192)
      (hap : ∀ w ∈ arithmeticWork,o+32 ≤ w.1 ∨ w.1+w.2 ≤ o) : num base t o = num base s o :=
    k.mem.wordsVal hap (by have := h.scr.nowrap; omega_using [hn8, hl])
  have ea := en (cfg.sl AP) (by decide) (by decide)
  have eb := en (cfg.sl EXPP) (by decide) (by decide)
  refine ⟨k.scr h.scr,h.mod.unch k.mem (by decide) h.scr.nowrap,?_,?_,?_,?_,?_,?_⟩
  · rw [ea]; exact h.a_lt
  · rw [eb]; exact h.b_lt
  · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) ea).trans h.a
  · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) eb).trans h.b
  · exact k.point h.scr h.generator (by decide) (by decide)
  · exact k.point h.scr h.peer (by decide) (by decide)

theorem entryWork_sub : ∀ w ∈ entryWork,w ∈ loopWork := by
  intro w h; exact List.mem_append_right _ h

theorem addWork_sub : ∀ w ∈ addWork,w ∈ loopWork := by
  intro w h; exact List.mem_append_left _ h

theorem loopWork_sub : ∀ w ∈ loopWork,w ∈ arithmeticWork := by
  intro w h; exact List.mem_append_left _ h

theorem double_points {base : Addr} {P Q A : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hI : Inputs base P Q s)
    (hA : onCurve C A = true) (hp : PointAt base s resultPt A) :
    WP isa double s fun t => Changes base loopWork s t ∧ Inputs base P Q t ∧
      PointAt base t resultPt (add A A) ∧ t.gpr .x19 = s.gpr .x19 := by
  rw [double]
  refine WP.seq (WP.mono (copy_point hI.scr entry_from_result hp) fun s₁ ⟨k₁,p₁,c₁⟩ => ?_)
  have W₁ := k₁.mono entryWork_sub
  have I₁ := hI.unch (W₁.mono loopWork_sub)
  have p₁' := k₁.point hI.scr hp (by decide) (by decide)
  refine WP.mono (sum_points hc hC I₁.scr I₁.mod I₁.a I₁.b I₁.a_lt I₁.b_lt hA hA p₁ p₁')
    fun t ⟨k₂,p₂,c₂⟩ => ?_
  have W₂ := k₂.mono addWork_sub
  have W := W₁.trans W₂
  exact ⟨W,hI.unch (W.mono loopWork_sub),p₂,c₂.trans c₁⟩
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Loop`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.LoopOps`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Digit`, which this module and modules that import it used -/

section

/-! Reading one public pair of unsigned two-bit digits. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

abbrev Bits (base : Addr) (u v : Nat) (s : State) : Prop :=
  (∀ t < 256,s.mem (off base (bitsU+t)) = if u.testBit t then 1 else 0) ∧
  (∀ t < 256,s.mem (off base (bitsV+t)) = if v.testBit t then 1 else 0)

def digitPair (u v j : Nat) : Nat := (u >>> (2*j)) % 4 + 4*((v >>> (2*j)) % 4)

theorem digitPair_lt (u v j : Nat) : digitPair u v j < 16 := by
  unfold digitPair; omega_using []

theorem Changes.bits {base : Addr} {u v : Nat} {s t : State}
    (h : Changes base arithmeticWork s t) (hb : Bits base u v s) : Bits base u v t := by
  have apart : ∀ b ∈ [bitsU,bitsV],∀ j < 256,∀ w ∈ arithmeticWork,
      b+j+1 ≤ w.1 ∨ w.1+w.2 ≤ b+j := by
    intro b h j hj w hw
    have hd : ∀ b ∈ [bitsU,bitsV],∀ w ∈ arithmeticWork,b+256 ≤ w.1 ∨ w.1+w.2 ≤ b := by decide
    have := hd b h w hw; omega_using [hj, this]
  constructor
  · intro j hj
    rw [h.mem.byte (apart bitsU (by simp) j hj) (by change 2944+j < 2^64; omega_using [hj])]
    exact hb.1 j hj
  · intro j hj
    rw [h.mem.byte (apart bitsV (by simp) j hj) (by change 3200+j < 2^64; omega_using [hj])]
    exact hb.2 j hj

theorem index2_ok {s : State} {base : Addr} (hs : Scr s base 8192) {j : Nat}
    (hx : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.lsl .x .x16 .x19 1,.add .x .x16 .x0 .x16]) s fun t =>
      t.gpr .x16 = off base (2*j) ∧ Keeps [.x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 1 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hx,hs.x0,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change base + BitVec.ofNat 64 j * BitVec.ofNat 64 2 = base + BitVec.ofNat 64 (2*j)
    rw [←BitVec.ofNat_mul,Nat.mul_comm j 2]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem read2_ok {base : Addr} {s : State} (hs : Scr s base 8192) {bits k j : Nat}
    (hbits : bits+256 ≤ 8192) (henc : bits+2 ≤ 4096) (hj : j < 128)
    (h16 : s.gpr .x16 = off base (2*j))
    (hb : ∀ t < 256,s.mem (off base (bits+t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (hornerBits bits 2)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 ((k >>> (2*j)) % 4) ∧ Keeps [.x2,.x4] s t := by
  have hv : ∀ i,(k.testBit (2*j+(i-bits))).toNat ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv 2 bits (s:=s) (by decide) henc fun i hi => ?_)
    fun t ⟨v,h⟩ => ⟨?_,h⟩
  · have e : s.gpr .x16+BitVec.ofNat 64 (bits+i) = off base (bits+(2*j+i)) := by
      rw [h16,off,off,BitVec.add_assoc,←BitVec.ofNat_add]
      exact congrArg (base+·) (congrArg _ (by omega_using []))
    refine ⟨?_,?_⟩
    · rw [e]; exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega_using [hbits, hj, hi]) (by decide)⟩
    · rw [e,hb _ (by omega_using [hj, hi]),show bits+i-bits=i by omega_using []]
      cases k.testBit (2*j+i) <;> rfl
  · have he : hornerVal (fun i => (k.testBit (2*j+(i-bits))).toNat) bits 2 = combWin 2 k j := by
      have hh := hornerVal_eq k 2 j 2 (Nat.le_refl _)
      rw [Nat.sub_self,Nat.add_zero] at hh
      rw [combWin,←hh]
      exact hornerVal_congr fun i _ => by simp only [show bits+i-bits=i by omega_using []]
    rw [v,he,combWin,Nat.shiftRight_eq_div_pow]

theorem save_digit_ok (s : State) :
    WP isa (.block [.addImm .x .x6 .x2 0]) s fun t => t.gpr .x6=s.gpr .x2 ∧ Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show (0 : Nat) < 4096 by decide,BitVec.setWidth_eq,BitVec.add_zero,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem combine_ok (s : State) {a b : Nat}
    (h6 : s.gpr .x6=BitVec.ofNat 64 a) (h2 : s.gpr .x2=BitVec.ofNat 64 b) :
    WP isa (.block [.lsl .x .x2 .x2 2,.add .x .x2 .x2 .x6]) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (a+4*b) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 2 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h6,h2,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 b*BitVec.ofNat 64 4+BitVec.ofNat 64 a=BitVec.ofNat 64 (a+4*b)
    rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega_using [])
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem digit_ok {base : Addr} {s : State} (hs : Scr s base 8192) {u v j : Nat}
    (hb : Bits base u v s) (hj : j < 128) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block digit) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v j) ∧ Keeps [.x2,.x4,.x6,.x16] s t := by
  rw [Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint.digit]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (index2_ok hs h19) fun s₁ ⟨p₁,k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (read2_ok (hs.of_keeps k₁ (by decide)) (bits:=bitsU) (k:=u) (by decide) (by decide) hj p₁
    (by rw [k₁.mem]; exact hb.1)) fun s₂ ⟨v₂,k₂⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (save_digit_ok s₂) fun s₃ ⟨v₃,k₃⟩ => ?_
  rw [WP.block_append_iff]
  have hs₃ := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have p₃ : s₃.gpr .x16=off base (2*j) := by rw [k₃.gpr _ (by decide),k₂.gpr _ (by decide),p₁]
  refine WP.mono (read2_ok hs₃ (bits:=bitsV) (k:=v) (by decide) (by decide) hj p₃
    (by rw [k₃.mem,k₂.mem,k₁.mem]; exact hb.2)) fun s₄ ⟨v₄,k₄⟩ => ?_
  have e₆ : s₄.gpr .x6=BitVec.ofNat 64 ((u >>> (2*j)) % 4) := by rw [k₄.gpr _ (by decide),v₃,v₂]
  refine WP.mono (combine_ok s₄ e₆ v₄) fun t ⟨v₅,k₅⟩ => ?_
  exact ⟨v₅,((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))⟩
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Fetch`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Copy`, which this module and modules that import it used -/

section

/-! Copies through the joint table's public entry pointer. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

theorem word_at_offset (m : Mem) (base : Addr) (a b : Nat) :
    word m (off base a) b = word m base (a+b) := by
  unfold word off
  rw [VG.Offset.add_add]

theorem source_ptr {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size)
    (ha : a ≤ size) (hr : s.gpr .x16 = off base a) :
    Ptr s .x16 (off base a) (size-a) where
  reg := hr
  enc := by have := hs.enc; omega
  ld d hd := by
    rw [VG.Offset.add_add]
    exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega_using [hd]) (by decide)⟩

/-- The selected entry is above or wholly below the destination. -/
theorem copyFrom_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {a src dst : Nat},
    Scr s base size → s.gpr .x16 = off base a →
    dst + 8*n ≤ size → a + src + 8*n ≤ size → dst % 8 = 0 → src % 8 = 0 →
    (dst + 8*n ≤ a + src ∨ a + src + 8*n ≤ dst) →
    WP isa (.block (copyFrom n dst src)) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base (a+src) n ∧
      KeepRegs [.x4] s t ∧ Outside base dst (8*n) s.mem t.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1, s, base, a, src, dst, hs, hr, hd, ha, hd8, hs8, hsep => by
    have hn := hs.nowrap
    have hp := source_ptr hs (by omega_using [ha] : a ≤ size) hr
    rw [copyFrom,WP.block_append_iff,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ldR_ok hp (d:=src) (by omega_using [ha]) hs8 .x4) fun s₀ ⟨e₀,k₀,_⟩ => ?_
    rw [word_at_offset] at e₀
    have hs₀ := hs.of_keeps k₀ (by decide)
    refine WP.mono (st_out hs₀ (o:=dst) (by omega_using [hd]) hd8 .x4) fun s₁ ⟨m₁,k₁,g₁⟩ => ?_
    rw [e₀,k₀.mem] at m₁
    have k₀₁ : KeepRegs [.x4] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    have hs₁ := hs.of_keepRegs k₀₁ (by decide)
    have O₁ : Outside base dst 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega_using [hd, hn])
    have hr₁ : s₁.gpr .x16 = off base a := (k₀₁.gpr .x16 (by decide)).trans hr
    have e₁ : wordsVal s₁.mem base (a+src+8) n = wordsVal s.mem base (a+src+8) n :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [ha, hn])
    refine WP.mono (copyFrom_ok n hs₁ hr₁ (dst:=dst+8) (src:=src+8)
      (by omega_using [hd]) (by omega_using [ha]) (by omega_using [hd8]) (by omega_using [hs8]) (by omega_using [hsep])) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
    refine ⟨?_,k₀₁.trans k₂,fun x hx => by rw [O₂ x (by omega_using [hx]),O₁ x (by omega_using [hx])]⟩
    rw [show a+(src+8)=a+src+8 by omega_using []] at e₂
    rw [wordsVal,O₂.word (by omega_using []) (by omega_using [hd, hn]),m₁,word_writeW_self,e₂,e₁,wordsVal]
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Table`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.TableLayout`, which this module and modules that import it used -/

section

/-! The fifteen projective table entries fit beside the existing arithmetic workspace. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

abbrev resultWork : List (Nat × Nat) := (coordinates resultPt).map (·,32)

theorem resultWork_sub : ∀ w ∈ resultWork,w ∈ loopWork := by decide

theorem table_coord_bounds {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ x ∈ coordinates (tablePt d),tableAt ≤ x ∧ x+32 ≤ 6720 ∧ x % 8 = 0 := by
  intro x hx
  change 5280 ≤ x ∧ x+32 ≤ 6720 ∧ x % 8 = 0
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨by omega,by omega,by omega⟩

theorem tableWork_cover {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ w ∈ (coordinates (tablePt d)).map (·,32),
      ∃ w' ∈ arithmeticWork,w'.1 ≤ w.1 ∧ w.1+w.2 ≤ w'.1+w'.2 := by
  intro w hw
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  have h := table_coord_bounds h1 h15 x hx
  exact ⟨(tableAt,1440),List.mem_append_right _ (by simp),h.1,h.2.1⟩

theorem Changes.table {base : Addr} {s t : State} (h : Changes base loopWork s t)
    (hs : Scr s base 8192) {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    PointAt base t (tablePt d) P := by
  refine h.point hs hp (fun x hx => Nat.le_trans (table_coord_bounds h1 h15 x hx).2.1 (by decide)) ?_
  intro x hx w hw
  have hb := (table_coord_bounds h1 h15 x hx).1
  have hh : ∀ w ∈ loopWork,w.1+w.2 ≤ tableAt := by decide
  exact Or.inr (Nat.le_trans (hh w hw) hb)

theorem earlier_table_apart {j d : Nat} (hj : 1 ≤ j) (hjd : j < d) :
    ∀ x ∈ coordinates (tablePt j),∀ w ∈ (coordinates (tablePt d)).map (·,32),
      x+32 ≤ w.1 ∨ w.1+w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> exact Or.inl (by omega_arith)
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! Building the joint digit-pair table with the existing complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

abbrev Table (base : Addr) (P Q : Point C) (m : Nat) (s : State) : Prop :=
  ∀ d,1 ≤ d → d ≤ m → PointAt base s (tablePt d) (pair P Q (d%4) (d/4))

theorem entry_from_generator : CopyLayout entry gSource := ⟨by decide,by decide,by decide,by decide,by decide⟩
theorem entry_from_peer : CopyLayout entry qSource := ⟨by decide,by decide,by decide,by decide,by decide⟩

end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! Public lookup of a nonzero digit pair, with all pointer bounds checked. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

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
    exact congrArg (base+·) (congrArg (BitVec.ofNat 64) (by omega_using []))
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
    dsimp only [tablePt] at hb ⊢; omega_using [hb]
  have hab : (tablePt d).x ≤ 8192 := by omega_using [ha]
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
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by simpa using hsep _ (by simp))))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₂ p₂ (a:=(tablePt d).x) (src:=32) (dst:=entry.y)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by omega_using [sepY])))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok 4 hs₃ p₃ (a:=(tablePt d).x) (src:=64) (dst:=entry.z)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by omega_using [sepZ])))
    fun t ⟨z,k₄,u₄⟩ => ?_
  have e_x : num base t entry.x = num base s (tablePt d).x := by
    change wordsVal t.mem base entry.x 4 = wordsVal s.mem base (tablePt d).x 4
    rw [u₄.wordsVal (by decide) (by omega_using [ex_bound]),
      u₃.wordsVal (by decide) (by omega_using [ex_bound]),x,k₁.mem]
    rfl
  have e_y : num base t entry.y = num base s (tablePt d).y := by
    change wordsVal t.mem base entry.y 4 = wordsVal s.mem base (tablePt d).y 4
    rw [u₄.wordsVal (by decide) (by omega_using [ey_bound]),y]
    rw [u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  have e_z : num base t entry.z = num base s (tablePt d).z := by
    change wordsVal t.mem base entry.z 4 = wordsVal s.mem base (tablePt d).z 4
    rw [z,u₃.wordsVal (Or.inr (by omega_using [sepY])) (by omega_using [ha]),
      u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
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
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! A public digit addition, including the zero-pair case. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

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
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hd])] at h
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
  have hda : d%4=(u >>> (2*j))%4 := by dsimp only [d,digitPair]; omega_using []
  have hdb : d/4=(v >>> (2*j))%4 := by dsimp only [d,digitPair]; omega_using []
  refine WP.ite (decide (d=0)) (zero_test hd d₁) (fun hz => ?_) (fun hn => ?_)
  · have hz' : d=0 := of_decide_eq_true hz
    have ha0 : (u >>> (2*j))%4=0 := by rw [hz'] at hda; omega_using [hda]
    have hb0 : (v >>> (2*j))%4=0 := by rw [hz'] at hdb; omega_using [hdb]
    have ep : pair P Q ((u >>> (2*j))%4) ((v >>> (2*j))%4)=.infinity := by
      rw [ha0,hb0]; exact pair_zero P Q
    rw [ep]
    exact WP.block_nil ⟨W₁,I₁,B₁,T₁,R₁,k₁.gpr _ (by decide)⟩
  · have hn' : d≠0 := of_decide_eq_false hn
    refine WP.seq (WP.mono (fetch_ok I₁.scr (by omega) (by omega) d₁ (T₁ d (by omega_using [hn']) (by omega_using [hd])))
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
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! One shared Horner loop advances both public verification scalars. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

structure Running (base : Addr) (P Q : Point C) (u v j : Nat) (s : State) : Prop where
  inputs : Inputs base P Q s
  bits : Bits base u v s
  table : Table base P Q 15 s
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  point : PointAt base s resultPt (stage P Q u v j)

theorem step_ok {base : Addr} {P Q : Point C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h1 : 1 ≤ j) (h256 : j ≤ 128) (h : Running base P Q u v j s) :
    WP isa step s fun t => Changes base loopWork s t ∧ Running base P Q u v (j-1) t := by
  rw [step]
  refine WP.seq (WP.mono (decCounter_ok s h1 (by omega_using [h256]) h.counter) fun s₀ ⟨c₀,k₀⟩ => ?_)
  have W₀ : Changes base loopWork s s₀ := Changes.of_keeps k₀ (by decide)
  have I₀ := h.inputs.unch (W₀.mono loopWork_sub)
  have R₀ := h.point.of_mem k₀.mem
  have hA : onCurve C (stage P Q u v j)=true := pair_curve hC hP hQ _ _
  refine WP.seq (WP.mono (double_points hc hC I₀ hA R₀) fun s₁ ⟨k₁,I₁,R₁,c₁⟩ => ?_)
  refine WP.seq (WP.mono (double_points hc hC I₁ (hC.onCurve_add hA hA) R₁) fun s₂ ⟨k₂,I₂,R₂,c₂⟩ => ?_)
  have W₂ := (W₀.trans k₁).trans k₂
  have B₂ := (W₂.mono loopWork_sub).bits h.bits
  have T₂ := h.table.of_changes h.inputs.scr W₂
  have C₂ : s₂.gpr .x19=BitVec.ofNat 64 (j-1) := c₂.trans (c₁.trans c₀)
  have hAA := hC.onCurve_add hA hA
  refine WP.mono (addDigit_ok hc hC hP hQ (hC.onCurve_add hAA hAA) I₂ B₂ T₂ R₂
    (by omega_using [h256]) C₂) fun t ⟨k₃,I₃,B₃,T₃,R₃,c₃⟩ => ?_
  have eqj : j-1+1=j := by omega_using [h1]
  have em := at_step hC hP hQ u v (j-1)
  rw [eqj] at em
  have hcmt := point_comm hC
    (pair_curve hC hP hQ ((u >>> (2*(j-1)))%4) ((v >>> (2*(j-1)))%4))
    (hC.onCurve_add hAA hAA)
  have final : add (pair P Q ((u >>> (2*(j-1)))%4) ((v >>> (2*(j-1)))%4))
      (add (add (stage P Q u v j) (stage P Q u v j))
        (add (stage P Q u v j) (stage P Q u v j))) = stage P Q u v (j-1) := hcmt.trans em
  rw [final] at R₃
  exact ⟨W₂.trans k₃,⟨I₃,B₃,T₃,c₃.trans C₂,R₃⟩⟩

theorem loop_ok {base : Addr} {P Q : Point C} {u v : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h : Running base P Q u v 128 s) :
    WP isa (.loop step (.nonzero .x .x19)) s fun t =>
      Changes base loopWork s t ∧ Running base P Q u v 0 t := by
  let inv := fun j t => Changes base loopWork s t ∧ Running base P Q u v j t
  refine countLoop_ok (Inv:=inv) (n:=128) (by decide) (fun j t h1 h256 ⟨k,hi⟩ => ?_)
    (fun _ h => h) (by decide) ⟨⟨rfl,rfl,rfl,rfl,Unch.refl _ _ _⟩,h⟩
  exact WP.mono (step_ok hc hC hP hQ h1 h256 hi) fun u ⟨k',hi'⟩ => ⟨⟨k.trans k',hi'⟩,hi'.counter⟩
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.Secp256k1.Joint.Build`, which only this module used -/

section

/-! Building the joint digit-pair table in a loop over its entries, with one complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

theorem indexFrom_ok (s : State) {k j : Nat} (hk : k < 2^16) (hj : j ≤ k)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (indexFrom k)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (k-j) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [indexFrom,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 16*0 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h19,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero,BitVec.shiftLeft_zero,BitVec.toNat_sub,BitVec.toNat_setWidth,
      BitVec.toNat_ofNat,show Size.x.bits = 64 from rfl]
    omega_using [hk, hj]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

/-- What `rowTest` leaves in `x2`. -/
def rowVal (j : Nat) : BitVec 64 := (BitVec.ofNat 64 j &&& 3) ^^^ 3

theorem rowVal_zero : ∀ j < 15, (rowVal j = 0) = ((15-j) % 4 = 0) := by decide

theorem rowTest_ok (s : State) {j : Nat} (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block rowTest) s fun t => t.gpr .x2 = rowVal j ∧ Keeps [.x2,.x5] s t := by
  apply WP.of_runBlock
  simp only [rowTest,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 16*0 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h19,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

/-- A pointer into the working space the copies store through. -/
theorem dest_ptr {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size)
    (ha : a ≤ size) (hr : s.gpr .x16 = off base a) :
    PtrW s .x16 (off base a) (size-a) where
  reg := hr
  st d hd := by
    rw [VG.Offset.add_add]
    exact ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  enc := by have := hs.enc; omega_using [this]
  nowrap := by
    have := hs.nowrap
    unfold off
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega_using [this]

theorem stR_out {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size) (ha : a ≤ size)
    (hr : s.gpr .x16 = off base a) {d : Nat} (hd : a + d + 8 ≤ size) (hd8 : d % 8 = 0) (t : Reg) :
    WP isa (.block [.str .x t .x16 d]) s fun s' =>
      s'.mem = s.mem.writeW (off base (a+d)) (s.gpr t) ∧ KeepRegs [] s s' :=
  WP.mono (stR_ok (dest_ptr hs ha hr) (d:=d) (by omega_using [hd]) hd8 t) fun s' e => by
    subst e
    refine ⟨?_,⟨fun _ _ => rfl,rfl,rfl,rfl⟩⟩
    show s.mem.writeW (off (off base a) d) _ = _
    unfold off
    rw [VG.Offset.add_add]

/-- The destination is above or wholly below the source. -/
theorem copyTo_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {a dst src : Nat},
    Scr s base size → s.gpr .x16 = off base a →
    a + dst + 8*n ≤ size → src + 8*n ≤ size → dst % 8 = 0 → src % 8 = 0 →
    (a + dst + 8*n ≤ src ∨ src + 8*n ≤ a + dst) →
    WP isa (.block (copyTo n dst src)) s fun t =>
      wordsVal t.mem base (a+dst) n = wordsVal s.mem base src n ∧
      KeepRegs [.x4] s t ∧ Outside base (a+dst) (8*n) s.mem t.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1, s, base, a, dst, src, hs, hr, hd, hsrc, hd8, hs8, hsep => by
    have hn := hs.nowrap
    rw [copyTo,WP.block_append_iff,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ld_ok hs (d:=src) (by omega_using [hsrc]) hs8 .x4) fun s₀ ⟨e₀,k₀,_⟩ => ?_
    obtain hs₀ := hs.of_keeps k₀ (by decide)
    obtain hr₀ : s₀.gpr .x16 = off base a := (k₀.gpr .x16 (by decide)).trans hr
    refine WP.mono (stR_out hs₀ (by omega_using [hd] : a ≤ size) hr₀ (d:=dst) (by omega_using [hd]) hd8 .x4)
      fun s₁ ⟨m₁,k₁⟩ => ?_
    rw [e₀,k₀.mem] at m₁
    obtain k₀₁ : KeepRegs [.x4] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    obtain hs₁ := hs.of_keepRegs k₀₁ (by decide)
    obtain O₁ : Outside base (a+dst) 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega_using [hd, hn])
    obtain hr₁ : s₁.gpr .x16 = off base a := (k₀₁.gpr .x16 (by decide)).trans hr
    obtain e₁ : wordsVal s₁.mem base (src+8) n = wordsVal s.mem base (src+8) n :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [hsrc, hn])
    refine WP.mono (copyTo_ok n hs₁ hr₁ (dst:=dst+8) (src:=src+8)
      (by omega_using [hd]) (by omega_using [hsrc]) (by omega_using [hd8]) (by omega_using [hs8]) (by omega_using [hsep])) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
    rw [show a+(dst+8)=a+dst+8 by omega_using []] at e₂ O₂
    refine ⟨?_,k₀₁.trans k₂,fun x hx => by rw [O₂ x (by omega_using [hx]),O₁ x (by omega_using [hx])]⟩
    rw [wordsVal,O₂.word (by omega_using []) (by omega_using [hd, hn]),m₁,word_writeW_self,e₂,e₁,wordsVal]

/-- Entry `d` of the table into the result, as `fetch_ok` into the entry. -/
theorem load_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    WP isa (.block (fetchHead ++ copyFrom 4 resultPt.x 0 ++ copyFrom 4 resultPt.y 32 ++
        copyFrom 4 resultPt.z 64)) s fun t =>
      Changes base resultWork s t ∧ PointAt base t resultPt P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  obtain htab := table_coord_bounds h1 h15
  obtain ha : (tablePt d).x+96 ≤ 8192 := by
    obtain hb := (htab (tablePt d).z (by simp)).2.1
    change _+32 ≤ 6720 at hb
    dsimp only [tablePt] at hb ⊢; omega_using [hb]
  obtain hsep : ∀ e ∈ coordinates resultPt,e+32 ≤ (tablePt d).x := by
    obtain hh : ∀ e ∈ coordinates resultPt,e+32 ≤ tableAt := by decide
    intro e he; exact Nat.le_trans (hh e he) (htab _ (by simp)).1
  obtain sepX := hsep resultPt.x (by decide)
  obtain sepY := hsep resultPt.y (by decide)
  obtain sepZ := hsep resultPt.z (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs h1 h15 h2) fun s₁ ⟨p₁,k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₁ p₁ (a:=(tablePt d).x) (src:=0) (dst:=resultPt.x)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by omega_using [sepX])))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₂ p₂ (a:=(tablePt d).x) (src:=32) (dst:=resultPt.y)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by omega_using [sepY])))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok 4 hs₃ p₃ (a:=(tablePt d).x) (src:=64) (dst:=resultPt.z)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by omega_using [sepZ])))
    fun t ⟨z,k₄,u₄⟩ => ?_
  obtain dx : resultPt.x + 32 ≤ resultPt.y := by decide
  obtain dy : resultPt.y + 32 ≤ resultPt.z := by decide
  obtain e_x : num base t resultPt.x = num base s (tablePt d).x := by
    change wordsVal t.mem base resultPt.x 4 = wordsVal s.mem base (tablePt d).x 4
    rw [u₄.wordsVal (by omega_using [dx, dy]) (by omega_using [ha, sepX]),
      u₃.wordsVal (by omega_using [dx]) (by omega_using [ha, sepX]),x,k₁.mem]
    rfl
  obtain e_y : num base t resultPt.y = num base s (tablePt d).y := by
    change wordsVal t.mem base resultPt.y 4 = wordsVal s.mem base (tablePt d).y 4
    rw [u₄.wordsVal (by omega_using [dy]) (by omega_using [ha, sepY]),y]
    rw [u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  obtain e_z : num base t resultPt.z = num base s (tablePt d).z := by
    change wordsVal t.mem base resultPt.z 4 = wordsVal s.mem base (tablePt d).z 4
    rw [z,u₃.wordsVal (Or.inr (by omega_using [sepY])) (by omega_using [ha]),
      u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  obtain kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))
  obtain u : Unch base resultWork s.mem t.mem := by
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
    obtain ey := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_y
    obtain ez := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_z
    change val base t resultPt.x = val base s (tablePt d).x at ex
    change val base t resultPt.y = val base s (tablePt d).y at ey
    change val base t resultPt.z = val base s (tablePt d).z at ez
    rw [ex,ey,ez]; exact hp.2

/-- The result into entry `15 - j` of the table. -/
theorem storeEntry_ok {base : Addr} {s : State} (hs : Scr s base 8192) {j : Nat} (hj : j < 15)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) {P : VG.Spec.Weierstrass.Point C}
    (hp : PointAt base s resultPt P) :
    WP isa (.block storeEntry) s fun t =>
      Changes base ((coordinates (tablePt (15-j))).map (·,32)) s t ∧
      PointAt base t (tablePt (15-j)) P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  obtain h1 : 1 ≤ 15-j := by omega_using [hj]
  obtain h15 : 15-j ≤ 15 := by omega_using []
  obtain htab := table_coord_bounds h1 h15
  obtain hlo := (htab (tablePt (15-j)).x (by simp)).1
  obtain ha : (tablePt (15-j)).x+96 ≤ 8192 := by
    obtain hb := (htab (tablePt (15-j)).z (by simp)).2.1
    change _+32 ≤ 6720 at hb
    dsimp only [tablePt] at hb ⊢; omega_using [hb]
  have ey : (tablePt (15-j)).y = (tablePt (15-j)).x + 32 := rfl
  have ez : (tablePt (15-j)).z = (tablePt (15-j)).x + 64 := rfl
  obtain hr : ∀ e ∈ coordinates resultPt,e+32 ≤ tableAt := by decide
  obtain sepX := hr resultPt.x (by decide)
  obtain sepY := hr resultPt.y (by decide)
  obtain sepZ := hr resultPt.z (by decide)
  have hta : tableAt = 5280 := rfl
  simp only [storeEntry,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (indexFrom_ok s (k:=15) (by decide) (by omega_using [hj]) h19) fun s₀ ⟨v₀,k₀⟩ => ?_
  obtain hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs₀ h1 h15 v₀) fun s₁ ⟨p₁,k₁⟩ => ?_
  obtain hs₁ := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyTo_ok 4 hs₁ p₁ (a:=(tablePt (15-j)).x) (dst:=0) (src:=resultPt.x)
    (by omega_using [ha]) (by decide) (by decide) (by decide) (Or.inr (by omega_using [hlo, sepX])))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyTo_ok 4 hs₂ p₂ (a:=(tablePt (15-j)).x) (dst:=32) (src:=resultPt.y)
    (by omega_using [ha]) (by decide) (by decide) (by decide) (Or.inr (by omega_using [hlo, sepY])))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyTo_ok 4 hs₃ p₃ (a:=(tablePt (15-j)).x) (dst:=64) (src:=resultPt.z)
    (by omega_using [ha]) (by decide) (by decide) (by decide) (Or.inr (by omega_using [hlo, sepZ])))
    fun t ⟨z,k₄,u₄⟩ => ?_
  obtain m₁ : s₁.mem = s.mem := k₁.mem.trans k₀.mem
  obtain e_x : num base t (tablePt (15-j)).x = num base s resultPt.x := by
    change wordsVal t.mem base (tablePt (15-j)).x 4 = wordsVal s.mem base resultPt.x 4
    rw [u₄.wordsVal (by omega_using []) (by omega_using [ha]),u₃.wordsVal (by omega_using []) (by omega_using [ha])]
    rw [show (tablePt (15-j)).x = (tablePt (15-j)).x + 0 by omega_using [],x,m₁]
  obtain e_y : num base t (tablePt (15-j)).y = num base s resultPt.y := by
    change wordsVal t.mem base (tablePt (15-j)).y 4 = wordsVal s.mem base resultPt.y 4
    rw [ey,u₄.wordsVal (by omega_using []) (by omega_using [ha]),y,
      u₂.wordsVal (by omega_using [hlo, sepY]) (by omega_using [sepY, hta]),m₁]
  obtain e_z : num base t (tablePt (15-j)).z = num base s resultPt.z := by
    change wordsVal t.mem base (tablePt (15-j)).z 4 = wordsVal s.mem base resultPt.z 4
    rw [ez,z,u₃.wordsVal (by omega_using [hlo, sepZ]) (by omega_using [sepZ, hta]),
      u₂.wordsVal (by omega_using [hlo, sepZ]) (by omega_using [sepZ, hta]),m₁]
  obtain kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    (((((Keeps.regs k₀).mono (by decide)).trans ((Keeps.regs k₁).mono (by decide))).trans
      (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))
  obtain u : Unch base ((coordinates (tablePt (15-j))).map (·,32)) s.mem t.mem := by
    rw [←m₁]
    refine (u₂.unch.trans (u₃.unch.trans u₄.unch)).mono ?_
    intro w hw
    simp only [List.mem_append,List.mem_singleton] at hw
    simp only [coordinates,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,ey,ez]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,u⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro e he
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [e_x]; exact hp.1 _ (by simp)
    · rw [e_y]; exact hp.1 _ (by simp)
    · rw [e_z]; exact hp.1 _ (by simp)
  · have ex := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_x
    obtain ey' := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_y
    obtain ez' := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_z
    change val base t (tablePt (15-j)).x = val base s resultPt.x at ex
    change val base t (tablePt (15-j)).y = val base s resultPt.y at ey'
    change val base t (tablePt (15-j)).z = val base s resultPt.z at ez'
    rw [ex,ey',ez']; exact hp.2

/-- The entry numbered `k - j` into the result, or the point at infinity for number zero. -/
theorem previousEntry_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (hc : BaseCfgOk cfg) (hC : Law C) {k j : Nat} (hk : k ≤ 15) (hj : j ≤ k)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) {A : VG.Spec.Weierstrass.Point C}
    (hA : k - j = 0 → A = .infinity) (ht : k - j ≠ 0 → PointAt base s (tablePt (k-j)) A) :
    WP isa (previousEntry k) s fun t =>
      Changes base resultWork s t ∧ PointAt base t resultPt A ∧ t.gpr .x19 = s.gpr .x19 := by
  rw [previousEntry]
  refine WP.seq (WP.mono (indexFrom_ok s (k:=k) (by omega_using [hk]) hj h19) fun s₁ ⟨v₁,k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain W₁ : Changes base resultWork s s₁ := Changes.of_keeps k₁ (by decide)
  obtain c₁ : s₁.gpr .x19 = s.gpr .x19 := k₁.gpr _ (by decide)
  refine WP.ite (decide (k-j=0)) (zero_test (by omega_using [hk]) v₁) (fun hz => ?_) (fun hn => ?_)
  · have hz' : k-j=0 := of_decide_eq_true hz
    rw [hA hz']
    exact WP.mono (infinity_ok hs₁ hc hC) fun t ⟨k₂,R₂,c₂⟩ => ⟨W₁.trans k₂,R₂,c₂.trans c₁⟩
  · have hn' : k-j≠0 := of_decide_eq_false hn
    obtain hp := (ht hn').of_mem k₁.mem
    exact WP.mono (load_ok hs₁ (by omega_using [hn']) (by omega_using [hk]) v₁ hp) fun t ⟨k₂,R₂,c₂⟩ =>
      ⟨W₁.trans k₂,R₂,c₂.trans c₁⟩

/-- The source `G` or `Q` into the addition's entry slots. -/
theorem affine_ok {base : Addr} {P Q : Point C} {s : State} (hi : Inputs base P Q s) (b : Bool) :
    WP isa (.block (if b then affineEntry PX PY else affineEntry GX GY)) s fun t =>
      Changes base entryWork s t ∧ PointAt base t entry (if b then Q else P) ∧
      t.gpr .x19 = s.gpr .x19 := by
  cases b
  · change WP isa (.block (copyPt 4 entry gSource)) s _
    exact WP.mono (copy_point hi.scr entry_from_generator hi.generator) fun t ⟨k,p,c⟩ => ⟨k,p,c⟩
  · change WP isa (.block (copyPt 4 entry qSource)) s _
    exact WP.mono (copy_point hi.scr entry_from_peer hi.peer) fun t ⟨k,p,c⟩ => ⟨k,p,c⟩

/-- Entry `d = 16 - j` of the table, from the counter `j`. -/
theorem buildStep_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    {j : Nat} (h1 : 1 ≤ j) (h15 : j ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (15-j) s) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa buildStep s fun t =>
      (Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q (15-(j-1)) t) ∧
      t.gpr .x19 = BitVec.ofNat 64 (j-1) := by
  rw [buildStep,←List.singleton_append]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (decCounter_ok s h1 (by omega_using [h15]) h19) fun s₀ ⟨c₀,k₀⟩ => ?_
  refine WP.mono (rowTest_ok s₀ c₀) fun s₁ ⟨v₁,k₁⟩ => ?_
  obtain k₀₁ : Keeps [.x19,.x2,.x5] s s₁ := (k₀.mono (by decide)).trans (k₁.mono (by decide))
  obtain W₁ : Changes base arithmeticWork s s₁ := Changes.of_keeps k₀₁ (by decide)
  obtain I₁ := hi.unch W₁
  obtain c₁ : s₁.gpr .x19 = BitVec.ofNat 64 (j-1) := (k₁.gpr _ (by decide)).trans c₀
  obtain T₁ : Table base P Q (15-j) s₁ := fun e he1 he => (ht e he1 he).of_mem k₀₁.mem
  let d := 15-(j-1)
  obtain hd1 : 1 ≤ d := by omega
  obtain hd15 : d ≤ 15 := by omega_using []
  let A := pair P Q ((previous d)%4) ((previous d)/4)
  obtain hpl := previous_lt hd1
  -- the source of the previous entry and `G` or `Q`, for either row case
  obtain src : ∀ (b : Bool), b = decide (d%4=0) →
      WP isa (.seq (previousEntry (if b then 11 else 14))
        (.block (if b then affineEntry PX PY else affineEntry GX GY))) s₁ fun t =>
        Changes base loopWork s₁ t ∧ Inputs base P Q t ∧ PointAt base t resultPt A ∧
        PointAt base t entry (if d%4=0 then Q else P) ∧ t.gpr .x19 = s₁.gpr .x19 := by
    intro b hb
    obtain hkj : (if b then 11 else 14) - (j-1) = previous d := by
      unfold previous
      by_cases hz : d%4=0
      · rw [decide_eq_true hz] at hb; subst hb
        rw [ite_eq_left hz]; simp only [ite_true]; omega_using []
      · rw [decide_eq_false hz] at hb; subst hb
        rw [ite_eq_right hz]; simp only [Bool.false_eq_true,ite_false]; omega_using []
    obtain hk15 : (if b then 11 else 14) ≤ 15 := by cases b <;> decide
    obtain hjk : j-1 ≤ (if b then 11 else 14) := by
      cases b
      · simp only [Bool.false_eq_true,ite_false]; omega_using [h15]
      · simp only [ite_true]
        obtain hz : d%4=0 := of_decide_eq_true hb.symm
        omega_using [h15, hz]
    refine WP.seq (WP.mono (previousEntry_ok I₁.scr hc hC hk15 hjk c₁ (A:=A)
      (fun h0 => by dsimp only [A]; rw [hkj] at h0; rw [h0]; exact pair_zero P Q)
      (fun h0 => by
        rw [hkj] at h0 ⊢
        exact T₁ _ (by omega_using [h0]) (by omega_using [hpl])))
      fun s₂ ⟨k₂,R₂,c₂⟩ => ?_)
    obtain W₂ := k₂.mono resultWork_sub
    obtain I₂ := I₁.unch (W₂.mono loopWork_sub)
    obtain e : (if b then Q else P) = (if d%4=0 then Q else P) := by
      by_cases hz : d%4=0
      · rw [decide_eq_true hz] at hb; subst hb; simp only [ite_true,ite_eq_left hz]
      · rw [decide_eq_false hz] at hb; subst hb; simp only [Bool.false_eq_true,ite_false,ite_eq_right hz]
    refine WP.mono (affine_ok I₂ b) fun t ⟨k₃,E₃,c₃⟩ => ?_
    obtain W₃ := W₂.trans (k₃.mono entryWork_sub)
    exact ⟨W₃,I₁.unch (W₃.mono loopWork_sub),k₃.point I₂.scr R₂ (by decide) (by decide),e ▸ E₃,
      c₃.trans c₂⟩
  obtain hrow : isa.eval (.zero .x .x2) s₁ = some (decide (d%4=0)) := by
    change some (s₁.read .x .x2 == 0) = _
    rw [read_x,v₁]
    obtain hz := rowVal_zero (j-1) (by omega_using [h15])
    by_cases h : (15-(j-1))%4=0
    · rw [decide_eq_true h,beq_iff_eq.mpr (hz ▸ h)]
    · rw [decide_eq_false h]
      exact congrArg some (beq_eq_false_iff_ne.mpr fun e => h (hz ▸ e))
  obtain cont : ∀ s₂, (Changes base loopWork s₁ s₂ ∧ Inputs base P Q s₂ ∧ PointAt base s₂ resultPt A ∧
      PointAt base s₂ entry (if d%4=0 then Q else P) ∧ s₂.gpr .x19 = s₁.gpr .x19) →
      WP isa (.seq addPoints (.block storeEntry)) s₂ fun t =>
        (Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q (15-(j-1)) t) ∧
        t.gpr .x19 = BitVec.ofNat 64 (j-1) := by
    intro s₂ ⟨k₂,I₂,R₂,E₂,c₂⟩
    obtain he : onCurve C (if d%4=0 then Q else P)=true := by
      by_cases hz : d%4=0
      · rw [ite_eq_left hz]; exact hQ
      · rw [ite_eq_right hz]; exact hP
    obtain hA : onCurve C A=true := pair_curve hC hP hQ _ _
    refine WP.seq (WP.mono (sum_points hc hC I₂.scr I₂.mod I₂.a I₂.b I₂.a_lt I₂.b_lt he hA E₂ R₂)
      fun s₃ ⟨k₃,R₃,c₃⟩ => ?_)
    obtain W₃ := k₂.trans (k₃.mono addWork_sub)
    obtain I₃ := I₁.unch (W₃.mono loopWork_sub)
    obtain c₃' : s₃.gpr .x19 = BitVec.ofNat 64 (j-1) := c₃.trans (c₂.trans c₁)
    obtain e : add (if d%4=0 then Q else P) A = pair P Q (d%4) (d/4) := table_step hC hP hQ hd1
    rw [e] at R₃
    refine WP.mono (storeEntry_ok I₃.scr (j:=j-1) (by omega_using [h15]) c₃' R₃) fun t ⟨k₄,R₄,c₄⟩ => ?_
    obtain W₄ := (W₃.mono loopWork_sub).trans (k₄.cover (tableWork_cover hd1 hd15))
    obtain W := W₁.trans W₄
    refine ⟨⟨W,hi.unch W,fun i hi1 hid => ?_⟩,c₄.trans c₃'⟩
    by_cases heq : i=d
    · subst i; exact R₄
    · have hi' : i < d := by omega_using [hid, heq]
      obtain old := W₃.table I₁.scr hi1 (by omega_using [hid]) (T₁ i hi1 (by omega_using [hid, heq]))
      exact k₄.point I₃.scr old
        (fun x hx => Nat.le_trans (table_coord_bounds hi1 (by omega_using [hid]) x hx).2.1 (by decide))
        (earlier_table_apart hi1 hi')
  exact WP.seq (WP.ite (decide (d%4=0)) hrow
    (fun hb => WP.mono (src true hb.symm) cont)
    (fun hb => WP.mono (src false hb.symm) cont))

theorem build_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hi : Inputs base P Q s) :
    WP isa build s fun t =>
      Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q 15 t := by
  rw [build]
  refine WP.seq (WP.mono (setCounter_ok s (j:=15) (by decide)) fun s₁ ⟨c₁,k₁⟩ => ?_)
  obtain W₁ : Changes base arithmeticWork s s₁ := Changes.of_keeps k₁ (by decide)
  let inv := fun j t => (Changes base arithmeticWork s t ∧ Inputs base P Q t ∧
    Table base P Q (15-j) t) ∧ t.gpr .x19 = BitVec.ofNat 64 j
  refine countLoop_ok (Inv:=inv) (n:=15) (by decide) (fun j t h1 h15 ⟨⟨k,I,T⟩,c⟩ => ?_)
    (fun t ⟨⟨k,I,T⟩,_⟩ => ⟨k,I,T⟩) (by decide)
    ⟨⟨W₁,hi.unch W₁,fun _ h1 h0 => False.elim (by omega_using [h1, h0])⟩,c₁⟩
  exact WP.mono (buildStep_ok hc hC hP hQ h1 h15 I T c) fun u ⟨⟨k',I',T'⟩,c'⟩ =>
    ⟨⟨⟨k.trans k',I',T'⟩,c'⟩,c'⟩

end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint

end

end

/-! The joint multiplier feeds the unchanged complete ECDSA final check. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/Secp256k1/Joint/Prepare.lean`, which only this module imported.
section

/-! Preparing the two bit tables and the general complete-addition coefficient. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

abbrev prepWork : List (Nat × Nat) := [(bitsU,512),(cfg.sl EXPP,32)]

theorem generator_point {base : Addr} {s : State} {g : Reg → BitVec 64}
    (hc : BaseCfgOk cfg) (hC : Law C) (hf : Fixed cfg base g s.mem) :
    PointAt base s gSource (G C) := by
  obtain hp : 0 < cfg.C.p := by have := hc.p_ge; omega_using [this]
  have hm (x : Nat) : cfg.mont x < C.p := Nat.mod_lt _ hp
  obtain e1 : num base s (cfg.sl ONEP)=cfg.mont 1 := by
    rw [num,hf.onep]; simp only [Cfg.mont,Cfg.R,Nat.one_mul]
  refine ⟨?_,?_⟩
  · intro x hx
    simp only [coordinates,gSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [num,hf.gx]; exact hm _
    · rw [num,hf.gy]; exact hm _
    · rw [e1]; exact hm _
  · have ex : val base s gSource.x=Fin.ofNat C.p C.gx :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) hf.gx).trans (toM_cmont hc _)
    obtain ey : val base s gSource.y=Fin.ofNat C.p C.gy :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) hf.gy).trans (toM_cmont hc _)
    obtain ez : val base s gSource.z=1 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e1).trans (toM_cmont hc 1)
    rw [ex,ey,ez]
    exact rep_affine' hC _ _

theorem prepare_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa prepare s fun t =>
      Changes base prepWork s t ∧ Inputs base (G C) P t ∧
      Bits base (sv cfg base s U) (sv cfg base s V) t := by
  have hn8 : cfg.n=4 := rfl
  obtain boundV : cfg.sl V+32 ≤ 8192 := by decide
  have hs := hM.scr
  have hn := hs.nowrap
  obtain hm0 : 0 < cfg.C.p := by have := hc.p_ge; omega_using [this]
  have hm (x : Nat) : cfg.mont x < C.p := Nat.mod_lt _ hm0
  obtain hbconst : cfg.mont (3*cfg.C.b) < 2^(64*cfg.n) := Nat.lt_trans (hm _) hc.p_lt
  rw [prepare]
  refine WP.seq (WP.mono (bits_ok hs (n:=4) (src:=cfg.sl U) (dst:=bitsU)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)))
    fun s₁ ⟨b₁,k₁,u₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain v₁ : wordsVal s₁.mem base (cfg.sl V) 4=wordsVal s.mem base (cfg.sl V) 4 :=
    u₁.wordsVal (by decide) (by omega_using [boundV])
  refine WP.seq (WP.mono (bits_ok hs₁ (n:=4) (src:=cfg.sl V) (dst:=bitsV)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)))
    fun s₂ ⟨b₂,k₂,u₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n:=cfg.n) (o:=cfg.sl EXPP) (by decide) (by decide) hbconst)
    fun t ⟨b₃,k₃,u₃⟩ => ?_
  obtain W : Changes base prepWork s t := by
    obtain kt := (k₁.trans k₂).trans (k₃.mono (by decide))
    refine ⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,?_⟩
    exact (u₁.unch.trans (u₂.unch.trans u₃.unch)).cover (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨(bitsU,512),by simp,by decide,by decide⟩
      · exact ⟨(bitsU,512),by simp,by decide,by decide⟩
      · exact ⟨(cfg.sl EXPP,32),by simp,by decide,by decide⟩)
  obtain F := hM.fixed.unch hc.n10 hn (by unfold FixedOk prepWork; decide) W.mem
  obtain hqp : PointAt base s qSource P := by
    refine ⟨?_,hrep⟩
    intro x hx
    simp only [coordinates,qSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hM.px_lt
    · exact hM.py_lt
    · rw [num,hM.fixed.onep]; exact Nat.mod_lt _ hm0
  obtain I : Inputs base (G C) P t := by
    refine ⟨W.scr hs,modP_of hc F.mp,?_,?_,?_,?_,generator_point hc hC F,
      W.point hs hqp (by decide) (by decide)⟩
    · rw [num,F.ap]; exact hm _
    · rw [num,b₃]; exact hm _
    · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) F.ap).trans (toM_cmont hc _)
    · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) b₃).trans (toM_cmont hc _)
  refine ⟨W,I,?_,?_⟩
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ 448+32 ≤ 2944+j; omega_using [])
        (by change 2944+j < 2^64; omega_using [hj]),
      u₂.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change 2944+j+1 ≤ 3200 ∨ _; omega_using [hj])
        (by change 2944+j < 2^64; omega_using [hj]),b₁ j hj]
    rfl
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ 448+32 ≤ 3200+j; omega_using [])
        (by change 3200+j < 2^64; omega_using [hj]),b₂ j hj,v₁]
    rfl
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V RM')
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

theorem arithmeticWork_sub : ∀ w ∈ arithmeticWork,w ∈ work := by decide
theorem prepWork_sub : ∀ w ∈ prepWork,w ∈ work := by decide

theorem setup_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa setup s fun t => Changes base work s t ∧
      Running base (G C) P (sv cfg base s U) (sv cfg base s V) 128 t := by
  rw [setup]
  refine WP.seq (WP.mono (prepare_ok hc hC hM hrep) fun s₁ ⟨k₁,I₁,B₁⟩ => ?_)
  refine WP.seq (WP.mono (build_ok hc hC hc.onG hP I₁) fun s₂ ⟨k₂,I₂,T₂⟩ => ?_)
  obtain B₂ := k₂.bits B₁
  rw [WP.block_append_iff]
  refine WP.mono (infinity_ok I₂.scr hc hC) fun s₃ ⟨k₃,R₃,_⟩ => ?_
  obtain W₃ := k₃.mono resultWork_sub
  obtain I₃ := I₂.unch (W₃.mono loopWork_sub)
  obtain B₃ := (W₃.mono loopWork_sub).bits B₂
  obtain T₃ := T₂.of_changes I₂.scr W₃
  refine WP.mono (setCounter_ok s₃ (j:=128) (by decide)) fun s₄ ⟨c₄,k₄⟩ => ?_
  obtain W₄ : Changes base loopWork s₃ s₄ := Changes.of_keeps k₄ (by decide)
  obtain I₄ := I₃.unch (W₄.mono loopWork_sub)
  obtain B₄ := (W₄.mono loopWork_sub).bits B₃
  obtain T₄ := T₃.of_changes I₃.scr W₄
  obtain R₄ := R₃.of_mem k₄.mem
  obtain hu := Nat.lt_trans hM.u_lt hc.n_lt
  obtain hv := Nat.lt_trans hM.v_lt hc.n_lt
  obtain hstart := at_top (G C) P (n:=cfg.n) hu hv
  rw [show 32*cfg.n=128 from rfl] at hstart
  rw [←hstart] at R₄
  exact ⟨(((k₁.mono prepWork_sub).trans (k₂.mono arithmeticWork_sub)).trans
    ((W₃.mono loopWork_sub).mono arithmeticWork_sub)).trans
    ((W₄.mono loopWork_sub).mono arithmeticWork_sub),⟨I₄,B₄,T₄,c₄,R₄⟩⟩

theorem points_raw {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t =>
      Changes base work s t ∧ PointAt base t resultPt
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) := by
  rw [points]
  refine WP.seq (WP.mono (setup_ok hc hC hP hM hrep) fun s₄ ⟨k₄,R₄⟩ => ?_)
  refine WP.mono (loop_ok hc hC hc.onG hP R₄) fun t ⟨k₅,h₅⟩ => ?_
  obtain W := k₄.trans ((k₅.mono loopWork_sub).mono arithmeticWork_sub)
  have p := h₅.point
  rw [at_zero] at p
  exact ⟨W,p⟩

theorem final_state {base : Addr} {s₀ s t : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hM : Mid cfg s₀ base g s) (h : Changes base work s t)
    (hp : PointAt base t resultPt P) : FinalState cfg s₀ base g t := by
  have hn := hM.scr.nowrap
  obtain flagBound : cfg.sl FLAG+8 ≤ 8192 := by decide
  have hn8 : cfg.n=4 := rfl
  have same (i : Nat) (hle : cfg.sl i+32 ≤ 8192)
      (hap : ∀ w ∈ work,cfg.sl i+32 ≤ w.1 ∨ w.1+w.2 ≤ cfg.sl i) :
      sv cfg base t i=sv cfg base s i :=
    h.mem.wordsVal hap (by omega_using [hn8, hle])
  obtain r := same RM' (by decide) (by decide)
  obtain k := same K (by decide) (by decide)
  refine ⟨h.scr hM.scr,h.wr.trans hM.wr,h.rd.trans hM.rd,
    hM.fixed.unch hc.n10 hn (by unfold FixedOk work loopWork addWork entryWork; decide) h.mem,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [h.mem.word (by decide) (by omega_using [flagBound])]
    exact hM.flag
  · rw [r]; exact hM.rm_lt
  · rw [r]; exact hM.rm
  · exact hp.1 _ (by decide)
  · exact (hM.unch.trans h.mem).cover (by
      intro w hw
      refine ⟨(0,8192),by simp,by omega_using [],?_⟩
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
      · have hd : ∀ w ∈ work,w.1+w.2 ≤ 8192 := by decide
        exact hd w hw)
  · exact k.trans hM.k
  · exact hp.1 _ (by decide)

theorem points_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t => FinalState cfg s₀ base g t ∧
      Rep C (val base t resultPt.x) (val base t resultPt.y) (val base t resultPt.z)
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) :=
  WP.mono (points_raw hc hC hP hM hrep) fun _ ⟨W,p⟩ => ⟨final_state hc hM W p,p.2⟩
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
