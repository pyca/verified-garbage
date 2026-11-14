module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Table
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.State
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.TableLayout
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Digit
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Fetch`, which only this module used -/

section

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Copy`, which only this module used -/

section

/-! Copies through the joint table's public entry pointer. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

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
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end


/-! Public lookup of a nonzero digit pair, with all pointer bounds checked. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

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
    show (144 : BitVec 16).setWidth 64 = BitVec.ofNat 64 144 from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change base+BitVec.ofNat 64 5280+(BitVec.ofNat 64 d-1)*BitVec.ofNat 64 144 = off base (tablePt d).x
    rw [hsub,←BitVec.ofNat_mul]
    change base+BitVec.ofNat 64 5280+BitVec.ofNat 64 ((d-1)*144)=
      base+BitVec.ofNat 64 (5280+144*(d-1))
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
  have ex_bound : entry.x+48 ≤ 8192 := by decide
  have ey_bound : entry.y+48 ≤ 8192 := by decide
  have htab := table_coord_bounds h1 h15
  have ha : (tablePt d).x+144 ≤ 8192 := by
    have hb := (htab (tablePt d).z (by simp)).2.1
    change _+48 ≤ 7440 at hb
    dsimp only [tablePt] at hb ⊢; omega_using [hb]
  have hab : (tablePt d).x ≤ 8192 := by omega_using [ha]
  have hsep : ∀ e ∈ coordinates entry,e+48 ≤ (tablePt d).x := by
    have hh : ∀ e ∈ coordinates entry,e+48 ≤ tableAt := by decide
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
  refine WP.mono (copyFrom_ok 6 hs₁ p₁ (a:=(tablePt d).x) (src:=0) (dst:=entry.x)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by simpa using hsep _ (by simp))))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 6 hs₂ p₂ (a:=(tablePt d).x) (src:=48) (dst:=entry.y)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by omega_using [sepY])))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok 6 hs₃ p₃ (a:=(tablePt d).x) (src:=96) (dst:=entry.z)
    (by decide) (by omega_using [ha]) (by decide) (by decide) (Or.inl (by omega_using [sepZ])))
    fun t ⟨z,k₄,u₄⟩ => ?_
  have e_x : num base t entry.x = num base s (tablePt d).x := by
    change wordsVal t.mem base entry.x 6 = wordsVal s.mem base (tablePt d).x 6
    rw [u₄.wordsVal (by decide) (by omega_using [ex_bound]),
      u₃.wordsVal (by decide) (by omega_using [ex_bound]),x,k₁.mem]
    rfl
  have e_y : num base t entry.y = num base s (tablePt d).y := by
    change wordsVal t.mem base entry.y 6 = wordsVal s.mem base (tablePt d).y 6
    rw [u₄.wordsVal (by decide) (by omega_using [ey_bound]),y]
    rw [u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  have e_z : num base t entry.z = num base s (tablePt d).z := by
    change wordsVal t.mem base entry.z 6 = wordsVal s.mem base (tablePt d).z 6
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
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end


/-! A public digit addition, including the zero-pair case. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

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
    (ht : Table base P Q 15 s) (hp : PointAt base s resultPt A) (hj : j < 192)
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
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
