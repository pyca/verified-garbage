module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.TableLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Fetch
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Copy
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.LoopOps
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Table

/-! Building the joint digit-pair table in a loop over its entries, with one complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.P192.Joint

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
    omega
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
  enc := by have := hs.enc; omega
  nowrap := by
    have := hs.nowrap
    unfold off
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega

theorem stR_out {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size) (ha : a ≤ size)
    (hr : s.gpr .x16 = off base a) {d : Nat} (hd : a + d + 8 ≤ size) (hd8 : d % 8 = 0) (t : Reg) :
    WP isa (.block [.str .x t .x16 d]) s fun s' =>
      s'.mem = s.mem.writeW (off base (a+d)) (s.gpr t) ∧ KeepRegs [] s s' :=
  WP.mono (stR_ok (dest_ptr hs ha hr) (d:=d) (by omega) hd8 t) fun s' e => by
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
    refine WP.mono (ld_ok hs (d:=src) (by omega) hs8 .x4) fun s₀ ⟨e₀,k₀,_⟩ => ?_
    have hs₀ := hs.of_keeps k₀ (by decide)
    have hr₀ : s₀.gpr .x16 = off base a := (k₀.gpr .x16 (by decide)).trans hr
    refine WP.mono (stR_out hs₀ (by omega : a ≤ size) hr₀ (d:=dst) (by omega) hd8 .x4)
      fun s₁ ⟨m₁,k₁⟩ => ?_
    rw [e₀,k₀.mem] at m₁
    have k₀₁ : KeepRegs [.x4] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    have hs₁ := hs.of_keepRegs k₀₁ (by decide)
    have O₁ : Outside base (a+dst) 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega)
    have hr₁ : s₁.gpr .x16 = off base a := (k₀₁.gpr .x16 (by decide)).trans hr
    have e₁ : wordsVal s₁.mem base (src+8) n = wordsVal s.mem base (src+8) n :=
      O₁.wordsVal (by omega) (by omega)
    refine WP.mono (copyTo_ok n hs₁ hr₁ (dst:=dst+8) (src:=src+8)
      (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
    rw [show a+(dst+8)=a+dst+8 by omega] at e₂ O₂
    refine ⟨?_,k₀₁.trans k₂,fun x hx => by rw [O₂ x (by omega),O₁ x (by omega)]⟩
    rw [wordsVal,O₂.word (by omega) (by omega),m₁,word_writeW_self,e₂,e₁,wordsVal]

/-- Entry `d` of the table into the result, as `fetch_ok` into the entry. -/
theorem load_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    WP isa (.block (fetchHead ++ copyFrom 4 resultPt.x 0 ++ copyFrom 4 resultPt.y 32 ++
        copyFrom 4 resultPt.z 64)) s fun t =>
      Changes base resultWork s t ∧ PointAt base t resultPt P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have htab := table_coord_bounds h1 h15
  have ha : (tablePt d).x+96 ≤ 8192 := by
    have hb := (htab (tablePt d).z (by simp)).2.1
    change _+32 ≤ 6720 at hb
    dsimp only [tablePt] at hb ⊢; omega
  have hsep : ∀ e ∈ coordinates resultPt,e+32 ≤ (tablePt d).x := by
    have hh : ∀ e ∈ coordinates resultPt,e+32 ≤ tableAt := by decide
    intro e he; exact Nat.le_trans (hh e he) (htab _ (by simp)).1
  have sepX := hsep resultPt.x (by decide)
  have sepY := hsep resultPt.y (by decide)
  have sepZ := hsep resultPt.z (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs h1 h15 h2) fun s₁ ⟨p₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₁ p₁ (a:=(tablePt d).x) (src:=0) (dst:=resultPt.x)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok 4 hs₂ p₂ (a:=(tablePt d).x) (src:=32) (dst:=resultPt.y)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok 4 hs₃ p₃ (a:=(tablePt d).x) (src:=64) (dst:=resultPt.z)
    (by decide) (by omega) (by decide) (by decide) (Or.inl (by omega)))
    fun t ⟨z,k₄,u₄⟩ => ?_
  have dx : resultPt.x + 32 ≤ resultPt.y := by decide
  have dy : resultPt.y + 32 ≤ resultPt.z := by decide
  have e_x : num base t resultPt.x = num base s (tablePt d).x := by
    change wordsVal t.mem base resultPt.x 4 = wordsVal s.mem base (tablePt d).x 4
    rw [u₄.wordsVal (by omega) (by omega),
      u₃.wordsVal (by omega) (by omega),x,k₁.mem]
    rfl
  have e_y : num base t resultPt.y = num base s (tablePt d).y := by
    change wordsVal t.mem base resultPt.y 4 = wordsVal s.mem base (tablePt d).y 4
    rw [u₄.wordsVal (by omega) (by omega),y]
    rw [u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  have e_z : num base t resultPt.z = num base s (tablePt d).z := by
    change wordsVal t.mem base resultPt.z 4 = wordsVal s.mem base (tablePt d).z 4
    rw [z,u₃.wordsVal (Or.inr (by omega)) (by omega),
      u₂.wordsVal (Or.inr (by omega)) (by omega),k₁.mem]
    rfl
  have kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))
  have u : Unch base resultWork s.mem t.mem := by
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
  have h1 : 1 ≤ 15-j := by omega
  have h15 : 15-j ≤ 15 := by omega
  have htab := table_coord_bounds h1 h15
  have hlo := (htab (tablePt (15-j)).x (by simp)).1
  have ha : (tablePt (15-j)).x+96 ≤ 8192 := by
    have hb := (htab (tablePt (15-j)).z (by simp)).2.1
    change _+32 ≤ 6720 at hb
    dsimp only [tablePt] at hb ⊢; omega
  have ey : (tablePt (15-j)).y = (tablePt (15-j)).x + 32 := rfl
  have ez : (tablePt (15-j)).z = (tablePt (15-j)).x + 64 := rfl
  have hr : ∀ e ∈ coordinates resultPt,e+32 ≤ tableAt := by decide
  have sepX := hr resultPt.x (by decide)
  have sepY := hr resultPt.y (by decide)
  have sepZ := hr resultPt.z (by decide)
  have hta : tableAt = 5280 := rfl
  simp only [storeEntry,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (indexFrom_ok s (k:=15) (by decide) (by omega) h19) fun s₀ ⟨v₀,k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs₀ h1 h15 v₀) fun s₁ ⟨p₁,k₁⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyTo_ok 4 hs₁ p₁ (a:=(tablePt (15-j)).x) (dst:=0) (src:=resultPt.x)
    (by omega) (by decide) (by decide) (by decide) (Or.inr (by omega)))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyTo_ok 4 hs₂ p₂ (a:=(tablePt (15-j)).x) (dst:=32) (src:=resultPt.y)
    (by omega) (by decide) (by decide) (by decide) (Or.inr (by omega)))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyTo_ok 4 hs₃ p₃ (a:=(tablePt (15-j)).x) (dst:=64) (src:=resultPt.z)
    (by omega) (by decide) (by decide) (by decide) (Or.inr (by omega)))
    fun t ⟨z,k₄,u₄⟩ => ?_
  have m₁ : s₁.mem = s.mem := k₁.mem.trans k₀.mem
  have e_x : num base t (tablePt (15-j)).x = num base s resultPt.x := by
    change wordsVal t.mem base (tablePt (15-j)).x 4 = wordsVal s.mem base resultPt.x 4
    rw [u₄.wordsVal (by omega) (by omega),u₃.wordsVal (by omega) (by omega)]
    rw [show (tablePt (15-j)).x = (tablePt (15-j)).x + 0 by omega,x,m₁]
  have e_y : num base t (tablePt (15-j)).y = num base s resultPt.y := by
    change wordsVal t.mem base (tablePt (15-j)).y 4 = wordsVal s.mem base resultPt.y 4
    rw [ey,u₄.wordsVal (by omega) (by omega),y,
      u₂.wordsVal (by omega) (by omega),m₁]
  have e_z : num base t (tablePt (15-j)).z = num base s resultPt.z := by
    change wordsVal t.mem base (tablePt (15-j)).z 4 = wordsVal s.mem base resultPt.z 4
    rw [ez,z,u₃.wordsVal (by omega) (by omega),
      u₂.wordsVal (by omega) (by omega),m₁]
  have kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    (((((Keeps.regs k₀).mono (by decide)).trans ((Keeps.regs k₁).mono (by decide))).trans
      (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))
  have u : Unch base ((coordinates (tablePt (15-j))).map (·,32)) s.mem t.mem := by
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
    have ey' := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_y
    have ez' := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e_z
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
  refine WP.seq (WP.mono (indexFrom_ok s (k:=k) (by omega) hj h19) fun s₁ ⟨v₁,k₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have W₁ : Changes base resultWork s s₁ := Changes.of_keeps k₁ (by decide)
  have c₁ : s₁.gpr .x19 = s.gpr .x19 := k₁.gpr _ (by decide)
  refine WP.ite (decide (k-j=0)) (zero_test (by omega) v₁) (fun hz => ?_) (fun hn => ?_)
  · have hz' : k-j=0 := of_decide_eq_true hz
    rw [hA hz']
    exact WP.mono (infinity_ok hs₁ hc hC) fun t ⟨k₂,R₂,c₂⟩ => ⟨W₁.trans k₂,R₂,c₂.trans c₁⟩
  · have hn' : k-j≠0 := of_decide_eq_false hn
    have hp := (ht hn').of_mem k₁.mem
    exact WP.mono (load_ok hs₁ (by omega) (by omega) v₁ hp) fun t ⟨k₂,R₂,c₂⟩ =>
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
  refine WP.mono (decCounter_ok s h1 (by omega) h19) fun s₀ ⟨c₀,k₀⟩ => ?_
  refine WP.mono (rowTest_ok s₀ c₀) fun s₁ ⟨v₁,k₁⟩ => ?_
  have k₀₁ : Keeps [.x19,.x2,.x5] s s₁ := (k₀.mono (by decide)).trans (k₁.mono (by decide))
  have W₁ : Changes base arithmeticWork s s₁ := Changes.of_keeps k₀₁ (by decide)
  have I₁ := hi.unch W₁
  have c₁ : s₁.gpr .x19 = BitVec.ofNat 64 (j-1) := (k₁.gpr _ (by decide)).trans c₀
  have T₁ : Table base P Q (15-j) s₁ := fun e he1 he => (ht e he1 he).of_mem k₀₁.mem
  let d := 15-(j-1)
  have hd1 : 1 ≤ d := by omega
  have hd15 : d ≤ 15 := by omega
  let A := pair P Q ((previous d)%4) ((previous d)/4)
  have hpl := previous_lt hd1
  -- the source of the previous entry and `G` or `Q`, for either row case
  have src : ∀ (b : Bool), b = decide (d%4=0) →
      WP isa (.seq (previousEntry (if b then 11 else 14))
        (.block (if b then affineEntry PX PY else affineEntry GX GY))) s₁ fun t =>
        Changes base loopWork s₁ t ∧ Inputs base P Q t ∧ PointAt base t resultPt A ∧
        PointAt base t entry (if d%4=0 then Q else P) ∧ t.gpr .x19 = s₁.gpr .x19 := by
    intro b hb
    have hkj : (if b then 11 else 14) - (j-1) = previous d := by
      unfold previous
      by_cases hz : d%4=0
      · rw [decide_eq_true hz] at hb; subst hb
        rw [ite_eq_left hz]; simp only [ite_true]; omega
      · rw [decide_eq_false hz] at hb; subst hb
        rw [ite_eq_right hz]; simp only [Bool.false_eq_true,ite_false]; omega
    have hk15 : (if b then 11 else 14) ≤ 15 := by cases b <;> decide
    have hjk : j-1 ≤ (if b then 11 else 14) := by
      cases b
      · simp only [Bool.false_eq_true,ite_false]; omega
      · simp only [ite_true]
        have hz : d%4=0 := of_decide_eq_true hb.symm
        omega
    refine WP.seq (WP.mono (previousEntry_ok I₁.scr hc hC hk15 hjk c₁ (A:=A)
      (fun h0 => by dsimp only [A]; rw [hkj] at h0; rw [h0]; exact pair_zero P Q)
      (fun h0 => by
        rw [hkj] at h0 ⊢
        exact T₁ _ (by omega) (by omega)))
      fun s₂ ⟨k₂,R₂,c₂⟩ => ?_)
    have W₂ := k₂.mono resultWork_sub
    have I₂ := I₁.unch (W₂.mono loopWork_sub)
    have e : (if b then Q else P) = (if d%4=0 then Q else P) := by
      by_cases hz : d%4=0
      · rw [decide_eq_true hz] at hb; subst hb; simp only [ite_true,ite_eq_left hz]
      · rw [decide_eq_false hz] at hb; subst hb; simp only [Bool.false_eq_true,ite_false,ite_eq_right hz]
    refine WP.mono (affine_ok I₂ b) fun t ⟨k₃,E₃,c₃⟩ => ?_
    have W₃ := W₂.trans (k₃.mono entryWork_sub)
    exact ⟨W₃,I₁.unch (W₃.mono loopWork_sub),k₃.point I₂.scr R₂ (by decide) (by decide),e ▸ E₃,
      c₃.trans c₂⟩
  have hrow : isa.eval (.zero .x .x2) s₁ = some (decide (d%4=0)) := by
    change some (s₁.read .x .x2 == 0) = _
    rw [read_x,v₁]
    have hz := rowVal_zero (j-1) (by omega)
    by_cases h : (15-(j-1))%4=0
    · rw [decide_eq_true h,beq_iff_eq.mpr (hz ▸ h)]
    · rw [decide_eq_false h]
      exact congrArg some (beq_eq_false_iff_ne.mpr fun e => h (hz ▸ e))
  have cont : ∀ s₂, (Changes base loopWork s₁ s₂ ∧ Inputs base P Q s₂ ∧ PointAt base s₂ resultPt A ∧
      PointAt base s₂ entry (if d%4=0 then Q else P) ∧ s₂.gpr .x19 = s₁.gpr .x19) →
      WP isa (.seq addPoints (.block storeEntry)) s₂ fun t =>
        (Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q (15-(j-1)) t) ∧
        t.gpr .x19 = BitVec.ofNat 64 (j-1) := by
    intro s₂ ⟨k₂,I₂,R₂,E₂,c₂⟩
    have he : onCurve C (if d%4=0 then Q else P)=true := by
      by_cases hz : d%4=0
      · rw [ite_eq_left hz]; exact hQ
      · rw [ite_eq_right hz]; exact hP
    have hA : onCurve C A=true := pair_curve hC hP hQ _ _
    refine WP.seq (WP.mono (sum_points hc hC I₂.scr I₂.mod I₂.a I₂.b I₂.a_lt I₂.b_lt he hA E₂ R₂)
      fun s₃ ⟨k₃,R₃,c₃⟩ => ?_)
    have W₃ := k₂.trans (k₃.mono addWork_sub)
    have I₃ := I₁.unch (W₃.mono loopWork_sub)
    have c₃' : s₃.gpr .x19 = BitVec.ofNat 64 (j-1) := c₃.trans (c₂.trans c₁)
    have e : add (if d%4=0 then Q else P) A = pair P Q (d%4) (d/4) := table_step hC hP hQ hd1
    rw [e] at R₃
    refine WP.mono (storeEntry_ok I₃.scr (j:=j-1) (by omega) c₃' R₃) fun t ⟨k₄,R₄,c₄⟩ => ?_
    have W₄ := (W₃.mono loopWork_sub).trans (k₄.cover (tableWork_cover hd1 hd15))
    have W := W₁.trans W₄
    refine ⟨⟨W,hi.unch W,fun i hi1 hid => ?_⟩,c₄.trans c₃'⟩
    by_cases heq : i=d
    · subst i; exact R₄
    · have hi' : i < d := by omega
      have old := W₃.table I₁.scr hi1 (by omega) (T₁ i hi1 (by omega))
      exact k₄.point I₃.scr old
        (fun x hx => Nat.le_trans (table_coord_bounds hi1 (by omega) x hx).2.1 (by decide))
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
  have W₁ : Changes base arithmeticWork s s₁ := Changes.of_keeps k₁ (by decide)
  let inv := fun j t => (Changes base arithmeticWork s t ∧ Inputs base P Q t ∧
    Table base P Q (15-j) t) ∧ t.gpr .x19 = BitVec.ofNat 64 j
  refine countLoop_ok (Inv:=inv) (n:=15) (by decide) (fun j t h1 h15 ⟨⟨k,I,T⟩,c⟩ => ?_)
    (fun t ⟨⟨k,I,T⟩,_⟩ => ⟨k,I,T⟩) (by decide)
    ⟨⟨W₁,hi.unch W₁,fun _ h1 h0 => False.elim (by omega)⟩,c₁⟩
  exact WP.mono (buildStep_ok hc hC hP hQ h1 h15 I T c) fun u ⟨⟨k',I',T'⟩,c'⟩ =>
    ⟨⟨⟨k.trans k',I',T'⟩,c'⟩,c'⟩

end VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
