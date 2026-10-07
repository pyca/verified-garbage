import VerifiedGarbage.Proof.Weierstrass.X86_64.PointTransfer
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero

/-! Branchless point selection expressed in the field-operation invariant. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nonzeroFieldMask_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {a : Nat} (ha : a ∈ V) :
    WP isa (.block (nzMask M.n a)) s fun t =>
      t.gpr .rcx = bmask (decide (E a ≠ 0)) ∧ Inv M base size m Sl V E t ∧
      ProgKeep M base [] s t := by
  refine WP.mono (nzMask_ok hI.scr hI.mod.n0 (hL.le a (hI.sl a ha)))
    fun t ⟨hz,hk⟩ => ⟨?_,hI.of_keeps hk (by decide),?_⟩
  · have he := toM_eq_zero_iff hm (hI.lt a ha)
    rw [hI.val a ha] at he
    rw [hz]
    simp only [ne_eq,he]
  · refine ⟨fun r hr => hk.1 r ?_,hk.2.2.1,hk.2.2.2,fun _ _ _ => congrFun hk.2.1 _⟩
    intro h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> exact hr (by simp [clob])

/-- Keep o when the mask is set, otherwise copy a into its contiguous slots. -/
theorem selectPointKeep_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hn : M.n=4)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {o a : Pt} (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (hV : ∀ x∈jacCoords o++jacCoords a,x∈V)
    (hap : ∀ x∈jacCoords o,∀ y∈jacCoords a,x≠y)
    (c : Bool) (hc : s.gpr .rcx=bmask c) :
    WP isa (.block (selPt M.n o a o)) s fun t =>
      ProgKeep M base (jacCoords o) s t ∧
      Inv M base size m Sl (jacCoords o++V) (pointTransferEnv E o (if c then o else a)) t := by
  have hO : ∀ x∈jacCoords o, Sl x := fun x hx => hI.sl x (hV x (List.mem_append_left _ hx))
  have hA : ∀ x∈jacCoords a, Sl x := fun x hx => hI.sl x (hV x (List.mem_append_right _ hx))
  have hin : ∀ d∈[o.x,o.y,o.z,a.x,a.y,a.z],d+8*M.n≤size := by
    intro d hd
    exact hL.le d (hI.sl d (hV d hd))
  have hoo : (o.x+8*M.n≤o.y ∨ o.y+8*M.n≤o.x) ∧
      (o.x+8*M.n≤o.z ∨ o.z+8*M.n≤o.x) ∧
      (o.y+8*M.n≤o.z ∨ o.z+8*M.n≤o.y) := by
    rw [hn,hy,hz]
    omega
  have hab : ∀ d∈[o.x,o.y,o.z],∀ e∈[a.x,a.y,a.z],d+8*M.n≤e ∨ e+8*M.n≤d :=
    fun d hd e he => hL.apart d e (hO d hd) (hA e he) (hap d hd e he)
  refine WP.mono (selPtKeep_ok hI.scr c hc hin hoo hab) fun t ⟨vx,vy,vz,hk,ho⟩ => ?_
  have hkr : KeepRegs [.rax,.rcx,.rdx] s t := hk.mono (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp)
  have hout : Outside base o.x 96 s.mem t.mem := by
    intro x hx
    exact ho x (by rw [hn]; omega) (by rw [hn,hy]; omega) (by rw [hn,hz]; omega)
  cases c with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at vx vy vz ⊢
    exact hI.transferPointFields hL hn hy hz hO
      (fun x hx => hV x (List.mem_append_right _ hx)) vx vy vz hkr hout
  | true =>
    simp only [ite_true] at vx vy vz ⊢
    exact hI.transferPointFields hL hn hy hz hO
      (fun x hx => hV x (List.mem_append_left _ hx)) vx vy vz hkr hout

def pointMaskEnv {F : Type} [Zero F] [DecidableEq F] (E : Nat → F) (o a : Pt) (z : Nat) : Nat → F :=
  pointTransferEnv E o (if E z=0 then a else o)

theorem pointTransferEnv_readonly {F : Type} (E : Nat → F) (o a : Pt) {x : Nat}
    (hx : x∉jacCoords o) : pointTransferEnv E o a x=E x := by
  simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_or] at hx
  simp only [pointTransferEnv,hx.1,hx.2.1,hx.2.2,ite_false]

theorem pointTransferEnv_values {F : Type} (E : Nat → F) (o a : Pt)
    (hy : o.y=o.x+32) (hz : o.z=o.x+64) :
    (pointTransferEnv E o a o.x,pointTransferEnv E o a o.y,pointTransferEnv E o a o.z)=
      (E a.x,E a.y,E a.z) := by
  have hyx : o.y≠o.x := by omega
  have hzx : o.z≠o.x := by omega
  have hzy : o.z≠o.y := by omega
  simp only [pointTransferEnv,ite_true,hyx,hzx,hzy,ite_false]

theorem pointMaskEnv_readonly {F : Type} [Zero F] [DecidableEq F]
    (E : Nat → F) (o a : Pt) (z : Nat) {x : Nat} (hx : x∉jacCoords o) :
    pointMaskEnv E o a z x=E x := pointTransferEnv_readonly E o _ hx

theorem pointMask_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hn : M.n=4) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {o a : Pt} {z : Nat} (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (hV : ∀ x∈jacCoords o++jacCoords a,x∈V) (hZ : z∈V)
    (hap : ∀ x∈jacCoords o,∀ y∈jacCoords a,x≠y) :
    WP isa (.block (nzMask M.n z++selPt M.n o a o)) s fun t =>
      ProgKeep M base (jacCoords o) s t ∧
      Inv M base size m Sl (jacCoords o++V) (pointMaskEnv E o a z) t := by
  rw [WP.block_append_iff]
  refine WP.mono (nonzeroFieldMask_ok hL hm hI hZ) fun u ⟨hc,iu,ku⟩ => ?_
  refine WP.mono (selectPointKeep_ok hL hn iu hy hz hV hap (decide (E z≠0)) hc)
    fun t ⟨kt,it⟩ => ?_
  refine ⟨(ku.mono (by simp)).trans kt,?_⟩
  have he : (if decide (E z≠0) then o else a)=(if E z=0 then a else o) := by
    by_cases h : E z=0 <;> simp only [h,ne_eq,not_true_eq_false,decide_false,
      Bool.false_eq_true,ite_false,not_false_eq_true,decide_true,ite_true]
  rw [he] at it
  exact it

end VG.Proof.Weierstrass.X86_64
