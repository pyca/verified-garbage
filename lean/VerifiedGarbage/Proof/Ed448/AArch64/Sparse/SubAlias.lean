module

public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sub
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Finish
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block

/-! Limb-wise subtraction permits exact input/output aliases: each word is
loaded before it is overwritten, and later input words remain untouched. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off word limbs)
open VG.Proof.Curve448.AArch64.Fast (K2 K4 twoPW twoPRegs_ok subStep_ok)
open VG.Impl.Curve448.AArch64.Fast (twoPRegs twoPReg)

private theorem futureWord {base:Addr} {m m':Mem} {o a i:Nat}
    (h:Outside base o (8*i) m m') (hi:i<8) (ha:a+64≤8192)
    (hsep:o=a ∨ o+64≤a ∨ a+64≤o) : word m' base (a+8*i)=word m base (a+8*i) := by
  apply h.word
  · rcases hsep with rfl | hsep | hsep <;> omega
  · omega

theorem subAlias_ok {s:State} {base:Addr} (hs:Scr s base) {o a b:Nat}
    (ho:o+64≤8192) (ha:a+64≤8192) (hb:b+64≤8192)
    (ho8:o%8=0) (ha8:a%8=0) (hb8:b%8=0)
    (hoa:o=a ∨ o+64≤a ∨ a+64≤o) (hob:o=b ∨ o+64≤b ∨ b+64≤o) :
    WP isa (.block (VG.Impl.Curve448.AArch64.Fast.sub o a b)) s fun t =>
      (∀ i<8,word t.mem base (o+8*i)=
        word s.mem base (a+8*i)+twoPW i-word s.mem base (b+8*i)) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps [.x0,.x2,.x4,.x5] s t := by
  rw [VG.Impl.Curve448.AArch64.Fast.sub,WP.block_append_iff]
  refine WP.mono (twoPRegs_ok s) fun t ⟨t0,t2,tm,tk⟩ => ?_
  let rs:List Reg:=[.x4,.x5]
  let inv:=fun i (u:State) =>
    (∀ j<i,word u.mem base (o+8*j)=word t.mem base (a+8*j)+twoPW j-word t.mem base (b+8*j)) ∧
    Outside base o (8*i) t.mem u.mem ∧ Keeps rs t u
  have hloop:WP isa (.block ((List.range 8).flatMap fun i =>
      [ld .x4 (a+8*i),ld .x5 (b+8*i),.add .x .x4 .x4 (twoPReg i),
       .sub .x .x4 .x4 .x5,st .x4 (o+8*i)])) t (inv 8):=by
    refine wp_range_flatMap (M:=isa) (N:=8) inv (fun i u hi ⟨uv,fo,ku⟩ => ?_)
      8 (by decide) t ⟨fun _ h => by omega,Outside.refl _ _ _ _,Keeps.refl _ _⟩
    have hu:Scr u base:=(hs.of_keeps tk (by decide)).of_keeps ku (by decide)
    have u0:u.gpr .x0=K2:=(ku.1 _ (by decide)).trans t0
    have u2:u.gpr .x2=K4:=(ku.1 _ (by decide)).trans t2
    refine WP.mono (subStep_ok hu hi ho ha hb ho8 ha8 hb8 u0 u2) fun v ⟨vm,kv⟩ => ?_
    refine ⟨fun j hj => ?_,?_,ku.trans kv⟩
    · rw [vm,VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega)]
      by_cases he:j=i
      · subst j
        rw [ite_eq_left rfl,futureWord fo hi ha hoa,futureWord fo hi hb hob]
      · rw [ite_eq_right (by omega)]
        exact uv j (by omega)
    · intro x hx
      rw [vm,VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega) x (by omega)]
      exact fo x (by omega)
  refine WP.mono hloop fun u ⟨uv,fo,ku⟩ => ?_
  refine ⟨fun j hj => ?_,?_,(tk.mono (by decide)).trans (ku.mono (by decide))⟩
  · rw [uv j hj,tm]
  · rw [tm] at fo
    exact fo

/-- Exact field-slot aliases are admitted without changing the arithmetic or its bounds. -/
theorem subAliasE {s:State} {base:Addr} (hs:Scr s base)
    (hb:VG.Proof.X448.AArch64.Fast.BEnv s.mem base)
    (o a b:VG.Proof.X448.AArch64.Weak.Index)
    (ha:VG.Proof.X448.AArch64.Fast.Bnd VG.Proof.Curve448.AArch64.Fast.Mb s.mem base
      (VG.Impl.X448.AArch64.slot a.val))
    (hb':VG.Proof.X448.AArch64.Fast.Bnd VG.Proof.Curve448.AArch64.Fast.Mb s.mem base
      (VG.Impl.X448.AArch64.slot b.val)) :
    WP isa (.block (VG.Impl.Curve448.AArch64.Fast.sub (VG.Impl.X448.AArch64.slot o.val)
      (VG.Impl.X448.AArch64.slot a.val) (VG.Impl.X448.AArch64.slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧
      VG.Proof.X448.AArch64.Fast.Same base [o] s.mem t.mem ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base=
        Function.update (VG.Proof.X448.AArch64.Weak.E s.mem base) o
          (VG.Proof.X448.AArch64.Weak.E s.mem base a-VG.Proof.X448.AArch64.Weak.E s.mem base b) := by
  have sep (i j:VG.Proof.X448.AArch64.Weak.Index) :
      VG.Impl.X448.AArch64.slot i.val=VG.Impl.X448.AArch64.slot j.val ∨
      VG.Impl.X448.AArch64.slot i.val+64≤VG.Impl.X448.AArch64.slot j.val ∨
      VG.Impl.X448.AArch64.slot j.val+64≤VG.Impl.X448.AArch64.slot i.val := by
    by_cases h:i=j
    · exact Or.inl (congrArg (fun x => VG.Impl.X448.AArch64.slot x.val) h)
    · exact Or.inr (VG.Proof.X448.AArch64.Fast.slot_sep64 h)
  refine WP.mono (subAlias_ok hs
    (by have := VG.Proof.X448.AArch64.Fast.slot_mem o;omega)
    (by have := VG.Proof.X448.AArch64.Fast.slot_mem a;omega)
    (by have := VG.Proof.X448.AArch64.Fast.slot_mem b;omega)
    (VG.Proof.X448.AArch64.Weak.slot_aligned o) (VG.Proof.X448.AArch64.Weak.slot_aligned a)
    (VG.Proof.X448.AArch64.Weak.slot_aligned b) (sep o a) (sep o b)) fun t ⟨tv,fo,tk⟩ => ?_
  have tl:∀ i<8,limbs t.mem base (VG.Impl.X448.AArch64.slot o.val) i=
      VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (VG.Impl.X448.AArch64.slot a.val))
        (limbs s.mem base (VG.Impl.X448.AArch64.slot b.val)) i:=by
    intro i hi
    show (word t.mem base (VG.Impl.X448.AArch64.slot o.val+8*i)).toNat=_
    rw [tv i hi,VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (ha i hi) (hb' i hi)]
    rfl
  have fm:VG.Proof.X448.AArch64.FieldMem base (VG.Impl.X448.AArch64.slot o.val) s.mem t.mem:=
    VG.Proof.X448.AArch64.FieldMem.output (fo.mono (Nat.le_refl _) (by omega))
  refine ⟨⟨tk.mono (by decide),VG.Proof.X448.AArch64.Fast.fieldMem_outside2 fm⟩,
    VG.Proof.X448.AArch64.Fast.env_update hb fm (fun i hi => ?_),
    VG.Proof.X448.AArch64.Fast.fieldMem_same fm,?_⟩
  · rw [tl i hi]
    exact VG.Proof.Curve448.AArch64.Fast.diff_bound ha i hi
  · rw [VG.Proof.X448.AArch64.Weak.E_update fm]
    refine congrArg (Function.update _ o) ?_
    change VG.Proof.X448.toFe _=VG.Proof.X448.toFe _-VG.Proof.X448.toFe _
    rw [VG.Proof.X448.Wide.valN_congr tl]
    exact VG.Proof.Curve448.AArch64.Fast.diff_val hb'

end VG.Proof.Ed448.AArch64.Sparse
