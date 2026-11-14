module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeBackInv
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

private theorem normalize_back_row_inverse (E : Nat → Fin fieldPrime) (X Y Z : Fin fieldPrime) :
    normalizeBackRowEnv E X Y Z 0=E 0*Z := by
  simp only [normalizeBackRowEnv,normalizeBackXEnv,normalizeBackYEnv,
    Function.update_of_ne (by decide : (0:Nat)≠3),Function.update_of_ne (by decide : (0:Nat)≠2),
    Function.update_self,Function.update_of_ne (by decide : (0:Nat)≠1),
    Function.update_of_ne (by decide : (3:Nat)≠1)]

theorem normalize_back_advance {base table : Addr} {row : Nat} {s : State}
    {X Y Z P : Nat → Fin fieldPrime} {I : Fin fieldPrime}
    (layout : NormalizeLayout base table 8192)
    (inv : NormalizeBackInv base table s X Y Z P I) (lo : 1≤row) (hi : row<16) :
    WP isa (normalizeBackRow (normalizePrefixSlot row) row) s fun t =>
      NormalizeBackInv base table t
        (Function.update X row (I*P row*(I*P row)*X row))
        (Function.update Y row (Y row*((I*P row*(I*P row))*(I*P row)))) Z P (I*Z row) ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table row 144 s.mem t.mem := by
  have bx := inv.tableValues.canonical row hi 0 (by decide)
  have byY := inv.tableValues.canonical row hi 1 (by decide)
  have bz := inv.tableValues.canonical row hi 2 (by decide)
  have vx := inv.tableValues.xValue row hi
  have vy := inv.tableValues.yValue row hi
  have vz := inv.tableValues.zValue row hi
  simp only [normalizeEntrySlot,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at bx byY bz vx vy vz
  refine WP.mono (normalize_back_row_ok layout (normalize_back_layout_prefix lo hi)
    (normalize_back_input_ok inv lo hi) hi bx byY bz)
    fun t ⟨state,kept,frame,tx,ty,xvalue,yvalue⟩ => ?_
  rw [vx,vy,vz] at state
  rw [vx] at xvalue
  rw [vy] at yvalue
  simp only [normalizeBackInput,ite_true,ite_eq_right (by decide : ¬(4:Nat)=0)] at xvalue yvalue
  have tableNew := normalize_back_table_update inv.tableValues layout hi frame tx ty xvalue yvalue
  have ib:=state.inv.bound 0 (by simp)
  have iv:=state.inv.value 0 (by simp)
  simp only [normalizeBackSlot,Nat.one_mul] at ib iv
  rw [normalize_back_row_inverse] at iv
  simp only [normalizeBackInput,ite_true] at iv
  refine ⟨⟨state.context,tableNew,?_,?_,ib,iv⟩,kept,frame⟩
  · intro n hn hn'
    rw [frame.prefix_words layout (by omega_arith) hn hn']
    exact inv.prefixBound n hn hn'
  · intro n hn hn'
    rw [frame.prefix_words layout (by omega_arith) hn hn']
    exact inv.prefixValue n hn hn'

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def normalizeBackWork : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (normalizeBackRow (normalizePrefixSlot (n+1)) (n+1)) (normalizeBackWork n)

@[irreducible] def normalizeBackResult {F : Type} [Mul F] (Z P : Nat → F) :
    Nat → (Nat → F) → (Nat → F) → F → (Nat → F) × (Nat → F) × F
  | 0,X,Y,I => (X,Y,I)
  | n+1,X,Y,I =>
    let H:=I*P (n+1)
    normalizeBackResult Z P n (Function.update X (n+1) (H*H*X (n+1)))
      (Function.update Y (n+1) (Y (n+1)*((H*H)*H))) (I*Z (n+1))

theorem NormalizeBackFrame.whole {base table : Addr} {row : Nat} {m m' : Mem}
    (frame : NormalizeBackFrame base table row 144 m m') (hi : row<16) :
    NormalizeBackFrame base table 0 3456 m m' := by
  intro x hw hs ht
  apply frame x hw hs
  omega_arith

theorem normalize_back_work_ok {base table : Addr} (n : Nat) {s : State}
    {X Y Z P : Nat → Fin fieldPrime} {I : Fin fieldPrime}
    (layout : NormalizeLayout base table 8192) (hi : n<16)
    (inv : NormalizeBackInv base table s X Y Z P I) :
    WP isa (normalizeBackWork n) s fun t =>
      NormalizeBackInv base table t (normalizeBackResult Z P n X Y I).1
        (normalizeBackResult Z P n X Y I).2.1 Z P (normalizeBackResult Z P n X Y I).2.2 ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table 0 3456 s.mem t.mem := by
  induction n generalizing s X Y I with
  | zero =>
    rw [normalizeBackWork,WP.block_nil_iff]
    simp only [normalizeBackResult]
    exact ⟨inv,.refl s,.refl base table 0 3456 s.mem⟩
  | succ n ih =>
    rw [normalizeBackWork,WP.seq_iff]
    simp only [normalizeBackResult]
    refine WP.mono (normalize_back_advance layout inv (by omega_arith) hi)
      fun a ⟨ia,ka,fa⟩ => ?_
    refine WP.mono (ih (s:=a) (by omega_arith) ia) fun t ⟨it,kt,ft⟩ => ?_
    exact ⟨it,ka.trans kt,(fa.whole hi).trans ft⟩

theorem normalize_back_work_readonly {base table : Addr} {s t : State}
    (layout : NormalizeLayout base table 8192) (frame : NormalizeBackFrame base table 0 3456 s.mem t.mem)
    {d : Nat} (lo : 3232≤d) (hi : d<3952) : t.mem (off base d)=s.mem (off base d) :=
  frame.readonly layout.tableApart (by decide) lo hi

end VG.Proof.Weierstrass.AArch64.P521Native
