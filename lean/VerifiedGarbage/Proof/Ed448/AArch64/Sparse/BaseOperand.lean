module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectBase
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.BaseWords
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
import VerifiedGarbage.Proof.Framework.Block

/-! The directly indexed affine base operand has canonical radix-2^56 limbs. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.X448.AArch64.Base (limb)
open VG.Proof.X448.AArch64 (Scr limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.Ed448.AArch64.Window (dst)
open VG.Proof.X448.AArch64.Base (F_of_words limb_lt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem baseOperand_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base)
    (ht:BaseTableAt s base (s.syms baseSym)) {m:Nat}
    (hm:m<128) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block selectBase) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [6,7] s.mem t.mem ∧
      Bnd Mb t.mem base (slot 6) ∧
      (EV t.mem base 6,EV t.mem base 7)=Impl.Ed448.PublicTable.entry (m/2) ∧
      VG.Proof.X448.AArch64.Keeps [.x11,.x8,.x9,.x4] s t := by
  refine WP.mono (selectBase_ok hs ht hm h11) fun t ⟨tv,fo,kt⟩ => ?_
  have sm:Same base [6,7] s.mem t.mem:=by
    intro i hi j hj
    have n6:i.val≠6:=fun h => hi (by rw [show i=(6:Index) from Fin.ext h];decide)
    have n7:i.val≠7:=fun h => hi (by rw [show i=(7:Index) from Fin.ext h];decide)
    have hilt:=i.isLt
    exact fo.limbs (by simp only [slot];omega) (by simp only [slot];omega) (by omega)
  have xw:∀ j<8,word t.mem base (slot 6+8*j)=limb (Impl.Ed448.PublicTable.entry (m/2)).1 j:=by
    intro j hj
    have hd:dst j=slot 6+8*j:=by simp only [dst,slot];omega
    rw [←hd,tv j (by omega),baseWord_entry (by omega),ite_eq_left hj,Nat.mod_eq_of_lt hj]
  have yw:∀ j<8,word t.mem base (slot 7+8*j)=limb (Impl.Ed448.PublicTable.entry (m/2)).2 j:=by
    intro j hj
    have hd:dst (8+j)=slot 7+8*j:=by simp only [dst,slot];omega
    rw [←hd,tv (8+j) (by omega),baseWord_entry (by omega),ite_eq_right (by omega),
      show (8+j)%8=j by omega]
  have tb:BEnv t.mem base:=by
    intro i j hj
    by_cases h6:i=6
    · subst i
      change (word t.mem base (slot 6+8*j)).toNat<Ib
      rw [xw j hj]
      exact Nat.lt_of_lt_of_le (limb_lt _ _) (by decide)
    · by_cases h7:i=7
      · subst i
        change (word t.mem base (slot 7+8*j)).toNat<Ib
        rw [yw j hj]
        exact Nat.lt_of_lt_of_le (limb_lt _ _) (by decide)
      · rw [sm i (by simp only [List.mem_cons,List.not_mem_nil,or_false];exact not_or.mpr ⟨h6,h7⟩) j hj]
        exact hb i j hj
  refine ⟨⟨kt.mono (by decide),fun x hx _ => fo x (by omega)⟩,tb,sm,?_,?_,kt⟩
  · intro j hj
    show (word t.mem base (slot 6+8*j)).toNat<Mb
    rw [xw j hj]
    exact Nat.lt_of_lt_of_le (limb_lt _ _) (by decide)
  · exact Prod.ext (F_of_words xw) (F_of_words yw)

end VG.Proof.Ed448.AArch64.Sparse
