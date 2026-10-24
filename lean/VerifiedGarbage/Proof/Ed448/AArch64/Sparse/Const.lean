module

public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
public import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.X448.AArch64.Weak.Env

/-! Lift existing constant-slot stores into the bounded field environment. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Proof.X448.AArch64 (Scr Keeps Outside FieldMem word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Same env_update fieldMem_same)
open VG.Proof.X448.AArch64.Base (constSlot_ok F_of_words bnd_of_words)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem constE {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base)
    (o:Index) (v:Spec.X448.Fe) :
    WP isa (.block (constSlot (slot o.val) v)) s fun t =>
      BEnv t.mem base ∧ Same base [o] s.mem t.mem ∧
      EV t.mem base=Function.update (EV s.mem base) o v ∧
      (∀ j<8,word t.mem base (slot o.val+8*j)=limb v j) ∧
      Outside base (slot o.val) 64 s.mem t.mem ∧ Keeps [.x4] s t := by
  have ho:=o.isLt
  refine WP.mono (constSlot_ok hs (by simp only [slot];omega) (by simp only [slot];omega) v)
    fun t ⟨tv,fo,kt⟩ => ?_
  have fm:FieldMem base (slot o.val) s.mem t.mem:=FieldMem.output (fo.mono (Nat.le_refl _) (by omega))
  refine ⟨env_update hb fm (bnd_of_words tv),fieldMem_same fm,?_,tv,fo,kt⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm,F_of_words tv]

end VG.Proof.Ed448.AArch64.Sparse
