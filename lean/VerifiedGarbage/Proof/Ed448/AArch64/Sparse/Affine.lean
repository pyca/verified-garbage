module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AffineSpec
public import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint

/-! Inline affine addition with the existing verified interleaved field formula. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob indeps_ops_mul2)
open VG.Proof.X448.AArch64.Base (affEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

private theorem mask_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block [.movz .x .x12 0xffff 0,.movk .x .x12 0x0fff 1]) s fun t =>
      Keeps [] s t ∧ t.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,Nat.reduceMul,
    Nat.reduceLT,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨⟨fun r _ => ?_,rfl,rfl⟩,rfl⟩
  by_cases h:r= .x12
  · subst r
    simp only [RegUpd.gpr_write,ite_true,hs.mask]
    rfl
  · simp only [RegUpd.gpr_write,h,ite_false]

theorem addAffine_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base)
    (hz:Bnd Mb s.mem base (slot 19)) :
    WP isa VG.Impl.Ed448.AArch64.Sparse.addAffine s fun t =>
      AffineKeep base s t ∧ BEnv t.mem base ∧
      Same base (VG.Proof.X448.AArch64.Base.temps++[5,3,4]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot 3) ∧ Bnd Mb t.mem base (slot 4) ∧ Bnd Mb t.mem base (slot 5) ∧
      EV t.mem base=affEnv 3 4 5 6 7 (EV s.mem base) := by
  unfold VG.Impl.Ed448.AArch64.Sparse.addAffine
  rw [WP.seq_iff,List.append_assoc,WP.block_append_iff]
  refine WP.mono (save_ok hs) fun a ⟨sv,fo,ag,ar,aw⟩ => ?_
  have ak:Keeps [] s a:=⟨fun _ _ => congrFun ag _,ar,aw⟩
  have ha:Scr a base:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mask_ok ha) fun b ⟨bk,bm⟩ => ?_
  have hb':Scr b base:=ha.of_keeps bk (by decide)
  have bb:BEnv b.mem base:=by rw [bm];exact save_bounds fo hb
  have bz:Bnd Mb b.mem base (slot 19):=by
    rw [bm]
    intro j hj
    rw [fo.limbs (Or.inl (by decide)) (by decide) (by omega)]
    exact hz j hj
  refine WP.mono (VG.Proof.X448.AArch64.Base.addAffine_ok 3 4 5 6 7
    (by decide) (by decide) (by decide) hb' bb bz
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel))
    (indeps_ops_mul2 _ _ _ _ _ _ _ (by decide +kernel)))
    fun c ⟨ck,cb,cs,cx,cy,cz,ce⟩ => ?_
  have hsv:Saved base s.gpr c.mem:=fun i hi => by
    rw [ck.mem.word (Or.inr (by simp only [GSAVE];omega)) (Or.inr (by simp only [ACC,GSAVE];omega)) (by simp only [GSAVE];omega),bm]
    exact sv i hi
  refine WP.mono (restore_ok (ck.scr hb') hsv) fun t ⟨tg,tm,tk⟩ => ?_
  refine ⟨⟨?_,tg,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · exact ((ak.mono (by decide)).trans (bk.mono (by decide))).trans
      (ck.regs.trans (tk.mono (by decide)))
  · intro x hx hy hz
    rw [tm,ck.mem x hx hy,bm,fo x hz]
  · rw [tm]
    exact cb
  · intro i hi j hj
    rw [tm,cs i hi j hj,bm]
    have h:=i.isLt
    exact fo.limbs (Or.inl (by simp only [slot,GSAVE];omega)) (by simp only [slot];omega) (by omega)
  · rw [tm]
    exact cx
  · rw [tm]
    exact cy
  · rw [tm]
    exact cz
  · rw [tm,ce,bm,save_env fo]

theorem affine_ok : AffineOk:=⟨fun hs hb hz => addAffine_ok hs hb hz⟩

end VG.Proof.Ed448.AArch64.Sparse
