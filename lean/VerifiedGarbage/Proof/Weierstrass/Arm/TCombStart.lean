module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Initialize the comb with its checked affine offset point. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm.Point
open VG.Proof.X25519.Arm

theorem start_ok (K : TCombCfg) {s : State} {base : Addr}
    (h : Layout K) (hs : Scr s base 4096)
    (hx : K.start.1<2^(64*K.L.M.n)) (hy : K.start.2<2^(64*K.L.M.n))
    (hz : K.one<2^(64*K.L.M.n)) (encJ : encodable (BitVec.ofNat 32 K.J)=true) :
    WP isa (.block (ladderSetup K.L ++
      setConst K.L.M.n K.L.R.x K.start.1 ++ setConst K.L.M.n K.L.R.y K.start.2 ++
      setConst K.L.M.n K.L.R.z K.one ++ ([.mov .r11 (.imm (BitVec.ofNat 32 K.J))] : List Instr))) s fun t =>
      Rest [.r4,.r11] s t ∧ Unch base (writes K) s.mem t.mem ∧
      CpOk K.L base t.mem s.mem ∧ t.gpr .r11=BitVec.ofNat 32 K.J ∧
      wordsVal t.mem base K.L.R.x K.L.M.n=K.start.1 ∧
      wordsVal t.mem base K.L.R.y K.L.M.n=K.start.2 ∧
      wordsVal t.mem base K.L.R.z K.L.M.n=K.one := by
  have hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low
  obtain ⟨rx,ry,rz,hzero,hneg⟩ := low
  obtain ⟨rxy,rxz,ryz⟩ := h.apart
  have nowrap := hs.nowrap
  rw [List.append_assoc,List.append_assoc,List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (ladderSetup_ok hs h.n3 h.n6 h.point)
    fun u ⟨ku,ou,cp⟩ => ?_
  have hsu := hs.of_rest ku (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsu (by omega) hx) fun v ⟨xv,kv,ov⟩ => ?_
  have hsv := hsu.of_rest kv (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsv (by omega) hy) fun a ⟨ya,ka,oa⟩ => ?_
  have hsa := hsv.of_rest ka (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsa (by omega) hz) fun b ⟨zb,kb,ob⟩ => ?_
  refine wp_mov (op2_imm encJ) fun t ut => WP.block_nil ?_
  have ub : Unch base [(K.L.R.x,8*K.L.M.n),(K.L.R.y,8*K.L.M.n),(K.L.R.z,8*K.L.M.n)] u.mem t.mem := by
    rw [ut.mem]
    exact ov.unch.trans (oa.unch.trans ob.unch)
  refine ⟨(ku.mono (by simp)).trans ((kv.mono (by simp)).trans
      ((ka.mono (by simp)).trans ((kb.mono (by simp)).trans (ut.rest (by simp))))),?_,?_,ut.gpr,?_,?_,?_⟩
  · apply (ou.trans ub).mono
    intro w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|(rfl|rfl|rfl) <;> simp [writes]
  · apply cp.keep h.n3 h.n6 ub
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl <;> exact .inl (Nat.le_trans (by assumption) (oAt_le_qAt _))
  · rw [ut.mem,ob.wordsVal (by omega) (by omega),oa.wordsVal (by omega) (by omega),xv]
  · rw [ut.mem,ob.wordsVal (by omega) (by omega),ya]
  · rw [ut.mem,zb]

end VG.Proof.Weierstrass.Arm.TComb
