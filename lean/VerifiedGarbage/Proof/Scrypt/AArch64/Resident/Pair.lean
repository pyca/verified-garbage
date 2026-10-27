module

public import VerifiedGarbage.Proof.Scrypt.AArch64.Resident.Load
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
import VerifiedGarbage.Proof.MdStream.AArch64.Common
public import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
public import VerifiedGarbage.Proof.Scrypt.BlockMix

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt.AArch64 (Holds Words wreg_ne_x1)
open VG.Impl.Scrypt.AArch64 (wreg)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem)
open VG.Proof.MdStream.AArch64 (wp_addImm wp_mov wp_subImm)

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop extends BlockMix.Inv s₀ k s where
  holds : Holds (words s.mem (BlockMix.xP s₀ k)) s

theorem other_ne {r : Reg} (hr : r ∈ BlockMix.others) : ¬ Words r ∧ r ≠ .x1 := by
  exact VG.Proof.Scrypt.AArch64.not_words_preserved (by
    simp only [BlockMix.others,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)

theorem Meta.pin {s₀ s : State} {out : Addr} (h : Meta s₀ out s) {r : Reg}
    (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24) :
    s.gpr r = s₀.gpr r := h.keep r (pin_ne hr).1 (pin_ne hr).2

theorem load_inv {s₀ : State} (hp : BlockMix.Pre s₀) {s : State} (h : BlockMix.Inv s₀ 0 s) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.load) s (Inv s₀ 0) := by
  have hi : ∀ j < 16, InRegions (s.rd ++ s.wr) (addr (s.gpr .x24) j) 4 := by
    intro j hj
    rw [h.rd,h.wr,h.x24,hp.rd,hp.wr]
    simp only [BlockMix.xP,addr]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_b hp (by have := hp.pos; omega))
  refine WP.mono (load_ok s hi) fun s' u => ?_
  have eq (r : Reg) (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24) :
      s'.gpr r = s.gpr r := u.keep r (pin_ne hr).1
  refine ⟨⟨h.k_le,u.rd.trans h.rd,u.wr.trans h.wr,u.sp.trans h.sp,
    (eq _ (by simp)).trans h.x19,(eq _ (by simp)).trans h.x20,(eq _ (by simp)).trans h.x21,
    (eq _ (by simp)).trans h.x22,(eq _ (by simp)).trans h.x23,(eq _ (by simp)).trans h.x24,
    fun r hr => (u.keep r (other_ne hr).1).trans (h.keep r hr),?_,?_,?_,?_⟩,?_⟩
  · rw [u.mem]; exact h.frame
  · rw [u.mem]; exact h.saved
  · rw [u.mem]; exact h.done
  · rw [u.mem]; exact h.x
  · intro j hj
    simpa only [u.mem,h.x24] using u.holds j hj hj

theorem tail_holds {s : State} (hh : Holds (words s.mem (s.gpr .x21)) s) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.tail) s fun s' => s'.mem = s.mem ∧
      Holds (words s'.mem (s.gpr .x21)) s' := by
  refine wp_mov fun a ua => wp_addImm (by decide) fun b ub => wp_addImm (by decide) fun c uc =>
    wp_addImm (by decide) fun d ud => wp_subImm (by decide) fun e ue => WP.block_nil ?_
  have hm : e.mem = s.mem := by rw [ue.mem,ud.mem,uc.mem,ub.mem,ua.mem]
  refine ⟨hm,fun j hj => ?_⟩
  have hn : wreg j ≠ .x19 ∧ wreg j ≠ .x20 ∧ wreg j ≠ .x21 ∧ wreg j ≠ .x23 ∧ wreg j ≠ .x24 := by
    have h : ∀ j, j < 16 → wreg j ≠ .x19 ∧ wreg j ≠ .x20 ∧ wreg j ≠ .x21 ∧ wreg j ≠ .x23 ∧ wreg j ≠ .x24 := by decide
    exact h j hj
  rw [ue.other _ hn.2.2.2.1,ud.other _ hn.2.2.1,uc.other _ hn.2.1,ub.other _ hn.1,ua.other _ hn.2.2.2.2,hm]
  exact hh j hj

theorem body_ok {s₀ : State} (hp : BlockMix.Pre s₀) {k : Nat} (hk : k < BlockMix.rr s₀)
    {s : State} (h : Inv s₀ k s) : WP isa VG.Impl.Scrypt.AArch64.Resident.body s (Inv s₀ (k+1)) := by
  have oe : 64*k+64 ≤ 128*BlockMix.rr s₀ := by omega
  have oo : 64*(BlockMix.rr s₀+k)+64 ≤ 128*BlockMix.rr s₀ := by omega
  have ib : ∀ j < 16, InRegions (s.rd ++ s.wr) (addr (BlockMix.bB s₀ k) j) 4 := by
    intro j hj
    rw [h.rd,h.wr,hp.rd,hp.wr]
    simp only [addr,BlockMix.bB]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_b hp (by omega))
  have ow : ∀ j < 16, InRegions s.wr (addr (BlockMix.yE s₀ k) j) 4 := by
    intro j hj
    rw [h.wr,hp.wr]
    simp only [addr,BlockMix.yE]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_y hp (by omega))
  refine WP.seq (WP.mono (step_ok (by simp) h.x19 h.x20
    ((hp.b_y.sub_left (BlockMix.b_sub hp (by omega))).sub_right (BlockMix.y_sub hp oe)) ib ow h.holds)
    fun a ⟨ma,ha,ba⟩ => ?_)
  refine WP.seq (wp_addImm (by decide) fun b ub => WP.block_nil ?_)
  have b19 : b.gpr .x19 = BlockMix.bP s₀ + BitVec.ofNat 64 (64*(2*k+1)) := by
    rw [ub.gpr,ma.pin (by simp),h.x19,add_ofNat]
    congr 2; omega
  have b21 : b.gpr .x21 = BlockMix.yO s₀ k := by rw [ub.other _ (by decide),ma.pin (by simp),h.x21]
  have hb : Holds (words b.mem (BlockMix.yE s₀ k)) b := by
    intro j hj
    have ne : wreg j ≠ .x19 := fun e => (pin_ne (r := .x19) (by simp)).1 ⟨j,hj,e.symm⟩
    rw [ub.other _ ne,ub.mem]
    exact ha j hj
  have ib' : ∀ j < 16, InRegions (b.rd ++ b.wr) (addr (BlockMix.bP s₀ + BitVec.ofNat 64 (64*(2*k+1))) j) 4 := by
    intro j hj
    rw [ub.rd,ub.wr,ma.rd,ma.wr,h.rd,h.wr,hp.rd,hp.wr]
    simp only [addr]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_b hp (by omega))
  have ow' : ∀ j < 16, InRegions b.wr (addr (BlockMix.yO s₀ k) j) 4 := by
    intro j hj
    rw [ub.wr,ma.wr,h.wr,hp.wr]
    simp only [addr,BlockMix.yO]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_y hp (by omega))
  refine WP.seq (WP.mono (step_ok (by simp) b19 b21
    ((hp.b_y.sub_left (BlockMix.b_sub hp (by omega))).sub_right (BlockMix.y_sub hp oo)) ib' ow' hb)
    fun c ⟨mc,hc,bc⟩ => ?_)
  have f1 : Frame [BlockMix.slot s₀ (64*k),⟨BlockMix.sc s₀,64⟩] s.mem a.mem := ma.frame.mono (by simp [BlockMix.slot])
  have f2 : Frame [BlockMix.slot s₀ (64*(BlockMix.rr s₀+k)),⟨BlockMix.sc s₀,64⟩] a.mem c.mem := by
    rw [← ub.mem]; exact mc.frame.mono (by simp [BlockMix.slot])
  rw [ub.mem] at bc
  obtain ⟨ff,ss,dd⟩ := BlockMix.mem_ok hp hk h.toInv f1 ba f2 bc
  have kee (r : Reg) (hr : r ≠ .x19) (hw : ¬ Words r) (hn : r ≠ .x1) : c.gpr r = s.gpr r := by
    rw [mc.keep r hw hn,ub.other r hr,ma.keep r hw hn]
  have mid : BlockMix.Mid s₀ k c := ⟨mc.rd.trans (ub.rd.trans (ma.rd.trans h.rd)),
    mc.wr.trans (ub.wr.trans (ma.wr.trans h.wr)),mc.sp.trans (ub.sp.trans (ma.sp.trans h.sp)),
    (mc.pin (by simp)).trans b19,by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x20],
    by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x21],
    by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x22],
    by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x23],
    fun r hr => (kee r (by simpa [BlockMix.others] using fun e => by subst r; simp [BlockMix.others] at hr)
      (other_ne hr).1 (other_ne hr).2).trans (h.keep r hr),ff,ss,dd⟩
  have ht : Holds (words c.mem (c.gpr .x21)) c := by rw [mid.x21]; exact hc
  exact WP.mono ((BlockMix.regs_ok hp hk mid).and (tail_holds ht)) fun s' ⟨hi,_,hh⟩ =>
    ⟨hi,by simpa only [BlockMix.xP,mid.x21] using hh⟩
end VG.Proof.Scrypt.AArch64.Resident
