module

-- separate module: Isolate instruction-level initialization of the sixteen mask slots from the AES subroutine proof.

public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset

/-! # Initialize the contiguous RISC-V seal mask blocks -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64.Contiguous
open VG.Spec.Gcm (blockAt blocksAt Block)

abbrev maskSlot (w : Addr) (i : Nat) := w+BitVec.ofNat 64 (256+16*i)

structure Cleared (s : State) (n : Nat) (t : State) : Prop where
  state : t = { s with mem := t.mem }
  blocks : ∀ i < n, blockAt t.mem (maskSlot (s.gpr .s0) i) = 0
  frame : Frame [⟨s.gpr .s0+256,256⟩] s.mem t.mem

private theorem clearPair {v : State} {w : Addr} {i : Nat} (ptr : v.gpr .s0=w) (zero : v.gpr .t0=0)
    (al : w.toNat%8=0) (wr : Covers [⟨w,2560⟩] v.wr) (hi : i<16) :
    let a := maskSlot w i
    let m := (v.mem.writeW a (0 : BitVec 64)).writeW (a+8) (0 : BitVec 64)
    WP isa (.block [.store .d .t0 .s0 (256+16*i),.store .d .t0 .s0 (264+16*i)]) v
      (· = {v with mem := m}) := by
  let a := maskSlot w i
  have e : a+8=w+BitVec.ofNat 64 (264+16*i) := by
    change (w+BitVec.ofNat 64 (256+16*i))+BitVec.ofNat 64 8=_
    rw [add_ofNat_assoc]; congr 2; omega
  apply Steps.WP.cons (s' := {v with mem := v.mem.writeW a (0 : BitVec 64)})
  · rw [exec_store_d (by omega) (by rw [ptr]; exact Spill.al8 al (by omega)) (by rw [ptr]; exact in_off wr (by omega) (by decide)),ptr,zero]
  apply Steps.WP.cons (s' := {v with mem := (v.mem.writeW a (0 : BitVec 64)).writeW (a+8) (0 : BitVec 64)})
  · rw [exec_store_d (by omega) (by change (v.gpr .s0+_).toNat%8=0; rw [ptr]; exact Spill.al8 al (by omega))
      (by change InRegions v.wr (v.gpr .s0+_) 8; rw [ptr]; exact in_off wr (by omega) (by decide))]
    simp only [ptr,zero,e]
  exact WP.block_nil rfl

theorem maskZero_wp {s : State} (zero : s.gpr .t0=0) (al : (s.gpr .s0).toNat%8=0)
    (wr : Covers [⟨s.gpr .s0,2560⟩] s.wr) {n : Nat} (bound : n≤16) :
    WP isa (.block (maskZero n)) s (Cleared s n) := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl,by omega,Frame.refl _ _⟩
  | succ i ih =>
    have lt : i < 16 := by omega
    have split : maskZero (i+1) = maskZero i ++ [.store .d .t0 .s0 (256+16*i),.store .d .t0 .s0 (264+16*i)] := by
      simp [maskZero,List.range_succ]
    rw [split,WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun v done => ?_
    have gr : v.gpr=s.gpr := by rw [done.state]
    have perm : v.wr=s.wr := by rw [done.state]
    refine WP.mono (clearPair (i := i) (congrFun gr .s0) ((congrFun gr .t0).trans zero) al (perm ▸ wr) lt) fun u eq => ?_
    let w := s.gpr .s0
    let a := maskSlot w i
    have step : Frame [⟨a,16⟩] v.mem u.mem := by rw [eq]; exact Proof.Cmac.frame_store2 _ _ _
    refine ⟨?_,fun j hj => ?_,done.frame.trans (step.sub ?_)⟩
    · rw [eq]; exact congrArg (fun q : State => {q with mem := (v.mem.writeW a (0 : BitVec 64)).writeW (a+8) (0 : BitVec 64)}) done.state
    · rcases Nat.lt_or_ge j i with before | last
      · rw [blockAt_frame step (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint w (d := 256+16*j) (e := 256+16*i) (n := 16) (k := 16) (.inl (by omega)) (by omega) (by omega))]
        exact done.blocks j before
      · obtain rfl : j=i := by omega
        rw [eq,blockAt]; exact (congrArg Spec.Gcm.ofBytes (zeroT_bytes v.mem a)).trans Proof.Gcm.ofBytes_zeros16
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_,List.mem_singleton_self _,?_⟩
      have e : a = (w+256)+BitVec.ofNat 64 (16*i) := by
        change maskSlot w i=w+BitVec.ofNat 64 256+BitVec.ofNat 64 (16*i)
        rw [add_ofNat_assoc]
      rw [e]
      exact Offset.sub_base _ (by omega)

theorem Cleared.prefix {s t : State} {n : Nat} (clear : Cleared s n t) {k : Nat} (bound : k ≤ n) :
    blocksAt t.mem (s.gpr .s0+256) k = List.replicate k (0 : Block) := by
  apply List.ext_getElem (by simp [blocksAt])
  intro i hi _
  simp only [blocksAt,List.length_map,List.length_range] at hi
  simp only [blocksAt,List.getElem_map,List.getElem_range,List.getElem_replicate]
  rw [show (s.gpr .s0+256)+BitVec.ofNat 64 (16*i)=maskSlot (s.gpr .s0) i from add_ofNat_assoc _ 256 (16*i)]
  exact clear.blocks i (by omega)

end VG.Proof.AesGcm.RISCV64.Contiguous
