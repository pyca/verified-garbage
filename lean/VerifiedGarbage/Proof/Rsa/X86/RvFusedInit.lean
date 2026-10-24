module

import VerifiedGarbage.Proof.Rsa.X86.RvFusedWindow
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedState
import VerifiedGarbage.Proof.Rsa.X86.RvOps

/-! Initializing the fused search after aligning the full exponent. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

 theorem fusedInit_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n : Nat}
    (h : KS g s0 A liveExp AW [wRc,wR] V slotsExp s)
    (positive : 0<n) (zero : A aZ=0) (one : A mY=2^(64*g.n)%n) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedInit s fun t =>
      FI g s0 A AW (upd V sWin 0) n (VG.Proof.Rsa.Fused.start n 1) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedInit
  refine WP.seq (WP.mono (h.copy_w (o := 0) (a := aZ) (by decide) (by decide)
    (by decide) (by decide)) fun u ⟨hu,_,_⟩ => ?_)
  rw [zero] at hu
  refine wp_movS rfl fun v U _ => ?_
  have hv := hu.of_rest U.keeps (by decide) U.mem
  refine WP.block_append (WP.mono (hv.storeSlot (d := sDone) (by decide) .eax) fun u1 ⟨h1,_,_⟩ => ?_)
  rw [U.gpr,show (1 : BitVec 32).toNat=1 from rfl] at h1
  refine wp_movS rfl fun w W _ => ?_
  have hw := h1.of_rest W.keeps (by decide) W.mem
  refine WP.block_append (WP.mono (hw.storeSlot (d := sOk) (by decide) .eax) fun u2 ⟨h2,_,K⟩ => ?_)
  rw [W.gpr,show (0 : BitVec 32).toNat=0 from rfl] at h2
  refine WP.mono (h2.storeSlot (d := sWin) (by decide) .eax) fun t ⟨ht,_,_⟩ => ?_
  rw [K.1 _ (by decide),W.gpr,show (0 : BitVec 32).toNat=0 from rfl] at ht
  refine ⟨0,positive,(by intro r hr; cases hr),ht.mono
    (fun j hj => ⟨by revert j; decide,?_⟩) (fun j hj => ⟨hj,rfl⟩)
    (fun d hd => ⟨by revert d; decide,?_⟩)⟩
  · simp only [fusedKeep,liveM,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with (rfl|rfl) | rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change 0=0*2^(64*g.n)%n
      simp
    · change A mY=1*2^(64*g.n)%n
      simpa only [Nat.one_mul] using one
    all_goals rfl
  · simp only [fusedKeepSlots,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

 theorem FI.windowCount {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n eLen dLen : Nat}
    {st : VG.Proof.Rsa.Fused.State} (h : FI g s0 A AW V n st s)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen)) (bound : 8*(dLen+eLen)<2^32) :
    WP isa (.block windowCount) s fun t =>
      FI g s0 A AW (upd V sCnt (2*(dLen+eLen))) n st t := by
  obtain ⟨z,zl,root,h⟩ := h
  refine WP.mono (windowCount_ok h ae ad bound) fun t ht => ⟨z,zl,root,?_⟩
  refine ht.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd,?_⟩)
  simp only [fusedKeepSlots,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end VG.Proof.Rsa.X86.Recover
