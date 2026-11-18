module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHeadCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBodyCT
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRunContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBodyCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! ### `Bignum.AArch64.CrtWindowGroupsCT`, which only this module used -/

section

/-! Complete groups iterate a public number of times. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (groupBody expGroups)

theorem groups_loop_ct (W : Window) :
    RelCT isa (Two fun p s => 0 < p.len/5 ∧ RunInv p 0 0 s)
      (.loop (groupBody W.code) (.nonzero .x .x9)) (fun _ _ => True) := by
  refine (two_loop (Φ := fun p j => RunInv p (5*j) 0) (Ψ := fun p => RunInv p (5*(p.len/5)) 0)
    (fun p : RunPub => p.len/5) ?_ ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact two_map (fun p : RunPub × Nat => (p.1,5*p.2))
      (fun _ _ h => ⟨by dsimp; omega,h.2⟩) (groupBody_ct W)
  · intro p j s hj hs
    refine WP.mono (hs.groupStep W (by omega_using [hj])) fun t ⟨ht,h9⟩ => ?_
    have hnext : RunInv p (5*(j+1)) 0 t := by simpa only [Nat.mul_add,Nat.mul_one] using ht
    refine ⟨?_,fun _ => hnext,fun he => by simpa only [he] using hnext⟩
    change some (!(t.gpr .x9 == 0)) = some (decide (j+1 < p.len/5))
    rw [h9]
    by_cases he : 5*j+10 ≤ p.len
    · simp only [he,ite_true,show j+1 < p.len/5 by omega_using [he],decide_true]; rfl
    · simp only [he,ite_false,show ¬ j+1 < p.len/5 by omega_using [he],decide_false]; rfl

def GroupsReady (p : RunPub) (s : State) : Prop :=
  RunInv p 0 0 s ∧ s.gpr .x9 = if 5 ≤ p.len then 1 else 0

theorem expGroups_ct (W : Window) :
    RelCT isa (Two fun p => RunInv p 0 0) (expGroups W.code) (fun _ _ => True) := by
  unfold expGroups
  refine RelCT.seq (two_post (Ψ := GroupsReady)
    (x0_ct (fun p : RunPub => off p.ws.B p.ws.o) (fun _ _ h => h.x0) (by taint_decide))
    (fun _ _ h => WP.mono (h.haveFive (Nat.zero_le _)) fun _ ht => ⟨ht.1,by simpa only [Nat.zero_add] using ht.2⟩)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x9 == 0)) = some (!(t.gpr .x9 == 0))
    rw [hs.2,ht.2]
  · exact two_map id (fun p s ⟨hs,he⟩ => ⟨by
      change 0 < p.len/5
      by_contra hz
      have hn : ¬ 5 ≤ p.len := by omega_using [hz]
      change some (!(s.gpr .x9 == 0)) = some true at he
      rw [hs.2,ite_eq_right hn] at he
      contradiction,hs.1⟩) (groups_loop_ct W)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowTailsCT`, which only this module used -/

section

/-! The trailing-byte loop depends on public length, never exponent bits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (tailBody expTail)

theorem tails_loop_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat) s => 0 < p.1.len-p.2 ∧ RunInv p.1 p.2 0 s)
      (.loop (tailBody W.code) (.nonzero .x .x3)) (fun _ _ => True) := by
  refine (two_loop (Φ := fun (p : RunPub × Nat) j => RunInv p.1 (p.2+j) ((8*j)%5))
    (Ψ := fun _ _ => True) (fun p : RunPub × Nat => p.1.len-p.2) ?_ ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact two_map (fun p : (RunPub × Nat) × Nat => (p.1.1,p.1.2+p.2,(8*p.2)%5))
      (fun _ _ h => ⟨by dsimp; omega,h.2⟩) (tailBody_ct W)
  · intro p j s hj hs
    have hL : p.1.len < 2 ^ 64 := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hL,_⟩ := hs
      exact hL
    refine WP.mono (hs.tailStep W (by omega_using [hj])) fun t ⟨ht,h3⟩ => ?_
    refine ⟨?_,?_,fun _ => trivial⟩
    · exact eval_nz_count hj (by rw [h3,cnt_ne (by omega_using [hL])]; omega_using [hj])
    · intro _
      have hb : ((8*j)%5+8)%5 = (8*(j+1))%5 := by omega_using []
      simpa only [hb,Nat.add_assoc] using ht

def TailsReady (p : RunPub × Nat) (s : State) : Prop :=
  p.2 ≤ p.1.len ∧ RunInv p.1 p.2 0 s ∧ s.gpr .x3 = BitVec.ofNat 64 (p.1.len-p.2)

theorem expTail_ct (W : Window) :
    RelCT isa (Two fun (p : RunPub × Nat) s => p.2 ≤ p.1.len ∧ RunInv p.1 p.2 0 s)
      (expTail W.code) (fun _ _ => True) := by
  unfold expTail
  refine RelCT.seq (two_post (Ψ := TailsReady)
    (x0_ct (fun p : RunPub × Nat => off p.1.ws.B p.1.ws.o) (fun _ _ h => h.2.x0) (by taint_decide))
    (fun _ _ h => WP.mono (h.2.remaining h.1) fun _ h' => ⟨h.1,h'⟩)) ?_
  refine two_ite ?_ ?_ ?_
  · intro p s t hs ht
    change some (!(s.gpr .x3 == 0)) = some (!(t.gpr .x3 == 0))
    rw [hs.2.2,ht.2.2]
  · exact two_map id (fun p s ⟨hs,he⟩ => ⟨by
      change 0 < p.1.len-p.2
      by_contra hz
      have hn : p.1.len-p.2 = 0 := by omega_using [hz]
      change some (!(s.gpr .x3 == 0)) = some true at he
      rw [hs.2.2,hn] at he
      contradiction,hs.2.1⟩) (tails_loop_ct W)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowRunCT`, which only this module used -/

section

/-! Constant time for the complete exponent, including both tails. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (expRun)

theorem expRun_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p => RunInv p 0 0) (expRun W.code M.mm S.code) (fun _ _ => True) := by
  unfold expRun
  refine RelCT.seq (two_post (Ψ := fun p => RunInv p (5*(p.len/5)) 0)
    (expGroups_ct W) (fun _ _ h => h.groups W)) ?_
  refine RelCT.seq (two_post (Ψ := fun p => RunInv p p.len ((8*(p.len-5*(p.len/5)))%5))
    (two_map (fun p : RunPub => (p,5*(p.len/5)))
      (fun _ _ h => ⟨by dsimp; omega_using [],h⟩) (expTail_ct W))
    (fun _ _ h => h.tails W (by omega_using []))) ?_
  exact two_map (fun p : RunPub => (p.ws,(8*(p.len-5*(p.len/5)))%5))
    (fun _ _ h => h.finish) (finish_ct M S)

end VG.Proof.Bignum.AArch64.WindowFive

end

end


/-! Constant time for wider-table prime exponentiation under the existing key bounds. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt (ldw)

def runPub (a : BPub) : RunPub := ⟨a.x,a.ptr,a.len⟩

theorem expHead_post (M : Mont) {sp sl : Nat} {a : BPub} {s : State}
    (h : EPreWide sp sl a s) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expHead M.mm sp sl) s (RunInv (runPub a) 0 0) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨mi,X,x,y,bs,hctx,hw2,hwx,hw30,hn,hinv,hodd,hxl,_,hyl,_,hsp,hsl,hep,hel,hL,_,hL2,he⟩ := h
  have hT : Scr s (off a.x.B a.x.o) (slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx) :=
    hctx.scr.sub (by omega_using [hwide]) (by unfold slot hdrBytes; omega_using [])
  have hout : ∀ i < bs.length, slot a.x.wx 8 + CrtWindowFive.tabBytes32 a.x.wx ≤
      ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i) := by
    intro i hi
    have := he.out i hi
    have hn := hctx.scr.nowrap
    have hp := hT.nowrap
    have hslot : 0 < slot a.x.wx 8 := by unfold slot hdrBytes; omega_using []
    rcases ofs_rebase a.x.B (a.ptr + BitVec.ofNat 64 i) (o := a.x.o) (by omega_using [hwide, hn, hslot]) with ⟨_,h2⟩ | ⟨h1,_⟩
    · omega_using [hwide, this, h2]
    · omega_using [hwide, this, h1]
  refine WP.mono (expHead_ok M (Q := False) (x := 0) hctx hT hw2 hwx hw30 hn hinv hodd
    hxl False.elim hyl False.elim hsp hsl hep hel) fun t ht => ?_
  exact ⟨s,mi,X,_,bs,ht,hw2,by dsimp [runPub]; omega_using [hwx, hw30],VG.Proof.Bignum.coprime_pow2 hodd _,hL,by dsimp [runPub]; omega,
    he.rd,he.val,hout⟩

theorem expLoop_ct (W : Window) (M : Mont) (S : Selector) {sp sl : Nat}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0,.x5]) (.block [ldw .x3 .x5 sp,sth .x3 Crt.sExp,
      ldw .x3 .x5 sl,sth .x3 Crt.sExpLen,movi .x3 0,sth .x3 Crt.sI]) hc).isSome = true) :
    RelCT isa (Two (EPreWide sp sl))
      (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.expLoop
  exact RelCT.seq (two_post (Ψ := fun a => RunInv (runPub a) 0 0) (expHead_ct M hT)
    (fun _ _ h => expHead_post M h)) (two_map runPub (fun _ _ h => h) (expRun_ct W M S))

end VG.Proof.Bignum.AArch64.WindowFive
