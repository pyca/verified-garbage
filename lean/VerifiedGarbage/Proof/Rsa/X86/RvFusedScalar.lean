module

import VerifiedGarbage.Proof.Rsa.X86.RvFusedMasks
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFlags
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
public import Aesop.BuiltinRules
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass

/-! Reading a bit of a four-bit window, and restarting the root-search flag. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.KeyBits32
open VG.Proof.Rsa (b2n)

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}

theorem KS.fusedBitHead_ok (h : KS g s0 A live AW liveW V ls s)
    (lw : sWin ∈ ls) (small : V sWin < 16) (k : Nat) (hk : k ≤ 3) :
    WP isa (.block (VG.Impl.Rsa.X86.RecoverRt.fusedBitHead k)) s fun t =>
      KS g s0 A live AW liveW (upd V sBit (V sWin / 2^k % 2)) (sBit::ls) t := by
  have finish {u : State} (hu : KS g s0 A live AW liveW V ls u)
      (value : u.gpr .eax = BitVec.ofNat 32 (V sWin) >>> k) :
      WP isa (.block [.alu .and .eax (.imm 1), .store (VG.Impl.Mont.X86.sc sBit) .eax]) u fun t =>
        KS g s0 A live AW liveW (upd V sBit (V sWin / 2^k % 2)) (sBit::ls) t := by
    refine wp_logicS (.inl rfl) rfl fun v D => ?_
    have hv := hu.of_rest D.keeps (by decide) D.mem
    have number : (v.gpr .eax).toNat = V sWin / 2^k % 2 := by
      rw [D.gpr, ite_eq_left rfl, value, bv_and_one, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show V sWin < 2^32 by omega)]
    refine WP.block_append (WP.mono (hv.storeSlot (d := sBit) (by decide) .eax)
      fun t ⟨ht,_,_⟩ => ?_)
    rw [number] at ht
    exact WP.block_nil ht
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedBitHead
  refine wp_movS (h.readSlot lw) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  by_cases zero : k = 0
  · subst zero
    apply finish hu
    rw [U.gpr]
    rfl
  · rw [ite_eq_right zero]
    refine wp_shr (by omega) fun v D _ => ?_
    exact finish (hu.of_rest D.keeps (by decide) D.mem) (by rw [D.gpr,U.gpr])

theorem fusedTail_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat}
    {live liveW ls : List Nat} {dn bit e1 e2 : Bool}
    (h : KS g s0 A live AW liveW V (sE2::sE1::ls) s)
    (ld : sDone ∈ ls) (lb : sBit ∈ ls) (fresh : sE1 ∉ ls)
    (vd : V sDone = b2n dn) (vb : V sBit = b2n bit)
    (v1 : V sE1 = b2n e1) (v2 : V sE2 = b2n e2) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedTail s fun t =>
      KS g s0 A live AW liveW (upd V sDone (b2n (dn || ((e1 || e2) && bit))))
        (sDone::ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedTail
  simp only [seqs]
  refine WP.seq (WP.mono (h.flagOr_ok (d := sE1) (a := sE1) (b := sE2)
    (x := e1) (y := e2) (by decide) (by simp) (by simp) v1 v2) fun u hu => ?_)
  refine WP.seq (WP.mono (hu.flagAnd_ok (d := sE1) (a := sE1) (b := sBit)
    (x := e1 || e2) (y := bit) (by decide) (by simp) (by simp [lb]) rfl vb) fun v hv => ?_)
  refine WP.mono (hv.flagOr_ok (d := sDone) (a := sDone) (b := sE1)
    (x := dn) (y := (e1 || e2) && bit) (by decide) (by simp [ld]) (by simp) vd rfl) fun t ht => ?_
  refine ht.mono (fun j hj => ⟨hj,rfl⟩) (fun j hj => ⟨hj,rfl⟩) fun d hd => ⟨?_, ?_⟩
  · rcases List.mem_cons.mp hd with rfl | hd
    · simp
    · simp [hd]
  ·
    by_cases e : d = sDone
    · subst e; rfl
    · have old : d ∈ ls := (List.mem_cons.mp hd).resolve_left e
      have ne : d ≠ sE1 := by intro eq; subst eq; exact fresh old
      simp only [upd_ne _ _ e, upd_ne _ _ ne]

end
end VG.Proof.Rsa.X86.Recover
