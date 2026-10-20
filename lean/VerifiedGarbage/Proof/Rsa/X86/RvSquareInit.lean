module

import VerifiedGarbage.Proof.Rsa.X86.RvCountInit
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Initializing the masked squaring search -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

theorem sqInit_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {eLen dLen : Nat}
    {e1 e2 : Bool} (h : KS g s0 A live AW liveW V ls s) (l1 : sE1 ∈ ls) (l2 : sE2 ∈ ls)
    (v1 : V sE1 = b2n e1) (v2 : V sE2 = b2n e2)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (bound : 8 * (dLen + eLen) < 2 ^ 32) :
    WP isa (.block sqInit) s fun t =>
      KS g s0 A live AW liveW
        (upd (upd (upd (upd V sDone (b2n (e1 || e2))) sOk 0) sK 0) sCnt (8 * (dLen + eLen)))
        (sCnt :: sK :: sOk :: sDone :: ls) t := by
  unfold sqInit
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (h.readSlot l1) fun s1 U1 _ => ?_
  have h1 := h.of_rest U1.keeps (by decide) U1.mem
  refine wp_orS (h1.readSlot l2) fun s2 U2 => ?_
  have h2 := h1.of_rest U2.keeps (by decide) U2.mem
  have done : (s2.gpr .eax).toNat = b2n (e1 || e2) := by
    rw [U2.gpr, U1.gpr, v1, v2]
    cases e1 <;> cases e2 <;> rfl
  refine WP.block_append (WP.mono (h2.storeSlot (d := sDone) (by decide) .eax)
    fun s3 ⟨h3, _, _⟩ => ?_)
  rw [done] at h3
  refine wp_movS rfl fun s4 U4 _ => ?_
  have h4 := h3.of_rest U4.keeps (by decide) U4.mem
  refine WP.block_append (WP.mono (h4.storeSlot (d := sOk) (by decide) .eax)
    fun s5 ⟨h5, _, R5⟩ => ?_)
  rw [U4.gpr] at h5
  refine WP.block_append (WP.mono (h5.storeSlot (d := sK) (by decide) .eax)
    fun s6 ⟨h6, _, _⟩ => ?_)
  rw [R5.1 .eax (by decide), U4.gpr] at h6
  exact h6.cntBits_ok ae ad bound

end VG.Proof.Rsa.X86.Recover
