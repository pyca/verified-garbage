module

public import VerifiedGarbage.Proof.Rsa.X86.RvArguments

/-! # The public bound on the exponent's bit count -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem KS.cntBits_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {eLen dLen : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (bound : 8 * (dLen + eLen) < 2 ^ 32) :
    WP isa (.block cntBits) s fun t =>
      KS g s0 A live AW liveW (upd V sCnt (8 * (dLen + eLen))) (sCnt :: ls) t := by
  unfold cntBits
  refine wp_movS (h.argument ae).readSrc fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_addS (hu.argument ad).readSrc fun v D _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  refine wp_addS rfl fun x X _ => ?_
  refine wp_addS rfl fun y Y _ => ?_
  have hy := (((hu.of_rest D.keeps (by decide) D.mem).of_rest W.keeps (by decide) W.mem).of_rest
    X.keeps (by decide) X.mem).of_rest Y.keeps (by decide) Y.mem
  have value : y.gpr .eax = BitVec.ofNat 32 (8 * (dLen + eLen)) := by
    rw [Y.gpr, X.gpr, W.gpr, D.gpr, U.gpr]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  refine WP.mono (hy.storeSlot (d := sCnt) (by decide) .eax) fun t ⟨ht, _, _⟩ => ?_
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at ht
  exact ht

end VG.Proof.Rsa.X86.Recover
