module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRanges
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Framed
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Preserve
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Arbitrary odd public exponents use one remainder and a fixed native gcd -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentFilter

theorem general_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Scr s base size) (width : 4 ≤ w)
    (space : slot w 5 + 8 * w ≤ size)
    (saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1)
    (large : 1 < candidate) (cOdd : candidate % 2 = 1)
    (eValue : Mod64.exponentValue s.mem base 128 = exponent) (eOdd : exponent % 2 = 1)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa (general w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) exponent = 1)).toNat ∧
      val32 t.mem base (slot w 0) (2 * w) = candidate ∧
      Frame [⟨base, size⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem := by
  have sizeBound : 400 ≤ size := by simp only [slot, stride, VG.Impl.Bignum.hdrBytes] at space; omega
  have savedLo : 400 ≤ slot w 5 := by simp only [slot, stride, VG.Impl.Bignum.hdrBytes]; omega
  have dstLo : 256 ≤ slot w 0 := by simp only [slot, stride, VG.Impl.Bignum.hdrBytes]; omega
  have sep : slot w 0 + 4 * (2 * w) ≤ slot w 5 := by simp only [slot, stride, VG.Impl.Bignum.hdrBytes]; omega
  unfold general
  refine WP.seq (WP.mono (Mod64.framed_ok S (by omega) (by omega) (by omega) saved eValue
    (by omega) fit separate) fun a ⟨Sa, remainder, savedA, eA, Fa, Ka⟩ => ?_)
  refine WP.mono (Gcd64.preserving_ok Sa sizeBound (by omega) (by decide) (by rw [eA]; exact eOdd)
    (by omega) (by omega) (by omega) dstLo savedLo sep (by rw [savedA]; omega))
    fun t ⟨result, restored, O, K⟩ => ?_
  rw [show 4 * (2 * w) = 8 * w by omega] at O
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))
  have Wa : WorkspaceFrame ⟨base, size, w⟩ [] s.mem a.mem :=
    workspace_of_frame Fa S.nowrap (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far)
  have Wb : WorkspaceFrame ⟨base, size, w⟩ (ranges w) a.mem t.mem := WorkspaceFrame.of_outs S.nowrap O
  refine ⟨?_, ?_, ?_, (Ka.mono (by decide)).trans (K.mono (by decide)),
    (Wa.mono (by intro r mem; nomatch mem)).trans Wb⟩
  · rw [remainder, eA] at result
    have gcdEq : Nat.gcd ((candidate - 1) % exponent) exponent = Nat.gcd (candidate - 1) exponent :=
      (Nat.gcd_rec exponent (candidate - 1)).symm.trans (Nat.gcd_comm _ _)
    simpa only [gcdEq] using result
  · rw [restored, savedA]; omega
  · have Fb : Frame [⟨base, size⟩] a.mem t.mem := workspaceGlobalFrame
      (g := ⟨base, size, 0⟩) O (by
        intro r mem
        change r.1 + r.2 ≤ size
        rcases List.mem_append.mp mem with mem | mem
        · exact Nat.le_trans (Gcd64.ranges_below mem) sizeBound
        · obtain rfl := List.mem_singleton.mp mem; omega)
    exact (Fa.mono (fun _ mem => List.mem_cons_of_mem _ mem)).trans
      (Fb.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self))

end VG.Proof.RsaKeyGen.X86.ExponentFilter
