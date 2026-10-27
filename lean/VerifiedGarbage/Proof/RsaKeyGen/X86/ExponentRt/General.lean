module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRanges
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Check
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Array
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Setup
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Result
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Preserve
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # An arbitrary odd public exponent: one remainder and a fixed native gcd, at a run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt
open VG.Proof.RsaKeyGen.X86 (Gcd64.checkRanges)

/-- Setting up and running the gcd keep the length in the header. -/
theorem gcd_keep_ok {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (width : 4 ≤ w) (space : slot w 5 + 8 * w ≤ size)
    (odd : Mod64.exponentValue s.mem base 128 % 2 = 1) :
    WP isa (.seq (.block (VG.Impl.RsaKeyGen.X86.Gcd64.setup 128)) VG.Impl.RsaKeyGen.X86.Gcd64.code) s fun t =>
      Scr t base size ∧ t.mem.readW (off base 4) 32 = s.mem.readW (off base 4) 32 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have lo' := slot5_eq w
  refine WP.seq (WP.mono (Gcd64.setup_ok scratch (by omega) (by omega) (by decide)) fun a ⟨Wa, R, E, Oa, Ka⟩ => ?_)
  refine WP.mono (Gcd64.code_ok Wa (by decide) (by rw [E]; exact odd)) fun b ⟨Wb, F, Kb, V⟩ => ?_
  have Ftotal : Outs base Gcd64.checkRanges s.mem b.mem :=
    (Outs.of_outside Oa (List.mem_append_left _ (List.mem_singleton_self _))).trans
      (Outs.mono F (fun _ mem => List.mem_append_right _ mem))
  have h := Ftotal.val32 (d := 4) (k := 1)
    (fun r mem => Or.inl (by have := ExponentFilter.gcd_ranges_class mem; omega)) (by have := scratch.nowrap; omega)
  simp only [val32, w32, Nat.mul_zero, Nat.add_zero] at h
  exact ⟨Wb.workspace, BitVec.eq_of_toNat_eq h, (Ka.mono (by decide)).trans (Kb.mono (by decide))⟩

theorem preserving_ok {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64) (space : slot w 5 + 8 * w ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : Mod64.exponentValue s.mem base 128 % 2 = 1)
    (even : val32 s.mem base (slot w 5) (2 * w) % 2 = 0) :
    WP isa (.seq (.block (VG.Impl.RsaKeyGen.X86.Gcd64.setup 128)) (.seq VG.Impl.RsaKeyGen.X86.Gcd64.code
      (.seq restore (.block VG.Impl.RsaKeyGen.X86.Gcd64.result)))) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (Mod64.pair (s.gpr .ecx) (s.gpr .ebx))
        (Mod64.exponentValue s.mem base 128) = 1)).toNat ∧
      val32 t.mem base (slot w 0) (2 * w) = val32 s.mem base (slot w 5) (2 * w) + 1 ∧
      Outs base (Gcd64.checkRanges ++ [(slot w 0, 8 * w)]) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have lo := slot5_ge w
  have lo' := slot5_eq w
  have space' : 400 ≤ size := by omega
  refine WP.seq (WP.mono (Gcd64.setup_ok scratch space' (by omega) (by decide)) fun a ⟨Wa, R, E, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Gcd64.code_ok Wa (by decide) (by rw [E]; exact odd)) fun b ⟨Wb, F, Kb, V⟩ => ?_)
  have Ftotal : Outs base Gcd64.checkRanges s.mem b.mem :=
    (Outs.of_outside Oa (List.mem_append_left _ (List.mem_singleton_self _))).trans
      (Outs.mono F (fun _ mem => List.mem_append_right _ mem))
  have savedValue : val32 b.mem base (slot w 5) (2 * w) = val32 s.mem base (slot w 5) (2 * w) :=
    Ftotal.val32 (fun r mem => Or.inr (by have := Gcd64.ranges_below mem; omega))
      (by have := scratch.nowrap; omega)
  have lenB : b.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
    have h := Ftotal.val32 (d := 4) (k := 1)
      (fun r mem => Or.inl (by have := ExponentFilter.gcd_ranges_class mem; omega)) (by omega)
    simp only [val32, w32, Nat.mul_zero, Nat.add_zero] at h
    exact (BitVec.eq_of_toNat_eq h).trans len
  refine WP.seq (WP.mono (restore_ok Wb.workspace width hw space lenB (by rw [savedValue]; exact even))
    fun c ⟨restored, Oc, Kc⟩ => ?_)
  rw [slot0_eq] at restored Oc
  refine WP.mono (Gcd64.result_ok (Wb.workspace.of_keeps Kc (by decide)) (by omega))
    fun t ⟨test, M, Kt⟩ => ?_
  have bank : num c.mem base 2 1 = num b.mem base 2 1 :=
    Oc.val32 (Or.inl (by change 176 + 4 * 2 ≤ 256; omega)) (by change 176 + 4 * 2 ≤ 2 ^ 64; decide)
  change t.gpr .eax = BitVec.ofNat 32 (decide (num c.mem base 2 1 = 1)).toNat at test
  rw [bank, V, R, E] at test
  refine ⟨test, ?_, ?_, ?_⟩
  · rw [M, slot0_eq, restored, savedValue]
  · rw [M, slot0_eq]
    exact (Ftotal.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (Outs.of_outside Oc (List.mem_append_right _ (List.mem_singleton_self _)))
  · have K1 : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s b := ((Ka.mono (by decide)).trans Kb).mono (by decide)
    exact (K1.trans (Kc.mono (by decide))).widen Kt

theorem general_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1)
    (large : 1 < candidate) (cOdd : candidate % 2 = 1)
    (eValue : Mod64.exponentValue s.mem base 128 = exponent) (eOdd : exponent % 2 = 1)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa general s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) exponent = 1)).toNat ∧
      val32 t.mem base (slot w 0) (2 * w) = candidate ∧
      Frame [⟨base, size⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      WorkspaceFrame ⟨base, size, w⟩ (ExponentFilter.ranges w) s.mem t.mem := by
  have sizeBound : 400 ≤ size := by have := slot5_eq w; omega
  unfold general
  refine WP.seq (WP.mono (framed_ok S width hw space len saved eValue (by omega) fit separate)
    fun a ⟨Sa, remainder, savedA, eA, Fa, Ka⟩ => ?_)
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))
  have lenA : a.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
    rw [← len]
    exact Fa.readW (r := ⟨base, size⟩) (Offset.contains_base _ (by omega) (by have := S.nowrap; omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far) (by decide)
  refine WP.mono (preserving_ok Sa width hw space lenA (by rw [eA]; exact eOdd) (by rw [savedA]; omega))
    fun t ⟨result, restored, O, K⟩ => ?_
  have Wa : WorkspaceFrame ⟨base, size, w⟩ [] s.mem a.mem :=
    VG.Proof.RsaKeyGen.X86.workspace_of_frame Fa S.nowrap
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far)
  have Wb : WorkspaceFrame ⟨base, size, w⟩ (ExponentFilter.ranges w) a.mem t.mem := WorkspaceFrame.of_outs S.nowrap O
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
        · obtain rfl := List.mem_singleton.mp mem; have := slot5_ge w; simp only [slot0_eq]; omega)
    exact (Fa.mono (fun _ mem => List.mem_cons_of_mem _ mem)).trans
      (Fb.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self))

end VG.Proof.RsaKeyGen.X86.ExponentRt
