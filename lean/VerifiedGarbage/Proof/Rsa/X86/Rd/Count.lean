module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Block

/-! # The loops' public counts in prime recovery by Appendix C.2 (i686)

Each loop counts its steps down in the header word `sK`, set from the
modulus's length: `32 w` (`countN`) or `32 W / 2` (`countW`); `countNext`
decrements it and sets ZF when it reaches zero, and `countLoop` runs a
body that keeps an invariant that many times.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.RecoverDetRt (sK countN countW countNext)
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem sK_ok : SlotOk sK := by decide

theorem KS.countN_ok (h : KS g s0 A live AW liveW V ls s) :
    WP isa (.block countN) s fun t => KS g s0 A live AW liveW (upd V sK (32 * g.w)) (sK :: ls) t := by
  unfold countN
  refine VG.Proof.Rsa.X86.KeyRt.bits_ok h.rt fun u K m e => ?_
  have hu := h.of_rest K (by decide) m
  refine WP.mono (hu.storeSlot sK_ok .esi) fun t ⟨ht, _, _⟩ => ?_
  rw [e, kw_nar, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.upper; change 32 * (2 * g.n + 2) < _; omega)] at ht
  exact ht

theorem KS.countW_ok (h : KS g s0 A live AW liveW V ls s) :
    WP isa (.block countW) s fun t => KS g s0 A live AW liveW (upd V sK (16 * g.W)) (sK :: ls) t := by
  unfold countW
  refine VG.Proof.Rsa.X86.KeyRt.bits_ok h.rtW fun u K m e => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun v U => ?_
  have hv := (h.of_rest K (by decide) m).of_rest U.keeps (by decide) U.mem
  refine WP.mono (hv.storeSlot sK_ok .esi) fun t ⟨ht, _, _⟩ => ?_
  have up := h.upper
  have val : (v.gpr .esi).toNat = 16 * g.W := by
    rw [U.gpr, e, kw_wid, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by change 32 * (2 * (2 * g.n + 2) + 2) < _; omega), Nat.shiftRight_eq_div_pow]
    change 32 * (2 * (2 * g.n + 2) + 2) / 2 ^ 1 = 16 * (2 * (2 * g.n + 2) + 2)
    omega
  rw [val] at ht
  exact ht

theorem KS.countNext_ok (h : KS g s0 A live AW liveW V ls s) (hc : sK ∈ ls)
    (lo : 1 ≤ V sK) (hi : V sK < 2 ^ 32) :
    WP isa (.block countNext) s fun t =>
      KS g s0 A live AW liveW (upd V sK (V sK - 1)) (sK :: ls) t ∧
      t.zf = some (decide (V sK - 1 = 0)) := by
  unfold countNext
  refine wp_movS (h.readSlot hc) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_subi fun v D _ flags => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : v.gpr .eax = BitVec.ofNat 32 (V sK - 1) := by
    rw [D.gpr, U.gpr]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) lo
  refine WP.mono (hv.storeSlot (d := sK) sK_ok .eax) fun t ⟨ht, zt, _⟩ => ?_
  have number : (v.gpr .eax).toNat = V sK - 1 := by
    rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨number ▸ ht, ?_⟩
  rw [zt, flags, U.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) lo]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  rfl

end

/-- A sequence with a last part: its first parts, then the last. -/
theorem wp_seqs_snoc : ∀ {c : Prog isa} {cs : List (Prog isa)} {last : Prog isa} {s : State}
    {Q : State → Prop}, WP isa (seqs (c :: cs)) s (fun u => WP isa last u Q) →
      WP isa (seqs (c :: cs ++ [last])) s Q
  | _, [], _, _, _, h => WP.seq h
  | _, _ :: _, _, _, _, h => WP.seq (WP.mono (WP.seq_iff.mp h) fun _ hu => wp_seqs_snoc hu)

/-- `K` runs of a body that takes its invariant from step `i` to `i + 1`, and sets ZF on the
last. -/
theorem countLoop {body : Prog isa} {K : Nat} (P : Nat → State → Prop) (pos : 0 < K) {s : State}
    (h0 : P 0 s)
    (step : ∀ i u, i < K → P i u → WP isa body u fun v => P (i + 1) v ∧ v.zf = some (decide (K - i - 1 = 0))) :
    WP isa (.loop body .ne) s (P K) := by
  refine WP.loop (M := isa) (fun j u => ∃ k, k + j = K ∧ 0 < j ∧ P k u) ?_ K s ⟨0, by omega, pos, h0⟩
  intro j u ⟨k, sum, hj, hu⟩
  refine WP.mono (step k u (by omega) hu) fun t ⟨ht, zt⟩ => ?_
  by_cases last : k + 1 = K
  · left
    refine ⟨?_, last ▸ ht⟩
    change t.zf.map (!·) = some false
    simp [zt, show K - k - 1 = 0 from by omega]
  · right
    refine ⟨?_, j - 1, by omega, k + 1, by omega, by omega, ht⟩
    change t.zf.map (!·) = some true
    simp [zt, show K - k - 1 ≠ 0 from by omega]

end VG.Proof.Rsa.X86.Recover
