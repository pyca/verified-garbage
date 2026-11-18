module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# TDEA-CMAC's streaming functions on AArch64, without secret residue

The postconditions of `vg_cmac_triple_des_stream_init`,
`vg_cmac_triple_des_absorb` and `vg_cmac_triple_des_finish` read the memory
on return only within the 416-byte state and `out` (`ScrubAll.ScrubAllOk`,
as x86-64's `Proof/CmacTripleDes/X86_64/Scrub.lean` proves them): each
returns with every register it may leave secret cleared and its whole stack
zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem initOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.Cmac.tdesStreamInitContract abi W) W (Spec.Cmac.tdesStreamInitSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Cmac.tdesStreamInitSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, _, _], _ =>
      simp only [Spec.Cmac.tdesStreamInitSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
      show Spec.Cmac.tdesRepr m₂ st _ _
      exact Stream.repr_congr_416 (agree_of hb.1 (by decide)) h

theorem absorbOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.Cmac.tdesAbsorbContract abi W) W (Spec.Cmac.tdesAbsorbSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Cmac.tdesAbsorbSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, _, _, _], _ =>
      simp only [Spec.Cmac.tdesAbsorbSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
      show ∀ key msg, Spec.Cmac.tdesRepr m st key msg → _ → _ → Spec.Cmac.tdesRepr m₂ st key _
      intro key msg hr hc hl
      exact Stream.repr_congr_416 (agree_of hb.1 (by decide)) (h key msg hr hc hl)

theorem finishOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.Cmac.tdesFinishContract abi W) W (Spec.Cmac.tdesFinishSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Cmac.tdesFinishSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, _, o], _ =>
      simp only [Spec.Cmac.tdesFinishSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
      show ∀ key msg, Spec.Cmac.tdesRepr m st key msg → _ → _ → Spec.Aes.bytesAt m₂ o 8 = _
      intro key msg hr hc hl
      rw [Stream.bytesAt_congr (agree_of hb.2.1 (by decide))]
      exact h key msg hr hc hl

end VG.Proof.CmacTripleDes.AArch64.Scrub
