module

public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ChaCha20's `apply` on AArch64, without secret residue

The postcondition of `vg_chacha20_apply` reads the memory on return only
within the state and the data (`ScrubAll.ScrubAllOk`, as x86-64's
`Proof/ChaCha20/X86_64/Scrub.lean` proves it): each implementation, generic
over the implementation of `vg_chacha20_xor` it calls and without frames,
returns with every register it may leave secret cleared
(`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.ChaCha20

/-- A state whose first 136 bytes are unchanged represents the same key and
keystream. -/
theorem stream_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 136, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    keyAt m' p = keyAt m p ∧ restAt m' p = restAt m p ∧ leftAt m' p = leftAt m p := by
  have hb : ∀ a n, a + n ≤ 136 → bytesAt m' (p + BitVec.ofNat 64 a) n = bytesAt m (p + BitVec.ofNat 64 a) n :=
    fun a n hn => List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      simpa only [Offset.add_add] using h (a + i) (by omega_using [hn, this])
  have hw : ∀ a w, a + w / 8 ≤ 136 → m'.readW (p + BitVec.ofNat 64 a) w = m.readW (p + BitVec.ofNat 64 a) w :=
    fun a w hn => Mem.readW_congr fun i hi => by
      simpa only [Offset.add_add] using h (a + i) (by omega_using [hn, hi])
  have hl : leftAt m' p = leftAt m p := by
    simp only [leftAt]; rw [show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, hw _ _ (by decide)]
  have hs : stateAt m' p = stateAt m p := by
    apply Vector.ext; intro i hi
    simp only [stateAt, Vector.getElem_ofFn]
    exact hw _ _ (by omega_using [hi])
  refine ⟨by simp only [keyAt]; exact hb 16 32 (by decide), ?_, hl⟩
  simp only [restAt, hl, hs]
  rw [hb _ _ (by omega_using [])]

theorem applyOk : ScrubAllOk (applyContract abi 0) 0 (applySig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := applySig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [applySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
    have hd : Spec.ChaCha20.bytesAt m₂ dt ln.toNat = Spec.ChaCha20.bytesAt m₁ dt ln.toNat := by
      simp only [Spec.ChaCha20.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this]) (by omega_using [this]))).symm
    obtain ⟨k, rs, -⟩ := stream_congr hs
    show keyAt m₂ st = _ ∧ _
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [k]; exact h1, ?_⟩
    have e64 : (ArgWord.int AArch64.abi.ptrBits).ofRaw ln = ln := BitVec.setWidth_eq ln
    rw [e64] at h2 ⊢
    split at h2 <;> split <;> rename_i h₁ h₂
    · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩
    · exact absurd h₁ h₂
    · exact absurd h₂ h₁
    · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩

end VG.Proof.ChaCha20.AArch64.Scrub
