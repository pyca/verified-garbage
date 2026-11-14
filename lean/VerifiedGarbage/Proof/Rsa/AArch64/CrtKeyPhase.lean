module

public import VerifiedGarbage.Proof.Rsa.AArch64.CkPhaseCore
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyTop
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# `vg_rsa_check_key` on AArch64: the shortened remainder

`reduceTop` (`ckReduceTop_ok`), the remainder `wmodOne` takes when
`wordGuard` fails (`Proof/Rsa/AArch64/CkPhase.lean`), and its counts of
quotient words (`topE_ok`, `topQ_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sQlen aM aA aRem aT)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ reduceTop topE topQ)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `reduceTop top`: the remainder of `[aA]` by `[aM]` into `[aRem]`, when
the words of `[aA]` from `c` up are below `[aM]`. -/
theorem ckReduceTop_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {top : List Instr} {c : Nat}
    (hT : TopOk top I.B I.Z s.mem c) (hc1 : 1 ≤ c) (hc : c < wW I.cap) :
    WP isa (seqs (reduceTop top)) s fun t =>
      CkS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (I.av s.mem aA / 2 ^ (64 * c) < I.av s.mem aM → I.av t.mem aRem = I.av s.mem aA % I.av s.mem aM) ∧
      ∀ i < 16, i ≠ aRem → i ≠ aQ → i ≠ aT → I.av t.mem i = I.av s.mem i := by
  have hn := h.ws.scr.nowrap
  refine WP.mono (reduceTop_ok h.ws hT hc1 hc) fun t ⟨_, f, k, hv⟩ => ?_
  have hr : ∀ r ∈ [ar (wW I.cap) aQ, ar (wW I.cap) aRem, ar (wW I.cap) aT], ∃ j < 16, r = ar (wW I.cap) j := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨aQ, by decide, rfl⟩
    · exact ⟨aRem, by decide, rfl⟩
    · exact ⟨aT, by decide, rfl⟩
  refine ⟨h.step f (fun r hr' => by obtain ⟨j, _, rfl⟩ := hr r hr'; exact Mut.ofSlot _ _ _)
    (fun r hr' => by obtain ⟨j, hj, rfl⟩ := hr r hr'; exact h.ws.sl hj) k (by decide), ?_, fun hlt => ?_,
    fun i hi h1 h2 h3 => ?_⟩
  · exact f.word_eq (fun r hr' => by
      obtain ⟨j, hj, rfl⟩ := hr r hr'
      have := hdr_lt_slot (wW I.cap) j (show Public.sMask < 32 by decide); exact Or.inl (by omega_using [this]))
      (by simp only [Public.sMask, sFn]; omega_using [])
  · have hM : 0 < I.av s.mem aM := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hr' := hv hlt
    have hlt' : wv t.mem I.B (slot (wW I.cap) aRem) (wW I.cap + 1) < 2 ^ (64 * wW I.cap) := by
      rw [hr']; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hM) (Nat.le_of_lt (wv_lt _ _ _ _))
    unfold CkIn.av
    rw [wv_low_of_lt (v := wW I.cap) (w := wW I.cap + 1) (by omega_using []) hlt', hr']
  · exact f.wv_eq (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl <;> dsimp only
      · have := slot_sep (w := wW I.cap) h2; omega_using [this]
      · have := slot_sep (w := wW I.cap) h1; omega_using [this]
      · have := slot_sep (w := wW I.cap) h3; omega_using [this]) (by have := h.ws.sl hi; omega_using [hn, this])

/-- `topE`: `x13 := 1`. -/
theorem topE_ok (B : Addr) (Z : Nat) (m₀ : Mem) : TopOk topE B Z m₀ 1 := fun t _ _ _ =>
  WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 1 ∧ t'.mem = t.mem ∧ t'.c = t.c)
    (by unfold topE; brun) (by decide) (by decide) (by decide +kernel)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩

/-- `topQ`: `x13 := ⌈q_len / 8⌉`, from the header slot of `q_len`. -/
theorem topQ_ok {B : Addr} {Z : Nat} {m₀ : Mem} {ql : Nat} (hq : word m₀ B (8 * sQlen) = BitVec.ofNat 64 ql)
    (hql : ql < 2 ^ 32) (hZ : 8 * 32 ≤ Z) : TopOk topQ B Z m₀ ((ql + 7) / 8) := fun t hs h0 hh => by
  have hl := hs.ld (d := 8 * sQlen) (by simp only [sQlen, sFn]; omega_using [hZ])
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.gpr .x13 = BitVec.ofNat 64 ((ql + 7) / 8) ∧ t'.mem = t.mem ∧
    t'.c = t.c) ?_ (by decide) (by decide) (by decide +kernel)) fun _ ⟨h, k⟩ => ⟨h, k.mono (by simp)⟩
  unfold topQ
  brun [h0, hl, hh sQlen (by decide), hq, BitVec.ofNat_add_ofNat, shr_ofNat (show ql + 7 < 2 ^ 64 by omega_using [hql])]

/-- A product by a number below `2^(64 k)`, shifted down by `64 k` bits, is at
most the other factor. -/
theorem mul_div_top_le {a b k : Nat} (hb : b < 2 ^ (64 * k)) : a * b / 2 ^ (64 * k) ≤ a :=
  Nat.div_le_of_le_mul (by rw [Nat.mul_comm (2 ^ _)]; exact Nat.mul_le_mul_left a (Nat.le_of_lt hb))

end VG.Proof.Rsa.AArch64
