module
public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Ed25519.Word64

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

structure RestoreInv (g : Reg → Word) (s : State) (k : Nat) (t : State) : Prop where
  done : ∀ i < k, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! = g VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]!
  mem : t.mem = s.mem
  keep : Keep VG.Impl.Bignum.AArch64.BlockedRedc.saved s t

def restorePrefix (k : Nat) : List Instr :=
  (List.range k).flatMap fun i => [ld VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! .x16 (8 * i)]

theorem restoreStep_ok {g : Reg → Word} {s t : State} {B : Addr} {Z eT k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 88 ≤ Z)
    (hSaved : ∀ i < 11, word s.mem B (eT + 8 * i) = g VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]!)
    (hk : k < 11) (hI : RestoreInv g s k t) :
    WP isa (.block [ld VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]! .x16 (8 * k)]) t
      (RestoreInv g s (k + 1)) := by
  have hptr := (hI.keep.gpr .x16 (by decide)).trans h16
  have hv := (congrArg (fun m : Mem => word m B (eT + 8 * k)) hI.mem).trans (hSaved k hk)
  have enc : (8 * k) % 8 = 0 ∧ 8 * k < 32768 := ⟨by omega, by omega⟩
  have hw : ∀ j < 11, writesOnly [VG.Impl.Bignum.AArch64.BlockedRedc.saved[j]!]
      (.block [ld VG.Impl.Bignum.AArch64.BlockedRedc.saved[j]! .x16 (8 * j)]) = true := by decide
  refine WP.mono (WP.keep [VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]!] (Q := fun u =>
      u.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]! = g VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]! ∧
        u.mem = t.mem)
    (by brun [hptr, enc, (hs.congr hI.keep.wr).ld (show eT + 8 * k + 8 ≤ Z by omega), hv])
    (hw k hk) rfl rfl) fun u ⟨⟨hu, hm⟩, ku⟩ => ?_
  refine ⟨?_, hm.trans hI.mem, (hI.keep.trans ku).mono ?_⟩
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hne : VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! ≠
          VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]! :=
        fun h => Nat.ne_of_lt hi (saved_injective i (by omega) k hk h)
      exact (ku.gpr _ (by simpa only [List.mem_singleton] using hne)).trans (hI.done i hi)
    · exact hu
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · have hj : ∀ j < 11, VG.Impl.Bignum.AArch64.BlockedRedc.saved[j]! ∈
          VG.Impl.Bignum.AArch64.BlockedRedc.saved := by decide
      exact (List.mem_singleton.mp hr) ▸ hj k hk

theorem restorePrefix_ok {g : Reg → Word} {s : State} {B : Addr} {Z eT k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 88 ≤ Z)
    (hSaved : ∀ i < 11, word s.mem B (eT + 8 * i) = g VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]!)
    (hk : k ≤ 11) : WP isa (.block (restorePrefix k)) s (RestoreInv g s k) := by
  induction k with
  | zero =>
    apply WP.block_nil
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), rfl, Keep.refl _ _⟩
  | succ k ih =>
    rewrite [restorePrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    exact WP.mono (ih (by omega)) fun t hI => restoreStep_ok hs h16 hT hSaved (by omega) hI

theorem restores_ok {g : Reg → Word} {s : State} {B : Addr} {Z w o : Nat} {minv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (ho : o < 8) (hw : 16 ≤ w)
    (hSaved : ∀ i < 11, word s.mem B (slot w o + 8 * i) = g VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]!) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.restores o)) s fun t =>
      (∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.saved, t.gpr r = g r) ∧ t.mem = s.mem ∧
      Keep (.x16 :: VG.Impl.Bignum.AArch64.BlockedRedc.saved) s t := by
  have he : VG.Impl.Bignum.AArch64.BlockedRedc.restores o = [ldh .x16 (sArr o)] ++ restorePrefix 11 := rfl
  rewrite [he]
  apply WP.block_append
  refine WP.mono (spillBase_ok hs h0 hH hZ ho) fun u ⟨⟨hu16, hum⟩, ku⟩ => ?_
  have hS : ∀ i < 11, word u.mem B (slot w o + 8 * i) = g VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! :=
    fun i hi => (congrArg (fun m : Mem => word m B (slot w o + 8 * i)) hum).trans (hSaved i hi)
  refine WP.mono (restorePrefix_ok (hs.congr ku.wr) hu16
    (by have := slot_le (w := w) ho; omega) hS (Nat.le_refl 11)) fun t hI => ?_
  refine ⟨?_, hI.mem.trans hum, (ku.trans hI.keep).mono (by decide)⟩
  intro r hr
  have hm : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.saved,
      ∃ i < 11, VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! = r := by decide
  obtain ⟨i, hi, rfl⟩ := hm r hr
  exact hI.done i hi

end VG.Proof.Bignum.AArch64.BlockedRedc
