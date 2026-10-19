module
public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Ed25519.Word64

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

structure SaveInv (s : State) (B : Addr) (eT k : Nat) (t : State) : Prop where
  done : ∀ i < k, word t.mem B (eT + 8 * i) = s.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]!
  frame : Outside B eT (8 * k) s.mem t.mem
  keep : Keep [] s t
  carry : t.c = s.c

def savePrefix (k : Nat) : List Instr :=
  (List.range k).flatMap fun i => [st VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! .x16 (8 * i)]

theorem saveStep_ok {s t : State} {B : Addr} {Z eT k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 88 ≤ Z)
    (hk : k < 11) (hI : SaveInv s B eT k t) :
    WP isa (.block [st VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]! .x16 (8 * k)]) t
      (SaveInv s B eT (k + 1)) := by
  have hn := hs.nowrap
  have hptr := (hI.keep.gpr .x16 (by decide)).trans h16
  have hr := (hI.keep.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]!
    (by simp))
  have enc : (8 * k) % 8 = 0 ∧ 8 * k < 32768 := ⟨by omega, by omega⟩
  refine WP.mono (WP.keep [] (Q := fun u =>
      u.mem = t.mem.writeW (off B (eT + 8 * k)) (s.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]!) ∧ u.c = t.c)
    (by brun [hptr, hr, enc, (hs.congr hI.keep.wr).st (show eT + 8 * k + 8 ≤ Z by omega)])
    rfl rfl rfl) fun u ⟨⟨hm, hc⟩, ku⟩ => ?_
  have ho := writeW_outside t.mem B (s.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[k]!) (d := eT + 8 * k) (by omega)
  refine ⟨?_, ?_, (hI.keep.trans ku).mono (by decide), hc.trans hI.carry⟩
  · intro i hi
    have hw := congrArg (fun m : Mem => word m B (eT + 8 * i)) hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hw.trans ((ho.word (by omega) (by omega)).trans (hI.done i hi))
    · exact hw.trans (word_writeW_self _ _ _ _)
  · have hf : Outside B (eT + 8 * k) 8 t.mem u.mem := by
      intro a ha
      exact (congrArg (fun m : Mem => m a) hm).trans (ho a ha)
    exact (hI.frame.mono (by omega) (by omega)).trans (hf.mono (by omega) (by omega))

theorem savePrefix_ok {s : State} {B : Addr} {Z eT k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 88 ≤ Z)
    (hk : k ≤ 11) : WP isa (.block (savePrefix k)) s (SaveInv s B eT k) := by
  induction k with
  | zero =>
    apply WP.block_nil
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keep.refl _ _, rfl⟩
  | succ k ih =>
    rewrite [savePrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    exact WP.mono (ih (by omega)) fun t hI => saveStep_ok hs h16 hT (by omega) hI

theorem saved_ne_ptr : ∀ i < 11, VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! ≠ .x16 := by decide

theorem saved_injective : ∀ i < 11, ∀ j < 11,
    VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! = VG.Impl.Bignum.AArch64.BlockedRedc.saved[j]! → i = j := by decide

theorem spillBase_ok {s : State} {B : Addr} {Z w o : Nat} {minv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (ho : o < 8) :
    WP isa (.block [ldh .x16 (sArr o)]) s fun t =>
      (t.gpr .x16 = off B (slot w o) ∧ t.mem = s.mem) ∧ Keep [.x16] s t := by
  have hslot : sArr o < 32 := by unfold sArr; omega
  refine WP.keep [.x16] ?_ rfl rfl rfl
  brun [h0, hdr_enc hslot, hs.ld (show 8 * sArr o + 8 ≤ Z by
    have := hdr_lt_slot w 8 hslot; omega), hH.harr o ho]

theorem saves_ok {s : State} {B : Addr} {Z w o : Nat} {minv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (ho : o < 8) (hw : 16 ≤ w) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.saves o)) s fun t =>
      (∀ i < 11, word t.mem B (slot w o + 8 * i) = s.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]!) ∧
      Outside B (slot w o) 88 s.mem t.mem ∧ Keep [.x16] s t := by
  have he : VG.Impl.Bignum.AArch64.BlockedRedc.saves o = [ldh .x16 (sArr o)] ++ savePrefix 11 := rfl
  rewrite [he]
  apply WP.block_append
  refine WP.mono (spillBase_ok hs h0 hH hZ ho) fun u ⟨⟨hu16, hum⟩, ku⟩ => ?_
  refine WP.mono (savePrefix_ok (hs.congr ku.wr) hu16
    (by have := slot_le (w := w) ho; omega) (Nat.le_refl 11)) fun t hI => ?_
  refine ⟨?_, ?_, (ku.trans hI.keep).mono (by decide)⟩
  · intro i hi
    exact (hI.done i hi).trans (ku.gpr _ (by simpa only [List.mem_singleton] using saved_ne_ptr i hi))
  · intro x hx
    exact (hI.frame x hx).trans (congrArg (fun m : Mem => m x) hum)

end VG.Proof.Bignum.AArch64.BlockedRedc
