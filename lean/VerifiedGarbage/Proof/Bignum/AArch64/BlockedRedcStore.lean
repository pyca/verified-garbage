module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

structure StoreInv (s : State) (B : Addr) (eT k : Nat) (t : State) : Prop where
  done : ∀ i < k, word t.mem B (eT + 8 * i) = accumulator s i
  frame : Outside B eT (8 * k) s.mem t.mem
  keep : Keep [] s t
  carry : t.c = s.c

def storePrefix (k : Nat) : List Instr :=
  (List.range k).flatMap fun i => [st VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! .x16 (8 * i)]

theorem storeStep_ok {s t : State} {B : Addr} {Z eT k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z)
    (hk : k < 8) (hI : StoreInv s B eT k t) :
    WP isa (.block [st VG.Impl.Bignum.AArch64.BlockedRedc.aa[k]! .x16 (8 * k)]) t
      (StoreInv s B eT (k + 1)) := by
  have hn := hs.nowrap
  have hptr := (hI.keep.gpr .x16 (by decide)).trans h16
  have hr := (hI.keep.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[k]!
    (by simp)).trans (accumulator_reg s hk).symm
  have enc : (8 * k) % 8 = 0 ∧ 8 * k < 32768 := ⟨by omega, by omega⟩
  refine WP.mono (WP.keep [] (Q := fun u =>
      u.mem = t.mem.writeW (off B (eT + 8 * k)) (accumulator s k) ∧ u.c = t.c)
    (by brun [hptr, hr, enc, (hs.congr hI.keep.wr).st (show eT + 8 * k + 8 ≤ Z by omega)])
    rfl rfl rfl) fun u ⟨⟨hm, hc⟩, ku⟩ => ?_
  have ho := writeW_outside t.mem B (accumulator s k) (d := eT + 8 * k) (by omega)
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

theorem storePrefix_ok {s : State} {B : Addr} {Z eT k : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z)
    (hk : k ≤ 8) : WP isa (.block (storePrefix k)) s (StoreInv s B eT k) := by
  induction k with
  | zero =>
    apply WP.block_nil
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keep.refl _ _, rfl⟩
  | succ k ih =>
    rewrite [storePrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    exact WP.mono (ih (by omega)) fun t hI => storeStep_ok hs h16 hT (by omega) hI

theorem asStore_ok {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedc.asStore) s fun t =>
      wv t.mem B eT 8 = blockValue (accumulator s) ∧
      Outside B eT 64 s.mem t.mem ∧ Keep [] s t ∧ t.c = s.c := by
  have he : VG.Impl.Bignum.AArch64.BlockedRedc.asStore = storePrefix 8 := rfl
  rewrite [he]
  refine WP.mono (storePrefix_ok hs h16 hT (Nat.le_refl 8)) fun t hI => ?_
  exact ⟨(blockValue_words t.mem B eT).symm.trans (blockValue_congr hI.done),
    hI.frame, hI.keep, hI.carry⟩

end VG.Proof.Bignum.AArch64.BlockedRedc
