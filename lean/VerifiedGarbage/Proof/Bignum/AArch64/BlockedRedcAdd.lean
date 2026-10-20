module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Add the next eight input words to the resident accumulator. -/
theorem addMemory_ok {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false)) s fun t =>
      (t.c = chainCarry (accumulator s) (fun i => word s.mem B (eT + 8 * i)) false 8 ∧
       (∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
         addCarry (accumulator s i) (word s.mem B (eT + 8 * i))
           (chainCarry (accumulator s) (fun j => word s.mem B (eT + 8 * j)) false i)) ∧
       t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ ([.x13] : List Reg)) s t := by
  have hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (eT + 8 * i)) 8 :=
    fun i hi => hs.ld (by omega)
  refine WP.keep (c := .block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false)) (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ ([.x13] : List Reg)) ?_
    (by decide) (by decide) (by decide)
  have hcode : VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false =
    [ld .x13 .x16 0, .adds .x .x19 .x19 .x13, ld .x13 .x16 8, .adcs .x .x20 .x20 .x13, ld .x13 .x16 16, .adcs .x .x21 .x21 .x13, ld .x13 .x16 24, .adcs .x .x22 .x22 .x13, ld .x13 .x16 32, .adcs .x .x23 .x23 .x13, ld .x13 .x16 40, .adcs .x .x24 .x24 .x13, ld .x13 .x16 48, .adcs .x .x25 .x25 .x13, ld .x13 .x16 56, .adcs .x .x26 .x26 .x13] := rfl
  brun [hcode,
    h16, hs.ld (show eT + 8 ≤ Z by omega), hld 1 (by decide), hld 2 (by decide),
    hld 3 (by decide), hld 4 (by decide), hld 5 (by decide), hld 6 (by decide), hld 7 (by decide)]
  refine ⟨?_, ?_⟩
  · rfl
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl

/-- Adding the next memory block retains its overflow in the carry flag. -/
theorem addMemory_value {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false)) s fun t =>
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat =
        blockValue (accumulator s) + wv s.mem B eT 8 ∧ t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ ([.x13] : List Reg)) s t := by
  refine WP.mono (addMemory_ok hs h16 hT) fun t ⟨⟨hc, hv, hm⟩, kt⟩ => ?_
  have he := (chain_result_value hc hv).trans (Nat.add_zero _)
  exact ⟨⟨he.trans (congrArg (blockValue (accumulator s) + ·)
    (blockValue_words s.mem B eT)), hm⟩, kt⟩

def addCarryMemory : List Instr :=
  (List.range 8).flatMap fun i => [ld .x13 .x16 (8 * i),
    .adcs .x VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]!
      VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! .x13]

/-- The final column uses the incoming pending bit in every carry chain. -/
theorem addCarryMemory_ok {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block addCarryMemory) s fun t =>
      (t.c = chainCarry (accumulator s) (fun i => word s.mem B (eT + 8 * i)) s.c 8 ∧
       (∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
         addCarry (accumulator s i) (word s.mem B (eT + 8 * i))
           (chainCarry (accumulator s) (fun j => word s.mem B (eT + 8 * j)) s.c i)) ∧
       t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ ([.x13] : List Reg)) s t := by
  have hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (eT + 8 * i)) 8 :=
    fun i hi => hs.ld (by omega)
  refine WP.keep (c := .block addCarryMemory) (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ ([.x13] : List Reg)) ?_
    (by decide) (by decide) (by decide)
  have hcode : addCarryMemory =
    [ld .x13 .x16 0, .adcs .x .x19 .x19 .x13, ld .x13 .x16 8, .adcs .x .x20 .x20 .x13, ld .x13 .x16 16, .adcs .x .x21 .x21 .x13, ld .x13 .x16 24, .adcs .x .x22 .x22 .x13, ld .x13 .x16 32, .adcs .x .x23 .x23 .x13, ld .x13 .x16 40, .adcs .x .x24 .x24 .x13, ld .x13 .x16 48, .adcs .x .x25 .x25 .x13, ld .x13 .x16 56, .adcs .x .x26 .x26 .x13] := rfl
  brun [hcode,
    h16, hs.ld (show eT + 8 ≤ Z by omega), hld 1 (by decide), hld 2 (by decide),
    hld 3 (by decide), hld 4 (by decide), hld 5 (by decide), hld 6 (by decide), hld 7 (by decide)]
  refine ⟨?_, ?_⟩
  · rfl
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl

theorem pendingHead_ok {s : State} {p : Bool}
    (h10 : s.gpr .x10 = BitVec.ofNat 64 p.toNat) :
    WP isa (.block [movi .x1 1, .subs .x .x1 .x10 .x1]) s fun t =>
      (t.c = p ∧ t.mem = s.mem) ∧ Keep [.x1] s t := by
  refine WP.keep [.x1] ?_ rfl rfl rfl
  brun [h10]
  cases p <;> rfl

theorem addMemory_pending_eq : VG.Impl.Bignum.AArch64.BlockedRedc.addMemory true =
    [movi .x1 1, .subs .x .x1 .x10 .x1] ++ addCarryMemory := rfl

theorem addMemory_pending_value {s : State} {B : Addr} {Z eT : Nat} {p : Bool}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z)
    (h10 : s.gpr .x10 = BitVec.ofNat 64 p.toNat) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory true)) s fun t =>
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat =
        blockValue (accumulator s) + wv s.mem B eT 8 + p.toNat ∧ t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ ([.x1, .x13] : List Reg)) s t := by
  rewrite [addMemory_pending_eq]
  apply WP.block_append
  refine WP.mono (pendingHead_ok h10) fun a ⟨⟨hac, ham⟩, ka⟩ => ?_
  refine WP.mono (addCarryMemory_ok (hs.congr ka.wr)
    ((ka.gpr .x16 (by decide)).trans h16) hT) fun t ⟨⟨hc, hv, hm⟩, kt⟩ => ?_
  have he := chain_result_value hc hv
  have ha := congrArg blockValue (keep_accumulator ka (by decide))
  have hw := (blockValue_words a.mem B eT).trans (congrArg (fun m : Mem => wv m B eT 8) ham)
  have hp := congrArg Bool.toNat hac
  have hs' : blockValue (accumulator a) + blockValue (fun i => word a.mem B (eT + 8 * i)) +
      a.c.toNat = blockValue (accumulator s) + wv s.mem B eT 8 + p.toNat := by
    exact (congrArg (fun n => n + blockValue (fun i => word a.mem B (eT + 8 * i)) + a.c.toNat) ha).trans
      ((congrArg (fun n => blockValue (accumulator s) + n + a.c.toNat) hw).trans
        (congrArg (blockValue (accumulator s) + wv s.mem B eT 8 + ·) hp))
  exact ⟨⟨he.trans hs', hm.trans ham⟩, (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.BlockedRedc
