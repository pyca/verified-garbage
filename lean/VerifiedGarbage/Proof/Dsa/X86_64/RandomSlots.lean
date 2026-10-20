module
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

/-! Exact memory effects of copying stack argument slots. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSlotsMem (B : Addr) (m : Mem) : List (Nat × Nat) → Mem
  | [] => m
  | (src, dst) :: rest => randomSlotsMem B (m.writeW (off B dst) (word m B src)) rest

theorem random_copySlot_ok {s : State} {B : Addr} (src dst : Nat)
    (hsp : s.gpr .rsp = B)
    (hr : InRegions (s.rd ++ s.wr) (off B src) 8) (hw : InRegions s.wr (off B dst) 8) :
    WP isa (.block (Random.copySlot src dst)) s fun t =>
      t.mem = s.mem.writeW (off B dst) (word s.mem B src) ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B dst) (word s.mem B src)) ?_ rfl
  unfold Random.copySlot
  xrun [random_ea_sp, hsp, hr, hw]

theorem random_copySlots_ok {s : State} {B : Addr} (slots : List (Nat × Nat))
    (hsp : s.gpr .rsp = B)
    (hr : ∀ p ∈ slots, InRegions (s.rd ++ s.wr) (off B p.1) 8)
    (hw : ∀ p ∈ slots, InRegions s.wr (off B p.2) 8) :
    WP isa (.block (slots.flatMap (fun p => Random.copySlot p.1 p.2))) s fun t =>
      t.mem = randomSlotsMem B s.mem slots ∧ Keep [.rax] s t := by
  induction slots generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | cons p rest ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (random_copySlot_ok p.1 p.2 hsp (hr p (by simp)) (hw p (by simp)))
      fun u ⟨hum, hku⟩ => ?_
    refine WP.mono (ih ((hku.gpr (by decide)).trans hsp)
      (fun q hq => by rw [hku.2.1, hku.2.2]; exact hr q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [hku.2.2]; exact hw q (List.mem_cons_of_mem _ hq)))
      fun t ⟨htm, hkt⟩ => ⟨by rw [htm, hum]; rfl, (hku.trans hkt).mono (by decide)⟩

theorem random_slots_outside (B : Addr) (m : Mem) (slots : List (Nat × Nat)) (o n : Nat)
    (hslots : ∀ p ∈ slots, o ≤ p.2 ∧ p.2 + 8 ≤ o + n ∧ p.2 + 8 ≤ 2 ^ 64) :
    Outside B o n m (randomSlotsMem B m slots) := by
  induction slots generalizing m with
  | nil => exact Outside.refl _ _ _ _
  | cons p rest ih =>
    have hp := hslots p (by simp)
    exact ((writeW_outside _ B _ hp.2.2).mono hp.1 hp.2.1).trans
      (ih _ (fun q hq => hslots q (List.mem_cons_of_mem _ hq)))

theorem random_word_write_other (m : Mem) (B : Addr) (src dst : Nat) (v : BitVec 64)
    (hs : src + 8 ≤ 2 ^ 64) (hd : dst + 8 ≤ 2 ^ 64)
    (h : src + 8 ≤ dst ∨ dst + 8 ≤ src) :
    word (m.writeW (off B dst) v) B src = word m B src :=
  (writeW_outside m B v hd).word h hs


end VG.Proof.Dsa.X86_64
