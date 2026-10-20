module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! Store a selected 64-byte block while preserving its source snapshot. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem write16_outside (m : Mem) (B : Addr) {d : Nat} (v : BitVec 128)
    (h : d + 16 ≤ 2 ^ 64) : Outside B d 16 m (m.write (off B d) 16 v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have he : (x - off B d).toNat = (2 ^ 64 - d + (x - B).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x B (by omega)
  rw [he]
  have := (x - B).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - B).toNat = (x - B).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem write16_byte (m source : Mem) (dst src : Addr) {j : Nat} (hj : j < 16) :
    (m.write dst 16 (source.read src 16)) (dst + BitVec.ofNat 64 j) =
      source (src + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Mem.sub_ofNat_toNat dst (show j < 2 ^ 64 by omega), hj, ite_true,
    Mem.extractLsb'_read source src hj]

theorem storePair_ok {s : State} {r : VReg} {i : Nat} (hi : i < 4)
    (hw : InRegions s.wr (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block [.strq r .x17 (16 * i)]) s fun t =>
      (t.mem = s.mem.write (s.gpr .x17 + BitVec.ofNat 64 (16 * i)) 16 (s.v r) ∧
        t.v = s.v) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, addr, show 16 * i % 16 = 0 by omega,
    show 16 * i < 4096 * 16 by omega, and_self, ite_true, Option.bind_some,
    State.store, hw, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']

def stores (n : Nat) : List Instr := (List.range n).map fun i => .strq (acc i) .x17 (16 * i)

structure StoreInv (s : State) (B : Addr) (dst src n : Nat) (t : State) : Prop where
  keep : Keep [] s t
  vectors : t.v = s.v
  frame : Outside B dst (16 * n) s.mem t.mem
  bytes : ∀ j < 16 * n, t.mem (off B (dst + j)) = s.mem (off B (src + j))

theorem stores_ok (n : Nat) {s : State} {B : Addr} {dst src : Nat}
    (hn : n ≤ 4) (hptr : s.gpr .x17 = off B dst) (hd : dst + 16 * n ≤ 2 ^ 64)
    (hv : ∀ i < n, s.v (acc i) = s.mem.read (off B (src + 16 * i)) 16)
    (hw : ∀ i < n, InRegions s.wr (off B (dst + 16 * i)) 16) :
    WP isa (.block (stores n)) s (StoreInv s B dst src n) := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨Keep.refl _ _, rfl, Outside.refl _ _ _ _, fun _ h => by omega⟩
  | succ n ih =>
    rw [show stores (n + 1) = stores n ++ [.strq (acc n) .x17 (16 * n)] by
      simp [stores, List.range_succ], WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega) (fun i hi => hv i (by omega))
      (fun i hi => hw i (by omega))) fun t ht => ?_
    have ptr : t.gpr .x17 + BitVec.ofNat 64 (16 * n) = off B (dst + 16 * n) := by
      rw [ht.keep.gpr .x17 (by simp), hptr, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    refine WP.mono (storePair_ok (r := acc n) (by omega)
      (by rw [ht.keep.wr, ptr]; exact hw n (by omega))) fun u ⟨⟨hm, huv⟩, ku⟩ => ?_
    rw [ptr, ht.vectors, hv n (by omega)] at hm
    have ho := write16_outside t.mem B (d := dst + 16 * n)
      (s.mem.read (off B (src + 16 * n)) 16) (by omega)
    rw [← hm] at ho
    refine ⟨(ht.keep.trans ku).mono (by decide), huv.trans ht.vectors,
      (ht.frame.mono (by omega) (by omega)).trans (ho.mono (by omega) (by omega)), ?_⟩
    intro j hj
    by_cases hjn : j < 16 * n
    · rw [ho _ (by
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show dst + j < 2 ^ 64 by omega)]
      omega)]
      exact ht.bytes j hjn
    · have hp : off B (dst + j) = off B (dst + 16 * n) + BitVec.ofNat 64 (j - 16 * n) := by
        rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact congrArg (fun z => B + BitVec.ofNat 64 z) (by omega)
      rw [hm, hp, write16_byte t.mem s.mem _ _ (by omega), off,
        BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (fun z => s.mem (B + BitVec.ofNat 64 z)) (by omega)

end VG.Proof.Bignum.AArch64.WindowVector
