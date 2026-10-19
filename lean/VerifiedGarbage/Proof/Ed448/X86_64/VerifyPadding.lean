module

import VerifiedGarbage.Proof.Ed448.X86_64.VerifyBits
public import VerifiedGarbage.Proof.Ed448.SignedWindow
public import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86_64.Basic
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.X448.X86_64.Bits
import VerifiedGarbage.Proof.Ed448.Scalar

/-! Zero padding for signed windows, within the existing scratch allocation. -/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr off ofs Outside writeW8_apply writeW8_outside off_eq_iff ea_sc)

private def zeroMem (m : Mem) (ds : List Addr) : Mem :=
  ds.foldl (fun m d => m.writeW d (0 : BitVec 8)) m

private theorem zeroMem_read (m : Mem) (ds : List Addr) (x : Addr) :
    zeroMem m ds x = if x ∈ ds then 0 else m x := by
  induction ds generalizing m with
  | nil => simp [zeroMem]
  | cons d ds ih =>
    change zeroMem (m.writeW d (0 : BitVec 8)) ds x = _
    rw [ih, writeW8_apply]
    by_cases hx : x = d <;> by_cases hd : x ∈ ds <;> simp [hx, hd]

private def padAddresses (base : Addr) (o : Nat) : List Addr :=
  [off base (o - 1), off base (o + 456), off base (o + 457), off base (o + 458), off base (o + 459)]

private theorem padding_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : 1 ≤ o) (hb : o + 460 ≤ 8192) :
    WP isa (.block (bitPadding o)) s fun u =>
      (∀ r, r ≠ .rdx → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.mem = zeroMem s.mem (padAddresses base o) := by
  have hw : ∀ d, d + 1 ≤ 8192 → InRegions s.wr (off base d) 1 := fun _ h => hs.write h
  apply WP.of_runBlock
  simp only [bitPadding, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, State.store8,
    ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.wr_setReg,  hs.rdi,
    hw (o - 1) (by omega), hw (o + 456) (by omega), hw (o + 457) (by omega),
    hw (o + 458) (by omega), hw (o + 459) (by omega),
    Option.map_some, Option.some.injEq, exists_eq_left',
    reduceCtorEq, ite_true, ite_false]
  exact ⟨fun r hr => by simp only [hr, ite_false], rfl, trivial, rfl⟩

private theorem pad_read {base : Addr} {o j : Nat} (ho : 1 ≤ o) (hb : o + 460 ≤ 8192)
    (hj : j < 461) (m : Mem) :
    zeroMem m (padAddresses base o) (off base (o - 1 + j)) =
      if j = 0 ∨ 457 ≤ j then 0 else m (off base (o - 1 + j)) := by
  rw [zeroMem_read]
  have he : (off base (o - 1 + j) ∈ padAddresses base o) ↔ j = 0 ∨ 457 ≤ j := by
    simp only [padAddresses, List.mem_cons, List.not_mem_nil, or_false,
      off_eq_iff base (by omega : o - 1 + j < 2 ^ 64) (by omega : o - 1 < 2 ^ 64),
      off_eq_iff base (by omega : o - 1 + j < 2 ^ 64) (by omega : o + 456 < 2 ^ 64),
      off_eq_iff base (by omega : o - 1 + j < 2 ^ 64) (by omega : o + 457 < 2 ^ 64),
      off_eq_iff base (by omega : o - 1 + j < 2 ^ 64) (by omega : o + 458 < 2 ^ 64),
      off_eq_iff base (by omega : o - 1 + j < 2 ^ 64) (by omega : o + 459 < 2 ^ 64)]
    omega
  simp only [he]

private theorem pad_outside {base : Addr} {o : Nat} (ho : 1 ≤ o) (hb : o + 460 ≤ 8192)
    (m : Mem) : Outside base (o - 1) 461 m (zeroMem m (padAddresses base o)) := by
  intro x hx
  rw [zeroMem_read, ite_eq_right]
  intro hm
  simp only [padAddresses, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    rw [VG.Proof.X448.X86_64.ofs_off' base (by omega)] at hx <;> omega

/-- The original 456 bits, with zero at index -1 and at indices 456 through 459. -/
theorem bitsAtPadded_ok {s : State} {base k : Addr} (hs : Scr s base) {o : Nat}
    (ho : 1 ≤ o) (hb : o + 460 ≤ 8192) (hk : s.gpr .rsi = k)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa (bitsAtPadded o) s fun u =>
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      Outside base (o - 1) 461 s.mem u.mem ∧
      ∀ j < 461, u.mem (off base (o - 1 + j)) = BitVec.ofNat 8
        (SignedWindow.carry (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem k 57)) j) := by
  rw [bitsAtPadded]
  refine WP.seq (WP.mono (bitsAt_ok (by omega) hs hk hkr hkd) fun v ⟨gv, rv, wv, ov, bv⟩ => ?_)
  have hv : Scr v base := ⟨(gv _ (by decide)).trans hs.rdi, wv ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (padding_ok hv ho hb) fun u ⟨gu, ru, wu, mu⟩ => ?_
  refine ⟨fun r hr => (gu r (fun h => hr (by simp [h]))).trans (gv r hr),
    ru.trans rv, wu.trans wv, ?_, ?_⟩
  · rw [mu]
    exact (ov.mono (by omega) (by omega)).trans (pad_outside ho hb v.mem)
  · intro j hj
    rw [mu, pad_read ho hb hj]
    by_cases hj0 : j = 0
    · subst j; simp [SignedWindow.carry]
    · by_cases hjh : 457 ≤ j
      · have hlt : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem k 57) < 2 ^ 456 :=
          decodeLE_below (by simp [Spec.Ed448.bytesAt])
        simp only [hj0, hjh, or_true, ite_true, SignedWindow.carry, ite_false,
          SignedWindow.bit_zero hlt (by omega : 456 ≤ j - 1), Nat.zero_mod]
        rfl
      · simp only [hj0, hjh, or_self, ite_false, SignedWindow.carry]
        rw [show o - 1 + j = o + (j - 1) by omega, bv (j - 1) (by omega), scalar_bit s.mem k (by omega)]
        simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

end VG.Proof.Ed448.X86_64
