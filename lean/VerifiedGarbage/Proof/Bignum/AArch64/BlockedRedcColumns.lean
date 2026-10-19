module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBlock
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev columnRegs := blockRegs ++ [.x17, .x15]

structure ColumnInv (s : State) (B : Addr) (eQ eT eN j : Nat) (t : State) : Prop where
  value : wv t.mem B eT (8 * j) + 2 ^ (64 * (8 * j)) * blockValue (accumulator t) =
    blockValue (accumulator s) + wv s.mem B eT (8 * j) +
      wv s.mem B eQ 8 * wv s.mem B eN (8 * j)
  ptrT : t.gpr .x16 = off B (eT + 64 * j)
  ptrN : t.gpr .x17 = off B (eN + 64 * j)
  frame : Outside B eT (64 * j) s.mem t.mem
  keep : Keep columnRegs s t

theorem wv_blocks_succ (m : Mem) (B : Addr) (e j : Nat) :
    wv m B e (8 * (j + 1)) = wv m B e (8 * j) +
      2 ^ (64 * (8 * j)) * wv m B (e + 64 * j) 8 := by
  have h := wv_add m B e (8 * j) 8
  rw [show 8 * j + 8 = 8 * (j + 1) by omega,
    show e + 8 * (8 * j) = e + 64 * j by omega] at h
  exact h

theorem pow_blocks_succ (j : Nat) : 2 ^ (64 * (8 * (j + 1))) =
    2 ^ (64 * (8 * j)) * (2 ^ 64) ^ 8 := by
  rw [show 64 * (8 * (j + 1)) = 64 * (8 * j) + 64 * 8 by omega, Nat.pow_add,
    Nat.pow_mul 2 64 8]

theorem columnFinish_ok {s : State} {B : Addr} {eN : Nat}
    (h17 : s.gpr .x17 = off B eN) :
    WP isa (.block [.addImm .x .x17 .x17 64, .subImm .x .x15 .x15 1]) s fun t =>
      (t.gpr .x17 = off B (eN + 64) ∧ t.gpr .x15 = s.gpr .x15 - BitVec.ofNat 64 1 ∧
        t.mem = s.mem) ∧ Keep [.x17, .x15] s t := by
  refine WP.keep [.x17, .x15] ?_ rfl rfl rfl
  brun [h17]

/-- Advance the column invariant for a complete counted-loop iteration. -/
theorem columnStep_ok {s t : State} {B : Addr} {Z eQ eT eN j k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * k ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * k ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * k ≤ eN)
    (hj : j < k) (hI : ColumnInv s B eQ eT eN j t) :
    WP isa (.block (tailBlock ++
      ([.addImm .x .x17 .x17 64, .subImm .x .x15 .x15 1] : List Instr))) t fun u =>
      ColumnInv s B eQ eT eN (j + 1) u ∧ u.gpr .x15 = t.gpr .x15 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  have q := hI.frame.wv (d := eQ) (k := 8) (by omega) (by omega)
  have x := hI.frame.wv (d := eT + 64 * j) (k := 8) (by omega) (by omega)
  have n := hI.frame.wv (d := eN + 64 * j) (k := 8) (by omega) (by omega)
  apply WP.block_append
  refine WP.mono (tailBlock_ok (hs.congr hI.keep.wr)
    ((hI.keep.gpr .x8 (by decide)).trans h8) hI.ptrT hI.ptrN
    ((hI.keep.gpr .x7 (by decide)).trans h7)
    hQ (by omega) (by omega) (by omega) (by omega)) fun a ⟨hav, _, ha16, hao, ka⟩ => ?_
  refine WP.mono (columnFinish_ok ((ka.gpr .x17 (by decide)).trans hI.ptrN))
    fun u ⟨⟨hu17, hu15, hum⟩, ku⟩ => ?_
  have hax : wv a.mem B eT (8 * j) = wv t.mem B eT (8 * j) :=
    hao.wv (by omega) (by omega)
  have hav' : wv a.mem B (eT + 64 * j) 8 + (2 ^ 64) ^ 8 * blockValue (accumulator a) =
      blockValue (accumulator t) + wv s.mem B (eT + 64 * j) 8 +
        wv s.mem B eQ 8 * wv s.mem B (eN + 64 * j) 8 := by
    exact hav.trans (by rewrite [x, q, n]; rfl)
  have he := columns_step hI.value hav'
  have hup := congrArg (fun m : Mem => wv m B eT (8 * (j + 1))) hum
  have hua := congrArg blockValue (keep_accumulator ku (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ((hI.keep.trans ka).trans ku).mono (by decide)⟩, ?_⟩
  · rewrite [hup, hua, wv_blocks_succ, hax, pow_blocks_succ,
      wv_blocks_succ s.mem B eT, wv_blocks_succ s.mem B eN]
    exact he
  · exact ((ku.gpr .x16 (by decide)).trans ha16).trans (congrArg (off B) (by omega))
  · exact hu17.trans (congrArg (off B) (by omega))
  · have ho : Outside B (eT + 64 * j) 64 t.mem u.mem := by
      intro a ha
      exact (congrArg (fun m : Mem => m a) hum).trans (hao a ha)
    exact (hI.frame.mono (by omega) (by omega)).trans (ho.mono (by omega) (by omega))
  · exact hu15.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x15 (by decide)))

/-- The complete fixed-count column loop, including pointer and memory frames. -/
theorem columns_ok {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 k)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * k ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * k ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * k ≤ eN)
    (hk : 0 < k) (hk' : k < 2 ^ 64) :
    WP isa (countLoop .x15 (tailBlock ++ ([.addImm .x .x17 .x17 64] : List Instr))) s
      (ColumnInv s B eQ eT eN k) := by
  have h0 : ColumnInv s B eQ eT eN 0 s :=
    ⟨columns_initial _ _, h16, h17, Outside.refl _ _ _ _, Keep.refl _ _⟩
  unfold countLoop
  rewrite [List.append_assoc]
  exact wp_countdown hk' hk (ColumnInv s B eQ eT eN)
    (fun j hj t hI _ => columnStep_ok hs h8 h7 hQ hT hN hQT hNT hj hI) h0 h15

theorem wv_blocks_first (m : Mem) (B : Addr) (e k : Nat) :
    wv m B e (8 * (k + 1)) = wv m B e 8 +
      (2 ^ 64) ^ 8 * wv m B (e + 64) (8 * k) := by
  have h := wv_radix_add m B e 8 (8 * k)
  rw [show 8 + 8 * k = 8 * (k + 1) by omega] at h
  exact h

end VG.Proof.Bignum.AArch64.BlockedRedc
