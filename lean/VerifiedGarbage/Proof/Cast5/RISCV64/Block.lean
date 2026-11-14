module

import VerifiedGarbage.Proof.Cast5.RISCV64.Scan
public import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Cast5.RISCV64.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Cast5

/-! ### `Cast5.RISCV64.Round`, which only this module used -/

section

/-!
# CAST5 on RISC-V: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`s0`–`s3` (`spread`), scans `VG_CAST5_S1234` and combines the four values
into `f` (`byType comb`), makes the Feistel step (`feistel`), and moves the
round's number modulo 3 and the count of rounds left on (`next`), as on
PPC64LE (`Proof/Cast5/PPC64LE/Round.lean`). The code's words are the low
words of registers (`lo`); `Kmᵢ` is read a byte at a time (`loadLE32_ok`),
and of `Krᵢ` only its low byte, whose low five bits are the rotation's.
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64

/-! ## Choosing by the type -/

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t < 3)
    (hv : s.gpr typ = BitVec.ofNat 64 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [tmp] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl
  · exact WP.ite true (by rw [eval_zero, hv]; rfl) (fun _ => hQ _ (Keep.refl _ _) rfl)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (imm := 1) (by decide) fun u hu => WP.block_nil ?_)
    have k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => hQ _ k hu.mem)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (imm := 1) (by decide) fun u hu => WP.block_nil ?_)
    have k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide))
      (fun _ => hQ _ k hu.mem)

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t < 3) {kmw d : Spec.Cast5.Word}
    (hR : lo (s.gpr xR) = d) (hin : InRegions (s.rd ++ s.wr) (s.gpr km) 4)
    (hv : s.mem.readW (s.gpr km) 32 = kmw) :
    WP isa (.block (Impl.Cast5.RISCV64.mix t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.mix t kmw d ∧ Keep [vI, tmp] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
  · simp only [Impl.Cast5.RISCV64.mix]
    rw [WP.block_append_iff]
    refine WP.mono (ByteLoad.loadLE32_ok (d := vI) (tmp := tmp) (n := km) (off := 0) (by decide) (by decide)
      (by decide) (by decide) (by rw [BitVec.add_zero]; exact hin)) fun u e => ?_
    subst e
    c5run [hv]
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
    · simp only [lo_add, lo_sub, lo_xor, lo_ext, hR]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [hr.1, hr.2, ite_false]

/-- The rotation: `Krᵢ`'s low byte `k` into `vKr`, then `vI` shifted left
by `k mod 32` (`sllw`) ORed with `vI` shifted right by `(32 - k) mod 32`
(`srlw`), which is `32 - k mod 32`, or 0 when that is 0 and the left shift
is too. -/
theorem rotate_ok (s : State) {a : BitVec 32} {kr : Byte} (hI : lo (s.gpr vI) = a)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 1)
    (hv : s.mem (s.gpr km + BitVec.ofNat 64 64) = kr) :
    WP isa (.block rotate) s fun u =>
      lo (u.gpr vI) = a.rotateLeft (kr.toNat % 32) ∧ Keep [vKr, wd, vI] s u ∧ u.mem = s.mem := by
  unfold rotate
  refine wp_lbu (by decide) rfl hin fun u hu => ?_
  have hk : u.gpr vKr = kr.setWidth 64 := by rw [hu.gpr, hv]
  have ha : lo (u.gpr vI) = a := by rw [hu.other _ (by decide)]; exact hI
  have hkn : (kr.setWidth 64).toNat = kr.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := kr.isLt; omega_using [])
  c5run [hk]
  refine ⟨?_, ⟨fun r hr => ?_, hu.rd, hu.wr⟩, hu.mem⟩
  · have e : lo (u.gpr .t5) = a := ha
    have hr : (32#64 - kr.setWidth 64).toNat % 32 = (32 - kr.toNat % 32) % 32 := by
      rw [BitVec.toNat_sub, hkn, show (32#64).toNat = 32 from rfl]; have := kr.isLt; omega_using []
    simp only [lo_or, lo_sext, e, hkn, hr]
    by_cases h0 : kr.toNat % 32 = 0
    · rw [h0, BitVec.rotateLeft_eq_rotateLeftAux_of_lt (by decide)]
      simp [BitVec.rotateLeftAux, BitVec.ushiftRight_eq_zero]
    · rw [Nat.mod_eq_of_lt (show 32 - kr.toNat % 32 < 32 by omega_using [h0])]
      exact rotl_shifts a (Nat.mod_lt _ (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.1, hr.2.2, ite_false]
    exact hu.other r hr.1

/-- Index `k` of a scan of `I`: byte `k` of `I` (from the least significant). -/
abbrev idxOf (i : BitVec 32) (k : Nat) : Nat := i.toNat / 2 ^ (8 * k) % 256

theorem idxOf_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idxOf i k) = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, idxOf]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] <;> omega_using []

theorem and255_toNat (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The low word of a sign-extended word is that word. -/
theorem sext32_toNat_mod (y : BitVec 32) : (sext32 y).toNat % 256 = y.toNat % 256 := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have := y.isLt
  by_cases h : y.msb = true <;> simp [h] <;> omega_using []

theorem sext32_toNat {y : BitVec 32} (h : y.toNat < 2 ^ 31) : (sext32 y).toNat = y.toNat := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have : y.msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega_using [h]
  have := y.isLt
  simp [*]; omega_using []

theorem ushr24_lt (x : BitVec 64) : (x.setWidth 32 >>> 24).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (x.setWidth 32).isLt
  omega_using []

theorem spread_ok (s : State) {i : BitVec 32} (hI : lo (s.gpr vI) = i) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, (u.gpr (idxReg k)).toNat = idxOf i k) ∧ Keep [.s0, .s1, .s2, .s3] s u ∧ u.mem = s.mem := by
  unfold spread
  c5run
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · have hi : i.toNat = (s.gpr .t5).toNat % 2 ^ 32 := by
      rw [← hI, BitVec.toNat_setWidth]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
      simp only [idxReg_0, idxReg_1, idxReg_2, idxReg_3, reduceCtorEq, ↓reduceIte, and255_toNat,
        sext32_toNat_mod, sext32_toNat (ushr24_lt _), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_setWidth, idxOf, Nat.reduceMul, Nat.reducePow, hi] <;>
      omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t < 3) :
    WP isa (.block (Impl.Cast5.RISCV64.comb t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.comb t (lo (s.gpr .s7)) (lo (s.gpr .s6)) (lo (s.gpr .s5))
        (lo (s.gpr .s4)) ∧ Keep [vI] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.RISCV64.comb
    c5run
    refine ⟨?_, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [hr, ite_false], rfl, rfl⟩⟩
    simp only [lo_add, lo_sub, lo_xor]
    rfl

theorem feistel_ok (s : State) (up : Bool) :
    WP isa (.block (feistel up)) s fun u =>
      u.gpr xL = s.gpr xR ∧ u.gpr xR = s.gpr vI ^^^ s.gpr xL ∧
      u.gpr km = (if up then s.gpr km + 4#64 else s.gpr km - 4#64) ∧ Keep [vI, xL, xR, km] s u ∧
      u.mem = s.mem := by
  cases up <;>
  · unfold feistel
    c5run
    refine ⟨fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The number modulo 3 of the round after the one numbered `t`. -/
def nextT (up : Bool) (t : Nat) : Nat :=
  if up then (if t = 2 then 0 else t + 1) else (if t = 0 then 2 else t - 1)

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t < 3) (hv : s.gpr typ = BitVec.ofNat 64 t) :
    WP isa (next up) s fun u =>
      u.gpr typ = BitVec.ofNat 64 (nextT up t) ∧ u.gpr left = s.gpr left - 1#64 ∧
      Keep [tmp, typ, left] s u ∧ u.mem = s.mem := by
  cases up <;>
  refine WP.mono (WP.keep [tmp, typ, left] (Q := fun u => u.gpr typ = BitVec.ofNat 64 (nextT _ t) ∧
    u.gpr left = s.gpr left - 1#64 ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩ <;>
  unfold next <;> rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · refine WP.seq (WP.ite true (by rw [eval_zero, hv]; rfl) (fun _ => ?_) (fun h => absurd h (by decide)))
    c5run
    c5run [nextT]
  · refine WP.seq (WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_))
    c5run [hv]
    c5run [nextT]
    rfl
  · refine WP.seq (WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_))
    c5run [hv]
    c5run [nextT]
    rfl
  all_goals refine WP.seq (WP.seq (wp_subi (imm := 2) (by decide) fun u hu => WP.block_nil ?_))
  · refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    have ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    have ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    have ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    have ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    have ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run
    c5run [ul, nextT, hu.mem]

/-! ## The round -/

/-- `f` of a round numbered `t` modulo 3 with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- What a round needs: `(L, R)` in the low words of `(a6, a7)`; `Kmᵢ` at
`km` and `Krᵢ` at `km + 64` (of which the low byte's low five bits matter);
the round's number modulo 3 in `typ`; and the table `VG_CAST5_S1234` at
`tbl`, readable and 64-byte aligned. -/
structure RoundPre (s : State) (kmw krw l r : Spec.Cast5.Word) (t : Nat) : Prop where
  xL : lo (s.gpr xL) = l
  xR : lo (s.gpr xR) = r
  inM : InRegions (s.rd ++ s.wr) (s.gpr km) 4
  valM : s.mem.readW (s.gpr km) 32 = kmw
  inR : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 1
  valR : (s.mem (s.gpr km + BitVec.ofNat 64 64)).toNat % 32 = krw.toNat % 32
  ht : t < 3
  typ : s.gpr typ = BitVec.ofNat 64 t
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  tal : (s.gpr tbl).toNat % 64 = 0
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234

/-- The registers a round writes. -/
def roundRegs : List Reg := [tmp, wd, .t2, ep, .s4, .s5, .s6, .s7, .s0, .s1, .s2, .s3, vI, vKr, .a5,
  xL, xR, km, typ, left]

theorem round_ok (s : State) (up : Bool) {kmw krw l r : Spec.Cast5.Word} {t : Nat}
    (h : RoundPre s kmw krw l r t) :
    WP isa (round up) s fun u =>
      lo (u.gpr xL) = r ∧ lo (u.gpr xR) = l ^^^ fT t kmw krw r ∧
      u.gpr km = (if up then s.gpr km + 4#64 else s.gpr km - 4#64) ∧
      u.gpr typ = BitVec.ofNat 64 (nextT up t) ∧ u.gpr left = s.gpr left - 1#64 ∧
      Keep roundRegs s u ∧ u.mem = s.mem := by
  have ht := h.ht
  unfold round
  -- `I` before the rotation.
  refine WP.seq (WP.mono (byType_ok s Impl.Cast5.RISCV64.mix (Q := fun v => lo (v.gpr vI) =
      Proof.Cast5.mix t kmw r ∧ Keep [tmp, vI] s v ∧ v.mem = s.mem) ht h.typ fun u uk um => ?_) fun v hv => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = s.gpr q := uk.gpr (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.xR)
      (by rw [uk.2.1, uk.2.2, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.trans vk).mono (by decide), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [tmp, vI]) : v.gpr q = s.gpr q := vk.gpr hq
  -- The rotation and the indices.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rotate_ok v v1 (by rw [vk.2.1, vk.2.2, gv _ (by decide)]; exact h.inR) rfl)
    fun w ⟨w1, wk, wm⟩ => ?_
  rw [vm, gv _ (by decide), h.valR] at w1
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t kmw r).rotateLeft (krw.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  have kw := vk.trans wk
  refine WP.mono (spread_ok w w1) fun x ⟨xi, xk, xm⟩ => ?_
  have kx := kw.trans xk
  have mx : x.mem = s.mem := xm.trans (wm.trans vm)
  have tx : x.gpr tbl = s.gpr tbl := kx.gpr (by decide)
  -- The scan.
  have sp : ScanPre x :=
    { idx := fun k hk => by rw [xi k hk]; exact Nat.mod_lt _ (by decide)
      tal := by rw [tx]; exact h.tal
      trd := by rw [tx, kx.2.1, kx.2.2]; exact h.trd }
  refine WP.seq (WP.mono (scan_ok x sp) fun y ⟨ya, yk, ym⟩ => ?_)
  have ky := kx.trans yk
  have my : y.mem = s.mem := ym.trans mx
  have ty : y.gpr typ = BitVec.ofNat 64 t := by rw [ky.gpr (by decide)]; exact h.typ
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.RISCV64.comb (Q := fun z => lo (z.gpr vI) = fT t kmw krw r ∧
      Keep [tmp, vI] y z ∧ z.mem = y.mem) ht ty fun u uk um => ?_) fun z ⟨z1, zk, zm⟩ => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = y.gpr q := uk.gpr (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, uk.trans zk, zm.trans um⟩
    have ent' (k : Nat) (hk : k < 4) : lo (y.gpr (accReg k)) = Proof.Cast5.tableEnt Spec.Cast5.S4 Spec.Cast5.S3
        Spec.Cast5.S2 Spec.Cast5.S1 (idxOf i k) k := by
      rw [ya k hk, mx, xi k hk, tx, lo_ext]
      exact ent_table h.held (Nat.mod_lt _ (by decide)) hk
    have a0 : lo (y.gpr .s4) = _ := ent' 0 (by decide)
    have a1 : lo (y.gpr .s5) = _ := ent' 1 (by decide)
    have a2 : lo (y.gpr .s6) = _ := ent' 2 (by decide)
    have a3 : lo (y.gpr .s7) = _ := ent' 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3]
    unfold fT
    rw [hi]
    simp only [Proof.Cast5.tableEnt, idxOf_byte i (show 0 < 4 by decide), idxOf_byte i (show 1 < 4 by decide),
      idxOf_byte i (show 2 < 4 by decide), idxOf_byte i (show 3 < 4 by decide)]
  have kz := ky.trans zk
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, akm, ak, am⟩ => ?_)
  have ka := kz.trans ak
  refine WP.mono (next_ok a up ht (by rw [ka.gpr (by decide)]; exact h.typ)) fun b ⟨bt, bl, bk, bm⟩ => ?_
  have kb := ka.trans bk
  have gb (q : Reg) (hq : q ∉ [tmp, typ, left]) : b.gpr q = a.gpr q := bk.gpr hq
  refine ⟨by rw [gb _ (by decide), a2, kz.gpr (by decide)]; exact h.xR, ?_, ?_, bt,
    by rw [bl, ka.gpr (by decide)], kb.mono (by decide), by rw [bm, am, zm, my]⟩
  · rw [gb _ (by decide), a3, lo_xor, z1, kz.gpr (by decide), h.xL, BitVec.xor_comm]
  · rw [gb _ (by decide), akm, kz.gpr (by decide)]

end VG.Proof.Cast5.RISCV64

end

end


/-!
# CAST5 on RISC-V: the block function

`crypt up pr` encrypts (`up`) or decrypts the block at `pr` in place, with
the schedule at `sch` and the number of rounds in `rnd` (`crypt_ok`): it
loads the halves, a byte at a time, big-endian (`load_ok`), runs the rounds
in a loop (`rounds_ok`), each from the state of the rounds (`RInv`), and
stores them, a byte at a time (`finish_ok`). It writes no memory but the
block's. As on PPC64LE (`Proof/Cast5/PPC64LE/Block.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq roundI)
open VG.WriteBytes (writeBytes)

/-- `fT` of round `i`'s number modulo 3 is the spec's `f`. -/
theorem fT_eq (i : Nat) (km kr d : Spec.Cast5.Word) : fT (i % 3) km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]; rfl

/-- The block's cipher. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cast5.Block → Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n else Spec.Cast5.decryptBlock k n

/-- What the block function needs: the block at `p` in `pr` (a register
the rounds keep), writable; the schedule at `kb` in `sch`, readable; the
number of rounds `n` in `rnd`; and the table `VG_CAST5_S1234` at `tbl`,
readable and 64-byte aligned. -/
structure BPre (s : State) (pr : Reg) (p kb : Addr) (n : Nat) : Prop where
  ptr : s.gpr pr = p
  prOk : pr ∉ roundRegs
  sched : s.gpr sch = kb
  rounds : s.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  tal : (s.gpr tbl).toNat % 64 = 0
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234
  inP : InRegions s.wr p 8
  inK : (⟨kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : kb.toNat + 128 ≤ 2 ^ 64

section
variable {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
include h

theorem BPre.inK' {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.inK, Offset.contains_base _ hw (by have := h.kfit; omega_arith)⟩

theorem BPre.inP' : InRegions (s.rd ++ s.wr) p 8 :=
  let ⟨r, hr, hc⟩ := h.inP; ⟨r, List.mem_append_right _ hr, hc⟩

end

/-! ## The rounds -/

/-- The state of a block's rounds, from `s`: the halves `lr`, the next
round's subkeys at `kp`, its number modulo 3 `t` and `left` rounds left. -/
structure RInv (s : State) (lr : Spec.Cast5.Word × Spec.Cast5.Word) (kp : Addr) (t nl : Nat)
    (u : State) : Prop where
  vL : lo (u.gpr xL) = lr.1
  vR : lo (u.gpr xR) = lr.2
  vkm : u.gpr km = kp
  vtyp : u.gpr typ = BitVec.ofNat 64 t
  vleft : u.gpr left = BitVec.ofNat 64 nl
  keep : Keep roundRegs s u
  mem : u.mem = s.mem

/-- Subkey `j` at `kb + 4 j`. -/
theorem key_at (s : State) (kb : Addr) {j : Nat} (hj : j < 32) :
    s.mem.readW (kb + BitVec.ofNat 64 (4 * j)) 32 = (Spec.Cast5.scheduleAt s.mem kb).getD j 0 :=
  (Proof.Cast5.scheduleAt_getD _ _ hj).symm

/-- The low five bits of a little-endian word are those of its first byte. -/
theorem readW_mod32 (m : Mem) (a : Addr) : (m.readW a 32).toNat % 32 = (m a).toNat % 32 := by
  have e : (m.readW a 32).setWidth 8 = m a := by
    rw [Proof.Cast5.readW32]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true, Bool.true_and, ite_true]
  have h8 : ((m.readW a 32).setWidth 8).toNat = (m.readW a 32).toNat % 256 := by
    rw [BitVec.toNat_setWidth]
  rw [← e, h8]
  omega_using []

/-- A round, from the state of the rounds. -/
theorem round_step {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {nl i : Nat}
    (hu : RInv s lr (kb + BitVec.ofNat 64 (4 * (i - 1))) (i % 3) nl u) (up : Bool)
    (hi : 1 ≤ i ∧ i ≤ 16) (hl : 1 ≤ nl ∧ nl < 2 ^ 64) :
    WP isa (round up) u fun v =>
      RInv s (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr)
        (if up then kb + BitVec.ofNat 64 (4 * (i - 1)) + 4#64 else kb + BitVec.ofNat 64 (4 * (i - 1)) - 4#64)
        (nextT up (i % 3)) (nl - 1) v := by
  have g (q : Reg) (hq : q ∉ roundRegs := by decide) : u.gpr q = s.gpr q := hu.keep.gpr hq
  have e64 : u.gpr km + BitVec.ofNat 64 64 = kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.vkm, Offset.add_add]; congr 2; omega_arith
  have pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem kb).getD (i - 1) 0)
      ((Spec.Cast5.scheduleAt s.mem kb).getD (15 + i) 0) lr.1 lr.2 (i % 3) :=
    { xL := hu.vL
      xR := hu.vR
      inM := by rw [hu.vkm, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valM := by rw [hu.vkm, hu.mem]; exact key_at s kb (by omega_arith)
      inR := by rw [e64, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valR := by rw [e64, hu.mem, ← key_at s kb (by omega_arith), readW_mod32]
      ht := Nat.mod_lt _ (by decide)
      typ := hu.vtyp
      trd := by rw [g tbl, hu.keep.2.1, hu.keep.2.2]; exact h.trd
      tal := by rw [g tbl]; exact h.tal
      held := by rw [g tbl, hu.mem]; exact h.held }
  refine WP.mono (round_ok u up pre) fun v ⟨v1, v2, vkm, vt, vl, vk, vm⟩ => ⟨v1, ?_, ?_, vt, ?_,
    (hu.keep.trans vk).mono (by decide), vm.trans hu.mem⟩
  · rw [v2, show (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr).2 =
      lr.1 ^^^ Spec.Cast5.f i lr.2 _ _ from rfl, fT_eq]
  · rw [vkm, hu.vkm]
  · rw [vl, hu.vleft]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-- The rounds loop, for any order of the rounds: round `idx i` is the
`i`-th, with its subkeys at `kpf i`, and the halves before it `fold i`. -/
theorem rounds_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool)
    (idx : Nat → Nat) (kpf : Nat → Addr) (fold : Nat → Spec.Cast5.Word × Spec.Cast5.Word)
    (hidx : ∀ i < n, 1 ≤ idx i ∧ idx i ≤ 16) (hkp : ∀ i < n, kpf i = kb + BitVec.ofNat 64 (4 * (idx i - 1)))
    (hfold : ∀ i < n, fold (i + 1) = Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) (idx i) (fold i))
    (hnext : ∀ i, i + 1 < n → kpf (i + 1) = (if up then kpf i + 4#64 else kpf i - 4#64) ∧
      idx (i + 1) % 3 = nextT up (idx i % 3))
    (h0 : RInv s (fold 0) (kpf 0) (idx 0 % 3) n u) :
    WP isa (.loop (round up) (.nonzero left)) u fun v => ∃ kp t, RInv s (fold n) kp t 0 v := by
  have hn : n = 12 ∨ n = 16 := h.nv
  refine WP.loop (M := isa) (fun m (v : State) => ∃ i, m = n - i ∧ i < n ∧
      RInv s (fold i) (kpf i) (idx i % 3) (n - i) v) ?_ n u ⟨0, rfl, by omega_arith, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (hidx i hi) (by omega_arith)) fun w hw => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  have ev : isa.eval (.nonzero left) w = some (BitVec.ofNat 64 (n - i - 1) != 0) := by
    rw [eval_nonzero, hw.vleft]
  by_cases hlast : i + 1 = n
  · refine .inl ⟨?_, _, _, by rw [hlast] at hw; rw [show n - i - 1 = 0 by omega_arith] at hw; exact hw⟩
    rw [ev, show n - i - 1 = 0 by omega_arith]; rfl
  · obtain ⟨hk, htn⟩ := hnext i (by omega_arith)
    refine .inr ⟨?_, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ?_⟩
    · rw [ev]
      congr 1
      have : BitVec.ofNat 64 (n - i - 1) ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega_arith
      simpa using this
    · rw [hk, htn, show n - (i + 1) = n - i - 1 by omega_arith]
      exact hw


/-! ## The block function -/

theorem _root_.VG.RISCV64.Steps.Upd.keep {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) :
    Keep [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.rd, h.wr⟩

theorem BPre.ne {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {r : Reg}
    (hr : r ∈ roundRegs) : pr ≠ r := fun e => h.prOk (e ▸ hr)

/-- The halves of the block at `p`: big-endian words, a byte at a time. -/
theorem decodeBlock_beWord (m : Mem) (p : Addr) :
    Spec.Cast5.decodeBlock (Spec.Cast5.blockAt m p) = (ByteLoad.beWord m p 0, ByteLoad.beWord m p 4) := by
  simp only [Spec.Cast5.decodeBlock, ByteLoad.beWord, Proof.Cast5.blockAt_get m p (show 0 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 1 < 8 by decide), Proof.Cast5.blockAt_get m p (show 2 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 3 < 8 by decide), Proof.Cast5.blockAt_get m p (show 4 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 5 < 8 by decide), Proof.Cast5.blockAt_get m p (show 6 < 8 by decide),
    Proof.Cast5.blockAt_get m p (show 7 < 8 by decide), Nat.reduceAdd]

/-- The halves into `xL`, `xR`. -/
theorem load_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Keep [xL, tmp, xR] s u → u.mem = s.mem →
      lo (u.gpr xL) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).1 →
      lo (u.gpr xR) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).2 → WP isa (.block is) u Q) :
    WP isa (.block (loadBlock pr ++ is)) s Q := by
  have in0 : InRegions (s.rd ++ s.wr) (s.gpr pr + BitVec.ofNat 64 0) 4 := by
    rw [h.ptr]; exact CallLay.inRegions_sub h.inP' (by decide) (by decide)
  have in4 : InRegions (s.rd ++ s.wr) (s.gpr pr + BitVec.ofNat 64 4) 4 := by
    rw [h.ptr]; exact CallLay.inRegions_sub h.inP' (by decide) (by decide)
  rw [loadBlock, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE32_ok (d := xL) (tmp := tmp) (n := pr) (off := 0) (h.ne (by decide)).symm
    (h.ne (by decide)).symm (by decide) (by decide) in0) fun u₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE32_ok (d := xR) (tmp := tmp) (n := pr) (off := 4) (h.ne (by decide)).symm
    (h.ne (by decide)).symm (by decide) (by decide) (by
      simp only [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, h.ne (show xL ∈ roundRegs by decide),
        h.ne (show tmp ∈ roundRegs by decide), ite_false]
      exact in4)) fun u₂ e₂ => ?_
  subst e₂
  refine k _ ⟨fun r hr => ?_, rfl, rfl⟩ rfl ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, decodeBlock_beWord, h.ptr]
  · simp only [RegUpd.gpr_write, ite_true, lo_ext, RegUpd.mem_write, decodeBlock_beWord,
      h.ne (show xL ∈ roundRegs by decide), h.ne (show tmp ∈ roundRegs by decide), ite_false, h.ptr]

theorem startEnc_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startEnc pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * 0)) ((0 + 1) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_li (imm := 1) (by decide) fun u₃ h₃ => WP.block_nil ?_
  exact
    { vL := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, uk.gpr (by decide), h.sched]; simp
      vtyp := by rw [h₃.gpr]
      vleft := by rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), uk.gpr (by decide), h.rounds]
      keep := ⟨fun r hr => by
          rw [h₃.other r (fun e => hr (e ▸ by decide)), h₂.other r (fun e => hr (e ▸ by decide)),
            h₁.other r (fun e => hr (e ▸ by decide)), uk.gpr (fun e => hr (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at e
              rcases e with rfl | rfl | rfl <;> decide))],
        by rw [h₃.rd, h₂.rd, h₁.rd, uk.2.1], by rw [h₃.wr, h₂.wr, h₁.wr, uk.2.2]⟩
      mem := by rw [h₃.mem, h₂.mem, h₁.mem, um] }

theorem startDec_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startDec pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * ((n - 0) - 1))) ((n - 0) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_sll (by decide) fun u₁ h₁ => wp_add fun u₂ h₂ => wp_subi (imm := 4) (by decide) fun u₃ h₃ =>
    wp_mv fun u₄ h₄ => wp_srl (by decide) fun u₅ h₅ => wp_subi (imm := 3) (by decide) fun u₆ h₆ =>
    WP.block_nil ?_
  have r4 : u.gpr rnd = BitVec.ofNat 64 n := by rw [uk.gpr (by decide), h.rounds]
  have r3 : u.gpr sch = kb := by rw [uk.gpr (by decide), h.sched]
  have kmv : u₃.gpr km = kb + (BitVec.ofNat 64 n <<< 2) - BitVec.ofNat 64 4 := by
    rw [h₃.gpr, h₂.gpr, h₁.other _ (by decide), h₁.gpr, r3, r4]
  have tv : u₆.gpr typ = (BitVec.ofNat 64 n >>> 2) - BitVec.ofNat 64 3 := by
    rw [h₆.gpr, h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), r4]
  have ko : ∀ r, r ∉ roundRegs → u₆.gpr r = s.gpr r := fun r hr => by
    have h' : ∀ q ∈ [tmp, km, left, typ, xL, xR], r ≠ q := fun q hq e => hr (by
      subst e; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [h₆.other r (h' _ (by decide)), h₅.other r (h' _ (by decide)), h₄.other r (h' _ (by decide)),
      h₃.other r (h' _ (by decide)), h₂.other r (h' _ (by decide)), h₁.other r (h' _ (by decide)),
      uk.gpr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h' _ (by decide), h' _ (by decide), h' _ (by decide)⟩)]
  exact
    { vL := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), kmv]
        rcases h.nv with rfl | rfl
        · rw [show (BitVec.ofNat 64 12 <<< 2) = BitVec.ofNat 64 48 by decide, Offset.add_ofNat_sub _ (by decide)]
        · rw [show (BitVec.ofNat 64 16 <<< 2) = BitVec.ofNat 64 64 by decide, Offset.add_ofNat_sub _ (by decide)]
      vtyp := by rw [tv]; rcases h.nv with rfl | rfl <;> decide
      vleft := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide), r4]
      keep := ⟨ko, by rw [h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, uk.2.1],
        by rw [h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, uk.2.2]⟩
      mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, um] }

/-- What the block function does: the block at `p` is `out`, and nothing
else in memory changed. -/
structure BPost (s : State) (p : Addr) (out : Spec.Cast5.Block) (t : State) : Prop where
  blk : Spec.Cast5.blockAt t.mem p = out
  frame : Frame [⟨p, 8⟩] s.mem t.mem
  keep : Keep roundRegs s t

theorem shr_lo (x : BitVec 64) {k : Nat} (hk : k ≤ 24) :
    (x >>> k).setWidth 8 = (lo x >>> k).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show k + i < 32 by omega_using [hk, hi]]

/-- What the stores leave: the block `(x, y)`. -/
theorem stored_block (m : Mem) (q : Addr) (x y : BitVec 64) :
    Spec.Cast5.blockAt (writeBytes m q (ByteLoad.beBytes 4 x ++ ByteLoad.beBytes 4 y)) q =
      Spec.Cast5.encodeBlock (lo x, lo y) := by
  apply Vector.ext
  intro i hi
  rw [Proof.Cast5.blockAt_get _ _ hi]
  simp only [Spec.Cast5.encodeBlock, Vector.getElem_ofFn, writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hi]), List.length_append,
    ByteLoad.beBytes_length, show i < 4 + 4 by omega_using [hi], ite_true]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [ByteLoad.beBytes_length]; exact h4)]
    simp only [ByteLoad.beBytes, List.getElem?_map, List.getElem?_range h4, Option.map_some, Option.getD_some]
    rw [shr_lo _ (by omega_using []), Nat.mod_eq_of_lt h4]
  · rw [ite_eq_right h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [ByteLoad.beBytes_length]; omega_using [h4]), ByteLoad.beBytes_length]
    simp only [ByteLoad.beBytes, List.getElem?_map, List.getElem?_range (show i - 4 < 4 by omega_using [hi]), Option.map_some,
      Option.getD_some]
    rw [shr_lo _ (by omega_using [])]
    congr 3; omega_using [hi, h4]

theorem finish_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : Addr} {t : Nat} (hu : RInv s lr kp t 0 u) :
    WP isa (.block (finish pr)) u (BPost s p (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have g (q : Reg) (hq : q ∉ roundRegs) : u.gpr q = s.gpr q := hu.keep.gpr hq
  have hp : u.gpr pr = p := by rw [g _ h.prOk, h.ptr]
  have hw : ∀ j < 8, InRegions u.wr (p + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hu.keep.2.2]; exact CallLay.inRegions_sub h.inP (by omega_using [hj]) (by decide)
  rw [finish, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (v := xR) (tmp := tmp) (n := pr) (off := 0) (w := 4) (by decide)
    (h.ne (by decide)).symm (by decide) (by decide) (by decide) fun j hj => by
      rw [hp, Nat.zero_add]; exact hw j (by omega_using [hj])) fun u₁ e₁ => ?_
  subst e₁
  have hp₁ : ∀ (m : Mem) (v : BitVec 64), ({ u with mem := m }.write tmp v).gpr pr = p := fun m v => by
    rw [RegUpd.gpr_write_of_ne _ _ (h.ne (by decide))]; exact hp
  refine WP.mono (ByteLoad.storeBE_ok (v := xL) (tmp := tmp) (n := pr) (off := 4) (w := 4) (by decide)
    (h.ne (by decide)).symm (by decide) (by decide) (by decide) fun j hj => by
      rw [hp₁]; exact hw (4 + j) (by omega_using [hj])) fun u₂ e₂ => ?_
  subst e₂
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.write_mem, hp, h.ne (show tmp ∈ roundRegs by decide),
    show xL ≠ tmp by decide, ite_false, BitVec.add_zero]
  have hm := WriteBytes.writeBytes_append u.mem p (ByteLoad.beBytes 4 (u.gpr xR)) (ByteLoad.beBytes 4 (u.gpr xL))
    (by simp only [ByteLoad.beBytes_length]; decide)
  rw [ByteLoad.beBytes_length] at hm
  refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩⟩
  · simp only [State.write]
    rw [hm, stored_block]
    exact congrArg _ (Prod.ext hu.vR hu.vL)
  · simp only [State.write]
    rw [hm, ← hu.mem]
    exact WriteBytes.writeBytes_frame _ _ _ (by
      simp only [List.length_append, ByteLoad.beBytes_length]
      exact Region.contains_self p 8)
  · have ht : r ≠ tmp := fun e => hr (by rw [e]; decide)
    simp only [State.write, ht, ite_false]
    exact hu.keep.gpr hr
  · exact hu.keep.2.1
  · exact hu.keep.2.2

theorem crypt_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool) :
    WP isa (crypt up pr) s (BPost s p (cipher up (Spec.Cast5.scheduleAt s.mem kb) n
      (Spec.Cast5.blockAt s.mem p))) := by
  have hn := h.nv
  cases up
  · unfold crypt
    simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (startDec_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h false (fun i => n - i) (fun i => kb + BitVec.ofNat 64 (4 * (n - i - 1)))
      (fun i => decFold _ n i _) (fun i hi => by omega_arith) (fun i hi => rfl)
      (fun i hi => decFold_succ _ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [Bool.false_eq_true, ite_false]
      rw [show n - i - 1 = n - (i + 1) - 1 + 1 by omega_arith, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact (BitVec.add_sub_cancel _ _).symm
    · simp only [nextT, Bool.false_eq_true, ite_false]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_right Bool.false_ne_true, decryptBlock_eq]
    exact hw
  · unfold crypt
    simp only [ite_true]
    refine WP.seq (WP.mono (startEnc_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h true (fun i => i + 1) (fun i => kb + BitVec.ofNat 64 (4 * i))
      (fun i => encFold _ i _) (fun i hi => by omega_arith)
      (fun i hi => by rw [Nat.add_sub_cancel]) (fun i hi => encFold_succ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu)
      fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [ite_true]
      rw [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
    · simp only [nextT, ite_true]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_left rfl, encryptBlock_eq]
    exact hw

end VG.Proof.Cast5.RISCV64
