module

public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Cast5.ModeMem
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Cast5.RISCV64.Scan
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Cast5.RISCV64.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Cast5

/-! ### `Cast5.RISCV64.Block`, which this module and modules that import it used -/

section

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
    obtain k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => hQ _ k hu.mem)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (imm := 1) (by decide) fun u hu => WP.block_nil ?_)
    obtain k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
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
  obtain hk : u.gpr vKr = kr.setWidth 64 := by rw [hu.gpr, hv]
  obtain ha : lo (u.gpr vI) = a := by rw [hu.other _ (by decide)]; exact hI
  obtain hkn : (kr.setWidth 64).toNat = kr.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := kr.isLt; omega_using [])
  c5run [hk]
  refine ⟨?_, ⟨fun r hr => ?_, hu.rd, hu.wr⟩, hu.mem⟩
  · have e : lo (u.gpr .t5) = a := ha
    obtain hr : (32#64 - kr.setWidth 64).toNat % 32 = (32 - kr.toNat % 32) % 32 := by
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
    obtain ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    obtain ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    obtain ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    obtain ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ul : u.gpr left = s.gpr left := hu.other _ (by decide)
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
  obtain kw := vk.trans wk
  refine WP.mono (spread_ok w w1) fun x ⟨xi, xk, xm⟩ => ?_
  obtain kx := kw.trans xk
  obtain mx : x.mem = s.mem := xm.trans (wm.trans vm)
  obtain tx : x.gpr tbl = s.gpr tbl := kx.gpr (by decide)
  -- The scan.
  obtain sp : ScanPre x :=
    { idx := fun k hk => by rw [xi k hk]; exact Nat.mod_lt _ (by decide)
      tal := by rw [tx]; exact h.tal
      trd := by rw [tx, kx.2.1, kx.2.2]; exact h.trd }
  refine WP.seq (WP.mono (scan_ok x sp) fun y ⟨ya, yk, ym⟩ => ?_)
  obtain ky := kx.trans yk
  obtain my : y.mem = s.mem := ym.trans mx
  obtain ty : y.gpr typ = BitVec.ofNat 64 t := by rw [ky.gpr (by decide)]; exact h.typ
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.RISCV64.comb (Q := fun z => lo (z.gpr vI) = fT t kmw krw r ∧
      Keep [tmp, vI] y z ∧ z.mem = y.mem) ht ty fun u uk um => ?_) fun z ⟨z1, zk, zm⟩ => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = y.gpr q := uk.gpr (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, uk.trans zk, zm.trans um⟩
    have ent' (k : Nat) (hk : k < 4) : lo (y.gpr (accReg k)) = Proof.Cast5.tableEnt Spec.Cast5.S4 Spec.Cast5.S3
        Spec.Cast5.S2 Spec.Cast5.S1 (idxOf i k) k := by
      rw [ya k hk, mx, xi k hk, tx, lo_ext]
      exact ent_table h.held (Nat.mod_lt _ (by decide)) hk
    obtain a0 : lo (y.gpr .s4) = _ := ent' 0 (by decide)
    obtain a1 : lo (y.gpr .s5) = _ := ent' 1 (by decide)
    obtain a2 : lo (y.gpr .s6) = _ := ent' 2 (by decide)
    obtain a3 : lo (y.gpr .s7) = _ := ent' 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3]
    unfold fT
    rw [hi]
    simp only [Proof.Cast5.tableEnt, idxOf_byte i (show 0 < 4 by decide), idxOf_byte i (show 1 < 4 by decide),
      idxOf_byte i (show 2 < 4 by decide), idxOf_byte i (show 3 < 4 by decide)]
  obtain kz := ky.trans zk
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, akm, ak, am⟩ => ?_)
  obtain ka := kz.trans ak
  refine WP.mono (next_ok a up ht (by rw [ka.gpr (by decide)]; exact h.typ)) fun b ⟨bt, bl, bk, bm⟩ => ?_
  obtain kb := ka.trans bk
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
  obtain e : (m.readW a 32).setWidth 8 = m a := by
    rw [Proof.Cast5.readW32]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true, Bool.true_and, ite_true]
  obtain h8 : ((m.readW a 32).setWidth 8).toNat = (m.readW a 32).toNat % 256 := by
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
  obtain e64 : u.gpr km + BitVec.ofNat 64 64 = kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.vkm, Offset.add_add]; congr 2; omega_arith
  obtain pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem kb).getD (i - 1) 0)
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
  obtain ev : isa.eval (.nonzero left) w = some (BitVec.ofNat 64 (n - i - 1) != 0) := by
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
  obtain in0 : InRegions (s.rd ++ s.wr) (s.gpr pr + BitVec.ofNat 64 0) 4 := by
    rw [h.ptr]; exact CallLay.inRegions_sub h.inP' (by decide) (by decide)
  obtain in4 : InRegions (s.rd ++ s.wr) (s.gpr pr + BitVec.ofNat 64 4) 4 := by
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
  obtain r4 : u.gpr rnd = BitVec.ofNat 64 n := by rw [uk.gpr (by decide), h.rounds]
  obtain r3 : u.gpr sch = kb := by rw [uk.gpr (by decide), h.sched]
  obtain kmv : u₃.gpr km = kb + (BitVec.ofNat 64 n <<< 2) - BitVec.ofNat 64 4 := by
    rw [h₃.gpr, h₂.gpr, h₁.other _ (by decide), h₁.gpr, r3, r4]
  obtain tv : u₆.gpr typ = (BitVec.ofNat 64 n >>> 2) - BitVec.ofNat 64 3 := by
    rw [h₆.gpr, h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), r4]
  obtain ko : ∀ r, r ∉ roundRegs → u₆.gpr r = s.gpr r := fun r hr => by
    obtain h' : ∀ q ∈ [tmp, km, left, typ, xL, xR], r ≠ q := fun q hq e => hr (by
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
  obtain hp : u.gpr pr = p := by rw [g _ h.prOk, h.ptr]
  obtain hw : ∀ j < 8, InRegions u.wr (p + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hu.keep.2.2]; exact CallLay.inRegions_sub h.inP (by omega_using [hj]) (by decide)
  rw [finish, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (v := xR) (tmp := tmp) (n := pr) (off := 0) (w := 4) (by decide)
    (h.ne (by decide)).symm (by decide) (by decide) (by decide) fun j hj => by
      rw [hp, Nat.zero_add]; exact hw j (by omega_using [hj])) fun u₁ e₁ => ?_
  subst e₁
  obtain hp₁ : ∀ (m : Mem) (v : BitVec 64), ({ u with mem := m }.write tmp v).gpr pr = p := fun m v => by
    rw [RegUpd.gpr_write_of_ne _ _ (h.ne (by decide))]; exact hp
  refine WP.mono (ByteLoad.storeBE_ok (v := xL) (tmp := tmp) (n := pr) (off := 4) (w := 4) (by decide)
    (h.ne (by decide)).symm (by decide) (by decide) (by decide) fun j hj => by
      rw [hp₁]; exact hw (4 + j) (by omega_using [hj])) fun u₂ e₂ => ?_
  subst e₂
  simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.write_mem, hp, h.ne (show tmp ∈ roundRegs by decide),
    show xL ≠ tmp by decide, ite_false, BitVec.add_zero]
  obtain hm := WriteBytes.writeBytes_append u.mem p (ByteLoad.beBytes 4 (u.gpr xR)) (ByteLoad.beBytes 4 (u.gpr xL))
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

end

end

/-!
# CAST5 on RISC-V: ECB

`ecb_wp`: every block becomes its encryption or decryption, one at a time
(`loop_run`); our caller's `s0`–`s10` are saved in the working space,
rounded up to a multiple of 8 (`prologue_ok`), and restored. The loop
writes only the blocks. As on PPC64LE (`Proof/Cast5/PPC64LE/Ecb.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)]
  exact h i hi

theorem s1234_len : 8 * Impl.Cast5.s1234.length = 4096 := by rw [Impl.Cast5.s1234, table_length]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this; exact this)
    simp only [bne, decide_eq_false h, Bool.not_false, Bool.not_eq_true']
    exact beq_eq_false_iff_ne.mpr this

/-! ## The loop -/

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The registers the loop writes. -/
def loopWrites : List Reg := roundRegs ++ [dat, cnt]

/-- The loop's fixed facts, about the state `s₀` before it: the schedule at
`S`, the `n` blocks at `D`, and the table at `T`, readable, 64-byte aligned
and apart from the blocks. -/
structure LoopEnv (S D T : Addr) (n N : Nat) (s₀ : State) : Prop where
  r3 : s₀.gpr sch = S
  r4 : s₀.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  tbl : s₀.gpr tbl = T
  key : (⟨S, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  kfit : S.toNat + 128 ≤ 2 ^ 64
  data : (⟨D, 8 * N⟩ : Region) ∈ s₀.wr
  keyData : (⟨S, 128⟩ : Region).Disjoint ⟨D, 8 * N⟩
  fit : D.toNat + 8 * N ≤ 2 ^ 64
  trd : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr
  tal : T.toNat % 64 = 0
  held : Held s₀.mem T Impl.Cast5.s1234
  tblData : (⟨T, 4096⟩ : Region).Disjoint ⟨D, 8 * N⟩

/-- After `k` blocks. -/
structure EInv (S D : Addr) (n N : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ N
  ptr : u.gpr dat = wAt D k
  cnt : u.gpr cnt = BitVec.ofNat 64 (N - k)
  keep : Keep loopWrites s₀ u
  done : ∀ b < k, Spec.Cast5.blockAt u.mem (wAt D b) =
    cipher up (Spec.Cast5.scheduleAt s₀.mem S) n (Spec.Cast5.blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < N → Spec.Cast5.blockAt u.mem (wAt D b) = Spec.Cast5.blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * N⟩] s₀.mem u.mem

theorem ecb_step {S D T : Addr} {n N : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D T n N s₀) {k : Nat}
    (hk : k < N) {u : State} (I : EInv S D n N up s₀ k u) :
    WP isa (.seq (crypt up dat) (.block [.addi dat dat 8, .addi cnt cnt (-1)])) u
      (fun u' => EInv S D n N up s₀ (k + 1) u' ∧ u'.gpr cnt = BitVec.ofNat 64 (N - (k + 1))) := by
  have fit := L.fit
  have g (q : Reg) (hq : q ∉ loopWrites := by decide) : u.gpr q = s₀.gpr q := I.keep.gpr hq
  have dTD : ∀ r ∈ [(⟨D, 8 * N⟩ : Region)], Region.Disjoint ⟨T, 8 * Impl.Cast5.s1234.length⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [s1234_len]; exact L.tblData
  have hK : Spec.Cast5.scheduleAt u.mem S = Spec.Cast5.scheduleAt s₀.mem S :=
    Proof.Cast5.scheduleAt_frame I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have bp : BPre u dat (wAt D k) S n :=
    { ptr := I.ptr
      prOk := by decide
      sched := by rw [g sch]; exact L.r3
      rounds := by rw [g rnd]; exact L.r4
      nv := L.nv
      trd := by rw [g tbl, L.tbl, I.keep.2.1, I.keep.2.2]; exact L.trd
      tal := by rw [g tbl, L.tbl]; exact L.tal
      held := by
        rw [g tbl, L.tbl]
        exact held_frame I.frame dTD (by rw [s1234_len]; decide) L.held
      inP := ⟨_, by rw [I.keep.2.2]; exact L.data, Offset.contains_base D (by omega_arith) (by omega_arith)⟩
      inK := by rw [I.keep.2.1, I.keep.2.2]; exact L.key
      kfit := L.kfit }
  refine WP.seq (WP.mono (crypt_ok bp up) fun u₁ B => ?_)
  refine wp_addi (imm := 8) (by decide) fun u₂ h₂ => wp_subi (imm := 1) (by decide) fun u₃ h₃ => WP.block_nil ?_
  have m₃ : u₃.mem = u₁.mem := by rw [h₃.mem, h₂.mem]
  have c₃ : u₃.gpr cnt = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [h₃.gpr, h₂.other _ (by decide), B.keep.gpr (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  have other : ∀ b, b < N → b ≠ k →
      Spec.Cast5.blockAt u₃.mem (wAt D b) = Spec.Cast5.blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame B.frame fun r hr => ?_]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)
  have hk3 : Keep loopWrites s₀ u₃ := ⟨fun r hr => by
      have h1 : r ≠ dat := fun e => hr (by rw [e]; decide)
      have h2 : r ≠ cnt := fun e => hr (by rw [e]; decide)
      rw [h₃.other r h2, h₂.other r h1, B.keep.gpr (fun e => hr (List.mem_append_left _ e)), I.keep.gpr hr],
    by rw [h₃.rd, h₂.rd, B.keep.2.1, I.keep.2.1], by rw [h₃.wr, h₂.wr, B.keep.2.2, I.keep.2.2]⟩
  refine ⟨⟨by omega_arith, ?_, c₃, hk3, fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃⟩
  · rw [h₃.other _ (by decide), h₂.gpr, B.keep.gpr (by decide), I.ptr, Offset.add_add]
    congr 2
  · by_cases hbk : b = k
    · subst hbk
      rw [m₃, B.blk, hK, I.rest b (by omega_arith) hk]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · rw [m₃]
    refine I.frame.trans (B.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base D (by omega_arith)⟩

theorem loop_run {S D T : Addr} {n N : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D T n N s₀) (hn : 0 < N)
    {u : State} (I : EInv S D n N up s₀ 0 u) :
    WP isa (.loop (.seq (crypt up dat) (.block [.addi dat dat 8, .addi cnt cnt (-1)])) (.nonzero cnt)) u
      (EInv S D n N up s₀ N) := by
  refine WP.loop (M := isa) (Q := EInv S D n N up s₀ N)
    (fun m v => ∃ k, k < N ∧ m = N - k ∧ EInv S D n N up s₀ k v) ?_ N u ⟨0, hn, rfl, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (ecb_step L hk J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : N < 2 ^ 64 := by have := L.fit; omega_arith
  rw [eval_nonzero, hz, ofNat_bne_zero (by omega_arith)]
  by_cases e : k + 1 = N
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, N - (k + 1), by omega_arith, k + 1, by omega_arith, rfl, J'⟩

/-! ## Saving and restoring -/

/-- The working space at `P` rounded up to a multiple of 8. -/
abbrev wbase (P : Addr) : Addr := P + BitVec.ofNat 64 (Align.pad P)

theorem prologue_eq (b : Reg) (sym : String) :
    prologue b sym = .addi b b 7 :: .logicImm .and b b (-8) ::
      (Spill.saveCode b savedSlots ++ ([.lla tbl sym] : List Instr)) := rfl

theorem epilogue_eq (b : Reg) : epilogue b = Spill.restoreCode b savedSlots := rfl

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem savedSlots_ok : ∀ p ∈ savedSlots, p.2 % 8 = 0 ∧ p.2 < 2048 := savedSlots_fits.1
theorem savedSlots_fst : ∀ p ∈ savedSlots, p.1 ∈ saved := by decide
theorem savedSlots_lt : ∀ p ∈ savedSlots, 64 ≤ p.2 ∧ p.2 + 8 ≤ 64 + 88 := by decide

/-- An access of `w` bytes at offset `d` of the rounded working space lies
within the working space at `P` (256 bytes). -/
theorem wbase_in {rs : List Region} {P : Addr} (hP : (⟨P, 256⟩ : Region) ∈ rs)
    {d w : Nat} (hd : d + w ≤ 249) : InRegions rs (wbase P + BitVec.ofNat 64 d) w :=
  ⟨_, hP, by
    have := Align.pad_lt P
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The rounded working space's bytes `[d, d + n)` are within the working space. -/
theorem wbase_sub (P : Addr) {d n : Nat} (hd : d + n ≤ 249) :
    Region.Sub ⟨wbase P + BitVec.ofNat 64 d, n⟩ ⟨P, 256⟩ := by
  rw [Offset.add_add]
  exact Offset.sub_base _ (by have := Align.pad_lt P; omega_arith)

theorem wbase_sub0 (P : Addr) {n : Nat} (hn : n ≤ 249) : Region.Sub ⟨wbase P, n⟩ ⟨P, 256⟩ := by
  have h := wbase_sub P (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at h

theorem wbase_toNat {P : Addr} (h : P.toNat + 256 ≤ 2 ^ 64) : (wbase P).toNat = P.toNat + Align.pad P := by
  have := Align.pad_lt P
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Align.pad P) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

/-- The prologue: the working space at `b` rounded up, the slots there hold
the callee-saved registers, and the table's address is in `tbl`. -/
theorem prologue_ok (s : State) (b : Reg) (hb : b ∉ saved ∧ b ≠ tbl) (sym : String) {P : Addr}
    (hB : s.gpr b = P) (hP : (⟨P, 256⟩ : Region) ∈ s.wr)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Spill.Saved (wbase P) s.gpr savedSlots u.mem →
      Frame [⟨wbase P + BitVec.ofNat 64 64, 88⟩] s.mem u.mem →
      Keep [b, tbl] s u → u.gpr b = wbase P → u.gpr tbl = s.syms sym → u.syms = s.syms →
      WP isa (.block is) u Q) :
    WP isa (.block (prologue b sym ++ is)) s Q := by
  rw [prologue_eq, List.cons_append, List.cons_append, List.append_assoc]
  refine WP.cons (exec_addi (by decide)) (WP.cons (exec_logicImm (by decide)) ?_)
  generalize hs₂ : State.write _ b _ = s₂
  have h₂ : s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.syms = s.syms := by
    subst hs₂; exact ⟨rfl, rfl, rfl, rfl⟩
  have e₂ : s₂.gpr b = wbase P := by
    subst hs₂
    simp only [RegUpd.gpr_write_self, hB]
    exact Align.align_eq P
  have g₂ : ∀ r, r ≠ b → s₂.gpr r = s.gpr r := fun r hr => by
    subst hs₂; simp only [RegUpd.gpr_write_of_ne _ _ hr]
  refine Spill.save_ok (s := s₂) (by rw [e₂]; exact Align.align_al P) savedSlots_ok
    (fun p hp => by
      rw [e₂, h₂.2.2.1]
      exact wbase_in hP (by have := savedSlots_lt p hp; omega_arith)) ?_
  rw [List.cons_append, List.nil_append]
  refine WP.cons exec_lla ?_
  have sv : Spill.Saved (wbase P) s.gpr savedSlots
      (Spill.saveMem s₂.mem (s₂.gpr b) s₂.gpr savedSlots) := by
    have h := Spill.saveMem_saved savedSlots_fits s₂.mem (s₂.gpr b) s₂.gpr
    rw [e₂] at h
    intro p hp
    rw [e₂, h p hp, g₂ p.1 (fun e => hb.1 (by
      rw [← e]; exact savedSlots_fst p hp))]
  have fr : Frame [⟨wbase P + BitVec.ofNat 64 64, 88⟩] s.mem
      (Spill.saveMem s₂.mem (s₂.gpr b) s₂.gpr savedSlots) := by
    rw [e₂, h₂.1]
    exact Spill.saveMem_frame savedSlots_lt (by decide) _ _ _
  refine k _ sv fr ⟨fun r hr => ?_, h₂.2.1, h₂.2.2.1⟩
    (by simp only [State.write]; rw [ite_eq_right hb.2]; exact e₂)
    (by simp [State.write, h₂.2.2.2]) h₂.2.2.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [State.write, hr.2, ite_false]
  exact g₂ r hr.1

/-- The epilogue: the callee-saved registers restored from the slots. -/
theorem epilogue_ok (u : State) (b : Reg) (hb : Spill.Restorable b savedSlots) {P : Addr} (hB : u.gpr b = wbase P)
    (hP : (⟨P, 256⟩ : Region) ∈ u.wr) {g : Reg → BitVec 64} (hsv : Spill.Saved (wbase P) g savedSlots u.mem) :
    WP isa (.block (epilogue b)) u (Spill.Restored g savedSlots u) := by
  rw [epilogue_eq, ← List.append_nil (Spill.restoreCode b savedSlots)]
  refine Spill.restore_ok (Align.align_al P) hB savedSlots_ok hb (fun p hp => ?_) hsv
    fun s' R => WP.block_nil R
  have ⟨r, hr, hc⟩ := wbase_in (rs := u.wr) hP (d := p.2) (w := 8) (by have := savedSlots_lt p hp; omega_arith)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A restored register holds what it held before the prologue. -/
theorem restored_saved {g : Reg → BitVec 64} {u s' : State} (R : Spill.Restored g savedSlots u s') {r : Reg}
    (hr : r ∈ saved) : s'.gpr r = g r :=
  R.gpr_of (.inl (by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide))

/-! ## The function -/

/-- What ECB may assume: the schedule and the table readable, the table
64-byte aligned, the `n` blocks and the working space writable, all apart,
none wrapping around, and 12 or 16 rounds. -/
structure EcbPre (s : State) : Prop where
  key : (⟨s.gpr .a0, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : (s.gpr .a0).toNat + 128 ≤ 2 ^ 64
  data : (⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩ : Region) ∈ s.wr
  fit : (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64
  scr : (⟨s.gpr .a4, 256⟩ : Region) ∈ s.wr
  keyData : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
  keyScr : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a4, 256⟩
  dataScr : (⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, 256⟩
  nv : (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 16
  trd : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region) ∈ s.rd ++ s.wr
  tal : (s.syms Impl.Cast5.s1234Sym).toNat % 64 = 0
  held : Held s.mem (s.syms Impl.Cast5.s1234Sym) Impl.Cast5.s1234
  tblData : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
  tblScr : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .a4, 256⟩

/-- What ECB guarantees. -/
structure EcbPost (up : Bool) (s s' : State) : Prop where
  done : ∀ b < (s.gpr .a3).toNat, Spec.Cast5.blockAt s'.mem (wAt (s.gpr .a2) b) =
    cipher up (Spec.Cast5.scheduleAt s.mem (s.gpr .a0)) (s.gpr .a1).toNat
      (Spec.Cast5.blockAt s.mem (wAt (s.gpr .a2) b))
  saved : ∀ r ∈ saved, s'.gpr r = s.gpr r

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Cast5.RISCV64.ecb up) s (EcbPost up s) := by
  have fit := h.fit
  have sub88 : Region.Sub ⟨wbase (s.gpr .a4) + BitVec.ofNat 64 64, 88⟩ ⟨s.gpr .a4, 256⟩ := wbase_sub _ (by decide)
  unfold Impl.Cast5.RISCV64.ecb
  apply WP.seq
  rw [← List.append_nil (prologue wkE _)]
  refine prologue_ok s wkE (by decide) _ rfl h.scr fun s₀ sv₀ fr₀ k₀ w₀ t₀ sy₀ => WP.block_nil ?_
  have g₀ (q : Reg) (hq : q ∉ [wkE, tbl] := by decide) : s₀.gpr q = s.gpr q := k₀.gpr hq
  have dS : ∀ r ∈ [(⟨wbase (s.gpr .a4) + BitVec.ofNat 64 64, 88⟩ : Region)],
      Region.Disjoint ⟨s.gpr .a0, 128⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.keyScr.sub_right sub88
  have dB (b : Nat) (hb : b < (s.gpr .a3).toNat) :
      ∀ r ∈ [(⟨wbase (s.gpr .a4) + BitVec.ofNat 64 64, 88⟩ : Region)], Region.Disjoint ⟨wAt (s.gpr .a2) b, 8⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (h.dataScr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right sub88
  have L : LoopEnv (s.gpr .a0) (s.gpr .a2) (s.syms Impl.Cast5.s1234Sym) (s.gpr .a1).toNat (s.gpr .a3).toNat s₀ :=
    { r3 := g₀ _
      r4 := by rw [g₀ rnd]; simp
      nv := h.nv
      tbl := t₀
      key := by rw [k₀.2.1, k₀.2.2]; exact h.key
      kfit := h.kfit
      data := by rw [k₀.2.2]; exact h.data
      keyData := h.keyData
      fit := fit
      trd := by rw [k₀.2.1, k₀.2.2]; exact h.trd
      tal := h.tal
      held := held_frame fr₀ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [s1234_len]; exact h.tblScr.sub_right sub88)
        (by rw [s1234_len]; decide) h.held
      tblData := h.tblData }
  have I0 : EInv (s.gpr .a0) (s.gpr .a2) (s.gpr .a1).toNat (s.gpr .a3).toNat up s₀ 0 s₀ :=
    ⟨by omega_arith, by rw [g₀ dat]; simp [wAt], by rw [g₀ cnt]; simp, Keep.refl _ _,
      fun b hb => absurd hb (by omega_arith), fun _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (Q := EInv (s.gpr .a0) (s.gpr .a2) (s.gpr .a1).toNat (s.gpr .a3).toNat up s₀
    (s.gpr .a3).toNat) ?_ fun u U => ?_
  · refine WP.ite (s.gpr .a3 == 0) (by rw [eval_zero, g₀ cnt]) (fun hz => ?_) (fun hz => ?_)
    · have hn : (s.gpr .a3).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
      exact WP.block_nil (hn ▸ I0)
    · have hn : 0 < (s.gpr .a3).toNat := by
        have : s.gpr .a3 ≠ 0 := by simpa using hz
        have : (s.gpr .a3).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
        omega_arith
      exact loop_run L hn I0
  · have r7 : u.gpr wkE = wbase (s.gpr .a4) := by rw [U.keep.gpr (by decide), w₀]
    have hsv : Spill.Saved (wbase (s.gpr .a4)) s.gpr savedSlots u.mem :=
      sv₀.frame U.frame fun p hp r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact h.dataScr.symm.sub_left (wbase_sub _ (by have := savedSlots_lt p hp; omega_arith))
    refine WP.mono (epilogue_ok u wkE (by decide) r7 (by rw [U.keep.2.2, k₀.2.2]; exact h.scr) hsv)
      fun s' R => ⟨fun b hb => ?_, fun r hr => restored_saved R hr⟩
    rw [R.mem, U.done b hb, Proof.Cast5.scheduleAt_frame fr₀ dS, blockAt_frame fr₀ (dB b hb)]

end VG.Proof.Cast5.RISCV64
