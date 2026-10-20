module

public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Store
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Ed448 verification on AArch64: a digit of the challenge

Untrusted: everything here is checked by Lean. `digitOf sh`, with `x19 = j`,
leaves in `x11` byte `j` of the challenge's copy at `KB` shifted right by `sh`
(0 or 4) and masked to 4 bits (`digitOf_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off word ofs Outside writeW8_outside writeW8_apply)

/-- A nibble of a byte. -/
def nibOf (b : BitVec 8) (sh : Nat) : Nat := (b.toNat >>> sh) % 16

theorem nibOf_lt (b : BitVec 8) (sh : Nat) : nibOf b sh < 16 := Nat.mod_lt _ (by decide)

/-- **A digit** of the challenge: `x11` := nibble `i` at `BITS + i` of the working space, through `x2`. -/
theorem digitOf_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 114)
    (hc : s.gpr .x19 = BitVec.ofNat 64 i) :
    WP isa (.block digitOf) s fun t =>
      t.gpr .x11 = BitVec.ofNat 64 (s.mem (off base (BITS + i))).toNat ∧ Keeps [.x2, .x11] s t ∧
        t.mem = s.mem := by
  have enc : BITS % 1 = 0 ∧ BITS < 4096 := ⟨Nat.mod_one _, by decide⟩
  have hr : InRegions (s.rd ++ s.wr) (off base (BITS + i)) 1 := hs.read (by simp only [BITS]; omega)
  have ha : base + BitVec.ofNat 64 i + BitVec.ofNat 64 BITS = off base (BITS + i) := by
    rw [off_add', Nat.add_comm]
  apply WP.of_runBlock
  simp only [digitOf, runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self, State.read,
    Size.bits, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hs.x3, hc, ha, State.load, hr, VG.Proof.X448.AArch64.read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.mem (off base (BITS + i))).isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## The nibbles -/

private theorem nib8 : ∀ b : BitVec 8,
    ((((b.setWidth 32).setWidth 64 &&& (15 : BitVec 16).setWidth 64).setWidth 32).setWidth 8 =
      BitVec.ofNat 8 (nibOf b 0)) ∧
    ((((b.setWidth 32).setWidth 64 >>> 4).setWidth 32).setWidth 8 = BitVec.ofNat 8 (nibOf b 4)) := by
  decide +kernel

private theorem dec57 : ∀ j < 57, BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 j ∧
    (BitVec.ofNat 64 j != 0) = decide (j ≠ 0) := by decide +kernel

/-- Byte `j` of the challenge's copy (`x19 = j + 1`), split into its nibbles at `BITS + 2 j`. -/
theorem nibBody_ok {s : State} {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 57)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block nibBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧
      t.mem = (s.mem.writeW (off base (BITS + 2 * j)) (BitVec.ofNat 8 (nibOf (s.mem (off base (KB + j))) 0))).writeW
        (off base (BITS + 2 * j + 1)) (BitVec.ofNat 8 (nibOf (s.mem (off base (KB + j))) 4)) ∧
      Keeps [.x19, .x2, .x4, .x5, .x6] s t := by
  have encK : KB % 1 = 0 ∧ KB < 4096 := ⟨Nat.mod_one _, by decide⟩
  have encB : BITS % 1 = 0 ∧ BITS < 4096 := ⟨Nat.mod_one _, by decide⟩
  have encB1 : (BITS + 1) % 1 = 0 ∧ BITS + 1 < 4096 := ⟨Nat.mod_one _, by decide⟩
  have hr : InRegions (s.rd ++ s.wr) (off base (KB + j)) 1 := hs.read (by simp only [KB]; omega)
  have w0 := hs.write (d := BITS + 2 * j) (n := 1) (by simp only [BITS]; omega)
  have w1 := hs.write (d := BITS + 2 * j + 1) (n := 1) (by simp only [BITS]; omega)
  have ha : base + BitVec.ofNat 64 j + BitVec.ofNat 64 KB = off base (KB + j) := by
    rw [off_add', Nat.add_comm]
  have hsh : BitVec.ofNat 64 j <<< 1 = BitVec.ofNat 64 (2 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have hb0 : base + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 BITS = off base (BITS + 2 * j) := by
    rw [off_add', Nat.add_comm]
  have hb1 : base + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (BITS + 1) = off base (BITS + 2 * j + 1) := by
    rw [off_add', show 2 * j + (BITS + 1) = BITS + 2 * j + 1 by omega]
  apply WP.of_runBlock
  simp only [nibBody, runBlock_cons, runStep_some, runBlock_nil, exec, addr, encK, encB, encB1, and_self,
    State.read, Size.bits, show (1 : Nat) < 4096 from by decide, show (4 : Nat) < 64 from by decide,
    show (1 : Nat) < 64 from by decide, show 16 * 0 < Size.x.bits from by decide,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hs.x3, hc, (dec57 j hj).1, ha, hsh, hb0, hb1, State.load, State.store, hr, w0, w1,
    VG.Proof.X448.AArch64.read1_eq, VG.Proof.X448.AArch64.write1_eq, BitVec.shiftLeft_zero, Nat.mul_zero,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    (nib8 _).1, (nib8 _).2]
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- The nibbles of byte `i` of `b`, at `BITS + 2 i` and `BITS + 2 i + 1`. -/
def NibsAt (base : Addr) (b : Nat → BitVec 8) (m : Mem) (i : Nat) : Prop :=
  m (off base (BITS + 2 * i)) = BitVec.ofNat 8 (nibOf (b i) 0) ∧
    m (off base (BITS + 2 * i + 1)) = BitVec.ofNat 8 (nibOf (b i) 4)

/-- **The nibbles**: the challenge's copy at `KB`, nibble `i` at `BITS + i`; only those 114 bytes
written. -/
theorem nibbles_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa nibbles s fun t =>
      Scr t base ∧ (∀ i < 57, NibsAt base (fun i => s.mem (off base (KB + i))) t.mem i) ∧
      Outside base BITS 114 s.mem t.mem ∧ Keeps [.x19, .x2, .x4, .x5, .x6] s t := by
  have hn := hs.nowrap
  unfold nibbles
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok s 57 (by decide))
    fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have k₁ : Keeps [.x19, .x2, .x4, .x5, .x6] s s₁ := ⟨fun r hr => g₁ r (fun e => hr (e ▸ List.mem_cons_self)), rd₁, wr₁⟩
  refine WP.loop (M := isa) (fun n (t : State) => 1 ≤ n ∧ n ≤ 57 ∧ t.gpr .x19 = BitVec.ofNat 64 n ∧
      Scr t base ∧ (∀ i, n ≤ i → i < 57 → NibsAt base (fun i => s.mem (off base (KB + i))) t.mem i) ∧
      Outside base BITS 114 s.mem t.mem ∧ Keeps [.x19, .x2, .x4, .x5, .x6] s t) ?_ 57 s₁
    ⟨by decide, by decide, c₁, hs.of_keeps k₁ (by decide), fun _ h1 h2 => absurd h2 (by omega),
      by rw [m₁]; exact fun _ _ => rfl, k₁⟩
  intro n t ⟨h1, hn57, ct, ht, nt, ot, kt⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  refine WP.mono (nibBody_ok ht (j := j) (by omega) ct) fun u ⟨cu, mu, ku⟩ => ?_
  have hu : Scr u base := ht.of_keeps ku (by decide)
  have kU : Keeps [.x19, .x2, .x4, .x5, .x6] s u := kt.trans ku
  have hK : t.mem (off base (KB + j)) = s.mem (off base (KB + j)) := by
    have ho : ofs base (off base (KB + j)) = KB + j := ofs_off0' base (by simp only [KB]; omega)
    exact ot _ (Or.inl (by rw [ho]; simp only [KB, BITS]; omega))
  have d0 : BITS + 2 * j < 2 ^ 64 := by simp only [BITS]; omega
  have d1 : BITS + 2 * j + 1 < 2 ^ 64 := by simp only [BITS]; omega
  have nU : ∀ i, j ≤ i → i < 57 → NibsAt base (fun i => s.mem (off base (KB + i))) u.mem i := by
    intro i hi1 hi2
    have e0 : ofs base (off base (BITS + 2 * i)) = BITS + 2 * i := ofs_off0' base (by simp only [BITS]; omega)
    have e1 : ofs base (off base (BITS + 2 * i + 1)) = BITS + 2 * i + 1 :=
      ofs_off0' base (by simp only [BITS]; omega)
    rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
    · refine ⟨?_, ?_⟩
      · rw [mu, writeW8_outside _ _ _ d1 (by rw [e0]; omega), writeW8_apply]; simp only [↓reduceIte, hK]
      · rw [mu, writeW8_apply]; simp only [↓reduceIte, hK]
    · obtain ⟨n0, n1⟩ := nt i (by omega) hi2
      refine ⟨?_, ?_⟩
      · rw [mu, writeW8_outside _ _ _ d1 (by rw [e0]; omega), writeW8_outside _ _ _ d0 (by rw [e0]; omega)]
        exact n0
      · rw [mu, writeW8_outside _ _ _ d1 (by rw [e1]; omega), writeW8_outside _ _ _ d0 (by rw [e1]; omega)]
        exact n1
  have oU : Outside base BITS 114 s.mem u.mem := fun x hx => by
    rw [mu, writeW8_outside _ _ _ d1 (by omega), writeW8_outside _ _ _ d0 (by omega)]; exact ot x hx
  simp only [eval, State.read, BitVec.setWidth_eq, cu, (dec57 j (by omega)).2]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact .inl ⟨rfl, hu, fun i hi => nU i (Nat.zero_le _) hi, oU, kU⟩
  · exact .inr ⟨congrArg some (decide_eq_true (by omega)), j, by omega, by omega, by omega, rfl, hu, nU, oU, kU⟩

end VG.Proof.Ed448.AArch64.Window
