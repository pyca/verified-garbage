module

import VerifiedGarbage.Proof.AesCtr.Inc

public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Impl.Modes.X86.Counter
public import VerifiedGarbage.Spec.Ctr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CTR on x86: the increments

`incAt` run once, with its memory as explicit writes (`incMem`): four
words, loaded and byte-reversed, the last plus 1 and each other plus the
carry out of the one after it, reversed again and stored. `incMem_bytes`:
the block it writes is `Spec.Ctr.inc` of the one it read. `inc32At`, GCM's
`inc₃₂` of a counter block's last word, likewise (`inc32Mem`,
`inc32Mem_bytes`): the big-endian word plus 1, modulo 2³².
-/

@[expose] public section

namespace VG.Proof.Modes.X86.Counter

open VG VG.X86 VG.X86.RegUpd VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

/-- A word plus a carry, as `adc` with 0 computes it. -/
abbrev adc0 (a : BitVec 32) (c : Bool) : BitVec 32 := a + 0 + (BitVec.ofBool c).setWidth 32

/-- The carry out of `adc0`. -/
abbrev cout (a : BitVec 32) (c : Bool) : Bool := decide (2 ^ 32 ≤ a.toNat + (0 : BitVec 32).toNat + c.toNat)

/-- The memory after `incAt` on the block at `Q`. -/
def incMem (m : Mem) (Q : Addr) : Mem :=
  let a3 := bswap (m.readW (Q + BitVec.ofNat 64 12) 32)
  let a2 := bswap (m.readW (Q + BitVec.ofNat 64 8) 32)
  let a1 := bswap (m.readW (Q + BitVec.ofNat 64 4) 32)
  let a0 := bswap (m.readW Q 32)
  let c3 := decide (2 ^ 32 ≤ a3.toNat + (1 : BitVec 32).toNat)
  let c2 := cout a2 c3
  let c1 := cout a1 c2
  (((m.writeW (Q + BitVec.ofNat 64 12) (bswap (a3 + 1))).writeW (Q + BitVec.ofNat 64 8) (bswap (adc0 a2 c3))).writeW
    (Q + BitVec.ofNat 64 4) (bswap (adc0 a1 c2))).writeW Q (bswap (adc0 a0 c1))

theorem incr_ok (s : State) {base : Reg} {off : Nat} (hne : base ≠ .eax) {Q : Addr}
    (ha : ∀ d < 16, addr (s.gpr base) (off + d) = Q + BitVec.ofNat 64 d)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa (incAt base off) s = some s' ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = incMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a0 : addr (s.gpr base) off = Q := by simpa using ha 0 (by decide)
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  have sep (m : Mem) (i j : Nat) (hi : i < 4) (hj : j < 4) (hne : i ≠ j) (v : BitVec 32) :
      (m.writeW (Q + BitVec.ofNat 64 (4 * j)) v).readW (Q + BitVec.ofNat 64 (4 * i)) 32 =
        m.readW (Q + BitVec.ofNat 64 (4 * i)) 32 :=
    Mem.readW_writeW_sep (Offset.sep Q (by omega) (by omega) (by omega)) (by decide)
  have sep0 (m : Mem) (j : Nat) (hj : j < 4) (hne : 0 ≠ j) (v : BitVec 32) :
      (m.writeW (Q + BitVec.ofNat 64 (4 * j)) v).readW Q 32 = m.readW Q 32 := by
    simpa using sep m 0 j (by decide) hj hne v
  refine ⟨_, by
    simp only [↓reduceIte, incAt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, ea_mk, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, hne, a0, ha 4 (by decide), ha 8 (by decide), ha 12 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide),
      hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h => by simp only [gpr_setReg, gpr_arithFlags, h, ite_false], ?_, rfl, rfl⟩
  simp only [incMem,
    sep _ 2 3 (by decide) (by decide) (by decide),
    sep _ 1 2 (by decide) (by decide) (by decide),
    sep _ 1 3 (by decide) (by decide) (by decide),
    sep0 _ 1 (by decide) (by decide), sep0 _ 2 (by decide) (by decide), sep0 _ 3 (by decide) (by decide)]

theorem adc0_toNat (a : BitVec 32) (c : Bool) : (adc0 a c).toNat = (a.toNat + c.toNat) % 2 ^ 32 := by
  have e₀ : (0 : BitVec 32).toNat = 0 := rfl
  cases c
  · have e : (BitVec.setWidth 32 (BitVec.ofBool false)).toNat = 0 := rfl
    rw [adc0, BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_false]; omega
  · have e : (BitVec.setWidth 32 (BitVec.ofBool true)).toNat = 1 := rfl
    rw [adc0, BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_true]; omega

theorem cout_toNat (a : BitVec 32) (c : Bool) : (cout a c).toNat = (a.toNat + c.toNat) / 2 ^ 32 := by
  have e₀ : (0 : BitVec 32).toNat = 0 := rfl
  have := a.isLt
  have := c.toNat_le
  rw [cout, e₀]
  by_cases h : 2 ^ 32 ≤ a.toNat + 0 + c.toNat
  · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega
  · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega

theorem incMem_bytes (m : Mem) (Q : Addr) : bytesAt (incMem m Q) Q 16 = Spec.Ctr.inc (bytesAt m Q 16) := by
  have c3 : (decide (2 ^ 32 ≤ (bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat + (1 : BitVec 32).toNat)).toNat =
      ((bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat + 1) / 2 ^ 32 := by
    have := (bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).isLt
    have e₁ : (1 : BitVec 32).toNat = 1 := rfl
    rw [e₁]
    by_cases h : 2 ^ 32 ≤ (bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat + 1
    · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega
    · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega
  apply AesCtr.inc_words32
  · show (bswap _ + 1).toNat = ((bswap _).toNat + 1) % 2 ^ 32
    rw [BitVec.toNat_add]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, c3]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, cout_toNat, c3]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, cout_toNat, cout_toNat, c3]; rfl

theorem incMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (incMem m Q) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide))

/-- The counter's bytes, with every other byte unchanged. -/
theorem incMem_apply (m : Mem) (Q x : Addr) :
    incMem m Q x = if (x - Q).toNat < 16 then
      (Spec.Ctr.inc (bytesAt m Q 16)).getD (x - Q).toNat 0 else m x := by
  split
  · rename_i hi
    have e := congrArg (fun bs : List Byte => bs.getD (x - Q).toNat 0) (incMem_bytes m Q)
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e
    have ex : Q + BitVec.ofNat 64 (x - Q).toNat = x := by bv_omega
    rwa [ex] at e
  · rename_i hi
    exact incMem_frame m Q x (by
      intro r hr hc
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at hc
      omega)

/-! ## GCM's `inc₃₂` -/

/-- The memory after `inc32At` on the word at `Q`. -/
def inc32Mem (m : Mem) (Q : Addr) : Mem := m.writeW Q (bswap (bswap (m.readW Q 32) + 1))

theorem inc32_ok (s : State) {base : Reg} {off : Nat} (hne : base ≠ .eax) {Q : Addr}
    (ha : addr (s.gpr base) off = Q) (hr : InRegions (s.rd ++ s.wr) Q 4) (hw : InRegions s.wr Q 4) :
    ∃ s', runBlock isa (inc32At base off) s = some s' ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = inc32Mem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, inc32At, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, ea_mk, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hne, ha, hr, hw]
    rfl, ?_⟩
  exact ⟨fun r h => by simp only [gpr_setReg, gpr_arithFlags, h, ite_false], rfl, rfl, rfl⟩

/-- The word `inc32At` writes: the big-endian number it held, plus 1,
modulo 2³². -/
theorem inc32Mem_bytes (m : Mem) (Q : Addr) :
    bytesAt (inc32Mem m Q) Q 4 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m Q 4) + 1) 4 := by
  have e : inc32Mem m Q = m.writeW Q (AesCtr.rv32 (AesCtr.rv32 (m.readW Q 32) + 1)) := rfl
  rw [e, AesCtr.bytesAt_writeW_rv32, AesCtr.bytesAt_rv32, AesCtr.toNat_ofNat]
  apply AesCtr.ofNat_congr
  have := (AesCtr.rv32 (m.readW Q 32)).isLt
  have e₁ : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_add, e₁]
  simp only [Nat.reducePow]
  omega

theorem inc32Mem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 4⟩] m (inc32Mem m Q) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 4) (by decide) (by decide))

/-- The word's bytes, with every other byte unchanged. -/
theorem inc32Mem_apply (m : Mem) (Q x : Addr) :
    inc32Mem m Q x = if (x - Q).toNat < 4 then
      (Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt m Q 4) + 1) 4).getD (x - Q).toNat 0 else m x := by
  split
  · rename_i hi
    have e := congrArg (fun bs : List Byte => bs.getD (x - Q).toNat 0) (inc32Mem_bytes m Q)
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e
    have ex : Q + BitVec.ofNat 64 (x - Q).toNat = x := by bv_omega
    rw [ex] at e
    rw [e]
    simp only [bytesAt, List.getD_eq_getElem?_getD]
  · rename_i hi
    exact inc32Mem_frame m Q x (by
      intro r hr hc
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at hc
      omega)

end VG.Proof.Modes.X86.Counter
