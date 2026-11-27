module

public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Curve448.AArch64.Fast.Finish`, which this module and modules that import it used -/

section

/-!
# The end of a product: the last carries and the result

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside write8_eq read8_eq limbs)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem read8_eq_word (m : Mem) (base : Addr) (d : Nat) :
    m.read (base + BitVec.ofNat 64 d) 8 = word m base d := by
  simp only [word, off, Mem.readW, BitVec.setWidth_eq]

theorem word_writeW (m : Mem) (base : Addr) {d d' : Nat} (hd : d + 8 ≤ 8192) (hd' : d' + 8 ≤ 8192)
    (h : d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') (v : BitVec 64) :
    word (m.writeW (off base d) v) base d' = if d' = d then v else word m base d' := by
  by_cases e : d' = d
  · rw [ite_eq_left e, e, word, Mem.readW_writeW_self64]
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem st_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat}
    (h8 : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ Keeps [] s t := by
  obtain w := hs.write (d := d) (n := 8) hd
  obtain oe : d % 8 = 0 ∧ d < 32768 := ⟨h8, by omega_arith⟩
  refine WP.of_runBlock ⟨_, by
    simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, read_x,
      State.store, oe, and_self, hs.x3, w, ite_true, Option.bind_some]; rfl, ?_⟩
  exact ⟨by simp only [BitVec.setWidth_eq, write8_eq], fun _ _ => rfl, rfl, rfl⟩

def finA : List Instr :=
  [.add .x .x4 .x4 CH, .add .x .x6 .x6 CH, .add .x .x6 .x6 CL,
    .lsr .x .x8 .x4 56, .logic .and .x .x4 .x4 MASK, .add .x .x5 .x5 .x8,
    .lsr .x .x8 .x6 56, .logic .and .x .x6 .x6 MASK, .add .x .x7 .x7 .x8]

theorem finA_ok (s : State) (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1))
    {l0 l1 l4 l5 cl ch : Nat} (h0 : (s.gpr .x4).toNat = l0) (h1 : (s.gpr .x5).toNat = l1)
    (h4 : (s.gpr .x6).toNat = l4) (h5 : (s.gpr .x7).toNat = l5)
    (hl : (s.gpr CL).toNat = cl) (hh : (s.gpr CH).toNat = ch)
    (c0 : l0 + ch < 2 ^ 64) (c4 : l4 + cl + ch < 2 ^ 64) (b1 : l1 < 2 ^ 56) (b5 : l5 < 2 ^ 56) :
    WP isa (.block finA) s fun t =>
      (t.gpr .x4).toNat = (l0 + ch) % radix ∧ (t.gpr .x5).toNat = l1 + (l0 + ch) / radix ∧
      (t.gpr .x6).toNat = (l4 + cl + ch) % radix ∧ (t.gpr .x7).toNat = l5 + (l4 + cl + ch) / radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [finA, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 56 < 64 from by decide, ite_true]; rfl, ?_⟩
  obtain m56 : ∀ x : BitVec 64, (x &&& BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = x.toNat % radix := by
    intro x
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = 2 ^ 56 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    rfl
  simp only [CL, CH, MASK] at hm hl hh
  simp only [State.read, RegUpd.gpr_write, BitVec.setWidth_eq, CL, CH, MASK,
    reduceCtorEq, ite_true, ite_false, hm]
  refine ⟨?_, ?_, ?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · rw [m56, BitVec.toNat_add, h0, hh, Nat.mod_eq_of_lt c0]
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, h1, h0, hh,
      Nat.mod_eq_of_lt c0, Nat.shiftRight_eq_div_pow]
    simp only [radix]
    omega_arith
  · rw [m56, BitVec.toNat_add, BitVec.toNat_add, h4, hh, hl,
      Nat.mod_eq_of_lt (by omega_arith : l4 + ch < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith : l4 + ch + cl < 2 ^ 64)]
    congr 1; omega_arith
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, h5, h4,
      hh, hl, Nat.mod_eq_of_lt (by omega_arith : l4 + ch < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_arith : l4 + ch + cl < 2 ^ 64), Nat.shiftRight_eq_div_pow]
    simp only [radix]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2, ite_false]

/-- The limbs that `finish` writes. -/
def finVal (l : Nat → Nat) (cl ch : Nat) (i : Nat) : Nat :=
  match i with
  | 0 => (l 0 + ch) % radix
  | 1 => l 1 + (l 0 + ch) / radix
  | 4 => (l 4 + cl + ch) % radix
  | 5 => l 5 + (l 4 + cl + ch) / radix
  | i => l i

theorem finish_split (ro : Reg) (o : Nat) : finish ro o =
    ([.ldr .x .x4 ro o, .ldr .x .x5 ro (o + 8), .ldr .x .x6 ro (o + 32), .ldr .x .x7 ro (o + 40)] :
      List Instr) ++
    finA ++ ([.str .x .x4 ro o, .str .x .x5 ro (o + 8), .str .x .x6 ro (o + 32),
      .str .x .x7 ro (o + 40)] : List Instr) := rfl

theorem finish_ok {s : State} {base : Addr} (hs : Scr s base) {ro : Reg} {D o : Nat}
    (hp : PtrOk s base ro D o) (hro : ro ∉ [.x4, .x5, .x6, .x7, .x8])
    (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) {l : Nat → Nat}
    (hl : ∀ i < 8, (word s.mem base (o + 8 * i)).toNat = l i) (hb : ∀ i < 8, l i < radix)
    {cl ch : Nat} (hcl : (s.gpr CL).toNat = cl) (hch : (s.gpr CH).toNat = ch)
    (c0 : l 0 + ch < 2 ^ 64) (c4 : l 4 + cl + ch < 2 ^ 64) :
    WP isa (.block (finish ro D)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = finVal l cl ch i) ∧ Outside base o 64 s.mem t.mem ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  have ho : o + 64 ≤ 8192 := hp.fit
  have hal := hp.al
  have hlt := hp.lt
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hro
  obtain ⟨n4, n5, n6, n7, n8⟩ := hro
  obtain rd : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 := fun d hd => hs.read hd
  obtain ae : ∀ d, d % 8 = 0 → d < 32768 → d % 8 = 0 ∧ d < 32768 := fun d h1 h2 => ⟨h1, h2⟩
  obtain p0 : s.gpr ro + BitVec.ofNat 64 D = off base o := by
    have := hp.ptr 0; simp only [Nat.add_zero] at this; exact this
  obtain p8 := hp.ptr 8
  obtain p32 := hp.ptr 32
  obtain p40 := hp.ptr 40
  rw [finish_split, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.load,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      ite_false, n4, n5, n6, p0, p8, p32, p40,
      ae D hal (by omega_arith), ae (D + 8) (by omega_arith) (by omega_arith), ae (D + 32) (by omega_arith) (by omega_arith),
      ae (D + 40) (by omega_arith) (by omega_arith), and_self, ite_true,
      rd o (by omega_arith), rd (o + 8) (by omega_arith), rd (o + 32) (by omega_arith),
      rd (o + 40) (by omega_arith), Option.map_some, Option.bind_some]; rfl, rfl⟩) fun t ht => ?_
  subst ht
  rw [WP.block_append_iff]
  have wv : ∀ i < 8, (word s.mem base (o + 8 * i)).toNat = l i := hl
  refine WP.mono (finA_ok _ (by simp only [RegUpd.gpr_write, MASK, reduceCtorEq, ite_false]; exact hm)
    (l0 := l 0) (l1 := l 1) (l4 := l 4) (l5 := l 5)
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 0 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 1 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 4 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 5 (by decide))
    (by simp only [RegUpd.gpr_write, CL, reduceCtorEq, ite_false]; exact hcl)
    (by simp only [RegUpd.gpr_write, CH, reduceCtorEq, ite_false]; exact hch)
    c0 c4 (hb 1 (by decide)) (hb 5 (by decide))) fun u ⟨u4, u5, u6, u7, um, uk⟩ => ?_
  obtain uro : u.gpr ro = s.gpr ro := by
    rw [uk.1 ro (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n4, n5, n6, n7, n8⟩)]
    simp only [RegUpd.gpr_write, n4, n5, n6, n7, ite_false]
  obtain u3 : u.gpr .x3 = base := by
    rw [uk.1 .x3 (by decide)]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
    exact hs.x3
  obtain u12 : u.gpr .x12 = 0x0fffffff := by
    rw [uk.1 .x12 (by decide)]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
    exact hs.mask
  obtain us : Scr u base := ⟨u3, u12, uk.2.2 ▸ hs.wr, hs.nowrap⟩
  have mu : u.mem = s.mem := um
  -- the four stores
  obtain sw : ∀ (t : State) (r : Reg) (E d : Nat), Scr t base →
      t.gpr ro + BitVec.ofNat 64 E = off base d → E % 8 = 0 → E < 32768 → d + 8 ≤ 8192 →
      WP isa (.block [.str .x r ro E]) t fun t' =>
        (∀ d', d' + 8 ≤ 8192 → (d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') →
          word t'.mem base d' = if d' = d then t.gpr r else word t.mem base d') ∧
        Outside base d 8 t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
    intro t r E d ht hE h8 hlt hd
    refine WP.mono (stAt_ok ht r ro hE h8 hlt hd) fun t' ⟨hm, hk⟩ =>
      ⟨fun d' hd' hs => ?_, ?_, ?_, hk.2.1, hk.2.2⟩
    · rw [hm]; exact word_writeW _ _ hd hd' hs _
    · rw [hm]; exact writeW_outside _ _ _ hd
    · funext q; exact hk.1 q (by simp)
  rw [show ([.str .x .x4 ro D, .str .x .x5 ro (D + 8), .str .x .x6 ro (D + 32),
      .str .x .x7 ro (D + 40)] : List Instr) =
      [.str .x .x4 ro D] ++ [.str .x .x5 ro (D + 8)] ++ [.str .x .x6 ro (D + 32)] ++
        [.str .x .x7 ro (D + 40)] from rfl]
  simp only [List.append_assoc]
  obtain ss : ∀ t : State, t.gpr .x3 = base → t.gpr .x12 = 0x0fffffff → t.wr = u.wr → Scr t base :=
    fun t h1 h2 h3 => ⟨h1, h2, h3 ▸ us.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (sw u .x4 D o us (by rw [uro]; exact p0) hal (by omega_arith) (by omega_arith))
    fun t1 ⟨t1w, t1o, t1g, t1r, t1wr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sw t1 .x5 (D + 8) (o + 8) (ss t1 (by simp only [*]) (by simp only [*]) (by simp only [*]))
    (by rw [t1g, uro]; exact p8) (by omega_arith) (by omega_arith) (by omega_arith)) fun t2 ⟨t2w, t2o, t2g, t2r, t2wr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sw t2 .x6 (D + 32) (o + 32) (ss t2 (by simp only [*]) (by simp only [*]) (by simp only [*]))
    (by rw [t2g, t1g, uro]; exact p32) (by omega_arith) (by omega_arith) (by omega_arith)) fun t3 ⟨t3w, t3o, t3g, t3r, t3wr⟩ => ?_
  refine WP.mono (sw t3 .x7 (D + 40) (o + 40) (ss t3 (by simp only [*]) (by simp only [*]) (by simp only [*]))
    (by rw [t3g, t2g, t1g, uro]; exact p40) (by omega_arith) (by omega_arith) (by omega_arith)) fun t4 ⟨t4w, t4o, t4g, t4r, t4wr⟩ => ?_
  obtain keep : ∀ d, d + 8 ≤ 8192 → (d + 8 ≤ o ∨ o + 8 ≤ d) → (d + 8 ≤ o + 8 ∨ o + 16 ≤ d) →
      (d + 8 ≤ o + 32 ∨ o + 40 ≤ d) → (d + 8 ≤ o + 40 ∨ o + 48 ≤ d) →
      word t4.mem base d = word s.mem base d := by
    intro d hd h1 h2 h3 h4
    rw [t4w d hd (by omega_arith), ite_eq_right (by omega_arith), t3w d hd (by omega_arith), ite_eq_right (by omega_arith),
      t2w d hd (by omega_arith), ite_eq_right (by omega_arith), t1w d hd (by omega_arith), ite_eq_right (by omega_arith), mu]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_arith
    · change (word t4.mem base (o)).toNat = _
      rw [t4w (o) (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), t3w (o) (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), t2w (o) (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), t1w (o) (by omega_arith) (by omega_arith), ite_eq_left rfl]
      rw [u4]; rfl
    · change (word t4.mem base (o + 8)).toNat = _
      rw [t4w (o + 8) (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), t3w (o + 8) (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), t2w (o + 8) (by omega_arith) (by omega_arith), ite_eq_left rfl]
      rw [t1g]
      rw [u5]; rfl
    · change (word t4.mem base (o + 16)).toNat = _
      rw [keep _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hl 2 (by decide)
    · change (word t4.mem base (o + 24)).toNat = _
      rw [keep _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hl 3 (by decide)
    · change (word t4.mem base (o + 32)).toNat = _
      rw [t4w (o + 32) (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), t3w (o + 32) (by omega_arith) (by omega_arith), ite_eq_left rfl]
      rw [t2g, t1g]
      rw [u6]; rfl
    · change (word t4.mem base (o + 40)).toNat = _
      rw [t4w (o + 40) (by omega_arith) (by omega_arith), ite_eq_left rfl]
      rw [t3g, t2g, t1g]
      rw [u7]; rfl
    · change (word t4.mem base (o + 48)).toNat = _
      rw [keep _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hl 6 (by decide)
    · change (word t4.mem base (o + 56)).toNat = _
      rw [keep _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hl 7 (by decide)
  · rw [← mu]
    obtain w : ∀ {m m' : Mem} {d : Nat}, Outside base d 8 m m' → o ≤ d → d + 8 ≤ o + 64 →
        Outside base o 64 m m' := fun h h1 h2 => h.mono h1 h2
    exact (w t1o (by omega_arith) (by omega_arith)).trans ((w t2o (by omega_arith) (by omega_arith)).trans
      ((w t3o (by omega_arith) (by omega_arith)).trans (w t4o (by omega_arith) (by omega_arith))))
  · refine ⟨fun q hq => ?_, ?_, ?_⟩
    · rw [t4g, t3g, t2g, t1g, uk.1 q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, ite_false]
    · rw [t4r, t3r, t2r, t1r, uk.2.1]; rfl
    · rw [t4wr, t3wr, t2wr, t1wr, uk.2.2]; rfl

end VG.Proof.Curve448.AArch64.Fast

end

end

/-!
# The start of a product: operands in registers, constants, operand sums

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem A_inj : ∀ i < 8, ∀ j < 8, i ≠ j → Mul.A i ≠ Mul.A j := by decide

theorem A_mem : ∀ i < 8, Mul.A i ∈ [Reg.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9] := by decide

def aRegs : List Reg := [.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9]

theorem loadA_ok {s : State} {base : Addr} (hs : Scr s base) {ra : Reg} {D a : Nat}
    (hp : PtrOk s base ra D a) (hra : ra ∉ aRegs) :
    WP isa (.block (loadA ra D)) s fun t =>
      (∀ i < 8, t.gpr (Mul.A i) = word s.mem base (a + 8 * i)) ∧ t.mem = s.mem ∧
      Keeps aRegs s t := by
  have e : loadA ra D = (List.range 8).flatMap fun i => [.ldr .x (Mul.A i) ra (D + 8 * i)] := by
    simp only [loadA]
    rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (Mul.A i) = word s.mem base (a + 8 * i)) ∧ t.mem = s.mem ∧ Keeps aRegs s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (ldPtr_ok ts (Mul.A n) (hp.of_keeps tk hra) hn) fun u ⟨uv, um, uk⟩ => ?_
  refine ⟨fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [uv, tm]
    · have hne : Mul.A i ∉ [Mul.A n] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact A_inj i (by omega_using [hn, hi]) n hn h
      rw [uk.1 _ hne, tv i (by omega_using [hi, h])]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact A_mem n hn

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun t =>
      t.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) ∧ t.gpr ZERO = 0 ∧ t.mem = s.mem ∧
      Keeps [MASK, ZERO] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide,
      show 16 * 2 < 64 from by decide, show 16 * 3 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [MASK, ZERO, State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [ZERO, RegUpd.gpr_write, ite_true]
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem add_ok (s : State) (d n m : Reg) :
    WP isa (.block [.add .x d n m]) s fun t =>
      t.gpr d = s.gpr n + s.gpr m ∧ t.mem = s.mem ∧ Keeps [d] s t := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, read_x, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_write, hq, ite_false]

theorem stw_ok {t : State} {base : Addr} (ht : Scr t base) (r : Reg) {d : Nat} (h8 : d % 8 = 0)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [st r d]) t fun t' =>
      (∀ d', d' + 8 ≤ 8192 → (d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') →
        word t'.mem base d' = if d' = d then t.gpr r else word t.mem base d') ∧
      Outside base d 8 t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine WP.mono (st_ok ht r h8 hd) fun t' ⟨hm, hk⟩ => ⟨fun d' hd' hs => ?_, ?_, ?_, hk.2.1, hk.2.2⟩
  · rw [hm]; exact word_writeW _ _ hd hd' hs _
  · rw [hm]; exact writeW_outside _ _ _ hd
  · funext q; exact hk.1 q (by simp)

theorem A_ne : ∀ i < 8, Mul.A i ∉ [Reg.x10, .x11, .x13] := by decide

/-- One step of the operand sums of a product. -/
theorem kakbStep_ok {s : State} {base : Addr} (hs : Scr s base) {rb : Reg} {D b i : Nat}
    (hp : PtrOk s base rb D b) (hb : b + 64 ≤ ACC) (hrb : rb ∉ [Reg.x10, .x11, .x13]) (hi : i < 4) :
    WP isa (.block [.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      .ldr .x Mul.R.t rb (D + 8 * i), .ldr .x Mul.R.p1 rb (D + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)]) s fun t =>
      word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4)) ∧
      word t.mem base (KB + 8 * i) = word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i) ∧
      Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t ∧
      (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KA + 8 * i ∨ KA + 8 * i + 8 ≤ d) →
        (d + 8 ≤ KB + 8 * i ∨ KB + 8 * i + 8 ≤ d) → word t.mem base d = word s.mem base d) := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = ACC := rfl
  have hKB : KB = ACC + 32 := rfl
  have hal := hp.al
  have hlt := hp.lt
  have hrb' : ∀ q ∈ [Reg.x10, .x11, .x13], rb ≠ q := fun q hq e => hrb (e ▸ hq)
  rw [show [Instr.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      .ldr .x Mul.R.t rb (D + 8 * i), .ldr .x Mul.R.p1 rb (D + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)] =
      [Instr.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4))] ++ [st Mul.R.p0 (KA + 8 * i)] ++
      [.ldr .x Mul.R.t rb (D + 8 * i)] ++ [.ldr .x Mul.R.p1 rb (D + 32 + 8 * i)] ++
      [Instr.add .x Mul.R.t Mul.R.t Mul.R.p1] ++ [st Mul.R.t (KB + 8 * i)] from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (add_ok s _ _ _) fun t1 ⟨v1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stw_ok s1 _ (d := KA + 8 * i) (by omega_using [hA, hKA]) (by omega_using [hi, hA, hKA])) fun t2 ⟨w2, o2, g2, r2, wr2⟩ => ?_
  have s2 : Scr t2 base := ⟨by rw [g2]; exact s1.x3, by rw [g2]; exact s1.mask, wr2 ▸ s1.wr, s1.nowrap⟩
  have p2 : PtrOk t2 base rb D b := (hp.of_keeps k1 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hrb' _ (by simp [Mul.R]))).keep (by rw [g2])
  rw [WP.block_append_iff]
  refine WP.mono (ldPtr_ok s2 Mul.R.t p2 (k := i) (by omega_using [hi])) fun t3 ⟨v3, m3, k3⟩ => ?_
  have s3 : Scr t3 base := s2.of_keeps k3 (by decide)
  have p3 : PtrOk t3 base rb D b := p2.of_keeps k3 (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hrb' _ (by simp [Mul.R]))
  have e3 := p3.ptr (32 + 8 * i)
  rw [← Nat.add_assoc, ← Nat.add_assoc] at e3
  rw [WP.block_append_iff]
  refine WP.mono (ldAt_ok s3 Mul.R.p1 rb e3 (by omega_using [hal]) (by omega_using [hi, hlt]) (by omega_using [hb, hi, hA])) fun t4 ⟨v4, m4, k4⟩ => ?_
  have s4 : Scr t4 base := s3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_ok t4 _ _ _) fun t5 ⟨v5, m5, k5⟩ => ?_
  have s5 : Scr t5 base := s4.of_keeps k5 (by decide)
  refine WP.mono (stw_ok s5 _ (d := KB + 8 * i) (by omega_using [hA, hKB]) (by omega_using [hi, hA, hKB])) fun t6 ⟨w6, o6, g6, r6, wr6⟩ => ?_
  have hb1 : word t2.mem base (b + 8 * i) = word s.mem base (b + 8 * i) := by
    rw [w2 _ (by omega_using [hb, hi, hA]) (by omega_using [hb, hKA]), ite_eq_right (by omega_using [hb, hKA]), m1]
  have hb2 : word t2.mem base (b + 32 + 8 * i) = word s.mem base (b + 32 + 8 * i) := by
    rw [w2 _ (by omega_using [hb, hi, hA]) (by omega_using [hb, hKA]), ite_eq_right (by omega_using [hb, hKA]), m1]
  refine ⟨?_, ?_, ?_, ?_, fun d hd h1 h2 => ?_⟩
  · rw [w6 _ (by omega_using [hi, hA, hKA]) (by omega_using [hKA, hKB]), ite_eq_right (by omega_using [hKA, hKB]), m5, m4, m3, w2 _ (by omega_using [hi, hA, hKA]) (by omega_using []),
      ite_eq_left rfl, v1]
  · rw [w6 _ (by omega_using [hi, hA, hKB]) (by omega_using []), ite_eq_left rfl, v5, k4.1 Mul.R.t (by decide), v3, v4, m3, hb1, hb2]
  · rw [← m1]
    refine (o2.mono (by omega_using []) (by omega_using [hi])).trans ?_
    rw [← m3, ← m4, ← m5]
    exact o6.mono (by omega_using [hKA, hKB]) (by omega_using [hi, hKA, hKB])
  · refine ⟨fun q hq => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [g6, k5.1 q (by simp [Mul.R, hq.1]), k4.1 q (by simp [Mul.R, hq.2.1]),
        k3.1 q (by simp [Mul.R, hq.1]), g2, k1.1 q (by simp [Mul.R, hq.2.2])]
    · rw [r6, k5.2.1, k4.2.1, k3.2.1, r2, k1.2.1]
    · rw [wr6, k5.2.2, k4.2.2, k3.2.2, wr2, k1.2.2]
  · rw [w6 _ hd (by omega_using [h2]), ite_eq_right (by omega_using [h2]), m5, m4, m3, w2 _ hd (by omega_using [h1]),
      ite_eq_right (by omega_using [h1]), m1]

end VG.Proof.Curve448.AArch64.Fast
