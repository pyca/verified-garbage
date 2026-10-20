module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-!
# P-384's Montgomery product modulo `p` as a function on AArch64

`mulFn384` (`Impl/Weierstrass/AArch64/Mont.lean`) is `mulFnS`'s entry and
exit around a body (`body384_ok`) that loads `[b]`, computes the product
(`prod_ok`), reduces its low half (`reds_ok`), adds the high half
(`addHigh_ok`), reduces the sum below `p` against `p` in registers
(`sparseLoad_ok`, `csubM_ok`) and stores it (`mulFn384_ok`).
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- `p`'s words, in the registers `sparseLoadCode` sets. -/
abbrev ms384 : List Reg := [.x23, .x24, .x25, .x26, .x26, .x26]

/-- After the product: its reductions, the high half added, `p` into
registers, the sum reduced below `p` and stored. -/
def finish384 : List Instr :=
  P384Mul.reds ++ (P384Mul.addHigh ++
    (sparseLoadCode ++ (csubM 6 P384Mul.lowRegs .x21 ms384 ++ storesR (roF 6) P384Mul.lowRegs 0)))

/-- What follows the pointers, for the product. -/
def body384 : List Instr :=
  loadsR .x3 P384Mul.bRegs384 0 ++ ((zero7 :: P384Mul.prod) ++ finish384)

/-- What follows the pointers, for the square. -/
def sqrBody384 : List Instr :=
  loadsR (raF 6) P384Sqr.aRegs 0 ++ ((zero7 :: P384Sqr.sq) ++ finish384)

theorem mulFn384_wp {s : State} {Q : State → Prop} : WP isa mulFn384 s Q ↔
    WP isa (.block (zextCode ++ (saveCode 6 ++ (ptrsCode 6 ++ (body384 ++ restoreCode 6))))) s Q := by
  rw [mulFn384, WP.seq_iff, ← WP.block_append_iff]
  simp only [body384, finish384, ptrsCode, List.append_assoc, List.cons_append, List.nil_append]

theorem sqrFn384_wp {s : State} {Q : State → Prop} : WP isa sqrFn384 s Q ↔
    WP isa (.block (zextCode ++ (saveCode 6 ++ (ptrsCode 6 ++ (sqrBody384 ++ restoreCode 6))))) s Q := by
  rw [sqrFn384, WP.seq_iff, ← WP.block_append_iff]
  simp only [sqrBody384, finish384, ptrsCode, List.append_assoc, List.cons_append, List.nil_append]

/-- What the body needs of its registers. -/
theorem body384_regs :
    (∀ r ∈ ([.x16, .x17] : List Reg) ++ (([.x1, .x2, .x3] : List Reg) ++ P384Mul.lowRegs), r ∈ bodyW 6) ∧
    (∀ r ∈ Reg.x1 :: .x2 :: .x3 :: P384Mul.accRegs, r ∈ bodyW 6) ∧
    (∀ r ∈ P384Mul.bRegs384, r ∈ bodyW 6) ∧ (∀ r ∈ Reg.x21 :: P384Mul.lowRegs, r ∈ bodyW 6) ∧
    (∀ r ∈ [Reg.x23, .x24, .x25, .x26], r ∈ bodyW 6) ∧
    (∀ r ∈ Reg.x2 :: P384Mul.lowRegs ++ dRegs 6, r ∈ bodyW 6) ∧ Reg.x7 ∈ bodyW 6 ∧
    P384Mul.bRegs384.Nodup ∧ Reg.x3 ∉ P384Mul.bRegs384 ∧ P384Mul.bRegs384.length = 6 ∧
    P384Mul.accRegs = P384Mul.lowRegs ++ P384Mul.highRegs ∧ P384Mul.lowRegs.length = 6 ∧
    Fresh (.x21 :: P384Mul.lowRegs) ∧ (∀ r ∈ ms384, r ∉ dRegs 6) ∧ P384Mul.lowRegs.Nodup ∧
    roF 6 ∉ bodyW 6 ∧ P384Mul.ra = raF 6 ∧ P384Mul.ra ∉ P384Mul.bRegs384 ∧ Reg.x0 ∉ bodyW 6 ∧
    (∀ r ∈ P384Mul.highRegs, r ∉ ([.x16, .x17] : List Reg) ++ (([.x1, .x2, .x3] : List Reg) ++ P384Mul.lowRegs)) ∧
    (∀ r ∈ P384Mul.lowRegs, r ∉ [Reg.x23, .x24, .x25, .x26]) ∧ Reg.x21 ∉ [Reg.x23, .x24, .x25, .x26] ∧
    Reg.x7 ∉ [Reg.x23, .x24, .x25, .x26] ∧ Reg.x7 ∉ Reg.x21 :: P384Mul.lowRegs ∧
    Reg.x7 ∉ ([.x16, .x17] : List Reg) ++ (([.x1, .x2, .x3] : List Reg) ++ P384Mul.lowRegs) ∧
    Reg.x7 ∉ Reg.x1 :: .x2 :: .x3 :: P384Mul.accRegs ∧
    (∀ r ∈ P384Mul.bRegs384, r ∉ [Reg.x7]) ∧ Reg.x7 ∉ Reg.x2 :: .x3 :: P384Mul.accRegs ∧
    (∀ r ∈ Reg.x2 :: .x3 :: P384Mul.accRegs, r ∈ bodyW 6) ∧ Reg.x27 = raF 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The tail: from `[acc] = X < 2^384 p`, `[po] = X 2^-384 mod p`, changing
only the registers `bodyW 6` and the memory at `[po]`. -/
theorem finish384_ok {s : State} {po : Addr} (hpo : PtrW s (roF 6) po (8 * 6)) (hz : s.gpr .x7 = 0)
    (hX : regsVal s P384Mul.accRegs < 2 ^ 384 * p384) :
    WP isa (.block finish384) s fun s' =>
      (∀ r, r ∉ bodyW 6 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside po 0 (8 * 6) s.mem s'.mem ∧ wordsVal s'.mem po 0 6 < p384 ∧
      wordsVal s'.mem po 0 6 * 2 ^ (64 * 6) % p384 = regsVal s P384Mul.accRegs % p384 := by
  obtain ⟨wR, -, -, wH, wM, wC, -, -, -, -, accE, llen, fr, md, lnd, nro, -, -, -,
    hiK, loM, x21M, x7M, x7H, x7R, -, -, -, -, -, -, -⟩ := body384_regs
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ bodyW 6) →
      ∀ r, r ∉ bodyW 6 → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  have e₃' : regsVal s P384Mul.accRegs = regsVal s P384Mul.lowRegs + 2 ^ (64 * 6) * regsVal s P384Mul.highRegs := by
    rw [show regsVal s P384Mul.accRegs = regsVal s (P384Mul.lowRegs ++ P384Mul.highRegs) by rw [← accE],
      regsVal_append, llen]
  -- The reductions.
  rw [finish384, WP.block_append_iff]
  refine WP.mono (P384Mul.reds_ok s hz) fun s₄ ⟨⟨W, hW, e₄⟩, k₄⟩ => ?_
  have z₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ x7R, hz]
  have hH₄ : regsVal s₄ P384Mul.highRegs = regsVal s P384Mul.highRegs :=
    regsVal_congr fun r hr => k₄.gpr r (hiK r hr)
  -- The high half added.
  rw [WP.block_append_iff]
  refine WP.mono (P384Mul.addHigh_ok s₄ z₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  have z₅ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ x7H, z₄]
  rw [hH₄] at e₅
  -- `p` into registers.
  rw [WP.block_append_iff]
  refine WP.mono (sparseLoad_ok s₅ z₅) fun s₆ ⟨h23, h24, h25, h26, k₆⟩ => ?_
  have z₆ : s₆.gpr .x7 = 0 := by rw [k₆.gpr _ x7M, z₅]
  have hm : regsVal s₆ ms384 = p384 := by
    simp only [regsVal, h23, h24, h25, h26]; rfl
  have hT₆ : regsVal s₆ P384Mul.lowRegs + 2 ^ (64 * 6) * (s₆.gpr .x21).toNat =
      regsVal s₅ P384Mul.lowRegs + 2 ^ 384 * (s₅.gpr .x21).toNat := by
    rw [regsVal_congr fun r hr => k₆.gpr r (loM r hr), k₆.gpr _ x21M]
  -- The sum is below `2p`.
  have hp : P384Mul.p = p384 := by decide
  rw [hp] at e₄
  have hsum : 2 ^ 384 * (regsVal s₅ P384Mul.lowRegs + 2 ^ 384 * (s₅.gpr .x21).toNat) =
      regsVal s P384Mul.accRegs + W * p384 := by
    rw [e₅, Nat.mul_add, e₄, e₃']; omega
  have hlt : regsVal s P384Mul.accRegs + W * p384 < 2 ^ 384 * (2 * p384) := by
    have h2 : W * p384 < 2 ^ 384 * p384 := Nat.mul_lt_mul_of_pos_right hW (by decide)
    omega
  rw [← hsum] at hlt
  have hV := Nat.lt_of_mul_lt_mul_left hlt
  rw [← hT₆] at hV
  -- The sum reduced.
  rw [WP.block_append_iff]
  refine WP.mono (csubM_ok llen rfl (by decide) (by decide) fr md z₆ hm (by decide) hV) fun s₇ ⟨e₇, k₇⟩ => ?_
  -- The store.
  have kr : ∀ r, r ∉ bodyW 6 → s₇.gpr r = s.gpr r := fun r hr => by
    rw [kw k₇ wC r hr, kw k₆ wM r hr, kw k₅ wH r hr, kw k₄ wR r hr]
  have hmem₇ : s₇.mem = s.mem := by rw [k₇.mem, k₆.mem, k₅.mem, k₄.mem]
  have hwr₇ : s₇.wr = s.wr := by rw [k₇.wr, k₆.wr, k₅.wr, k₄.wr]
  have hpo₇ : PtrW s₇ (roF 6) po (8 * 6) :=
    ⟨(kr _ nro).trans hpo.reg, by rw [hwr₇]; exact hpo.st, hpo.enc, hpo.nowrap⟩
  refine WP.mono (storesR_ok _ hpo₇ (o := 0) (by rw [llen]) rfl lnd) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  rw [llen] at e₈ O₈
  have hR : wordsVal s₈.mem po 0 6 = (regsVal s₅ P384Mul.lowRegs + 2 ^ 384 * (s₅.gpr .x21).toNat) % p384 := by
    rw [e₈, e₇, hT₆]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₈.gpr r (by simp), kr r hr]
  · rw [k₈.rd, k₇.rd, k₆.rd, k₅.rd, k₄.rd]
  · rw [k₈.wr, hwr₇]
  · rw [k₈.sp, k₇.sp, k₆.sp, k₅.sp, k₄.sp]
  · intro x hx; rw [O₈ x hx, hmem₇]
  · rw [hR]; exact Nat.mod_lt _ (by decide)
  · rw [hR, Nat.mod_mul_mod, show (64 * 6 : Nat) = 384 from rfl, Nat.mul_comm, hsum,
      Nat.add_mul_mod_self_right]

/-- The P-384 body: `[po] = [pa] [pb] 2^-384 mod p`, changing only the
registers `bodyW 6` and the memory at `[po]`. -/
theorem body384_ok {s : State} {pa pb po : Addr} (hpa : Ptr s (raF 6) pa (8 * 6)) (hpb : Ptr s .x3 pb (8 * 6))
    (hpo : PtrW s (roF 6) po (8 * 6)) (hB : wordsVal s.mem pb 0 6 < p384) :
    WP isa (.block body384) s fun s' =>
      (∀ r, r ∉ bodyW 6 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside po 0 (8 * 6) s.mem s'.mem ∧ wordsVal s'.mem po 0 6 < p384 ∧
      wordsVal s'.mem po 0 6 * 2 ^ (64 * 6) % p384 = wordsVal s.mem pa 0 6 * wordsVal s.mem pb 0 6 % p384 := by
  obtain ⟨-, wA, wB, -, -, -, w7, bnd, b3, blen, -, -, -, -, -, nro, raE, rab, -,
    -, -, -, -, -, -, x7A, b7, -, -, -⟩ := body384_regs
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ bodyW 6) →
      ∀ r, r ∉ bodyW 6 → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  rw [body384, WP.block_append_iff]
  refine WP.mono (loadsEach_ok P384Mul.bRegs384 hpb (a := 0) (by rw [blen]) rfl bnd b3)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hB₁ : regsVal s₁ P384Mul.bRegs384 = wordsVal s.mem pb 0 6 := by
    rw [regsVal_of_loads _ 0 e₁, blen]
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s₁) fun s₂ ⟨z₂, k₂⟩ => ?_
  have hpa₂ : Ptr s₂ P384Mul.ra pa 48 := by
    rw [raE]
    exact (hpa.of_keeps k₁ (by rw [← raE]; exact rab)).of_keeps k₂ (by decide)
  have hB₂ : regsVal s₂ P384Mul.bRegs384 = wordsVal s.mem pb 0 6 := by
    rw [← hB₁]; exact regsVal_congr fun r hr => k₂.gpr r (b7 r hr)
  rw [WP.block_append_iff]
  refine WP.mono (P384Mul.prod_ok hpa₂ z₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ x7A, z₂]
  rw [hB₂, k₂.mem, k₁.mem] at e₃
  have k₁₃ : ∀ r, r ∉ bodyW 6 → s₃.gpr r = s.gpr r := fun r hr => by
    rw [kw k₃ wA r hr, kw k₂ (fun q hq => by simp only [List.mem_singleton] at hq; exact hq ▸ w7) r hr,
      kw k₁ wB r hr]
  have hm₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  have hpo₃ : PtrW s₃ (roF 6) po (8 * 6) :=
    ⟨(k₁₃ _ nro).trans hpo.reg, by rw [k₃.wr, k₂.wr, k₁.wr]; exact hpo.st, hpo.enc, hpo.nowrap⟩
  have hX : regsVal s₃ P384Mul.accRegs < 2 ^ 384 * p384 := by
    rw [e₃]
    exact Nat.mul_lt_mul_of_lt_of_le (by simpa using wordsVal_lt s.mem pa 0 6) (Nat.le_of_lt hB) (by decide)
  refine WP.mono (finish384_ok hpo₃ z₃ hX) fun s' ⟨G, rd, wr, sp, O, V, C⟩ => ?_
  refine ⟨fun r hr => (G r hr).trans (k₁₃ r hr), by rw [rd, k₃.rd, k₂.rd, k₁.rd], by rw [wr, k₃.wr, k₂.wr, k₁.wr],
    by rw [sp, k₃.sp, k₂.sp, k₁.sp], hm₃ ▸ O, V, by rw [C, e₃]⟩

/-- The P-384 square's body: `[po] = [pa]^2 2^-384 mod p`. -/
theorem sqrBody384_ok {s : State} {pa po : Addr} (hpa : Ptr s (raF 6) pa (8 * 6))
    (hpo : PtrW s (roF 6) po (8 * 6)) (hA : wordsVal s.mem pa 0 6 < p384) :
    WP isa (.block sqrBody384) s fun s' =>
      (∀ r, r ∉ bodyW 6 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside po 0 (8 * 6) s.mem s'.mem ∧ wordsVal s'.mem po 0 6 < p384 ∧
      wordsVal s'.mem po 0 6 * 2 ^ (64 * 6) % p384 = wordsVal s.mem pa 0 6 * wordsVal s.mem pa 0 6 % p384 := by
  obtain ⟨-, -, wB, -, -, -, w7, bnd, -, blen, -, -, -, -, -, nro, -, rab, -,
    -, -, -, -, -, -, -, b7, x7S, wS, e27⟩ := body384_regs
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ bodyW 6) →
      ∀ r, r ∉ bodyW 6 → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  have ra27 : raF 6 ∉ P384Sqr.aRegs := by decide
  rw [sqrBody384, WP.block_append_iff]
  refine WP.mono (loadsEach_ok P384Sqr.aRegs hpa (a := 0) (by rw [blen]) rfl bnd ra27)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hA₁ : regsVal s₁ P384Sqr.aRegs = wordsVal s.mem pa 0 6 := by
    rw [regsVal_of_loads _ 0 e₁, blen]
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s₁) fun s₂ ⟨z₂, k₂⟩ => ?_
  have hpa₂ : Ptr s₂ .x27 pa 48 := by
    rw [e27]
    exact (hpa.of_keeps k₁ ra27).of_keeps k₂ (by decide)
  have hA₂ : regsVal s₂ P384Sqr.aRegs = wordsVal s.mem pa 0 6 := by
    rw [← hA₁]; exact regsVal_congr fun r hr => k₂.gpr r (b7 r hr)
  rw [WP.block_append_iff]
  refine WP.mono (P384Sqr.sq_ok hpa₂ z₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ x7S, z₂]
  rw [hA₂] at e₃
  have k₁₃ : ∀ r, r ∉ bodyW 6 → s₃.gpr r = s.gpr r := fun r hr => by
    rw [kw k₃ wS r hr, kw k₂ (fun q hq => by simp only [List.mem_singleton] at hq; exact hq ▸ w7) r hr,
      kw k₁ wB r hr]
  have hm₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  have hpo₃ : PtrW s₃ (roF 6) po (8 * 6) :=
    ⟨(k₁₃ _ nro).trans hpo.reg, by rw [k₃.wr, k₂.wr, k₁.wr]; exact hpo.st, hpo.enc, hpo.nowrap⟩
  have hX : regsVal s₃ P384Mul.accRegs < 2 ^ 384 * p384 := by
    rw [e₃]
    exact Nat.mul_lt_mul_of_lt_of_le (by simpa using wordsVal_lt s.mem pa 0 6) (Nat.le_of_lt hA) (by decide)
  refine WP.mono (finish384_ok hpo₃ z₃ hX) fun s' ⟨G, rd, wr, sp, O, V, C⟩ => ?_
  refine ⟨fun r hr => (G r hr).trans (k₁₃ r hr), by rw [rd, k₃.rd, k₂.rd, k₁.rd], by rw [wr, k₃.wr, k₂.wr, k₁.wr],
    by rw [sp, k₃.sp, k₂.sp, k₁.sp], hm₃ ▸ O, V, by rw [C, e₃]⟩

/-- `vg_p384_mul_mod_p`: `[o] = [a] [b] 2^-384 mod p`. -/
theorem mulFn384_ok {W : Nat} {s : State} (hp : Pre 6 W s)
    (hb : wordsVal s.mem (s.gpr .x0) (arg s .x3) 6 < p384) :
    WP isa mulFn384 s fun s' => abiPreserved s s' ∧ Kept 6 (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 < p384 ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 * 2 ^ (64 * 6) % p384 =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 * wordsVal s.mem (s.gpr .x0) (arg s .x3) 6 % p384) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  rw [mulFn384_wp]
  exact mulFnOf_ok (.inl rfl) (fun _ B => B < p384) (· * ·) (by decide +kernel)
    (fun _ _ _ _ hpa hpb hpo hB => body384_ok hpa hpb hpo hB) hp hb

/-- `vg_p384_sqr_mod_p`: `[o] = [a]^2 2^-384 mod p`. -/
theorem sqrFn384_ok {W : Nat} {s : State} (hp : Pre 6 W s)
    (ha : wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 < p384) :
    WP isa sqrFn384 s fun s' => abiPreserved s s' ∧ Kept 6 (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 < p384 ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) 6 * 2 ^ (64 * 6) % p384 =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 * wordsVal s.mem (s.gpr .x0) (arg s .x2) 6 % p384) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  rw [sqrFn384_wp]
  exact mulFnOf_ok (.inl rfl) (fun A _ => A < p384) (fun A _ => A * A) (by decide +kernel)
    (fun _ _ _ _ hpa _ hpo hA => sqrBody384_ok hpa hpo hA) hp ha

end VG.Proof.Weierstrass.AArch64.Mont
