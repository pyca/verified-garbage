import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Proof.Modes.Block16
import VerifiedGarbage.Impl.Modes.AArch64.CbcEnc

/-!
# The steps of CBC encryption on AArch64

The blocks of code of `cbcEncrypt`, each as `copy16` or `xor16` on memory:
`whiten_ok` (the IV into the first block), `encIn_ok` (a block of the data
to the core's buffer), `encOut_ok` (back), `encChain_ok` (the buffer's block
into the next block of the data).
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb ldS stS eorR)

variable {c : Core}

theorem wordAddr_succ (B : Addr) (k : Nat) : wordAddr B (k + 1) = wordAddr B k + BitVec.ofNat 64 8 := by
  simp only [wordAddr]; rw [addr_add, Nat.mul_succ]

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- The buffer's two slots are within reach of a load's offset. -/
theorem buf_imm (hL : Layout c) (w : Nat) (hw : w < 2) : 8 * (c.buf + w) < 32768 := by
  have := hL.small; have := hL.room; have := hL.buf_le; have := hL.G_pos; omega

/-- `ldr t, [b, #o]; ldr u, [b', #o']; eor t, t, u; str t, [b, #o]`, as a
store of the XOR of two loads. -/
theorem xorWord_gen (s : State) (t u b b' : Reg) (htu : t ≠ u) (hbt : b ≠ t) (hbu : b ≠ u) (hb't : b' ≠ t)
    {o o' : Nat} (ho : o % 8 = 0 ∧ o < 32768) (ho' : o' % 8 = 0 ∧ o' < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 o) 8)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr b' + BitVec.ofNat 64 o') 8)
    (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.ldr .x t b o, .ldr .x u b' o', eorR t t u, .str .x t b o] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 o)
        (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64 ^^^ s.mem.readW (s.gpr b' + BitVec.ofNat 64 o') 64) ∧
      (∀ r, r ≠ t → r ≠ u → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldr_ok s t b ho hr
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldr_ok s₁ u b' ho' (by rw [rd₁, wr₁, o₁ _ hb't]; exact hr')
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ t t u
  have b₃ : s₃.gpr b = s.gpr b := by rw [o₃ _ hbt, o₂ _ hbu, o₁ _ hbt]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := str_ok s₃ t b ho (by rw [wr₃, wr₂, wr₁, b₃]; exact hw)
  refine ⟨s₄, ?_, ?_, fun r h1 h2 => by rw [g₄, o₃ r h1, o₂ r h2, o₁ r h1], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show ([.ldr .x t b o, .ldr .x u b' o', eorR t t u, .str .x t b o] : List Instr) =
      [.ldr .x t b o] ++ ([.ldr .x u b' o'] ++ ([eorR t t u] ++ [.str .x t b o])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [m₄, b₃, v₃, v₂, o₂ _ htu, v₁, m₃, m₂, m₁, o₁ _ hb't]

/-- `ldr t, [b, #o]; ldr u, [sb, #8 k]; eor t, t, u; str t, [b, #o]`. -/
theorem xorSlot_ok (s : State) (t u b : Reg) (htu : t ≠ u) (hbt : b ≠ t) (hbu : b ≠ u) (hsb : t ≠ sb)
    {B : Addr} (hB : s.gpr sb = B) {o k : Nat} (ho : o % 8 = 0 ∧ o < 32768) (hk : 8 * k < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 o) 8)
    (hr' : InRegions (s.rd ++ s.wr) (wordAddr B k) 8)
    (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.ldr .x t b o, ldS u k, eorR t t u, .str .x t b o] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 o)
        (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64 ^^^ s.mem.readW (wordAddr B k) 64) ∧
      (∀ r, r ≠ t → r ≠ u → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, m, g, rd, wr⟩ := xorWord_gen s t u b sb htu hbt hbu (Ne.symm hsb) ho ⟨by omega, hk⟩ hr
    (by rw [hB]; exact hr') hw
  exact ⟨s', e, by rw [m, hB], g, rd, wr⟩

/-- The IV at `P` (in `r.ctr`) XORed into the block at `D` (in `r.data`). -/
theorem whiten_ok (r : CtrRegs) (hc6 : r.ctr ≠ .x6) (hc7 : r.ctr ≠ .x7) (hd6 : r.data ≠ .x6) (hd7 : r.data ≠ .x7)
    (s : State) {P D : Addr} (hP : s.gpr r.ctr = P) (hD : s.gpr r.data = D)
    (hrP : ∀ o, o + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 o) 8)
    (hwD : ∀ o, o + 8 ≤ 16 → InRegions s.wr (D + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.ldr .x .x6 r.data 0, .ldr .x .x7 r.ctr 0, eorR .x6 .x6 .x7, .str .x .x6 r.data 0,
        .ldr .x .x6 r.data 8, .ldr .x .x7 r.ctr 8, eorR .x6 .x6 .x7, .str .x .x6 r.data 8] s = some s' ∧
      s'.mem = xor16 s.mem D P ∧ (∀ x, x ≠ .x6 → x ≠ .x7 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := xorWord_gen s .x6 .x7 r.data r.ctr (by decide) hd6 hd7 hc6
    (o := 0) (o' := 0) (by decide) (by decide) (by rw [hD]; exact inRd (hwD 0 (by decide)))
    (by rw [hP]; exact hrP 0 (by decide)) (by rw [hD]; exact hwD 0 (by decide))
  have d₁ : s₁.gpr r.data = D := by rw [g₁ _ hd6 hd7, hD]
  have p₁ : s₁.gpr r.ctr = P := by rw [g₁ _ hc6 hc7, hP]
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := xorWord_gen s₁ .x6 .x7 r.data r.ctr (by decide) hd6 hd7 hc6
    (o := 8) (o' := 8) (by decide) (by decide) (by rw [rd₁, wr₁, d₁]; exact inRd (hwD 8 (by decide)))
    (by rw [rd₁, wr₁, p₁]; exact hrP 8 (by decide)) (by rw [wr₁, d₁]; exact hwD 8 (by decide))
  refine ⟨s₂, ?_, ?_, fun x h1 h2 => by rw [g₂ x h1 h2, g₁ x h1 h2], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [show ([.ldr .x .x6 r.data 0, .ldr .x .x7 r.ctr 0, eorR .x6 .x6 .x7, .str .x .x6 r.data 0,
        .ldr .x .x6 r.data 8, .ldr .x .x7 r.ctr 8, eorR .x6 .x6 .x7, .str .x .x6 r.data 8] : List Instr) =
        [.ldr .x .x6 r.data 0, .ldr .x .x7 r.ctr 0, eorR .x6 .x6 .x7, .str .x .x6 r.data 0] ++
        [.ldr .x .x6 r.data 8, .ldr .x .x7 r.ctr 8, eorR .x6 .x6 .x7, .str .x .x6 r.data 8] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · rw [m₂, m₁, d₁, p₁, hD, hP, add_zero', add_zero']

/-- The block at `A` (in `dataReg`) to the buffer's first block. -/
theorem encIn_ok (hL : Layout c) (hd6 : c.dataReg ≠ .x6) (s : State) {B A : Addr} (hb : s.gpr sb = B)
    (hA : s.gpr c.dataReg = A) (rA : ∀ o, o + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 o) 8)
    (wS : ∀ w < 2, InRegions s.wr (wordAddr B (c.buf + w)) 8) :
    ∃ s', runBlock isa c.encIn s = some s' ∧ s'.mem = copy16 s.mem (wordAddr B c.buf) A ∧
      (∀ x, x ≠ .x6 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := ldr_ok s .x6 c.dataReg (off := 0) (by decide)
    (by rw [hA]; exact rA 0 (by decide))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_ok (s := s₁) (b := B) (k := c.buf) .x6 (by rw [o₁ _ (by decide), hb])
    (by have := buf_imm hL 0 (by decide); omega) (by rw [wr₁]; exact wS 0 (by decide))
  obtain ⟨s₃, e₃, d₃, o₃, m₃, rd₃, wr₃⟩ := ldr_ok s₂ .x6 c.dataReg (off := 8) (by decide)
    (by rw [rd₂, wr₂, rd₁, wr₁, g₂, o₁ _ hd6, hA]; exact rA 8 (by decide))
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_ok (s := s₃) (b := B) (k := c.buf + 1) .x6
    (by rw [o₃ _ (by decide), g₂, o₁ _ (by decide), hb]) (buf_imm hL 1 (by decide))
    (by rw [wr₃, wr₂, wr₁]; exact wS 1 (by decide))
  refine ⟨s₄, ?_, ?_, fun x hx => by rw [g₄, o₃ x hx, g₂, o₁ x hx], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.encIn, show ([.ldr .x .x6 c.dataReg 0, stS c.buf .x6, .ldr .x .x6 c.dataReg 8,
        stS (c.buf + 1) .x6] : List Instr) = [.ldr .x .x6 c.dataReg 0] ++ ([stS c.buf .x6] ++
        ([.ldr .x .x6 c.dataReg 8] ++ ([stS (c.buf + 1) .x6] : List Instr))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · have q₂ : s₂.gpr c.dataReg = A := by rw [g₂, o₁ _ hd6, hA]
    simp only [m₄, m₃, m₂, m₁, d₃, d₁, q₂, hA, add_zero', wordAddr_succ, copy16]

/-- The buffer's first block back to `A` (in `dataReg`), and one block
fewer left. -/
theorem encOut_ok (hL : Layout c) (hd6 : c.dataReg ≠ .x6) (hl6 : c.leftReg ≠ .x6) (s : State)
    {B A : Addr} (hb : s.gpr sb = B) (hA : s.gpr c.dataReg = A)
    (rS : ∀ w < 2, InRegions (s.rd ++ s.wr) (wordAddr B (c.buf + w)) 8)
    (wA : ∀ o, o + 8 ≤ 16 → InRegions s.wr (A + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa c.encOut s = some s' ∧ s'.mem = copy16 s.mem A (wordAddr B c.buf) ∧
      s'.gpr c.leftReg = s.gpr c.leftReg - BitVec.ofNat 64 1 ∧
      (∀ x, x ≠ .x6 → x ≠ c.leftReg → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (s := s) (b := B) (k := c.buf) .x6 hb
    (by have := buf_imm hL 0 (by decide); omega) (rS 0 (by decide))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := str_ok s₁ .x6 c.dataReg (off := 0) (by decide)
    (by rw [wr₁, o₁ _ hd6, hA]; exact wA 0 (by decide))
  obtain ⟨s₃, e₃, d₃, o₃, m₃, rd₃, wr₃⟩ := ldS_ok (s := s₂) (b := B) (k := c.buf + 1) .x6
    (by rw [g₂, o₁ _ (by decide), hb]) (buf_imm hL 1 (by decide)) (by rw [rd₂, wr₂, rd₁, wr₁]; exact rS 1 (by decide))
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := str_ok s₃ .x6 c.dataReg (off := 8) (by decide)
    (by rw [wr₃, wr₂, wr₁, o₃ _ hd6, g₂, o₁ _ hd6, hA]; exact wA 8 (by decide))
  obtain ⟨s₅, e₅, l₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ c.leftReg c.leftReg (v := 1) (by decide)
  have lf : s₄.gpr c.leftReg = s.gpr c.leftReg := by rw [g₄, o₃ _ hl6, g₂, o₁ _ hl6]
  refine ⟨s₅, ?_, ?_, by rw [l₅, lf], fun x h1 h2 => by rw [o₅ x h2, g₄, o₃ x h1, g₂, o₁ x h1],
    by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.encOut, show ([ldS .x6 c.buf, .str .x .x6 c.dataReg 0, ldS .x6 (c.buf + 1), .str .x .x6 c.dataReg 8,
        .subImm .x c.leftReg c.leftReg 1] : List Instr) = [ldS .x6 c.buf] ++ ([.str .x .x6 c.dataReg 0] ++
        ([ldS .x6 (c.buf + 1)] ++ ([.str .x .x6 c.dataReg 8] ++ ([.subImm .x c.leftReg c.leftReg 1] : List Instr))))
        from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₅]
  · have q₁ : s₁.gpr c.dataReg = A := by rw [o₁ _ hd6, hA]
    have q₃ : s₃.gpr c.dataReg = A := by rw [o₃ _ hd6, g₂, q₁]
    simp only [m₅, m₄, m₃, m₂, m₁, d₃, d₁, q₁, q₃, add_zero', wordAddr_succ, copy16]

/-- The buffer's first block XORed into the block at `A + 16` (`A` in
`dataReg`). -/
theorem encChain_ok (hL : Layout c) (hd6 : c.dataReg ≠ .x6) (hd7 : c.dataReg ≠ .x7) (s : State) {B A : Addr}
    (hb : s.gpr sb = B) (hA : s.gpr c.dataReg = A)
    (rS : ∀ w < 2, InRegions (s.rd ++ s.wr) (wordAddr B (c.buf + w)) 8)
    (wA : ∀ o, o + 8 ≤ 16 → InRegions s.wr (A + BitVec.ofNat 64 (16 + o)) 8) :
    ∃ s', runBlock isa c.encChain s = some s' ∧
      s'.mem = xor16 s.mem (A + BitVec.ofNat 64 16) (wordAddr B c.buf) ∧
      (∀ x, x ≠ .x6 → x ≠ .x7 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := xorSlot_ok s .x6 .x7 c.dataReg (by decide) hd6 hd7 (by decide) hb
    (o := 16) (k := c.buf) (by decide) (by have := buf_imm hL 0 (by decide); omega)
    (by rw [hA]; exact inRd (wA 0 (by decide))) (rS 0 (by decide)) (by rw [hA]; exact wA 0 (by decide))
  have q₁ : s₁.gpr c.dataReg = A := by rw [g₁ _ hd6 hd7, hA]
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := xorSlot_ok s₁ .x6 .x7 c.dataReg (by decide) hd6 hd7 (by decide)
    (by rw [g₁ _ (by decide) (by decide), hb]) (o := 24) (k := c.buf + 1) (by decide) (buf_imm hL 1 (by decide))
    (by rw [rd₁, wr₁, q₁]; exact inRd (wA 8 (by decide))) (by rw [rd₁, wr₁]; exact rS 1 (by decide))
    (by rw [wr₁, q₁]; exact wA 8 (by decide))
  refine ⟨s₂, ?_, ?_, fun x h1 h2 => by rw [g₂ x h1 h2, g₁ x h1 h2], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [Core.encChain, show ([.ldr .x .x6 c.dataReg 16, ldS .x7 c.buf, eorR .x6 .x6 .x7, .str .x .x6 c.dataReg 16,
        .ldr .x .x6 c.dataReg 24, ldS .x7 (c.buf + 1), eorR .x6 .x6 .x7, .str .x .x6 c.dataReg 24] : List Instr) =
        [.ldr .x .x6 c.dataReg 16, ldS .x7 c.buf, eorR .x6 .x6 .x7, .str .x .x6 c.dataReg 16] ++
        [.ldr .x .x6 c.dataReg 24, ldS .x7 (c.buf + 1), eorR .x6 .x6 .x7, .str .x .x6 c.dataReg 24] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · have a24 : A + BitVec.ofNat 64 24 = A + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 := by rw [addr_add]
    rw [m₂, m₁, q₁, hA, a24, wordAddr_succ]

end VG.Proof.Modes.AArch64
