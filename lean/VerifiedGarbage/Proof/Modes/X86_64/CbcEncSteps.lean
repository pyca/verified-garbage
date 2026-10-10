import VerifiedGarbage.Proof.Modes.X86_64.Block16
import VerifiedGarbage.Impl.Modes.X86_64.CbcEnc

/-!
# The steps of CBC encryption on x86-64

The blocks of code of `cbcEncrypt`, each as `copy16` or `xor16` on memory:
`whiten_ok` (the IV into the first block), `encIn_ok` (a block of the data
to the core's buffer), `encOut_ok` (back), `encChain_ok` (the buffer's block
into the next block of the data).
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st xorS)

variable {c : Core}

theorem wordAddr_succ (B : Addr) (k : Nat) : wordAddr B (k + 1) = wordAddr B k + BitVec.ofNat 64 8 := by
  simp only [wordAddr]; rw [addr_add, Nat.mul_succ]

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

/-- `xor d, [b + o]`. -/
theorem xorMem_ok (s : State) (d b : Reg) (o : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.alu .xor d (.mem (at_ b o))] s = some s' ∧
      s'.gpr d = s.gpr d ^^^ s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64 ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(arithFlags s (s.gpr d ^^^ s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64) false false).setReg d
    (s.gpr d ^^^ s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_arithFlags], rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, State.ea,
    ofInt_nat, hr, ite_true, Option.bind_some]

/-- The IV at `P` (in `r.ctr`) XORed into the block at `D` (in `r.data`). -/
theorem whiten_ok (r : CtrRegs) (hcd : r.ctr ≠ .rax) (hdd : r.data ≠ .rax) (s : State) {P D : Addr}
    (hP : s.gpr r.ctr = P) (hD : s.gpr r.data = D)
    (hrP : ∀ o, o + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 o) 8)
    (hwD : ∀ o, o + 8 ≤ 16 → InRegions s.wr (D + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ r.ctr 0)), .alu .xor .rax (.mem (at_ r.data 0)), .store (at_ r.data 0) .rax,
        .mov .rax (.mem (at_ r.ctr 8)), .alu .xor .rax (.mem (at_ r.data 8)), .store (at_ r.data 8) .rax] s = some s' ∧
      s'.mem = xor16 s.mem D P ∧ (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have rdD : ∀ o, o + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 o) 8 := fun o h => inRd (hwD o h)
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := load_ok s .rax r.ctr 0 (by rw [hP]; exact hrP 0 (by decide))
  obtain ⟨s₂, e₂, d₂, o₂, m₂, rd₂, wr₂⟩ := xorMem_ok s₁ .rax r.data 0
    (by rw [rd₁, wr₁, o₁ _ hdd, hD]; exact rdD 0 (by decide))
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := store_ok s₂ r.data .rax 0
    (by rw [wr₂, wr₁, o₂ _ hdd, o₁ _ hdd, hD]; exact hwD 0 (by decide))
  obtain ⟨s₄, e₄, d₄, o₄, m₄, rd₄, wr₄⟩ := load_ok s₃ .rax r.ctr 8
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, g₃, o₂ _ hcd, o₁ _ hcd, hP]; exact hrP 8 (by decide))
  obtain ⟨s₅, e₅, d₅, o₅, m₅, rd₅, wr₅⟩ := xorMem_ok s₄ .rax r.data 8
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, o₄ _ hdd, g₃, o₂ _ hdd, o₁ _ hdd, hD]; exact rdD 8 (by decide))
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := store_ok s₅ r.data .rax 8
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, o₅ _ hdd, o₄ _ hdd, g₃, o₂ _ hdd, o₁ _ hdd, hD]; exact hwD 8 (by decide))
  have d₄' : s₄.gpr r.data = D := by rw [o₄ _ hdd, g₃, o₂ _ hdd, o₁ _ hdd, hD]
  refine ⟨s₆, ?_, ?_, fun x hx => ?_, by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show ([.mov .rax (.mem (at_ r.ctr 0)), .alu .xor .rax (.mem (at_ r.data 0)), .store (at_ r.data 0) .rax,
        .mov .rax (.mem (at_ r.ctr 8)), .alu .xor .rax (.mem (at_ r.data 8)), .store (at_ r.data 8) .rax] : List Instr) =
        [.mov .rax (.mem (at_ r.ctr 0))] ++ ([.alu .xor .rax (.mem (at_ r.data 0))] ++ ([.store (at_ r.data 0) .rax] ++
        ([.mov .rax (.mem (at_ r.ctr 8))] ++ ([.alu .xor .rax (.mem (at_ r.data 8))] ++
        ([.store (at_ r.data 8) .rax] : List Instr))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · have q₁ : s₁.gpr r.data = D := by rw [o₁ _ hdd, hD]
    have q₂ : s₂.gpr r.data = D := by rw [o₂ _ hdd, q₁]
    have q₃ : s₃.gpr r.ctr = P := by rw [g₃, o₂ _ hcd, o₁ _ hcd, hP]
    have q₅ : s₅.gpr r.data = D := by rw [o₅ _ hdd, d₄']
    simp only [m₆, m₅, m₄, m₃, m₂, m₁, d₅, d₄, d₂, d₁, q₁, q₂, q₃, q₅, d₄', hP, add_zero', xor16, BitVec.xor_comm]
  · rw [g₆, o₅ x hx, o₄ x hx, g₃, o₂ x hx, o₁ x hx]

/-- The block at `A` (in `dataReg`) to the buffer's first block. -/
theorem encIn_ok (hdr : c.dataReg ≠ .rax) (s : State) {B A : Addr} (hb : s.gpr sb = B) (hA : s.gpr c.dataReg = A)
    (rA : ∀ o, o + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 o) 8)
    (wS : ∀ w < 2, InRegions s.wr (wordAddr B (c.buf + w)) 8) :
    ∃ s', runBlock isa c.encIn s = some s' ∧ s'.mem = copy16 s.mem (wordAddr B c.buf) A ∧
      (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := load_ok s .rax c.dataReg 0 (by rw [hA]; exact rA 0 (by decide))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stReg_ok (s := s₁) (b := B) (k := c.buf) .rax (by rw [o₁ _ (by decide), hb])
    (by rw [wr₁]; exact wS 0 (by decide))
  obtain ⟨s₃, e₃, d₃, o₃, m₃, rd₃, wr₃⟩ := load_ok s₂ .rax c.dataReg 8
    (by rw [rd₂, wr₂, rd₁, wr₁, g₂, o₁ _ hdr, hA]; exact rA 8 (by decide))
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (s := s₃) (b := B) (k := c.buf + 1) .rax
    (by rw [o₃ _ (by decide), g₂, o₁ _ (by decide), hb]) (by rw [wr₃, wr₂, wr₁]; exact wS 1 (by decide))
  refine ⟨s₄, ?_, ?_, fun x hx => by rw [g₄, o₃ x hx, g₂, o₁ x hx], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.encIn, show ([.mov .rax (.mem (at_ c.dataReg 0)), st c.buf .rax, .mov .rax (.mem (at_ c.dataReg 8)),
        st (c.buf + 1) .rax] : List Instr) = [.mov .rax (.mem (at_ c.dataReg 0))] ++ ([st c.buf .rax] ++
        ([.mov .rax (.mem (at_ c.dataReg 8))] ++ ([st (c.buf + 1) .rax] : List Instr))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · have q₂ : s₂.gpr c.dataReg = A := by rw [g₂, o₁ _ hdr, hA]
    simp only [m₄, m₃, m₂, m₁, d₃, d₁, q₂, hA, add_zero', wordAddr_succ, copy16]

/-- The buffer's first block back to `A` (in `dataReg`), and one block
fewer left. -/
theorem encOut_ok (hdr : c.dataReg ≠ .rax) (hlr : c.leftReg ≠ .rax) (s : State)
    {B A : Addr} (hb : s.gpr sb = B) (hA : s.gpr c.dataReg = A)
    (rS : ∀ w < 2, InRegions (s.rd ++ s.wr) (wordAddr B (c.buf + w)) 8)
    (wA : ∀ o, o + 8 ≤ 16 → InRegions s.wr (A + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa c.encOut s = some s' ∧ s'.mem = copy16 s.mem A (wordAddr B c.buf) ∧
      s'.gpr c.leftReg = s.gpr c.leftReg - 1 ∧ s'.zf = some (s.gpr c.leftReg - 1 == 0) ∧
      (∀ x, x ≠ .rax → x ≠ c.leftReg → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (s := s) (b := B) (k := c.buf) .rax hb (rS 0 (by decide))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := store_ok s₁ c.dataReg .rax 0
    (by rw [wr₁, o₁ _ hdr, hA]; exact wA 0 (by decide))
  obtain ⟨s₃, e₃, d₃, o₃, m₃, rd₃, wr₃⟩ := movS_ok (s := s₂) (b := B) (k := c.buf + 1) .rax
    (by rw [g₂, o₁ _ (by decide), hb]) (by rw [rd₂, wr₂, rd₁, wr₁]; exact rS 1 (by decide))
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := store_ok s₃ c.dataReg .rax 8
    (by rw [wr₃, wr₂, wr₁, o₃ _ hdr, g₂, o₁ _ hdr, hA]; exact wA 8 (by decide))
  obtain ⟨s₅, e₅, l₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ c.leftReg 1
  have lf : s₄.gpr c.leftReg = s.gpr c.leftReg := by rw [g₄, o₃ _ hlr, g₂, o₁ _ hlr]
  refine ⟨s₅, ?_, ?_, by rw [l₅, lf]; rfl, by rw [z₅, lf]; rfl,
    fun x h1 h2 => by rw [o₅ x h2, g₄, o₃ x h1, g₂, o₁ x h1], by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.encOut, show ([movS .rax c.buf, .store (at_ c.dataReg 0) .rax, movS .rax (c.buf + 1),
        .store (at_ c.dataReg 8) .rax, .alu .sub c.leftReg (.imm 1)] : List Instr) = [movS .rax c.buf] ++
        ([.store (at_ c.dataReg 0) .rax] ++ ([movS .rax (c.buf + 1)] ++ ([.store (at_ c.dataReg 8) .rax] ++
        ([.alu .sub c.leftReg (.imm 1)] : List Instr)))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₅]
  · have q₁ : s₁.gpr c.dataReg = A := by rw [o₁ _ hdr, hA]
    have q₃ : s₃.gpr c.dataReg = A := by rw [o₃ _ hdr, g₂, q₁]
    simp only [m₅, m₄, m₃, m₂, m₁, d₃, d₁, q₁, q₃, add_zero', wordAddr_succ, copy16]

/-- The buffer's first block XORed into the block at `A + 16` (`A` in
`dataReg`). -/
theorem encChain_ok (hdr : c.dataReg ≠ .rax) (s : State) {B A : Addr} (hb : s.gpr sb = B)
    (hA : s.gpr c.dataReg = A) (rS : ∀ w < 2, InRegions (s.rd ++ s.wr) (wordAddr B (c.buf + w)) 8)
    (wA : ∀ o, o + 8 ≤ 16 → InRegions s.wr (A + BitVec.ofNat 64 (16 + o)) 8) :
    ∃ s', runBlock isa c.encChain s = some s' ∧
      s'.mem = xor16 s.mem (A + BitVec.ofNat 64 16) (wordAddr B c.buf) ∧
      (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := load_ok s .rax c.dataReg 16 (by rw [hA]; exact inRd (wA 0 (by decide)))
  obtain ⟨s₂, e₂, d₂, o₂, m₂, rd₂, wr₂⟩ := xorS_ok (s := s₁) (b := B) (k := c.buf) .rax (by rw [o₁ _ (by decide), hb])
    (by rw [rd₁, wr₁]; exact rS 0 (by decide))
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := store_ok s₂ c.dataReg .rax 16
    (by rw [wr₂, wr₁, o₂ _ hdr, o₁ _ hdr, hA]; exact wA 0 (by decide))
  obtain ⟨s₄, e₄, d₄, o₄, m₄, rd₄, wr₄⟩ := load_ok s₃ .rax c.dataReg 24
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, g₃, o₂ _ hdr, o₁ _ hdr, hA]; exact inRd (wA 8 (by decide)))
  obtain ⟨s₅, e₅, d₅, o₅, m₅, rd₅, wr₅⟩ := xorS_ok (s := s₄) (b := B) (k := c.buf + 1) .rax
    (by rw [o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide), hb])
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact rS 1 (by decide))
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := store_ok s₅ c.dataReg .rax 24
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, o₅ _ hdr, o₄ _ hdr, g₃, o₂ _ hdr, o₁ _ hdr, hA]; exact wA 8 (by decide))
  refine ⟨s₆, ?_, ?_, fun x hx => by rw [g₆, o₅ x hx, o₄ x hx, g₃, o₂ x hx, o₁ x hx],
    by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.encChain, show ([.mov .rax (.mem (at_ c.dataReg 16)), xorS .rax c.buf, .store (at_ c.dataReg 16) .rax,
        .mov .rax (.mem (at_ c.dataReg 24)), xorS .rax (c.buf + 1), .store (at_ c.dataReg 24) .rax] : List Instr) =
        [.mov .rax (.mem (at_ c.dataReg 16))] ++ ([xorS .rax c.buf] ++ ([.store (at_ c.dataReg 16) .rax] ++
        ([.mov .rax (.mem (at_ c.dataReg 24))] ++ ([xorS .rax (c.buf + 1)] ++
        ([.store (at_ c.dataReg 24) .rax] : List Instr))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · have q₁ : s₁.gpr c.dataReg = A := by rw [o₁ _ hdr, hA]
    have q₂ : s₂.gpr c.dataReg = A := by rw [o₂ _ hdr, q₁]
    have q₃ : s₃.gpr c.dataReg = A := by rw [g₃, q₂]
    have q₅ : s₅.gpr c.dataReg = A := by rw [o₅ _ hdr, o₄ _ hdr, q₃]
    have a24 : A + BitVec.ofNat 64 24 = A + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 := by rw [addr_add]
    simp only [m₆, m₅, m₄, m₃, m₂, m₁, d₅, d₄, d₂, d₁, q₂, q₃, q₅, hA, a24, wordAddr_succ, xor16]

end VG.Proof.Modes.X86_64
