module
-- separate module: the inverse's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvPacked
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Divstep.Packed
import Mathlib.Data.BitVec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Packed divsteps in a working space within a writable region

`Proof/Weierstrass/X86_64/InvPacked.lean`'s chunks (`pchunk_ok`), whose
proofs these repeat, for a window `rdi` points into anywhere in a writable
region (`CScr`, as `Proof/Bignum/X86_64/Words.lean`'s `Scr` describes the
RSA working space) rather than at the start of one: the run-time-width RSA
inverse (`Impl/Rsa/X86_64/InvBatch.lean`) runs them on a window of its own
arrays. The steps on registers (`pstepsCode_ok`, `pext_ok`, `pfirst_ok`)
are InvPacked's.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Chunk

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open VG.Proof.Divstep (MSt mstep msteps pstep pextLo pextHi ite_t ite_f)

/-- `size` bytes at `base`, a working space within a writable region, with
`rdi` at `base`. -/
structure CScr (s : State) (base : Addr) (size : Nat) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr s base size
  rdi : s.gpr .rdi = base

theorem CScr.nowrap {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) : base.toNat + size ≤ 2 ^ 64 :=
  hs.scr.nowrap

theorem CScr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : CScr s base size) (h : Keeps rs s s') (hr : .rdi ∉ rs) : CScr s' base size :=
  ⟨hs.scr.congr h.2.2.2, (h.1 _ hr).trans hs.rdi⟩

theorem CScr.of_keepRegs {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : CScr s base size) (h : KeepRegs rs s s') (hr : .rdi ∉ rs) : CScr s' base size :=
  ⟨hs.scr.congr h.wr, (h.gpr _ hr).trans hs.rdi⟩

theorem load_scC {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : s.load64 (s.ea (sc d)) = some (word s.mem base d) := by
  rw [ea_sc, hs.rdi, State.load64, ite_eq_left (hs.scr.ld hd)]

theorem store_scC {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (v : BitVec 64) :
    s.store64 (s.ea (sc d)) v = some { s with mem := s.mem.writeW (off base d) v } := by
  rw [ea_sc, hs.rdi, State.store64, ite_eq_left (hs.scr.st hd)]

theorem movMemC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) (r : Reg) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun s' =>
      s'.gpr r = word s.mem base d ∧ s'.cf = s.cf ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, load_scC hs hd, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.cf_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, hq, ite_false]

theorem storeRegC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) (r : Reg) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.store (sc d) r]) s fun s' =>
      s'.mem = s.mem.writeW (off base d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.cf = s.cf ∧
        KeepRegs [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_scC hs hd, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, ⟨fun _ _ => rfl, rfl, rfl⟩⟩

/-- A row's start. -/
theorem psetRowC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {t : Nat} (ht : t + 8 ≤ size)
    (r : Reg) (hr : r ∉ [Reg.rax]) (c : BitVec 64) :
    WP isa (.block (psetRow r t c)) s fun s' =>
      s'.gpr r = (word s.mem base t &&& 0x7fff) + c ∧ Keeps [.rax, r] s s' := by
  have h1 : ¬ r = .rax := fun h => hr (by simp [h])
  have h2 : ¬ Reg.rax = r := fun h => h1 h.symm
  irun [psetRow, load_scC hs ht, sext7fff, h1, h2, RegUpd.gpr_setReg_self]
  refine ⟨fun q hq => ?_, by simp only [RegUpd.mem_setReg, RegUpd.mem_arithFlags], by simp only [RegUpd.rd_setReg, RegUpd.rd_arithFlags], by simp only [RegUpd.wr_setReg, RegUpd.wr_arithFlags]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2, ↓reduceIte]

/-- The rows' start. -/
theorem psetC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {t : Nat} (ht : t + 16 ≤ size) :
    WP isa (.block (pset t)) s fun s' =>
      s'.gpr .r8 = (word s.mem base t &&& 0x7fff) + 2 ^ 31 ∧
      s'.gpr .r13 = (word s.mem base (t + 8) &&& 0x7fff) + 2 ^ 47 ∧ Keeps [.rax, .r8, .r13] s s' := by
  rw [pset, WP.block_append_iff]
  refine WP.mono (psetRowC_ok hs (t := t) (by omega_arith) .r8 (by decide) _) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (psetRowC_ok (hs.of_keeps k₁ (by decide)) (t := t + 8) (by omega_arith) .r13 (by decide) _)
    fun s₂ ⟨e₂, k₂⟩ => ⟨?_, by rw [e₂, k₁.2.1], (k₁.mono (by decide)).trans (k₂.mono (by decide))⟩
  rw [k₂.1 _ (by decide), e₁]


/-- `rax = [d] r`. -/
theorem ldMulC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {d : Nat} (hd : d + 8 ≤ size)
    (r : Reg) (hr : r ∉ [Reg.rax, .rdx]) :
    WP isa (.block (ldMul d r)) s fun s' => s'.gpr .rax = word s.mem base d * s.gpr r ∧ Keeps [.rax, .rdx] s s' := by
  have h1 : ¬ r = .rax := fun h => hr (by simp [h])
  irun [ldMul, load_scC hs hd, mul_lo, h1]
  refine ⟨fun q hq => ?_, by simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags], by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags], by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq.1, hq.2, ↓reduceIte]

/-- `[e] = (rax + [d]) >> n`. -/
theorem addShrStC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {d n e : Nat}
    (hd : d + 8 ≤ size) (he : e + 8 ≤ size) (hn : 1 ≤ n ∧ n ≤ 63) :
    WP isa (.block (addShrSt d n e)) s fun s' =>
      s'.mem = s.mem.writeW (off base e) ((s.gpr .rax + word s.mem base d) >>> n) ∧ KeepRegs [.rax] s s' := by
  rw [addShrSt, WP.block_append_iff]
  have h : WP isa (.block [.alu .add .rax (.mem (sc d)), .shift .shr .rax n]) s fun s₁ =>
      s₁.gpr .rax = (s.gpr .rax + word s.mem base d) >>> n ∧ Keeps [.rax] s s₁ := by
    irun [load_scC hs hd, hn]
    refine ⟨fun q hq => ?_, by simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags], by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags], by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hq, ↓reduceIte]
  refine WP.mono h fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (storeRegC_ok (hs.of_keeps k₁ (by decide)) .rax he) fun s₂ ⟨m₂, _, _, k₂⟩ =>
    ⟨by rw [m₂, e₁, k₁.2.1], (Keeps.regs k₁).trans (k₂.mono (by regions_sub))⟩

/-- A chunk's update of the low words at `[t]`, `[t + 8]`. -/
theorem plowC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {n t : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (ht : t + 24 ≤ size) :
    WP isa (.block (plow n t)) s fun s' =>
      word s'.mem base t = (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n ∧
      word s'.mem base (t + 8) =
        (word s.mem base (t + 8) * s.gpr .rbp + word s.mem base t * s.gpr .r13) >>> n ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside base t 24 s.mem s'.mem := by
  have hN := hs.nowrap
  simp only [plow, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldMulC_ok hs (d := t) (by omega_arith) .r8 (by decide)) fun s₁ ⟨a₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeRegC_ok hs₁ .rax (d := t + 16) (by omega_arith)) fun s₂ ⟨m₂, g₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldMulC_ok hs₂ (d := t + 8) (by omega_arith) .rcx (by decide)) fun s₃ ⟨a₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addShrStC_ok hs₃ (d := t + 16) (e := t + 16) (by omega_arith) (by omega_arith) hn) fun s₄ ⟨m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldMulC_ok hs₄ (d := t) (by omega_arith) .r13 (by decide)) fun s₅ ⟨a₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeRegC_ok hs₅ .rax (d := t) (by omega_arith)) fun s₆ ⟨m₆, g₆, _, k₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldMulC_ok hs₆ (d := t + 8) (by omega_arith) .rbp (by decide)) fun s₇ ⟨a₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addShrStC_ok hs₇ (d := t) (e := t + 8) (by omega_arith) (by omega_arith) hn) fun s₈ ⟨m₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_keepRegs k₈ (by decide)
  rw [show [Instr.mov .rax (.mem (sc (t + 16))), .store (sc t) .rax] =
    [Instr.mov .rax (.mem (sc (t + 16)))] ++ [.store (sc t) .rax] from rfl, WP.block_append_iff]
  refine WP.mono (movMemC_ok hs₈ .rax (d := t + 16) (by omega_arith)) fun s₉ ⟨a₉, _, k₉⟩ => ?_
  refine WP.mono (storeRegC_ok (hs₈.of_keeps k₉ (by decide)) .rax (d := t) (by omega_arith)) fun u ⟨mu, _, _, ku⟩ => ?_
  have R2 : ∀ r ∉ [Reg.rax, .rdx], s₂.gpr r = s.gpr r := fun r hr => by rw [g₂, k₁.1 r hr]
  have R4 : ∀ r ∉ [Reg.rax, .rdx], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; simp [h])), k₃.1 r hr, R2 r hr]
  have R6 : ∀ r ∉ [Reg.rax, .rdx], s₆.gpr r = s.gpr r := fun r hr => by rw [g₆, k₅.1 r hr, R4 r hr]
  have ap : ∀ (m : Mem) (d e : Nat) (v : BitVec 64), d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ size → e + 8 ≤ size →
      word (m.writeW (off base e) v) base d = word m base d := fun m d e v h hd he =>
    word_apart m base v h (by omega_arith) (by omega_arith)
  have ou : ∀ (m : Mem) (e : Nat) (v : BitVec 64), t ≤ e → e + 8 ≤ t + 24 →
      Outside base t 24 m (m.writeW (off base e) v) := fun m e v h1 h2 =>
    (writeW_outside m base v (by omega_arith)).mono h1 h2
  -- The words after each store.
  have w2_0 : word s₂.mem base t = word s.mem base t := by rw [m₂, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₁.2.1]
  have w2_8 : word s₂.mem base (t + 8) = word s.mem base (t + 8) := by
    rw [m₂, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₁.2.1]
  have w2_16 : word s₂.mem base (t + 16) = word s.mem base t * s.gpr .r8 := by rw [m₂, word_writeW_self, a₁]
  have hF : (s₃.gpr .rax + word s₃.mem base (t + 16)) >>> n =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [a₃, k₃.2.1, w2_8, w2_16, R2 .rcx (by decide)]
  have w4_0 : word s₄.mem base t = word s.mem base t := by
    rw [m₄, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₃.2.1, w2_0]
  have w4_8 : word s₄.mem base (t + 8) = word s.mem base (t + 8) := by
    rw [m₄, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₃.2.1, w2_8]
  have w4_16 : word s₄.mem base (t + 16) =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [m₄, word_writeW_self, hF]
  have w6_0 : word s₆.mem base t = word s.mem base t * s.gpr .r13 := by
    rw [m₆, word_writeW_self, a₅, w4_0, R4 .r13 (by decide)]
  have w6_8 : word s₆.mem base (t + 8) = word s.mem base (t + 8) := by
    rw [m₆, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₅.2.1, w4_8]
  have w6_16 : word s₆.mem base (t + 16) =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [m₆, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₅.2.1, w4_16]
  have hG : (s₇.gpr .rax + word s₇.mem base t) >>> n =
      (word s.mem base (t + 8) * s.gpr .rbp + word s.mem base t * s.gpr .r13) >>> n := by
    rw [a₇, k₇.2.1, w6_8, w6_0, R6 .rbp (by decide)]
  have w8_8 : word s₈.mem base (t + 8) =
      (word s.mem base (t + 8) * s.gpr .rbp + word s.mem base t * s.gpr .r13) >>> n := by
    rw [m₈, word_writeW_self, hG]
  have w8_16 : word s₈.mem base (t + 16) =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [m₈, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₇.2.1, w6_16]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mu, word_writeW_self, a₉, w8_16]
  · rw [mu, ap _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), k₉.2.1, w8_8]
  · exact ((((((((((Keeps.regs k₁).trans (k₂.mono (by regions_sub))).trans (Keeps.regs k₃)).trans
      (k₄.mono (by regions_sub))).trans (Keeps.regs k₅)).trans (k₆.mono (by regions_sub))).trans (Keeps.regs k₇)).trans
      (k₈.mono (by regions_sub))).trans ((Keeps.regs k₉).mono (by regions_sub))).trans (ku.mono (by regions_sub)))
  · rw [mu, k₉.2.1, m₈, k₇.2.1, m₆, k₅.2.1, m₄, k₃.2.1, m₂, k₁.2.1]
    exact (((((ou _ (t + 16) _ (by omega_arith) (by omega_arith)).trans (ou _ (t + 16) _ (by omega_arith) (by omega_arith))).trans
      (ou _ t _ (by omega_arith) (by omega_arith))).trans (ou _ (t + 8) _ (by omega_arith) (by omega_arith))).trans
      (ou _ t _ (by omega_arith) (by omega_arith)))



/-- A column of the batch's matrix times the chunk's. -/
theorem pcolC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {t : Nat} (ht : t + 8 ≤ size)
    {x y : Reg} (hx : x = .r9 ∧ y = .r11 ∨ x = .r10 ∧ y = .r12) :
    WP isa (.block (pcol x y t)) s fun s' =>
      s'.gpr x = s.gpr .r8 * s.gpr x + s.gpr .rcx * s.gpr y ∧
      s'.gpr y = s.gpr .rbp * s.gpr y + s.gpr .r13 * s.gpr x ∧
      KeepRegs [.rax, .rdx, x, y] s s' ∧ Outside base t 8 s.mem s'.mem := by
  have hN := hs.nowrap
  have F : ∀ r ∈ [Reg.rax, .rdx, .r8, .rcx, .rbp, .r13, .rdi], (¬ r = x ∧ ¬ x = r) ∧ (¬ r = y ∧ ¬ y = r) := by
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hxy : ¬ x = y ∧ ¬ y = x := by rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := F .rax (by simp)
  obtain ⟨⟨d1, d2⟩, d3, d4⟩ := F .rdx (by simp)
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := F .r8 (by simp)
  obtain ⟨⟨c1, c2⟩, c3, c4⟩ := F .rcx (by simp)
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := F .rbp (by simp)
  obtain ⟨⟨f1, f2⟩, f3, f4⟩ := F .r13 (by simp)
  obtain ⟨⟨i1, i2⟩, i3, i4⟩ := F .rdi (by simp)
  rw [pcol, WP.block_append_iff, WP.block_append_iff,
    show [Instr.mov .rax (.reg .r13), .mul x, .store (sc t) .rax] =
      [Instr.mov .rax (.reg .r13), .mul x] ++ [.store (sc t) .rax] from rfl, WP.block_append_iff]
  have h0 : WP isa (.block [.mov .rax (.reg .r13), .mul x]) s fun s₁ =>
      s₁.gpr .rax = s.gpr .r13 * s.gpr x ∧ Keeps [.rax, .rdx] s s₁ := by
    irun [mul_lo, a1, a2]
    refine ⟨fun r hr => ?_, by simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags], by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags], by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ↓reduceIte]
  refine WP.mono h0 fun s₁ ⟨a₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (storeRegC_ok hs₁ .rax (d := t) ht) fun s₂ ⟨m₂, g₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have h1 : WP isa (.block [.mov .rax (.reg .r8), .mul x, .mov x (.reg .rax), .mov .rax (.reg .rcx), .mul y,
      .alu .add x (.reg .rax), .mov .rax (.reg .rbp), .mul y]) s₂ fun s₃ =>
      s₃.gpr x = s₂.gpr .r8 * s₂.gpr x + s₂.gpr .rcx * s₂.gpr y ∧ s₃.gpr .rax = s₂.gpr .rbp * s₂.gpr y ∧
        Keeps [.rax, .rdx, x] s₂ s₃ := by
    irun [mul_lo, a1, a2, a3, a4, d1, d2, d3, d4, e1, e2, c1, c2, b1, b2, b3, b4, hxy.1, hxy.2,
      RegUpd.gpr_setReg_self]
    refine ⟨fun r hr => ?_, by simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags], by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags], by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ↓reduceIte]
  refine WP.mono h1 fun s₃ ⟨x₃, a₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by simp [i1])
  have R : ∀ r, r ∉ [Reg.rax, .rdx] → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂, k₁.1 r hr]
  have y3 : s₃.gpr y = s.gpr y := by rw [k₃.1 y (by simp [a4, d4, hxy.2]), R y (by simp [a4, d4])]
  have t3 : word s₃.mem base t = s.gpr .r13 * s.gpr x := by rw [k₃.2.1, m₂, word_writeW_self, a₁]
  have xx : s₃.gpr x = s.gpr .r8 * s.gpr x + s.gpr .rcx * s.gpr y := by
    rw [x₃, R .r8 (by decide), R x (by simp [a2, d2]), R .rcx (by decide), R y (by simp [a4, d4])]
  have ra : s₃.gpr .rax = s.gpr .rbp * s.gpr y := by rw [a₃, R .rbp (by decide), R y (by simp [a4, d4])]
  irun [load_scC hs₃ ht, a1, a2, a3, a4, hxy.1, hxy.2, RegUpd.gpr_setReg_self, t3, xx, ra]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne (h := hr.2.2.2), RegUpd.gpr_setReg_of_ne (h := hr.1), RegUpd.gpr_arithFlags,
      k₃.1 r (by simp [hr.1, hr.2.1, hr.2.2.1]), R r (by simp [hr.1, hr.2.1])]
  · exact k₃.2.2.1.trans (k₂.rd.trans k₁.2.2.1)
  · exact k₃.2.2.2.trans (k₂.wr.trans k₁.2.2.2)
  · rw [k₃.2.1, m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega_arith)

/-- The batch's matrix times the chunk's. -/
theorem pcompC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {t : Nat} (ht : t + 8 ≤ size) :
    WP isa (.block (pcomp t)) s fun s' =>
      s'.gpr .r9 = s.gpr .r8 * s.gpr .r9 + s.gpr .rcx * s.gpr .r11 ∧
      s'.gpr .r11 = s.gpr .rbp * s.gpr .r11 + s.gpr .r13 * s.gpr .r9 ∧
      s'.gpr .r10 = s.gpr .r8 * s.gpr .r10 + s.gpr .rcx * s.gpr .r12 ∧
      s'.gpr .r12 = s.gpr .rbp * s.gpr .r12 + s.gpr .r13 * s.gpr .r10 ∧
      KeepRegs [.rax, .rdx, .r9, .r10, .r11, .r12] s s' ∧ Outside base t 8 s.mem s'.mem := by
  rw [pcomp, WP.block_append_iff]
  refine WP.mono (pcolC_ok hs ht (Or.inl ⟨rfl, rfl⟩)) fun s₁ ⟨x₁, y₁, k₁, o₁⟩ => ?_
  refine WP.mono (pcolC_ok (hs.of_keepRegs k₁ (by decide)) ht (Or.inr ⟨rfl, rfl⟩)) fun s₂ ⟨x₂, y₂, k₂, o₂⟩ => ?_
  have g : ∀ r ∈ [Reg.r8, .rcx, .rbp, .r13, .r10, .r12], s₁.gpr r = s.gpr r := fun r hr => k₁.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
  have g' : ∀ r ∈ [Reg.r9, .r11], s₂.gpr r = s₁.gpr r := fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> subst h <;> decide)
  refine ⟨?_, ?_, ?_, ?_, (k₁.mono (by regions_sub)).trans (k₂.mono (by regions_sub)), o₁.trans o₂⟩
  · rw [g' .r9 (by simp), x₁]
  · rw [g' .r11 (by simp), y₁]
  · rw [x₂, g .r8 (by simp), g .r10 (by simp), g .rcx (by simp), g .r12 (by simp)]
  · rw [y₂, g .rbp (by simp), g .r12 (by simp), g .r13 (by simp), g .r10 (by simp)]

/-! ## A chunk -/

/-- A chunk of `n` steps from the batch's state `T` so far: `T`'s `n` steps. -/
theorem pchunkC_ok {s : State} {base : Addr} {size : Nat} (hs : CScr s base size) {t n K : Nat}
    {first last : Bool} (hn : 1 ≤ n ∧ n ≤ 15) (hK : n ≤ K ∧ K ≤ 64) (ht : t + 24 ≤ size) {T : MSt}
    (hf : T.f % 2 = 1) (hd : |T.d| + 2 * n < 2 ^ 62) (hI : ChunkAt base t K first T s) :
    WP isa (.block (pchunk t n first last)) s fun s' =>
      s'.gpr .rbx = ~~~BitVec.ofInt 64 (msteps n T).d ∧
      s'.gpr .r9 = BitVec.ofInt 64 (msteps n T).u ∧ s'.gpr .r10 = BitVec.ofInt 64 (msteps n T).v ∧
      s'.gpr .r11 = BitVec.ofInt 64 (msteps n T).q ∧ s'.gpr .r12 = BitVec.ofInt 64 (msteps n T).r ∧
      (last = false → ((word s'.mem base t).toNat : Int) % 2 ^ (K - n) = (msteps n T).f % 2 ^ (K - n) ∧
        ((word s'.mem base (t + 8)).toNat : Int) % 2 ^ (K - n) = (msteps n T).g % 2 ^ (K - n)) ∧
      KeepRegs chunkRegs s s' ∧ Outside base t 24 s.mem s'.mem := by
  have hN := hs.nowrap
  have hmat := Divstep.msteps_mat (d := T.d) (g := T.g) hf n
  have bnd := Divstep.msteps_bnd T.d T.f T.g n
  have lo := Divstep.msteps_lo T.d T.f T.g n
  have hrel := Divstep.psteps_rel (d := T.d) (f := T.f) (g := T.g)
    (P := (((word s.mem base t).toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 31)
    (Q := (((word s.mem base (t + 8)).toNat % 2 ^ 15 : Nat) : Int) + 2 ^ 47) (n := n) (by omega_arith) hf hd
    (prow_mod hn.2 hK.1 (by norm_num) hI.f) (prow_mod hn.2 hK.1 (by norm_num) hI.g) n le_rfl
  rw [Divstep.msteps_gen n T]
  simp only
  set m := msteps n (MSt.init T.d T.f T.g) with hm
  simp only [pchunk, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (psetC_ok hs (t := t) (by omega_arith)) fun s₁ ⟨r8₁, r13₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pstepsCode_ok s₁ hn.2) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [r8₁, r13₁, pset_int _ _ c31, pset_int _ _ c47, k₁.1 _ (by decide), hI.d, hrel] at e₂
  simp only [Prod.mk.injEq] at e₂
  obtain ⟨d₂, f₂, g₂⟩ := e₂
  rw [WP.block_append_iff]
  refine WP.mono (pext_ok s₂) fun s₃ ⟨u₃, v₃, q₃, r₃, k₃⟩ => ?_
  have p15 : (2 : Int) ^ n ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) hn.2
  have ha : (word s.mem base t).toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  have hb : (word s.mem base (t + 8)).toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by norm_num)
  obtain ⟨eu, ev⟩ := Divstep.pext_rel ha hb (u := m.u) (v := m.v) (by linarith [lo.1]) (by linarith [lo.2.1])
    (by linarith [bnd.1])
  obtain ⟨eq, er⟩ := Divstep.pext_rel ha hb (u := m.q) (v := m.r) (by linarith [lo.2.2.1])
    (by linarith [lo.2.2.2.1]) (by linarith [bnd.2])
  rw [f₂, eu] at u₃
  rw [f₂, ev] at v₃
  rw [g₂, eq] at q₃
  rw [g₂, er] at r₃
  have hs₃ : CScr s₃ base size := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have mem₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  have keep₃ : ∀ r ∈ [Reg.r9, .r10, .r11, .r12], s₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k₃.1 r (by rcases hr with h | h | h | h <;> subst h <;> decide),
      k₂.1 r (by rcases hr with h | h | h | h <;> subst h <;> decide),
      k₁.1 r (by rcases hr with h | h | h | h <;> subst h <;> decide)]
  have rbx₃ : s₃.gpr .rbx = ~~~BitVec.ofInt 64 m.d := by rw [k₃.1 _ (by decide), d₂]
  rw [WP.block_append_iff]
  have hlow : WP isa (.block (if last = true then [] else plow n t)) s₃ fun s₄ =>
      (∀ r ∈ [Reg.rbx, .r8, .rcx, .r13, .rbp, .r9, .r10, .r11, .r12], s₄.gpr r = s₃.gpr r) ∧
      (last = false → ((word s₄.mem base t).toNat : Int) % 2 ^ (K - n) = m.f % 2 ^ (K - n) ∧
        ((word s₄.mem base (t + 8)).toNat : Int) % 2 ^ (K - n) = m.g % 2 ^ (K - n)) ∧
      KeepRegs [.rax, .rdx] s₃ s₄ ∧ Outside base t 24 s₃.mem s₄.mem := by
    cases last
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have kr : ∀ r ∈ [Reg.rbx, .r8, .rcx, .r13, .rbp, .r9, .r10, .r11, .r12], r ∉ [Reg.rax, .rdx] := by decide
      refine WP.mono (plowC_ok hs₃ ⟨hn.1, by omega_arith⟩ ht) fun s₄ ⟨w0, w1, k₄, o₄⟩ =>
        ⟨fun r hr => k₄.gpr r (kr r hr), fun _ => ⟨?_, ?_⟩, k₄, o₄⟩
      · rw [w0, mem₃, u₃, v₃, add_comm]
        exact Divstep.low_upd hK.2 hK.1 hI.f hI.g hmat.1
      · rw [w1, mem₃, q₃, r₃, add_comm]
        exact Divstep.low_upd hK.2 hK.1 hI.f hI.g hmat.2
    · simp only [↓reduceIte]
      exact WP.block_nil_iff.mpr ⟨fun _ _ => rfl, fun h => absurd h (by decide), ⟨fun _ _ => rfl, rfl, rfl⟩,
        Outside.refl _ _ _ _⟩
  refine WP.mono hlow fun s₄ ⟨R₄, w₄, k₄, o₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have k34 : KeepRegs chunkRegs s s₄ := ((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono
    (by decide))).trans ((Keeps.regs k₃).mono (by decide))).trans (k₄.mono (by decide))
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨m9, m10, m11, m12⟩ := hI.mat rfl
    refine WP.mono (pcompC_ok hs₄ (t := t + 16) (by omega_arith)) fun s₅ ⟨x9, x11, x10, x12, k₅, o₅⟩ =>
      ⟨?_, ?_, ?_, ?_, ?_, fun h => ?_, k34.trans (k₅.mono (by decide)), ?_⟩
    · rw [k₅.gpr _ (by decide), R₄ _ (by simp), rbx₃]
    · rw [x9, R₄ .r8 (by simp), R₄ .rcx (by simp), R₄ .r9 (by simp), R₄ .r11 (by simp), u₃, v₃,
        keep₃ .r9 (by simp), keep₃ .r11 (by simp), m9, m11, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
        ← BitVec.ofInt_add]
    · rw [x10, R₄ .r8 (by simp), R₄ .rcx (by simp), R₄ .r10 (by simp), R₄ .r12 (by simp), u₃, v₃,
        keep₃ .r10 (by simp), keep₃ .r12 (by simp), m10, m12, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
        ← BitVec.ofInt_add]
    · rw [x11, R₄ .rbp (by simp), R₄ .r13 (by simp), R₄ .r9 (by simp), R₄ .r11 (by simp), q₃, r₃,
        keep₃ .r9 (by simp), keep₃ .r11 (by simp), m9, m11, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
        ← BitVec.ofInt_add, add_comm]
    · rw [x12, R₄ .rbp (by simp), R₄ .r13 (by simp), R₄ .r10 (by simp), R₄ .r12 (by simp), q₃, r₃,
        keep₃ .r10 (by simp), keep₃ .r12 (by simp), m10, m12, ← BitVec.ofInt_mul, ← BitVec.ofInt_mul,
        ← BitVec.ofInt_add, add_comm]
    · rw [o₅.word (d := t) (by omega_arith) (by omega_arith), o₅.word (d := t + 8) (by omega_arith) (by omega_arith)]; exact w₄ h
    · rw [← mem₃]; exact o₄.trans (o₅.mono (by omega_arith) (by omega_arith))
  · simp only [↓reduceIte]
    obtain ⟨i1, i2, i3, i4⟩ := hI.id rfl
    refine WP.mono (pfirst_ok s₄) fun s₅ ⟨x9, x10, x11, x12, k₅⟩ =>
      ⟨?_, ?_, ?_, ?_, ?_, fun h => by rw [k₅.2.1]; exact w₄ h, k34.trans ((Keeps.regs k₅).mono (by decide)), ?_⟩
    · rw [k₅.1 _ (by decide), R₄ _ (by simp), rbx₃]
    · rw [x9, R₄ .r8 (by simp), u₃, i1, i3]; congr 1; ring
    · rw [x10, R₄ .rcx (by simp), v₃, i2, i4]; congr 1; ring
    · rw [x11, R₄ .r13 (by simp), q₃, i1, i3]; congr 1; ring
    · rw [x12, R₄ .rbp (by simp), r₃, i2, i4]; congr 1; ring
    · rw [k₅.2.1, ← mem₃]; exact o₄


end VG.Proof.Rsa.X86_64.Chunk
