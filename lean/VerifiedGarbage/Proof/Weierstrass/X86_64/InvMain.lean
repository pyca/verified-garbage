import VerifiedGarbage.Proof.Weierstrass.X86_64.InvBatch
import VerifiedGarbage.Proof.Weierstrass.InvArith

/-!
# Inversion by divsteps on x86-64: the whole inversion

`InvCfg.inv P` leaves `[acc]` reading (in Montgomery form) as `[base]^(m - 2)`
for a prime `m` (`invPow_ok`, as `pow_ok` for the exponent `m - 2`): the
start holds `(d, f, g, a, b) = (1, m, x, 0, 1)` (`init_ok`), each of the `B`
batches takes it to the next `Divstep.invRun` (`batch_ok`), and the end
multiplies `a` by `C` or `m - C` by the sign of `f = ±1` (`finish_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers the inversion writes, within a power's. -/
theorem invClob_sub {n : Nat} (h4 : 4 ≤ n) (h7 : n < 7) : ∀ r ∈ batchRegs, r ∈ powClob n := by
  obtain rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 := by omega
  all_goals decide

/-- `[dst] = [src]` (`n` words) with a zero word on top. -/
theorem copyTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src n : Nat}
    (hsrc : src + 8 * n ≤ size) (hdst : dst + 8 * (n + 1) ≤ size) (hsep : dst + 8 * (n + 1) ≤ src ∨ src + 8 * n ≤ dst) :
    WP isa (.block (copy n dst src ++ zeroTop dst n)) s fun t =>
      wordsVal t.mem base dst (n + 1) = wordsVal s.mem base src n ∧ KeepRegs [.rax, .r8] s t ∧
      Outside base dst (8 * (n + 1)) s.mem t.mem := by
  have hn := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok n hs (o := dst) (a := src) (by omega) hsrc (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  refine WP.mono (zeroTop_ok (hs.of_keepRegs k₁ (by decide)) (U := dst) (n := n) (by omega)) fun t ⟨z, kt, Ot⟩ =>
    ⟨?_, (k₁.mono (by decide)).trans (kt.mono (by decide)), fun x hx => by rw [Ot x (by omega), O₁ x (by omega)]⟩
  rw [wordsVal_succ_top, Ot.wordsVal (by omega) (by omega), z, e₁]
  simp

theorem sext1' : (1 : BitVec 32).setWidth 64 = BitVec.ofInt 64 1 := by decide

/-- `rbx = 1`, `rax = B`. -/
theorem initRegs_ok (s : State) {B : Nat} (hB : B < 2 ^ 16) :
    WP isa (.block [.mov32 .rbx (.imm 1), .mov32 .rax (.imm (BitVec.ofNat 32 B))]) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 1 ∧ t.gpr .rax = BitVec.ofNat 64 B ∧ Keeps [.rbx, .rax] s t := by
  irun [sext1']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

set_option hygiene false in
/-- The slots' arithmetic, from `slots` and the layout (named `eL` … `eC`, `n4`, `htbl`, `hn`). -/
local macro "slot_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, eC, n4, htbl, hn])

set_option hygiene false in
/-- `slot_omega` with the modulus's place (`hmt`, `hmo`). -/
local macro "slotm_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, eC, n4, htbl, hn, hmt, hmo])

set_option hygiene false in
/-- `slot_omega` with a hypothesis `hx` about an address. -/
local macro "slotx_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, eC, n4, htbl, hn, hx])

theorem zext1' : (1 : BitVec 32).setWidth 64 = 1 := by decide

/-- `[d] = 1`, through `r8`. -/
theorem setOne_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block [.mov32 .r8 (.imm 1), .store (sc d) .r8]) s fun t =>
      t.mem = s.mem.writeW (off base d) (1 : BitVec 64) ∧ KeepRegs [.r8] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  have h : WP isa (.block [.mov32 .r8 (.imm 1)]) s fun v => v.gpr .r8 = 1 ∧ Keeps [.r8] s v := by
    irun [zext1']
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h fun s₁ ⟨g₁, k₁⟩ => ?_
  refine WP.mono (storeReg_ok (hs.of_keeps k₁ (by decide)) .r8 hd) fun t ⟨mt, _, _, kt⟩ =>
    ⟨by rw [mt, g₁, k₁.2.1], (Keeps.regs k₁).trans (kt.mono (by decide))⟩

/-- The start's first part: `d = 1`, the count, `f = m`, `g = x`. -/
abbrev init₁ (P : InvCfg) : List Instr :=
  [.mov32 .rbx (.imm 1), .mov32 .rax (.imm (BitVec.ofNat 32 P.B)), .store (sc P.sCnt) .rax] ++
  (copy P.M.n P.sF P.M.mo ++ zeroTop P.sF P.M.n) ++ (copy P.M.n P.sG P.base ++ zeroTop P.sG P.M.n)

/-- The start's second part: `a = 0`, `b = 1`. -/
abbrev init₂ (P : InvCfg) : List Instr :=
  zeroWords P.M.n P.sA ++ zeroWords P.M.n P.sB ++ [.mov32 .r8 (.imm 1), .store (sc P.sB) .r8]

theorem init_eq (P : InvCfg) : P.init = init₁ P ++ init₂ P := by
  simp only [InvCfg.init, init₁, init₂, List.append_assoc, List.cons_append, List.nil_append]

theorem init₁_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOk P.M size m s.mem base) (hB : P.B < 2 ^ 16) :
    WP isa (.block (init₁ P)) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 1 ∧ word t.mem base P.sCnt = BitVec.ofNat 64 P.B ∧
      wordsVal t.mem base P.sF P.L = m ∧ wordsVal t.mem base P.sG P.L = wordsVal s.mem base P.base P.M.n ∧
      KeepRegs [.rax, .rbx, .r8] s t ∧ Unch base [(P.sF, 16 * P.M.n + 16), (P.sCnt, 8)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU, eC⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl; have hmt := hL.mo_tbl; unfold invTbl at hmt
  have hmo := hM.mo; have hbase := hL.base; have hbt := hL.base_tbl; unfold invTbl at hbt
  rw [init₁, show ([.mov32 .rbx (.imm 1), .mov32 .rax (.imm (BitVec.ofNat 32 P.B)), .store (sc P.sCnt) .rax] :
      List Instr) = [.mov32 .rbx (.imm 1), .mov32 .rax (.imm (BitVec.ofNat 32 P.B))] ++
      [.store (sc P.sCnt) .rax] from rfl, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (initRegs_ok s hB) fun s₁ ⟨b₁, a₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeReg_ok hs₁ .rax (d := P.sCnt) (by slot_omega)) fun s₂ ⟨m₂, g₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have O₂ : Outside base P.sCnt 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (copyTop_ok hs₂ (dst := P.sF) (src := P.M.mo) (n := P.M.n) hmo (by slot_omega) (by slotm_omega))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have hbs : P.base + 8 * P.M.n ≤ P.sF ∨ P.sG + 8 * (P.M.n + 1) ≤ P.base := by
    omega_using [eF, eG, n4, hbt]
  refine WP.mono (copyTop_ok hs₃ (dst := P.sG) (src := P.base) (n := P.M.n) hbase (by slot_omega)
    (by omega_using [eF, eG, n4, hbs])) fun t ⟨e₄, k₄, O₄⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), b₁]
  · rw [O₄.word (by slot_omega) (by slot_omega), O₃.word (by slot_omega) (by slot_omega), m₂, word_writeW_self,
      a₁]
  · rw [eL, O₄.wordsVal (by slot_omega) (by slot_omega), e₃, O₂.wordsVal (by slotm_omega) (by slotm_omega), k₁.2.1,
      hM.val]
  · rw [eL, e₄, O₃.wordsVal (by omega_using [eF, eG, hbs]) (by omega_using [hbase, hn]),
      O₂.wordsVal (by omega_using [eC, hbt, n4]) (by omega_using [hbase, hn]), k₁.2.1]
  · exact ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
      (k₄.mono (by decide))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [O₄ x (by slotx_omega), O₃ x (by slotx_omega), O₂ x (by slotx_omega), k₁.2.1]

theorem init₂_ok {P : InvCfg} {base : Addr} {size : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size) :
    WP isa (.block (init₂ P)) s fun t =>
      wordsVal t.mem base P.sA P.M.n = 0 ∧ wordsVal t.mem base P.sB P.M.n = 1 ∧
      KeepRegs [.r8] s t ∧ Outside base P.sA (16 * P.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU, eC⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [init₂, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroWords_ok hs (k := P.M.n) (t := P.sA) (by slot_omega)) fun s₅ ⟨z₅, k₅, O₅⟩ => ?_
  have hs₅ := hs.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroWords_ok hs₅ (k := P.M.n) (t := P.sB) (by slot_omega)) fun s₆ ⟨z₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  refine WP.mono (setOne_ok hs₆ (d := P.sB) (by slot_omega)) fun t ⟨mt, kt⟩ => ?_
  have Ot : Outside base P.sB 8 s₆.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by omega)
  refine ⟨?_, ?_, (k₅.trans k₆).trans kt, fun x hx => by
    rw [Ot x (by slotx_omega), O₆ x (by slotx_omega), O₅ x (by slotx_omega)]⟩
  · rw [Ot.wordsVal (by slot_omega) (by slot_omega), O₆.wordsVal (by slot_omega) (by slot_omega), z₅]
  · obtain ⟨k, hk⟩ : ∃ k, P.M.n = k + 1 := ⟨P.M.n - 1, by omega⟩
    have z₆' := z₆
    rw [hk, wordsVal] at z₆'
    have h0 : wordsVal s₆.mem base (P.sB + 8) k = 0 := by
      rcases Nat.eq_zero_or_pos (wordsVal s₆.mem base (P.sB + 8) k) with h | h
      · exact h
      · have := Nat.mul_le_mul_left (2 ^ 64) h; omega
    rw [hk, wordsVal, mt, word_writeW_self, (writeW_outside s₆.mem base (d := P.sB) 1 (by omega)).wordsVal
      (by omega) (by omega), h0]
    rfl

/-- The start: `d = 1`, the count, and `(f, g, a, b) = (m, x, 0, 1)`. -/
theorem init_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOk P.M size m s.mem base) (hB : P.B < 2 ^ 16) :
    WP isa (.block P.init) s fun t =>
      IInv P base ⟨1, m, wordsVal s.mem base P.base P.M.n, 0, 1⟩ t ∧
      word t.mem base P.sCnt = BitVec.ofNat 64 P.B ∧
      KeepRegs [.rax, .rbx, .r8] s t ∧ Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU, eC⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [init_eq, WP.block_append_iff]
  refine WP.mono (init₁_ok hL hs hM hB) fun s₁ ⟨b₁, c₁, f₁, g₁, k₁, U₁⟩ => ?_
  refine WP.mono (init₂_ok hL (hs.of_keepRegs k₁ (by decide))) fun t ⟨a₂, b₂, k₂, O₂⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, k₁.trans (k₂.mono (by decide)), ?_⟩
  · rw [k₂.gpr _ (by decide), b₁]
  · rw [O₂.wordsVal (by slot_omega) (by slot_omega), f₁]
  · rw [O₂.wordsVal (by slot_omega) (by slot_omega), g₁]
  · rw [a₂]; rfl
  · rw [b₂]; rfl
  · rw [O₂.word (by slot_omega) (by slot_omega), c₁]
  · intro x hx
    simp only [batchW, invTbl, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [O₂ x (by slotx_omega), U₁ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; slotx_omega)]

end VG.Proof.Weierstrass.X86_64
