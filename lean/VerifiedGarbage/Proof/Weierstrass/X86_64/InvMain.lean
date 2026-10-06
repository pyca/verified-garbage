import VerifiedGarbage.Proof.Weierstrass.X86_64.InvBatch
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Divstep.Iter
import Mathlib.Data.Nat.Prime.Basic

/-!
# Inversion by divsteps on x86-64: the whole inversion

`InvCfg.inv P` leaves `[acc]` reading (in Montgomery form) as `[base]^(m - 2)`
for a prime `m` (`invPow_ok`, as `pow_ok` for the exponent `m - 2`), given
`InvToM m`, which the variants that supply `InvSound` prove with Mathlib's
algebra (`InvArith.lean`), so that this module does not import it: the
start holds `(d, f, g, a, b) = (1, m, x, 0, 1)` (`init_ok`), each of the `B`
batches takes it to the next `Divstep.invRun` (`batch_ok`), and the end
multiplies `a` by `C` or `m - C` by the sign of `f = ±1` (`finish_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers the inversion writes. -/
theorem invClob_sub {n : Nat} (h4 : 4 ≤ n) (h7 : n < 10) : ∀ r ∈ batchRegs, r ∈ invClob n := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
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

/-- `rbx = 1`, `r14 = B`. -/
theorem initRegs_ok (s : State) {B : Nat} (hB : B < 2 ^ 16) :
    WP isa (.block [.mov32 .rbx (.imm 1), .mov32 .r14 (.imm (BitVec.ofNat 32 B))]) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 1 ∧ t.gpr .r14 = BitVec.ofNat 64 B ∧ Keeps [.rbx, .r14] s t := by
  irun [sext1']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

set_option hygiene false in
/-- The slots' arithmetic, from `slots` and the layout (named `eL` … `eU`, `n4`, `htbl`, `hn`). -/
local macro "slot_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, n4, htbl, hn])

set_option hygiene false in
/-- `slot_omega` with the modulus's place (`hmt`, `hmo`). -/
local macro "slotm_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, n4, htbl, hn, hmt, hmo])

set_option hygiene false in
/-- `slot_omega` with a hypothesis `hx` about an address. -/
local macro "slotx_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, n4, htbl, hn, hx])

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
  [.mov32 .rbx (.imm 1), .mov32 .r14 (.imm (BitVec.ofNat 32 P.B))] ++
  (copy P.M.n P.sF P.M.mo ++ zeroTop P.sF P.M.n) ++ (copy P.M.n P.sG P.base ++ zeroTop P.sG P.M.n)

/-- The start's second part: `a = 0`, `b = 1`. -/
abbrev init₂ (P : InvCfg) : List Instr :=
  zeroWords P.M.n P.sA ++ zeroWords P.M.n P.sB ++ [.mov32 .r8 (.imm 1), .store (sc P.sB) .r8]

theorem init_eq (P : InvCfg) : P.init = init₁ P ++ init₂ P := by
  simp only [InvCfg.init, init₁, init₂, List.append_assoc, List.cons_append, List.nil_append]

theorem init₁_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hB : P.B < 2 ^ 16) :
    WP isa (.block (init₁ P)) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 1 ∧ t.gpr .r14 = BitVec.ofNat 64 P.B ∧
      wordsVal t.mem base P.sF P.L = m ∧ wordsVal t.mem base P.sG P.L = wordsVal s.mem base P.base P.M.n ∧
      KeepRegs [.rax, .rbx, .r8, .r14] s t ∧ Unch base [(P.sF, 16 * P.M.n + 16)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl; have hmt := hL.mo_tbl; unfold invTbl at hmt
  have hmo := hM.mo; have hbase := hL.base; have hbt := hL.base_tbl; unfold invTbl at hbt
  rw [init₁, List.append_assoc, WP.block_append_iff]
  refine WP.mono (initRegs_ok s hB) fun s₂ ⟨b₁, a₁, k₁⟩ => ?_
  have hs₂ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyTop_ok hs₂ (dst := P.sF) (src := P.M.mo) (n := P.M.n) hmo (by slot_omega) (by slotm_omega))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have hbs : P.base + 8 * P.M.n ≤ P.sF ∨ P.sG + 8 * (P.M.n + 1) ≤ P.base := by
    omega_using [eF, eG, n4, hbt]
  refine WP.mono (copyTop_ok hs₃ (dst := P.sG) (src := P.base) (n := P.M.n) hbase (by slot_omega)
    (by omega_using [eF, eG, n4, hbs])) fun t ⟨e₄, k₄, O₄⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁]
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), a₁]
  · rw [eL, O₄.wordsVal (by slot_omega) (by slot_omega), e₃, k₁.2.1, hM.val]
  · rw [eL, e₄, O₃.wordsVal (by omega_using [eF, eG, hbs]) (by omega_using [hbase, hn]), k₁.2.1]
  · exact (((Keeps.regs k₁).mono (by decide)).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [O₄ x (by slotx_omega), O₃ x (by slotx_omega), k₁.2.1]

theorem init₂_ok {P : InvCfg} {base : Addr} {size : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size) :
    WP isa (.block (init₂ P)) s fun t =>
      wordsVal t.mem base P.sA P.M.n = 0 ∧ wordsVal t.mem base P.sB P.M.n = 1 ∧
      KeepRegs [.r8] s t ∧ Outside base P.sA (16 * P.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
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
    (hM : ModOkW P.M size m s.mem base) (hB : P.B < 2 ^ 16) :
    WP isa (.block P.init) s fun t =>
      IInv P base ⟨1, m, wordsVal s.mem base P.base P.M.n, 0, 1⟩ t ∧
      t.gpr .r14 = BitVec.ofNat 64 P.B ∧
      KeepRegs [.rax, .rbx, .r8, .r14] s t ∧ Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
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
  · rw [k₂.gpr _ (by decide), c₁]
  · intro x hx
    simp only [batchW, invTbl, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [O₂ x (by slotx_omega), U₁ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; slotx_omega)]

/-- The batches, counted down in memory, from `invRun 0` to `invRun B`. -/
theorem loop_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) {X : Nat} (hX : X < m) (hm2 : m % 2 = 1) (hm1 : 1 < m)
    (hB1 : 1 ≤ P.B) (hB : P.B < 2 ^ 16)
    (hI : IInv P base (Divstep.invRun 59 m P.M.minv.toNat X 0) s)
    (hc : s.gpr .r14 = BitVec.ofNat 64 P.B) :
    WP isa (.loop P.batch .ne) s fun t =>
      IInv P base (Divstep.invRun 59 m P.M.minv.toNat X P.B) t ∧ KeepRegs batchRegs s t ∧
      Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  have hmt := hL.mo_tbl; have hmo := hM.mo; have n4 := hL.n4
  have hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n := P.B)
    (Inv := fun j t => IInv P base (Divstep.invRun 59 m P.M.minv.toNat X (P.B - j)) t ∧
      t.gpr .r14 = BitVec.ofNat 64 j ∧ Scr t base size ∧ ModOkW P.M size m t.mem base ∧
      KeepRegs batchRegs s t ∧ Unch base (batchW P) s.mem t.mem)
    (fun j t hj1 hjB ⟨It, ct, St, Mt, Kt, Ut⟩ => ?_) (fun t ⟨It, _, _, _, Kt, Ut⟩ => ⟨by simpa using It, Kt, Ut⟩)
    hB1 ⟨by rw [Nat.sub_self]; exact hI, hc, hs, hM, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _⟩
  obtain ⟨bd, bf1, bf, bg, ba0, ba1, bb0, bb1⟩ := Divstep.invRun_bounds (N := 59) (by decide) (p := m)
    (m := P.M.minv.toNat) (x := X) (by exact_mod_cast hm2) (by exact_mod_cast hm1) hmi (by omega)
    (by exact_mod_cast hX) (P.B - j)
  refine WP.mono (batch_ok hL St Mt It (by
      have : (59 * (P.B - j) : Nat) ≤ 59 * 2 ^ 16 := Nat.mul_le_mul_left _ (by omega)
      have h2 : ((59 * (P.B - j) : Nat) : Int) ≤ 59 * 2 ^ 16 := by exact_mod_cast this
      omega) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le) (by rw [abs_of_nonneg bb0]; exact bb1.le)
    hj1 (by omega) ct) fun u ⟨⟨Iu, cu, Ku, Uu⟩, zu⟩ => ⟨⟨?_, cu, ?_, ?_, Kt.trans Ku, (Ut.trans Uu).mono ?_⟩, zu⟩
  · rw [show P.B - (j - 1) = P.B - j + 1 by omega]; exact Iu
  · exact St.of_keepRegs Ku (by decide)
  · refine modOk_out Mt Uu (fun w hw => ?_) hn
    simp only [batchW, invTbl, List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw; unfold invTbl at hmt; dsimp only; omega
  · intro w hw; simp only [batchW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw ⊢
    exact hw

/-- The selection's instructions: `rax = rcx ? Cn_i : C_i`. -/
theorem selIns_ok (s : State) (hm : IsMask (s.gpr .rcx)) (c c' : BitVec 64) :
    WP isa (.block [.movImm64 .rax c, .movImm64 .rdx c', .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx),
      .alu .xor .rax (.reg .rdx)]) s fun t =>
      t.gpr .rax = (if s.gpr .rcx = BitVec.allOnes 64 then c' else c) ∧ Keeps [.rax, .rdx] s t := by
  irun
  refine ⟨sel_eq hm, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- Words `0 … j - 1` of the constant `C` or `Cn`, by the mask in `rcx`. -/
theorem selRows_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hm : IsMask (s.gpr .rcx)) :
    ∀ j, P.sC + 8 * j ≤ size → WP isa (.block ((List.range j).flatMap fun i =>
      [.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * i))), .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * i))),
        .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx),
        .store (sc (P.sC + 8 * i)) .rax]))
      s fun t =>
        wordsVal t.mem base P.sC j = (if s.gpr .rcx = BitVec.allOnes 64 then P.Cn else P.C) % 2 ^ (64 * j) ∧
        KeepRegs [.rax, .rdx] s t ∧ Outside base P.sC (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp only [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selRows_ok hs hm j (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have m₁ : s₁.gpr .rcx = s.gpr .rcx := k₁.gpr _ (by decide)
    rw [show ([.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * j))),
        .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * j))), .alu .xor .rdx (.reg .rax),
        .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx), .store (sc (P.sC + 8 * j)) .rax] : List Instr) =
        [.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * j))), .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * j))),
          .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx)] ++
        [.store (sc (P.sC + 8 * j)) .rax] from rfl, WP.block_append_iff]
    refine WP.mono (selIns_ok s₁ (by rw [m₁]; exact hm) _ _) fun s₂ ⟨c₂, k₂⟩ => ?_
    refine WP.mono (storeReg_ok (hs₁.of_keeps k₂ (by decide)) .rax (d := P.sC + 8 * j) (by omega))
      fun t ⟨mt, _, _, kt⟩ => ?_
    have Ot := writeW_outside s₂.mem base (d := P.sC + 8 * j) (s₂.gpr .rax) (by omega)
    refine ⟨?_, (k₁.trans ((Keeps.regs k₂).mono (by decide))).trans (kt.mono (by decide)), fun x hx => by
      rw [mt, Ot x (by omega), k₂.2.1, O₁ x (by omega)]⟩
    rw [wordsVal_succ_top, mt, word_writeW_self, Ot.wordsVal (by omega) (by omega), k₂.2.1, e₁, c₂, m₁,
      pow64_succ, Nat.mul_comm (2 ^ 64), Nat.mod_mul]
    split <;> rw [const_word]

/-- The end: `[C] = C` or `Cn` by the sign of `f` (`±1`), and `acc = a [C] / R`. -/
theorem finish_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) {I : Divstep.IState} (hI : IInv P base I s) (hC : P.C < m)
    (hCn : P.Cn < m) :
    WP isa (.block P.finish) s fun t =>
      ∃ Cs, (I.f = 1 → Cs = P.C) ∧ (I.f = -1 → Cs = P.Cn) ∧
        wordsVal t.mem base P.acc P.M.n < m ∧
        wordsVal t.mem base P.acc P.M.n * 2 ^ (64 * P.M.n) % m = wordsVal s.mem base P.sA P.M.n * Cs % m ∧
        KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  have n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; unfold invTbl at htbl
  have hmt := hL.mo_tbl; unfold invTbl at hmt; have hmo := hM.mo; have hacc := hL.acc
  have hat := hL.acc_tbl; unfold invTbl at hat; have htt := hL.tbl_tmp; unfold invTbl at htt
  have hmc := hL.mo_acc; have hct := hL.acc_tmp; have htmp := hL.tmp
  have hsC : P.sC = P.sNF := rfl
  rw [InvCfg.finish, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rdx (d := P.sF) (by slot_omega)) fun s₁ ⟨c₁, _, k₁⟩ => ?_
  refine WP.mono (maskOf_ok s₁ (d := .rcx) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  have mk₂ : IsMask (s₂.gpr .rcx) := by rw [g₂]; exact smask_isMask _
  refine WP.mono (selRows_ok hs₂ mk₂ P.M.n (by rw [hsC]; slot_omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have m₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  have M₃ : ModOkW P.M size m s₃.mem base :=
    modOk_out hM (by rw [← m₂]; exact O₃.unch) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; rw [hsC]; slotm_omega) hn
  have hmP : m < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hCs : (if s₂.gpr .rcx = BitVec.allOnes 64 then P.Cn else P.C) < m := by split; exacts [hCn, hC]
  have e₃' : wordsVal s₃.mem base P.sC P.M.n = if s₂.gpr .rcx = BitVec.allOnes 64 then P.Cn else P.C := by
    rw [e₃, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (mul_ok hs₃ M₃ (o := P.acc) (a := P.sA) (b := P.sC) hacc (by slot_omega)
    (by rw [hsC]; slot_omega) hct (by omega_using [eA, htt, n4]) (by rw [hsC]; omega_using [eNF, htt, n4])
    (by omega_using [hmc]) (by rw [e₃']; exact hCs))
    fun t ⟨Kt, lt, ev⟩ =>
      ⟨if s₂.gpr .rcx = BitVec.allOnes 64 then P.Cn else P.C, ?_, ?_, lt, ?_, ?_, ?_⟩
  -- The sign of `f`, from its low word.
  · intro hf
    have hw : ((s₁.gpr .rdx).toNat : Int) % 2 ^ 64 = 1 := by
      have hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega)
      rw [c₁, low_word _ _ _ P.L (by omega), ← Int.emod_emod_of_dvd _ hdvd, hI.f,
        Int.emod_emod_of_dvd _ hdvd, hf]; rfl
    have h1 : (s₁.gpr .rdx).toNat = 1 := by have := (s₁.gpr .rdx).isLt; omega
    have h0 : s₂.gpr .rcx ≠ BitVec.allOnes 64 := fun h => by
      have := smask_toNat (s₁.gpr .rdx)
      rw [← g₂, h, BitVec.toNat_allOnes, sgnW, h1] at this; simp at this
    simp only [h0, ↓reduceIte]
  · intro hf
    have hw : ((s₁.gpr .rdx).toNat : Int) % 2 ^ 64 = 2 ^ 64 - 1 := by
      have hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega)
      rw [c₁, low_word _ _ _ P.L (by omega), ← Int.emod_emod_of_dvd _ hdvd, hI.f,
        Int.emod_emod_of_dvd _ hdvd, hf]; rfl
    have h1 : (s₁.gpr .rdx).toNat = 2 ^ 64 - 1 := by have := (s₁.gpr .rdx).isLt; omega
    have h0 : s₂.gpr .rcx = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by
      rw [g₂, smask_toNat, sgnW, h1, BitVec.toNat_allOnes]; rfl)
    simp only [h0, ↓reduceIte]
  · rw [ev, e₃', O₃.wordsVal (by rw [hsC]; slot_omega) (by slot_omega), m₂]
  · refine ⟨fun r hr => ?_, Kt.rd.trans (k₃.rd.trans (k₂.2.2.1.trans k₁.2.2.1)),
      Kt.wr.trans (k₃.wr.trans (k₂.2.2.2.trans k₁.2.2.2))⟩
    have h7 : r ∉ clob P.M.n := fun h => hr (List.mem_cons_of_mem _ h)
    have hsub : ∀ q, q ∈ [Reg.rax, .rcx, .rdx] → q ∈ powClob P.M.n := fun q h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [powClob, clob]
    rw [Kt.gpr r h7,
      k₃.gpr r (fun h => hr (hsub r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h]))),
      k₂.1 r (fun h => hr (hsub r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h]))),
      k₁.1 r (fun h => hr (hsub r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; simp [h])))]
  · intro x hx
    have h1 := hx _ (List.mem_cons_self ..)
    have h2 := hx (P.tbl, invTbl P.M.n) (by simp [invW])
    have h3 := hx (P.M.tmp, 8 * P.M.n) (by simp [invW])
    dsimp only at h1 h2 h3
    unfold invTbl at h2
    rw [Kt.mem x h1 h3, O₃ x (by rw [hsC]; omega_using [eNF, h2, n4]), m₂]

/-- `[acc] = [base]^(m - 2)` in Montgomery form, for a prime `m > 2`. -/
theorem invPow_ok {P : InvCfg} {base : Addr} {size m : Nat} [NeZero m] (hpr : m.Prime) (hT : InvToM m)
    (hL : InvLay P size) (hm2 : 2 < m) (hR : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hX : wordsVal s.mem base P.base P.M.n < m) (hC : InvOk P m) :
    WP isa (InvCfg.inv P) s fun s' => KeepRegs (invClob P.M.n) s s' ∧ Unch base (invW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2) := by
  have hn := hs.nowrap
  have n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; have hmt := hL.mo_tbl; have hmo := hM.mo
  unfold invTbl at htbl hmt
  have hm2' : m % 2 = 1 := (hpr.eq_one_or_self_of_dvd 2 |>.mt (by omega) |> fun h => by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩) (by omega)
    · omega)
  have hCm : P.C < m := by rw [hC.C]; exact Nat.mod_lt _ (by omega)
  have hCnm : P.Cn < m := by rw [hC.Cn]; have := hC.Cpos; omega
  -- The modulus, through writes to the working area.
  have modU : ∀ {mem' : Mem}, Unch base (batchW P) s.mem mem' → ModOkW P.M size m mem' base := fun U =>
    modOk_out hM U (fun w hw => by
      simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; unfold invTbl; dsimp only; omega) hn
  rw [InvCfg.inv]
  refine WP.seq (WP.mono (init_ok hL hs hM hC.B16) fun s₁ ⟨I₁, c₁, K₁, U₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  refine WP.seq (WP.mono (loop_ok hL hs₁ (modU U₁) hX hm2' (by omega) hC.B1 hC.B16 I₁ c₁)
    fun s₂ ⟨I₂, K₂, U₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs K₂ (by decide)
  have U₁₂ : Unch base (batchW P) s.mem s₂.mem := (U₁.trans U₂).mono fun w hw => by
    simp only [batchW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw ⊢; exact hw
  refine WP.mono (finish_ok hL hs₂ (modU U₁₂) I₂ hCm hCnm) fun t ⟨Cs, hf1, hfm1, lt, ev, K₃, U₃⟩ =>
    ⟨?_, ?_, lt, ?_⟩
  · have hsub := invClob_sub n4 n7
    exact (((K₁.mono fun r h => hsub r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h | h <;> simp [h])).trans (K₂.mono hsub)).trans
      (K₃.mono fun r h => List.mem_cons_of_mem _ h))
  · intro x hx
    rw [U₃ x hx, U₁₂ x fun w hw => by
      simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      exact hx (P.tbl, invTbl P.M.n) (by simp [invW])]
  -- The arithmetic.
  set X := wordsVal s.mem base P.base P.M.n with hXd
  set I := Divstep.invRun 59 m P.M.minv.toNat X P.B with hId
  have hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  have ha : (wordsVal s₂.mem base P.sA P.M.n : Int) = I.a := I₂.a
  -- The divsteps end.
  have done : ∀ x : Int, 0 ≤ x → x < m → (Divstep.divsteps (59 * P.B) (1, m, x)).2.2 = 0 ∧
      (Divstep.divsteps (59 * P.B) (1, m, x)).2.1.natAbs = Int.gcd m x := fun x h0 h1 => by
    have hodd : (m : Int) % 2 = 1 := by exact_mod_cast hm2'
    have hmP := hM.val ▸ wordsVal_lt s.mem base P.M.mo P.M.n
    have hfn : (m : Int) < 2 ^ (64 * P.M.n) := by exact_mod_cast hmP
    exact Divstep.divsteps_words hodd h0 h1.le hfn hC.bound
  -- `x ≠ 0`: `f = ±1` and `x f a 2^(5 B) ≡ 1`.
  have spec : X ≠ 0 → (I.f = 1 ∨ I.f = -1) ∧ (X : Int) * (I.f * I.a) * 2 ^ ((64 - 59) * P.B) ≡ 1 [ZMOD m] :=
    fun hX0 => Divstep.invRun_spec (N := 59) (B := P.B) (by decide) (by exact_mod_cast hm2')
      (by exact_mod_cast hpr.one_lt) hmi (done X (by omega) (by exact_mod_cast hX)) (by
        rw [Int.gcd_natCast_natCast]
        exact Nat.coprime_of_lt_prime (by omega) hX hpr)
  refine hT (K := 2 ^ (5 * P.B)) (f := I.f) (a := wordsVal s₂.mem base P.sA P.M.n) (Cs := Cs) hm2 hR hX
    ?_ ?_ ?_ ev
  · intro hX0
    have h := (Divstep.invRun_zero (N := 59) (p := m) (m := P.M.minv.toNat) (by omega) P.B).2
    have hIa : I.a = 0 := by rw [hId, hX0, Nat.cast_zero]; exact h
    have : (wordsVal s₂.mem base P.sA P.M.n : Int) = 0 := by rw [ha, hIa]
    exact_mod_cast this
  · intro hX0
    have h := (spec hX0).2
    rw [ha, show (64 - 59) * P.B = 5 * P.B by omega] at *
    push_cast
    exact h
  · intro hX0
    rcases (spec hX0).1 with h | h
    · rw [hf1 h, hC.C, h]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]; ring_nf
    · rw [hfm1 h, hC.Cn, h, Nat.cast_sub hCm.le]
      have hc : (P.C : Int) ≡ ((2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 : Nat) : Int) [ZMOD m] := by
        rw [hC.C]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
      have hm0 : (m : Int) ≡ 0 [ZMOD m] := Int.emod_self.trans (Int.zero_emod _).symm
      have := hm0.sub hc
      push_cast at this ⊢
      rw [show (-1 : Int) * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3) =
        0 - 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 by ring]
      exact this

/-- A prime modulus's inversion is sound. -/
theorem invSound_of_toM {m : Nat} [NeZero m] (hp : m.Prime) (hT : InvToM m) : InvSound m :=
  fun hL hm2 hR _ hs hM hX hC => invPow_ok hp hT hL hm2 hR hs hM hX hC

end VG.Proof.Weierstrass.X86_64
