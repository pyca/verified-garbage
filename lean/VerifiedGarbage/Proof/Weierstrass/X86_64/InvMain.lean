module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvBatch
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Divstep.Iter
import VerifiedGarbage.Proof.Framework.IsPrime
import Mathlib.Tactic.FieldSimp
public import VerifiedGarbage.Proof.Weierstrass.InvMask
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Batch
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Inversion by divsteps on x86-64: the whole inversion

`InvCfg.inv P` leaves `[acc]` reading (in Montgomery form) as `[base]^(m - 2)`
for a prime `m` (`invPow_ok`, as `pow_ok` for the exponent `m - 2`), given
`InvToM m`, which the variants that supply `InvSound` prove with Mathlib's
algebra (`InvArith.lean`), so that this module does not import it: the
start holds `(d, f, g, a, b) = (1, m, x, 0, 1)` (`init_ok`), each of the `B`
batches takes it to the next `Divstep.invRunS` (`batch_ok`), and the end
brings `a` into `[0, m)`, where it is `Divstep.invRun`'s (`norm_invRunS`), and
multiplies it by `C` or `m - C` by the sign of `f = ±1` (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Divstep

/-! ## A run from `b = c`

A shared inversion starts `b` at a seed `c` rather than `1`, so that `a` ends
scaled by `c`: `invRunC` is `invRunS` from `b = c`, whose `d`, `f`, `g` are
`invRun`'s and whose `a`, `b` are `c` times its, modulo `p` (`invRunC_rel`). -/

/-- `invRunS` from `(d, f, g, a, b) = (1, p, x, 0, c)`. -/
def invRunC (N : Nat) (p m x c : Int) : Nat → IState
  | 0 => ⟨1, p, x, 0, c⟩
  | B + 1 => batchS N p m (invRunC N p m x c B)

theorem invRunC_one (N : Nat) (p m x : Int) : ∀ B, invRunC N p m x 1 B = invRunS N p m x B
  | 0 => rfl
  | B + 1 => by simp only [invRunC, invRunS, invRunC_one N p m x B]

/-- `mredRaw` of `c t` is `c` times `mred t`, modulo `p`. -/
theorem mredRaw_mul_cong {p m t c : Int} (hp : p % 2 = 1) (hp0 : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) :
    mredRaw p m (c * t) ≡ c * mred p m t [ZMOD p] := by
  apply cancel_pow2 (N := 64) hp hp0
  have e : 2 ^ 64 * mredRaw p m (c * t) ≡ c * t [ZMOD p] := by
    rw [mredRaw_spec hm]; exact Int.add_mul_emod_self_right _ _ _
  refine e.trans ?_
  have h := (mred_cong (t := t) hm).symm.mul_left c
  rw [show c * (2 ^ 64 * mred p m t) = 2 ^ 64 * (c * mred p m t) by ring] at h
  exact h

theorem invRunC_rel {N : Nat} {p m x c : Int} (hp : p % 2 = 1) (hp0 : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) :
    ∀ B, (invRunC N p m x c B).d = (invRun N p m x B).d ∧ (invRunC N p m x c B).f = (invRun N p m x B).f ∧
      (invRunC N p m x c B).g = (invRun N p m x B).g ∧
      (invRunC N p m x c B).a ≡ c * (invRun N p m x B).a [ZMOD p] ∧
      (invRunC N p m x c B).b ≡ c * (invRun N p m x B).b [ZMOD p]
  | 0 => ⟨rfl, rfl, rfl, by simp [invRunC, invRun, Int.ModEq], by simp [invRunC, invRun, Int.ModEq]⟩
  | B + 1 => by
    obtain ⟨hd, hf, hg, ha, hb⟩ := invRunC_rel (N := N) (x := x) (c := c) hp hp0 hm B
    simp only [invRunC, invRun, batchS, batch]
    rw [hd, hf, hg]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · refine (mredRaw_cong hp hp0 hm (((ha.mul_left _).add (hb.mul_left _)).trans ?_)).trans
        (mredRaw_mul_cong hp hp0 hm)
      rw [show ∀ u v a b : Int, u * (c * a) + v * (c * b) = c * (u * a + v * b) from fun _ _ _ _ => by ring]
    · refine (mredRaw_cong hp hp0 hm (((ha.mul_left _).add (hb.mul_left _)).trans ?_)).trans
        (mredRaw_mul_cong hp hp0 hm)
      rw [show ∀ u v a b : Int, u * (c * a) + v * (c * b) = c * (u * a + v * b) from fun _ _ _ _ => by ring]

/-- `a`, `b` stay in `(-p, 2p)`, from `c` in it. -/
theorem invRunC_range {N : Nat} (hN : N ≤ 62) {p m x c : Int} (hp1 : 1 < p) (hm : (p * m + 1) % 2 ^ 64 = 0)
    (hc0 : -p < c) (hc1 : c < 2 * p) :
    ∀ B, -p < (invRunC N p m x c B).a ∧ (invRunC N p m x c B).a < 2 * p ∧
      -p < (invRunC N p m x c B).b ∧ (invRunC N p m x c B).b < 2 * p
  | 0 => by simp only [invRunC]; omega_arith
  | B + 1 => by
    obtain ⟨a0, a1, b0, b1⟩ := invRunC_range (x := x) hN hp1 hm hc0 hc1 B
    set s := invRunC N p m x c B
    obtain ⟨bu, bq⟩ := msteps_bnd s.d s.f s.g N
    have ha : |s.a| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
    have hb : |s.b| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
    have rA := mredRaw_range (by omega_arith) hm (comb_le2 hN (by omega_arith) bu ha hb)
    have rB := mredRaw_range (by omega_arith) hm (comb_le2 hN (by omega_arith) bq ha hb)
    simp only [invRunC, batchS]
    exact ⟨rA.1, rA.2, rB.1, rB.2⟩

/-- Divsteps from `g = 0` keep `f`. -/
theorem divsteps_g0 : ∀ (k : Nat) (d f : Int), (divsteps k (d, f, 0)).2.1 = f
  | 0, _, _ => rfl
  | k + 1, d, f => by
    rw [divsteps, show divstep (d, f, 0) = (2 + d, f, 0) by simp [divstep]]
    exact divsteps_g0 k _ _

/-- The inversion of `0` ends with `f = p`. -/
theorem invRun_f_zero {N : Nat} {p m : Int} (hp : p % 2 = 1) (B : Nat) : (invRun N p m 0 B).f = p := by
  obtain h := (invRun_dfg (N := N) (m := m) (x := 0) hp B).1
  obtain e : (invRun N p m 0 B).f = (divsteps (N * B) (1, p, 0)).2.1 := by rw [← h]
  rw [e, divsteps_g0]

end VG.Proof.Divstep

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers the inversion writes. -/
theorem invClob_sub {n : Nat} (h4 : 4 ≤ n) (h7 : n < 10) : ∀ r ∈ batchRegs, r ∈ invClob n := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega_using [h4, h7]
  all_goals decide

/-- `[dst] = [src]` (`n` words) with a zero word on top. -/
theorem copyTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src n : Nat}
    (hsrc : src + 8 * n ≤ size) (hdst : dst + 8 * (n + 1) ≤ size) (hsep : dst + 8 * (n + 1) ≤ src ∨ src + 8 * n ≤ dst) :
    WP isa (.block (copy n dst src ++ zeroTop dst n)) s fun t =>
      wordsVal t.mem base dst (n + 1) = wordsVal s.mem base src n ∧ KeepRegs [.rax, .r8] s t ∧
      Outside base dst (8 * (n + 1)) s.mem t.mem := by
  have hn := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok n hs (o := dst) (a := src) (by omega_using [hdst]) hsrc (by omega_using [hsep])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  refine WP.mono (zeroTop_ok (hs.of_keepRegs k₁ (by decide)) (U := dst) (n := n) (by omega_using [hdst])) fun t ⟨z, kt, Ot⟩ =>
    ⟨?_, (k₁.mono (by decide)).trans (kt.mono (by decide)), fun x hx => by rw [Ot x (by omega_using [hx]), O₁ x (by omega_using [hx])]⟩
  rw [wordsVal_succ_top, Ot.wordsVal (by omega_using []) (by omega_using [hdst, hn]), z, e₁]
  simp

theorem sext1' : (1 : BitVec 32).setWidth 64 = BitVec.ofInt 64 1 := by decide

/-- `rbx = 1`, `r14 = B`. -/
theorem initRegs_ok (s : State) {B : Nat} (hB : B < 2 ^ 16) :
    WP isa (.block [.mov32 .rbx (.imm 1), .mov32 .r14 (.imm (BitVec.ofNat 32 B))]) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 1 ∧ t.gpr .r14 = BitVec.ofNat 64 B ∧ Keeps [.rbx, .r14] s t := by
  irun [sext1']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []),
      Nat.mod_eq_of_lt (by omega_using [hB]), Nat.mod_eq_of_lt (by omega_using [hB])]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-- `inv_slot_omega` with a hypothesis `hx` about an address. -/
tactic_template "inv_slotx_omega" : tactic =>
  `(tactic| ((try simp only [eL, eF, eG, eA, eB, eNF, eNG, eT, eU] at hx ⊢); omega_using [n4, htbl, hn, hx]))

theorem zext1' : (1 : BitVec 32).setWidth 64 = 1 := by decide

/-- `[d] = 1`, through `r8`. -/
theorem setOne_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block [.mov32 .r8 (.imm 1), .store (sc d) .r8]) s fun t =>
      t.mem = s.mem.writeW (off base d) (1 : BitVec 64) ∧ KeepRegs [.r8] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  obtain h : WP isa (.block [.mov32 .r8 (.imm 1)]) s fun v => v.gpr .r8 = 1 ∧ Keeps [.r8] s v := by
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
  zeroWords P.L P.sA ++ zeroWords P.L P.sB ++ [.mov32 .r8 (.imm 1), .store (sc P.sB) .r8]

theorem init_eq (P : InvCfg) (h : P.seed = none) : P.init = init₁ P ++ init₂ P := by
  simp only [InvCfg.init, h, init₁, init₂, List.append_assoc, List.cons_append, List.nil_append]

theorem init₁_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hB : P.B < 2 ^ 16) :
    WP isa (.block (init₁ P)) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 1 ∧ t.gpr .r14 = BitVec.ofNat 64 P.B ∧
      wordsVal t.mem base P.sF P.L = m ∧ wordsVal t.mem base P.sG P.L = wordsVal s.mem base P.base P.M.n ∧
      KeepRegs [.rax, .rbx, .r8, .r14] s t ∧ Unch base [(P.sF, 16 * P.M.n + 16)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl; have hmt := hL.mo_tbl; unfold invTbl at hmt
  obtain hmo := hM.mo; have hbase := hL.base; have hbt := hL.base_tbl; unfold invTbl at hbt
  rw [init₁, List.append_assoc, WP.block_append_iff]
  refine WP.mono (initRegs_ok s hB) fun s₂ ⟨b₁, a₁, k₁⟩ => ?_
  obtain hs₂ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyTop_ok hs₂ (dst := P.sF) (src := P.M.mo) (n := P.M.n) hmo (by inv_slot_omega) (by inv_slotm_omega))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain hbs : P.base + 8 * P.M.n ≤ P.sF ∨ P.sG + 8 * (P.M.n + 1) ≤ P.base := by
    omega_using [eF, eG, n4, hbt]
  refine WP.mono (copyTop_ok hs₃ (dst := P.sG) (src := P.base) (n := P.M.n) hbase (by inv_slot_omega)
    (by omega_using [eF, eG, n4, hbs])) fun t ⟨e₄, k₄, O₄⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁]
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), a₁]
  · rw [eL, O₄.wordsVal (by inv_slot_omega) (by inv_slot_omega), e₃, k₁.2.1, hM.val]
  · rw [eL, e₄, O₃.wordsVal (by omega_using [eF, eG, hbs]) (by omega_using [hbase, hn]), k₁.2.1]
  · exact (((Keeps.regs k₁).mono (by decide)).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [O₄ x (by inv_slotx_omega), O₃ x (by inv_slotx_omega), k₁.2.1]

theorem init₂_ok {P : InvCfg} {base : Addr} {size : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size) :
    WP isa (.block (init₂ P)) s fun t =>
      wordsVal t.mem base P.sA P.L = 0 ∧ wordsVal t.mem base P.sB P.L = 1 ∧
      KeepRegs [.r8] s t ∧ Outside base P.sA (16 * P.M.n + 16) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [init₂, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroWords_ok hs (k := P.L) (t := P.sA) (by inv_slot_omega)) fun s₅ ⟨z₅, k₅, O₅⟩ => ?_
  obtain hs₅ := hs.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroWords_ok hs₅ (k := P.L) (t := P.sB) (by inv_slot_omega)) fun s₆ ⟨z₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_keepRegs k₆ (by decide)
  refine WP.mono (setOne_ok hs₆ (d := P.sB) (by inv_slot_omega)) fun t ⟨mt, kt⟩ => ?_
  obtain Ot : Outside base P.sB 8 s₆.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by inv_slot_omega)
  refine ⟨?_, ?_, (k₅.trans k₆).trans kt, fun x hx => by
    rw [Ot x (by inv_slotx_omega), O₆ x (by inv_slotx_omega), O₅ x (by inv_slotx_omega)]⟩
  · rw [Ot.wordsVal (by inv_slot_omega) (by inv_slot_omega), O₆.wordsVal (by inv_slot_omega) (by inv_slot_omega), z₅]
  · obtain ⟨k, hk⟩ : ∃ k, P.L = k + 1 := ⟨P.M.n, eL⟩
    have z₆' := z₆
    rw [hk, wordsVal] at z₆'
    obtain h0 : wordsVal s₆.mem base (P.sB + 8) k = 0 := by
      rcases Nat.eq_zero_or_pos (wordsVal s₆.mem base (P.sB + 8) k) with h | h
      · exact h
      · have := Nat.mul_le_mul_left (2 ^ 64) h; omega_using [z₆']
    rw [hk, wordsVal, mt, word_writeW_self, (writeW_outside s₆.mem base (d := P.sB) 1 (by inv_slot_omega)).wordsVal
      (by omega_using [hk]) (by omega_using [hk, eL, eB, n4, htbl, hn]), h0]
    rfl

/-- The start: `d = 1`, the count, and `(f, g, a, b) = (m, x, 0, 1)`. -/
theorem init_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hB : P.B < 2 ^ 16) (hS : P.seed = none) :
    WP isa (.block P.init) s fun t =>
      IInv P base ⟨1, m, wordsVal s.mem base P.base P.M.n, 0, 1⟩ t ∧
      t.gpr .r14 = BitVec.ofNat 64 P.B ∧
      KeepRegs [.rax, .rbx, .r8, .r14] s t ∧ Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [init_eq P hS, WP.block_append_iff]
  refine WP.mono (init₁_ok hL hs hM hB) fun s₁ ⟨b₁, c₁, f₁, g₁, k₁, U₁⟩ => ?_
  refine WP.mono (init₂_ok hL (hs.of_keepRegs k₁ (by decide))) fun t ⟨a₂, b₂, k₂, O₂⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, k₁.trans (k₂.mono (by decide)), ?_⟩
  · rw [k₂.gpr _ (by decide), b₁]
  · rw [O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega), f₁]
  · rw [O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega), g₁]
  · rw [a₂]; rfl
  · rw [b₂]; rfl
  · rw [k₂.gpr _ (by decide), c₁]
  · intro x hx
    simp only [batchW, invTbl, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [O₂ x (by inv_slotx_omega), U₁ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; inv_slotx_omega)]

/-- The batches, counted down in memory, from `invRunC 0` to `invRunC B`, from
`b = c`. -/
theorem loop_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) {X : Nat} (hX : X < m) (hm2 : m % 2 = 1) (hm1 : 1 < m)
    (hB1 : 1 ≤ P.B) (hB : P.B < 2 ^ 16) {c : Int} (hc0 : -(m : Int) < c) (hc1 : c < 2 * m)
    (hI : IInv P base (Divstep.invRunC 59 m P.M.minv.toNat X c 0) s)
    (hc : s.gpr .r14 = BitVec.ofNat 64 P.B) (hr : P.seed.isSome = true → s.gpr .r15 = P.M.minv) :
    WP isa (.loop P.batch .ne) s fun t =>
      IInv P base (Divstep.invRunC 59 m P.M.minv.toNat X c P.B) t ∧ KeepRegs batchRegs s t ∧
      Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain hmt := hL.mo_tbl; have hmo := hM.mo; have n4 := hL.n4
  obtain hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n := P.B)
    (Inv := fun j t => IInv P base (Divstep.invRunC 59 m P.M.minv.toNat X c (P.B - j)) t ∧
      t.gpr .r14 = BitVec.ofNat 64 j ∧ Scr t base size ∧ ModOkW P.M size m t.mem base ∧
      KeepRegs batchRegs s t ∧ Unch base (batchW P) s.mem t.mem)
    (fun j t hj1 hjB ⟨It, ct, St, Mt, Kt, Ut⟩ => ?_) (fun t ⟨It, _, _, _, Kt, Ut⟩ => ⟨by simpa using It, Kt, Ut⟩)
    hB1 ⟨by rw [Nat.sub_self]; exact hI, hc, hs, hM, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _⟩
  obtain ⟨bd, bf1, bf, bg, -, -, -, -⟩ := Divstep.invRun_bounds (N := 59) (by decide) (p := m)
    (m := P.M.minv.toNat) (x := X) (by exact_mod_cast hm2) (by exact_mod_cast hm1) hmi (by omega_using [])
    (by exact_mod_cast hX) (P.B - j)
  obtain ⟨rd, rf, rg, -, -⟩ := Divstep.invRunC_rel (N := 59) (x := (X : Int)) (c := c) (by exact_mod_cast hm2)
    (by omega_using [hm1]) hmi (P.B - j)
  obtain ⟨ba0, ba1, bb0, bb1⟩ := Divstep.invRunC_range (N := 59) (x := (X : Int)) (by decide)
    (by exact_mod_cast hm1) hmi hc0 hc1 (P.B - j)
  rw [← rd] at bd
  rw [← rf] at bf1 bf
  rw [← rg] at bg
  refine WP.mono (batch_ok hL St Mt It (by
      have : (59 * (P.B - j) : Nat) ≤ 59 * 2 ^ 16 := Nat.mul_le_mul_left _ (by omega_using [hB])
      obtain h2 : ((59 * (P.B - j) : Nat) : Int) ≤ 59 * 2 ^ 16 := by exact_mod_cast this
      omega_using [bd, h2]) bf1 bf bg (abs_le.mpr ⟨by omega_using [ba0], ba1.le⟩) (abs_le.mpr ⟨by omega_using [bb0], bb1.le⟩)
    hj1 (by omega_using [hB, hjB]) ct (fun h => by rw [Kt.gpr _ (by decide)]; exact hr h))
    fun u ⟨⟨Iu, cu, Ku, Uu⟩, zu⟩ => ⟨⟨?_, cu, ?_, ?_, Kt.trans Ku, (Ut.trans Uu).mono ?_⟩, zu⟩
  · rw [show P.B - (j - 1) = P.B - j + 1 by omega_using [hj1, hjB]]; exact Iu
  · exact St.of_keepRegs Ku (by decide)
  · refine modOk_out Mt Uu (fun w hw => ?_) hn
    simp only [batchW, invTbl, List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw; unfold invTbl at hmt; dsimp only; omega_using [hmt]
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
    refine WP.mono (selRows_ok hs hm j (by omega_using [hj])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    obtain hs₁ := hs.of_keepRegs k₁ (by decide)
    obtain m₁ : s₁.gpr .rcx = s.gpr .rcx := k₁.gpr _ (by decide)
    rw [show ([.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * j))),
        .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * j))), .alu .xor .rdx (.reg .rax),
        .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx), .store (sc (P.sC + 8 * j)) .rax] : List Instr) =
        [.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * j))), .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * j))),
          .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx)] ++
        [.store (sc (P.sC + 8 * j)) .rax] from rfl, WP.block_append_iff]
    refine WP.mono (selIns_ok s₁ (by rw [m₁]; exact hm) _ _) fun s₂ ⟨c₂, k₂⟩ => ?_
    refine WP.mono (storeReg_ok (hs₁.of_keeps k₂ (by decide)) .rax (d := P.sC + 8 * j) (by omega_using [hj]))
      fun t ⟨mt, _, _, kt⟩ => ?_
    obtain Ot := writeW_outside s₂.mem base (d := P.sC + 8 * j) (s₂.gpr .rax) (by omega_using [hj, hn])
    refine ⟨?_, (k₁.trans ((Keeps.regs k₂).mono (by decide))).trans (kt.mono (by decide)), fun x hx => by
      rw [mt, Ot x (by omega_using [hx]), k₂.2.1, O₁ x (by omega_using [hx])]⟩
    rw [wordsVal_succ_top, mt, word_writeW_self, Ot.wordsVal (by omega_using []) (by omega_using [hj, hn]), k₂.2.1, e₁, c₂, m₁,
      pow64_succ, Nat.mul_comm (2 ^ 64), Nat.mod_mul]
    split <;> rw [const_word]

/-- The end but the normalization of `a`: the selection of `C` and the multiplication. -/
abbrev finTail (P : InvCfg) : List Instr :=
  [.mov .rdx (.mem (sc P.sF))] ++ maskOf .rcx .rdx ++
  ((List.range P.M.n).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (P.C >>> (64 * i))), .movImm64 .rdx (BitVec.ofNat 64 (P.Cn >>> (64 * i))),
      .alu .xor .rdx (.reg .rax), .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx),
      .store (sc (P.sC + 8 * i)) .rax]) ++
  VG.Impl.Mont.X86_64.mul P.M P.acc P.sA P.sC

theorem finish_eq (P : InvCfg) (h : P.seed = none) : P.finish = normC P.M (P.sA - 8) P.sNG ++ finTail P := by
  simp only [InvCfg.finish, h, finTail, List.append_assoc]

/-- `[C] = C` or `Cn` by the sign of `f` (`±1`), and `acc = a [C] / R`. -/
theorem finTail_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) {I : Divstep.IState}
    (hF : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.f % ((2 ^ (64 * P.L) : Nat) : Int))
    (hC : P.C < m) (hCn : P.Cn < m) :
    WP isa (.block (finTail P)) s fun t =>
      ∃ Cs, (I.f = 1 → Cs = P.C) ∧ (I.f = -1 → Cs = P.Cn) ∧
        wordsVal t.mem base P.acc P.M.n < m ∧
        wordsVal t.mem base P.acc P.M.n * 2 ^ (64 * P.M.n) % m = wordsVal s.mem base P.sA P.M.n * Cs % m ∧
        KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; unfold invTbl at htbl
  obtain hmt := hL.mo_tbl; unfold invTbl at hmt; have hmo := hM.mo; have hacc := hL.acc
  obtain hat := hL.acc_tbl; unfold invTbl at hat; have htt := hL.tbl_tmp; unfold invTbl at htt
  obtain hmc := hL.mo_acc; have hct := hL.acc_tmp; have htmp := hL.tmp
  have hsC : P.sC = P.sNF := rfl
  rw [finTail, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rdx (d := P.sF) (by inv_slot_omega)) fun s₁ ⟨c₁, _, k₁⟩ => ?_
  refine WP.mono (maskOf_ok s₁ (d := .rcx) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  obtain hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  obtain mk₂ : IsMask (s₂.gpr .rcx) := by rw [g₂]; exact smask_isMask _
  refine WP.mono (selRows_ok hs₂ mk₂ P.M.n (by rw [hsC]; inv_slot_omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  obtain M₃ : ModOkW P.M size m s₃.mem base :=
    modOk_out hM (by rw [← m₂]; exact O₃.unch) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; rw [hsC]; inv_slotm_omega) hn
  obtain hmP : m < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain hCs : (if s₂.gpr .rcx = BitVec.allOnes 64 then P.Cn else P.C) < m := by split; exacts [hCn, hC]
  obtain e₃' : wordsVal s₃.mem base P.sC P.M.n = if s₂.gpr .rcx = BitVec.allOnes 64 then P.Cn else P.C := by
    rw [e₃, Nat.mod_eq_of_lt (by omega_using [hmP, hCs])]
  refine WP.mono (mul_ok hs₃ M₃ (o := P.acc) (a := P.sA) (b := P.sC) hacc (by inv_slot_omega)
    (by rw [hsC]; inv_slot_omega) hct (by omega_using [eA, htt, n4]) (by rw [hsC]; omega_using [eNF, htt, n4])
    (by omega_using [hmc]) (by rw [e₃']; exact hCs))
    fun t ⟨Kt, lt, ev⟩ =>
      ⟨if s₂.gpr .rcx = BitVec.allOnes 64 then P.Cn else P.C, ?_, ?_, lt, ?_, ?_, ?_⟩
  -- The sign of `f`, from its low word.
  · intro hf
    obtain hw : ((s₁.gpr .rdx).toNat : Int) % 2 ^ 64 = 1 := by
      obtain hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega_using [eL])
      rw [c₁, low_word _ _ _ P.L (by omega_using [eL]), ← Int.emod_emod_of_dvd _ hdvd, hF,
        Int.emod_emod_of_dvd _ hdvd, hf]; rfl
    obtain h1 : (s₁.gpr .rdx).toNat = 1 := by have := (s₁.gpr .rdx).isLt; omega_using [hw]
    obtain h0 : s₂.gpr .rcx ≠ BitVec.allOnes 64 := fun h => by
      have := smask_toNat (s₁.gpr .rdx)
      rw [← g₂, h, BitVec.toNat_allOnes, sgnW, h1] at this; simp at this
    simp only [h0, ↓reduceIte]
  · intro hf
    obtain hw : ((s₁.gpr .rdx).toNat : Int) % 2 ^ 64 = 2 ^ 64 - 1 := by
      obtain hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by omega_using [eL])
      rw [c₁, low_word _ _ _ P.L (by omega_using [eL]), ← Int.emod_emod_of_dvd _ hdvd, hF,
        Int.emod_emod_of_dvd _ hdvd, hf]; rfl
    obtain h1 : (s₁.gpr .rdx).toNat = 2 ^ 64 - 1 := by have := (s₁.gpr .rdx).isLt; omega_using [hw]
    obtain h0 : s₂.gpr .rcx = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by
      rw [g₂, smask_toNat, sgnW, h1, BitVec.toNat_allOnes]; rfl)
    simp only [h0, ↓reduceIte]
  · rw [ev, e₃', O₃.wordsVal (by rw [hsC]; inv_slot_omega) (by inv_slot_omega), m₂]
  · refine ⟨fun r hr => ?_, Kt.rd.trans (k₃.rd.trans (k₂.2.2.1.trans k₁.2.2.1)),
      Kt.wr.trans (k₃.wr.trans (k₂.2.2.2.trans k₁.2.2.2))⟩
    obtain h7 : r ∉ clob P.M.n := fun h => hr (mem_powClob_of_clob h)
    obtain hsub : ∀ q, q ∈ [Reg.rax, .rcx, .rdx] → q ∈ powClob P.M.n := fun q h => by
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
    obtain h1 := hx _ (List.mem_cons_self ..)
    obtain h2 := hx (P.tbl, invTbl P.M.n) (by simp [invW])
    obtain h3 := hx (P.M.tmp, 8 * P.M.n) (by simp [invW])
    dsimp only at h1 h2 h3
    unfold invTbl at h2
    rw [Kt.mem x h1 h3, O₃ x (by rw [hsC]; omega_using [eNF, h2, n4]), m₂]

/-- The registers the normalization writes. -/
theorem normRegs_sub {n : Nat} (h4 : 4 ≤ n) (h7 : n < 10) : ∀ r ∈ [Reg.rax, .rdx, .r8, .r13], r ∈ powClob n := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega_using [h4, h7]
  all_goals decide

/-- The end: `a` into `[0, m)`, `[C] = C` or `Cn` by the sign of `f` (`±1`), and
`acc = a [C] / R`. -/
theorem finish_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) {I : Divstep.IState} (hI : IInv P base I s)
    (hS : P.seed = none) (ha0 : -(m : Int) < I.a) (ha1 : I.a < 2 * m) (hC : P.C < m) (hCn : P.Cn < m) :
    WP isa (.block P.finish) s fun t =>
      ∃ Cs A : Nat, (A : Int) = Divstep.norm m I.a ∧ (I.f = 1 → Cs = P.C) ∧ (I.f = -1 → Cs = P.Cn) ∧
        wordsVal t.mem base P.acc P.M.n < m ∧
        wordsVal t.mem base P.acc P.M.n * 2 ^ (64 * P.M.n) % m = A * Cs % m ∧
        KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; unfold invTbl at htbl
  obtain hmt := hL.mo_tbl; unfold invTbl at hmt; have hmo := hM.mo
  obtain e8 : P.sA - 8 + 8 = P.sA := by omega_using [eA]
  rw [finish_eq P hS, WP.block_append_iff]
  refine WP.mono (normC_ok hs hM (t := P.sA - 8) (U := P.sNG) (by inv_slot_omega) (by inv_slot_omega)
    (by inv_slotm_omega) (by inv_slot_omega) (by inv_slotm_omega) ha0 ha1 (by rw [e8]; exact hI.a))
    fun s₀ ⟨e₀, k₀, U₀⟩ => ?_
  rw [e8] at e₀ U₀
  obtain hs₀ := hs.of_keepRegs k₀ (by decide)
  obtain M₀ := modOk_out hM U₀ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; inv_slotm_omega) hn
  obtain hf₀ : (wordsVal s₀.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
      I.f % ((2 ^ (64 * P.L) : Nat) : Int) := by
    rw [U₀.wordsVal (by inv_apart_arith; done) (by inv_slot_omega)]; exact hI.f
  refine WP.mono (finTail_ok hL hs₀ M₀ hf₀ hC hCn) fun t ⟨Cs, h1, h2, lt, ev, K, U⟩ =>
    ⟨Cs, wordsVal s₀.mem base P.sA P.M.n, e₀, h1, h2, lt, ev, (k₀.mono (normRegs_sub n4 n7)).trans K, ?_⟩
  intro x hx
  obtain h2 := hx (P.tbl, invTbl P.M.n) (by simp [invW])
  dsimp only at h2
  unfold invTbl at h2
  rw [U x hx, U₀ x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega_using [h2, eL, eA, eNG, n4])]

/-! ## A shared inversion

A seeded inversion (`P.seed = some (sd, md)`) reads `-m⁻¹ mod 2^64` at `md`
into `r15` and starts `b` at the seed at `sd` (`initS_ok`), and ends with
`acc = a` or `m - a` by the sign of `f` (`finishS_ok`). -/

theorem initS_eq (P : InvCfg) {sd md : Nat} (h : P.seed = some (sd, md)) :
    P.init = ([.mov .r15 (.mem (sc md))] : List Instr) ++ init₁ P ++
      (zeroWords P.L P.sA ++ (copy P.M.n P.sB sd ++ zeroTop P.sB P.M.n)) := by
  simp only [InvCfg.init, h, init₁, List.append_assoc, List.cons_append, List.nil_append]

/-- The seeded start: `r15 = [md]`, `d = 1`, the count, and `(f, g, a, b) = (m, x, 0, [sd])`. -/
theorem initS_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hB : P.B < 2 ^ 16) {sd md : Nat} (hS : P.seed = some (sd, md))
    (hsd : sd + 8 * P.M.n ≤ size) (hst : sd + 8 * P.M.n ≤ P.tbl ∨ P.tbl + invTbl P.M.n ≤ sd)
    (hmd : md + 8 ≤ size) :
    WP isa (.block P.init) s fun t =>
      IInv P base ⟨1, m, wordsVal s.mem base P.base P.M.n, 0, wordsVal s.mem base sd P.M.n⟩ t ∧
      t.gpr .r14 = BitVec.ofNat 64 P.B ∧ t.gpr .r15 = word s.mem base md ∧
      KeepRegs [.rax, .rbx, .r8, .r14, .r15] s t ∧ Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl hst
  rw [initS_eq P hS, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r15 hmd) fun s₀ ⟨r₀, _, k₀⟩ => ?_
  obtain hs₀ := hs.of_keeps k₀ (by decide)
  obtain m₀ : s₀.mem = s.mem := k₀.2.1
  refine WP.mono (init₁_ok (m := m) hL hs₀ (by rw [m₀]; exact hM) hB) fun s₁ ⟨b₁, c₁, f₁, g₁, k₁, U₁⟩ => ?_
  obtain hs₁ := hs₀.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroWords_ok hs₁ (k := P.L) (t := P.sA) (by inv_slot_omega)) fun s₂ ⟨a₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copyTop_ok hs₂ (dst := P.sB) (src := sd) (n := P.M.n) hsd (by inv_slot_omega)
    (by omega_using [eB, hst, n4])) fun t ⟨b₃, k₃, O₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), b₁]
  · rw [O₃.wordsVal (by inv_slot_omega) (by inv_slot_omega), O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega), f₁]
  · rw [O₃.wordsVal (by inv_slot_omega) (by inv_slot_omega), O₂.wordsVal (by inv_slot_omega) (by inv_slot_omega), g₁,
      m₀]
  · rw [O₃.wordsVal (by inv_slot_omega) (by inv_slot_omega), a₂]; rfl
  · rw [eL, b₃, O₂.wordsVal (by omega_using [eA, eL, hst, n4]) (by omega_using [hsd, hn]),
      U₁.wordsVal (by inv_apart_arith) (by omega_using [hsd, hn]), m₀]
  · rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁]
  · rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), r₀]
  · exact ((((Keeps.regs k₀).mono (by decide)).trans (k₁.mono (by decide))).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))
  · intro x hx
    simp only [batchW, invTbl, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hx
    rw [O₃ x (by inv_slotx_omega), O₂ x (by inv_slotx_omega), U₁ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; inv_slotx_omega), m₀]

theorem finishS_eq (P : InvCfg) {sd md : Nat} (h : P.seed = some (sd, md)) :
    P.finish = normC P.M (P.sA - 8) P.sNG ++ (([.mov .rdx (.mem (sc (P.sF + 8 * P.M.n)))] : List Instr) ++ (maskOf .rcx .rdx ++
      (chainW .sub .sbb P.M.n P.acc P.M.mo P.sA ++ (([.mov .rax (.reg .rcx)] : List Instr) ++ selectsW P.M.n P.sA P.acc)))) := by
  simp only [InvCfg.finish, h, List.append_assoc]

/-- The registers the seeded end writes. -/
theorem finSRegs_sub {n : Nat} (h4 : 4 ≤ n) (h7 : n < 10) :
    ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8, .r13], r ∈ powClob n := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega_using [h4, h7]
  all_goals decide

/-- A signed number of `n + 1` words, of magnitude below `2^(64 n)`, is negative iff its top word's top bit is set. -/
theorem top_sign {W n : Nat} {f : Int} (hW : W < 2 ^ (64 * (n + 1)))
    (hf : (W : Int) % ((2 ^ (64 * (n + 1)) : Nat) : Int) = f % ((2 ^ (64 * (n + 1)) : Nat) : Int))
    (hf0 : -((2 ^ (64 * n) : Nat) : Int) < f) (hf1 : f < ((2 ^ (64 * n) : Nat) : Int)) :
    2 ^ (64 * n) * 2 ^ 63 ≤ W ↔ f < 0 := by
  rw [show 64 * (n + 1) = 64 * n + 64 by omega_using [], Nat.pow_add,
    show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at hW hf
  rw [show (2 : Nat) ^ 63 = 9223372036854775808 from rfl]
  generalize 2 ^ (64 * n) = Q at *
  obtain hQ : 0 < Q := by omega_using [hf0, hf1]
  rw [Int.emod_eq_of_lt (by omega_using []) (by push_cast; omega_using [hW])] at hf
  by_cases h : f < 0
  · rw [← Int.add_mul_emod_self_left f ((Q * 18446744073709551616 : Nat) : Int) 1,
      Int.emod_eq_of_lt (by push_cast; omega_using [h, hf0, hQ]) (by push_cast; omega_using [h])] at hf
    push_cast at hf
    simp only [h, iff_true]; omega_using [hf, hf0, hQ]
  · rw [Int.emod_eq_of_lt (by omega_using [h]) (by push_cast; omega_using [hf1, hQ])] at hf
    simp only [h, iff_false]; omega_using [hf, hf1, hQ]

/-- The seeded end: `a` into `[0, m)`, then `acc = m - a`, or `a` if `f ≥ 0`. -/
theorem finishS_ok {P : InvCfg} {base : Addr} {size m : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) {I : Divstep.IState} (hI : IInv P base I s)
    {sd md : Nat} (hS : P.seed = some (sd, md)) (ha0 : -(m : Int) < I.a) (ha1 : I.a < 2 * m)
    (hf0 : -((2 ^ (64 * P.M.n) : Nat) : Int) < I.f) (hf1 : I.f < ((2 ^ (64 * P.M.n) : Nat) : Int)) :
    WP isa (.block P.finish) s fun t =>
      ∃ A : Nat, (A : Int) = Divstep.norm m I.a ∧
        wordsVal t.mem base P.acc P.M.n = (if I.f < 0 then m - A else A) ∧
        KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  obtain n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; unfold invTbl at htbl
  obtain hmt := hL.mo_tbl; unfold invTbl at hmt; have hmo := hM.mo
  obtain hacc := hL.acc; obtain hat := hL.acc_tbl; unfold invTbl at hat; obtain hmc := hL.mo_acc
  obtain e8 : P.sA - 8 + 8 = P.sA := by omega_using [eA]
  obtain hsub := finSRegs_sub n4 n7
  obtain hsub' : ∀ l : List Reg, (∀ r ∈ l, r ∈ [Reg.rax, .rcx, .rdx, .r8, .r13]) → ∀ r ∈ l, r ∈ powClob P.M.n :=
    fun l h r hr => hsub r (h r hr)
  rw [finishS_eq P hS, WP.block_append_iff]
  refine WP.mono (normC_ok hs hM (t := P.sA - 8) (U := P.sNG) (by inv_slot_omega) (by inv_slot_omega)
    (by inv_slotm_omega) (by inv_slot_omega) (by inv_slotm_omega) ha0 ha1 (by rw [e8]; exact hI.a))
    fun s₀ ⟨e₀, k₀, U₀⟩ => ?_
  rw [e8] at e₀ U₀
  obtain hs₀ := hs.of_keepRegs k₀ (by decide)
  obtain ⟨nr0, nr1⟩ := Divstep.norm_range ha0 ha1
  obtain hA : wordsVal s₀.mem base P.sA P.M.n < m := by omega_using [e₀, nr1]
  obtain P₀ : wordsVal s₀.mem base P.M.mo P.M.n = m := by
    rw [U₀.wordsVal (by inv_apart_arith) (by omega_using [hmo, hn])]; exact hM.val
  obtain hf₀ : (wordsVal s₀.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
      I.f % ((2 ^ (64 * P.L) : Nat) : Int) := by
    rw [U₀.wordsVal (by inv_apart_arith; done) (by inv_slot_omega)]; exact hI.f
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok hs₀ .rdx (d := P.sF + 8 * P.M.n) (by inv_slot_omega)) fun s₁ ⟨c₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .rcx) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  obtain hs₂ := (hs₀.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  obtain m₂ : s₂.mem = s₀.mem := by rw [k₂.2.1, k₁.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (chainWSub_ok P.M.n hs₂ (op := .sub) (c := false) (.inl ⟨rfl, rfl⟩) (.inl (by omega_using [n4]))
    (t := P.acc) (a := P.M.mo) (b := P.sA) hacc hmo (by inv_slot_omega) (by unfold Near; omega_using [hmc])
    (by unfold Near; omega_using [hat, eA, n4])) fun s₃ ⟨cb, _, e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [m₂, P₀] at e₃
  obtain hacc₃ : wordsVal s₃.mem base P.acc P.M.n = m - wordsVal s₀.mem base P.sA P.M.n := by
    obtain hmP : m < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
    obtain hlt := wordsVal_lt s₃.mem base P.acc P.M.n
    cases cb <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at e₃ <;>
      omega_using [e₃, hA, hmP, hlt]
  rw [WP.block_append_iff]
  refine WP.mono (movReg_ok s₃ .rax .rcx) fun s₄ ⟨x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hx : s₄.gpr .rax =
      if decide (¬ 2 ^ 63 ≤ (s₁.gpr .rdx).toNat) = true then 0 else BitVec.allOnes 64 := by
    rw [x₄, k₃.gpr _ (by decide), g₂]
    apply BitVec.eq_of_toNat_eq
    rw [smask_toNat]; unfold sgnW
    by_cases h : 2 ^ 63 ≤ (s₁.gpr .rdx).toNat
    · simp only [h, ↓reduceIte, not_true_eq_false, decide_false, Bool.false_eq_true, BitVec.toNat_allOnes]
    · simp only [h, ↓reduceIte, not_false_eq_true, decide_true]; rfl
  refine WP.mono (selectsW_ok P.M.n (x := P.sA) (o := P.acc) _ hs₄ (by inv_slot_omega) hacc
    (by omega_using [hat, eA, n4]) hx) fun t ⟨e₅, k₅, O₅⟩ =>
      ⟨wordsVal s₀.mem base P.sA P.M.n, e₀, ?_, ?_, ?_⟩
  · obtain hsgn := (sgn_iff s₀.mem base P.sF P.M.n).trans (top_sign (n := P.M.n) (by
      rw [← eL]; exact wordsVal_lt _ _ _ _) (by rw [← eL]; exact hf₀) hf0 hf1)
    rw [← c₁] at hsgn
    obtain m₄ : s₄.mem = s₃.mem := k₄.2.1
    rw [e₅, m₄, hacc₃, O₃.wordsVal (by omega_using [hat, eA, n4]) (by inv_slot_omega), m₂]
    by_cases h : I.f < 0
    · simp [hsgn.mpr h, h]
    · simp only [h, ↓reduceIte, decide_eq_true_eq]
      rw [ite_eq_left (fun e => h (hsgn.mp e))]
  · exact ((((k₀.mono (hsub' _ (by decide))).trans ((Keeps.regs k₁).mono (hsub' _ (by decide)))).trans
      ((Keeps.regs k₂).mono (hsub' _ (by decide)))).trans ((k₃.mono (hsub' _ (by decide))).trans
      (((Keeps.regs k₄).mono (hsub' _ (by decide))).trans (k₅.mono (hsub' _ (by decide))))))
  · intro x hx
    obtain h1 := hx _ (List.mem_cons_self ..)
    obtain h2 := hx (P.tbl, invTbl P.M.n) (by simp [invW])
    dsimp only at h1 h2
    unfold invTbl at h2
    rw [O₅ x h1, k₄.2.1, O₃ x h1, m₂, U₀ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega_using [h2, eL, eA, eNG, n4])]

/-- `[acc] = [base]^(m - 2)` in Montgomery form, for a prime `m > 2`. -/
theorem invPow_ok {P : InvCfg} {base : Addr} {size m : Nat} [NeZero m] (hpr : IsPrime m) (hT : InvToM m)
    (hL : InvLay P size) (hm2 : 2 < m) (hR : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hX : wordsVal s.mem base P.base P.M.n < m) (hC : InvOk P m)
    (hS : P.seed = none) :
    WP isa (InvCfg.inv P) s fun s' => KeepRegs (invClob P.M.n) s s' ∧ Unch base (invW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2) := by
  have hn := hs.nowrap
  obtain n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; have hmt := hL.mo_tbl; have hmo := hM.mo
  unfold invTbl at htbl hmt
  obtain hm2' : m % 2 = 1 := (hpr.eq_one_or_self_of_dvd 2 |>.mt (by omega_using [hm2]) |> fun h => by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega_using [hk]⟩) (by omega_using [h])
    · omega_using [hk])
  obtain hCm : P.C < m := by rw [hC.C]; exact Nat.mod_lt _ (by omega_using [hm2'])
  obtain hCnm : P.Cn < m := by rw [hC.Cn]; have := hC.Cpos; omega_using [hCm, this]
  -- The modulus, through writes to the working area.
  obtain modU : ∀ {mem' : Mem}, Unch base (batchW P) s.mem mem' → ModOkW P.M size m mem' base := fun U =>
    modOk_out hM U (fun w hw => by
      simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; unfold invTbl; dsimp only; omega_using [hmt]) hn
  rw [InvCfg.inv]
  refine WP.seq (WP.mono (init_ok hL hs hM hC.B16 hS) fun s₁ ⟨I₁, c₁, K₁, U₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs K₁ (by decide)
  refine WP.seq (WP.mono (loop_ok hL hs₁ (modU U₁) hX hm2' (by omega_using [hm2]) hC.B1 hC.B16 (c := 1)
      (by omega_using [hm2]) (by omega_using [hm2]) I₁ c₁ (fun h => by simp [hS] at h))
    fun s₂ ⟨I₂, K₂, U₂⟩ => ?_)
  rw [Divstep.invRunC_one] at I₂
  obtain hs₂ := hs₁.of_keepRegs K₂ (by decide)
  obtain U₁₂ : Unch base (batchW P) s.mem s₂.mem := (U₁.trans U₂).mono fun w hw => by
    simp only [batchW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw ⊢; exact hw
  obtain hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  obtain ⟨rA0, rA1, -, -⟩ := Divstep.invRunS_range (N := 59) (p := m) (m := P.M.minv.toNat)
    (x := (wordsVal s.mem base P.base P.M.n : Int)) (by decide) (by exact_mod_cast hpr.one_lt) hmi P.B
  refine WP.mono (finish_ok hL hs₂ (modU U₁₂) I₂ hS rA0 rA1 hCm hCnm)
    fun t ⟨Cs, A, hA, hf1, hfm1, lt, ev, K₃, U₃⟩ => ⟨?_, ?_, lt, ?_⟩
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
  obtain ha : (A : Int) = I.a :=
    hA.trans (Divstep.norm_invRunS (by decide) (by exact_mod_cast hm2') (by exact_mod_cast hpr.one_lt) hmi P.B)
  obtain hfS : (Divstep.invRunS 59 m P.M.minv.toNat X P.B).f = I.f :=
    (Divstep.invRunS_rel (N := 59) (x := (X : Int)) (by exact_mod_cast hm2') (by omega_using [hm2]) hmi P.B).2.1
  -- The divsteps end.
  obtain done : ∀ x : Int, 0 ≤ x → x < m → (Divstep.divsteps (59 * P.B) (1, m, x)).2.2 = 0 ∧
      (Divstep.divsteps (59 * P.B) (1, m, x)).2.1.natAbs = Int.gcd m x := fun x h0 h1 => by
    obtain hodd : (m : Int) % 2 = 1 := by exact_mod_cast hm2'
    obtain hmP := hM.val ▸ wordsVal_lt s.mem base P.M.mo P.M.n
    obtain hfn : (m : Int) < 2 ^ (64 * P.M.n) := by exact_mod_cast hmP
    exact Divstep.divsteps_words hodd h0 h1.le hfn hC.bound
  -- `x ≠ 0`: `f = ±1` and `x f a 2^(5 B) ≡ 1`.
  obtain spec : X ≠ 0 → (I.f = 1 ∨ I.f = -1) ∧ (X : Int) * (I.f * I.a) * 2 ^ ((64 - 59) * P.B) ≡ 1 [ZMOD m] :=
    fun hX0 => Divstep.invRun_spec (N := 59) (B := P.B) (by decide) (by exact_mod_cast hm2')
      (by exact_mod_cast hpr.one_lt) hmi (done X (by omega_using []) (by exact_mod_cast hX)) (by
        rw [Int.gcd_natCast_natCast]
        exact hpr.coprime_of_lt (by omega_using [hX0]) hX)
  refine hT (K := 2 ^ (5 * P.B)) (f := I.f) (a := A) (Cs := Cs) hm2 hR hX
    ?_ ?_ ?_ ev
  · intro hX0
    obtain h := (Divstep.invRun_zero (N := 59) (p := m) (m := P.M.minv.toNat) (by omega_using [hX]) P.B).2
    obtain hIa : I.a = 0 := by rw [hId, hX0, Nat.cast_zero]; exact h
    have : (A : Int) = 0 := by rw [ha, hIa]
    exact_mod_cast this
  · intro hX0
    obtain h := (spec hX0).2
    rw [ha, show (64 - 59) * P.B = 5 * P.B by omega_using []] at *
    push_cast
    exact h
  · intro hX0
    rcases (spec hX0).1 with h | h
    · rw [hf1 (hfS.trans h), hC.C, h]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]; ring_nf
    · rw [hfm1 (hfS.trans h), hC.Cn, h, Nat.cast_sub hCm.le]
      obtain hc : (P.C : Int) ≡ ((2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 : Nat) : Int) [ZMOD m] := by
        rw [hC.C]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
      obtain hm0 : (m : Int) ≡ 0 [ZMOD m] := Int.emod_self.trans (Int.zero_emod _).symm
      have := hm0.sub hc
      push_cast at this ⊢
      rw [show (-1 : Int) * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3) =
        0 - 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 by ring]
      exact this


/-- The registers the seeded start writes. -/
theorem initSRegs_sub {n : Nat} (h4 : 4 ≤ n) (h7 : n < 10) :
    ∀ r ∈ [Reg.rax, .rbx, .r8, .r14, .r15], r ∈ invClob n := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega_using [h4, h7]
  all_goals decide

/-- A shared inversion's `[acc] = [base]^(m - 2)` in Montgomery form, for a prime `m > 2`: `b`
starts at the seed `c ≡ 2^(5 B) R²`, so that `a` ends as `c` times the
inversion's from `b = 1` (`Divstep.invRunC_rel`), which is the result up to
the sign of `f`. -/
theorem invPowS_ok {P : InvCfg} {base : Addr} {size m : Nat} [NeZero m] (hpr : IsPrime m) (hT : InvToM m)
    (hL : InvLay P size) (hm2 : 2 < m) (hR : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hX : wordsVal s.mem base P.base P.M.n < m) (hC : InvOk P m)
    {sd md : Nat} (hS : P.seed = some (sd, md)) (hSd : SeedOk P size m s.mem base) :
    WP isa (InvCfg.inv P) s fun s' => KeepRegs (invClob P.M.n) s s' ∧ Unch base (invW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2) := by
  simp only [SeedOk, hS] at hSd
  obtain ⟨hsd, hmd, hst, hseed, hminv⟩ := hSd
  have hn := hs.nowrap
  obtain n4 := hL.n4; have n7 := hL.n10; have htbl := hL.tbl; have hmt := hL.mo_tbl; have hmo := hM.mo
  unfold invTbl at htbl hmt
  obtain hm2' : m % 2 = 1 := (hpr.eq_one_or_self_of_dvd 2 |>.mt (by omega_using [hm2]) |> fun h => by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega_using [hk]⟩) (by omega_using [h])
    · omega_using [hk])
  obtain modU : ∀ {mem' : Mem}, Unch base (batchW P) s.mem mem' → ModOkW P.M size m mem' base := fun U =>
    modOk_out hM U (fun w hw => by
      simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; unfold invTbl; dsimp only; omega_using [hmt]) hn
  obtain hcm : wordsVal s.mem base sd P.M.n < m := by rw [hseed]; exact Nat.mod_lt _ (by omega_using [hm2])
  rw [InvCfg.inv]
  refine WP.seq (WP.mono (initS_ok hL hs hM hC.B16 hS hsd hst hmd) fun s₁ ⟨I₁, c₁, r₁, K₁, U₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs K₁ (by decide)
  refine WP.seq (WP.mono (loop_ok hL hs₁ (modU U₁) hX hm2' (by omega_using [hm2]) hC.B1 hC.B16
      (c := (wordsVal s.mem base sd P.M.n : Int)) (by omega_using [hm2]) (by omega_using [hcm]) I₁ c₁
      (fun _ => by rw [r₁, hminv]))
    fun s₂ ⟨I₂, K₂, U₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs K₂ (by decide)
  obtain U₁₂ : Unch base (batchW P) s.mem s₂.mem := (U₁.trans U₂).mono fun w hw => by
    simp only [batchW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw ⊢; exact hw
  obtain hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  set X := wordsVal s.mem base P.base P.M.n with hXd
  set c := wordsVal s.mem base sd P.M.n with hcd
  obtain ⟨-, rf, -, ra, -⟩ := Divstep.invRunC_rel (N := 59) (x := (X : Int)) (c := (c : Int))
    (by exact_mod_cast hm2') (by omega_using [hm2]) hmi P.B
  obtain ⟨ra0, ra1, -, -⟩ := Divstep.invRunC_range (N := 59) (x := (X : Int)) (c := (c : Int)) (by decide)
    (by exact_mod_cast hpr.one_lt) hmi (by omega_using [hm2]) (by omega_using [hcm]) P.B
  obtain ⟨-, -, bf, -, ba0, -, -, -⟩ := Divstep.invRun_bounds (N := 59) (by decide) (p := m)
    (m := P.M.minv.toNat) (x := X) (by exact_mod_cast hm2') (by exact_mod_cast hpr.one_lt) hmi
    (by omega_using []) (by exact_mod_cast hX) P.B
  obtain hmP : m < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain hmPi : (m : Int) < ((2 ^ (64 * P.M.n) : Nat) : Int) := by exact_mod_cast hmP
  obtain ⟨f0, f1⟩ := abs_le.mp bf
  refine WP.mono (finishS_ok hL hs₂ (modU U₁₂) I₂ hS ra0 ra1 (by rw [rf]; omega_using [f0, hmPi])
      (by rw [rf]; omega_using [f1, hmPi]))
    fun t ⟨A, hA, hacc, K₃, U₃⟩ => ⟨?_, ?_, ?_⟩
  · have hsub := invClob_sub n4 n7
    exact ((K₁.mono (initSRegs_sub n4 n7)).trans (K₂.mono hsub)).trans
      (K₃.mono fun r h => List.mem_cons_of_mem _ h)
  · intro x hx
    rw [U₃ x hx, U₁₂ x fun w hw => by
      simp only [batchW, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      exact hx (P.tbl, invTbl P.M.n) (by simp [invW])]
  -- The arithmetic.
  rw [rf] at hacc
  set I := Divstep.invRun 59 m P.M.minv.toNat X P.B with hId
  obtain ⟨A0, hA0⟩ : ∃ A0 : Nat, (A0 : Int) = I.a := ⟨I.a.toNat, Int.toNat_of_nonneg ba0⟩
  obtain hAc : (A : Int) ≡ c * A0 [ZMOD m] := by rw [hA, hA0]; exact Divstep.norm_cong.trans ra
  obtain hAm : A < m := by
    obtain ⟨-, h⟩ := Divstep.norm_range ra0 ra1
    rw [← hA] at h; exact_mod_cast h
  obtain hc : (c : Int) ≡ 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 2 [ZMOD m] := by
    rw [hseed, InvCfg.seedOf]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
  obtain hm0 : (m : Int) ≡ 0 [ZMOD m] := Int.emod_self.trans (Int.zero_emod _).symm
  -- The divsteps end.
  obtain done : ∀ x : Int, 0 ≤ x → x < m → (Divstep.divsteps (59 * P.B) (1, m, x)).2.2 = 0 ∧
      (Divstep.divsteps (59 * P.B) (1, m, x)).2.1.natAbs = Int.gcd m x := fun x h0 h1 => by
    obtain hodd : (m : Int) % 2 = 1 := by exact_mod_cast hm2'
    obtain hfn : (m : Int) < 2 ^ (64 * P.M.n) := by exact_mod_cast hmP
    exact Divstep.divsteps_words hodd h0 h1.le hfn hC.bound
  obtain spec : X ≠ 0 → (I.f = 1 ∨ I.f = -1) ∧ (X : Int) * (I.f * A0) * 2 ^ (5 * P.B) ≡ 1 [ZMOD m] :=
    fun hX0 => by
      obtain h := Divstep.invRun_spec (N := 59) (B := P.B) (by decide) (by exact_mod_cast hm2')
        (by exact_mod_cast hpr.one_lt) hmi (done X (by omega_using []) (by exact_mod_cast hX)) (by
          rw [Int.gcd_natCast_natCast]
          exact hpr.coprime_of_lt (by omega_using [hX0]) hX)
      rw [show (64 - 59) * P.B = 5 * P.B by omega_using [], ← hA0] at h
      exact h
  -- The constant the result is multiplied by.
  set Cs : Nat := ((I.f * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3)) % m).toNat with hCsd
  obtain hCs : (Cs : Int) ≡ I.f * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3) [ZMOD m] := by
    rw [hCsd, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega_using [hm2]))]; exact Int.mod_modEq _ _
  -- `acc` and its congruence.
  obtain key : wordsVal t.mem base P.acc P.M.n < m ∧
      wordsVal t.mem base P.acc P.M.n * 2 ^ (64 * P.M.n) % m = A0 * Cs % m := by
    by_cases hX0 : X = 0
    · obtain hIa : I.a = 0 := by
        rw [hId, hX0, Nat.cast_zero]; exact (Divstep.invRun_zero (by omega_using [hm2]) P.B).2
      obtain hIf : I.f = m := by
        rw [hId, hX0, Nat.cast_zero]; exact Divstep.invRun_f_zero (by exact_mod_cast hm2') P.B
      obtain e0 : A0 = 0 := by omega_using [hA0, hIa]
      rw [e0, Nat.cast_zero, Int.mul_zero] at hAc
      obtain eA : A = 0 := by
        have hz : (A : Int) % m = 0 % m := hAc
        obtain hAm' : (A : Int) < m := by exact_mod_cast hAm
        rw [Int.zero_emod, Int.emod_eq_of_lt (Int.natCast_nonneg _) hAm'] at hz
        exact_mod_cast hz
      rw [hacc, hIf, eA, e0]
      simp only [show ¬ ((m : Int) < 0) by omega_using [], ↓reduceIte, Nat.zero_mul, Nat.zero_mod]
      exact ⟨by omega_using [hm2], by simp⟩
    · obtain ⟨hf, hsp⟩ := spec hX0
      -- `A ≠ 0`, else `m ∣ R²`.
      obtain hA0' : A ≠ 0 := fun h => by
        rw [h, Nat.cast_zero] at hAc
        obtain e : ((2 : Int) ^ (64 * P.M.n)) ^ 2 ≡ 0 [ZMOD m] :=
          calc ((2 : Int) ^ (64 * P.M.n)) ^ 2 = (2 ^ (64 * P.M.n)) ^ 2 * 1 := by ring
            _ ≡ (2 ^ (64 * P.M.n)) ^ 2 * ((X : Int) * (I.f * A0) * 2 ^ (5 * P.B)) [ZMOD m] :=
              hsp.symm.mul_left _
            _ = X * I.f * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 2 * A0) := by ring
            _ ≡ X * I.f * (c * A0) [ZMOD m] := ((hc.mul_right _).symm.mul_left _)
            _ ≡ X * I.f * 0 [ZMOD m] := hAc.symm.mul_left _
            _ = 0 := by ring
        obtain hd : ((m : Nat) : Int) ∣ (((2 ^ (64 * P.M.n)) ^ 2 : Nat) : Int) := by
          push_cast; exact (Int.modEq_zero_iff_dvd).mp e
        obtain hd2 := hpr.dvd_of_dvd_pow (hpr.dvd_of_dvd_pow (Int.natCast_dvd_natCast.mp hd))
        obtain hle := Nat.le_of_dvd (by decide) hd2
        omega_using [hm2, hle]
      obtain base₁ : (A : Int) * 2 ^ (64 * P.M.n) ≡
          2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 * A0 [ZMOD m] :=
        calc (A : Int) * 2 ^ (64 * P.M.n) ≡ c * A0 * 2 ^ (64 * P.M.n) [ZMOD m] := hAc.mul_right _
          _ ≡ 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 2 * A0 * 2 ^ (64 * P.M.n) [ZMOD m] :=
            (hc.mul_right _).mul_right _
          _ = 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 * A0 := by ring
      rcases hf with hf | hf
      · rw [hacc, hf]
        simp only [show ¬ ((1 : Int) < 0) by decide, ↓reduceIte]
        refine ⟨hAm, ?_⟩
        obtain h : ((A * 2 ^ (64 * P.M.n) : Nat) : Int) ≡ ((A0 * Cs : Nat) : Int) [ZMOD m] := by
          push_cast
          refine base₁.trans ?_
          rw [hf] at hCs
          refine (Int.ModEq.trans ?_ (hCs.symm.mul_left _))
          rw [show (2 : Int) ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 * A0 =
            A0 * (1 * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3)) by ring]
        exact Int.natCast_modEq_iff.mp h
      · rw [hacc, hf]
        simp only [show ((-1 : Int) < 0) by decide, ↓reduceIte]
        refine ⟨by omega_using [hA0', hAm], ?_⟩
        obtain h : (((m - A) * 2 ^ (64 * P.M.n) : Nat) : Int) ≡ ((A0 * Cs : Nat) : Int) [ZMOD m] := by
          rw [Nat.cast_mul, Nat.cast_sub hAm.le]
          push_cast
          refine ((hm0.sub_right _).mul_right _).trans ?_
          rw [show ((0 : Int) - A) * 2 ^ (64 * P.M.n) = -((A : Int) * 2 ^ (64 * P.M.n)) by ring]
          refine base₁.neg.trans ?_
          rw [hf] at hCs
          refine (Int.ModEq.trans ?_ (hCs.symm.mul_left _))
          rw [show -((2 : Int) ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 * A0) =
            A0 * (-1 * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3)) by ring]
        exact Int.natCast_modEq_iff.mp h
  refine ⟨key.1, hT (K := 2 ^ (5 * P.B)) (f := I.f) (a := A0) (Cs := Cs) hm2 hR hX ?_ ?_ ?_ key.2⟩
  · intro hX0
    obtain h := (Divstep.invRun_zero (N := 59) (p := m) (m := P.M.minv.toNat) (by omega_using [hX]) P.B).2
    obtain hIa : I.a = 0 := by rw [hId, hX0, Nat.cast_zero]; exact h
    omega_using [hA0, hIa]
  · intro hX0
    obtain h := (spec hX0).2
    push_cast
    exact h
  · intro _
    push_cast
    exact hCs

/-- A prime modulus's inversion is sound. -/
theorem invSound_of_toM {m : Nat} [NeZero m] (hp : IsPrime m) (hT : InvToM m) : InvSound m := by
  intro P _ _ hL hm2 hR _ hs hM hX hC hSd
  cases hS : P.seed with
  | none => exact invPow_ok hp hT hL hm2 hR hs hM hX hC hS
  | some sm => exact invPowS_ok hp hT hL hm2 hR hs hM hX hC (sd := sm.1) (md := sm.2) hS hSd

end VG.Proof.Weierstrass.X86_64
