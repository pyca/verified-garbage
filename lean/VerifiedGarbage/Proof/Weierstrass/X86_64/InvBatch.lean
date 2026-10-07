import VerifiedGarbage.Proof.Weierstrass.X86_64.InvRed
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvPacked
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Inversion by divsteps on x86-64: a batch

The signed linear combinations of a batch as integers modulo the words'
range (`linM_ok`), the shift by 59 of a multiple of `2^59` (`shrM_ok`), and a
batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` updated by
their matrix, as `Divstep.batch` (`batch_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- `[T] = u [x] + v [y]` modulo `2^(64 K)`, for words `u`, `v` (signed) in `w`, `w'`. -/
theorem linM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {T x y U k K : Nat} (hkK : k ≤ K) (hK : 2 ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hy : y + 8 * k ≤ size) (hT : T + 8 * K ≤ size) (hU : U + 8 * (K - 1) ≤ size)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T)
    (hUT : U + 8 * (K - 1) ≤ T ∨ T + 8 * K ≤ U) (hUx : U + 8 * (K - 1) ≤ x ∨ x + 8 * k ≤ U)
    (hUy : U + 8 * (K - 1) ≤ y ∨ y + 8 * k ≤ U) :
    WP isa (.block (lin w w' T x y U k K)) s fun t =>
      (wordsVal t.mem base T K : Int) % ((2 ^ (64 * K) : Nat) : Int) =
        ((s.gpr w).toInt * wordsVal s.mem base x k + (s.gpr w').toInt * wordsVal s.mem base y k) %
          ((2 ^ (64 * K) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧ Unch base [(T, 8 * K), (U, 8 * (K - 1))] s.mem t.mem := by
  refine WP.mono (lin_ok hs hw hw' hkK hK hk' hx hy hT hU hTx hTy hUT hUx hUy) fun t ⟨e, kt, O⟩ => ⟨?_, kt, O⟩
  rw [masked_smask, masked_smask] at e
  have e' := congrArg (Nat.cast : Nat → Int) e
  push_cast at e'
  rw [← Divstep.toInt_sgn, ← Divstep.toInt_sgn]
  refine Divstep.lin_words (X' := wordsVal s.mem base x (K - 1)) (Y' := wordsVal s.mem base y (K - 1)) ?_ ?_ ?_
  · have := shifted_cong s.mem base x (k := k) (K := K) (by omega) (by omega); push_cast at this; exact this
  · have := shifted_cong s.mem base y (k := k) (K := K) (by omega) (by omega); push_cast at this; exact this
  · push_cast; convert e' using 3

/-- `[dst] = y / 2^59` modulo `2^(64 L)`, for `[src] ≡ y` with `|y| < 2^(64 L - 1)`
a multiple of `2^59`. -/
theorem shrM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat} (hL : 1 ≤ L)
    (hsrc : src + 8 * L ≤ size) (hdst : dst + 8 * L ≤ size) (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) {y z : Int}
    (hy : (wordsVal s.mem base src L : Int) % ((2 ^ (64 * L) : Nat) : Int) = y % ((2 ^ (64 * L) : Nat) : Int))
    (hy1 : -((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int) ≤ y) (hy2 : y < ((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int))
    (hz : y = 2 ^ 59 * z) :
    WP isa (.block (shr59 dst src L)) s fun t =>
      (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) = z % ((2 ^ (64 * L) : Nat) : Int) ∧
      KeepRegs [.rax, .rdx, .r8] s t ∧ Outside base dst (8 * L) s.mem t.mem := by
  refine WP.mono (shr59_ok hs hL hsrc hdst hsep) fun t ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hy1 hy2 ⊢
  have hQ : 2 ^ (64 * (j + 1)) = 2 * (2 ^ (64 * j) * 2 ^ 63) := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ring
  rw [sext, Nat.add_sub_cancel, sgnW_top, hQ] at e
  rw [hQ] at hy ⊢
  exact Divstep.shr_nat (c := 2 ^ 59) (B := 2 ^ 64) rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := wordsVal_lt s.mem base src (j + 1); rw [hQ] at this; exact this) hy hy1 hy2 hz e

theorem modOk_out {M : Mod} {size p : Nat} {mem mem' : Mem} {base : Addr} (hM : ModOkW M size p mem base)
    {W : List (Nat × Nat)} (hU : Unch base W mem mem') (hsep : ∀ w ∈ W, M.mo + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ M.mo)
    (hn : base.toNat + size ≤ 2 ^ 64) : ModOkW M size p mem' base :=
  ⟨hM.n0, hM.mo, hM.tmp, hM.sep, by rw [hU.wordsVal hsep (by have := hM.mo; omega)]; exact hM.val,
    hM.inv, hM.red⟩

/-- Apart from each range of a list written out. -/
local macro "apart" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
  forall_eq_or_imp, forall_eq] <;> omega))

/-- Half a batch's update of `f`, `g`: `[dst] = (u f + v g) / 2^59` (`L` words, signed). -/
theorem fHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y U dst L : Nat} (hL : 2 ≤ L) (hx : x + 8 * L ≤ size) (hy : y + 8 * L ≤ size) (hT : T + 8 * L ≤ size)
    (hU : U + 8 * (L - 1) ≤ size) (hd : dst + 8 * L ≤ size)
    (hTx : T + 8 * L ≤ x ∨ x + 8 * L ≤ T) (hTy : T + 8 * L ≤ y ∨ y + 8 * L ≤ T)
    (hUT : U + 8 * (L - 1) ≤ T ∨ T + 8 * L ≤ U) (hUx : U + 8 * (L - 1) ≤ x ∨ x + 8 * L ≤ U)
    (hUy : U + 8 * (L - 1) ≤ y ∨ y + 8 * L ≤ U) (hdT : dst + 8 * L ≤ T ∨ T + 8 * L ≤ dst) {p : Nat} {f g : Int}
    (hf : (wordsVal s.mem base x L : Int) % ((2 ^ (64 * L) : Nat) : Int) = f % ((2 ^ (64 * L) : Nat) : Int))
    (hg : (wordsVal s.mem base y L : Int) % ((2 ^ (64 * L) : Nat) : Int) = g % ((2 ^ (64 * L) : Nat) : Int))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (64 * (L - 1))) (hdiv : 2 ^ 59 ∣ u * f + v * g) :
    WP isa (.block (lin w w' T x y U L L ++ shr59 dst T L)) s fun t =>
      (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(T, 8 * L), (U, 8 * (L - 1)), (dst, 8 * L)] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (linM_ok hs hw hw' (k := L) (K := L) (Nat.le_refl _) hL (by omega) hx hy hT hU hTx hTy hUT hUx hUy)
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), Divstep.cong_comb hf hg] at e₁
  obtain ⟨b1, b2⟩ := Divstep.comb_range (A := 2 ^ (64 * (L - 1))) huv hfb hgb hp
  refine WP.mono (shrM_ok hs₁ (dst := dst) (src := T) (by omega) hT hd hdT e₁ b1 b2 (Int.mul_ediv_cancel' hdiv).symm)
    fun t ⟨e, k, O⟩ => ⟨e, k₁.trans (k.mono (by decide)), (O₁.trans O.unch).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]⟩

/-- Half a batch's update of `a`, `b`: `[dst] = mred (u a + v b)` (`n` words). -/
theorem abHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkW M size p s.mem base) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y U dst : Nat} (hx : x + 8 * M.n ≤ size) (hy : y + 8 * M.n ≤ size) (hT : T + 8 * (M.n + 2) ≤ size)
    (hU : U + 8 * (M.n + 1) ≤ size) (hd : dst + 8 * M.n ≤ size)
    (hTx : T + 8 * (M.n + 2) ≤ x ∨ x + 8 * M.n ≤ T) (hTy : T + 8 * (M.n + 2) ≤ y ∨ y + 8 * M.n ≤ T)
    (hUT : U + 8 * (M.n + 1) ≤ T ∨ T + 8 * (M.n + 2) ≤ U) (hUx : U + 8 * (M.n + 1) ≤ x ∨ x + 8 * M.n ≤ U)
    (hUy : U + 8 * (M.n + 1) ≤ y ∨ y + 8 * M.n ≤ U) (hdT : dst + 8 * M.n ≤ T ∨ T + 8 * (M.n + 2) ≤ dst)
    (hTm : T + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ T) (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    {a b : Int} (ha : (wordsVal s.mem base x M.n : Int) = a) (hb : (wordsVal s.mem base y M.n : Int) = b)
    (ha0 : |a| ≤ p) (hb0 : |b| ≤ p) :
    WP isa (.block (lin w w' T x y U M.n (M.n + 1) ++ mredC M dst T U)) s fun t =>
      (wordsVal t.mem base dst M.n : Int) = Divstep.mred p M.minv.toNat (u * a + v * b) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(T, 8 * (M.n + 2)), (U, 8 * (M.n + 1)), (dst, 8 * M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  have hn0 := hM.n0
  rw [WP.block_append_iff]
  refine WP.mono (linM_ok hs hw hw' (k := M.n) (K := M.n + 1) (by omega) (by omega) (by omega) hx hy (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), ha, hb] at e₁
  have hM₁ := modOk_out hM O₁ (by have := hM.mo; apart) hn
  have hT' : |u * a + v * b| ≤ 2 ^ 63 * (p : Int) := by
    have := Divstep.comb_le huv ha0 hb0
    have hp : (0 : Int) ≤ p := Int.natCast_nonneg _
    nlinarith
  have O₁' : Unch base [(T, 8 * (M.n + 2)), (U, 8 * (M.n + 1))] s.mem s₁.mem := fun z hz => O₁ z (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz ⊢; omega)
  refine WP.mono (mredC_ok hs₁ hM₁ hT hd hU hTm hdT (by omega) hUm hT' e₁) fun t ⟨e, k, O⟩ =>
    ⟨e, k₁.trans k, (O₁'.trans O).mono fun w hw => ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with h | h | h | h | h <;> simp [h]

/-! ## A batch -/

/-- The slots, from the working area. -/
theorem slots (P : InvCfg) :
    P.L = P.M.n + 1 ∧ P.sF = P.tbl ∧ P.sG = P.tbl + 8 * P.M.n + 8 ∧ P.sA = P.tbl + 16 * P.M.n + 16 ∧
      P.sB = P.tbl + 24 * P.M.n + 16 ∧ P.sNF = P.tbl + 32 * P.M.n + 16 ∧ P.sNG = P.tbl + 40 * P.M.n + 24 ∧
      P.sT = P.tbl + 48 * P.M.n + 32 ∧ P.sU = P.tbl + 56 * P.M.n + 48 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [InvCfg.L, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sNG, InvCfg.sT, InvCfg.sU] <;>
    omega

set_option hygiene false in
/-- The slots' arithmetic, from `slots` and the layout (named `eL` … `eU`, `n4`, `htbl`, `hn`). -/
local macro "slot_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, n4, htbl, hn])

/-- What a batch writes: the working area. -/
def batchW (P : InvCfg) : List (Nat × Nat) := [(P.tbl, invTbl P.M.n)]

/-- The registers the divsteps and the updates write. -/
abbrev wordRegs : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13]

/-- The registers a batch writes: those and the count in `r14`. -/
abbrev batchRegs : List Reg := .r14 :: wordRegs

/-- The batch state in memory: `d` in `rbx`, `f`, `g` (two's complement, `n + 1`
words), `a`, `b` (`n` words). -/
structure IInv (P : InvCfg) (base : Addr) (I : Divstep.IState) (s : State) : Prop where
  d : s.gpr .rbx = BitVec.ofInt 64 I.d
  f : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.f % ((2 ^ (64 * P.L) : Nat) : Int)
  g : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = I.g % ((2 ^ (64 * P.L) : Nat) : Int)
  a : (wordsVal s.mem base P.sA P.M.n : Int) = I.a
  b : (wordsVal s.mem base P.sB P.M.n : Int) = I.b

theorem zext1 : (1 : BitVec 32).setWidth 64 = 1 := by decide

/-- `[d] = [a]`, through `rax`. -/
theorem copy1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d a : Nat} (hd : d + 8 ≤ size)
    (ha : a + 8 ≤ size) :
    WP isa (.block (copy 1 d a)) s fun t =>
      t.mem = s.mem.writeW (off base d) (word s.mem base a) ∧ KeepRegs [.rax] s t := by
  rw [copy, copy, List.append_nil, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax ha) fun s₁ ⟨c₁, _, k₁⟩ => ?_
  refine WP.mono (storeReg_ok (hs.of_keeps k₁ (by decide)) .rax hd) fun t ⟨m, _, _, k⟩ =>
    ⟨by rw [m, c₁, k₁.2.1], (Keeps.regs k₁).trans (k.mono (by simp))⟩

theorem xor_m1 (x : BitVec 64) : x ^^^ (-1 : BitVec 32).signExtend 64 = ~~~x := by
  rw [show (-1 : BitVec 32).signExtend 64 = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]

/-- `rbx = ~rbx`. -/
theorem notRbx_ok (s : State) :
    WP isa (.block [.alu .xor .rbx (.imm (-1))]) s fun t => t.gpr .rbx = ~~~s.gpr .rbx ∧ Keeps [.rbx] s t := by
  irun [xor_m1]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ↓reduceIte]

/-- A batch's start: the low words of `f`, `g` at `[sT]`, `[sT + 8]`, and `~d`. -/
theorem batchStart_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hF : P.sF + 8 ≤ size) (hG : P.sG + 8 ≤ size) (hT : P.sT + 16 ≤ size) (hGT : P.sG + 8 ≤ P.sT) :
    WP isa (.block P.batchStart) s fun t =>
      word t.mem base P.sT = word s.mem base P.sF ∧ word t.mem base (P.sT + 8) = word s.mem base P.sG ∧
      t.gpr .rbx = ~~~s.gpr .rbx ∧ KeepRegs [.rax, .rbx] s t ∧ Outside base P.sT 16 s.mem t.mem := by
  have hn := hs.nowrap
  rw [InvCfg.batchStart, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy1_ok hs (d := P.sT) (a := P.sF) (by omega) hF) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copy1_ok hs₁ (d := P.sT + 8) (a := P.sG) (by omega) hG) fun s₂ ⟨m₂, k₂⟩ => ?_
  refine WP.mono (notRbx_ok s₂) fun t ⟨b, k⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [k.2.1, m₂, word_apart _ _ _ (by omega) (by omega) (by omega), m₁, word_writeW_self]
  · rw [k.2.1, m₂, word_writeW_self, m₁, word_apart _ _ _ (by omega) (by omega) (by omega)]
  · rw [b, k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · exact ((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans ((Keeps.regs k).mono (by simp))
  · rw [k.2.1, m₂, m₁]
    exact ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))

/-- The low word of numbers of `L` words congruent modulo `2^(64 L)`. -/
theorem low_cong {P : InvCfg} {m : Mem} {base : Addr} {d : Nat} {x : Int}
    (h : (wordsVal m base d P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = x % ((2 ^ (64 * P.L) : Nat) : Int)) :
    ((word m base d).toNat : Int) % 2 ^ 64 = x % 2 ^ 64 := by
  have hdvd : ((2 : Int) ^ 64) ∣ ((2 ^ (64 * P.L) : Nat) : Int) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_dvd_pow 2 (by unfold InvCfg.L; omega)
  have low : ((word m base d).toNat : Int) % 2 ^ 64 = (wordsVal m base d P.L : Int) % 2 ^ 64 := by
    unfold InvCfg.L; rw [wordsVal]; push_cast; rw [Int.add_mul_emod_self_left]
  rw [low, ← Int.emod_emod_of_dvd _ hdvd, h, Int.emod_emod_of_dvd _ hdvd]

theorem msteps_d15 {T : Divstep.MSt} {k : Nat} (h : |T.d| + 2 * k ≤ 2 ^ 31) :
    |(Divstep.msteps 15 T).d| + 2 * k ≤ 2 ^ 31 + 30 := by
  have := Divstep.msteps_d T 15; push_cast at this; linarith

/-- A batch's words: `59` divsteps from the low words of `f`, `g`, in chunks,
leave `d` and the matrix in `rbx`, `r9`–`r12`. -/
theorem words_ok {P : InvCfg} {base : Addr} {size : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    {I : Divstep.IState} (hI : IInv P base I s) (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1) :
    WP isa (.block P.words) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).d ∧
      t.gpr .r9 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u ∧
      t.gpr .r10 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v ∧
      t.gpr .r11 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q ∧
      t.gpr .r12 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r ∧
      Outside base P.sT 24 s.mem t.mem ∧ KeepRegs wordRegs s t := by
  obtain ⟨eL, eF, eG, -, -, -, -, eT, -⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  have hn := hs.nowrap
  set T0 := Divstep.MSt.init I.d I.f I.g with hT0
  have f0 : T0.f % 2 = 1 := hf1
  have odd : ∀ k, (Divstep.msteps k T0).f % 2 = 1 := Divstep.msteps_f_odd f0
  have dd : ∀ k, |(Divstep.msteps k T0).d| ≤ 2 ^ 30 + 2 * k := fun k => by
    have := Divstep.msteps_d T0 k
    rw [show T0.d = I.d from rfl] at this
    linarith
  have hT : P.sT + 24 ≤ size := by omega
  rw [InvCfg.words]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (batchStart_ok hs (by omega) (by omega) (by omega) (by omega))
    fun s₁ ⟨wf₁, wg₁, b₁, k₁, o₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have c₁ : ChunkAt base P.sT 64 true T0 s₁ :=
    ⟨by rw [b₁, hI.d]; rfl, by rw [wf₁]; exact low_cong hI.f, by rw [wg₁]; exact low_cong hI.g,
      fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => absurd h (by decide)⟩
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₁ (n := 15) (K := 64) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT f0 (by rw [show T0.d = I.d from rfl]; push_cast; linarith) c₁)
    fun s₂ ⟨d₂, u₂, v₂, q₂, r₂, w₂, k₂, o₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain ⟨f₂, g₂⟩ := w₂ rfl
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₂ (n := 15) (K := 49) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 15) (by have := dd 15; norm_num at this ⊢; linarith)
    ⟨d₂, f₂, g₂, fun h => absurd h (by decide), fun _ => ⟨u₂, v₂, q₂, r₂⟩⟩)
    fun s₃ ⟨d₃, u₃, v₃, q₃, r₃, w₃, k₃, o₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain ⟨f₃, g₃⟩ := w₃ rfl
  rw [← Divstep.msteps_add] at d₃ u₃ v₃ q₃ r₃ f₃ g₃
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₃ (n := 15) (K := 34) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 30) (by have := dd 30; norm_num at this ⊢; linarith)
    ⟨d₃, f₃, g₃, fun h => absurd h (by decide), fun _ => ⟨u₃, v₃, q₃, r₃⟩⟩)
    fun s₄ ⟨d₄, u₄, v₄, q₄, r₄, w₄, k₄, o₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain ⟨f₄, g₄⟩ := w₄ rfl
  rw [← Divstep.msteps_add] at d₄ u₄ v₄ q₄ r₄ f₄ g₄
  rw [WP.block_append_iff]
  refine WP.mono (pchunk_ok hs₄ (n := 14) (K := 19) (first := false) (last := true) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 45) (by have := dd 45; norm_num at this ⊢; linarith)
    ⟨d₄, f₄, g₄, fun h => absurd h (by decide), fun _ => ⟨u₄, v₄, q₄, r₄⟩⟩)
    fun s₅ ⟨d₅, u₅, v₅, q₅, r₅, _, k₅, o₅⟩ => ?_
  rw [← Divstep.msteps_add] at d₅ u₅ v₅ q₅ r₅
  refine WP.mono (notRbx_ok s₅) fun t ⟨b, k⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b, d₅, BitVec.not_not]
  · rw [k.1 _ (by decide), u₅]
  · rw [k.1 _ (by decide), v₅]
  · rw [k.1 _ (by decide), q₅]
  · rw [k.1 _ (by decide), r₅]
  · rw [k.2.1]
    exact ((((o₁.mono (by omega) (by omega)).trans o₂).trans o₃).trans o₄).trans o₅
  · exact ((((k₁.mono (by decide)).trans k₂).trans k₃).trans k₄).trans k₅ |>.trans ((Keeps.regs k).mono (by decide))

set_option hygiene false in
/-- Each range of a list written out in one of another's, by `slot_omega`. -/
local macro "cover_omega" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, exists_eq_or_imp, exists_eq_left] <;> slot_omega))

/-- Both halves of the update of `f`, `g` into `f'`, `g'`. -/
abbrev fgHalves (P : InvCfg) : List Instr :=
  (lin .r9 .r10 P.sT P.sF P.sG P.sU P.L P.L ++ shr59 P.sNF P.sT P.L) ++
  (lin .r11 .r12 P.sT P.sF P.sG P.sU P.L P.L ++ shr59 P.sNG P.sT P.L)

/-- The update of `f`, `g`. -/
abbrev fgCode (P : InvCfg) : List Instr :=
  fgHalves P ++ (copy P.L P.sF P.sNF ++ copy P.L P.sG P.sNG)

/-- `f' = (u f + v g) / 2^59`, `g' = (q f + r g) / 2^59`, by the matrix in `r9`–`r12`. -/
theorem fgHalves_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State}
    (hs : Scr s base size) (hp : p < 2 ^ (64 * P.M.n)) {u v q r f g : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hF : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = f % ((2 ^ (64 * P.L) : Nat) : Int))
    (hG : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = g % ((2 ^ (64 * P.L) : Nat) : Int))
    (hf : |f| ≤ p) (hg : |g| ≤ p) (hdf : 2 ^ 59 ∣ u * f + v * g) (hdg : 2 ^ 59 ∣ q * f + r * g) :
    WP isa (.block (fgHalves P)) s fun t =>
      (wordsVal t.mem base P.sNF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sNG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((q * f + r * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sNF, 32 * P.M.n + 40)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  have hp' : p < 2 ^ (64 * (P.L - 1)) := by rw [eL, Nat.add_sub_cancel]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (fHalf_ok hs (w := .r9) (w' := .r10) (by decide) (by decide) h9 h10 huv
    (T := P.sT) (x := P.sF) (y := P.sG) (U := P.sU) (dst := P.sNF) (L := P.L) (by slot_omega) (by slot_omega)
    (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega)
    (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega) hF hG hf hg hp' hdf) fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁' : Unch base [(P.sNF, 32 * P.M.n + 40)] s.mem s₁.mem := Unch.cover U₁ (by cover_omega)
  have rF : wordsVal s₁.mem base P.sF P.L = wordsVal s.mem base P.sF P.L :=
    U₁'.wordsVal (by cover_omega) (by slot_omega)
  have rG : wordsVal s₁.mem base P.sG P.L = wordsVal s.mem base P.sG P.L :=
    U₁'.wordsVal (by cover_omega) (by slot_omega)
  refine WP.mono (fHalf_ok hs₁ (w := .r11) (w' := .r12) (by decide) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact h11) (by rw [k₁.gpr _ (by decide)]; exact h12) hqr
    (T := P.sT) (x := P.sF) (y := P.sG) (U := P.sU) (dst := P.sNG) (L := P.L) (by slot_omega) (by slot_omega)
    (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega)
    (by slot_omega) (by slot_omega) (by slot_omega) (by slot_omega)
    (by rw [rF]; exact hF) (by rw [rG]; exact hG) hf hg hp' hdg) fun t ⟨e₂, k₂, U₂⟩ => ⟨?_, e₂, k₁.trans k₂,
      Unch.cover (U₁'.trans U₂) (by cover_omega)⟩
  rw [U₂.wordsVal (by cover_omega) (by slot_omega)]; exact e₁

/-- A batch's update of `f`, `g`, by the matrix in `r9`–`r12`. -/
theorem fgUpd_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hp : p < 2 ^ (64 * P.M.n)) {u v q r f g : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hF : (wordsVal s.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = f % ((2 ^ (64 * P.L) : Nat) : Int))
    (hG : (wordsVal s.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) = g % ((2 ^ (64 * P.L) : Nat) : Int))
    (hf : |f| ≤ p) (hg : |g| ≤ p) (hdf : 2 ^ 59 ∣ u * f + v * g) (hdg : 2 ^ 59 ∣ q * f + r * g) :
    WP isa (.block (fgCode P)) s fun t =>
      (wordsVal t.mem base P.sF P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      (wordsVal t.mem base P.sG P.L : Int) % ((2 ^ (64 * P.L) : Nat) : Int) =
        ((q * f + r * g) / 2 ^ 59) % ((2 ^ (64 * P.L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sF, 16 * P.M.n + 16), (P.sNF, 32 * P.M.n + 40)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [WP.block_append_iff]
  refine WP.mono (fgHalves_ok hL hs hp h9 h10 h11 h12 huv hqr hF hG hf hg hdf hdg) fun s₂ ⟨e₁, e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok P.L hs₂ (o := P.sF) (a := P.sNF) (by slot_omega) (by slot_omega) (by slot_omega))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have rNG : wordsVal s₃.mem base P.sNG P.L = wordsVal s₂.mem base P.sNG P.L :=
    O₃.wordsVal (by slot_omega) (by slot_omega)
  refine WP.mono (copy_ok P.L hs₃ (o := P.sG) (a := P.sNG) (by slot_omega) (by slot_omega) (by slot_omega))
    fun t ⟨e₄, k₄, O₄⟩ => ⟨?_, ?_, k₂.trans ((k₃.trans k₄).mono (by decide)), ?_⟩
  · rw [O₄.wordsVal (by slot_omega) (by slot_omega), e₃]; exact e₁
  · rw [e₄, rNG]; exact e₂
  · exact Unch.cover (U₂.trans (O₃.unch.trans O₄.unch)) (by cover_omega)

set_option hygiene false in
/-- `slot_omega` with the modulus's place (`hmt`, `hmo`). -/
local macro "slotm_omega" : tactic =>
  `(tactic| omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, eU, n4, htbl, hn, hmt, hmo])

/-- Both halves of the update of `a`, `b`, into `a'` and `b`. -/
abbrev abHalves (P : InvCfg) : List Instr :=
  (lin .r9 .r10 P.sT P.sA P.sB P.sU P.M.n P.L ++ mredC P.M P.sNF P.sT P.sU) ++
  (lin .r11 .r12 P.sT P.sA P.sB P.sU P.M.n P.L ++ mredC P.M P.sB P.sT P.sU)

/-- The update of `a`, `b`. -/
abbrev abCode (P : InvCfg) : List Instr := abHalves P ++ copy P.M.n P.sA P.sNF

/-- `a' = mred (u a + v b)`, `b = mred (q a + r b)`, by the matrix in `r9`–`r12`. -/
theorem abHalves_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State}
    (hs : Scr s base size) (hM : ModOkW P.M size p s.mem base) {u v q r a b : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hA : (wordsVal s.mem base P.sA P.M.n : Int) = a) (hB : (wordsVal s.mem base P.sB P.M.n : Int) = b)
    (ha : |a| ≤ p) (hb : |b| ≤ p) :
    WP isa (.block (abHalves P)) s fun t =>
      (wordsVal t.mem base P.sNF P.M.n : Int) = Divstep.mred p P.M.minv.toNat (u * a + v * b) ∧
      (wordsVal t.mem base P.sB P.M.n : Int) = Divstep.mred p P.M.minv.toNat (q * a + r * b) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sB, 40 * P.M.n + 40)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl; have hmt := hL.mo_tbl; unfold invTbl at hmt
  have hmo := hM.mo
  rw [WP.block_append_iff]
  refine WP.mono (abHalf_ok hs hM (w := .r9) (w' := .r10) (by decide) (by decide) h9 h10 huv
    (T := P.sT) (x := P.sA) (y := P.sB) (U := P.sU) (dst := P.sNF) (by slotm_omega) (by slotm_omega)
    (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega)
    (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega) hA hB ha hb)
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁' : Unch base [(P.sB, 40 * P.M.n + 40)] s.mem s₁.mem := Unch.cover U₁ (by cover_omega)
  have rA : wordsVal s₁.mem base P.sA P.M.n = wordsVal s.mem base P.sA P.M.n :=
    U₁'.wordsVal (by cover_omega) (by slot_omega)
  have rB : wordsVal s₁.mem base P.sB P.M.n = wordsVal s.mem base P.sB P.M.n :=
    U₁.wordsVal (by cover_omega) (by slot_omega)
  have M₁ := modOk_out hM U₁' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; slotm_omega) hn
  refine WP.mono (abHalf_ok hs₁ M₁ (w := .r11) (w' := .r12) (by decide) (by decide)
    (by rw [k₁.gpr _ (by decide)]; exact h11) (by rw [k₁.gpr _ (by decide)]; exact h12) hqr
    (T := P.sT) (x := P.sA) (y := P.sB) (U := P.sU) (dst := P.sB) (by slotm_omega) (by slotm_omega)
    (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega)
    (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega) (by slotm_omega)
    (by rw [rA]; exact hA) (by rw [rB]; exact hB) ha hb) fun t ⟨e₂, k₂, U₂⟩ =>
      ⟨?_, e₂, k₁.trans k₂, Unch.cover (U₁'.trans U₂) (by cover_omega)⟩
  rw [U₂.wordsVal (by cover_omega) (by slot_omega)]; exact e₁

/-- A batch's update of `a`, `b`, by the matrix in `r9`–`r12`. -/
theorem abUpd_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size p s.mem base) {u v q r a b : Int}
    (h9 : s.gpr .r9 = BitVec.ofInt 64 u) (h10 : s.gpr .r10 = BitVec.ofInt 64 v)
    (h11 : s.gpr .r11 = BitVec.ofInt 64 q) (h12 : s.gpr .r12 = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hA : (wordsVal s.mem base P.sA P.M.n : Int) = a) (hB : (wordsVal s.mem base P.sB P.M.n : Int) = b)
    (ha : |a| ≤ p) (hb : |b| ≤ p) :
    WP isa (.block (abCode P)) s fun t =>
      (wordsVal t.mem base P.sA P.M.n : Int) = Divstep.mred p P.M.minv.toNat (u * a + v * b) ∧
      (wordsVal t.mem base P.sB P.M.n : Int) = Divstep.mred p P.M.minv.toNat (q * a + r * b) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(P.sA, 48 * P.M.n + 40)] s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl
  rw [WP.block_append_iff]
  refine WP.mono (abHalves_ok hL hs hM h9 h10 h11 h12 huv hqr hA hB ha hb) fun s₂ ⟨e₁, e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok P.M.n hs₂ (o := P.sA) (a := P.sNF) (by slot_omega) (by slot_omega) (by slot_omega))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨by rw [e₃]; exact e₁, by rw [O₃.wordsVal (by slot_omega) (by slot_omega)]; exact e₂,
      k₂.trans (k₃.mono (by decide)), Unch.cover (U₂.trans O₃.unch) (by cover_omega)⟩

/-- The count of batches less one, its zero flag whether it is now zero. -/
theorem batchEnd_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hb : s.gpr .r14 = BitVec.ofNat 64 j) :
    WP isa (.block InvCfg.batchEnd) s fun s' =>
      s'.gpr .r14 = BitVec.ofNat 64 (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) ∧ Keeps [.r14] s s' := by
  apply WP.of_runBlock
  simp only [InvCfg.batchEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags, ite_true, Option.some.injEq,
    exists_eq_left', hb, sext1]
  have e : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega : j - 1 < 2 ^ 64)]
    omega
  refine ⟨e, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [e]
    congr 1
    by_cases h : j - 1 = 0
    · rw [h]; simp
    · rw [decide_eq_false h]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact h this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem update_eq (P : InvCfg) :
    P.fgUpdate ++ P.abUpdate ++ InvCfg.batchEnd = fgCode P ++ (abCode P ++ InvCfg.batchEnd) := by
  simp only [fgCode, fgHalves, abCode, abHalves, InvCfg.fgUpdate, InvCfg.abUpdate, List.append_assoc]

/-- A batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` by their matrix,
and the count less one. -/
theorem batch_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size p s.mem base) {I : Divstep.IState} (hI : IInv P base I s)
    (hd : |I.d| ≤ 2 ^ 30) (hf1 : I.f % 2 = 1) (hf : |I.f| ≤ p) (hg : |I.g| ≤ p)
    (ha : |I.a| ≤ p) (hb : |I.b| ≤ p) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hc : s.gpr .r14 = BitVec.ofNat 64 j) :
    WP isa P.batch s fun t =>
      (IInv P base (Divstep.batch 59 p P.M.minv.toNat I) t ∧ t.gpr .r14 = BitVec.ofNat 64 (j - 1) ∧
        KeepRegs batchRegs s t ∧ Unch base (batchW P) s.mem t.mem) ∧ t.zf = some (decide (j - 1 = 0)) := by
  have hn := hs.nowrap
  obtain ⟨eL, eF, eG, eA, eB, eNF, eNG, eT, eU⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; unfold invTbl at htbl; have hmt := hL.mo_tbl; unfold invTbl at hmt
  have hmo := hM.mo
  have hp : p < 2 ^ (64 * P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain ⟨buv, bqr⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  obtain ⟨mf, mg⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hf1 59
  rw [InvCfg.batch, List.append_assoc (P.words ++ _), List.append_assoc P.words, WP.block_append_iff]
  refine WP.mono (words_ok hL hs hI hd hf1) fun s₂ h₂ => ?_
  obtain ⟨hD, hU, hV, hQ, hR, O₂, k₂⟩ := h₂
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  have hM₂ : ModOkW P.M size p s₂.mem base := modOk_out hM O₂.unch (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; slotm_omega) hn
  rw [← List.append_assoc, update_eq, WP.block_append_iff]
  refine WP.mono (fgUpd_ok hL hs₂ hp hU hV hQ hR buv bqr (by rw [O₂.wordsVal (by slot_omega) (by slot_omega)]; exact hI.f)
    (by rw [O₂.wordsVal (by slot_omega) (by slot_omega)]; exact hI.g) hf hg
    ⟨_, mf.symm⟩ ⟨_, mg.symm⟩) fun s₃ ⟨eF₃, eG₃, k₃, U₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have g₃ : ∀ r ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r13], s₃.gpr r = s₂.gpr r := k₃.gpr
  have M₃ : ModOkW P.M size p s₃.mem base := modOk_out hM₂ U₃ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; slotm_omega) hn
  rw [WP.block_append_iff]
  refine WP.mono (abUpd_ok hL hs₃ M₃ (by rw [g₃ _ (by decide)]; exact hU) (by rw [g₃ _ (by decide)]; exact hV)
    (by rw [g₃ _ (by decide)]; exact hQ) (by rw [g₃ _ (by decide)]; exact hR) buv bqr
    (by rw [U₃.wordsVal (by cover_omega) (by slot_omega), O₂.wordsVal (by slot_omega) (by slot_omega)]; exact hI.a)
    (by rw [U₃.wordsVal (by cover_omega) (by slot_omega), O₂.wordsVal (by slot_omega) (by slot_omega)]; exact hI.b)
    ha hb) fun s₄ ⟨eA₄, eB₄, k₄, U₄⟩ => ?_
  have c₄ : s₄.gpr .r14 = BitVec.ofNat 64 j := by
    rw [k₄.gpr _ (by decide), g₃ _ (by decide), k₂.gpr _ (by decide), hc]
  refine WP.mono (batchEnd_ok s₄ hj hj' c₄) fun t ⟨ct, zt, kt⟩ =>
    ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ct, ?_, ?_⟩, zt⟩
  · simp only [Divstep.batch]
    rw [kt.1 _ (by decide), k₄.gpr _ (by decide), g₃ _ (by decide)]; exact hD
  · simp only [Divstep.batch]
    rw [kt.2.1, U₄.wordsVal (by cover_omega) (by slot_omega)]; exact eF₃
  · simp only [Divstep.batch]
    rw [kt.2.1, U₄.wordsVal (by cover_omega) (by slot_omega)]; exact eG₃
  · simp only [Divstep.batch]
    rw [kt.2.1]; exact eA₄
  · simp only [Divstep.batch]
    rw [kt.2.1]; exact eB₄
  · exact ((k₂.mono (by decide)).trans ((k₃.trans k₄).mono (by decide))).trans ((Keeps.regs kt).mono (by decide))
  · rw [kt.2.1]; exact Unch.cover ((O₂.unch.trans U₃).trans U₄) (by unfold batchW invTbl; cover_omega)

end VG.Proof.Weierstrass.X86_64
