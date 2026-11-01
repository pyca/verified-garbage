module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.VLanes

/-!
# ML-DSA on x86-64: a table of `u32`s from a static

`vtabFill` and `ytabFill` copy the static table of `tabWords t n` into
`scratch`, 16 or 32 bytes at a time, leaving the table `Tab t` there
(`vtabFill_ok`, `ytabFill_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.Round (coeffAt_eq coeffAddr)
open VG.Proof.Sha3.X86_64 (WP.cons)

theorem tabWords_getD (t : Nat → Nat) {n j : Nat} (hj : j < n / 2) :
    (tabWords t n).getD j 0 = BitVec.ofNat 64 (t (2 * j) + 2 ^ 32 * t (2 * j + 1)) := by
  simp [tabWords, List.getD_eq_getElem?_getD, hj]

theorem tabWords_length (t : Nat → Nat) (n : Nat) : (tabWords t n).length = n / 2 := by
  simp [tabWords]

/-- Doubleword `e` of the two words of `t (2j), …, t (2j + 3)`. -/
theorem dword_words2 (t : Nat → Nat) (ht : ∀ k, t k < 2 ^ 32) (j : Nat) {e : Nat} (he : e < 4) :
    (BitVec.ofNat 64 (t (2 * (j + 1)) + 2 ^ 32 * t (2 * (j + 1) + 1)) ++
        BitVec.ofNat 64 (t (2 * j) + 2 ^ 32 * t (2 * j + 1))).extractLsb' (32 * e) 32 =
      BitVec.ofNat 32 (t (2 * j + e)) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := ht (2 * j); have h1 := ht (2 * j + 1)
  have h2 := ht (2 * (j + 1)); have h3 := ht (2 * (j + 1) + 1)
  have lo : t (2 * j) + 2 ^ 32 * t (2 * j + 1) < 2 ^ 64 := by omega
  have hi : t (2 * (j + 1)) + 2 ^ 32 * t (2 * (j + 1) + 1) < 2 ^ 64 := by omega
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lo, Nat.mod_eq_of_lt hi, ← Nat.shiftLeft_add_eq_or_of_lt lo, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl
  · rw [show 2 * j + 0 = 2 * j from rfl, Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reducePow]; omega
  · rw [Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.mul_one, Nat.reducePow]; omega
  · rw [show 2 * j + 2 = 2 * (j + 1) by omega, Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.reduceMul, Nat.reducePow]; omega
  · rw [show 2 * j + 3 = 2 * (j + 1) + 1 by omega, Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.reduceMul, Nat.reducePow]; omega

theorem ea_atT (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  show s.gpr b + BitVec.ofInt 64 (d : Int) = _
  rw [BitVec.ofInt_natCast]

/-- The 32 bytes of words `4i, …, 4i + 3` of `ws`. -/
abbrev chunk32 (ws : List (BitVec 64)) (i : Nat) : BitVec 256 :=
  (ws.getD (4 * i + 3) 0 ++ ws.getD (4 * i + 2) 0) ++ (ws.getD (4 * i + 1) 0 ++ ws.getD (4 * i) 0)

/-- One step of `ytabFill`: words `4i, …, 4i + 3` of the static to `[r + 32i]`. -/
theorem ytab_step {name : String} {ws : List (BitVec 64)} {r : Reg} {sP : Addr} {i : Nat}
    (hl : 4 * i + 4 ≤ ws.length) (hi : 32 * i < 2 ^ 31) {w : State}
    (h9 : w.gpr .r9 = w.syms name) (hsi : w.gpr r = sP) (hin : InRegions w.wr (sP + BitVec.ofNat 64 (32 * i)) 32) :
    WP isa (.block [.vmovdquTbl .xmm0 (at_ .r9 (32 * i)) name ws, .vmovdquStore .l256 (at_ r (32 * i)) .xmm0]) w
      fun w' => w'.mem = w.mem.writeW (sP + BitVec.ofNat 64 (32 * i)) (chunk32 ws i) ∧ w'.gpr = w.gpr ∧
        w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.mxcsr = w.mxcsr ∧ w'.syms = w.syms := by
  have ho : (w.ea (at_ .r9 (32 * i)) - w.syms name).toNat = 8 * (4 * i) := by
    rw [ea_atT, h9, BitVec.add_comm, BitVec.add_sub_cancel,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have h8 : 8 * (4 * i) % 8 = 0 := by omega
  have hd : 8 * (4 * i) / 8 = 4 * i := by omega
  let w1 := w.setV .l256 .xmm0 (ws.getD (4 * i + 1) 0 ++ ws.getD (4 * i) 0) (ws.getD (4 * i + 3) 0 ++ ws.getD (4 * i + 2) 0)
  refine WP.cons (s' := w1) ?_ ?_
  · simp only [exec, show (at_ .r9 (32 * i)).base = .r9 from rfl, h9, ho, h8, hd, hl, and_self, ite_true,
      Nat.add_zero, w1]
  have hy : w1.ymm .xmm0 = chunk32 ws i := by
    rw [State.ymm_eq, State.lane_setV256, State.lane_setV256]; rfl
  have g1 : w1.gpr = w.gpr := rfl
  have hin1 : InRegions w1.wr (w1.ea (at_ r (32 * i))) 32 := by rw [ea_atT, g1, hsi]; exact hin
  refine WP.cons (s' := w1.setMem (w1.mem.writeW (w1.ea (at_ r (32 * i))) (w1.ymm .xmm0))) ?_ ?_
  · simp only [exec, State.store256_eq, hin1, ite_true]
  · refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [State.setMem_mem, ea_atT, g1, hsi, hy]; rfl

/-- Doubleword `e < 8` of two 128-bit halves. -/
theorem dword_app128 (X Y : BitVec 128) {e : Nat} (he : e < 8) :
    (X ++ Y).extractLsb' (32 * e) 32 =
      if e < 4 then Y.extractLsb' (32 * e) 32 else X.extractLsb' (32 * (e - 4)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  split <;> rename_i h
  · simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and,
      show 32 * e + j < 128 by omega, ite_true]
  · simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and,
      show ¬ 32 * e + j < 128 by omega, ite_false, show 32 * e + j - 128 = 32 * (e - 4) + j by omega]

/-- Doubleword `e < 8` of chunk `i` of `tabWords t n`: `t (8i + e)`. -/
theorem chunk32_dword (t : Nat → Nat) (ht : ∀ k, t k < 2 ^ 32) {n i e : Nat} (hi : 4 * i + 4 ≤ n / 2)
    (he : e < 8) : (chunk32 (tabWords t n) i).extractLsb' (32 * e) 32 = BitVec.ofNat 32 (t (8 * i + e)) := by
  rw [chunk32, dword_app128 _ _ he, tabWords_getD t (show 4 * i + 3 < n / 2 by omega),
    tabWords_getD t (show 4 * i + 2 < n / 2 by omega), tabWords_getD t (show 4 * i + 1 < n / 2 by omega),
    tabWords_getD t (show 4 * i < n / 2 by omega)]
  split <;> rename_i h
  · have := dword_words2 t ht (4 * i) (e := e) h
    rwa [show 2 * (4 * i) + e = 8 * i + e by omega] at this
  · have := dword_words2 t ht (4 * i + 2) (e := e - 4) (by omega)
    rwa [show 2 * (4 * i + 2 + 1) = 2 * (4 * i + 3) by omega, show 4 * i + 2 + 1 = 4 * i + 3 by omega,
      show 2 * (4 * i + 2) + (e - 4) = 8 * i + e by omega] at this

/-- `ytabFill name t 256 r`: the table `t` at `sP` (in `r`), from the static `name`. -/
theorem ytabFill_ok (name : String) (t : Nat → Nat) (ht : ∀ k, t k < 2 ^ 32) {r : Reg} (hr : r ≠ .r9) {sP : Addr}
    {s : State} (hsi : s.gpr r = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block (ytabFill name t 256 r)) s fun s' => Tab t s'.mem sP 256 ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [ytabFill]
  refine WP.cons (s' := s.setReg .r9 (s.syms name)) (by simp only [exec]) ?_
  have hl := tabWords_length t 256
  refine WP.mono (wp_range_flatMap (M := isa) (N := 32) (fun i w =>
      Tab t w.mem sP (8 * i) ∧ Frame [pR sP] s.mem w.mem ∧ Keep [.r9] s w ∧ w.gpr .r9 = w.syms name ∧
        w.mxcsr = s.mxcsr)
    (fun i w hi ⟨hT, hf, hk, h9, hm⟩ => ?_) 32 (Nat.le_refl _) _
    ⟨fun _ h => absurd h (by omega), Frame.refl _ _,
      ⟨fun r' hr' => by simp only [List.mem_singleton] at hr'; simp only [RegUpd.gpr_setReg, hr', ite_false], rfl, rfl⟩,
      by simp only [RegUpd.gpr_setReg, ite_true]; rfl, rfl⟩)
    fun w ⟨hT, hf, hk, _, hm⟩ => ⟨hT, hf, hk, hm⟩
  have hsi' : w.gpr r = sP := by rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have hin : InRegions w.wr (sP + BitVec.ofNat 64 (32 * i)) 32 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by omega) (by omega)⟩
  refine WP.mono (ytab_step (by rw [hl]; omega) (by omega) h9 hsi' hin)
    fun w' ⟨hm', hg', hrd', hwr', hx', hy'⟩ => ⟨fun k hk' => ?_, ?_, ⟨fun r' hr' => by rw [hg']; exact hk.1 r' hr',
      by rw [hrd', hk.2.1], by rw [hwr', hk.2.2]⟩, by rw [hg', hy']; exact h9, by rw [hx', hm]⟩
  · rw [coeffAt_eq, hm']
    by_cases h : 8 * i ≤ k
    · rw [coeffAddr, show sP + BitVec.ofNat 64 (4 * k) =
          sP + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (4 * (k - 8 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega)),
        show 32 = 8 * 4 from rfl, readW_writeW_inside _ _ _ (by omega) (by decide),
        show 8 * (4 * (k - 8 * i)) = 32 * (k - 8 * i) by omega,
        chunk32_dword t ht (by omega) (by omega), show 8 * i + (k - 8 * i) = k by omega]
    · rw [Mem.readW_writeW_sep (Offset.sep sP (by omega) (by omega) (by omega)) (by decide)]
      exact hT k (by omega)
  · rw [hm']
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base sP (by omega) (by omega))

/-- The 16 bytes of words `2i` and `2i + 1` of `ws`. -/
abbrev chunk16 (ws : List (BitVec 64)) (i : Nat) : BitVec 128 := ws.getD (2 * i + 1) 0 ++ ws.getD (2 * i) 0

/-- One step of `vtabFill`: words `2i` and `2i + 1` of the static to `[r + 16i]`. -/
theorem vtab_step {name : String} {ws : List (BitVec 64)} {r : Reg} {sP : Addr} {i : Nat}
    (hl : 2 * i + 2 ≤ ws.length) (hi : 16 * i < 2 ^ 31) {w : State}
    (h9 : w.gpr .r9 = w.syms name) (hsi : w.gpr r = sP) (hin : InRegions w.wr (sP + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block [.movdquTbl .xmm0 (at_ .r9 (16 * i)) name ws, .movdquStore (at_ r (16 * i)) .xmm0]) w
      fun w' => w'.mem = w.mem.writeW (sP + BitVec.ofNat 64 (16 * i)) (chunk16 ws i) ∧ w'.gpr = w.gpr ∧
        w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.mxcsr = w.mxcsr ∧ w'.syms = w.syms := by
  have ho : (w.ea (at_ .r9 (16 * i)) - w.syms name).toNat = 8 * (2 * i) := by
    rw [ea_atT, h9, BitVec.add_comm, BitVec.add_sub_cancel,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have h8 : 8 * (2 * i) % 8 = 0 := by omega
  have hd : 8 * (2 * i) / 8 = 2 * i := by omega
  let w1 := w.setXmm .xmm0 (chunk16 ws i)
  refine WP.cons (s' := w1) ?_ ?_
  · simp only [exec, show (at_ .r9 (16 * i)).base = .r9 from rfl, h9, ho, h8, hd, hl, and_self, ite_true,
      Nat.add_zero, w1]
  have g1 : w1.gpr = w.gpr := rfl
  have hin1 : InRegions w1.wr (w1.ea (at_ r (16 * i))) 16 := by rw [ea_atT, g1, hsi]; exact hin
  refine WP.cons (s' := w1.setMem (w1.mem.writeW (w1.ea (at_ r (16 * i))) (w1.xmm .xmm0))) ?_ ?_
  · simp only [exec, State.store128_eq, hin1, ite_true]
  · refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [State.setMem_mem, ea_atT, g1, hsi]
    simp only [w1, VG.Proof.MlKem.X86_64.xmm_setXmm, ite_true]; rfl

/-- `vtabFill name t 256 r`: the table `t` at `sP` (in `r`), from the static `name`. -/
theorem vtabFill_ok (name : String) (t : Nat → Nat) (ht : ∀ k, t k < 2 ^ 32) {r : Reg} (hr : r ≠ .r9) {sP : Addr}
    {s : State} (hsi : s.gpr r = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block (vtabFill name t 256 r)) s fun s' => Tab t s'.mem sP 256 ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [vtabFill]
  refine WP.cons (s' := s.setReg .r9 (s.syms name)) (by simp only [exec]) ?_
  have hl := tabWords_length t 256
  refine WP.mono (wp_range_flatMap (M := isa) (N := 64) (fun i w =>
      Tab t w.mem sP (4 * i) ∧ Frame [pR sP] s.mem w.mem ∧ Keep [.r9] s w ∧ w.gpr .r9 = w.syms name ∧
        w.mxcsr = s.mxcsr)
    (fun i w hi ⟨hT, hf, hk, h9, hm⟩ => ?_) 64 (Nat.le_refl _) _
    ⟨fun _ h => absurd h (by omega), Frame.refl _ _,
      ⟨fun r' hr' => by simp only [List.mem_singleton] at hr'; simp only [RegUpd.gpr_setReg, hr', ite_false], rfl, rfl⟩,
      by simp only [RegUpd.gpr_setReg, ite_true]; rfl, rfl⟩)
    fun w ⟨hT, hf, hk, _, hm⟩ => ⟨hT, hf, hk, hm⟩
  have hsi' : w.gpr r = sP := by rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have hin : InRegions w.wr (sP + BitVec.ofNat 64 (16 * i)) 16 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by omega) (by omega)⟩
  refine WP.mono (vtab_step (by rw [hl]; omega) (by omega) h9 hsi' hin)
    fun w' ⟨hm', hg', hrd', hwr', hx', hy'⟩ => ⟨fun k hk' => ?_, ?_, ⟨fun r' hr' => by rw [hg']; exact hk.1 r' hr',
      by rw [hrd', hk.2.1], by rw [hwr', hk.2.2]⟩, by rw [hg', hy']; exact h9, by rw [hx', hm]⟩
  · rw [coeffAt_eq, hm']
    by_cases h : 4 * i ≤ k
    · rw [coeffAddr, show sP + BitVec.ofNat 64 (4 * k) =
          sP + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (4 * (k - 4 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega)),
        show 32 = 8 * 4 from rfl, readW_writeW_inside _ _ _ (by omega) (by decide),
        show 8 * (4 * (k - 4 * i)) = 32 * (k - 4 * i) by omega, chunk16,
        tabWords_getD t (show 2 * i + 1 < 256 / 2 by omega), tabWords_getD t (show 2 * i < 256 / 2 by omega)]
      have := dword_words2 t ht (2 * i) (e := k - 4 * i) (by omega)
      rwa [show 2 * (2 * i) + (k - 4 * i) = k by omega, show 2 * i + 1 = 2 * i + 1 from rfl] at this
    · rw [Mem.readW_writeW_sep (Offset.sep sP (by omega) (by omega) (by omega)) (by decide)]
      exact hT k (by omega)
  · rw [hm']
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base sP (by omega) (by omega))

end VG.Proof.MlDsa.X86_64.Arith
