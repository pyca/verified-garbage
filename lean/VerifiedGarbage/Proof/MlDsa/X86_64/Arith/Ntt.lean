module

import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
public import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec
import VerifiedGarbage.Proof.MlKem.X86_64.S4Vec
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.VLanes

/-! ### `MlDsa.X86_64.Arith.TabFill`, which this module and modules that import it used -/

section

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
  have lo : t (2 * j) + 2 ^ 32 * t (2 * j + 1) < 2 ^ 64 := by omega_using [h0, h1]
  have hi : t (2 * (j + 1)) + 2 ^ 32 * t (2 * (j + 1) + 1) < 2 ^ 64 := by omega_using [h2, h3]
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lo, Nat.mod_eq_of_lt hi, ← Nat.shiftLeft_add_eq_or_of_lt lo, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rcases (by omega_using [he] : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl
  · rw [show 2 * j + 0 = 2 * j from rfl, Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reducePow]; omega_using [h0]
  · rw [Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.mul_one, Nat.reducePow]; omega_using [h0, h1]
  · rw [show 2 * j + 2 = 2 * (j + 1) by omega_using [], Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.reduceMul, Nat.reducePow]; omega_using [h0, h1, h2]
  · rw [show 2 * j + 3 = 2 * (j + 1) + 1 by omega_using [], Nat.mod_eq_of_lt (ht _)]
    simp only [Nat.reduceMul, Nat.reducePow]; omega_using [h0, h1, h2, h3]

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
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]; omega_using []
  have h8 : 8 * (4 * i) % 8 = 0 := by omega_using []
  have hd : 8 * (4 * i) / 8 = 4 * i := by omega_using []
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
      show ¬ 32 * e + j < 128 by omega_using [h], ite_false, show 32 * e + j - 128 = 32 * (e - 4) + j by omega_using [h]]

/-- Doubleword `e < 8` of chunk `i` of `tabWords t n`: `t (8i + e)`. -/
theorem chunk32_dword (t : Nat → Nat) (ht : ∀ k, t k < 2 ^ 32) {n i e : Nat} (hi : 4 * i + 4 ≤ n / 2)
    (he : e < 8) : (chunk32 (tabWords t n) i).extractLsb' (32 * e) 32 = BitVec.ofNat 32 (t (8 * i + e)) := by
  rw [chunk32, dword_app128 _ _ he, tabWords_getD t (show 4 * i + 3 < n / 2 by omega_using [hi]),
    tabWords_getD t (show 4 * i + 2 < n / 2 by omega_using [hi]), tabWords_getD t (show 4 * i + 1 < n / 2 by omega_using [hi]),
    tabWords_getD t (show 4 * i < n / 2 by omega_using [hi])]
  split <;> rename_i h
  · have := dword_words2 t ht (4 * i) (e := e) h
    rwa [show 2 * (4 * i) + e = 8 * i + e by omega_using []] at this
  · have := dword_words2 t ht (4 * i + 2) (e := e - 4) (by omega_using [he])
    rwa [show 2 * (4 * i + 2 + 1) = 2 * (4 * i + 3) by omega_using [], show 4 * i + 2 + 1 = 4 * i + 3 by omega_using [],
      show 2 * (4 * i + 2) + (e - 4) = 8 * i + e by omega_using [h]] at this

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
    ⟨fun _ h => absurd h (by omega_using []), Frame.refl _ _,
      ⟨fun r' hr' => by simp only [List.mem_singleton] at hr'; simp only [RegUpd.gpr_setReg, hr', ite_false], rfl, rfl⟩,
      by simp only [RegUpd.gpr_setReg, ite_true]; rfl, rfl⟩)
    fun w ⟨hT, hf, hk, _, hm⟩ => ⟨hT, hf, hk, hm⟩
  have hsi' : w.gpr r = sP := by rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have hin : InRegions w.wr (sP + BitVec.ofNat 64 (32 * i)) 32 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by omega_using [hi]) (by omega_using [hi])⟩
  refine WP.mono (ytab_step (by rw [hl]; omega_using [hi]) (by omega_using [hi]) h9 hsi' hin)
    fun w' ⟨hm', hg', hrd', hwr', hx', hy'⟩ => ⟨fun k hk' => ?_, ?_, ⟨fun r' hr' => by rw [hg']; exact hk.1 r' hr',
      by rw [hrd', hk.2.1], by rw [hwr', hk.2.2]⟩, by rw [hg', hy']; exact h9, by rw [hx', hm]⟩
  · rw [coeffAt_eq, hm']
    by_cases h : 8 * i ≤ k
    · rw [coeffAddr, show sP + BitVec.ofNat 64 (4 * k) =
          sP + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (4 * (k - 8 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega_using [h])),
        show 32 = 8 * 4 from rfl, readW_writeW_inside _ _ _ (by omega_using [hk']) (by decide),
        show 8 * (4 * (k - 8 * i)) = 32 * (k - 8 * i) by omega_using [],
        chunk32_dword t ht (by omega_using [hi]) (by omega_using [hk']), show 8 * i + (k - 8 * i) = k by omega_using [h]]
    · rw [Mem.readW_writeW_sep (Offset.sep sP (by omega_using [h]) (by omega_using [hi, hk']) (by omega_using [hi])) (by decide)]
      exact hT k (by omega_using [h])
  · rw [hm']
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base sP (by omega_using [hi]) (by omega_using [hi]))

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
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]; omega_using []
  have h8 : 8 * (2 * i) % 8 = 0 := by omega_using []
  have hd : 8 * (2 * i) / 8 = 2 * i := by omega_using []
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
    ⟨fun _ h => absurd h (by omega_using []), Frame.refl _ _,
      ⟨fun r' hr' => by simp only [List.mem_singleton] at hr'; simp only [RegUpd.gpr_setReg, hr', ite_false], rfl, rfl⟩,
      by simp only [RegUpd.gpr_setReg, ite_true]; rfl, rfl⟩)
    fun w ⟨hT, hf, hk, _, hm⟩ => ⟨hT, hf, hk, hm⟩
  have hsi' : w.gpr r = sP := by rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have hin : InRegions w.wr (sP + BitVec.ofNat 64 (16 * i)) 16 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by omega_using [hi]) (by omega_using [hi])⟩
  refine WP.mono (vtab_step (by rw [hl]; omega_using [hi]) (by omega_using [hi]) h9 hsi' hin)
    fun w' ⟨hm', hg', hrd', hwr', hx', hy'⟩ => ⟨fun k hk' => ?_, ?_, ⟨fun r' hr' => by rw [hg']; exact hk.1 r' hr',
      by rw [hrd', hk.2.1], by rw [hwr', hk.2.2]⟩, by rw [hg', hy']; exact h9, by rw [hx', hm]⟩
  · rw [coeffAt_eq, hm']
    by_cases h : 4 * i ≤ k
    · rw [coeffAddr, show sP + BitVec.ofNat 64 (4 * k) =
          sP + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (4 * (k - 4 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega_using [h])),
        show 32 = 8 * 4 from rfl, readW_writeW_inside _ _ _ (by omega_using [hk']) (by decide),
        show 8 * (4 * (k - 4 * i)) = 32 * (k - 4 * i) by omega_using [], chunk16,
        tabWords_getD t (show 2 * i + 1 < 256 / 2 by omega_using [hi]), tabWords_getD t (show 2 * i < 256 / 2 by omega_using [hi])]
      have := dword_words2 t ht (2 * i) (e := k - 4 * i) (by omega_using [hk'])
      rwa [show 2 * (2 * i) + (k - 4 * i) = k by omega_using [h], show 2 * i + 1 = 2 * i + 1 from rfl] at this
    · rw [Mem.readW_writeW_sep (Offset.sep sP (by omega_using [h]) (by omega_using [hi, hk']) (by omega_using [hi])) (by decide)]
      exact hT k (by omega_using [h])
  · rw [hm']
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base sP (by omega_using [hi]) (by omega_using [hi]))

end VG.Proof.MlDsa.X86_64.Arith

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_ntt`

The code sets no MXCSR of its own (`noMx_ok`, `mx_correct`); the prologue leaves the table of zetas in `scratch` and the
constants (`vpro_ok`), each layer is `nttLayer` (`vlay_ok`, `vlay2_ok`,
`vlay1_ok`), and the eight layers are `NTT` (`ntt_eq_layers`). `LI`, `vpro_ok`
and `inPlaceSat` serve `NTT⁻¹` too.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep WP.keep writesOnly gprPreserved_of mxR mx_sub xmm_setXmm
  GOnly add_ofNat_zero sel)
open VG.Spec.MlDsa (q n Poly Zq zetas ntt)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)

/-! ## The prologue -/

theorem vconsts_ok (s : State) :
    WP isa (.block vconsts) s fun s' => VConsts s' ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr := by
  simp only [vconsts]
  vrund
  refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true]; decide
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]; decide
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]

/-- The table of zetas and the constants. -/
theorem vpro_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block vpro) s fun s' => Tab zmTab s'.mem sP 256 ∧ VConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9, .rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [vpro, WP.block_append_iff]
  refine WP.mono (vtabFill_ok zetaTbl zmTab (fun k => Nat.lt_trans (zmTab_lt k) (by decide)) (by decide) hsi hw)
    fun s1 ⟨hT, hf, k1, x1⟩ => WP.mono (vconsts_ok s1) fun s2 ⟨hc, k2, m2, x2⟩ =>
      ⟨by rw [m2]; exact hT, hc, by rw [m2]; exact hf, (k1.trans k2).mono (by simp), by rw [x2, x1]⟩

/-! ## The layers -/

/-- Between the layers: the polynomial `F` at `fP`, the table at `sP`, and
the constants. -/
structure LI (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : VConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-- The last layer. -/
theorem LI.last {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l : Prog isa}
    {F F' : Poly}
    (hl : ∀ s, VConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInv fP s s')
    {s : State} (hI : LI fP sP s₀ F s) : WP isa l s (LI fP sP s₀ F') :=
  WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩

/-- A layer, then `c`. -/
theorem LI.seq {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l c : Prog isa}
    {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, VConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInv fP s s')
    (hc : ∀ s, LI fP sP s₀ F' s → WP isa c s Q) {s : State} (hI : LI fP sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

theorem step_fwd (p : Addr) (a d : Nat) {dz : BitVec 32} (h : BitVec.signExtend 64 dz = BitVec.ofNat 64 (4 * d)) :
    coeffAddr p a + BitVec.signExtend 64 dz = coeffAddr p (a + d) := by
  rw [h, coeffAddr_add]

theorem step_bwd (p : Addr) (a d : Nat) {dz : BitVec 32}
    (h : BitVec.ofNat 64 (4 * d) + BitVec.signExtend 64 dz = 0) :
    coeffAddr p (a + d) + BitVec.signExtend 64 dz = coeffAddr p a := by
  rw [← coeffAddr_add, BitVec.add_assoc, h]; exact BitVec.add_zero _

/-- The block of `NTT`. -/
abbrev fwdBlk : Poly → Nat → Nat → Nat → Nat → Poly := fun f len k st t => blockN bfly f len (zetas k) st t

theorem nttLayer_eq (F : Poly) (len : Nat) :
    nttLayer F len = layF fwdBlk F len (fun c => 128 / len + c) (128 / len) := rfl

/-- A layer of `NTT` with `len ≥ 4`, whose first zeta is `zetas k`. -/
theorem fwdLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat) (hlen : len ∈ [4, 8, 16, 32, 64, 128]) (hk : 128 / len = k)
    {F : Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vbfly len k 4) s fun s' => PolyIs s'.mem fP (nttLayer F len) ∧ BInv fP s s' := by
  rw [nttLayer_eq]
  exact vlay_ok vbfly_spec nttBlk_ok hlen 4 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith)
    (fun c _ => step_fwd _ _ 1 (by decide)) hc hdi hsi hS hT hwf hw hd

theorem fwdLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr)
    (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vbfly 64 0x50 8) s fun s' => PolyIs s'.mem fP (nttLayer F 2) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0x50 e = e / 2 := by decide
  rw [nttLayer_eq, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vbfly_spec nttBlk_ok 64 0x50 8 (fun c => 64 + c) (fun i => 64 + 2 * i) rfl
    (fun i _ => by omega_arith) (fun i _ e he => by rw [hs e he]; omega_arith)
    (fun i _ => (step_fwd _ _ 2 (by decide)).trans (congrArg _ (by omega_arith))) hc hdi hsi hS hT hwf hw hd

theorem fwdLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr)
    (hw : pR sP ∈ s.wr) :
    WP isa (vlay1 vbfly 128 0xE4 16) s fun s' => PolyIs s'.mem fP (nttLayer F 1) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0xE4 e = e := by decide
  rw [nttLayer_eq, show 128 / 1 = 128 from rfl]
  exact vlay1_ok vbfly_spec nttBlk_ok 128 0xE4 16 (fun c => 128 + c) (fun i => 128 + 4 * i) rfl
    (fun i _ => by omega_arith) (fun i _ e he => by rw [hs e he]; omega_arith)
    (fun i _ => (step_fwd _ _ 4 (by decide)).trans (congrArg _ (by omega_arith))) hc hdi hsi hS hT hwf hw hd

/-! ## `vg_mldsa_ntt` -/

theorem mx_sub' (sP : Addr) : Region.Sub (mxR sP) (pR sP) := mx_sub sP

/-- The regions of `scratch` within it, and `f`. -/
theorem frame_fs {fP sP : Addr} {m m' : Mem} {rs : List Region} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (pR fP) ∨ Region.Sub r (pR sP)) : Frame [pR fP, pR sP] m m' :=
  h.sub fun r hr => (hs r hr).elim (fun h => ⟨_, List.mem_cons_self .., h⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

/-- The code, from its state `s1`: the prologue, then the
layers `l`, which leave `F`, then `NTT⁻¹`'s scaling or nothing. -/
theorem nttBody_ok {t : Poly → Poly} {s s1 : State} (hs : (inPlaceK t).pre s) {l : Prog isa} {G : Poly}
    (k1 : Keep [.rax, .r11] s s1) (f1 : Frame [mxR (s.gpr .rsi)] s.mem s1.mem)
    (hl : ∀ s2, LI (s.gpr .rdi) (s.gpr .rsi) s2 (polyAt s.mem (s.gpr .rdi)) s2 → s2.gpr .rdi = s.gpr .rdi →
      s2.gpr .rsi = s.gpr .rsi → pR (s.gpr .rdi) ∈ s2.wr → pR (s.gpr .rsi) ∈ s2.wr →
      WP isa l s2 fun s3 => LI (s.gpr .rdi) (s.gpr .rsi) s2 G s3) :
    WP isa (.seq (.block vpro) l) s1 fun s' =>
      PolyIs s'.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
  have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
  have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _))
      ⟨hs.2.2.2.2.2, rfl⟩
  refine WP.seq (WP.mono (vpro_ok hsi1 (by rw [k1.2.2]; exact hw)) fun s2 ⟨hT, hc, hf2, k2, _⟩ => ?_)
  have hF2 : PolyIs s2.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF1
  refine WP.mono (hl s2 ⟨hF2, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    (by rw [k2.gpr (by decide), hdi1]) (by rw [k2.gpr (by decide), hsi1])
    (by rw [k2.2.2, k1.2.2]; exact hwf) (by rw [k2.2.2, k1.2.2]; exact hw)) fun s3 hI => ⟨hI.P, ?_⟩
  refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans (frame_fs hI.frame ?_)) <;>
    intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
  exacts [.inr (mx_sub' _), .inr fun _ h => h, .inl fun _ h => h]

/-- The body, and the ABI. -/
theorem mx_correct {t : Poly → Poly} {l : Prog isa} (s : State) (hs : (inPlaceK t).pre s)
    (hctl : ctlOk (.seq (.block vpro) l : Prog isa) = true)
    (hk' : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r11])
      (.seq (.block vpro) l : Prog isa) = true)
    (hl : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR (s.gpr .rsi)] s.mem s1.mem →
      WP isa (.seq (.block vpro) l) s1 fun s' => PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem) :
    ∃ tr s', Exec isa (.seq (.block vpro) l : Prog isa) s tr s' ∧
      abiPreserved s s' ∧ (inPlaceK t).post s s' := by
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW := noMx_ok (c := .seq (.block vpro) l) hl
  obtain ⟨tr, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (writesOnly_of hk')
  refine ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub' _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _)) hP

theorem ntt_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.ntt s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine mx_correct s hs (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (nttBody_ok hs k1 f1 (G := nttLens.foldl nttLayer (polyAt s.mem (s.gpr .rdi)))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [ntt_eq_layers]; exact hP, hf⟩
  simp only [nttLens, List.foldl_cons, List.foldl_nil]
  refine LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 64 2 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 32 4 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 16 8 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 8 16 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 4 32 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay2_ok hd) ?_ hI
  exact fun _ hI => LI.last hdi hsi hwf hw hd (fwdLay1_ok hd) hI

/-- The pointers and `rsp` are public. -/
theorem inPlace_agree {t : Poly → Poly} (s₁ s₂ : State) (_ : (inPlaceK t).pre s₁) (_ : (inPlaceK t).pre s₂)
    (hp : (inPlaceK t).pub s₁ s₂) : X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem ntt_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub Impl.MlDsa.X86_64.Arith.ntt :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.ntt (Proof.MlDsa.nttContract X86_64.abi) :=
  Verified.of_correct ntt_correct ntt_ct (by
    mldsa_implies [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith
