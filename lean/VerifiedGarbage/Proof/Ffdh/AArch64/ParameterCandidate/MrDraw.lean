module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops

/-! ### `Ffdh.AArch64.ParameterCandidate.Shape`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on AArch64: the candidate `p`

`shapeP` (`shapeP_ok`): the first `out_len` octets of the tape into `aN`
(`loadA`), then its top word and'ed with `fTop = 2^k − 1` and bit `k − 1`
set, and its low bit set: `candidateOf bits` of their number (`wv_shape`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- A prefix of a source. -/
theorem src_take {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs) (n : Nat) :
    Src s B Z p (bs.take n) :=
  ⟨fun i hi => h.rd i (by rw [List.length_take] at hi; omega_arith), fun i hi => by
    rw [List.getElem_take]; exact h.val i (by rw [List.length_take] at hi; omega_arith),
    fun i hi => h.out i (by rw [List.length_take] at hi; omega_arith)⟩

/-- A suffix of a source, at its offset. -/
theorem src_drop {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs) (n : Nat) :
    Src s B Z (p + BitVec.ofNat 64 n) (bs.drop n) := by
  have e : ∀ i, p + BitVec.ofNat 64 n + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (n + i) := fun i => by
    rw [BitVec.add_assoc, ofNat_add_ofNat]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [e]; exact h.rd (n + i) (by rw [List.length_drop] at hi; omega_arith)
  · rw [e, List.getElem_drop]; exact h.val (n + i) (by rw [List.length_drop] at hi; omega_arith)
  · rw [e]; exact h.out (n + i) (by rw [List.length_drop] at hi; omega_arith)

theorem shr1_add1 {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 64) :
    BitVec.ofNat 64 (2 ^ k - 1) >>> 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ (k - 1)) := by
  rw [shr_ofNat, Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; omega_arith),
    ofNat_add_ofNat]
  congr 1
  have e : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← Nat.pow_succ']; congr 1; omega_arith
  have := Nat.two_pow_pos (k - 1)
  rw [e]; omega_arith

/-- The shaping block, from `aN` holding the loaded number. -/
theorem shapeBlock_ok {s : State} {B : Addr} {Z w k : Nat} (h : Ws s B Z w) (hk1 : 1 ≤ k) (hk : k ≤ 64)
    (hT : word s.mem B (8 * fTop) = BitVec.ofNat 64 (2 ^ k - 1)) :
    WP isa (.block (ws ++ base aN .x16 ++ ([.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8,
      ldh .x4 fTop, ld .x3 .x16, ld .x6 .x5, movi .x9 1, .logic .orr .x .x3 .x3 .x9, .logic .and .x .x6 .x6 .x4,
      .lsr .x .x9 .x4 1, .addImm .x .x9 .x9 1, .logic .orr .x .x6 .x6 .x9, st .x3 .x16, st .x6 .x5] : List Instr))) s fun t =>
      wv t.mem B (slot w aN) w = Spec.Ffdh.candidateOf (64 * (w - 1) + k) (wv s.mem B (slot w aN) w) ∧
      Frm B [(slot w aN, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have hTs : 8 * fTop + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  generalize ht : word s.mem B (slot w aN + 8 * (w - 1)) = top
  generalize hb : word s.mem B (slot w aN) = bot
  have one16 : (1#16).setWidth 64 = (1 : BitVec 64) := rfl
  have hsel := shr1_add1 hk1 hk
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x9] (Q := fun t => t.mem =
      (s.mem.writeW (off B (slot w aN)) (bot ||| 1)).writeW (off B (slot w aN + 8 * (w - 1)))
        ((top &&& BitVec.ofNat 64 (2 ^ k - 1)) ||| BitVec.ofNat 64 (2 ^ (k - 1)))) (by
    brun [hm₂, h16, e12, h0₂, one16, hb, ht, hT, hsel,
      top_addr B (d := slot w aN) (w := w) (by omega_arith) (by omega_arith),
      hs₂.ld (d := slot w aN) (by omega_arith), hs₂.st (d := slot w aN) (by omega_arith),
      hs₂.ld (d := slot w aN + 8 * (w - 1)) (by omega_arith), hs₂.st (d := slot w aN + 8 * (w - 1)) (by omega_arith),
      hdr_enc (show fTop < 32 by decide), hs₂.ld (d := 8 * fTop) (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ⟨?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm]
    refine VG.Proof.Ffdh.ParameterCandidate.wv_shape (by omega_arith) hk1 hk ?_ ?_ ?_
    · rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self, hb]
    · rw [word_writeW_self, ht]
    · intro j h0 hj
      rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith),
        (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
  · intro x hx
    rw [hm, writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith)]

/-- `shapeP`: `p` into `aN`. -/
theorem shapeP_ok {s : State} {p : PP} (h : PSt p (mW p.bits) s)
    (hK : word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.L)
    (hT : word s.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1)) (hr : p.L ≤ p.r.length) :
    WP isa (seqs shapeP) s fun t =>
      PSt p (mW p.bits) t ∧
      wv t.mem p.B (slot (mW p.bits) aN) (mW p.bits) =
        Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) ∧
      Frm p.B [(slot (mW p.bits) aN, 8 * (mW p.bits + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hws := h.ws
  have hn := hws.scr.nowrap
  have sN := hws.sl (show aN < 16 by decide)
  have hTs : 8 * fTop + 8 ≤ slot (mW p.bits) aN := hdr_lt_slot _ aN (by decide)
  unfold shapeP
  refine wp_seqs_append (by simp [loadA]) (by simp) ?_
  refine WP.mono (loadA_ok hws (j := aN) (sPtr := kRand) (sLen := kLen) (len := p.L) (bs := p.r.take p.L)
    (by decide) (by decide) (by decide) h.args.rand hK (src_take h.src p.L) (by rw [List.length_take]; omega_arith)
    (by simp only [PP.L]; omega_arith) (by simp only [PP.L, mW]; omega_arith)) fun s₁ ⟨hv₁, o₁, _, _, k₁⟩ => ?_
  have f₁ : Frm p.B [(slot (mW p.bits) aN, 8 * (mW p.bits + 2))] s.mem s₁.mem := Frm.of_outside o₁ (by simp)
  have st₁ : PSt p (mW p.bits) s₁ :=
    h.step (hws.congr' f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k₁ (by decide))
      f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) k₁
  have hT₁ : word s₁.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1) := by
    rw [f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl hTs) (by omega_arith)]; exact hT
  rw [seqs_one]
  refine WP.mono (shapeBlock_ok st₁.ws (by simp only [mK, mW]; omega_arith) (by simp only [mK, mW]; omega_arith) hT₁)
    fun t ⟨hv, f₂, k₂⟩ => ⟨st₁.step (st₁.ws.congr' f₂ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k₂ (by decide)) f₂
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) k₂, ?_, f₁.trans f₂,
      (k₁.trans k₂).mono (by decide)⟩
  rw [hv, hv₁, show 64 * (mW p.bits - 1) + mK p.bits = p.bits by simp only [mK, mW]; omega_arith]

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-! ### `Ffdh.AArch64.ParameterCandidate.Round`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on AArch64: a round

`round` (`round_ok`): an accepted witness `a` in Montgomery form, the shared
round (`Kernel.ok`, whose result is FFDH's `mrRound`: `rsa_round_eq`), then
`kStat := 2` for a failing witness, else the passing witnesses counted and
`kStat` 4 or, once there are `fChecks` of them, 1.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- What a round changes. -/
def rdRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++
    Caller.callRanges w ++ [(8 * fIdx, 8), (8 * kStat, 8)]

theorem mm3_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [] [(2, 1), (3, 1), (5, 1)]
    [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes, aAcc]; omega_using [], by simp only [slot, hdrBytes, aAcc]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes, aTmp]; omega_using [], by simp only [slot, hdrBytes, aTmp]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes, aXm]; omega_using [], by simp only [slot, hdrBytes, aXm]; omega_using []⟩

theorem rdRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w
    ([] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)] ++ [(8 * fIdx, 8), (8 * kStat, 8)])
    ([(2, 1), (3, 1), (5, 1)] ++ [(7, 1), (2, 1), (3, 1), (5, 1), (6, 1), (8, 1), (11, 16)] ++ [])
    (rdRanges w) :=
  VG.Proof.RsaKeyGen.shape_append (VG.Proof.RsaKeyGen.shape_append (mm3_shape w) (sharedKernel_shape w))
    (VG.Proof.RsaKeyGen.shape_self w _)

/-- A header word a round keeps. -/
theorem rdRanges_hdr (w : Nat) {k : Nat} (hk : k ∈ [0, 2, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27]) :
    ∀ r ∈ rdRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact VG.Proof.RsaKeyGen.hdr_of_shape (rdRanges_shape w) (by decide) (by decide)

/-- An array a round keeps. -/
theorem rdRanges_arr (w : Nat) {j : Nat} (hj : j ∈ [aN, aR2, aR1, aRm1]) :
    ∀ r ∈ rdRanges w, slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;>
    exact VG.Proof.RsaKeyGen.arr_of_shape (rdRanges_shape w) (by decide) (by decide) (Nat.le_refl _)

theorem rdRanges_lt (w : Nat) : ∀ r ∈ rdRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  rcases (rdRanges_shape w) r hr with h | ⟨q, hq, _, h2⟩
  · exact Nat.le_trans ((by decide : ∀ h ∈ ([] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)] ++
      [(8 * fIdx, 8), (8 * kStat, 8)] : List (Nat × Nat)), h.1 + h.2 ≤ hdrBytes) r h)
      (show hdrBytes ≤ slot w aE by unfold slot; exact Nat.le_add_right _ _)
  · refine Nat.le_trans h2 (VG.Proof.RsaKeyGen.slot_le_slot ?_)
    exact (by decide : ∀ q ∈ ([(2, 1), (3, 1), (5, 1)] ++ [(7, 1), (2, 1), (3, 1), (5, 1), (6, 1), (8, 1),
      (11, 16)] ++ [] : List (Nat × Nat)), q.1 + q.2 ≤ aE) q hq

theorem rdRanges_pmut (w : Nat) : ∀ r ∈ rdRanges w, PMut r := by
  intro r hr
  rcases (rdRanges_shape w) r hr with h | ⟨q, _, h1, _⟩
  · have := (by decide : ∀ h ∈ ([] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)] ++
      [(8 * fIdx, 8), (8 * kStat, 8)] : List (Nat × Nat)), 8 * 26 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * 16 ∨
      (8 * 18 ≤ h.1 ∧ h.1 + h.2 ≤ 8 * 19) ∨ (8 * 22 ≤ h.1 ∧ h.1 + h.2 ≤ 8 * 24)) r h
    exact this
  · exact Or.inl (Nat.le_trans (by unfold slot hdrBytes; omega_using []) h1)

/-- The end of a round. -/
theorem rdTail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {f : Bool} {i K : Nat} (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * fIdx) = BitVec.ofNat 64 i)
    (hC : word s.mem B (8 * fChecks) = BitVec.ofNat 64 K) (hi : i < 2 ^ 62) (hK : K < 2 ^ 62) :
    WP isa (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 2, sth .x3 kStat])
        (.block [ldh .x3 fIdx, ldh .x4 fChecks, .addImm .x .x3 .x3 1, .subs .x .x5 .x3 .x4, movi .x6 4, movi .x7 1,
          .csel .x .x5 .x7 .x6, sth .x3 fIdx, sth .x5 kStat])]) s fun t =>
      t.mem = (if f then (s.mem.writeW (off B (8 * fIdx)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))
        else s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 2)) ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask f ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kFlag < 32 by decide), hs.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega_using [h256]),
      hF]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  refine WP.ite (!f) (by rw [eval_zero, h3₁]; cases f <;> decide) (fun hf => ?_) (fun hf => ?_)
  · simp only [Bool.not_eq_true'] at hf
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 2)) (by
      brun [h0₁, hdr_enc (show kStat < 32 by decide), hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using [h256]), hm₁]
      rfl) (by decide) (by decide) (by decide +kernel))
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hf]; rfl, (k₁.trans k).mono (by decide)⟩
  · simp only [Bool.not_eq_false'] at hf
    have hI' : s₁.mem.readW (B + BitVec.ofNat 64 (8 * fIdx)) 64 = BitVec.ofNat 64 i := by rw [hm₁]; exact hI
    have hC' : s₁.mem.readW (B + BitVec.ofNat 64 (8 * fChecks)) 64 = BitVec.ofNat 64 K := by rw [hm₁]; exact hC
    refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x7] (Q := fun t => t.mem =
        (s₁.mem.writeW (off B (8 * fIdx)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))) (by
      brun [h0₁, hdr_enc (show fIdx < 32 by decide), hdr_enc (show fChecks < 32 by decide),
        hdr_enc (show kStat < 32 by decide), hs₁.ld (d := 8 * fIdx) (by simp only [fIdx]; omega_using [h256]),
        hs₁.ld (d := 8 * fChecks) (by simp only [fChecks]; omega_using [h256]),
        hs₁.st (d := 8 * fIdx) (by simp only [fIdx]; omega_using [h256]), hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using [h256]),
        hI', hC', subs_carry]
      have e1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add _ _).symm
      rw [e1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show K < 2 ^ 64 by omega_using [hK]),
        Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega_using [hi])]
      by_cases hc : i + 1 < K
      · rw [decide_eq_false (by omega_using [hc])]; simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl
      · rw [decide_eq_true (by omega_using [hc])]; simp only [hc, ↓reduceIte]; rfl) (by decide) (by decide) (by decide +kernel))
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hm₁, hf]; rfl, (k₁.trans k).mono (by decide)⟩

/-- A round of an accepted witness `a`. -/
theorem round_ok (M : Mont) (R : Kernel) {s : State} {B : Addr} {Z w c bm a i K : Nat} (hw4 : 4 ≤ w)
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aX) w = a) (ha : a < c)
    (hI : word s.mem B (8 * fIdx) = BitVec.ofNat 64 i) (hC : word s.mem B (8 * fChecks) = BitVec.ofNat 64 K)
    (hi : i < 2 ^ 62) (hK : K < 2 ^ 62) :
    WP isa (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.round M.mm R.run)) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64
        (if Proof.MillerRabin.Round.round c a then (if i + 1 < K then 4 else 1) else 2) ∧
      word t.mem B (8 * fIdx) = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then i + 1 else i) ∧
      Frm B (rdRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hw' : w < 2 ^ 31 := by omega_using [hw128]
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc3]
  simp only [VG.Impl.Ffdh.AArch64.ParameterCandidate.round]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) R.nonempty ?_
  simp only [seqs_one]
  -- `a R mod c` into `aXm`.
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hR2, hc.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨_, hlt₁, hy₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hy₁
  rw [hx, hR2] at hy₁
  have hXm : wv s₁.mem B (slot w aXm) w = a % c * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt ha]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₁, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₁ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]
      s.mem s₁.mem := Frm.of_arrays ha₁ (by simp)
  have hc₁ : MrCtx s₁ B Z w c bm := hc.of_frm f₁ (by kmut) k₁ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  have he₁ : ECtx s₁.mem B w c := he.of_frm f₁ (fun r hr => Or.inr (rdRanges_lt w r (by
    simp only [rdRanges]; exact List.mem_append_left _ (List.mem_append_left _ hr)))) (by omega_arith)
  have hI₁ : word s₁.mem B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₁.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (mm3_shape w) (by decide) (by decide))
      (by simp only [fIdx]; omega_arith)]; exact hI
  have hC₁ : word s₁.mem B (8 * fChecks) = BitVec.ofNat 64 K := by
    rw [f₁.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (mm3_shape w) (by decide) (by decide))
      (by simp only [fChecks]; omega_arith)]; exact hC
  -- The round.
  refine WP.mono (R.ok hc₁ he₁ hw4 hw128 hEZ hodd hc3 hXm) fun s₂ ⟨⟨bm₂, hc₂⟩, he₂, hf₂, f₂, k₂⟩ => ?_
  have hI₂ : word s₂.mem B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (sharedKernel_shape w) (by decide) (by decide))
      (by simp only [fIdx]; omega_arith)]; exact hI₁
  have hC₂ : word s₂.mem B (8 * fChecks) = BitVec.ofNat 64 K := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (sharedKernel_shape w) (by decide) (by decide))
      (by simp only [fChecks]; omega_arith)]; exact hC₁
  generalize Proof.MillerRabin.Round.round c a = f at hf₂ ⊢
  refine WP.mono (rdTail_ok hc₂.ws hf₂ hI₂ hC₂ hi hK) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * fIdx, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    cases f <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp)
    · exact (Frm.of_outside (writeW_outside s₂.mem B _ (d := 8 * fIdx) (by decide)) (by simp)).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp))
  refine ⟨⟨bm₂, hc₂.of_frm hft (by kmut) k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
    he₂.of_frm hft (fun r hr => Or.inr (rdRanges_lt w r (by
      simp only [rdRanges]; exact List.mem_append_right _ hr))) (by omega_arith), ?_, ?_, ?_,
    ((k₁.trans k₂).trans k).mono (by decide)⟩
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · rw [hm]
    cases f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hI₂
    · simp only [↓reduceIte]
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · simp only [rdRanges]
    exact ((f₁.mono fun r hr => List.mem_append_left _ (List.mem_append_left _ hr)).trans
      (f₂.mono fun r hr => List.mem_append_left _ (List.mem_append_right _ hr))).trans
      (hft.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on AArch64: a draw

`draw_ok`: the next `⌈mb / 8⌉` octets of the tape, cut to `mb` bits (the
witness `wA` of `drawWitness`), rejected (`kStat := 4`) unless in
`[2, N − 2]`, else the round (`round_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The modulus `N` of `mb` bits, its `w` words and its `K` checks. -/
structure MrDims (p : PP) (w N mb K : Nat) : Prop where
  hw : w = mW mb
  mb1 : 511 ≤ mb
  mb2 : mb ≤ 8192
  eZ : slot w aE + 8 * (w + 2) ≤ p.Z
  odd : N % 2 = 1
  n3 : 3 ≤ N
  bl : Spec.RsaKeyGen.bitLength (N - 1) = mb
  k : K < 2 ^ 62
  hL : p.L ≤ p.r.length
  mbb : mb ≤ p.bits

/-- What the witnesses of `N` keep. -/
structure MrFix (p : PP) (w N mb K : Nat) (s : State) : Prop where
  st : PSt p w s
  ctx : ∃ bm, MrCtx s p.B p.Z w N bm
  ex : ECtx s.mem p.B w N
  r2 : wv s.mem p.B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  len : word s.mem p.B (8 * kLen) = BitVec.ofNat 64 (mLen mb)
  top : word s.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK mb - 1)
  chk : word s.mem p.B (8 * fChecks) = BitVec.ofNat 64 K
  msk : word s.mem p.B (8 * Public.sMask) = mask true

/-- The witness drawn at offset `u`. -/
def wA (mb : Nat) (r : List Byte) (u : Nat) : Nat := Spec.Rsa.os2ip ((r.drop u).take (mLen mb)) % 2 ^ mb

/-- `kStat` after a draw. -/
def dStat (N K i a : Nat) : Nat :=
  if 2 ≤ a ∧ a < N - 1 then (if Spec.Ffdh.mrRound N a then (if i + 1 < K then 4 else 1) else 2) else 4

/-- `fIdx` after a draw. -/
def dIdx (N i a : Nat) : Nat := if 2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true then i + 1 else i

theorem MrFix.of_frm {p : PP} {w N mb K : Nat} {s t : State} (h : MrFix p w N mb K s)
    (hEZ : slot w aE + 8 * (w + 2) ≤ p.Z) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem) (hm : ∀ r ∈ rs, KMut r) (hp : ∀ r ∈ rs, PMut r) (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (dB : ∀ r ∈ rs, slot w aB + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aB)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1)
    (d2 : ∀ r ∈ rs, slot w aR2 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR2)
    (dE : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE)
    (dM : ∀ r ∈ rs, 8 * Public.sMask + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * Public.sMask)
    (dL : ∀ r ∈ rs, 8 * kLen + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kLen)
    (dT : ∀ r ∈ rs, 8 * fTop + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * fTop)
    (dC : ∀ r ∈ rs, 8 * fChecks + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * fChecks) : MrFix p w N mb K t := by
  obtain ⟨bm, hc⟩ := h.ctx
  have hn := hc.ws.scr.nowrap
  have hZ' := hc.ws.hZ
  have h256 := hc.ws.h256
  have hc' := hc.of_frm hf hm k hr dI dN dB d1 dm
  have sR2 : slot w aR2 + 8 * (w + 2) ≤ p.Z := by
    have := VG.Proof.Rsa.slot_lt (w := w) (show aR2 < 16 by decide); omega_using [hZ', this]
  have sE : p.B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by omega_using [hEZ, hn]
  refine ⟨h.st.step hc'.ws hf hp hZ k, ⟨bm, hc'⟩, h.ex.of_frm hf dE sE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.wv_eq d2 (by omega_using [hn, sR2])]; exact h.r2
  · rw [hf.word_eq dL (by simp only [kLen, sK, sFn]; omega_using [hn, h256])]; exact h.len
  · rw [hf.word_eq dT (by simp only [fTop]; omega_using [hn, h256])]; exact h.top
  · rw [hf.word_eq dC (by simp only [fChecks]; omega_using [hn, h256])]; exact h.chk
  · rw [hf.word_eq dM (by simp only [Public.sMask, sFn]; omega_using [hn, h256])]; exact h.msk

theorem mr_round_eq {N : Nat} (a : Nat) (hN : 3 ≤ N) (ho : N % 2 = 1) :
    Proof.MillerRabin.Round.round N a = Spec.Ffdh.mrRound N a := by
  simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq a hN ho

/-- The draw before its test. -/
def drawHead : List (Prog isa) := (draw (fun _ _ _ => .block []) []).take 9

theorem draw_eq (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa)) :
    draw mul roundCode = drawHead ++ ([.ite (.zero .x .x9) (.block [movi .x3 4, sth .x3 kStat])
      (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.round mul roundCode))] : List (Prog isa)) := rfl

/-- After `drawHead`, from `s₀`, with `i` witnesses passed and `u` octets
read before it. -/
structure DrawMid (p : PP) (w N mb K i u : Nat) (s₀ s : State) : Prop where
  fix : MrFix p w N mb K s
  used : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u + mLen mb)
  x9 : s.gpr .x9 = mask (decide (2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1))
  ax : wv s.mem p.B (slot w aX) w = wA mb p.r u
  idx : word s.mem p.B (8 * fIdx) = BitVec.ofNat 64 i
  isc : InScr p.B p.Z s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- `drawHead`: the witness and its range's mask. -/
theorem drawHead_ok {p : PP} {w N mb K i u : Nat} {s : State} (d : MrDims p w N mb K)
    (h : MrFix p w N mb K s) (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u)
    (hI : word s.mem p.B (8 * fIdx) = BitVec.ofNat 64 i) (hroom : u + mLen mb ≤ p.r.length) :
    WP isa (seqs drawHead) s (DrawMid p w N mb K i u s) := by
  have hws := h.st.ws
  have hn := hws.scr.nowrap
  have hEZ := d.eZ
  have hZ := hws.hZ
  have hw : w = mW mb := d.hw
  have hmb1 := d.mb1
  have hmb2 := d.mb2
  have hw8 : 8 ≤ w := by rw [hw]; simp only [mW]; omega_arith
  have hw128 : w ≤ 128 := by rw [hw]; simp only [mW]; omega_arith
  have hlw : mLen mb ≤ 8 * w := by rw [hw]; simp only [mLen, mW]; omega_arith
  have hl1 : 1 ≤ mLen mb := by simp only [mLen]; omega_arith
  have hk : mK mb ≤ 64 := by simp only [mK, mW]; omega_arith
  have hcut : 64 * (w - 1) + mK mb = mb := by rw [hw]; simp only [mK, mW]; omega_arith
  have sX : slot w aX + 8 * (w + 2) ≤ p.Z := by
    have := VG.Proof.Rsa.slot_lt (w := w) (show aX < 16 by decide); omega_using [hZ, this]
  unfold drawHead
  refine wp_seqs_append (a := [_, _, _]) (by simp) (by simp) ?_
  -- The octets.
  have hsrc := src_take (src_drop h.st.src u) (mLen mb)
  refine WP.mono (drawLoad_ok hws h.st.args.rand hU h.len hl1 hlw hsrc (by
    simp only [List.length_take, List.length_drop]; omega_arith)) fun s₁ ⟨hx₁, hu₁, f₁, ws₁, k₁⟩ => ?_
  have h₁ : MrFix p w N mb K s₁ := h.of_frm hEZ f₁ (by kmut)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact PMut.ofSlot _ _ _
      · exact PMut.hdr (by simp only [kUsed, sFn]; omega_arith))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sX
      · simp only [kUsed, sFn]; have := hws.h256; omega_arith)
    k₁ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
  have hI₁ : word s₁.mem p.B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fIdx]; omega_arith)]; exact hI
  -- The cut.
  refine wp_seqs_append (a := [_]) (by simp) (by simp) ?_
  rw [seqs_one]
  refine WP.mono (drawCut_ok h₁.st.ws hk h₁.top) fun s₂ ⟨hx₂, f₂, k₂⟩ => ?_
  rw [hx₁, hcut] at hx₂
  have h₂ : MrFix p w N mb K s₂ := h₁.of_frm hEZ f₂ (by kmut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sX)
    k₂ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
  have hI₂ : word s₂.mem p.B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fIdx]; omega_arith)]; exact hI₁
  have hu₂ : word s₂.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u + mLen mb) := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_arith)]; exact hu₁
  -- The range.
  obtain ⟨bm₂, hc₂⟩ := h₂.ctx
  refine WP.mono (drawRange_ok h₂.st.ws hx₂) fun s₃ ⟨h9₃, hm₃, k₃⟩ => ?_
  rw [hc₂.n] at h9₃
  have h₃ : MrFix p w N mb K s₃ := h₂.of_frm (rs := []) hEZ (by rw [hm₃]; exact Frm.refl _ _ _) (by simp) (by simp)
    (by simp) k₃ (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp)
  have hwa : wA mb p.r u = Spec.Rsa.os2ip ((p.r.drop u).take (mLen mb)) % 2 ^ mb := rfl
  rw [← hwa] at h9₃ hx₂
  have hacc : ∀ a, (decide (2 ≤ a) && decide (a + (1 - a % 2) < N)) = decide (2 ≤ a ∧ a < N - 1) := fun a => by
    rw [← Bool.decide_and]; exact decide_eq_decide.mpr (and_congr Iff.rfl (or1_lt_iff d.odd))
  rw [hacc] at h9₃
  have hU256 : 8 * kUsed + 8 ≤ p.Z := by simp only [kUsed, sFn]; have := hws.h256; omega_arith
  have hS₃ : InScr p.B p.Z s.mem s₃.mem := by
    rw [hm₃]
    refine (InScr.of_frm f₁ fun r hr => ?_).trans (InScr.of_frm f₂ fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sX
      · exact hU256
    · rw [List.mem_singleton.mp hr]; exact sX
  exact ⟨h₃, by rw [hm₃]; exact hu₂, h9₃, by rw [hm₃]; exact hx₂, by rw [hm₃]; exact hI₂, hS₃,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A draw. -/
theorem draw_ok (M : Mont) (R : Kernel) {p : PP} {w N mb K i u : Nat} {s : State} (d : MrDims p w N mb K)
    (h : MrFix p w N mb K s) (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u)
    (hI : word s.mem p.B (8 * fIdx) = BitVec.ofNat 64 i) (hi : i < 2 ^ 62) (hroom : u + mLen mb ≤ p.r.length) :
    WP isa (seqs (draw M.mm R.run)) s fun t => MrFix p w N mb K t ∧
      word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u + mLen mb) ∧
      word t.mem p.B (8 * kStat) = BitVec.ofNat 64 (dStat N K i (wA mb p.r u)) ∧
      word t.mem p.B (8 * fIdx) = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) ∧ InScr p.B p.Z s.mem t.mem ∧
      Keep mmRegs s t := by
  have hEZ := d.eZ
  have hZ := h.st.ws.hZ
  have hw : w = mW mb := d.hw
  have hmb1 := d.mb1
  have hmb2 := d.mb2
  have hw8 : 8 ≤ w := by rw [hw]; simp only [mW]; omega_arith
  have hw128 : w ≤ 128 := by rw [hw]; simp only [mW]; omega_arith
  have hle : ∀ r ∈ rdRanges w, r.1 + r.2 ≤ p.Z := fun r hr => by
    have := rdRanges_lt w r hr; omega_using [this, hEZ]
  rw [draw_eq]
  refine wp_seqs_append (by simp [drawHead, draw]) (by simp) ?_
  refine WP.mono (drawHead_ok d h hU hI hroom) fun s₃ hd => ?_
  rw [seqs_one]
  have h₃ := hd.fix
  have hu₂ := hd.used
  have h9₃ := hd.x9
  have hx₃ := hd.ax
  have hI₃ := hd.idx
  have hS₃ := hd.isc
  have k₁₃ := hd.keep
  generalize wA mb p.r u = a at h9₃ hx₃ ⊢
  have hs₃ := h₃.st.ws.scr
  have h0₃ : s₃.gpr .x0 = p.B := h₃.st.ws.x0
  refine WP.ite (!decide (2 ≤ a ∧ a < N - 1)) (by rw [eval_zero, h9₃]; cases decide (2 ≤ a ∧ a < N - 1) <;> decide)
    (fun hb => ?_) (fun hb => ?_)
  · -- Rejected.
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₃.mem.writeW (off p.B (8 * kStat)) (BitVec.ofNat 64 4)) (by
      have h256 := h₃.st.ws.h256
      brun [h0₃, hdr_enc (show kStat < 32 by decide), hs₃.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
    have ft : Frm p.B [(8 * kStat, 8)] s₃.mem t.mem := by
      rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
    refine ⟨h₃.of_frm hEZ ft (by kmut) (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [kStat, sFn]; have := h₃.st.ws.h256; omega_arith)
      k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
      (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl), ?_, ?_, ?_,
      hS₃.trans (InScr.of_frm ft fun r hr => by
        rw [List.mem_singleton.mp hr]; simp only [kStat, sFn]; have := h₃.st.ws.h256; omega_arith),
      (k₁₃.trans k).mono (by decide)⟩
    · rw [ft.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_arith)]; exact hu₂
    · rw [hm, word_writeW_self]; simp only [dStat, hb, ↓reduceIte]
    · rw [ft.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fIdx]; omega_arith), hI₃]
      have hnot : ¬(2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true) := fun h' => hb ⟨h'.1, h'.2.1⟩
      simp only [dIdx, hnot, ↓reduceIte]
  · -- The round.
    simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    obtain ⟨bm₃, hc₃⟩ := h₃.ctx
    have hn3 := d.n3
    have hw4 : 4 ≤ w := by omega_arith
    have haN : a < N := by omega_arith
    refine WP.mono (round_ok (a := a) (i := i) (K := K) M R hw4 hw128 hEZ hc₃ h₃.ex h₃.r2 d.odd d.n3 hx₃
      haN hI₃ h₃.chk hi d.k) fun t ⟨⟨bm', hct⟩, het, hst, hix, ft, k⟩ => ?_
    rw [mr_round_eq a d.n3 d.odd] at hst hix
    have hn' := hct.ws.scr.nowrap
    have hr2 : wv t.mem p.B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
      have := VG.Proof.Rsa.slot_lt (w := w) (show aR2 < 16 by decide)
      rw [ft.wv_eq (fun r hr => by have := rdRanges_arr w (j := aR2) (by decide) r hr; omega_arith)
        (by omega_using [hn', hZ, this])]
      exact h₃.r2
    have hw' : ∀ {j : Nat}, j ∈ [0, 2, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27] →
        word t.mem p.B (8 * j) = word s₃.mem p.B (8 * j) := fun hj =>
      ft.word_eq (rdRanges_hdr w hj) (by
        have h256 := hct.ws.h256
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        omega_using [hj, h256, hn'])
    refine ⟨⟨h₃.st.step hct.ws ft (rdRanges_pmut w) hle k, ⟨bm', hct⟩, het, hr2,
      (hw' (j := kLen) (by decide)).trans h₃.len, (hw' (j := fTop) (by decide)).trans h₃.top,
      (hw' (j := fChecks) (by decide)).trans h₃.chk, (hw' (j := Public.sMask) (by decide)).trans h₃.msk⟩, ?_, ?_, ?_,
      hS₃.trans (InScr.of_frm ft hle), (k₁₃.trans k).mono (by decide)⟩
    · rw [hw' (j := kUsed) (by decide)]; exact hu₂
    · rw [hst]; simp only [dStat, hb, and_self, ↓reduceIte]
    · rw [hix]; simp only [dIdx, hb, true_and]

end VG.Proof.Ffdh.AArch64.ParameterCandidate
