module

public import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Slots
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrCtx
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Core
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math

/-!
# A candidate on AArch64: Miller–Rabin's squarings

`ECtx`: the exponent `E` in `aE` and the lowest set bit of `c − 1`'s lowest
nonzero word after it. `mrSq_ok`: `y := y²` (as `y R mod c`) and the flag
or'ed with `y = c − 1`; `mrLast_ok`: the same, under the mask of `σ > j`
from that bit.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- The exponent of a candidate `c`: `E` in `aE`, and after its `w` words
the lowest set bit `2^(a mod 64)` of `c − 1`'s lowest nonzero word. -/
structure ECtx (m : Mem) (B : Addr) (w c : Nat) : Prop where
  e : wv m B (slot w aE) w = mrE c
  l : word m B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64)

/-- `ECtx` survives changes away from `aE`. -/
theorem ECtx.of_frm {m m' : Mem} {B : Addr} {w c : Nat} {rs : List (Nat × Nat)} (h : ECtx m B w c)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE)
    (hn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64) : ECtx m' B w c :=
  ⟨by rw [hf.wv_eq (fun r hr => by have := hd r hr; omega) (by omega)]; exact h.e,
    by rw [hf.word_eq (fun r hr => by have := hd r hr; omega) (by omega)]; exact h.l⟩

/-- Disjointness of a range from each of a list of literal ranges of
Miller–Rabin. -/
tactic_template "w_disj" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.cons_append,
    List.nil_append, slot, hdrBytes, aN, aAcc, aTmp, aY, aXm, aB, aR1, aRm1, aE, aT0, kG, kFlag, kPlen, kV, kT0,
    sCnt, kBits, kT2, kWords, kT1, kU, sFn, sMinv]
  and_intros <;> omega_arith))

/-- The ranges of a list of literal ranges are `KMut`. -/
tactic_template "w_mut" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  and_intros <;> first | exact KMut.ofSlot _ _ _ | exact KMut.hdr (by decide)))

/-- What a squaring changes. -/
def sqRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (8 * kFlag, 8)]

/-- `sqRanges`'s ranges, in the header and in the arrays. -/
theorem sqRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(184, 8)]
    [(2, 1), (3, 1), (6, 1)] (sqRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    sqRanges, Public.aAcc, Public.aTmp, Public.aY, aAcc, aTmp, aY, sFn, kFlag, kPlen] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)

theorem mrSq_eq (mul : Nat → Nat → Nat → Prog isa) : mrSq mul =
    ([mul aY aY aY] : List (Prog isa)) ++ (eqMask aRm1 ++
      ([.block [ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15, sth .x4 kFlag]] : List (Prog isa))) := rfl

/-- `y := y²`, as `y R mod c` in `aY`: the multiplication, then the mask of
`y = c − 1` into `x15`. -/
theorem sqHead_ok (M : Mont) {s : State} {B : Addr} {Z w c bm y : Nat} (hw128 : w ≤ 128)
    (hc : MrCtx s B Z w c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) :
    WP isa (seqs (([M.mm aY aY aY] : List (Prog isa)) ++ eqMask aRm1)) s fun t =>
      MrCtx t B Z w c bm ∧ wv t.mem B (slot w aY) w = (y * y % c) * 2 ^ (64 * w) % c ∧
      t.gpr .x15 = mask (decide (y * y % c = c - 1)) ∧
      Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hw2 := hc.ws.w1
  have hw' : w < 2 ^ 31 := by omega_arith
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_arith
  refine wp_seqs_append (by simp) (by simp [eqMask, eqA]) ?_
  simp only [seqs]
  refine WP.mono (M.mm_ok hg.1 hg.2 hw2 hw' (o := aY) (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hY, hc.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨_, hlt₁, hy₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hy₁
  rw [hY] at hy₁
  have hY₁ : wv s₁.mem B (slot w aY) w = y * y % c * 2 ^ (64 * w) % c := mont_val hR hlt₁ hy₁ rfl rfl
  have hf₁ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s.mem s₁.mem :=
    Frm.of_arrays ha₁ (by simp)
  have hc₁ : MrCtx s₁ B Z w c bm := hc.of_frm hf₁ (by w_mut) k₁ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  refine WP.mono (eqMask_ok hc₁.ws (j := aRm1) (by decide)) fun t ⟨h15, hm, k⟩ => ?_
  have hlt2 : y * y % c < c := Nat.mod_lt _ hc0
  rw [hY₁, hc₁.rm1, decide_eq_decide.mpr (mont_eq_m1 hR hc1 hlt2)] at h15
  refine ⟨hc₁.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide) (by simp) (by simp)
    (by simp) (by simp) (by simp), by rw [hm]; exact hY₁, h15, by rw [hm]; exact hf₁, (k₁.trans k).mono (by decide)⟩

/-- The flag's update: `kFlag |= x15`. -/
theorem flagOr_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {P b : Bool}
    (hP : word s.mem B (8 * kFlag) = mask P) (h15 : s.gpr .x15 = mask b) :
    WP isa (.block [ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15, sth .x4 kFlag]) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kFlag)) (mask (P || b)) ∧ Keep [.x4] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  refine WP.mono (WP.keep [.x4] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kFlag)) (mask (P || b))) (by
    brun [h.x0, hdr_enc (show kFlag < 32 by decide), hs.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega),
      hs.st (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega), hP, h15, mask_or2])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨hm, k⟩

/-- `mrSq`: `y := y²` and the flag or'ed with `y = c − 1`. -/
theorem mrSq_ok (M : Mont) {s : State} {B : Addr} {Z w c bm y : Nat} {P : Bool} (hw128 : w ≤ 128)
    (hc : MrCtx s B Z w c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask P) :
    WP isa (seqs (mrSq M.mm)) s fun t =>
      MrCtx t B Z w c bm ∧ wv t.mem B (slot w aY) w = (y * y % c) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (P || decide (y * y % c = c - 1)) ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  rw [mrSq_eq, ← List.append_assoc]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (sqHead_ok M hw128 hc hodd hc1 hY) fun s₁ ⟨hc₁, hY₁, h15, hf₁, k₁⟩ => ?_
  have hP₁ : word s₁.mem B (8 * kFlag) = mask P := by
    rw [hf₁.word_eq (d := 8 * kFlag) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by have := hc.ws.hZ; simp only [slot, hdrBytes, kFlag, kPlen, sFn] at *; omega_arith)]
    exact hP
  simp only [seqs]
  refine WP.mono (flagOr_ok hc₁.ws hP₁ h15) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kFlag, 8)] s₁.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by decide)) (by simp)
  refine ⟨hc₁.of_frm hft (by w_mut) k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl),
    ?_, by rw [hm, word_writeW_self], ?_, (k₁.trans k).mono (by decide)⟩
  · have hZ8 := hc₁.good.2
    rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith)]; exact hY₁
  · exact (hf₁.mono (by simp [sqRanges])).trans (hft.mono (by simp [sqRanges]))

theorem sigK_and (j : Nat) (hj : 1 ≤ j ∧ j ≤ 3) {k : Nat} (hk : k < 64) :
    (BitVec.twoPow 64 k &&& BitVec.ofNat 64 (sigK j) = 0) = ¬ (j < sigOf k) := by
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl
  · exact sig_mask1 k hk
  · exact sig_mask2 k hk
  · exact sig_mask3 k hk

/-- `ldK j`: `x4 := sigK j`. -/
theorem ldK_ok (s : State) (j : Nat) :
    WP isa (.block (ldK j)) s fun t => (t.gpr .x4 = BitVec.ofNat 64 (sigK j) ∧ t.mem = s.mem) ∧ Keep [.x4] s t := by
  unfold ldK
  generalize sigK j = K
  refine WP.keep [.x4] ?_ rfl rfl rfl
  brun [exec_movz_x' (show 0 < 4 by decide), exec_movk_x (show 1 < 4 by decide), exec_movk_x (show 2 < 4 by decide),
    exec_movk_x (show 3 < 4 by decide), movk_word]

theorem ofNat_shl3 {x : Nat} (hx : x < 2 ^ 60) : BitVec.ofNat 64 x <<< 3 = BitVec.ofNat 64 (8 * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega_arith), Nat.mul_comm]

theorem csel_mask_pos (c : Bool) :
    (if c then BitVec.setWidth 64 (0#16) - 1#64 else BitVec.setWidth 64 (0#16)) = mask c := by
  cases c <;> rfl

theorem mask_and3 (a b : Bool) : mask a &&& mask b = mask (a && b) := by cases a <;> cases b <;> decide

/-- The flag's update after a last squaring: `kFlag |= x15 & mask (σ > j)`. -/
def lastTail (j : Nat) : List Instr :=
  ws ++ (base aE .x16 ++ (([.lsl .x .x5 .x12 3, .add .x .x16 .x16 .x5, ld .x3 .x16] : List Instr) ++ (ldK j ++
    ([.logic .and .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0, .subImm .x .x8 .x7 1,
      .csel .x .x6 .x8 .x7, .logic .and .x .x15 .x15 .x6, ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15, sth .x4 kFlag] :
      List Instr))))

theorem mrLast_eq (mul : Nat → Nat → Nat → Prog isa) (j : Nat) :
    mrLast mul j = ([mul aY aY aY] : List (Prog isa)) ++ (eqMask aRm1 ++
      ([.block (lastTail j)] : List (Prog isa))) := by
  simp only [mrLast, lastTail, List.append_assoc]

theorem lastTail_ok {s : State} {B : Addr} {Z w c : Nat} (h : Ws s B Z w) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hE : ECtx s.mem B w c) {P b : Bool} (hP : word s.mem B (8 * kFlag) = mask P) (h15 : s.gpr .x15 = mask b)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (.block (lastTail j)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kFlag)) (mask (P || (b && decide (j < mrSig c)))) ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x15, .x16] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  unfold lastTail
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aE .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have h12₂ : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  rw [WP.block_append_iff]
  have hL : word s₂.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by rw [m₂, m₁]; exact hE.l
  refine WP.mono (WP.keep [.x5, .x16, .x3] (Q := fun t => t.gpr .x3 = BitVec.twoPow 64 (mrA c % 64) ∧
      t.mem = s₂.mem) (by
    brun [h16, h12₂, ofNat_shl3 (show w < 2 ^ 60 by omega_arith), off_add,
      (hs.congr (k₁.trans k₂).wr).ld (d := slot w aE + 8 * w) (by omega_arith), hL])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h3, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldK_ok s₃ j) fun s₄ ⟨⟨h4, m₄⟩, k₄⟩ => ?_
  have h3₄ : s₄.gpr .x3 = BitVec.twoPow 64 (mrA c % 64) := (k₄.gpr .x3 (by decide)).trans h3
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have h0₄ : s₄.gpr .x0 = B := (k14.gpr .x0 (by decide)).trans h.x0
  have h15₄ : s₄.gpr .x15 = mask b := (k14.gpr .x15 (by decide)).trans h15
  have hP₄ : word s₄.mem B (8 * kFlag) = mask P := by rw [m₄, m₃, m₂, m₁]; exact hP
  have hσ : (!decide (BitVec.twoPow 64 (mrA c % 64) &&& BitVec.ofNat 64 (sigK j) = 0)) = decide (j < mrSig c) := by
    have e := sigK_and j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
    rw [sigOf_mod] at e
    unfold mrSig; simp only [e, decide_not, Bool.not_not]
  have hs₄ := hs.congr k14.wr
  refine WP.mono (WP.keep [.x3, .x4, .x6, .x7, .x8, .x15] (Q := fun t => t.mem = s₄.mem.writeW (off B (8 * kFlag))
      (mask (P || (b && decide (j < mrSig c))))) (by
    brun [h0₄, h3₄, h4, h15₄, hdr_enc (show kFlag < 32 by decide),
      hs₄.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega), hs₄.st (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega),
      hP₄, subs_one_c, hσ, csel_mask_pos, mask_and3, mask_or2])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  exact ⟨by rw [hm, m₄, m₃, m₂, m₁], (k14.trans k).mono (by decide)⟩

/-- `mrLast j`: `y := y²` and the flag or'ed with `y = c − 1` if `σ > j`. -/
theorem mrLast_ok (M : Mont) {s : State} {B : Addr} {Z w c bm y : Nat} {P : Bool} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1)
    (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask P)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (mrLast M.mm j)) s fun t =>
      MrCtx t B Z w c bm ∧ wv t.mem B (slot w aY) w = (y * y % c) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (P || (decide (y * y % c = c - 1) && decide (j < mrSig c))) ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  rw [mrLast_eq, ← List.append_assoc]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (sqHead_ok M hw128 hc hodd hc1 hY) fun s₁ ⟨hc₁, hY₁, h15, hf₁, k₁⟩ => ?_
  have hP₁ : word s₁.mem B (8 * kFlag) = mask P := by
    rw [hf₁.word_eq (d := 8 * kFlag) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by have := hc.ws.hZ; simp only [slot, hdrBytes, kFlag, kPlen, sFn] at *; omega_arith)]
    exact hP
  have hE₁ : ECtx s₁.mem B w c := hE.of_frm hf₁ (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (by simp only [slot, aE] at *; omega_arith)
  simp only [seqs]
  refine WP.mono (lastTail_ok hc₁.ws hEZ hE₁ hP₁ h15 hj) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kFlag, 8)] s₁.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by decide)) (by simp)
  refine ⟨hc₁.of_frm hft (by w_mut) k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl),
    ?_, by rw [hm, word_writeW_self], ?_, (k₁.trans k).mono (by decide)⟩
  · have hZ8 := hc₁.good.2
    rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith)]; exact hY₁
  · exact (hf₁.mono (by simp [sqRanges])).trans (hft.mono (by simp [sqRanges]))

end VG.Proof.RsaKeyGen.AArch64
