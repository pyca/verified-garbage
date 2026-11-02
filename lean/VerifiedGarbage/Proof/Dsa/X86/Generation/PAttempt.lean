module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PX
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Arith
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Copy
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # One counter of p's search (A.1.1.2 steps 11.1–11.8)

The candidate of the counter's offset, its bit-length guard, and its
probable-prime test. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

/-- The candidate at `offset` for seed `k` and q `Q`. -/
def pcand (g : Geo) (E : Env) (k offset Q : Nat) : Nat :=
  Spec.Dsa.pCandidate (8 * g.pLen) (8 * g.qLen) Q (chunk E k) offset

/-- `fP` after a tested candidate: 0 if the witnesses ran out, 1 for a
probable prime, and 4, still searching, for a composite. -/
def pCode : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 4

/-- The ranges a counter changes. -/
def paRanges (g : Geo) : List (Nat × Nat) :=
  pxRanges g ++ aRanges g.pLen ++ [(sPP, 8 * ppWords), (fRes, 4), (fUsed, 4), (fUsedOut, 8), (fP, 4)]

theorem paRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (paRanges g) := by
  have sz := v.size_ge
  have b := G.bounds
  intro o ho
  simp only [paRanges, pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sState, sX, arr, sPk, sPP, ppWords, fRes, fUsed, fUsedOut, fP, fOut, fWitLen, hdr] <;> omega

/-- After a counter. -/
structure PAPost (E : Env) (g : Geo) (k offset Q used : Nat) (s t : State) : Prop where
  base : Base E t
  pk : Spec.Rsa.bytesAt t.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen (pcand g E k offset Q)
  pm1 : val32 t.mem E.base aPm1 (g.pLen / 4) = pcand g E k offset Q - 1
  e : val32 t.mem E.base aE (g.pLen / 4) = (pcand g E k offset Q - 1) / Q
  pv : val32 t.mem E.base aP (g.pLen / 4) = pcand g E k offset Q
  one : val32 t.mem E.base aOne (g.pLen / 4) = 1
  fp : t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32
    (if pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) then 4
      else pCode (Spec.Dsa.probablePrime (pcand g E k offset Q) (E.witT.drop used)))
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32
    (if pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) then used
      else nextUsed E.witLen used (Spec.Dsa.probablePrime (pcand g E k offset Q) (E.witT.drop used)))
  chg : E.Chg (paRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The top bit of a byte, as `and eax, 0x80; cmp eax, 0` tests it. -/
theorem and80 (b : Byte) :
    ((b.setWidth 32 &&& (0x80 : BitVec 32)) - 0 == 0) = decide (b.toNat < 128) := by
  have hb := b.isLt
  have key : ∀ x < 256, (x &&& 128 = 0 ↔ x < 128) := by decide +kernel
  have e : ((b.setWidth 32 &&& (0x80 : BitVec 32)) - 0).toNat = b.toNat &&& 128 := by
    rw [BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_setWidth]
    show (2 ^ 32 - 0 + (b.toNat % 2 ^ 32 &&& 128)) % 2 ^ 32 = b.toNat &&& 128
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
    have : b.toNat &&& 128 < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left (by omega)
    omega
  by_cases h : b.toNat < 128
  · simp only [h, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [e, (key _ hb).mpr h]; rfl)
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [e] at this
    exact h ((key _ hb).mp this)

theorem status_lt (r : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status r < 2 ^ 32 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp [Proof.Dsa.ProbablePrime.status]

theorem pCode_zero {r : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status r = 0) :
    pCode r = 0 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status, pCode]

theorem pCode_one {r : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status r = 1) :
    pCode r = 1 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status, pCode]

theorem pCode_other {r : Option (Bool × Spec.RsaKeyGen.Rand)} (h₀ : Proof.Dsa.ProbablePrime.status r ≠ 0)
    (h₁ : Proof.Dsa.ProbablePrime.status r ≠ 1) : pCode r = 4 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp_all [Proof.Dsa.ProbablePrime.status, pCode]

/-- After X, p and its guard: the guard's flag, p and its arrays, and the
state words the test reads. -/
structure PAFront (E : Env) (g : Geo) (k offset Q used : Nat) (s t : State) : Prop where
  base : Base E t
  zf : isa.eval .e t = some (decide (pcand g E k offset Q < 2 ^ (8 * g.pLen - 1)))
  pk : Spec.Rsa.bytesAt t.mem (off E.base sPk) g.pLen = Spec.Dsa.encodeBE g.pLen (pcand g E k offset Q)
  pm1 : val32 t.mem E.base aPm1 (g.pLen / 4) = pcand g E k offset Q - 1
  e : val32 t.mem E.base aE (g.pLen / 4) = (pcand g E k offset Q - 1) / Q
  pv : val32 t.mem E.base aP (g.pLen / 4) = pcand g E k offset Q
  one : val32 t.mem E.base aOne (g.pLen / 4) = 1
  fp : t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4
  used : t.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used
  chg : E.Chg (paRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms
  odd : pcand g E k offset Q % 2 = 1
  lt : pcand g E k offset Q < 2 ^ (8 * g.pLen)

/-- p from X, and the guard `p ≥ 2^(L − 1)`. -/
theorem paMid_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t₁ : State} {k offset : Nat}
    (X₁ : XPost E g k offset s t₁) {Q : Nat}
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q) (hQ0 : 0 < Q)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used)
    (hP4 : s.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4) :
    WP isa (.seq (pArith g.pLen g.qLen)
      (.block [.movzx8 .eax (sc sPk), .alu .and .eax (.imm 0x80), .alu .cmp .eax (.imm 0)])) t₁
      (PAFront E g k offset Q used s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have Apa := paRanges_apart G v
  have hQ₁ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₁.mem (off E.base (sPk + g.pLen)) g.qLen) = Q := by
    rw [Env.Chg.scratch v X₁.chg (by simp only [sPk]; omega) fun o ho => by
      simp only [pxRanges, List.mem_singleton] at ho; subst ho
      exact ⟨by simp only [sState, sX]; omega, by left; simp only [sState, sX, sPk]; omega⟩, hQ]
  -- p.
  have lens : g.pLen = 128 ∨ g.pLen = 256 ∨ g.pLen = 384 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  refine WP.seq (VG.X86.WP.mono_syms (pArith_ok lens ⟨bd.1, bd.2.1⟩ X₁.base.scr sz X₁.x hQ₁ hQ0)
    fun t₂ ⟨P₂, E₂, V₂, K₂, O₂, Kr₂, One₂⟩ sy₂ => ?_)
  have hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * g.qLen) bs).length = 8 * g.qLen := fun bs => by
    rw [← G.seedHash, G.hash.hash_length, G.N]
  have pEq : Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) -
      Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) % (2 * Q) + 1 =
      pcand g E k offset Q := by
    unfold pcand
    rw [pCandidate_shaped (by omega) hlen]
    have := Nat.mod_le (Spec.Ffdh.candidateOf (8 * g.pLen)
      (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1))) (2 * Q)
    show _ = Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) + 1 -
      Spec.Ffdh.candidateOf (8 * g.pLen)
        (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) % (2 * Q)
    omega
  have Xsh := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := 8 * g.pLen) (by omega)
    (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1))
  generalize Spec.Ffdh.candidateOf (8 * g.pLen)
    (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) = X
    at P₂ E₂ V₂ K₂ pEq Xsh
  generalize hpc : pcand g E k offset Q = pc at pEq
  have dm := Nat.div_add_mod X (2 * Q)
  have ml := Nat.mod_le X (2 * Q)
  have dQ : 2 * Q * (X / (2 * Q)) = 2 * (Q * (X / (2 * Q))) := Nat.mul_assoc _ _ _
  have pcOdd : pc % 2 = 1 := by omega
  have pcLt : pc < 2 ^ (8 * g.pLen) := by omega
  have e256 : (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) := by rw [Nat.pow_mul]
  rw [pEq] at V₂ K₂
  rw [show X - X % (2 * Q) = pc - 1 by omega] at P₂ E₂
  -- What changed so far.
  have Aa : E.Apart (aRanges g.pLen) := fun o ho => Apa o
    (List.mem_append_left _ (List.mem_append_right _ ho))
  have Ca : E.Chg (aRanges g.pLen) t₁.mem t₂.mem := Env.Chg.of_frame
    (VG.Proof.Bignum.outs_frame O₂ fun r hr => by
      simp only [aRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [arr, sPk] <;> omega) fun r hr => by
    simp only [List.mem_map] at hr
    obtain ⟨o, ho, rfl⟩ := hr
    exact Env.in_range ho (Nat.le_refl _) (Nat.le_refl _)
  have B₂ : Base E t₂ := X₁.base.keep v Ca Aa (Kr₂.1 _ (by decide)) (Kr₂.1 _ (by decide)) Kr₂.2.1 Kr₂.2.2 sy₂
  have C₂' : E.Chg (pxRanges g ++ aRanges g.pLen) s.mem t₂.mem :=
    (X₁.chg.widen fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩).trans
      (Ca.widen fun o ho => ⟨o, List.mem_append_right _ ho, Nat.le_refl _, Nat.le_refl _⟩)
  have inPa : ∀ o ∈ pxRanges g ++ aRanges g.pLen, ∃ o' ∈ paRanges g, o'.1 ≤ o.1 ∧ o.1 + o.2 ≤ o'.1 + o'.2 :=
    fun o ho => ⟨o, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩
  have C₂ : E.Chg (paRanges g) s.mem t₂.mem := C₂'.widen inPa
  have word₂ : ∀ d, d + 4 ≤ sState → t₂.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    fun d hd => Env.Chg.word v C₂' (by simp only [sState] at hd; omega) fun o ho => by
      simp only [pxRanges, aRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [sState, sX, arr, sPk] at hd ⊢ <;> omega
  have hP₂ : t₂.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
    rw [word₂ fP (by simp only [fP, hdr, sState]; omega), hP4]
  have hU₂ : t₂.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [word₂ fUsed (by simp only [fUsed, hdr, sState]; omega), hU]
  -- The guard `p ≥ 2^(L − 1)`, by p's first byte.
  have hb : t₂.mem (off E.base sPk) = (Spec.Dsa.encodeBE g.pLen pc).getD 0 0 := by
    have := congrArg (fun l : List Byte => l.getD 0 0) K₂
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show 0 < g.pLen by omega), Option.map_some, Option.getD_some] at this
    rw [List.getD_eq_getElem?_getD, ← this, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have top : (t₂.mem (off E.base sPk)).toNat < 128 ↔ pc < 2 ^ (8 * g.pLen - 1) := by
    rw [hb]; exact candidate_firstByte (by omega) (by rw [e256]; exact pcLt)
  refine ld8_ok B₂.scr (d := sPk) (by simp only [sPk]; omega) fun s₃ u₃ => wp_andi fun s₄ u₄ =>
    wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ?_
  have zf₅ : isa.eval .e s₅ = some (decide ((t₂.mem (off E.base sPk)).toNat < 128)) := by
    show s₅.zf = _
    rw [z₅, u₄.gpr, u₃.gpr, and80]
  have m₅ : s₅.mem = t₂.mem := by rw [f₅.mem, u₄.mem, u₃.mem]
  have regs₅ : ∀ r, r ≠ .eax → s₅.gpr r = t₂.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr, u₃.other r hr]
  have rd₅ : s₅.rd = t₂.rd := by rw [f₅.rd, u₄.rd, u₃.rd]
  have wr₅ : s₅.wr = t₂.wr := by rw [f₅.wr, u₄.wr, u₃.wr]
  have sy₅ : s₅.syms = t₂.syms := by rw [f₅.syms, u₄.syms, u₃.syms]
  have B₅ : Base E s₅ := B₂.regs m₅ (regs₅ _ (by decide)) (regs₅ _ (by decide)) rd₅ wr₅ sy₅
  have rd₂ : t₂.rd = s.rd := by rw [Kr₂.2.1, X₁.rd]
  have wr₂ : t₂.wr = s.wr := by rw [Kr₂.2.2, X₁.wr]
  have sy₂s : t₂.syms = s.syms := by rw [sy₂, X₁.syms]
  subst hpc
  refine ⟨B₅, by rw [zf₅]; exact congrArg some (decide_eq_decide.mpr top), by rw [m₅]; exact K₂,
    by rw [m₅]; exact P₂, by rw [m₅]; exact E₂, by rw [m₅]; exact V₂, by rw [m₅]; exact One₂,
    by rw [m₅]; exact hP₂, by rw [m₅]; exact hU₂, by rw [m₅]; exact C₂, by rw [rd₅, rd₂], by rw [wr₅, wr₂],
    by rw [sy₅, sy₂s], pcOdd, pcLt⟩

theorem pAttempt_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid)
    (hq : E.qLen = g.qLen) {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {offset : Nat} (hO : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset)
    (hoff : offset + g.count + 256 ≤ 2 ^ 32) {Q : Nat}
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off E.base (sPk + g.pLen)) g.qLen) = Q) (hQ0 : 0 < Q)
    {used : Nat} (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used) (hu : used ≤ E.witLen)
    (hP4 : s.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4) :
    WP isa g.pAttempt s (PAPost E g k offset Q used s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have Apa := paRanges_apart G v
  unfold Geo.pAttempt
  simp only [seqs]
  refine WP.seq (WP.mono (pX_ok G v hq B hk hS hO hoff) fun t₁ X₁ =>
    WP.assoc (WP.seq (WP.mono (paMid_ok G v X₁ hQ hQ0 hU hP4) fun s₅ F => ?_)))
  have B₅ := F.base
  refine WP.ite (decide (pcand g E k offset Q < 2 ^ (8 * g.pLen - 1))) F.zf (fun hlo => WP.block_nil ?_) (fun hhi => ?_)
  · -- Below `2^(L − 1)`: skipped.
    have hlt : pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) := of_decide_eq_true hlo
    refine ⟨B₅, F.pk, F.pm1, F.e, F.pv, F.one, ?_, ?_, F.chg, F.rd, F.wr, F.syms⟩
    · simp only [F.fp, hlt, ↓reduceIte]
    · simp only [F.used, hlt, ↓reduceIte]
  -- At least `2^(L − 1)`: tested.
  have hge : ¬ pcand g E k offset Q < 2 ^ (8 * g.pLen - 1) := of_decide_eq_false hhi
  have pcOdd := F.odd
  have pcLt := F.lt
  have e256 : (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) := by rw [Nat.pow_mul]
  have lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
  have candLe : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate + g.pLen ≤ 8 * ppWords := by
    simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at lay ⊢; omega_arith
  have szT : VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width (8 * g.pLen)) ≤
      8 * ppWords := by simp only [VG.Impl.Dsa.X86.ProbablePrime.layout] at candLe; omega_arith
  refine WP.seq (VG.X86.WP.mono_syms (copyS_ok B₅.scr
    (dst := sPP + (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).candidate) (src := sPk) (n := g.pLen)
    (by omega_arith) (by simp only [sPP, ppWords] at candLe ⊢; omega_arith) (by simp only [sPk]; omega_arith)
    (by right; simp only [sPP, sPk]; omega_arith)) fun t₆ ⟨R₆, F₆, K₆⟩ sy₆ => ?_)
  have pp : (sPP, 8 * ppWords) ∈ paRanges g := by simp [paRanges]
  have C₆ : E.Chg [(sPP, 8 * ppWords)] s₅.mem t₆.mem := Env.Chg.of_frame F₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range (List.mem_singleton_self _) (by omega_arith) (by omega_arith)
  have App : E.Apart [(sPP, 8 * ppWords)] := fun o ho => Apa o (by simp only [List.mem_singleton] at ho; rw [ho]; exact pp)
  have B₆ : Base E t₆ := B₅.keep v C₆ App (K₆.1 _ (by decide)) (K₆.1 _ (by decide)) K₆.2.1 K₆.2.2 sy₆
  have hU₆ : t₆.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 used := by
    rw [Env.Chg.word v C₆ (by simp only [fUsed, hdr]; omega_arith) (fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sPP, ppWords, fUsed, hdr]; omega_arith), F.used]
  have hP₆ : t₆.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 4 := by
    rw [Env.Chg.word v C₆ (by simp only [fP, hdr]; omega_arith) (fun o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [sPP, ppWords, fP, hdr]; omega_arith), F.fp]
  have cval : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)) t₆.mem
      (off E.base sPP) = pcand g E k offset Q := by
    unfold Proof.Dsa.ProbablePrime.candidateAt
    have b8 : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.pLen)).bits / 8 = g.pLen := by
      show 8 * g.pLen / 8 = g.pLen; omega_arith
    rw [b8, VG.Offset.add_add, R₆, F.pk, decodeBE_encodeBE (by rw [e256]; exact pcLt)]
  have plen : Spec.Dsa.bitLength (pcand g E k offset Q) = 8 * g.pLen :=
    (bitLength_iff_bounds (by omega_arith)).mpr ⟨by omega_arith, pcLt⟩
  refine WP.seq (VG.X86.WP.mono_syms (test_ok G.pv G.pNoSp G.pStack v B₆ hU₆ hu lay (by rw [cval]; exact pcOdd)
    (by rw [cval]; exact plen)) fun t₇ P sy₇ => ?_)
  rw [cval] at P
  obtain ⟨r, hr⟩ : ∃ r, Spec.Dsa.probablePrime (pcand g E k offset Q) (E.witT.drop used) = r := ⟨_, rfl⟩
  have res₇ := P.res
  have used₇ := P.used
  rw [hr] at res₇ used₇
  -- The ranges the test changed are the counter's.
  have Cp : E.Chg (paRanges g) s.mem t₇.mem := by
    refine (F.chg.trans (C₆.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact pp,
      Nat.le_refl _, Nat.le_refl _⟩)).trans (P.chg.widen fun o ho => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact ⟨_, pp, Nat.le_refl _, by omega_arith⟩
    · exact ⟨_, by simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩
  have testR : ∀ o ∈ [(sPP, VG.Impl.Dsa.X86.ProbablePrime.scratchBytes (VG.Impl.Dsa.X86.ProbablePrime.width
      (8 * g.pLen))), (fRes, 4), (fUsed, 4), (fUsedOut, 8)], o.1 + o.2 ≤ E.size := fun o ho => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, ppWords, fRes, fUsed, fUsedOut, hdr] at szT ⊢ <;> omega_arith
  have keep7 : ∀ {d k : Nat}, d + 4 * k ≤ sPP → 7400 ≤ d →
      val32 t₇.mem E.base d k = val32 s₅.mem E.base d k := fun h₁ h₂ => by
    rw [Env.Chg.val32 v P.chg (by simp only [sPP] at h₁; omega_arith) fun o ho => ⟨testR o ho, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, fRes, fUsed, fUsedOut, hdr] at h₁ h₂ ⊢ <;> omega_arith⟩,
      (outside_of_frame F₆ (by simp only [sPP, ppWords] at candLe ⊢; omega_arith)).val32
        (by left; simp only [sPP] at h₁ ⊢; omega_arith) (by simp only [sPP] at h₁; omega_arith)]
  have fin : ∀ t : State, Base E t → E.Chg [(fP, 4)] t₇.mem t.mem →
      t.mem.readW (off E.base fP) 32 = BitVec.ofNat 32 (pCode r) → t.rd = t₇.rd → t.wr = t₇.wr →
      t.syms = t₇.syms → PAPost E g k offset Q used s t := by
    intro t Bt Ct fpt rdt wrt syt
    have fPR : ∀ {d n : Nat}, d + n ≤ fP ∨ fP + 4 ≤ d → d + n ≤ E.size →
        ∀ o ∈ [(fP, 4)], o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + n ≤ o.1) := fun h₁ h₂ o ho => by
      simp only [List.mem_singleton] at ho; subst ho; simp only [fP, hdr] at h₁ ⊢; omega_arith
    have arrV : ∀ {d : Nat}, d + 4 * (g.pLen / 4) ≤ sPP → 7400 ≤ d →
        val32 t.mem E.base d (g.pLen / 4) = val32 s₅.mem E.base d (g.pLen / 4) := fun h₁ h₂ => by
      rw [Env.Chg.val32 v Ct (by simp only [sPP] at h₁; omega_arith) (fPR (by right; simp only [fP, hdr]; omega_arith)
        (by simp only [sPP] at h₁; omega_arith)), keep7 h₁ h₂]
    refine ⟨Bt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Cp.trans (Ct.widen fun o ho => ⟨o, by
        simp only [List.mem_singleton] at ho; rw [ho]; simp [paRanges], Nat.le_refl _, Nat.le_refl _⟩),
      by rw [rdt, P.rd, K₆.2.1, F.rd], by rw [wrt, P.wr, K₆.2.2, F.wr],
      by rw [syt, P.syms, sy₆, F.syms]⟩
    · rw [Env.Chg.scratch v Ct (by simp only [sPk]; omega_arith) (fPR (by right; simp only [fP, sPk, hdr]; omega_arith)
        (by simp only [sPk]; omega_arith)),
        Env.Chg.scratch v P.chg (by simp only [sPk]; omega_arith) (fun o ho => ⟨testR o ho, by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, sPk, fRes, fUsed, fUsedOut, hdr] <;> omega_arith⟩),
        frame_bytes F₆ (by right; simp only [sPP, sPk]; omega_arith) (by simp only [sPP, ppWords] at candLe ⊢; omega_arith)
          (by simp only [sPk]; omega_arith), F.pk]
    · rw [arrV (by simp only [aPm1, arr, sPP]; omega_arith) (by simp only [aPm1, arr]; omega_arith), F.pm1]
    · rw [arrV (by simp only [aE, arr, sPP]; omega_arith) (by simp only [aE, arr]; omega_arith), F.e]
    · rw [arrV (by simp only [aP, arr, sPP]; omega_arith) (by simp only [aP, arr]; omega_arith), F.pv]
    · rw [arrV (by simp only [aOne, arr, sPP]; omega_arith) (by simp only [aOne, arr]; omega_arith), F.one]
    · simp only [hge, ↓reduceIte, hr]; exact fpt
    · simp only [hge, ↓reduceIte, hr]
      rw [Env.Chg.word v Ct (by simp only [fUsed, hdr]; omega_arith) (fPR (by left; simp only [fUsed, fP, hdr]; omega_arith)
        (by simp only [fUsed, hdr]; omega_arith)), used₇]
  have Afp : E.Apart [(fP, 4)] := fun o ho => Apa o (by simp only [List.mem_singleton] at ho; rw [ho]; simp [paRanges])
  have store : ∀ (u u' : State) (c : Nat), Base E u → u.mem = t₇.mem →
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) → u'.mem = u.mem.writeW (off E.base fP) (BitVec.ofNat 32 c) →
      u'.rd = u.rd → u'.wr = u.wr → u'.syms = u.syms → u.rd = t₇.rd → u.wr = t₇.wr → u.syms = t₇.syms →
      c = pCode r → PAPost E g k offset Q used s u' := by
    intro u u' c Bu mu gu mu' rdu wru syu rdu₇ wru₇ syu₇ hc
    have Cu : E.Chg [(fP, 4)] t₇.mem u'.mem := by
      rw [mu', mu]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) _
    refine fin u' (Bu.keep v (by rw [mu]; exact Cu) Afp (gu _ (by decide)) (gu _ (by decide)) rdu wru syu) Cu
      (by rw [mu', Mem.readW_writeW_self32, hc]) (by rw [rdu, rdu₇]) (by rw [wru, wru₇]) (by rw [syu, syu₇])
  refine WP.seq (cmpF_end P.base.scr (o := fRes) (v := 0) (by simp only [fRes, hdr]; omega_arith) res₇ (status_lt r)
    (by decide) fun s₈ g₈ m₈ rd₈ wr₈ sy₈ z₈ => ?_)
  have B₈ : Base E s₈ := P.base.regs m₈ (g₈ _ (by decide)) (g₈ _ (by decide)) rd₈ wr₈ sy₈
  refine WP.ite _ z₈ (fun h0 => stImm_end B₈.scr (o := fP) (v := 0) (by simp only [fP, hdr]; omega_arith)
    fun s₉ g₉ m₉ rd₉ wr₉ sy₉ => store s₈ s₉ 0 B₈ m₈ g₉ m₉ rd₉ wr₉ sy₉ rd₈ wr₈ sy₈
      (pCode_zero (of_decide_eq_true h0)).symm) (fun h0 => ?_)
  refine WP.seq (cmpF_end B₈.scr (o := fRes) (v := 1) (by simp only [fRes, hdr]; omega_arith) (by rw [m₈]; exact res₇)
    (status_lt r) (by decide) fun s₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ sy₁₀ z₁₀ => ?_)
  have B₁₀ : Base E s₁₀ := B₈.regs m₁₀ (g₁₀ _ (by decide)) (g₁₀ _ (by decide)) rd₁₀ wr₁₀ sy₁₀
  refine WP.ite _ z₁₀ (fun h1 => stImm_end B₁₀.scr (o := fP) (v := 1) (by simp only [fP, hdr]; omega_arith)
    fun s₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ => store s₁₀ s₁₁ 1 B₁₀ (by rw [m₁₀, m₈]) g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁
      (by rw [rd₁₀, rd₈]) (by rw [wr₁₀, wr₈]) (by rw [sy₁₀, sy₈]) (pCode_one (of_decide_eq_true h1)).symm)
    (fun h1 => WP.block_nil ?_)
  -- A composite: `fP` stays 4.
  have m : s₁₀.mem = t₇.mem := by rw [m₁₀, m₈]
  refine fin s₁₀ B₁₀ (by rw [m]; exact Env.Chg.refl _ _) ?_ (by rw [rd₁₀, rd₈]) (by rw [wr₁₀, wr₈])
    (by rw [sy₁₀, sy₈])
  rw [pCode_other (of_decide_eq_false h0) (of_decide_eq_false h1), m,
    Env.Chg.word v P.chg (by simp only [fP, hdr]; omega_arith) (fun o ho => ⟨testR o ho, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp only [sPP, fRes, fUsed, fUsedOut, fP, hdr] <;> omega_arith⟩), hP₆]

end VG.Proof.Dsa.X86.Generation
