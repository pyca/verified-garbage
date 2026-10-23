module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHash
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.X86.Generation.Seqs
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! # p's `X`: the hashes, shaped (A.1.1.2 steps 11.1–11.3) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Dsa.Generation

/-- `c + 1` digits of `q` bytes ending at `T`, the most significant first,
are their radix-`2^(8 q)` sum. -/
theorem digits_value (m : Mem) (p : Addr) (T q : Nat) (v : Nat → Nat) (c : Nat) (hc : (c + 1) * q ≤ T)
    (hv : ∀ j ≤ c, Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off p (T - (j + 1) * q)) q) = v j) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off p (T - (c + 1) * q)) ((c + 1) * q)) =
      contributions (8 * q) v (c + 1) := by
  induction c with
  | zero =>
    rw [contributions_succ, contributions_zero, ← hv 0 (Nat.le_refl _)]
    simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
  | succ c ih =>
    have e₁ : (c + 1 + 1) * q = q + (c + 1) * q := by rw [Nat.succ_mul, Nat.add_comm]
    have e₂ : T - (c + 1 + 1) * q + q = T - (c + 1) * q := by rw [e₁] at hc ⊢; omega
    have ho : VG.Proof.Bignum.off (off p (T - (q + (c + 1) * q))) q = off p (T - (q + (c + 1) * q) + q) :=
      off_add_ofNat p _ q
    rw [e₁, bytesAt_append, ho, ← e₁, e₂, e₁, decodeBE_append, VG.Proof.Bignum.bytesAt_length,
      ih (by rw [e₁] at hc; omega) (fun j hj => hv j (by omega)), ← e₁, hv (c + 1) (Nat.le_refl _),
      contributions_succ (k := c + 1), Nat.add_comm (v (c + 1) * _)]
    congr 2
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, Nat.mul_comm 8, Nat.mul_assoc, Nat.mul_comm q 8]

/-- Seed `k` is `qLen` bytes. -/
theorem chunk_length {E : Env} {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen) :
    (chunk E k).length = E.qLen := by
  have hl : E.seedT.length = E.seedsLen := by rw [← B.seeds, VG.Proof.Bignum.bytesAt_length]
  rw [Nat.succ_mul] at hk
  simp only [chunk, List.length_take, List.length_drop, hl]
  omega

/-- After `X`: its value, A.1.1.2's shaped hashes. -/
structure XPost (E : Env) (g : Geo) (k offset : Nat) (s t : State) : Prop where
  base : Base E t
  x : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off E.base sX) g.pLen) =
    Spec.Ffdh.candidateOf (8 * g.pLen)
      (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1))
  chg : E.Chg (pxRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem pX_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {k : Nat} (hk : (k + 1) * E.qLen ≤ E.seedsLen)
    (hS : s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (k * E.qLen)).setWidth 32)
    {offset : Nat} (hO : s.mem.readW (off E.base fOffset) 32 = BitVec.ofNat 32 offset)
    (hoff : offset + g.count + 256 ≤ 2 ^ 32) :
    WP isa g.pX s (XPost E g k offset s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have Apx := pxRanges_apart G v
  have hcq : (g.count + 1) * g.qLen ≤ sX + g.pLen := by simp only [sX]; omega_arith
  unfold Geo.pX
  rw [seqs_append_iff]
  refine WP.mono (seqs_range_ok (g.count + 1) g.pHash (fun i t => Base E t ∧
      (∀ j < i, Spec.Rsa.bytesAt t.mem (off E.base (hashAt g j)) g.qLen = pDig g (chunk E k) offset j) ∧
      E.Chg (pxRanges g) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms)
    (fun j hj t ⟨Bt, Ht, Ct, rdt, wrt, syt⟩ => ?_) s
    ⟨B, fun j hj => absurd hj (Nat.not_lt_zero _), Env.Chg.refl _ _, rfl, rfl, rfl⟩)
    fun t ⟨Bt, Ht, Ct, rdt, wrt, syt⟩ => ?_
  · -- One hash.
    have word : ∀ d, d + 4 ≤ sState → t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
      fun d hd => Env.Chg.word v Ct (by simp only [sState] at hd; omega_arith) fun o ho => ⟨(Apx o ho).1, by
        simp only [pxRanges, List.mem_singleton] at ho; subst ho; right; exact hd⟩
    have hjc : j ≤ g.count := by omega_arith
    refine WP.mono (pHash_ok G v hq Bt hk (offset := offset) (j := j) (by rw [word fSeed (by simp only [fSeed, hdr, sState]; omega_arith), hS])
      (by rw [word fOffset (by simp only [fOffset, hdr, sState]; omega_arith), hO]) (by omega_arith) hjc)
      fun t' ⟨B', H', C', rd', wr', sy'⟩ => ⟨B', fun j' hj' => ?_, Ct.trans (C'.widen fun o ho => ?_),
        rd'.trans rdt, wr'.trans wrt, sy'.trans syt⟩
    · by_cases he : j' = j
      · subst he; exact H'
      have hm : (j' + 1) * g.qLen ≤ j * g.qLen := Nat.mul_le_mul_right _ (by omega_arith)
      have hs : (j + 1) * g.qLen = j * g.qLen + g.qLen := Nat.succ_mul _ _
      have hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega_arith)
      rw [Env.Chg.scratch v C' (by simp only [hashAt, sX]; omega_arith) fun o ho => ?_, Ht j' (by omega_arith)]
      refine ⟨(hRanges_apart G v hjc o ho).1, ?_⟩
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX] <;> omega_arith
    · have hjq : (j + 1) * g.qLen ≤ (g.count + 1) * g.qLen := Nat.mul_le_mul_right _ (by omega_arith)
      have hs : (j + 1) * g.qLen = j * g.qLen + g.qLen := Nat.succ_mul _ _
      refine ⟨(sState, sX + g.pLen - sState), by simp [pxRanges], ?_⟩
      simp only [hRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp only [hashAt, sState, sHScr, sX] <;> omega_arith
  · -- The shaping.
    simp only [seqs]
    rw [show orByte (sX + g.pLen - 1) 1 = orByte (sX + g.pLen - 1) 1 ++ [] from (List.append_nil _).symm]
    refine orByte_ok Bt.scr (by simp only [sX]; omega_arith) (by decide) fun t₁ g₁ rd₁ wr₁ sy₁ m₁ =>
      orByte_ok (Scr.of_eq Bt.scr (g₁ _ (by decide)) (g₁ _ (by decide)) wr₁) (by simp only [sX]; omega_arith)
        (by decide) fun t₂ g₂ rd₂ wr₂ sy₂ m₂ => WP.block_nil ?_
    rw [m₁] at m₂
    have aEq : off E.base (sX + g.pLen - 1) = off E.base sX + BitVec.ofNat 64 (g.pLen - 1) := by
      rw [off_add_ofNat]; congr 1; omega_arith
    rw [aEq, shape_mem t.mem _ (by omega_arith) (by omega_arith)] at m₂
    have bl := VG.Proof.Bignum.bytesAt_length t.mem (off E.base sX) g.pLen
    have shaped : Spec.Rsa.bytesAt t₂.mem (off E.base sX) g.pLen =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Rsa.bytesAt t.mem (off E.base sX) g.pLen) 7 := by
      rw [m₂]
      conv => lhs; rw [← bl]
      refine VG.Proof.Dsa.Generation.qShape_memory (by omega_arith) (by omega_arith) fun i hi => ?_
      rw [bl] at hi
      simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi, Option.map_some, Option.getD_some]
    -- The value of the hashes.
    have cl := chunk_length B hk
    have digits := digits_value t.mem E.base (sX + g.pLen) g.qLen (pDigest (8 * g.qLen) (chunk E k) offset)
      g.count hcq fun j hj => by
        rw [show sX + g.pLen - (j + 1) * g.qLen = hashAt g j from rfl, Ht j (by omega_arith), pDig, pDigest, cl, hq]
    have suffix := bytesAt_suffix_value t.mem (off E.base (sX + g.pLen - (g.count + 1) * g.qLen))
      ((g.count + 1) * g.qLen - g.pLen) g.pLen
    have ho : VG.Proof.Bignum.off (off E.base (sX + g.pLen - (g.count + 1) * g.qLen))
        ((g.count + 1) * g.qLen - g.pLen) = off E.base sX := by
      rw [show VG.Proof.Bignum.off (off E.base (sX + g.pLen - (g.count + 1) * g.qLen))
        ((g.count + 1) * g.qLen - g.pLen) = off E.base (sX + g.pLen - (g.count + 1) * g.qLen +
          ((g.count + 1) * g.qLen - g.pLen)) from off_add_ofNat _ _ _]
      congr 1; omega_arith
    rw [ho, show (g.count + 1) * g.qLen - g.pLen + g.pLen = (g.count + 1) * g.qLen by omega_arith, digits,
      show (256 : Nat) ^ g.pLen = 2 ^ (8 * g.pLen) by rw [Nat.pow_mul]] at suffix
    have hne : Spec.Rsa.bytesAt t.mem (off E.base sX) g.pLen ≠ [] := by
      intro h; rw [h] at bl; simp only [List.length_nil] at bl; omega_arith
    have xv : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t₂.mem (off E.base sX) g.pLen) =
        Spec.Ffdh.candidateOf (8 * g.pLen)
          (contributions (8 * g.qLen) (pDigest (8 * g.qLen) (chunk E k) offset) (g.count + 1)) := by
      rw [shaped, decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value hne (by decide)
        (show 8 * g.pLen = _ by rw [bl]; omega_arith), ← decodeBE_os2ip, ← suffix,
        candidateOf_mod_width (by omega_arith) (Nat.le_refl _)]
    -- What changed.
    have px : (sState, sX + g.pLen - sState) ∈ pxRanges g := by simp [pxRanges]
    have C₂ : E.Chg (pxRanges g) s.mem t₂.mem := by
      rw [m₂]
      have h1 := Ct.byte px (i := sX - sState) (by simp only [sX, sState]; omega_arith)
        (by simp only [sX, sState]; omega_arith)
        (t.mem (off E.base sX) ||| 128#8)
      rw [off_add_ofNat, show sState + (sX - sState) = sX by simp only [sX, sState]] at h1
      have h2 := h1.byte px (i := sX - sState + (g.pLen - 1))
        (by simp only [sX, sState]; omega_arith) (by simp only [sX, sState]; omega_arith)
        (t.mem (off E.base sX + BitVec.ofNat 64 (g.pLen - 1)) ||| 1#8)
      rwa [off_add_ofNat, show sState + (sX - sState + (g.pLen - 1)) = sX + (g.pLen - 1) by
        simp only [sX, sState]; omega_arith, ← off_add_ofNat E.base sX] at h2
    have edi₂ : t₂.gpr .edi = s.gpr .edi := by rw [g₂ _ (by decide), g₁ _ (by decide)]; exact BitVec.eq_of_toNat_eq (by rw [Bt.scr.edi_toNat, B.scr.edi_toNat])
    exact ⟨B.keep v C₂ Apx edi₂ (by rw [g₂ _ (by decide), g₁ _ (by decide), Bt.sp, B.sp])
      (by rw [rd₂, rd₁, rdt]) (by rw [wr₂, wr₁, wrt]) (by rw [sy₂, sy₁, syt]), xv, C₂,
      by rw [rd₂, rd₁, rdt], by rw [wr₂, wr₁, wrt], by rw [sy₂, sy₁, syt]⟩

end VG.Proof.Dsa.X86.Generation
