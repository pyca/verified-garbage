module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
public import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrBit
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.Gcd
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrTab
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest

/-! ### `RsaKeyGen.X86_64.MrWitAll`, which only this module used -/

section

/-!
# A candidate on x86-64: `mrWitness`

`mrWitness_ok`: the witness `Spec.RsaKeyGen.witness (c − 1) x` for the next
`8 w` octets `x` of `rand` in `aX`, the mask of its uniformity in `kU`, and
`kUsed` advanced.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `mrWitness` changes. -/
def witRanges (w : Nat) : List (Nat × Nat) := [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8), (8 * kU, 8)]

/-- `witRanges`'s ranges, in the header and in the arrays. -/
theorem witRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(200, 8), (240, 8)]
    [(1, 1)] (witRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    witRanges, Public.aX, aX, sFn, kU, kUsed] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem mrWitness_eq : mrWitness =
    ([.block [.mov .rsi (.mem (hdr kRand)), .mov .rax (.mem (hdr kUsed)), .alu .add .rsi (.reg .rax),
        .mov .rcx (.mem (hdr kLen)), .mov .rbx (.mem (hdr (sArr aX))), .alu .add .rax (.reg .rcx),
        .store (hdr kUsed) .rax], loadBE] : List (Prog isa)) ++
    (([.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))), .mov .rbp (.mem (at0 .rbx)),
        .alu .and .rbp (.imm (BitVec.ofInt 32 (-2)))],
      wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)]] : List (Prog isa)) ++
    (([.block [.alu .cmp .rbp (.imm 1), .alu .sbb .r15 (.reg .r15),
        .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))), .mov .r10 (.mem (hdr (sArr aN))), .mov .rax (.mem (at0 .rbx)),
        .alu .or .rax (.imm 1), .alu .sub .rax (.mem (at0 .r10)), cfToRbp],
      wordLoop 1 cmpBody] : List (Prog isa)) ++
    ([.block [.alu .and .r15 (.reg .rbp), .store (hdr kU) .r15, .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
      .mov .rax (.reg .r15), .alu .and .rax (.imm 2), .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax,
      .movImm64 .rax (BitVec.ofNat 64 (2 ^ 63)), .alu .and .rax (.reg .r15),
      .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.mem (ix .rbx .r12 (-8))),
      .store (ix .rbx .r12 (-8)) .rax]] : List (Prog isa)))) := rfl

/-- `mrWitness`. -/
theorem mrWitness_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} (hd : MrDims B Z w)
    (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {u : Nat} {bs : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z (rp + BitVec.ofNat 64 u) bs) (hbl : bs.length = 8 * w) :
    WP isa (seqs mrWitness) s fun t => MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aX) w = (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip bs)).1 ∧
      word t.mem B (8 * kU) = mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip bs)).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (u + 8 * w) ∧
      Frm B (witRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hw4 := hd.w4
  have hw' : w < 2 ^ 27 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  rw [mrWitness_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witLoad_ok hg hZ (by omega_arith) hw' hR hU hK hsrc hbl) fun s₁ ⟨hx₁, hu₁, hf₁, hg₁, k₁⟩ => ?_
  have hc₁ : MrCtx s₁ B Z w mi c bm := hc.of_frm hd hf₁ hg₁.scr hg₁.rdi (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  have hx : Spec.Rsa.os2ip bs < 2 ^ (64 * w) := by
    have := os2ip_lt bs; rw [hbl, pow256_eq] at this; rwa [show 8 * (8 * w) = 64 * w by omega_arith] at this
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witLow_ok hg₁ hZ (by omega_arith) (by omega_arith)) fun s₂ ⟨hlow, hbx₂, h12₂, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witCmp_ok hg₂ hZ (by omega_arith) (by omega_arith) hbx₂ h12₂ (by rw [hm₂]; exact hlow))
    fun s₃ ⟨h15, hbp, hm₃, k₃⟩ => ?_
  rw [hm₂, hx₁] at h15
  rw [hm₂, hx₁, hc₁.n] at hbp
  have hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, by rw [hm₃]; exact hg₂.hdr⟩
  refine WP.mono (witForce_ok hg₃ hZ (by omega_arith) (by omega_arith) ((k₃.gpr (by decide)).trans hbx₂)
    ((k₃.gpr (by decide)).trans h12₂) h15 hbp) fun t ⟨hm, k⟩ => ?_
  rw [hm₃, hm₂] at hm
  generalize hu : (decide (2 ≤ Spec.Rsa.os2ip bs) && decide (Spec.Rsa.os2ip bs + (1 - Spec.Rsa.os2ip bs % 2) < c)) = uu
    at hm
  have hwit := witness_eq hodd hb hx
  rw [hu] at hwit
  -- The words of `aX` after the stores.
  have hw0 : word t.mem B (slot w aX) = if uu then word s₁.mem B (slot w aX) else word s₁.mem B (slot w aX) ||| 2 := by
    rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_arith)).word (d := slot w aX) (Or.inl (by omega_arith))
      (by omega_arith), word_writeW_self]
  have hwt : word t.mem B (slot w aX + 8 * (w - 1)) = if uu then word s₁.mem B (slot w aX + 8 * (w - 1))
      else word s₁.mem B (slot w aX + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63)) := by
    rw [hm, word_writeW_self]
  have hwm : ∀ j, 0 < j → j < w - 1 → word t.mem B (slot w aX + 8 * j) = word s₁.mem B (slot w aX + 8 * j) := by
    intro j hj0 hj
    rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_arith)).word (Or.inl (by omega_arith)) (by omega_arith),
      (writeW_outside _ B _ (d := slot w aX) (by omega_arith)).word (Or.inr (by omega_arith)) (by omega_arith),
      (writeW_outside _ B _ (d := 8 * kU) (by unfold kU sFn; omega_arith)).word
        (Or.inr (by unfold slot kU sFn aX hdrBytes; omega_arith)) (by omega_arith)]
  have hft : Frm B (witRanges w) s₁.mem t.mem := by
    rw [hm]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kU) (by unfold kU sFn; omega_arith)) (by simp [witRanges])).trans
      (Frm.of_outside ((writeW_outside _ B _ (d := slot w aX) (by omega_arith)).mono (o' := slot w aX) (n' := 8 * (w + 2))
        (Nat.le_refl _) (by omega_arith)) (by simp [witRanges]))).trans
      (Frm.of_outside ((writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_arith)).mono (o' := slot w aX)
        (n' := 8 * (w + 2)) (by omega_arith) (by omega_arith)) (by simp [witRanges]))
  have hgt : Good t B Z w mi := ⟨hg₃.scr.congr k.2.2, (k.gpr (by decide)).trans hg₃.rdi,
    Hdr.of_frm (by rw [← hm₂, ← hm₃]; exact hg₃.hdr) hft (by simp only [witRanges]; rng_disj)⟩
  refine ⟨hc₁.of_frm hd hft hgt.scr hgt.rdi (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj),
    ?_, ?_, ?_, (Frm.mono hf₁ (by simp [witRanges])).trans hft, ((((k₁.trans k₂).trans k₃).trans k).mono (by decide))⟩
  · rw [hwit, ← hx₁]
    cases uu
    · exact wv_force (by omega_arith) (by rw [hw0]; rfl) (by rw [hwt]; rfl) hwm
    · exact wv_congr2 fun i hi => by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [Nat.mul_zero, Nat.add_zero, hw0]; rfl
        · by_cases hit : i = w - 1
          · rw [hit, hwt]; rfl
          · exact hwm i hi0 (by omega_arith)
  · rw [hwit, hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_arith)).word (d := 8 * kU)
      (Or.inl (by unfold slot kU sFn aX hdrBytes; omega_arith)) (by unfold kU sFn; omega_arith),
      (writeW_outside _ B _ (d := slot w aX) (by omega_arith)).word (d := 8 * kU)
      (Or.inl (by unfold slot kU sFn aX hdrBytes; omega_arith)) (by unfold kU sFn; omega_arith), word_writeW_self]
  · rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega_arith)).word (d := 8 * kUsed)
      (Or.inl (by unfold slot kUsed sFn aX hdrBytes; omega_arith)) (by unfold kUsed sFn; omega_arith),
      (writeW_outside _ B _ (d := slot w aX) (by omega_arith)).word (d := 8 * kUsed)
      (Or.inl (by unfold slot kUsed sFn aX hdrBytes; omega_arith)) (by unfold kUsed sFn; omega_arith),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hu₁

end VG.Proof.RsaKeyGen.X86_64

end

end


/-!
# A candidate on x86-64: one round of Miller–Rabin

What the start of a round changes (`preRanges`), and the end of a round
(`roundTail_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The octets of `rand` from `a`. -/
theorem Src.seg {s : State} {B : Addr} {Z : Nat} {rp : Addr} {r : List Byte} (h : Src s B Z rp r) {a n : Nat}
    (ha : a + n ≤ r.length) : Src s B Z (rp + BitVec.ofNat 64 a) (VG.Proof.RsaKeyGen.seg r a n) := by
  have hl : (VG.Proof.RsaKeyGen.seg r a n).length = n := by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [ha]
  have he : ∀ i, rp + BitVec.ofNat 64 a + BitVec.ofNat 64 i = rp + BitVec.ofNat 64 (a + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [he]; exact h.rd (a + i) (by omega_using [ha, hl, hi])
  · rw [he, h.val (a + i) (by omega_using [ha, hl, hi])]
    simp only [VG.Proof.RsaKeyGen.seg, List.getElem_take, List.getElem_drop]
  · rw [he]; exact h.out (a + i) (by omega_using [ha, hl, hi])

/-- What the start of a round changes. -/
def preRanges (w : Nat) : List (Nat × Nat) :=
  witRanges w ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++ tabRanges w

/-- `preRanges`'s ranges, in the header and in the arrays. -/
theorem preRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(200, 8), (240, 8), (208, 8), (224, 8)]
    [(1, 1), (2, 1), (3, 1), (5, 1), (8, 16), (6, 1)] (preRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    preRanges, tabRanges, witRanges, Public.aX, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aX, aAcc, aTmp, aXm, aY, VG.Proof.Bignum.tabBytes, kT0, sFn, kV, kBits, kU, kT2, kUsed] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(8, 16), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem mask_and1' (c : Bool) : mask c &&& BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

theorem rcx_stat2 (a b : Bool) : ((0#64 - (BitVec.ofBool a).setWidth 64 ||| 0#64 - (BitVec.ofBool b).setWidth 64) &&&
    (3 : BitVec 64)) + 1 = BitVec.ofNat 64 (if a || b then 4 else 1) := by
  cases a <;> cases b <;> decide

/-- The end of a round: `kStat := 3` if the witness proves `c` composite;
otherwise the witness counts, and `kStat := 4` to go on or 1. -/
theorem roundTail_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {f u : Bool} {i uni ch : Nat} (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa (seqs [.block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
      .ite .e (.block [])
        (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
          .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
          .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
          .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
      .block [.store (hdr kStat) .rcx]]) s fun t =>
      t.mem = (if f then ((s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
          (BitVec.ofNat 64 (uni + u.toNat))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1))
        else s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 3)) ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 3 ∧
      t.zf = some (!f) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kFlag (by decide), hF, BitVec.and_self]
    cases f <;> decide) rfl) fun s₁ ⟨⟨hcx₁, hz₁, hm₁⟩, k₁⟩ => ?_)
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  refine WP.seq (WP.ite (!f) (by simp [eval, hz₁]) (fun hf => ?_) (fun hf => ?_))
  · simp only [Bool.not_eq_true'] at hf
    refine WP.block_nil (WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat))
      (BitVec.ofNat 64 3)) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, show s₁.wr = s.wr from k₁.2.2 ▸ rfl, hs kStat (by decide), hcx₁, hm₁]
      ) rfl) fun t ⟨hm, k⟩ => ⟨by rw [hm, hf]; rfl, (k₁.trans k).mono (by decide)⟩)
  · simp only [Bool.not_eq_false'] at hf
    have hs₁ := hg.scr.congr k₁.2.2
    have hst : ∀ i < 32, InRegions s₁.wr (off B (8 * i)) 8 := fun i hi => by rw [k₁.2.2]; exact hs i hi
    have hld : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi => by
      rw [k₁.2.1, k₁.2.2]; exact hl i hi
    refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t =>
        t.gpr .rcx = BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1) ∧
        t.mem = (s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
          (BitVec.ofNat 64 (uni + u.toNat))) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hld kI (by decide), hld kU (by decide), hld kUni (by decide),
        hld kChecks (by decide), hst kI (by decide), hst kUni (by decide), hm₁, hI, ofNat_add_one,
        fun X => (hdrStore_hdr s.mem B X (show kI < 32 by decide) (show kU < 32 by decide) (by decide)).trans hU,
        fun X => (hdrStore_hdr s.mem B X (show kI < 32 by decide) (show kUni < 32 by decide) (by decide)).trans hN,
        fun X Y => (hdrStore_hdr _ B Y (show kUni < 32 by decide) (show kChecks < 32 by decide) (by decide)).trans
          ((hdrStore_hdr s.mem B X (show kI < 32 by decide) (show kChecks < 32 by decide) (by decide)).trans hC),
        mask_and1', sbb_self, cmp_imm_cf (show i + 1 < 2 ^ 63 by omega_using [hi]) (show 17 < 2 ^ 31 by decide)]
      have e1 : (mask u &&& 1) + BitVec.ofNat 64 uni = BitVec.ofNat 64 (uni + u.toNat) := by
        cases u
        · simp [mask_false]
        · simp [mask_true]; rw [← BitVec.ofNat_add, Nat.add_comm]
      rw [e1]
      refine ⟨?_, rfl⟩
      rw [show (BitVec.signExtend 64 (17 : BitVec 32)).toNat = 17 by decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega_using [hi]),
        Nat.mod_eq_of_lt (show uni + u.toNat < 2 ^ 64 by cases u <;> simp <;> omega_using [huni]),
        Nat.mod_eq_of_lt (show ch < 2 ^ 64 by omega_using [hch]), rcx_stat2]
      by_cases h1 : i + 1 < 17 <;> by_cases h2 : uni + u.toNat < ch <;> simp [h1, h2]) rfl)
      fun s₂ ⟨⟨hcx₂, hm₂⟩, k₂⟩ => ?_
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (off B (8 * kStat))
      (BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1))) (by
      xrun [State.ea, hdr, (k₂.gpr (by decide) : s₂.gpr .rdi = s₁.gpr .rdi).trans hdi₁, hdrOff,
        show s₂.wr = s.wr from k₂.2.2.trans k₁.2.2, hs kStat (by decide), hcx₂]) rfl)
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hm₂, hf]; rfl, ((k₁.trans k₂).trans k).mono (by decide)⟩

end VG.Proof.RsaKeyGen.X86_64
