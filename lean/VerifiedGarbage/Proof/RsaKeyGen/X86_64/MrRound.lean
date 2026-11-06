module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWitAll
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrTab
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit

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
