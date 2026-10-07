import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrCtx
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front

/-!
# A candidate on AArch64: the end of a round of Miller–Rabin

`roundTail_ok`: `kStat := 3` if the witness proves `c` composite (the flag
clear); otherwise the witness counts (`kI`, `kUni`), and `kStat := 4` to go
on (fewer than 16 witnesses, or fewer uniform ones than needed) or 1.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The end of a round. -/
theorem roundTail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {f u : Bool} {i uni ch : Nat} (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 3, sth .x3 kStat])
        (.block [ldh .x3 kI, .addImm .x .x3 .x3 1, sth .x3 kI, ldh .x4 kU, movi .x5 1, .logic .and .x .x4 .x4 .x5,
          ldh .x5 kUni, .add .x .x4 .x4 .x5, sth .x4 kUni,
          movi .x9 4, movi .x10 1, movi .x5 17, .subs .x .x6 .x3 .x5, .csel .x .x13 .x10 .x9, ldh .x5 kChecks,
          .subs .x .x6 .x4 .x5, .csel .x .x13 .x13 .x9, sth .x13 kStat])]) s fun t =>
      t.mem = (if f then ((s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
          (BitVec.ofNat 64 (uni + u.toNat))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1))
        else s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 3)) ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask f ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kFlag < 32 by decide), hs.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega),
      hF]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  refine WP.ite (!f) (by rw [eval_zero, h3₁]; cases f <;> decide) (fun hf => ?_) (fun hf => ?_)
  · simp only [Bool.not_eq_true'] at hf
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 3)) (by
      brun [h0₁, hdr_enc (show kStat < 32 by decide), hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega), hm₁]
      rfl) (by decide) (by decide) (by decide +kernel))
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hf]; rfl, (k₁.trans k).mono (by decide)⟩
  · simp only [Bool.not_eq_false'] at hf
    have hd : ∀ {a b : Nat}, a < 32 → b < 32 → a ≠ b → 8 * a + 8 ≤ 8 * b ∨ 8 * b + 8 ≤ 8 * a := fun _ _ _ => by omega
    have r1 : ∀ X : BitVec 64, (s.mem.writeW (off B (8 * kI)) X).readW (off B (8 * kU)) 64 = mask u := fun X =>
      ((writeW_outside _ _ _ (by simp only [kI, kElen, sFn]; omega)).word (by simp only [kI, kElen, kU, sFn]; omega)
        (by simp only [kU]; omega)).trans hU
    have r2 : ∀ X : BitVec 64, (s.mem.writeW (off B (8 * kI)) X).readW (off B (8 * kUni)) 64 = BitVec.ofNat 64 uni :=
      fun X => ((writeW_outside _ _ _ (by simp only [kI, kElen, sFn]; omega)).word
        (by simp only [kI, kElen, kUni, kP, sFn]; omega) (by simp only [kUni, kP, sFn]; omega)).trans hN
    have r3 : ∀ X Y : BitVec 64, ((s.mem.writeW (off B (8 * kI)) X).writeW (off B (8 * kUni)) Y).readW
        (off B (8 * kChecks)) 64 = BitVec.ofNat 64 ch := fun X Y =>
      ((writeW_outside _ _ _ (by simp only [kUni, kP, sFn]; omega)).word
        (by simp only [kUni, kP, kChecks, kE, sFn]; omega) (by simp only [kChecks, kE, sFn]; omega)).trans
      (((writeW_outside _ _ _ (by simp only [kI, kElen, sFn]; omega)).word
        (by simp only [kI, kElen, kChecks, kE, sFn]; omega) (by simp only [kChecks, kE, sFn]; omega)).trans hC)
    have hs₁' : ∀ {d : Nat}, d + 8 ≤ 256 → InRegions s₁.wr (off B d) 8 := fun hd => hs₁.st (by omega)
    have hl₁ : ∀ {d : Nat}, d + 8 ≤ 256 → InRegions (s₁.rd ++ s₁.wr) (off B d) 8 := fun hd => hs₁.ld (by omega)
    refine (WP.block_append_iff (M := isa) (l₁ := ([ldh .x3 kI, .addImm .x .x3 .x3 1, sth .x3 kI, ldh .x4 kU, movi .x5 1,
      .logic .and .x .x4 .x4 .x5, ldh .x5 kUni, .add .x .x4 .x4 .x5, sth .x4 kUni] : List Instr))).mpr ?_
    refine WP.mono (WP.keep [.x3, .x4, .x5] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (i + 1) ∧
        t.gpr .x4 = BitVec.ofNat 64 (uni + u.toNat) ∧
        t.mem = (s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
          (BitVec.ofNat 64 (uni + u.toNat))) (by
      have hI' : s.mem.readW (B + BitVec.ofNat 64 (8 * kI)) 64 = BitVec.ofNat 64 i := hI
      have r1' : ∀ X : BitVec 64, (s.mem.writeW (B + BitVec.ofNat 64 (8 * kI)) X).readW
          (B + BitVec.ofNat 64 (8 * kU)) 64 = mask u := r1
      have r2' : ∀ X : BitVec 64, (s.mem.writeW (B + BitVec.ofNat 64 (8 * kI)) X).readW
          (B + BitVec.ofNat 64 (8 * kUni)) 64 = BitVec.ofNat 64 uni := r2
      brun [h0₁, hm₁, hdr_enc (show kI < 32 by decide), hdr_enc (show kU < 32 by decide),
        hdr_enc (show kUni < 32 by decide), hs₁.ld (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega),
        hs₁.st (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega), hs₁.ld (d := 8 * kU) (by simp only [kU]; omega),
        hs₁.ld (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega),
        hs₁.st (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega), hI', r1', r2']
      have e1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add _ _).symm
      have e2 : (mask u &&& BitVec.setWidth 64 1#16) + BitVec.ofNat 64 uni = BitVec.ofNat 64 (uni + u.toNat) := by
        rw [BitVec.ofNat_add, BitVec.add_comm]
        congr 1
        cases u <;> decide
      rw [e1, e2]
      exact ⟨rfl, rfl, rfl⟩) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h3₂, h4₂, hm₂⟩, k₂⟩ => ?_
    have h0₂ : s₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans h0₁
    have hs₂ := hs₁.congr k₂.wr
    have r3' : ((s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
        (BitVec.ofNat 64 (uni + u.toNat))).readW (B + BitVec.ofNat 64 (8 * kChecks)) 64 = BitVec.ofNat 64 ch := r3 _ _
    refine (WP.block_append_iff (M := isa) (l₁ := ([movi .x9 4, movi .x10 1, movi .x5 17, .subs .x .x6 .x3 .x5,
      .csel .x .x13 .x10 .x9] : List Instr))).mpr ?_
    refine WP.mono (WP.keep [.x5, .x6, .x9, .x10, .x13] (Q := fun t => t.gpr .x9 = 4 ∧
      t.gpr .x13 = (if i + 1 < 17 then 4 else 1) ∧ t.gpr .x4 = s₂.gpr .x4 ∧ t.mem = s₂.mem ∧ t.gpr .x0 = B) (by
      brun [h3₂, h0₂, subs_carry]
      have e17 : (BitVec.setWidth 64 17#16).toNat = 17 := by decide
      have ei : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      rw [e17, ei]
      by_cases hc : i + 1 < 17
      · rw [decide_eq_false (by omega)]; simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl
      · rw [decide_eq_true (by omega)]; simp only [hc, ↓reduceIte]; rfl) (by decide) (by decide) (by decide +kernel))
      fun s₃ ⟨⟨h9₃, h13₃, h4₃, hm₃, h0₃⟩, k₃⟩ => ?_
    have hs₃ := hs₂.congr k₃.wr
    have rc : s₃.mem.readW (B + BitVec.ofNat 64 (8 * kChecks)) 64 = BitVec.ofNat 64 ch := by rw [hm₃, hm₂]; exact r3'
    refine WP.mono (WP.keep [.x5, .x6, .x13] (Q := fun t => t.mem =
        s₃.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1))) (by
      brun [h0₃, h4₃, h4₂, h9₃, h13₃, rc, hdr_enc (show kChecks < 32 by decide), hdr_enc (show kStat < 32 by decide),
        hs₃.ld (d := 8 * kChecks) (by simp only [kChecks, kE, sFn]; omega),
        hs₃.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega), subs_carry]
      have hu1 : u.toNat ≤ 1 := by cases u <;> decide
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ch < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show uni + u.toNat < 2 ^ 64 by omega)]
      refine congrArg _ ?_
      rcases Nat.lt_or_ge (uni + u.toNat) ch with h2 | h2
      · rw [decide_eq_false (by omega)]; simp only [h2, or_true, Bool.false_eq_true, ↓reduceIte]; rfl
      · rw [decide_eq_true h2]
        by_cases h1 : i + 1 < 17
        · simp only [h1, true_or, ↓reduceIte]; rfl
        · simp only [h1, Nat.not_lt.mpr h2, or_self, ↓reduceIte]; rfl) (by decide) (by decide) (by decide +kernel))
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hm₃, hm₂, hf]; rfl, (((k₁.trans k₂).trans k₃).trans k).mono (by decide)⟩

end VG.Proof.RsaKeyGen.AArch64
