module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadow
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Rsa.X86_64.Loops

-- separate module: isolate shadow-header initialization from input copy loops

/-! # Entering the validation reducer's second workspace -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.WordValidation VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Shifting a natural word is multiplication modulo the word size. -/
theorem shl_nat (n b : Nat) : BitVec.ofNat 64 n <<< b = BitVec.ofNat 64 (n * 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mod_mod]

theorem addr_view (B : Addr) (a d : Nat) : off (off B a) d = off B (a + d) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

def enterMem (m : Mem) (B : Addr) (w : Nat) : Mem :=
  (m.writeW (off (off B (start w)) (8 * sW)) (BitVec.ofNat 64 w)).writeW
    (off (off B (start w)) (8 * VG.Impl.Rsa.X86_64.Keys.sStride)) (BitVec.ofNat 64 (8 * (w + 2)))

theorem enterLoad_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (h : Good s B Z w minv)
    (hZ : start w + span w ≤ Z) :
    WP isa (.block enterLoad) s fun t =>
      (t.gpr .rsi = off B (slot w aAcc) ∧ t.gpr .r10 = off B (slot w VG.Impl.Rsa.X86_64.CheckKey.aM) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) ∧
      Keep [.rsi, .r10, .r12, .r9] s t := by
  have hz : 256 ≤ Z := by simp only [start, span, slot, hdrBytes] at hZ; omega_using [hZ]
  have eadd : BitVec.ofNat 64 w + 2 = BitVec.ofNat 64 (w + 2) := by rw [BitVec.ofNat_add]; rfl
  have es : (w + 2) * 2 ^ 3 = 8 * (w + 2) := by omega_arith
  refine WP.keep [.rsi, .r10, .r12, .r9] (by
    xrun [enterLoad, State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sArr aAcc) (by change 8 * 10 + 8 ≤ Z; omega_using [hz]),
      h.scr.ld (d := 8 * sArr VG.Impl.Rsa.X86_64.CheckKey.aM) (by change 8 * 12 + 8 ≤ Z; omega_using [hz]),
      h.scr.ld (d := 8 * sW) (by change 8 * 6 + 8 ≤ Z; omega_using [hz]), h.hdr.harr aAcc (by decide),
      h.hdr.harr VG.Impl.Rsa.X86_64.CheckKey.aM (by decide), h.hdr.hw, eadd, shl_nat, es]) rfl

/-- Pointer and header setup before the source copies. -/
theorem enter_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (h : Good s B Z w minv)
    (hZ : start w + span w ≤ Z) (hw : 4 ≤ w) :
    WP isa (.block enter) s fun t =>
      t.gpr .rdi = off B (start w) ∧ t.gpr .rsi = off B (slot w aAcc) ∧
      t.gpr .r10 = off B (slot w VG.Impl.Rsa.X86_64.CheckKey.aM) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.mem = enterMem s.mem B w ∧ Keep [.rsi, .r10, .r12, .rdi, .r9] s t := by
  have hs := h.scr.sub hZ (by simp only [span, slot, hdrBytes]; omega_arith)
  unfold enter
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (enterLoad_ok h hZ) fun t₁ ⟨⟨hsi, h10, h12, h9, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok 8 (r := .rdi) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9) fun t₂ ⟨hdi, m₂, k₂⟩ => ?_
  change t₂.gpr .rdi = off B (start w) at hdi
  have hs₂ := hs.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = enterMem s.mem B w) (by
    xrun [enterHeader, State.ea, hdr, hdi, hdrOff,
      (k₂.gpr (by decide) : t₂.gpr .r12 = _), h12,
      (k₂.gpr (by decide) : t₂.gpr .r9 = _), h9,
      hs₂.st (d := 8 * sW) (by simp only [span, slot, hdrBytes, sW]; omega_arith),
      hs₂.st (d := 8 * VG.Impl.Rsa.X86_64.Keys.sStride) (by simp only [span, slot, hdrBytes, VG.Impl.Rsa.X86_64.Keys.sStride, sFn]; omega_arith),
      m₂, m₁, enterMem]) rfl) fun t ⟨hm, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans hdi, ((k₂.trans k₃).gpr (by decide)).trans hsi,
    ((k₂.trans k₃).gpr (by decide)).trans h10, ((k₂.trans k₃).gpr (by decide)).trans h12,
    ((k₂.trans k₃).gpr (by decide)).trans h9, hm, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem enterMem_width (m : Mem) (B : Addr) (w : Nat) :
    word (enterMem m B w) (off B (start w)) (8 * sW) = BitVec.ofNat 64 w := by
  unfold enterMem
  rw [(writeW_outside _ _ _ (by change 224 + 8 ≤ 2 ^ 64; decide)).word
      (Or.inl (by change 48 + 8 ≤ 224; decide)) (by decide), word_writeW_self]

theorem enterMem_stride (m : Mem) (B : Addr) (w : Nat) :
    word (enterMem m B w) (off B (start w)) (8 * VG.Impl.Rsa.X86_64.Keys.sStride) =
      BitVec.ofNat 64 (8 * (w + 2)) := by unfold enterMem; exact word_writeW_self _ _ _ _

theorem enterMem_frame {s : State} {B : Addr} {Z w : Nat} (h : Scr s B Z)
    (hZ : start w + span w ≤ Z) : Outside B (start w) (span w) s.mem (enterMem s.mem B w) := by
  have hn := h.nowrap
  have hp : 0 < span w := by simp only [span, slot, hdrBytes]; omega_arith
  apply outside_view (by omega_using [hn, hZ]) hp
  intro x hx
  unfold enterMem
  rw [writeW_outside _ _ _ (d := 8 * VG.Impl.Rsa.X86_64.Keys.sStride) (by change 224 + 8 ≤ 2 ^ 64; decide) x
      (Or.inr (by simp only [span, slot, hdrBytes, VG.Impl.Rsa.X86_64.Keys.sStride, sFn] at hx ⊢; omega_using [hx])),
    writeW_outside _ _ _ (d := 8 * sW) (by change 48 + 8 ≤ 2 ^ 64; decide) x
      (Or.inr (by simp only [span, slot, hdrBytes, sW] at hx ⊢; omega_using [hx]))]

/-- Array pointers complete the second workspace's invariant. -/
theorem setup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (h : Good s B Z w minv)
    (hZ : start w + span w ≤ Z) (hw : 4 ≤ w) (hw' : w < 2 ^ 24) :
    WP isa (.seq (.block enter) (.block setBases)) s fun t =>
      VG.Proof.Rsa.X86_64.Ws t (off B (start w)) (span w) w ∧
      t.gpr .rsi = off B (slot w aAcc) ∧ t.gpr .r10 = off B (slot w VG.Impl.Rsa.X86_64.CheckKey.aM) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      Outside B (start w) (span w) s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hn := h.scr.nowrap
  have hp : 0 < span w := by simp only [span, slot, hdrBytes]; omega_arith
  have hs := h.scr.sub hZ hp
  refine WP.seq (WP.mono (enter_ok h hZ hw) fun t₁ ⟨hdi, hsi, h10, h12, h9, m₁, k₁⟩ => ?_)
  refine WP.mono (setBases_ok (hs.congr k₁.2.2) hdi h12
    (by simp only [span, slot, hdrBytes, sArr]; omega_arith)) fun t ⟨ha, o₂, k₂⟩ => ?_
  have wt : word t.mem (off B (start w)) (8 * sW) = BitVec.ofNat 64 w := by
    rw [o₂.word (Or.inl (by change 48 + 8 ≤ 64; decide)) (by decide), m₁, enterMem_width]
  have st : word t.mem (off B (start w)) (8 * VG.Impl.Rsa.X86_64.Keys.sStride) = BitVec.ofNat 64 (8 * (w + 2)) := by
    rw [o₂.word (Or.inr (by change 64 + 64 ≤ 224; decide)) (by decide), m₁, enterMem_stride]
  have ot : Outside B (start w) (span w) t₁.mem t.mem := outside_view (by omega_using [hn, hZ]) hp
    (InScr.of_outside o₂ (by simp only [span, slot, hdrBytes, sArr]; omega_arith))
  have o₁ : Outside B (start w) (span w) s.mem t₁.mem := by rw [m₁]; exact enterMem_frame h.scr hZ
  refine ⟨⟨hs.congr (k₁.trans k₂).2.2, (k₂.gpr (by decide)).trans hdi, wt, st, ha,
    by simp only [span, slot]; omega_arith, by omega_using [hw], hw'⟩,
    (k₂.gpr (by decide)).trans hsi, (k₂.gpr (by decide)).trans h10,
    (k₂.gpr (by decide)).trans h12, (k₂.gpr (by decide)).trans h9, o₁.trans ot,
    (k₁.trans k₂).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.WordValidation
