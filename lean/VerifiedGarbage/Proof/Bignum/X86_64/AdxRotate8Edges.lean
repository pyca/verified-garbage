import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedc

/-! The initial pending carry and the final two padding words. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem setup_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxRotate8.setup) s fun t =>
      t.gpr .rcx = off B (slot w aAcc + 16) ∧ word t.mem B (slot w aAcc) = 0 ∧
      Outside B (slot w aAcc) 8 s.mem t.mem ∧ Keep [.rcx, .rax] s t := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) (show aAcc < 8 by decide)
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aAcc)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 (show sArr aAcc < 32 by decide); omega)
  have back : off B (slot w aAcc + 16) + BitVec.ofInt 64 (-16) = off B (slot w aAcc) := by
    rw [show BitVec.ofInt 64 (-16) = 0 - BitVec.ofNat 64 16 from rfl,
      Offset.add_ofNat_add_neg B (show 16 ≤ slot w aAcc + 16 by omega), Nat.add_sub_cancel]
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t =>
    t.gpr .rcx = off B (slot w aAcc + 16) ∧ t.mem = s.mem.writeW (off B (slot w aAcc)) (0 : BitVec 64)) ?_ rfl)
    fun t ⟨⟨hc, hm⟩, kt⟩ => ?_
  · unfold AdxRotate8.setup AdxRotate8.setupBases
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, AdxRotate8.tileCarry, hdi, hdrOff, hl, hH.harr aAcc (by decide),
      off_add16, back, hs.st (show slot w aAcc + 8 ≤ Z by omega)]
    rfl
  · rw [hm]
    exact ⟨hc, word_writeW_self _ _ _ _, writeW_outside _ _ _ (by omega), kt⟩

theorem finishSetup_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B (slot w aTmp)) :
    WP isa (.block AdxRotate8.finishSetup) s fun t =>
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbp = BitVec.ofNat 64 w ∧
      t.gpr .r10 = word s.mem B (slot w aTmp - 16) ∧ t.mem = s.mem ∧ Keep [.r8, .rbp, .r10] s t := by
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  have ht16 : 16 ≤ slot w aTmp := by unfold slot hdrBytes; omega
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)
  have back : off B (slot w aTmp) + BitVec.ofInt 64 (-16) = off B (slot w aTmp - 16) := by
    rw [show BitVec.ofInt 64 (-16) = 0 - BitVec.ofNat 64 16 from rfl]
    exact Offset.add_ofNat_add_neg B ht16
  refine WP.mono (WP.keep [.r8, .rbp, .r10] (Q := fun t =>
    t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbp = BitVec.ofNat 64 w ∧
      t.gpr .r10 = word s.mem B (slot w aTmp - 16) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, kt⟩
  unfold AdxRotate8.finishSetup
  xrun [State.ea, hdr, AdxRotate8.tileCarry, hdi, hdrOff, hc, back, hl, hH.hw,
    hs.ld (show slot w aTmp - 16 + 8 ≤ Z by omega)]

theorem finish_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B (slot w aTmp)) :
    WP isa (.block AdxRotate8.finish) s fun t =>
      wv t.mem B (slot w aTmp) (w + 2) = wv s.mem B (slot w aTmp) w +
        2 ^ (64 * w) * (word s.mem B (slot w aTmp - 16)).toNat ∧
      Outside B (slot w aTmp + 8 * w) 16 s.mem t.mem ∧ Keep [.r8, .rbp, .r10, .rax] s t := by
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  change WP isa (.block (AdxRotate8.finishSetup ++ AdxSquare.redcFinish)) s _
  rw [WP.block_append_iff]
  refine WP.mono (finishSetup_ok hs hdi hH hZ hc) fun a ⟨h8, hp, hv, hm, ka⟩ => ?_
  refine WP.mono (AdxSquare.redcFinish_ok (hs.congr ka.2.2) h8 hp (by omega)) fun t ⟨vt, ot, kt⟩ => ?_
  rw [hm, hv] at vt
  rw [hm] at ot
  exact ⟨vt, ot, (ka.trans kt).mono (by simp)⟩
end VG.Proof.Bignum.X86_64.AdxRotate8
