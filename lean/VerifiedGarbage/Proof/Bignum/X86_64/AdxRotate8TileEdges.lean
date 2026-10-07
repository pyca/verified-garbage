import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Middle
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head

/-! Initial columns, zero block carry, and public tile advance. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem tileBegin_ok {s : State} {B : Addr} {Z w e : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B e) (he : e + 64 ≤ Z) :
    WP isa AdxRotate8.tileBegin s fun t => cols t = wv s.mem B e 8 ∧
      t.gpr .rbp = off B (slot w aN) ∧ t.gpr .rsi = off B e ∧ t.mem = s.mem ∧
      Keep [.rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aN)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega)
  unfold AdxRotate8.tileBegin
  refine WP.seq (WP.mono (WP.keep [.rbp, .rsi] (Q := fun t =>
    t.gpr .rbp = off B (slot w aN) ∧ t.gpr .rsi = off B e ∧ t.mem = s.mem) ?_ rfl)
    fun a ⟨⟨hp, ho, hm⟩, ka⟩ => ?_)
  · xrun [State.ea, hdr, hdi, hdrOff, hc, hl, hH.harr aN (by decide)]
  · refine WP.mono (loadCols_ok (hs.congr ka.2.2) ho he) fun t ⟨hv, kt⟩ => ?_
    exact ⟨hm ▸ hv, (kt.gpr (by decide)).trans hp, (kt.gpr (by decide)).trans ho,
      kt.2.1.trans hm, (ka.trans kt.keep).mono (by simp)⟩

theorem clearCarry_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B e) (he : 8 ≤ e) (hZ : e ≤ Z) :
    WP isa (.block AdxRotate8.clearCarry) s fun t =>
      word t.mem B (e - 8) = 0 ∧ Outside B (e - 8) 8 s.mem t.mem ∧ Keep [.rax] s t := by
  unfold AdxRotate8.clearCarry
  rw [show ([Instr.mov32 .rax (.imm 0), .store AdxRotate8.blockCarry .rax]) =
    [.mov32 .rax (.imm 0)] ++ [.store AdxRotate8.blockCarry .rax] from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok s .rax) fun a ⟨za, _, _, ka⟩ => ?_
  refine WP.mono (storeMem_ok (hs.congr ka.2.2.2) (ea_carry ((ka.gpr (by decide)).trans hc) he)
    (show e - 8 + 8 ≤ Z by omega)) fun t ⟨wt, ot, kt⟩ => ?_
  exact ⟨wt.trans za, by rw [ka.2.1] at ot; exact ot, (ka.keep.trans kt).mono (by simp)⟩

theorem tileEnd_ok {s : State} {B : Addr} {Z w e : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B e) (he : hdrBytes ≤ e)
    (heZ : e + 72 ≤ Z) :
    WP isa (.block AdxRotate8.tileEnd) s fun t =>
      word t.mem B (e + 48) = s.gpr .rax ∧ t.gpr .rcx = off B (e + 64) ∧
      t.zf = some (decide (e + 64 = slot w aTmp)) ∧ Outside B (e + 48) 8 s.mem t.mem ∧ Keep [.rcx] s t := by
  have hn := hs.nowrap
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  unfold AdxRotate8.tileEnd
  rw [show ([Instr.store (AdxRotate8.at_ .rcx 48) .rax, .alu .add .rcx (.imm 64),
    .alu .cmp .rcx (.mem (hdr (sArr aTmp)))]) = [.store (AdxRotate8.at_ .rcx 48) .rax] ++
      [.alu .add .rcx (.imm 64), .alu .cmp .rcx (.mem (hdr (sArr aTmp)))] from rfl, WP.block_append_iff]
  refine WP.mono (storeAt_ok hs hc (show e + 48 + 8 ≤ Z by omega)) fun a ⟨wa, oa, ka⟩ => ?_
  have sa := hs.congr ka.2.2
  have ha := hH.of_outside oa (by omega)
  have hca := (ka.gpr (by simp)).trans hc
  have hda := (ka.gpr (by simp)).trans hdi
  have hl : InRegions (a.rd ++ a.wr) (off B (8 * sArr aTmp)) 8 :=
    sa.ld (by have := hdr_lt_slot w 8 (show sArr aTmp < 32 by decide); omega)
  have adv : off B e + BitVec.signExtend 64 (64 : BitVec 32) = off B (e + 64) := by
    change off (off B e) 64 = off B (e + 64)
    exact off_off _ _ _
  refine WP.mono (WP.keep [.rcx] (Q := fun t =>
    t.gpr .rcx = off B (e + 64) ∧ t.zf = some (decide (e + 64 = slot w aTmp)) ∧ t.mem = a.mem) ?_ rfl)
    fun t ⟨⟨hc', hz, hm⟩, kt⟩ => ?_
  · xrun [State.ea, hdr, hda, hdrOff, hca, adv, hl, ha.harr aTmp (by decide),
      off_sub_beq B (show e + 64 < 2 ^ 64 by omega) (show slot w aTmp < 2 ^ 64 by omega)]
  · exact ⟨by rw [hm]; exact wa, hc', hz, by rw [hm]; exact oa, (ka.trans kt).mono (by simp)⟩
end VG.Proof.Bignum.X86_64.AdxRotate8
