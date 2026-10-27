module

public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The probable-prime test's arguments in the generation's frame slots -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Impl.Bignum.AArch64 (movi)

/-- The memory after the entry's stores. -/
def entryMem (s : State) (F : Addr) : Mem :=
  ((((s.mem.writeW (off F 40) (s.gpr .x0)).writeW (off F 112) (s.gpr .x2)).writeW (off F 120) (s.gpr .x3)).writeW
    (off F usedSlot) (s.gpr .x4)).writeW (off F 128) (0 : BitVec 64)

theorem entryMem_outside (s : State) (F : Addr) :
    Outside F 40 104 s.mem (entryMem s F) := by
  unfold entryMem usedSlot
  exact ((((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
    ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))).trans
    ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))).trans
    ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)) |>.trans
    ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))

theorem entryMem_word (s : State) (F : Addr) :
    word (entryMem s F) F 40 = s.gpr .x0 ∧ word (entryMem s F) F 112 = s.gpr .x2 ∧
      word (entryMem s F) F 120 = s.gpr .x3 ∧ word (entryMem s F) F usedSlot = s.gpr .x4 ∧
      word (entryMem s F) F 128 = 0 := by
  unfold entryMem usedSlot
  have o (m : Mem) {d : Nat} (v : BitVec 64) (e : Nat) (he : e + 8 ≤ d ∨ d + 8 ≤ e) (hd : d + 8 ≤ 272) (he' : e + 8 ≤ 272) :
      word (m.writeW (off F d) v) F e = word m F e :=
    (writeW_outside m F v (by omega)).word (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, word_writeW_self _ _ _ _⟩
  · rw [o _ _ 40 (by decide) (by decide) (by decide), o _ _ 40 (by decide) (by decide) (by decide),
      o _ _ 40 (by decide) (by decide) (by decide), o _ _ 40 (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [o _ _ 112 (by decide) (by decide) (by decide), o _ _ 112 (by decide) (by decide) (by decide),
      o _ _ 112 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [o _ _ 120 (by decide) (by decide) (by decide), o _ _ 120 (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [o _ _ 136 (by decide) (by decide) (by decide), word_writeW_self]

theorem entry_ok {s : State} {F : Addr} (hsp : s.sp = F)
    (hw : ∀ d, d + 8 ≤ 272 → InRegions s.wr (off F d) 8) :
    WP isa (.block entry) s fun t =>
      t.mem = entryMem s F ∧ t.gpr .x0 = off (s.gpr .x0) arithmetic ∧ Keep [.x0, .x3] s t := by
  have hr40 : InRegions (s.rd ++ s.wr) (off F 40) 8 := by
    obtain ⟨r, hr, hc⟩ := hw 40 (by decide); exact ⟨r, List.mem_append_right _ hr, hc⟩
  have h40 := (entryMem_word s F).1
  have run : WP isa (.block entry) s fun t => t.mem = entryMem s F ∧ t.gpr .x0 = off (s.gpr .x0) arithmetic := by
    rw [show entry = [.strSp .x0 40, .strSp .x2 112, .strSp .x3 120, .strSp .x4 usedSlot, movi .x3 0] ++
      ([.strSp .x3 128, .ldrSp .x0 40, movi .x3 arithmetic, .add .x .x0 .x0 .x3] : List Instr) from rfl]
    apply WP.block_append
    have run1 : WP isa (.block [.strSp .x0 40, .strSp .x2 112, .strSp .x3 120, .strSp .x4 usedSlot, movi .x3 0]) s
        fun u => u.mem = (((s.mem.writeW (off F 40) (s.gpr .x0)).writeW (off F 112) (s.gpr .x2)).writeW
          (off F 120) (s.gpr .x3)).writeW (off F usedSlot) (s.gpr .x4) ∧ u.gpr .x3 = 0 ∧ u.gpr .x0 = s.gpr .x0 ∧
          u.sp = F ∧ u.rd = s.rd ∧ u.wr = s.wr := by
      unfold usedSlot
      brun [exec_storeSp (by decide : 40 % 8 = 0 ∧ 40 < 32768), exec_storeSp (by decide : 112 % 8 = 0 ∧ 112 < 32768),
        exec_storeSp (by decide : 120 % 8 = 0 ∧ 120 < 32768), exec_storeSp (by decide : 136 % 8 = 0 ∧ 136 < 32768),
        hsp, hw 40 (by decide), hw 112 (by decide), hw 120 (by decide), hw 136 (by decide), off]
      done
    refine WP.mono run1 fun u ⟨hm, h3, h0, hspu, hrd, hwr⟩ => ?_
    have hw128 : InRegions u.wr (off F 128) 8 := by rw [hwr]; exact hw 128 (by decide)
    have hr40' : InRegions (u.rd ++ u.wr) (off F 40) 8 := by rw [hrd, hwr]; exact hr40
    have hread : (u.mem.writeW (off F 128) (0 : BitVec 64)).readW (off F 40) 64 = s.gpr .x0 := by
      have := h40; unfold entryMem at this; rw [← hm] at this; exact this
    brun [exec_storeSp (by decide : 128 % 8 = 0 ∧ 128 < 32768), exec_ldrSp (by decide : 40 % 8 = 0 ∧ 40 < 32768),
      hspu, hw128, hr40', h3, off, entryMem, hm]
    rw [show BitVec.setWidth 64 (BitVec.ofNat 16 arithmetic) = BitVec.ofNat 64 arithmetic by decide]
    exact congrArg (· + BitVec.ofNat 64 arithmetic) (by simpa only [hm, off] using hread)
  exact WP.mono (WP.keep [.x0, .x3] run (by decide)) fun t ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

end VG.Proof.Dsa.AArch64.ProbablePrime
