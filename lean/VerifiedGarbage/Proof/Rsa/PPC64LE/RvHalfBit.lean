module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Recover
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvTop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: the count of the halvings

`halfRest_ok`: from the low bit `b` of `m` in `sBit`, `sBit := 1 - b` (`m`
even) and `t += 1 - b` in `sTc`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Recover (sBit sTc)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

theorem xor1_val (x : BitVec 32) (hx : x.toNat ≤ 1) :
    ((x.setWidth 64 ^^^ BitVec.ofNat 64 1).setWidth 32).toNat = 1 - x.toNat ∧
      (x.setWidth 64 ^^^ BitVec.ofNat 64 1).toNat = 1 - x.toNat := by
  rcases (show x = 0 ∨ x = 1 by
    rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega_arith) with e | e
    · exact .inl (BitVec.eq_of_toNat_eq e)
    · exact .inr (BitVec.eq_of_toNat_eq e)) with rfl | rfl <;> decide

theorem add_val (y : BitVec 32) (z : BitVec 64) (hy : y.toNat < 2 ^ 31) (hz : z.toNat ≤ 1) :
    ((y.setWidth 64 + z).setWidth 32).toNat = y.toNat + z.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth]
  omega_arith

/-- The rest of `halfBit`: `sBit := 1 - sBit` and `sTc += 1 - sBit`. -/
theorem halfRest_ok {s : State} {B : Addr} {Z v N : Nat} (h : Ws s B Z v N) (hb : slot s.mem B sBit ≤ 1)
    (hT : slot s.mem B sTc < 2 ^ 31) :
    WP isa (.block [.load .w .r0 .r31 sBit, .li .r3 1, .logic .xor .r0 .r0 .r3, .store .w .r0 .r31 sBit,
        .load .w .r3 .r31 sTc, .add .r3 .r3 .r0, .store .w .r3 .r31 sTc]) s fun t =>
      Ws t B Z v N ∧ KeyWorkspace.Keep B v [] [sBit, sTc] s.mem t.mem ∧
      slot t.mem B sBit = 1 - slot s.mem B sBit ∧ slot t.mem B sTc = slot s.mem B sTc + (1 - slot s.mem B sBit) ∧
      Keep [.r0, .r3] s t := by
  have hz : 160 ≤ Z := h.hdr_le
  have nw := h.nowrap
  have hs := h.scr
  let x := s.mem.readW (off B sBit) 32
  let y := s.mem.readW (off B sTc) 32
  let vb : BitVec 32 := (x.setWidth 64 ^^^ BitVec.ofNat 64 1).setWidth 32
  let vt : BitVec 32 := (y.setWidth 64 + (x.setWidth 64 ^^^ BitVec.ofNat 64 1)).setWidth 32
  have ey : (s.mem.writeW (off B sBit) vb).readW (off B sTc) 32 = y := by
    unfold y; rw [Mem.readW_writeW_sep (Offset.sep B (show sTc + 4 ≤ sBit ∨ sBit + 4 ≤ sTc by decide)
      (by simp only [sTc]; omega_arith) (by simp only [sBit]; omega_arith)) (by decide)]
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun t => t.mem = (s.mem.writeW (off B sBit) vb).writeW (off B sTc) vt)
    ?_ (by decide)) fun t ⟨m, kt⟩ => ?_
  · prun [h.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sBit < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sTc < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sBit < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sTc < 2 ^ 15 by decide),
      hs.ld (show sBit + 4 ≤ Z by simp only [sBit]; omega_arith), hs.ld (show sTc + 4 ≤ Z by simp only [sTc]; omega_arith),
      hs.st (show sBit + 4 ≤ Z by simp only [sBit]; omega_arith), hs.st (show sTc + 4 ≤ Z by simp only [sTc]; omega_arith)]
    rw [show B + BitVec.ofNat 64 sBit = off B sBit from rfl, show B + BitVec.ofNat 64 sTc = off B sTc from rfl, ey]
  · have hx : x.toNat ≤ 1 := hb
    have hy : y.toNat < 2 ^ 31 := hT
    obtain ⟨xv, xv'⟩ := xor1_val x hx
    refine ⟨h.of_keep kt, ?_, ?_, ?_, kt⟩
    · rw [m]
      exact (keep_slot _ _ (by simp) (by simp only [sBit]; omega_arith)).trans
        (keep_slot _ _ (by simp) (by simp only [sTc]; omega_arith))
    · rw [m, show slot ((s.mem.writeW (off B sBit) vb).writeW (off B sTc) vt) B sBit =
          slot (s.mem.writeW (off B sBit) vb) B sBit from
        w32_sep _ _ _ (by decide) (by simp only [sBit]; omega_arith) (by simp only [sTc]; omega_arith), slot_write_self]
      exact xv
    · rw [m, slot_write_self]
      unfold vt
      rw [add_val _ _ hy (by omega_arith), xv']

end VG.Proof.Rsa.PPC64LE.Keys
