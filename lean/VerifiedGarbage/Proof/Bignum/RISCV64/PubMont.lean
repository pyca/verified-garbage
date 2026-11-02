module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA public-key operation on RISC-V: a Montgomery multiplication

`montOp_ok`: `montOp o a b`, the bases of its arrays set from array 0's
(`a7`) and the arrays' size (`s5`), then `MontCore.lean`'s `tail`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)

/-- The registers a Montgomery multiplication writes. -/
def montRegs : List Reg := [.a2, .a3, .a4, .a5, .a6] ++ tailRegs

/-- `montOp o a b`, in the working space at `B` with array 0 at `a7`, the
arrays' size in `s5`, `w` in `t0` and `-n⁻¹ mod 2⁶⁴` in `t1`. -/
theorem montOpN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a b : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hb : b < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w b) w < wordsVal s.mem B (slot w 0) w) :
    WP isa (montOp o a b) s fun t =>
      (wordsVal t.mem B (slot w o) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w o) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w a) w * wordsVal s.mem B (slot w b) w % wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, o] s.mem t.mem) ∧
      Keep montRegs s t := by
  unfold montOp
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a2) (by decide) h7 h5 o) fun t₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a3) (by decide) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h5) a) fun t₂ ⟨⟨a3, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a4) (by decide) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) b) fun t₃ ⟨⟨a4, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .a5) (by decide) ((k13.gpr (by decide)).trans h7)
    ((k13.gpr (by decide)).trans h5) 2) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (base_ok (rd := .a6) (by decide) ((k14.gpr (by decide)).trans h7)
    ((k14.gpr (by decide)).trans h5) 3) fun t₅ ⟨⟨a6, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have hm : t₅.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  have g : ∀ r ∈ [Reg.a7, .t0, .t1], t₅.gpr r = s.gpr r := fun r hr => k15.gpr (by revert r hr; decide)
  have g2 : t₅.gpr .a2 = off B (slot w o) := by rw [k5.gpr (by decide), k4.gpr (by decide),
    k3.gpr (by decide), k2.gpr (by decide), a2]
  have g3 : t₅.gpr .a3 = off B (slot w a) := by rw [k5.gpr (by decide), k4.gpr (by decide),
    k3.gpr (by decide), a3]
  have g4 : t₅.gpr .a4 = off B (slot w b) := by rw [k5.gpr (by decide), k4.gpr (by decide), a4]
  have g5 : t₅.gpr .a5 = off B (slot w 2) := by rw [k5.gpr (by decide), a5]
  rw [← hm] at hinv hB ⊢
  refine WP.mono (tailN_ok (hs.congr k15.2.2) hn ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ g2 g3 g4 g5 a6
    ((g _ (by decide)).trans h7) ((g _ (by decide)).trans ht0)
    (by rw [g _ (by decide)]; exact hinv) hB) fun t ⟨h, k⟩ => ⟨h, (k15.trans k).mono (by decide)⟩

/-- `montOpN_ok` for arrays below 8. -/
theorem montOp_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w b) w < wordsVal s.mem B (slot w 0) w) :
    WP isa (montOp o a b) s fun t =>
      (wordsVal t.mem B (slot w o) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w o) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w a) w * wordsVal s.mem B (slot w b) w % wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, o] s.mem t.mem) ∧
      Keep montRegs s t :=
  montOpN_ok hs (by decide) ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ h7 h5 ht0 hinv hB

end VG.Proof.Bignum.RISCV64.Pub
