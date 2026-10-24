module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA sampling on PPC64LE: a draw into the nonce

`copy_ok`: `copy` copies the `W` octets of the tape from `used` to the
nonce's last `W` octets, the first masked by `M` (`cpy`), changing memory
there only, and adds `W` to `used`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- The registers `copy` writes. -/
def copyRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r25]

/-- The draw's octet `j` as the nonce gets it: the first masked. -/
def cpy (bs : List Byte) (M : Nat) (j : Nat) : Byte :=
  if j = 0 then bs.getD 0 0 &&& BitVec.ofNat 8 M else bs.getD j 0

/-- The frame's offset of the draw in the nonce. -/
abbrev SE.o (E : SE) : Nat := oNonce + (E.ql - E.W)

theorem copy_ok {E : SE} {R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (h : SEnv E R s)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u + E.W ≤ E.rl) :
    WP isa copy s fun t =>
      (t.gpr .r25 = BitVec.ofNat 64 (u + E.W) ∧ Outside E.F E.o E.W s.mem t.mem ∧
        ∀ j < E.W, t.mem (off E.F (E.o + j)) = cpy (R.drop u) E.M j) ∧ Keep copyRegs s t := by
  have hf := hE.fnw
  have hW1 := hE.W1
  have hWq := hE.Wq
  have hql := hE.ql
  have hrn := hE.rnw
  have hM := hE.M
  simp only [frameBytes] at hf
  refine WP.keep copyRegs ?_ (by decide)
  unfold copy Precompute.countLoop
  have hi : WP isa (.block copyInit) s fun s₁ =>
      s₁.gpr .r3 = off E.rand u ∧ s₁.gpr .r4 = off E.F E.o ∧ s₁.gpr .r5 = BitVec.ofNat 64 E.W ∧
        s₁.gpr .r6 = BitVec.ofNat 64 E.M ∧ s₁.gpr .r25 = BitVec.ofNat 64 u ∧
        s₁.gpr .r28 = BitVec.ofNat 64 E.W ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    unfold copyInit
    prun [h.r23, h25, h.r21, h.r28, h.r29, h.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), BitVec.add_zero]
    rw [VG.Offset.add_ofNat_sub _ (by simp only [oNonce]; omega)]
    rw [show oNonce + E.ql - E.W = oNonce + (E.ql - E.W) by omega]
  refine WP.seq (WP.mono hi fun s₁ ⟨i3, i4, i5, i6, i25, i28, im, ird, iwr⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r3 = off E.rand (u + i) ∧ t.gpr .r4 = off E.F (E.o + i) ∧
      t.gpr .r6 = BitVec.ofNat 64 (if i = 0 then E.M else 255) ∧ t.gpr .r25 = BitVec.ofNat 64 u ∧
      t.gpr .r28 = BitVec.ofNat 64 E.W ∧ Outside E.F E.o E.W s.mem t.mem ∧
      (∀ j < i, t.mem (off E.F (E.o + j)) = cpy (R.drop u) E.M j) ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.seq (WP.mono (wp_countdown (body := .block (copyByte ++ ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := E.W) (by omega) (by omega) Inv
    (fun i hi t ⟨t3, t4, t6, t25, t28, tout, tb, trd, twr⟩ _ => ?_)
    ⟨by rw [i3, Nat.add_zero], by rw [i4, Nat.add_zero], by rw [i6]; rfl, i25, i28, by rw [im]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega), ird, iwr⟩ i5) fun t ht => ?_)
  · have hrd : InRegions (t.rd ++ t.wr) (off E.rand (u + i)) 1 := by
      rw [trd, twr]; exact h.rr _ (by omega)
    have hwr : InRegions t.wr (off E.F (E.o + i)) 1 := by
      have := (h.nw.congr (twr.trans rfl)).st (d := E.ql - E.W + i) (n := 1) (by omega)
      rwa [off_off, show oNonce + (E.ql - E.W + i) = E.o + i by simp only [SE.o]; omega] at this
    have hb : t.mem (off E.rand (u + i)) = R.getD (u + i) 0 := by
      rw [tout _ (outside_of_disj hE hE.dR (VG.Offset.contains_base _ (by omega) (by omega)) (o := E.ql - E.W)
        (n := E.W) (by omega)), h.byte (by omega)]
    generalize hv : (BitVec.ofNat 64 (t.mem (off E.rand (u + i))).toNat &&&
      BitVec.ofNat 64 (if i = 0 then E.M else 255)).setWidth 8 = v
    have hst : WP isa (.block (copyByte ++ ([.subi .r5 .r5 1] : List Instr))) t fun t' =>
        t'.gpr .r3 = off E.rand (u + i + 1) ∧ t'.gpr .r4 = off E.F (E.o + i + 1) ∧
          t'.gpr .r6 = BitVec.ofNat 64 255 ∧ t'.gpr .r5 = t.gpr .r5 - BitVec.ofNat 64 1 ∧
          t'.gpr .r25 = t.gpr .r25 ∧ t'.gpr .r28 = t.gpr .r28 ∧
          t'.mem = t.mem.write (off E.F (E.o + i)) 1 v ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
      unfold copyByte
      prun [t3, t4, t6, exec_lbz' (show Reg.r3 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd, hwr, BitVec.add_zero,
        read_byte64, hv]
    have hw1 := write1_outside t.mem E.F (d := E.o + i) v (by simp only [SE.o, oNonce]; omega)
    refine WP.mono hst fun t' ⟨a3, a4, a6, a5, a25, a28, am, ard, awr⟩ => ⟨⟨by rw [a3, Nat.add_assoc],
      by rw [a4, Nat.add_assoc], ?_, a25.trans t25, a28.trans t28, ?_, ?_, ard.trans trd, awr.trans twr⟩, a5⟩
    · rw [a6, ite_eq_right (by omega)]
    · rw [am]; exact tout.trans (hw1.mono (by omega) (by omega))
    · intro j hj
      rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [hw1 _ (by rw [Mont.ofs_off0 E.F (by simp only [SE.o, oNonce]; omega)]; omega)]; exact tb j hj
      · have hd : ∀ k, (R.drop u).getD k 0 = R.getD (u + k) 0 := fun k => by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [write1_self, ← hv, hb, cpy, hd, hd]
        split
        · rename_i hj0; subst hj0
          exact mask_byte _ hM
        · rename_i hj0
          exact mask_byte_ff _
  · obtain ⟨-, -, -, t25, t28, tout, tb, -, -⟩ := ht
    prun [t25, t28, ← BitVec.ofNat_add]
    exact ⟨tout, tb⟩

end VG.Proof.Dsa.PPC64LE.Rnd
