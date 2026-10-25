module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Framework.Offset

/-!
# An FFDH parameter candidate on PPC64LE: p to `out`

`writeP_ok`: `out`'s byte `i` is array 0's byte `k − 1 − i`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh)

/-- `writeP`'s first block: `out`, `out_len`, and the address of p's last
octet. -/
theorem writeHead_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z)
    (h31 : s.gpr .r31 = B) (h10 : s.gpr .r10 = off B 256)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hZ : 256 + k ≤ Z) :
    WP isa (.block [ldh .r4 hOut, ldh .r5 hLen, .add .r6 .r10 .r5, .subi .r6 .r6 1]) s fun s₂ =>
      (s₂.gpr .r6 = off B (256 + (k - 1)) ∧ s₂.gpr .r4 = O ∧ s₂.gpr .r5 = BitVec.ofNat 64 k ∧ s₂.mem = s.mem) ∧
        Keep [.r4, .r5, .r6] s s₂ := by
  have hnw := hs.nowrap
  refine WP.keep [.r4, .r5, .r6] ?_ (by decide)
  simp only [ldh, hOut, hLen]
  prun [h31, h10, hO, hL, hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith),
    off_add, BitVec.add_zero]
  rw [off_sub1 _ (by omega_arith)]; congr 2; omega_arith

theorem writeP_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z) (ho : Scr s O k)
    (h31 : s.gpr .r31 = B) (h10 : s.gpr .r10 = off B 256)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hZ : 256 + k ≤ Z) (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x) :
    WP isa writeP s fun t =>
      ((∀ i < k, t.mem (off O i) = s.mem (off B (256 + (k - 1 - i)))) ∧ Outside O 0 k s.mem t.mem) ∧
      Keep [.r0, .r4, .r5, .r6] s t := by
  have hnw := hs.nowrap
  have hno := ho.nowrap
  unfold writeP
  refine WP.seq ?_
  refine WP.mono (writeHead_ok hs h31 h10 hO hL hk hZ) fun s₂ ⟨⟨b6, b4, b5, m2⟩, k2⟩ => ?_
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r6 = off B (256 + (k - 1) - j) ∧ t.gpr .r4 = off O j ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = s.mem (off B (256 + (k - 1 - i)))) ∧ Keep [.r0, .r4, .r5, .r6] s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r6 0, .stb .r0 .r4 0, .addi .r4 .r4 1,
      .subi .r6 .r6 1] ++ ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t6, t4, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b6]; rfl, by rw [b4]; simp [off], by rw [m2]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k2.mono (by decide)⟩ b5) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hrd : InRegions (t.rd ++ t.wr) (off B (256 + (k - 1) - j)) 1 := by
    rw [tk.rd, tk.wr]; exact hs.ld (show 256 + (k - 1) - j + 1 ≤ Z by omega_arith)
  have hst : WP isa (.block [.lbz .r0 .r6 0, .stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r6 .r6 1,
      .subi .r5 .r5 1]) t fun t' => t' = ((({ (t.write .r0
        ((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64)) with
        mem := t.mem.write (off O j) 1 (((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64).setWidth 8) } :
          State).write .r4 (off O (j + 1))).write .r6
            (off B (256 + (k - 1) - j) - BitVec.ofNat 64 1)).write .r5 (t.gpr .r5 - BitVec.ofNat 64 1) := by
    prun [t6, t4, exec_lbz' (show Reg.r6 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_stb (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
      (ho.congr tk.wr).st (d := j) (n := 1) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem O (d := j) (((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64).setWidth 8)
    (by omega_arith)
  have harr : t.mem (off B (256 + (k - 1) - j)) = s.mem (off B (256 + (k - 1) - j)) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    have := hsep (off B (256 + (k - 1) - j)) (by omega_arith)
    rw [show ofs B (off B (256 + (k - 1) - j)) = 256 + (k - 1) - j from
      Mem.sub_ofNat_toNat B (by omega_arith)] at this
    omega_arith
  refine ⟨⟨?_, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; rw [off_sub1 _ (by omega_arith), show 256 + (k - 1) - j - 1 = 256 + (k - 1) - (j + 1) by omega_arith]
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self, Pub.read1_setWidth, show 256 + (k - 1 - i) = 256 + (k - 1) - i by omega_arith, ← harr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (t.mem (off B (256 + (k - 1) - i))).isLt
      omega_arith
  · exact tk.trans' (((((Keep.write _ _ _).trans (Keep.mem _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
