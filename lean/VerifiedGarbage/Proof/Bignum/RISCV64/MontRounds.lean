module

public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on RISC-V: the rounds

`rounds_ok`: the `w` rounds of `rounds`, from the accumulator 0, leave `T <
2m` with `T 2^(64 w) ≡ a b (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64
open VG.Proof.Bignum (round_lt round_step)

/-- `addi r r -1`: the counter decremented. -/
theorem dec_ok (s : State) (r : Reg) :
    WP isa (.block [.addi r r (-1)]) s fun s' => s' = s.write r (s.gpr r - BitVec.ofNat 64 1) := by
  brun

/-- The `w` rounds (`rounds`), counted by `a1` from `w`, over the words of
`a` (at `da` of `B`, pointed to by `a3`), from the accumulator 0: `T < 2m`
and `T 2^(64 w) ≡ a b (mod m)`, for `b < m` (`w` words each, at `dB` and
`dM`), only the accumulator's `w + 2` words changed. -/
theorem rounds_ok {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s₀ B Z)
    (ha8 : da % 8 = 0) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (h3 : s₀.gpr .a3 = off B da) (h5 : s₀.gpr .a5 = off B dA) (h4 : s₀.gpr .a4 = off B dB)
    (h7 : s₀.gpr .a7 = off B dM) (ht0 : s₀.gpr .t0 = BitVec.ofNat 64 w)
    (h1 : s₀.gpr .a1 = BitVec.ofNat 64 w)
    (hinv : ((word s₀.mem B dM).toNat * (s₀.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dM)
    (hz : wordsVal s₀.mem B dA (w + 1) = 0) (hb : wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w) :
    WP isa rounds s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem) ∧ Keep (roundRegs ++ ([.a1] : List Reg)) s₀ s := by
  have hnw := hs.nowrap
  let M := wordsVal s₀.mem B dM w
  let Bv := wordsVal s₀.mem B dB w
  let J : Nat → State → Prop := fun i s =>
    s.gpr .a3 = off B (da + 8 * i) ∧ Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧
    wordsVal s.mem B dA (w + 1) < 2 * M ∧
    2 ^ (64 * i) * wordsVal s.mem B dA (w + 1) % M = wordsVal s₀.mem B da i * Bv % M ∧
    Keep (roundRegs ++ ([.a1] : List Reg)) s₀ s
  have hJ0 : J 0 s₀ := by
    refine ⟨by rw [h3]; rfl, Outside.refl _ _ _ _, by rw [hz]; omega_arith, by rw [hz]; simp [wordsVal],
      Keep.refl _ _⟩
  refine wp_countdown (body := .seq round (.block [.addi .a1 .a1 (-1)])) (cnt := .a1) (N := w)
    (by omega_arith) (by omega_arith) J (fun i hi s hJ hc => ?_) hJ0 h1 |>.mono
    fun s ⟨_, jout, jlt, jeq, jk⟩ => ⟨⟨jlt, jeq, jout⟩, jk⟩
  obtain ⟨j3, jout, jlt, jeq, jk⟩ := hJ
  have keep : ∀ r ∈ [Reg.a4, .a5, .a7, .t0, .t1], s.gpr r = s₀.gpr r := fun r hr =>
    jk.gpr (by revert r hr; decide)
  have vM : wordsVal s.mem B dM w = M := jout.wordsVal (by omega_arith) (by omega_arith)
  have vB : wordsVal s.mem B dB w = Bv := jout.wordsVal (by omega_arith) (by omega_arith)
  have wM : word s.mem B dM = word s₀.mem B dM := jout.word (by omega_arith) (by omega_arith)
  have wa : word s.mem B (da + 8 * i) = word s₀.mem B (da + 8 * i) := jout.word (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (round_ok (dA := dA) (dB := dB) (dM := dM) (hs.congr jk.2.2) (by omega_arith) hA8 hB8 hM8 j3
    (by rw [keep .a4 (by decide), h4]) (by rw [keep .a5 (by decide), h5])
    (by rw [keep .a7 (by decide), h7]) (by rw [keep .t0 (by decide), ht0])
    (by rw [keep .t1 (by decide), wM]; exact hinv)
    (by omega_arith) hw' (by omega_arith) (by omega_arith) hB hM (by omega_arith) (by omega_arith))
    fun s₁ ⟨⟨k3, kout, u, hu, keq⟩, k₁⟩ => ?_)
  refine WP.mono (dec_ok s₁ .a1) fun s₂ e => ?_
  subst e
  rw [vM, vB, wa] at keq
  have hM0 : 0 < M := by omega_arith
  refine ⟨⟨by gsimp; rw [k3, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_, ?_⟩, ?_⟩
  · gsimp; exact jout.trans (kout.mono (Nat.le_refl _) (by omega_arith))
  · gsimp; exact round_lt keq jlt (s₀.mem.readW _ 64).isLt hb hu
  · gsimp
    rw [wordsVal_succ_top s₀.mem B da i, Nat.mul_succ, Nat.pow_add]
    exact round_step keq jeq
  · have k₂ : Keep [.a1] s₁ (s₁.write .a1 (s₁.gpr .a1 - BitVec.ofNat 64 1)) := Keep.write _ _ _
    exact Keep.trans' jk (Keep.trans' (k₁.mono (by decide)) (k₂.mono (by decide)))
  · gsimp
    rw [k₁.gpr (by decide)]

end VG.Proof.Bignum.RISCV64
