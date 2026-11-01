module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.BallLoop
import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# ML-DSA on PPC64LE: `vg_mldsa_sample_in_ball`, correctness

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/Ball.lean`). The function runs in
pieces: the prologue (`J0`, with `r27` the zero-extended `τ`), the sponge,
whose output is `H(c̃, 272)` (`J6`), the zeroing of `c` (`ZDone`), the setup
of the loop, which loads the sign bits (`setup_ok`, with `readW_leNat`: the
doubleword is the first 8 bytes of output as a little-endian number), and the
264 iterations of the loop (`BAt`, `body_ok`), after which `c` and `i` are
what `ballFold` computes.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.Ball

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (wp_loop_nz)
open VG.Spec.MlDsa (Zq q H IPoly n ofInt toRq)
open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-! ## The setup of the loop -/

/-- `lis` and `ori` of `q - 2`. -/
theorem q2_val :
    ((0x7F : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0xDFFF : BitVec 16).setWidth 64 =
      BitVec.ofNat 64 8380415 := by decide

/-- The first `i`, `256 - τ`. -/
theorem i0_val (x : BitVec 64) (h : (x.setWidth 32).toNat ≤ 256) :
    BitVec.ofNat 64 256 - zx x = BitVec.ofNat 64 (256 - (x.setWidth 32).toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, zx_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

section
variable {σ : State} (hp : SpOk (spOf σ) σ) (hτ : tau σ ≤ 256)
include hp hτ

theorem setup_ok {s : State} (h : ZDone σ s) : WP isa (.block bSetup) s (BAt σ 0) := by
  have g30 := h.env.r30
  have g31 := h.env.r31
  have g27 := h.r27
  have i9 : InRegions (s.rd ++ s.wr) ((spOf σ).scr + BitVec.ofNat 64 840) 8 := inScrRd hp h.env.wr (by decide)
  have hk : WP isa (.block bSetup) s fun u =>
      u.gpr .r9 = s.mem.readW ((spOf σ).scr + BitVec.ofNat 64 840) 64 ∧
      u.gpr .r5 = BitVec.ofNat 64 256 - zx (σ.gpr .r5) ∧
      u.gpr .r4 = (spOf σ).a + (BitVec.ofNat 64 256 - zx (σ.gpr .r5)) <<< 2 ∧
      u.gpr .r3 = (spOf σ).scr + BitVec.ofNat 64 848 ∧ u.gpr .r6 = BitVec.ofNat 64 264 ∧
      u.gpr .r7 = BitVec.ofNat 64 8380415 ∧
      (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
    prun [bSetup, exec_lis, exec_ori, q2_val, g30, g31, g27, i9]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun u ⟨g9, g5, g4, g3, g6, g7, gp, m, rd, wr, sp⟩ => ?_
  have e0 := i0_val (σ.gpr .r5) hτ
  have hSt : St σ 0 = (Vector.replicate n 0, i0 σ) := rfl
  refine ⟨h.env.regs hp m gp rd wr sp, by rw [m]; exact h.out, g3, ?_, ?_, ?_, g6, g7, by rw [m, hSt]; exact h.st⟩
  · rw [g4, e0, hSt, shl2 (by omega)]
  · rw [g5, e0, hSt]
  · show (u.gpr .r9).toNat = _
    rw [hSt, Nat.sub_self, Nat.pow_zero, Nat.div_one, g9, readW_leNat _ _ (X σ) fun k hk => by
      have := congrArg (fun L => L.getD k 0) h.out
      rw [MlKem.bytesAt_getD _ _ (by omega)] at this
      exact this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := leNat_lt ((X σ).take 8)
    rw [List.length_take, X_length] at this
    exact this

/-- The loop, from the zeroed polynomial. -/
theorem loop_ok {s : State} (h : ZDone σ s) : WP isa bLoop s (BAt σ 264) :=
  WP.seq (WP.mono (setup_ok hp hτ h) fun _ h0 =>
    wp_loop_nz (BAt σ) (N := 264) (by decide) (fun t ht s h => body_ok hp hτ ht h) (fun _ h => h) h0)

end

/-! ## The end -/

theorem St_all (σ : State) : St σ 264 = ballFold (tau σ) (X σ) := by
  simp only [St, ballFold, i0]; rw [List.take_of_length_le (by rw [List.length_drop, X_length])]

theorem end_ok {σ : State} (hp : SpOk (spOf σ) σ) {s : State} (h : BAt σ 264 s) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .r3 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (σ.gpr .r6) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.r5 (St_le _ _)) fun s' ⟨h3, hm, ha⟩ => ⟨by rw [h3, St_all], fun _ => by
    rw [hm]
    have hst := h.st
    rw [St_all] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map], ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : Pre σ) : WP isa Impl.MlDsa.PPC64LE.Sample.sampleInBall σ fun s' =>
    s'.gpr .r3 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (σ.gpr .r6) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' := by
  have hτ : tau σ ≤ 256 := by have := hp.tau_le; omega
  exact WP.seq (WP.mono (pro_ball hp.ok rfl (by simp) rfl rfl) fun s₁ ⟨j1, h27⟩ =>
    WP.seq (WP.mono (sponge_ok hp.ok (rate := 136) (outlen := 272) (by decide) (by decide) j1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp.ok h2 h27) fun _ h3 => WP.seq (WP.mono (loop_ok hp.ok hτ h3)
        fun _ h4 => end_ok hp.ok h4))))

end VG.Proof.MlDsa.PPC64LE.Sample.Ball
