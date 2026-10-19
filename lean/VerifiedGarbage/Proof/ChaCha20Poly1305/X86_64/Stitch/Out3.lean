module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Last3
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Setup

/-!
# ChaCha20 and Poly1305 together (x86-64): `tail3O`'s straight-line code

`Avx2Tail.setup3` with no data (`setup3_ok0`, as `Avx2Tail.setup3_ok`), and
`tail3O`'s output: the rounds' result plus the input states of the three
sets, stored to the 384 bytes at `rsi` (`out3_ok`, as `Avx2Tail.last3_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64.Avx2Tail (setup3 addIn3)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB YM3 Incs inT3 outT3 masks3Ok inT3_eval outT3_eval ym3_of yw run SRel
  SRel.init srun_ok)
open VG.Proof.ChaCha20.X86_64.Avx512 (Sym Sym.init xidx_zreg)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (bsize regn baseR wregs Ctx S0 byte_out)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (plus Consts)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (serialize)

/-- `setup3`'s check with no data. -/
def setup3Check0 : Bool :=
  match run 0 Sym.init setup3 with
  | some σ => !σ.dirty && masks3Ok σ && (List.range 3).all fun k => (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg (4 * k + r) p == inT3 k (4 * r + p % 4) (p / 4)
  | none => false

/-- The output of the three sets, stored to the 96 doublewords at `rsi`. -/
def out3Check : Bool :=
  match run 96 Sym.init (addIn3 ++ (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++ storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256))) with
  | some σ => (List.range 6).all fun j => (List.range 16).all fun i =>
      σ.mem 2 (16 * j + i) == outT3 (j / 2) i (j % 2)
  | none => false

theorem setup3Check0_eq : setup3Check0 = true := by decide +kernel
theorem out3Check_eq : out3Check = true := by decide +kernel

theorem setup3_ok0 {s : State} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9)) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup3) s fun s' =>
      HB 3 (fun j => ctr (S0 s) j) s' ∧ YM3 s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setup3Check0_eq
  unfold setup3Check0 at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup3 (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym3_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 k hk _ (by omega) _ (by omega)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (i / 4) + i % 4 = i by omega] at r
    rw [r, inT3_eval hi hk hi16 hl]
  · cases e

theorem out3_ok {s : State} (hc : Ctx 96 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 3 vs s) :
    WP isa (.block (addIn3 ++ (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++ (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256)))) s fun s' =>
      (∀ k < 384, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) =
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 96 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := out3Check_eq
  unfold out3Check at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 96 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr, h.rd, h.wr⟩
    refine byte_out (f := fun j => plus vs (S0 s) j) ?_
    have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e _ (by omega) _ (by omega),
      outT3_eval hz hi (by omega) (by omega) (by omega),
      show 2 * (k / 64 / 2) + k / 64 % 2 = k / 64 by omega] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
    exact d
  · cases e

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
