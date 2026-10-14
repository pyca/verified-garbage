module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48To
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The blocks after the last group, out of place

`remTo_ok`: `StitchZHTo.remTo` is `StitchZH.rem` reading the `r` blocks
after the last group from the plaintext (at `rdx + r8`, `r8` holding
`src - dst`) and writing them to the output: the counter after all the
blocks (`remSetup_ok`), the keystream of the `r` blocks while the last group
of the output is hashed (`ksSel_ok`, on the in-place view `dst s₀`), the
`r` blocks encrypted and their products with their powers added
(`remLoops_ok`), and reduced into `Y`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR addr_eq in_sub in_sub_int in_rdwr blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (gq lastG)
open VG.Impl.Gcm.X86_64.StitchZH (ksSel remWith remSetup remBody tailR remLoops)
open VG.Impl.Gcm.X86_64.StitchZHTo (remTo)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv QG gq_ok FinOk)
open VG.Proof.Gcm.X86_64.StitchZTo (EInvTo dst dst_gpr_ne dst_mem sAddr oAddr ctbT blocks_ctr32To finalTo_ok)
open VG.Proof.Gcm.X86_64.StitchZH (RemOk REnv RInv1 ksR ksSel_ok QG.ksR remSetup_ok remLoops_ok keys_of cmp16_ok
  laneAcc_congr zeroZ_ok)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- Before the loop: `rdx` at the output blocks, `r8` at the plaintext
blocks, `r10 = 0`, and the products cleared. -/
theorem remPreTo_ok (s : State) :
    WP isa (.block (([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] : List Instr) ++
      ([.alu .add .r8 (.reg .rdx)] : List Instr) ++ Impl.Gcm.X86_64.StitchAvx.zero)) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r8 = s.gpr .r8 + (s.gpr .rdx + 256) ∧
        s'.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
        (∀ q, q ≠ .rdx → q ≠ .r10 → q ≠ .r8 → s'.gpr q = s.gpr q) ∧
        (∀ l < 4, s'.zlane .xmm8 l = 0 ∧ s'.zlane .xmm9 l = 0 ∧ s'.zlane .xmm10 l = 0) ∧
        (∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → ∀ l < 4, s'.zlane x l = s.zlane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  rw [WP.block_append_iff]
  have hA : WP isa (.block ([.alu .add .rdx (.imm 256), .mov32 .r10 (.imm 0)] ++
      ([.alu .add .r8 (.reg .rdx)] : List Instr))) s fun s₁ =>
      s₁.gpr .rdx = s.gpr .rdx + 256 ∧ s₁.gpr .r8 = s.gpr .r8 + (s.gpr .rdx + 256) ∧
      s₁.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      (∀ q, q ≠ .rdx → q ≠ .r10 → q ≠ .r8 → s₁.gpr q = s.gpr q) ∧ (∀ x l, s₁.zlane x l = s.zlane x l) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, readSrc32, arithFlags, State.setFlags, State.setReg32, isa, State.setReg, e256, reduceCtorEq,
      ↓reduceIte, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, rfl, fun q h1 h2 h3 => by simp only [h1, h2, h3, ↓reduceIte], fun _ _ => rfl, trivial,
      trivial, trivial⟩
  refine WP.mono hA fun s₁ ⟨d₁, r₁, z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (zeroZ_ok s₁) fun s' ⟨zz, f', g', m', rd', wr'⟩ =>
    ⟨by rw [g', d₁], by rw [g', r₁], by rw [g', z₁], fun q h1 h2 h3 => by rw [g', g₁ q h1 h2 h3],
      zz, fun x h8 h9 h10 l hl => by rw [f' x h8 h9 h10 l hl, l₁], by rw [m', m₁],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩


end VG.Proof.Gcm.X86_64.StitchZHTo
