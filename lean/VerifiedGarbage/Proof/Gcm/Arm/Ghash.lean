module

public import VerifiedGarbage.Impl.Gcm.Arm
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# GHASH on ARMv7: the contract

Untrusted: everything here is checked by Lean. `vg_ghash`'s contract on
32-bit ARM (`ghashArm`), a block as four words (`w4`), and its constant-time
proof (`ghash_ct`). As on RISC-V (`Proof/Gcm/RISCV64/Ghash.lean`), callers
take its correctness as a hypothesis (`GhashLaw`): its proof (`Law.lean`)
imports the polynomial algebra of `Proof/Gcm/Poly.lean`, which the AES-GCM,
AES-GCM-SIV and SM4-GCM proofs then need not import, and the registration
files supply it.
-/

@[expose] public section

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.Arm in
/-- 32-bit ARM contract for `vg_ghash(h = r0, y = r1, data = r2, n = r3,
scratch = [sp])`: replaces the block `Y` at `y` with `GHASH_H` continued from
`Y` over the `n` blocks at `data`, where `H` is the block at `h`.

The code may read `h` (16 bytes), `data` (`16 n` bytes) and the argument on
the stack (4 bytes at `sp`), and read and write `y` (16 bytes) and `scratch`
(256 bytes, whose contents on exit are unspecified). `y` and `scratch` may
not overlap each other, the other buffers or the stack argument, and none
may wrap around the end of the (32-bit) address space. The pointers and `n`
are public; `H`, `Y` and the data are secret. -/
def ghashArm : Contract Arm.isa where
  pre s :=
    let h : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let y : Region := ⟨State.addr (s.gpr .r1), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 256⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [h, data, args] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch ∧ y.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 256 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    blockAt s'.mem (State.addr (s.gpr .r1)) =
      ghashFrom (blockAt s.mem (State.addr (s.gpr .r0))) (blockAt s.mem (State.addr (s.gpr .r1)))
        (blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Gcm

namespace VG.Proof.Gcm.Arm

open VG VG.Arm VG.Impl.Gcm.Arm VG.Proof.Gcm
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Four words as a block -/

/-- Four words, the most significant first. -/
def w4 (a b c d : BitVec 32) : Block := a ++ b ++ c ++ d

theorem getLsbD_w4 (a b c d : BitVec 32) (i : Nat) :
    (w4 a b c d).getLsbD i =
      if i < 32 then d.getLsbD i else if i < 64 then c.getLsbD (i - 32)
      else if i < 96 then b.getLsbD (i - 64) else a.getLsbD (i - 96) := by
  simp only [w4, BitVec.getLsbD_append]
  repeat' split
  all_goals first | omega | rfl

theorem w4_xor (a b c d a' b' c' d' : BitVec 32) :
    w4 a b c d ^^^ w4 a' b' c' d' = w4 (a ^^^ a') (b ^^^ b') (c ^^^ c') (d ^^^ d') := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_w4, getLsbD_w4, getLsbD_w4]
  by_cases h1 : i < 32 <;> by_cases h2 : i < 64 <;> by_cases h3 : i < 96 <;>
    simp [h1, h2, h3, BitVec.getLsbD_xor]

/-- Bit `t` (from the left) of byte `j` of the block at `p`. -/
theorem blockAt_msb (m : Mem) (p : Addr) {j t : Nat} (hj : j < 16) (ht : t < 8) :
    (blockAt m p).getMsbD (8 * j + t) = (m (p + BitVec.ofNat 64 j)).getMsbD t := by
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.getMsbD_eq_getLsbD, decide_eq_true (show 8 * j + t < 128 by omega_arith),
    decide_eq_true ht, Bool.true_and, Bool.true_and,
    show 128 - 1 - (8 * j + t) = 8 * (15 - j) + (8 - 1 - t) by omega_arith,
    Proof.Aes.blockAt_bit m p hj (by omega_arith)]

/-- A block whose word `k` (little-endian) is `rev (W k)`. -/
theorem blockAt_w4 (m : Mem) (p : Addr) (W : Nat → BitVec 32)
    (h : ∀ k < 4, ∀ t < 4, m (p + BitVec.ofNat 64 (4 * k + t)) = (rev (W k)).extractLsb' (8 * t) 8) :
    blockAt m p = w4 (W 0) (W 1) (W 2) (W 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨j, b, hj, hb, rfl⟩ : ∃ j b, j < 16 ∧ b < 8 ∧ i = 8 * (15 - j) + b :=
    ⟨15 - i / 8, i % 8, by omega_arith, by omega_arith, by omega_arith⟩
  rw [Proof.Aes.blockAt_bit m p hj hb]
  obtain ⟨k, t, hk, ht, rfl⟩ : ∃ k t, k < 4 ∧ t < 4 ∧ j = 4 * k + t :=
    ⟨j / 4, j % 4, by omega_arith, by omega_arith, by omega_arith⟩
  rw [h k hk t ht, BitVec.getLsbD_extractLsb', decide_eq_true hb, Bool.true_and, rev_bit _ ht hb,
    getLsbD_w4]
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]; congr 1; omega_arith
  · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left (by omega_arith)]; congr 1; omega_arith
  · rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith)]; congr 1; omega_arith
  · rw [ite_eq_left (by omega_arith)]; congr 1; omega_arith

theorem w4_zero : w4 0 0 0 0 = 0 := by decide

/-- Four loads and `rev`s read a block. -/
theorem blockAt_rev (m : Mem) (p : Addr) :
    blockAt m p = w4 (rev (m.readW p 32)) (rev (m.readW (p + BitVec.ofNat 64 4) 32))
      (rev (m.readW (p + BitVec.ofNat 64 8) 32)) (rev (m.readW (p + BitVec.ofNat 64 12) 32)) := by
  refine blockAt_w4 m p (fun k => rev (m.readW (p + BitVec.ofNat 64 (4 * k)) 32)) (fun k hk t ht => ?_)
    |>.trans ?_
  · rw [rev_rev, ← Mem.readW_byte _ _ ht, BitVec.ofNat_add, BitVec.add_assoc]
  · rw [show 4 * 0 = 0 from rfl, BitVec.add_zero]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev hA : BitVec 32 := s₀.gpr .r0
abbrev yp : BitVec 32 := s₀.gpr .r1
abbrev dp : BitVec 32 := s₀.gpr .r2
abbrev nb : Nat := (s₀.gpr .r3).toNat
abbrev bp : BitVec 32 := stackArg s₀ 0
abbrev hR : Region := ⟨State.addr (hA s₀), 16⟩
abbrev yR : Region := ⟨State.addr (yp s₀), 16⟩
abbrev dR : Region := ⟨State.addr (dp s₀), 16 * nb s₀⟩
abbrev bR : Region := ⟨State.addr (bp s₀), 256⟩
abbrev aR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev H₀ : Block := blockAt s₀.mem (State.addr (hA s₀))
abbrev Y₀ : Block := blockAt s₀.mem (State.addr (yp s₀))

/-- Block `i`. -/
abbrev blk (i : Nat) : BitVec 32 := dp s₀ + BitVec.ofNat 32 (16 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀, aR s₀]
  wr : s₀.wr = [yR s₀, bR s₀]
  dHY : (hR s₀).Disjoint (yR s₀)
  dHB : (hR s₀).Disjoint (bR s₀)
  dYD : (yR s₀).Disjoint (dR s₀)
  dYB : (yR s₀).Disjoint (bR s₀)
  dDB : (dR s₀).Disjoint (bR s₀)
  dYA : (yR s₀).Disjoint (aR s₀)
  dBA : (bR s₀).Disjoint (aR s₀)
  fitH : (hA s₀).toNat + 16 ≤ 2 ^ 32
  fitY : (yp s₀).toNat + 16 ≤ 2 ^ 32
  fitD : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 32
  fitB : (bp s₀).toNat + 256 ≤ 2 ^ 32
  fitSp : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Gcm.ghashArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem blk_addr {i : Nat} (hi : i < nb s₀) :
    State.addr (blk s₀ i) = State.addr (dp s₀) + BitVec.ofNat 64 (16 * i) := by
  have := hp.fitD; exact addr_add (by omega_arith)

theorem blk_fit {i : Nat} (hi : i < nb s₀) : (blk s₀ i).toNat + 16 ≤ 2 ^ 32 := by
  have := hp.fitD
  simp only [blk]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨State.addr (blk s₀ i), 16⟩ (dR s₀) := by
  have := hp.fitD
  rw [hp.blk_addr hi]; exact VG.Proof.MdStream.Arm.sub_offset (by omega_arith) (by omega_arith)

end Pre

/-- The callee-saved registers, in the order of their slots. -/
def greg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11 | _ => .lr

/-! ## The law -/

/-- `vg_ghash` meets its contract: what `Law.lean` proves, which callers take
as a hypothesis so that they do not import its algebra. -/
class GhashLaw : Prop where
  correct : ∀ s, Proof.Gcm.ghashArm.pre s →
    ∃ t s', Exec isa Impl.Gcm.Arm.ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashArm.post s s'

theorem ghash_correct [GhashLaw] (s : State) (hs : Proof.Gcm.ghashArm.pre s) :
    ∃ t s', Exec isa Impl.Gcm.Arm.ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashArm.post s s' :=
  GhashLaw.correct s hs

/-! ## Constant time -/

/-- The initial taint: the pointers, `n` and the stack argument are public;
`r1` points at `y`, and the stack argument at the scratch buffer. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [16, 256],
    bases := [(.r1, 0)], argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {s : State} (h : Proof.Gcm.ghashArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  obtain hp := pre_of h
  obtain e : (⟨State.addr s.sp, 4⟩ : Region) = aR s := by simp [aR, stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.fitSp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.dYB
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fitY; have := hp.fitB
    rintro r (rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega_arith
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.dYA.symm
    · exact hp.dBA.symm
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Gcm.ghashArm.pre s₁) (h₂ : Proof.Gcm.ghashArm.pre s₂)
    (hpub : Proof.Gcm.ghashArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [yR, bR, yp, bp, p1, a0]
  · simp only [τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.fitSp hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.fitSp hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide)),
      show k / 4 = 0 by omega_arith]
    exact congrArg _ a0

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashArm.pre Proof.Gcm.ghashArm.pub Impl.Gcm.Arm.ghash :=
  VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Gcm.Arm
