module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Poly1305.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
meta import VerifiedGarbage.Proof.Poly1305.Scratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Poly1305.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Poly1305.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wide
meta import VerifiedGarbage.Spec.Poly1305
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.TCB.Artifact

/-! ### `Poly1305.RISCV64.Buffer`, which this module and modules that import it used -/

section

/-! ### `Poly1305.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# Poly1305: the RISC-V contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts (`Spec/Poly1305/Contract.lean`), which imply these
(`Contract.Implies`). No function uses the stack or a working space.
-/

@[expose] public section

namespace VG.Proof.Poly1305

open Spec.Poly1305

open RISCV64 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let key : Region := ⟨s.gpr .a1, 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key
  post s s' := Repr s'.mem (s.gpr .a0) (bytesAt s.mem (s.gpr .a1) 32) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

open RISCV64 in
/-- `vg_poly1305_update(state = a0, count = a1, data = a2, len = a3)`: only
`count mod 16`, the number of bytes buffered, matters. -/
def updateRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    s.rd = [data] ∧ s.wr = [state] ∧ state.Disjoint data ∧ (s.gpr .a0).toNat % 8 = 0
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .a0) key msg →
    (s.gpr .a1).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .a0) key (msg ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open RISCV64 in
/-- `vg_poly1305_finalize(state = a0, count = a1, out = a2)`: only `count mod
16`, the number of bytes buffered, matters. -/
def finalizeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let out : Region := ⟨s.gpr .a2, 16⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧ (s.gpr .a0).toNat % 8 = 0
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .a0) key msg →
    (s.gpr .a1).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .a2) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

end VG.Proof.Poly1305

end

end

/-! ### `Poly1305.RISCV64.State`, which this module and modules that import it used -/

section

/-! ### `Poly1305.RISCV64.Reduce`, which this module and modules that import it used -/

section

/-! ### `Poly1305.RISCV64.Absorb`, which this module and modules that import it used -/

section

/-!
# Poly1305 on RISC-V: absorbing a block

The arithmetic in radix `2⁶⁴` of `Proof/Poly1305/Limbs64.lean` (as on AArch64,
`Proof/Poly1305/AArch64/Radix64/Absorb.lean`), with the sums of
`Proof/Framework/RISCV64/Wide.lean`: `absorb_ok` says that absorbing a block
multiplies the accumulator plus the block by the clamped `r`, modulo `p`,
keeping its top word at most 4.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Proof.Poly1305.Limbs64
open VG.Spec.Poly1305 (P)

/-- The accumulator in `t0`–`t2`. -/
abbrev hv (s : State) : Nat := val3 s H0 H1 H2

/-- The key in the registers: `r0`, `r1 = 4 q` and `s1 = 5 q`, the clamped `r`
being `R`. -/
def Keys (R : Nat) (s : State) : Prop :=
  ∃ q, (s.gpr R0).toNat < 2 ^ 60 ∧ (s.gpr R1).toNat = 4 * q ∧ q < 2 ^ 58 ∧
    (s.gpr S1).toNat = 5 * q ∧ (s.gpr R0).toNat + 2 ^ 64 * (s.gpr R1).toNat = R

/-- The bound on the accumulator between blocks. -/
def Bounds (s : State) : Prop := (s.gpr H2).toNat ≤ 4

/-- The registers absorbing a block writes. -/
abbrev absorbRegs : List Reg := [H0, H1, H2, X0, X1, Y0, Y1, T1, T2]

/-- The little-endian doubleword at `off(b)`, as a number. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

theorem Keys.of_regs {R : Nat} {s s' : State} (hk : Keys R s)
    (h : ∀ r ∈ [R0, R1, S1], s'.gpr r = s.gpr r) : Keys R s' := by
  simpa only [Keys, h R0 (by simp), h R1 (by simp), h S1 (by simp)] using hk

theorem Keeps.keys {rs : List Reg} {R : Nat} {s s' : State} (hk : Keys R s) (h : Keeps rs s s')
    (hr : R0 ∉ rs ∧ R1 ∉ rs ∧ S1 ∉ rs := by decide) : Keys R s' :=
  hk.of_regs fun r hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    exacts [h.1 _ hr.1, h.1 _ hr.2.1, h.1 _ hr.2.2]

/-! ## Adding the block -/

/-- `h2 += pad`. -/
def padI (pad : Bool) : List Instr := if pad then [.addi H2 H2 1] else []

theorem addBlock_eq (b : Reg) (off : Nat) (pad : Bool) : addBlock b off pad false =
    Impl.Words64.RISCV64.loadLE64 X0 T1 T2 b off ++
      (Impl.Words64.RISCV64.loadLE64 X1 T1 T2 b (off + 8) ++
      (Impl.Words.RISCV64.add3 H0 H1 H2 X0 X1 ++ padI pad)) := by
  simp only [addBlock, padI, List.append_assoc, Bool.false_eq_true, ite_false]

theorem addBlock_eq_wide (b : Reg) (off : Nat) (pad : Bool) : addBlock b off pad true =
    .load .d X0 b off :: .load .d X1 b (off + 8) ::
      (Impl.Words.RISCV64.add3 H0 H1 H2 X0 X1 ++ padI pad) := by
  simp only [addBlock, padI, ite_true, List.cons_append, List.nil_append]

theorem padI_ok (s : State) (pad : Bool) :
    WP isa (.block (padI pad)) s fun s' =>
      ((s.gpr H2).toNat + pad.toNat < 2 ^ 64 → (s'.gpr H2).toNat = (s.gpr H2).toNat + pad.toNat) ∧
      Keeps [H2] s s' := by
  cases pad
  · exact WP.block_nil ⟨fun _ => rfl, Keeps.refl _ _⟩
  · apply WP.of_runBlock
    simp only [padI, ite_true, runBlock_cons, runStep_some, runBlock_nil,
      exec_addi (show imm12 1 by decide), Option.some.injEq, exists_eq_left']
    refine ⟨fun h => ?_, (Keeps.refl [H2] s).write _ (by decide)⟩
    rw [RegUpd.gpr_write_self, BitVec.toNat_add, show (BitVec.ofInt 64 1).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt h

theorem upd3_keeps {s s' : State} {d t₁ t₂ : Reg} {v : BitVec 64} (h : Words64.Upd3 s s' d t₁ t₂ v) :
    Keeps [d, t₁, t₂] s s' :=
  ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact h.other r hr.1 hr.2.1 hr.2.2, h.mem, h.rd, h.wr, h.sp⟩

/-- A register write keeps everything else. -/
theorem upd_keeps {s s' : State} {d : Reg} {v : BitVec 64} (h : VG.RISCV64.Steps.Upd s s' d v) : Keeps [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.mem, h.rd, h.wr, h.sp⟩

/-- The sum and the pad, after the block's words are in `X0` and `X1`. -/
theorem addTail_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) {s₂ : State}
    (x₀ : (s₂.gpr X0).toNat = word s.mem (s.gpr b) off)
    (x₁ : (s₂.gpr X1).toNat = word s.mem (s.gpr b) (off + 8)) (k₂ : Keeps [X0, X1, T1, T2] s s₂) :
    WP isa (.block (Impl.Words.RISCV64.add3 H0 H1 H2 X0 X1 ++ padI pad)) s₂ fun s' =>
      (hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat) < 2 ^ 192 →
        hv s' = hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) ∧
      Keeps [H0, H1, H2, X0, X1, T1, T2] s s' := by
  refine WP.block_append (WP.mono add3_ok fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.mono (padI_ok s₃ pad) fun s₄ ⟨e₄, k₄⟩ => ?_
  refine ⟨fun hlt => ?_, ((k₂.trans k₃).trans k₄).mono⟩
  have hv₂ : val3 s₂ H0 H1 H2 = hv s := by
    simp only [val3, hv, k₂.gpr' (r := H0), k₂.gpr' (r := H1), k₂.gpr' (r := H2)]
  rw [hv₂, x₀, x₁] at e₃
  have hp := Bool.toNat_le pad
  have w₀ := (s₃.gpr H0).isLt; have w₁ := (s₃.gpr H1).isLt
  have m₀ := (s.mem.readW (s.gpr b + BitVec.ofNat 64 off) 64).isLt
  have m₁ := (s.mem.readW (s.gpr b + BitVec.ofNat 64 (off + 8)) 64).isLt
  have hh := (s.gpr H0).isLt; have hh1 := (s.gpr H1).isLt
  rw [Nat.mod_eq_of_lt (by omega_using [hlt, hp])] at e₃
  have e₄ := e₄ (by simp only [val3, word, hv] at e₃ hlt; omega_using [e₃, hlt, hp, w₀, w₁])
  simp only [hv, val3, k₄.gpr' (r := H0), k₄.gpr' (r := H1), e₄]
  simp only [val3] at e₃
  have hvs : hv s = (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat := rfl
  omega_using [e₃, hp, hvs]

theorem addBlock_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (addBlock b off pad wide)) s fun s' =>
      (hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat) < 2 ^ 192 →
        hv s' = hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) ∧
      Keeps [H0, H1, H2, X0, X1, T1, T2] s s' := by
  simp only [absorbRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hb
  cases wide
  · rw [addBlock_eq]
    refine WP.block_append (WP.mono (Words64.loadLE64_ok (Ne.symm b3) (Ne.symm b7) (by decide)
      (Ne.symm b8) (by decide) (by decide) (by omega_using [ho]) h0) fun s₁ u₁ => ?_)
    have hb₁ : s₁.gpr b = s.gpr b := u₁.other b b3 b7 b8
    refine WP.block_append (WP.mono (Words64.loadLE64_ok (Ne.symm b4) (Ne.symm b7) (by decide)
      (Ne.symm b8) (by decide) (by decide) (by omega_using [ho])
      (by rw [hb₁, u₁.rd, u₁.wr]; exact h8)) fun s₂ u₂ => ?_)
    exact addTail_ok s b off pad (by rw [u₂.other _ (by decide) (by decide) (by decide), u₁.gpr])
      (by rw [u₂.gpr, u₁.mem, hb₁]) ((upd3_keeps u₁).trans (upd3_keeps u₂)).mono
  · have a0 := hal rfl
    have a8 : (s.gpr b + BitVec.ofNat 64 (off + 8)).toNat % 8 = 0 := by
      rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (s.gpr b + BitVec.ofNat 64 off).isLt
      omega_using [a0]
    rw [addBlock_eq_wide]
    refine VG.RISCV64.Steps.wp_ld (a := s.gpr b + BitVec.ofNat 64 off) (by omega_using [ho]) rfl a0 h0 fun s₁ u₁ => ?_
    have hb₁ : s₁.gpr b = s.gpr b := u₁.other b b3
    refine VG.RISCV64.Steps.wp_ld (a := s.gpr b + BitVec.ofNat 64 (off + 8)) (by omega_using [ho]) (by rw [hb₁]) a8
      (by rw [u₁.rd, u₁.wr]; exact h8) fun s₂ u₂ => ?_
    exact addTail_ok s b off pad (by rw [u₂.other _ (by decide), u₁.gpr])
      (by rw [u₂.gpr, u₁.mem]) ((upd_keeps (d := X0) u₁).trans (upd_keeps (d := X1) u₂)).mono

/-! ## The products, folded -/

theorem notFour_bits : ∀ i : Fin 64, (BitVec.ofInt 64 (-4)).getLsbD i.val = decide (2 ≤ i.val) := by
  decide

/-- `andi` with `-4` clears the two low bits. -/
theorem andm4_toNat (x : BitVec 64) :
    (x &&& BitVec.ofInt 64 (-4)).toNat = x.toNat - x.toNat % 4 := by
  have e : x &&& BitVec.ofInt 64 (-4) = (x >>> 2) <<< 2 := by
    ext i hi
    have hb := notFour_bits ⟨i, hi⟩
    rw [BitVec.getLsbD_eq_getElem hi] at hb
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, hb]
    by_cases h : i < 2
    · simp [h]
    · simp [h]
      rw [show 2 + (i - 2) = i by omega_using [h], BitVec.getLsbD_eq_getElem hi]
      simp; omega_using [h]
  rw [e, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega_using [])]
  omega_using []

theorem and3_toNat' (x : BitVec 64) : (x &&& BitVec.ofInt 64 3).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 3).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The first four instructions of `fold`: `t mod 4` and `5 ⌊t / 4⌋`. -/
def foldA : List Instr :=
  [.logicImm .and H2 Y1 3, .logicImm .and T1 Y1 (-4), .shift .srl .d T2 Y1 2, .add T1 T1 T2]

theorem foldA_ok (s : State) :
    WP isa (.block foldA) s fun s' =>
      (s'.gpr H2).toNat = (s.gpr Y1).toNat % 4 ∧
      ((s.gpr Y1).toNat < 2 ^ 63 → (s'.gpr T1).toNat = 5 * ((s.gpr Y1).toNat / 4)) ∧
      Keeps [H2, T1, T2] s s' := by
  apply WP.of_runBlock
  simp only [foldA, runBlock_cons, runStep_some, runBlock_nil, exec_logicImm (show imm12 3 by decide),
    exec_logicImm (show imm12 (-4) by decide), exec_shift_d (show 2 < 64 by decide), exec_add,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun h => ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, and3_toNat']
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [BitVec.toNat_add, andm4_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega_using [h]
  · exact ((((Keeps.refl [H2, T1, T2] s).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)

theorem mulSmall_ok (s : State) :
    WP isa (.block [.mul T2 H2 R0]) s fun s' =>
      ((s.gpr H2).toNat * (s.gpr R0).toNat < 2 ^ 64 →
        (s'.gpr T2).toNat = (s.gpr H2).toNat * (s.gpr R0).toNat) ∧ Keeps [T2] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun h => ?_, (Keeps.refl _ _).write _ (by decide)⟩
  rw [RegUpd.gpr_write_self, BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem mul_eq : products ++ combine ++ fold =
    Impl.Words.RISCV64.mulWide X0 X1 H0 R0 ++ (Impl.Words.RISCV64.mulWide Y0 Y1 H0 R1 ++
    (Impl.Words.RISCV64.mulAdd X0 X1 T1 T2 H1 S1 ++ (Impl.Words.RISCV64.mulAdd Y0 Y1 T1 T2 H1 R0 ++
    (Impl.Words.RISCV64.mulAddSmall Y0 Y1 T1 H2 S1 ++ (([.mul T2 H2 R0] : List Instr) ++
    (Impl.Words.RISCV64.add2 Y0 Y1 X1 T2 ++ (foldA ++
    Impl.Words.RISCV64.addW3 H0 H1 H2 X0 Y0 H2 T1))))))) := by
  simp only [products, combine, fold, foldA, List.append_assoc, List.cons_append, List.nil_append]

theorem mul_ok (s₁ : State) {q : Nat}
    (hr0 : (s₁.gpr R0).toNat < 2 ^ 60) (hr1 : (s₁.gpr R1).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s₁.gpr S1).toNat = 5 * q) :
    WP isa (.block (products ++ combine ++ fold)) s₁ fun s' =>
      ((s₁.gpr H2).toNat ≤ 6 →
        hv s' % P = (hv s₁ * ((s₁.gpr R0).toNat + 2 ^ 64 * (s₁.gpr R1).toNat)) % P ∧
        (s'.gpr H2).toNat ≤ 4) ∧ Keeps absorbRegs s₁ s' := by
  rw [mul_eq]
  refine WP.block_append (WP.mono mulWide_ok fun s₂ ⟨e₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono mulWide_ok fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono mulAdd_ok fun s₄ ⟨e₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono mulAdd_ok fun s₅ ⟨e₅, k₅⟩ => ?_)
  refine WP.block_append (WP.mono mulAddSmall_ok fun s₆ ⟨e₆, k₆⟩ => ?_)
  refine WP.block_append (WP.mono (mulSmall_ok s₆) fun s₇ ⟨e₇, k₇⟩ => ?_)
  refine WP.block_append (WP.mono add2_ok fun s₈ ⟨e₈, k₈⟩ => ?_)
  refine WP.block_append (WP.mono (foldA_ok s₈) fun s₉ ⟨f₁, f₂, k₉⟩ => ?_)
  refine WP.mono addW3_ok fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  refine ⟨fun a2 => ?_, (((((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans
    k₈).trans k₉).trans k₁₀)).mono⟩
  have a0 := (s₁.gpr H0).isLt; have a1 := (s₁.gpr H1).isLt
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds a0 a1 a2 hr0 hq
  -- x = h0 r0, y = h0 r1
  have k₂₃ := k₂.trans k₃
  rw [k₂.gpr' (r := H0), k₂.gpr' (r := R1), hr1] at e₃
  -- x += h1 s1
  rw [k₃.gpr' (r := X0), k₃.gpr' (r := X1), e₂, k₂₃.gpr' (r := H1), k₂₃.gpr' (r := S1), hs1,
    Nat.mod_eq_of_lt (by omega_using [b1, b2])] at e₄
  have k₂₄ := k₂₃.trans k₄
  -- y += h1 r0
  rw [k₄.gpr' (r := Y0), k₄.gpr' (r := Y1), e₃, k₂₄.gpr' (r := H1), k₂₄.gpr' (r := R0),
    Nat.mod_eq_of_lt (by omega_using [b3, b4])] at e₅
  have k₂₅ := k₂₄.trans k₅
  -- y += h2 s1
  rw [e₅, k₂₅.gpr' (r := H2), k₂₅.gpr' (r := S1), hs1, Nat.mod_eq_of_lt (by omega_using [b3, b4, b5])] at e₆
  have e₆ := e₆ b5
  have k₂₆ := k₂₅.trans k₆
  -- h2 r0
  rw [k₂₆.gpr' (r := H2), k₂₆.gpr' (r := R0)] at e₇
  have e₇ := e₇ (by omega_using [hr0, b6])
  -- the top word
  have x0 := (s₄.gpr X0).isLt; have x1 := (s₄.gpr X1).isLt
  have y0 := (s₆.gpr Y0).isLt; have y1 := (s₆.gpr Y1).isLt
  have r14 : s₇.gpr Y0 = s₆.gpr Y0 := k₇.gpr'
  have r15 : s₇.gpr Y1 = s₆.gpr Y1 := k₇.gpr'
  have r13 : s₇.gpr X1 = s₄.gpr X1 := ((k₅.trans k₆).trans k₇).gpr'
  rw [r14, r15, r13, e₇, Nat.mod_eq_of_lt (by omega_using [hr0, e₄, e₆, b1, b2, b3, b4, b5, b6])] at e₈
  have u0 := (s₈.gpr Y0).isLt
  have ht : (s₈.gpr Y1).toNat < 2 ^ 63 := by
    omega_using [hr0, e₄, e₆, b1, b2, b3, b4, b5, b6, e₈, u0]
  have f₂ := f₂ ht
  have hX0 : s₉.gpr X0 = s₄.gpr X0 := ((((k₅.trans k₆).trans k₇).trans k₈).trans k₉).gpr'
  have hY0 : s₉.gpr Y0 = s₈.gpr Y0 := k₉.gpr'
  simp only [val3] at e₁₀
  rw [hX0, hY0, f₁, f₂, Nat.mod_eq_of_lt (by omega_using [hr0, e₄, e₆, b1, b2, b3, b4, b5, b6, e₈, u0, x0])] at e₁₀
  have w0 := (s₁₀.gpr H0).isLt; have w1 := (s₁₀.gpr H1).isLt
  have hu : (s₈.gpr Y0).toNat + 2 ^ 64 * (((s₆.gpr Y0).toNat + (s₄.gpr X1).toNat) / 2 ^ 64) =
      (s₆.gpr Y0).toNat + (s₄.gpr X1).toNat := by
    omega_using [e₈, u0, y0, x1]
  have ht' : (s₈.gpr Y1).toNat = (s₆.gpr Y1).toNat + (s₁.gpr H2).toNat * (s₁.gpr R0).toNat +
      ((s₆.gpr Y0).toNat + (s₄.gpr X1).toNat) / 2 ^ 64 := by
    omega_using [e₈, hu, u0]
  rw [ht'] at e₁₀
  obtain ⟨m, hb⟩ := absorb_arith (q := q)
    (w0 := (s₁₀.gpr H0).toNat) (w1 := (s₁₀.gpr H1).toNat) (w2 := (s₁₀.gpr H2).toNat)
    (x0 := (s₄.gpr X0).toNat) (x1 := (s₄.gpr X1).toNat)
    (y0 := (s₆.gpr Y0).toNat) (y1 := (s₆.gpr Y1).toNat) (u0 := (s₈.gpr Y0).toNat)
    (c1 := ((s₆.gpr Y0).toNat + (s₄.gpr X1).toNat) / 2 ^ 64)
    a0 a1 a2 hr0 hq e₄ x0 e₆ hu u0 (by omega_using [e₁₀]) w0 w1
  refine ⟨?_, hb⟩
  rw [hv, val3, m, hr1]

theorem absorb_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) {q : Nat}
    (hr0 : (s.gpr R0).toNat < 2 ^ 60) (hr1 : (s.gpr R1).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr S1).toNat = 5 * q) (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (absorb b off pad wide)) s fun s' =>
      ((s.gpr H2).toNat ≤ 4 →
        hv s' % P = ((hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) * ((s.gpr R0).toNat + 2 ^ 64 * (s.gpr R1).toNat)) % P ∧
        (s'.gpr H2).toNat ≤ 4) ∧ Keeps absorbRegs s s' := by
  rw [show absorb b off pad wide = addBlock b off pad wide ++ (products ++ combine ++ fold) by
    simp only [absorb, List.append_assoc]]
  refine WP.block_append (WP.mono (addBlock_ok s b off pad wide ho h0 h8 hal hb) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have r0₁ : s₁.gpr R0 = s.gpr R0 := k₁.gpr'
  have r1₁ : s₁.gpr R1 = s.gpr R1 := k₁.gpr'
  have s1₁ : s₁.gpr S1 = s.gpr S1 := k₁.gpr'
  refine WP.mono (mul_ok s₁ (by rw [r0₁]; exact hr0) (by rw [r1₁]; exact hr1) hq (by rw [s1₁]; exact hs1))
    fun s' ⟨hm, k⟩ => ⟨fun hh2 => ?_, (k₁.trans k).mono⟩
  have hp1 : pad.toNat ≤ 1 := Bool.toNat_le pad
  have hw0 := (s.mem.readW (s.gpr b + BitVec.ofNat 64 off) 64).isLt
  have hw8 := (s.mem.readW (s.gpr b + BitVec.ofNat 64 (off + 8)) 64).isLt
  have g0 := (s.gpr H0).isLt; have g1 := (s.gpr H1).isLt
  have e₁ := e₁ (by simp only [word, hv, val3]; omega_using [hh2, hp1, hw0, hw8, g0, g1])
  have a0 := (s₁.gpr H0).isLt; have a1 := (s₁.gpr H1).isLt
  obtain ⟨hv', hb'⟩ := hm (add_arith g0 g1 hh2 hw0 hw8 hp1 e₁ a0 a1)
  refine ⟨?_, hb'⟩
  rw [hv', show hv s₁ = _ from e₁, r0₁, r1₁]

end VG.Proof.Poly1305.RISCV64

end

end

/-!
# Poly1305 on RISC-V: the final reduction

`reduce_ok`: `reduce` leaves the accumulator modulo `p`, as on AArch64
(`Proof/Poly1305/AArch64/Radix64/Reduce.lean`): `g = h + 5` is selected if it
reaches `2¹³⁰`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P)

theorem select_keep (x y : BitVec 64) : y ^^^ ((x ^^^ y) &&& ((0 : BitVec 64) + BitVec.ofInt 64 (-1))) = x := by
  rw [show (0 : BitVec 64) + BitVec.ofInt 64 (-1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
    ← BitVec.xor_assoc, BitVec.xor_comm y x, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem select_take (x y : BitVec 64) : y ^^^ ((x ^^^ y) &&& ((1 : BitVec 64) + BitVec.ofInt 64 (-1))) = y := by
  rw [show (1 : BitVec 64) + BitVec.ofInt 64 (-1) = 0 by decide]
  simp

theorem reduce_eq : reduce = plus5 ++ (mask ++
    (selectLimb H0 X0 ++ selectLimb H1 X1 ++ selectLimb H2 Y0)) := by
  simp only [reduce, List.append_assoc]

theorem plus5_ok (s : State) :
    WP isa (.block plus5) s fun s' =>
      val3 s' X0 X1 Y0 = (hv s + 5) % 2 ^ 192 ∧ Keeps [T1, X0, X1, Y0, T1] s s' := by
  refine WP.block_cons_iff.mpr ⟨_, exec_li (show imm12 5 by decide), ?_⟩
  refine WP.mono addW3_ok fun s' ⟨e, k⟩ => ⟨?_, ((Keeps.refl [T1] s).write _ (by decide)).trans k⟩
  rw [e]
  simp only [val3, hv, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  rfl

theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' =>
      s'.gpr T1 = (s.gpr Y0 >>> 2) + BitVec.ofInt 64 (-1) ∧
      s'.gpr Y0 = s.gpr Y0 &&& BitVec.ofInt 64 3 ∧ Keeps [T1, Y0] s s' := by
  apply WP.of_runBlock
  simp only [mask, runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 2 < 64 by decide),
    exec_addi (show imm12 (-1) by decide), exec_logicImm (show imm12 3 by decide),
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (((Keeps.refl _ s).write _ (by decide)).write _ (by decide)).write _ (by decide)⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]

theorem select_ok (s : State) :
    WP isa (.block (selectLimb H0 X0 ++ selectLimb H1 X1 ++ selectLimb H2 Y0)) s fun s' =>
      s'.gpr H0 = s.gpr X0 ^^^ ((s.gpr H0 ^^^ s.gpr X0) &&& s.gpr T1) ∧
      s'.gpr H1 = s.gpr X1 ^^^ ((s.gpr H1 ^^^ s.gpr X1) &&& s.gpr T1) ∧
      s'.gpr H2 = s.gpr Y0 ^^^ ((s.gpr H2 ^^^ s.gpr Y0) &&& s.gpr T1) ∧
      Keeps [H0, H1, H2, T2] s s' := by
  apply WP.of_runBlock
  simp only [selectLimb, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec_logic, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · exact (((((((((Keeps.refl _ s).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)).write _ (by decide)

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      ((s.gpr H2).toNat ≤ 4 → hv s' = hv s % P) ∧
      Keeps [H0, H1, H2, X0, X1, Y0, T1, T2] s s' := by
  have g0 := (s.gpr H0).isLt; have g1 := (s.gpr H1).isLt
  rw [reduce_eq]
  refine WP.block_append (WP.mono (plus5_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (mask_ok s₁) fun s₂ ⟨m₁, m₂, k₂⟩ => ?_)
  refine WP.mono (select_ok s₂) fun s₃ ⟨c₁, c₂, c₃, k₃⟩ => ?_
  refine ⟨fun hh2 => ?_, ((k₁.trans k₂).trans k₃).mono⟩
  have hv5 : hv s + 5 < 2 ^ 192 := by simp only [hv, val3]; omega_using [g0, g1, hh2]
  rw [Nat.mod_eq_of_lt hv5] at e₁
  simp only [val3] at e₁
  have ga := (s₁.gpr X0).isLt; have gd := (s₁.gpr X1).isLt
  have hg2 : (s₁.gpr Y0).toNat ≤ 5 := by simp only [hv, val3] at e₁; omega_using [g0, g1, hh2, e₁, ga, gd]
  have k₁₂ := k₁.trans k₂
  rw [k₁₂.gpr' (r := H0), k₂.gpr' (r := X0), m₁] at c₁
  rw [k₁₂.gpr' (r := H1), k₂.gpr' (r := X1), m₁] at c₂
  rw [k₁₂.gpr' (r := H2), m₂, m₁] at c₃
  have ht : (s₁.gpr Y0 >>> 2).toNat = (s₁.gpr Y0).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [hv, val3, c₁, c₂, c₃]
  simp only [hv, val3] at e₁
  have hP : P = 2 ^ 130 - 5 := rfl
  by_cases hge : 4 ≤ (s₁.gpr Y0).toNat
  · have h1 : s₁.gpr Y0 >>> 2 = 1 := BitVec.eq_of_toNat_eq (by
      rw [ht]; show _ = 1; omega_using [hg2, hge])
    rw [h1, select_take, select_take, select_take, and3_toNat']
    have ge : P ≤ (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat := by
      omega_using [e₁, hg2, hP, hge, ga, gd]
    have lt : (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat - P <
        P := by omega_using [g0, g1, hh2, e₁, hP, ge]
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    omega_using [g0, g1, hh2, e₁, hP, ge, lt, ga, gd, hge, hg2]
  · have h0 : s₁.gpr Y0 >>> 2 = 0 := BitVec.eq_of_toNat_eq (by
      rw [ht]; show _ = 0; omega_using [hg2, hge])
    have lt : (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat <
        P := by omega_using [e₁, hg2, hP, hge, ga, gd]
    rw [h0, select_keep, select_keep, select_keep, Nat.mod_eq_of_lt lt]

end VG.Proof.Poly1305.RISCV64

end

end

/-!
# Poly1305 on RISC-V: the state

The regions of the state (as on PPC64LE, `Proof/Poly1305/PPC64LE/Setup.lean`),
the key and the accumulator as numbers, and the code that reads and writes
them a byte at a time: `setup_ok` (the clamped `r` and the accumulator on
entry), `storeH_ok`, `addS_ok` and `storeTag_ok`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := Offset.contains_base base h hd

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p h (by omega_using [hd]) (by omega_using [he])) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The buffer and the rest. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) :=
  Offset.sub_base st h

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint_base st (by decide) (by decide)
  · exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp only [Nat.reducePow, Nat.reduceLeDiff])
    (List.mem_range.mp hi)

/-- A word of the key, unchanged by writes to the accumulator and the working space. -/
theorem key_word {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') {d : Nat}
    (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 56) : m'.readW (off st d) 64 = m.readW (off st d) 64 := by
  refine hf.readW (r := ⟨off st d, 8⟩) (a := off st d) (w := 64) (Region.contains_self _ _) ?_
    (by omega_using [])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base st (n := 8) (k := 24) (by omega_using [h₁]) (by omega_using [h₂])
  · exact Offset.disjoint st (n := 8) (e := 56) (k := 72) (by omega_using [h₂]) (by omega_using [h₂]) (by omega_using [])

/-! ## The accumulator and the key as numbers -/

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = word m st 0 + 2 ^ 64 * word m st 8 + 2 ^ 128 * word m st 16 := by
  rw [Poly1305.leNum_bytesAt_24, word, add_ofNat_zero]
  rfl

theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add,
    List.take_left' (Poly1305.length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add,
    List.drop_left' (Poly1305.length_bytesAt _ _ _),
    List.take_of_length_le (by rw [Poly1305.length_bytesAt])]
  congr 1
  simp only [off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = word m p 0 + 2 ^ 64 * word m p 8 := by
  rw [Poly1305.leNum_bytesAt_16, word, add_ofNat_zero]
  rfl

theorem off_24 (p : Addr) : off p 24 = p + 24 := rfl

/-- The clamping mask of `r1`. -/
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The clamped `r` of the key in the state. -/
abbrev Rk (m : Mem) (st : Addr) : Nat :=
  (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) = Rk m st := by
  rw [key_take, leNum_key, word, word, off, add_ofNat_zero, BitVec.add_assoc, ← BitVec.ofNat_add,
    Poly1305.clamp_words]
  rfl

/-! ## The state on entry -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev st : Addr := s₀.gpr .a0
/-- The clamped `r`. -/
abbrev Rn : Nat := Rk s₀.mem (st s₀)
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (st s₀) 24)
end

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

theorem repr_key {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    bytesAt s₀.mem (off (st s₀) 24) 32 = key := h.2.1

theorem repr_acc {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    accumulate (Rn s₀) msg = A0 s₀ := by
  rw [A0, h.2.2, ← repr_key h, clamp_key]

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-! ## Storing the accumulator -/

/-- The words of `h` stored. -/
def storeHm (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) : Mem :=
  ((m.writeW (off st 0) w0).writeW (off st 8) w1).writeW (off st 16) w2

theorem storeHm_frame {st : Addr} {r : Region} {m m' : Mem} (hf : Frame [hR st, r] m m')
    (w0 w1 w2 : BitVec 64) : Frame [hR st, r] m (storeHm m' st w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd =>
    contains_off hd (by omega_using [hd])
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

theorem storeHm_acc (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) :
    leNum (bytesAt (storeHm m st w0 w1 w2) st 24) = w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat := by
  rw [leNum_acc]
  simp only [word, storeHm]
  rw [show st + BitVec.ofNat 64 0 = off st 0 from rfl, show st + BitVec.ofNat 64 8 = off st 8 from rfl,
    show st + BitVec.ofNat 64 16 = off st 16 from rfl,
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    Mem.readW_writeW_self64]

theorem in_st {s : State} {p : Addr} (hw : sR p ∈ s.wr) {d n : Nat} (h : d + n ≤ 128) :
    InRegions s.wr (p + BitVec.ofNat 64 d) n :=
  ⟨_, hw, contains_off h (by omega_using [h])⟩

theorem in_st' {s : State} {p : Addr} (hw : sR p ∈ s.rd ++ s.wr) {d n : Nat} (h : d + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) n :=
  ⟨_, hw, contains_off h (by omega_using [h])⟩

/-- The state plus a multiple of 8 is 8-byte aligned. -/
theorem st_al8 {p : Addr} (ha : p.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) :
    (p + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega_using [ha, hd]

theorem storeH_ok (s : State) (hw : sR (s.gpr .a0) ∈ s.wr) (ha : (s.gpr .a0).toNat % 8 = 0) :
    WP isa (.block storeH) s fun s' =>
      s'.mem = storeHm s.mem (s.gpr .a0) (s.gpr H0) (s.gpr H1) (s.gpr H2) ∧
      (∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [storeH]
  refine VG.RISCV64.Steps.wp_sd (a := off (s.gpr .a0) 0) (by decide) rfl (st_al8 ha (by decide))
    (in_st hw (by decide)) fun s₁ g₁ => ?_
  refine VG.RISCV64.Steps.wp_sd (a := off (s.gpr .a0) 8) (by decide) (by rw [g₁.gpr])
    (st_al8 ha (by decide)) (by rw [g₁.wr]; exact in_st hw (by decide)) fun s₂ g₂ => ?_
  refine VG.RISCV64.Steps.wp_sd (a := off (s.gpr .a0) 16) (by decide) (by rw [g₂.gpr, g₁.gpr])
    (st_al8 ha (by decide)) (by rw [g₂.wr, g₁.wr]; exact in_st hw (by decide)) fun s₃ g₃ =>
    WP.block_nil ⟨?_, fun r _ _ => by rw [g₃.gpr, g₂.gpr, g₁.gpr], by rw [g₃.rd, g₂.rd, g₁.rd],
      by rw [g₃.wr, g₂.wr, g₁.wr], by rw [g₃.sp, g₂.sp, g₁.sp]⟩
  rw [g₃.mem, g₂.mem, g₁.mem, g₂.gpr, g₁.gpr]
  rfl

/-! ## Loading the state -/

/-- A doubleword of the state at `a0`, loaded into `d`. -/
theorem ldSt_ok (s : State) (d : Reg) {off : Nat} (ho : off + 8 ≤ 128) (hw : sR (s.gpr .a0) ∈ s.rd ++ s.wr)
    (ha : (s.gpr .a0).toNat % 8 = 0) (h8 : off % 8 = 0 := by decide) :
    WP isa (.block [.load .d d .a0 off]) s fun s' =>
      Words64.Upd3 s s' d T1 T2 (s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 off) 64) :=
  VG.RISCV64.Steps.wp_ld (by omega_using [ho]) rfl (st_al8 ha h8) (in_st' hw ho) fun s' u =>
    WP.block_nil ⟨u.gpr, fun r h _ _ => u.other r h, u.mem, u.rd, u.wr, u.sp⟩

theorem upd3_regs {s s' : State} {d t₁ t₂ : Reg} {v : BitVec 64} (h : Words64.Upd3 s s' d t₁ t₂ v) :
    Keeps [d, t₁, t₂] s s' :=
  ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact h.other r hr.1 hr.2.1 hr.2.2, h.mem, h.rd, h.wr, h.sp⟩

theorem M0_M1 : M0 &&& BitVec.ofInt 64 (-4) = M1 := by decide

theorem key0_lt (k : BitVec 64) : (k &&& M0).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_lt (k : BitVec 64) : (k &&& M1).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem key1_mod (k : BitVec 64) : (k &&& M1).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show (4 : Nat) = 2 ^ 2 from rfl,
    ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show M1.toNat &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

theorem s1_toNat (k : BitVec 64) :
    (((k &&& M1) >>> 2) + (k &&& M1)).toNat = 5 * ((k &&& M1).toNat / 4) := by
  have h1 := key1_lt k
  have h2 := key1_mod k
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega_using [h1, h2]

/-- The clamping and `s1`. -/
def clampI : List Instr :=
  [.logic .and R0 R0 T1, .logicImm .and T1 T1 (-4), .logic .and R1 R1 T1, .shift .srl .d S1 R1 2,
    .add S1 S1 R1]

theorem clampI_ok (s : State) :
    WP isa (.block clampI) s fun s' =>
      s'.gpr R0 = s.gpr R0 &&& s.gpr T1 ∧ s'.gpr R1 = s.gpr R1 &&& (s.gpr T1 &&& BitVec.ofInt 64 (-4)) ∧
      s'.gpr S1 = ((s.gpr R1 &&& (s.gpr T1 &&& BitVec.ofInt 64 (-4))) >>> 2) +
        (s.gpr R1 &&& (s.gpr T1 &&& BitVec.ofInt 64 (-4))) ∧
      Keeps [R0, T1, R1, S1] s s' := by
  apply WP.of_runBlock
  simp only [clampI, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_logicImm (show imm12 (-4) by decide), exec_shift_d (show 2 < 64 by decide), exec_add,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · exact (((((Keeps.refl _ s).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)).write _ (by decide)

theorem setup_eq : setup =
    ([.load .d R0 .a0 24] : List Instr) ++ (([.load .d R1 .a0 32] : List Instr) ++
    (Impl.Words64.RISCV64.movImm64 T1 T2 M0 ++ (clampI ++
    (([.load .d H0 .a0 0] : List Instr) ++ (([.load .d H1 .a0 8] : List Instr) ++
      ([.load .d H2 .a0 16] : List Instr)))))) := by
  simp only [setup, clampI, List.append_assoc, List.cons_append, List.nil_append]

/-- The registers `setup` writes. -/
abbrev setupRegs : List Reg := [R0, T1, T2, R1, S1, H0, H1, H2]

theorem setup_ok (s : State) (hw : sR (s.gpr .a0) ∈ s.rd ++ s.wr) (ha : (s.gpr .a0).toNat % 8 = 0) :
    WP isa (.block setup) s fun s' =>
      Keys (Rk s.mem (s.gpr .a0)) s' ∧ (A0 s < P → hv s' = A0 s ∧ Bounds s') ∧
      Keeps setupRegs s s' := by
  rw [setup_eq]
  refine WP.block_append (WP.mono (ldSt_ok s R0 (by decide) hw ha) fun s₁ u₁ => ?_)
  have k₁ := upd3_regs u₁
  have a₁ : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr'
  have hw₁ : sR (s₁.gpr .a0) ∈ s₁.rd ++ s₁.wr := by rw [a₁, k₁.2.2.1, k₁.2.2.2.1]; exact hw
  refine WP.block_append (WP.mono (ldSt_ok s₁ R1 (by decide) hw₁ (by rw [a₁]; exact ha)) fun s₂ u₂ => ?_)
  have k₂ := k₁.trans (upd3_regs u₂)
  refine WP.block_append (WP.mono (Words64.movImm64_ok (d := T1) (tmp := T2) (s := s₂) (by decide) M0)
    fun s₃ ⟨t₃, o₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  have k₃ : Keeps [T1, T2] s₂ s₃ := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact o₃ r hr.1 hr.2, m₃, rd₃, wr₃, sp₃⟩
  refine WP.block_append (WP.mono (clampI_ok s₃) fun s₄ ⟨c₀, c₁, c₂, k₄⟩ => ?_)
  have k₁₄ := (k₂.trans k₃).trans k₄
  have a₄ : s₄.gpr .a0 = s.gpr .a0 := k₁₄.gpr'
  have hw₄ : sR (s₄.gpr .a0) ∈ s₄.rd ++ s₄.wr := by rw [a₄, k₁₄.2.2.1, k₁₄.2.2.2.1]; exact hw
  refine WP.block_append (WP.mono (ldSt_ok s₄ H0 (by decide) hw₄ (by rw [a₄]; exact ha)) fun s₅ u₅ => ?_)
  have k₅ := upd3_regs u₅
  have hw₅ : sR (s₅.gpr .a0) ∈ s₅.rd ++ s₅.wr := by
    rw [k₅.gpr' (r := .a0), k₅.2.2.1, k₅.2.2.2.1]; exact hw₄
  refine WP.block_append (WP.mono (ldSt_ok s₅ H1 (by decide) hw₅
    (by rw [k₅.gpr' (r := .a0), a₄]; exact ha)) fun s₆ u₆ => ?_)
  have k₆ := upd3_regs u₆
  have hw₆ : sR (s₆.gpr .a0) ∈ s₆.rd ++ s₆.wr := by
    rw [k₆.gpr' (r := .a0), k₆.2.2.1, k₆.2.2.2.1]; exact hw₅
  refine WP.mono (ldSt_ok s₆ H2 (by decide) hw₆
    (by rw [k₆.gpr' (r := .a0), k₅.gpr' (r := .a0), a₄]; exact ha)) fun s₇ u₇ => ?_
  have k₇ := upd3_regs u₇
  have k₅₇ := (k₅.trans k₆).trans k₇
  have K := k₁₄.trans k₅₇
  -- The memory and the base are those on entry.
  have mm : ∀ {t : State}, t.mem = s.mem → t.gpr .a0 = s.gpr .a0 → ∀ d,
      t.mem.readW (t.gpr .a0 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 d) 64 :=
    fun hm ha _ => by rw [hm, ha]
  have r0 : s₇.gpr R0 = s.mem.readW (off (s.gpr .a0) 24) 64 &&& M0 := by
    rw [k₅₇.gpr' (r := R0), c₀, k₃.gpr' (r := R0), t₃, (upd3_regs u₂).gpr' (r := R0), u₁.gpr]
  have r1 : s₇.gpr R1 = s.mem.readW (off (s.gpr .a0) 32) 64 &&& M1 := by
    rw [k₅₇.gpr' (r := R1), c₁, k₃.gpr' (r := R1), t₃, u₂.gpr, M0_M1, mm k₁.2.1 a₁]
  have s1 : s₇.gpr S1 = ((s.mem.readW (off (s.gpr .a0) 32) 64 &&& M1) >>> 2) +
      (s.mem.readW (off (s.gpr .a0) 32) 64 &&& M1) := by
    rw [k₅₇.gpr' (r := S1), c₂, k₃.gpr' (r := R1), t₃, u₂.gpr, M0_M1, mm k₁.2.1 a₁]
  refine ⟨⟨(s₇.gpr R1).toNat / 4, ?_, ?_, ?_, ?_, ?_⟩, fun hA => ?_, K.mono⟩
  · rw [r0]; exact key0_lt _
  · have e := key1_mod (s.mem.readW (off (s.gpr .a0) 32) 64)
    rw [← r1] at e
    omega_using [e]
  · have e := key1_lt (s.mem.readW (off (s.gpr .a0) 32) 64)
    rw [← r1] at e
    omega_using [e]
  · rw [s1, s1_toNat, r1]
  · rw [r0, r1]
  · have m₄ : s₄.mem = s.mem := k₁₄.2.1
    have h0 : s₇.gpr H0 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 0) 64 := by
      rw [((upd3_regs u₆).trans k₇).gpr' (r := H0), u₅.gpr, mm m₄ a₄]
    have h1 : s₇.gpr H1 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 8) 64 := by
      rw [k₇.gpr' (r := H1), u₆.gpr, mm (k₅.2.1.trans m₄) (k₅.gpr'.trans a₄)]
    have h2 : s₇.gpr H2 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 16) 64 := by
      rw [u₇.gpr, mm ((k₅.trans (upd3_regs u₆)).2.1.trans m₄)
        ((k₅.trans (upd3_regs u₆)).gpr'.trans a₄)]
    have e : hv s₇ = A0 s := by
      simp only [hv, val3, h0, h1, h2, A0, st, leNum_acc, word]
    refine ⟨e, ?_⟩
    have a0 := (s₇.gpr H0).isLt
    have a1 := (s₇.gpr H1).isLt
    simp only [Bounds, hv, val3, P] at e hA ⊢
    omega_using [e, hA, a0, a1]

/-! ## The tag -/

theorem addS_eq : addS = ([.load .d X0 .a0 40] : List Instr) ++
    (([.load .d X1 .a0 48] : List Instr) ++ Impl.Words.RISCV64.add2 H0 H1 X0 X1) := by
  simp only [addS, List.cons_append, List.nil_append]

theorem addS_ok (s : State) (hw : sR (s.gpr .a0) ∈ s.rd ++ s.wr) (ha : (s.gpr .a0).toNat % 8 = 0) :
    WP isa (.block addS) s fun s' =>
      (s'.gpr H0).toNat + 2 ^ 64 * (s'.gpr H1).toNat =
        ((s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat +
          (word s.mem (s.gpr .a0) 40 + 2 ^ 64 * word s.mem (s.gpr .a0) 48)) % 2 ^ 128 ∧
      Keeps [X0, T1, T2, X1, T1, T2, H0, H1, X0] s s' := by
  rw [addS_eq]
  refine WP.block_append (WP.mono (ldSt_ok s X0 (by decide) hw ha) fun s₁ u₁ => ?_)
  have k₁ := upd3_regs u₁
  have hw₁ : sR (s₁.gpr .a0) ∈ s₁.rd ++ s₁.wr := by
    rw [k₁.gpr' (r := .a0), k₁.2.2.1, k₁.2.2.2.1]; exact hw
  refine WP.block_append (WP.mono (ldSt_ok s₁ X1 (by decide) hw₁
    (by rw [k₁.gpr' (r := .a0)]; exact ha)) fun s₂ u₂ => ?_)
  have k₂ := upd3_regs u₂
  refine WP.mono add2_ok fun s₃ ⟨e₃, k₃⟩ => ⟨?_, (k₁.trans k₂).trans k₃⟩
  rw [e₃, (k₁.trans k₂).gpr' (r := H0), (k₁.trans k₂).gpr' (r := H1),
    k₂.gpr' (r := X0), u₁.gpr, u₂.gpr, k₁.2.1, k₁.gpr' (r := .a0)]

/-- The tag. -/
abbrev outR (p : Addr) : Region := ⟨p, 16⟩

theorem storeTag_ok (s : State) (ho : outR (s.gpr .a2) ∈ s.wr) :
    WP isa (.block storeTag) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .a2) (s.gpr H0)).writeW
        (s.gpr .a2 + BitVec.ofNat 64 8) (s.gpr H1) := by
  rw [storeTag]
  refine WP.block_append (WP.mono (Words64.storeLE64_ok (v := H0) (n := .a2) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, ho, contains_off (by decide) (by decide)⟩) fun s₁ ⟨g₁, m₁, r₁, w₁, p₁⟩ => ?_)
  have a₁ : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide)
  have i₁ : InRegions s₁.wr (s₁.gpr .a2 + BitVec.ofNat 64 8) 8 := by
    rw [w₁, a₁]; exact ⟨_, ho, contains_off (by decide) (by decide)⟩
  refine WP.mono (Words64.storeLE64_ok (v := H1) (n := .a2) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) i₁)
    fun s₂ ⟨_, m₂, _, _, _⟩ => ?_
  rw [m₂, m₁, a₁, g₁ _ (by decide) (by decide), add_ofNat_zero]

/-- The tag stored: the low 128 bits of `x`. -/
theorem tag_bytes (m : Mem) (p : Addr) (h0 h1 : BitVec 64) (x : Nat)
    (hx : h0.toNat + 2 ^ 64 * h1.toNat = x % 2 ^ 128) :
    bytesAt ((m.writeW p h0).writeW (p + BitVec.ofNat 64 8) h1) p 16 =
      Spec.Poly1305.leBytes 16 x := by
  have q0 : ((m.writeW p h0).writeW (p + BitVec.ofNat 64 8) h1).readW p 64 = h0 := by
    rw [Mem.readW_writeW_sep (Offset.sep_base p (n := 8) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  have q1 : ((m.writeW p h0).writeW (p + BitVec.ofNat 64 8) h1).readW
      (p + BitVec.ofNat 64 8) 64 = h1 := Mem.readW_writeW_self64 _ _ _
  have a0 := h0.isLt; have a1 := h1.isLt
  refine Poly1305.bytesAt_leBytes_16 _ _ _ ?_ ?_
  · rw [q0]; omega_using [hx, a0, a1]
  · rw [q1]; omega_using [hx, a0, a1]

end VG.Proof.Poly1305.RISCV64

end

end

/-! ### `Poly1305.RISCV64.Blocks`, which this module and modules that import it used -/

section

/-!
# Poly1305 on RISC-V: `blocks`

As on AArch64 (`Proof/Poly1305/AArch64/Radix64/Blocks.lean`): the loop
invariant says that the accumulator in the registers is that of the message
on entry followed by the blocks absorbed so far, modulo `p`; the epilogue
reduces and stores it. The code writes only temporaries and argument
registers, and the memory only in the state's accumulator.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-- The registers the code writes: no preserved register, nor `ra`. -/
def written : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The absorbing of a block, with the key from `Keys`. -/
theorem absorb_key_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) {R : Nat}
    (hk : Keys R s)
    (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (absorb b off pad wide)) s fun s' =>
      (Bounds s → hv s' % P =
        ((hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  obtain ⟨q, hr0, hr1, hq, hs1, hr⟩ := hk
  simpa only [← hr, Bounds] using absorb_ok s b off pad wide hr0 hr1 hq hs1 ho h0 h8 hal hb

/-! ## The precondition -/

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value (m : Mem) (p : Addr) :
    word m p 0 + 2 ^ 64 * word m p (0 + 8) + 2 ^ 128 * true.toNat =
      leNum (bytesAt m p 16 ++ [0x01]) := by
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

end VG.Proof.Poly1305.RISCV64

end

end

/-!
# Poly1305 on RISC-V: the buffer

The buffer (bytes 56–71 of the state) as `update` and `finalize` fill it, and
absorbing it as a block, as on PPC64LE (`Proof/Poly1305/PPC64LE/Buffer.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

theorem off_56 (p : Addr) : off p 56 = p + 56 := rfl

/-- `x &&& 15`. -/
theorem and15 (x : BitVec 64) : x &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

/-- The buffer. -/
abbrev bfR (st : Addr) : Region := ⟨off st 56, 16⟩

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) :=
  Offset.sub st (by decide) (by decide)

/-- The two words of the buffer, as a number. -/
theorem leNum_buf (m : Mem) (st : Addr) :
    word m st 56 + 2 ^ 64 * word m st (56 + 8) = leNum (bytesAt m (off st 56) 16) := by
  rw [leNum_key, word, word, word, word, add_ofNat_zero, off, Offset.add_add]

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) (pad : Bool) {R : Nat} (hk : Keys R s)
    (hw : sR (s.gpr .a0) ∈ s.wr) :
    WP isa (.block (absorb .a0 56 pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (leNum (bytesAt s.mem (off (s.gpr .a0) 56) 16) +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  have hin : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 d) 8 :=
    fun d hd => in_st' (List.mem_append_right _ hw) hd
  refine WP.mono (absorb_key_ok s .a0 56 pad false hk (by decide) (hin 56 (by decide))
    (hin (56 + 8) (by decide)) (fun h => by cases h)) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, k⟩
  obtain ⟨hv', hb'⟩ := ha hb
  refine ⟨?_, hb'⟩
  rw [hv', leNum_buf]

/-- The `k + n` bytes at `base` after `n` bytes are written from `base + k` on. -/
theorem bytesAt_after {m m' : Mem} {base : Addr} {k n : Nat} (hkn : k + n ≤ 16)
    (hf : Frame [⟨base + BitVec.ofNat 64 k, n⟩] m m') (src : Nat → Byte)
    (hc : ∀ i < n, m' (base + BitVec.ofNat 64 k + BitVec.ofNat 64 i) = src i) :
    bytesAt m' base (k + n) = bytesAt m base k ++ (List.range n).map src := by
  rw [Poly1305.bytesAt_add]
  congr 1
  · refine Poly1305.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hkn])
    simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.base_disjoint base (by omega_using []) (by omega_using [hkn])
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)

/-- The proof contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

end VG.Proof.Poly1305.RISCV64

end

end

/-! ### `Poly1305.RISCV64.Update`, which the modules that import this one used -/

section

/-!
# Poly1305 on RISC-V: `update`

As on PPC64LE (`Proof/Poly1305/PPC64LE/Shared.lean`): a non-empty buffer is
filled from the data and, once full, absorbed; then the whole blocks of the
data are absorbed, and the rest is copied into the buffer. The invariants
say which data is consumed, what the accumulator in the registers has
absorbed, and what the buffer holds.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.RISCV64.Steps VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev dp : Addr := s₀.gpr .a2
abbrev dl : Nat := (s₀.gpr .a3).toNat
abbrev dR : Region := ⟨dp s₀, dl s₀⟩
/-- The number of bytes buffered. -/
abbrev kb : Nat := (s₀.gpr .a1).toNat % 16
/-- The bytes buffered. -/
abbrev Bf : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kb s₀)
/-- The first `c` bytes of data. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c
end

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_d : (sR (st s₀)).Disjoint (dR s₀)
  st_al : (st s₀).toNat % 8 = 0

theorem dl_lt (s₀ : State) : dl s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by decide)

theorem a3_eq (s₀ : State) : s₀.gpr .a3 = BitVec.ofNat 64 (dl s₀) := by simp

/-! ## Invariants -/

/-- What holds throughout. -/
structure UCommon (s₀ : State) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  keys : Keys (Rn s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [wR (st s₀)] s₀.mem s.mem

/-- The accumulator in `t0`–`t2` is that of the message on entry followed by
the whole blocks `X`. -/
def Acc (s₀ : State) (X : List Byte) (s : State) : Prop :=
  A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) X % P ∧ Bounds s

/-- Before any data is consumed. -/
structure Pre1 (s₀ : State) (s : State) : Prop extends UCommon s₀ s where
  a2 : s.gpr .a2 = dp s₀
  a3 : s.gpr .a3 = s₀.gpr .a3
  y1 : s.gpr Y1 = BitVec.ofNat 64 (kb s₀)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s

/-- The buffer and the first `c` bytes of data are absorbed, a whole number
of blocks, and the rest of the data is at `a2`. -/
structure Cons (s₀ : State) (c : Nat) (s : State) : Prop extends UCommon s₀ s where
  c_le : c ≤ dl s₀
  whole : (kb s₀ + c) % 16 = 0
  a2 : s.gpr .a2 = dp s₀ + BitVec.ofNat 64 c
  a3 : s.gpr .a3 = BitVec.ofNat 64 (dl s₀ - c)
  acc : Acc s₀ (Bf s₀ ++ Dt s₀ c) s

/-- The buffer and the data are the whole blocks `X`, absorbed, followed by
`Y`, in the buffer. -/
structure Done (s₀ : State) (s : State) : Prop extends UCommon s₀ s where
  done : ∃ X Y : List Byte, Acc s₀ X s ∧ X.length % 16 = 0 ∧ Y.length < 16 ∧
    Bf s₀ ++ Dt s₀ (dl s₀) = X ++ Y ∧ bytesAt s.mem (off (st s₀) 56) Y.length = Y

/-- The registers that hold what is kept throughout. -/
abbrev kept : List Reg := [.a0, H0, H1, H2, R0, R1, S1]

/-- A state that differs from `s` only in other registers. -/
def Temps (s s' : State) : Prop :=
  (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Temps.trans {s₁ s₂ s₃ : State} (h₁ : Temps s₁ s₂) (h₂ : Temps s₂ s₃) : Temps s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Temps.upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ kept := by decide) : Temps s s' :=
  ⟨fun r hr => u.other r fun e => hd (e ▸ hr), u.mem, u.rd, u.wr⟩

theorem Temps.keys {s₀ s s' : State} (h : Keys (Rn s₀) s) (ht : Temps s s') : Keys (Rn s₀) s' :=
  h.of_regs fun r hr => ht.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)

theorem Temps.ucommon {s₀ s s' : State} (h : UCommon s₀ s) (ht : Temps s s') : UCommon s₀ s' :=
  ⟨(ht.1 .a0 (by simp)).trans h.a0, Temps.keys h.keys ht, ht.2.2.1.trans h.rd,
    ht.2.2.2.trans h.wr, by rw [ht.2.1]; exact h.frame⟩

theorem Temps.acc {s₀ s s' : State} {X : List Byte} (h : Acc s₀ X s) (ht : Temps s s') :
    Acc s₀ X s' := by
  intro hA
  obtain ⟨h1, h2⟩ := h hA
  obtain e : hv s' = hv s := by
    simp only [hv, val3, ht.1 H0 (by simp), ht.1 H1 (by simp), ht.1 H2 (by simp)]
  refine ⟨by rw [e]; exact h1, ?_⟩
  simp only [Bounds, ht.1 H2 (by simp)]
  exact h2

theorem Temps.done {s₀ s s' : State} (h : Done s₀ s) (ht : Temps s s') : Done s₀ s' := by
  obtain ⟨X, Y, a, b, c, d, e⟩ := h.done
  exact { Temps.ucommon h.toUCommon ht with
    done := ⟨X, Y, Temps.acc a ht, b, c, d, by rw [ht.2.1]; exact e⟩ }

/-- Bytes of data read from memory the code has written only in the working space. -/
theorem UPre.data {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame [wR (st s₀)] s₀.mem m) {i : Nat}
    (hi : i < dl s₀) : m (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  hf.bytes (R := dR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.st_d.symm.sub_right (sub_sR _ (by decide)))
    (show dl s₀ ≤ 2 ^ 64 by have := dl_lt s₀; omega_using [this]) hi

theorem UCommon.in_st {s₀ : State} (hp : UPre s₀) {s : State} (h : UCommon s₀ s) :
    sR (s.gpr .a0) ∈ s.wr := by
  rw [h.wr, h.a0, hp.wr]; exact List.mem_singleton_self _

/-- Data bytes are readable. -/
theorem UPre.data_in {s₀ : State} (hp : UPre s₀) {s : State} (h : UCommon s₀ s) {c n : Nat}
    (hc : c + n ≤ dl s₀) : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c) n := by
  rw [h.rd, hp.rd]
  exact ⟨dR s₀, List.mem_append_left _ (List.mem_singleton_self _),
    contains_off hc (by have := dl_lt s₀; omega_using [hc, this])⟩

/-! ## Prologue -/

theorem uprologue_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (.logicImm .and Y1 .a1 15 :: setup)) s₀ (Pre1 s₀) := by
  refine wp_andi (by decide) fun s₁ u₁ => WP.mono (setup_ok s₁ (by
    rw [u₁.other _ (by decide), u₁.rd, u₁.wr, hp.wr]
    exact List.mem_append_right _ (List.mem_singleton_self _))
    (by rw [u₁.other _ (by decide)]; exact hp.st_al)) fun s₂ ⟨hk, ha, k⟩ => ?_
  have m₁ : s₁.mem = s₀.mem := u₁.mem
  obtain a0₁ : s₁.gpr .a0 = s₀.gpr .a0 := u₁.other _ (by decide)
  obtain hR : Rk s₁.mem (s₁.gpr .a0) = Rn s₀ := by rw [m₁, a0₁]
  obtain hA : A0 s₁ = A0 s₀ := by simp only [A0, st, m₁, a0₁]
  rw [hR] at hk
  rw [hA] at ha
  refine { a0 := by rw [k.gpr' (r := .a0), a0₁]
           keys := hk
           rd := by rw [k.2.2.1, u₁.rd]
           wr := by rw [k.2.2.2.1, u₁.wr]
           frame := by rw [k.2.1, m₁]; exact Frame.refl _ _
           a2 := by rw [k.gpr' (r := .a2), u₁.other _ (by decide)]
           a3 := by rw [k.gpr' (r := .a3), u₁.other _ (by decide)]
           y1 := by rw [k.gpr' (r := Y1), u₁.gpr, and15]
           buf := by rw [k.2.1, m₁]
           acc := fun h => ?_ }
  obtain ⟨e, b⟩ := ha h
  exact ⟨by rw [e, Poly1305.absorbAll_nil], b⟩

/-- Nothing buffered: nothing of the data is consumed yet. -/
theorem Pre1.cons {s₀ s : State} (h : Pre1 s₀ s) (hk : kb s₀ = 0) : Cons s₀ 0 s :=
  { h.toUCommon with
    c_le := Nat.zero_le _, whole := by rw [hk]
    a2 := by rw [h.a2, add_ofNat_zero]
    a3 := by rw [h.a3, a3_eq, Nat.sub_zero]
    acc := by
      obtain e : Bf s₀ ++ Dt s₀ 0 = [] := by simp only [Bf, Dt, hk]; rfl
      rw [e]; exact h.acc }

/-! ## Filling the buffer -/

/-- After the count: `n = min(16 - kb, dl)` bytes to copy. -/
structure Counted (s₀ : State) (n : Nat) (s : State) : Prop extends UCommon s₀ s where
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  t1 : s.gpr T1 = dp s₀
  a2 : s.gpr .a2 = dp s₀ + BitVec.ofNat 64 n
  a3 : s.gpr .a3 = BitVec.ofNat 64 (dl s₀ - n)
  y1 : s.gpr Y1 = BitVec.ofNat 64 (kb s₀ + n)
  x0 : s.gpr X0 = BitVec.ofNat 64 n
  x1 : s.gpr X1 = st s₀ + BitVec.ofNat 64 (56 + kb s₀)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s

theorem Pre1.temps {s₀ s s' : State} (h : Pre1 s₀ s) (ht : Temps s s')
    (h2 : s'.gpr .a2 = s.gpr .a2) (h3 : s'.gpr .a3 = s.gpr .a3) (hy : s'.gpr Y1 = s.gpr Y1) :
    Pre1 s₀ s' :=
  { Temps.ucommon h.toUCommon ht with
    a2 := h2.trans h.a2, a3 := h3.trans h.a3, y1 := hy.trans h.y1
    buf := by rw [ht.2.1]; exact h.buf
    acc := Temps.acc h.acc ht }

theorem eval_ltu (s : State) (a b : Reg) :
    isa.eval (.ltu a b) s = some (decide (s.gpr a < s.gpr b)) := rfl

theorem count_ok {s₀ : State} {s : State} (h : Pre1 s₀ s) :
    WP isa count s (Counted s₀ (min (16 - kb s₀) (dl s₀))) := by
  obtain hkl := kb_lt s₀
  obtain hdl := dl_lt s₀
  refine WP.seq (wp_li (imm := 16) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => WP.block_nil ?_)
  obtain ht₂ : Temps s s₂ := (Temps.upd u₁).trans (Temps.upd u₂)
  obtain hx0 : s₂.gpr X0 = BitVec.ofNat 64 (16 - kb s₀) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.y1, Poly1305.sub_ofNat (by omega_using [hkl])]
  obtain hP₂ : Pre1 s₀ s₂ := h.temps ht₂ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
  -- `t3 = n`.
  refine WP.seq (WP.mono (Q := fun s₃ : State => Pre1 s₀ s₃ ∧
      s₃.gpr X0 = BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀))) ?_ fun s₃ ⟨hP₃, hx0₃⟩ => ?_)
  · have hlt : s₂.gpr .a3 < s₂.gpr X0 ↔ dl s₀ < 16 - kb s₀ := by
      rw [hP₂.a3, a3_eq, hx0, BitVec.lt_def, toNat_ofNat_lt hdl, toNat_ofNat_lt (by omega_using [hkl])]
    refine WP.ite (decide (dl s₀ < 16 - kb s₀))
      (by rw [eval_ltu]; exact congrArg some (decide_eq_decide.mpr hlt)) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mv fun s₃ u₃ => WP.block_nil ⟨hP₂.temps (Temps.upd u₃) (u₃.other _ (by decide))
        (u₃.other _ (by decide)) (u₃.other _ (by decide)), ?_⟩
      rw [u₃.gpr, hP₂.a3, a3_eq, Nat.min_eq_right (by omega_using [hb])]
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      exact WP.block_nil ⟨hP₂, by rw [hx0, Nat.min_eq_left hb]⟩
  · refine wp_sub fun s₄ u₄ => wp_addi (imm := 56) (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ =>
      wp_add fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_add fun s₉ u₉ => WP.block_nil ?_
    obtain ht : Temps s₃ s₉ := (((((Temps.upd u₄).trans (Temps.upd u₅)).trans (Temps.upd u₆)).trans
      (Temps.upd u₇)).trans (Temps.upd u₈)).trans (Temps.upd u₉)
    obtain hn : min (16 - kb s₀) (dl s₀) ≤ dl s₀ := Nat.min_le_right _ _
    obtain hn' : kb s₀ + min (16 - kb s₀) (dl s₀) ≤ 16 := by
      have := Nat.min_le_left (16 - kb s₀) (dl s₀); omega_using [hkl, this]
    obtain g : ∀ r ∈ [Reg.a0, .a2, .a3, X0, Y1], s₄.gpr r = s₃.gpr r ∨ r = .a3 := by
      intro r hr; by_cases e : r = .a3
      · exact .inr e
      · exact .inl (u₄.other r e)
    refine { Temps.ucommon hP₃.toUCommon ht with
      n_le := hn, n_le' := hn'
      t1 := by
        rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), hP₃.a2]
      a2 := by
        rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), hP₃.a2, hx0₃]
      a3 := by
        rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hP₃.a3, a3_eq, hx0₃,
          Poly1305.sub_ofNat hn]
      y1 := by
        rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
          u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₄.other _ (by decide), hP₃.y1, hx0₃, ← BitVec.ofNat_add]
      x0 := by
        rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), hx0₃]
      x1 := by
        rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
          u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₄.other _ (by decide),
          hP₃.a0, hP₃.y1, Offset.add_add]
      buf := by rw [ht.2.1]; exact hP₃.buf
      acc := Temps.acc hP₃.acc ht }

/-- After copying `n` bytes of data into the buffer. -/
structure Filled (s₀ : State) (n : Nat) (s : State) : Prop extends UCommon s₀ s where
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  a2 : s.gpr .a2 = dp s₀ + BitVec.ofNat 64 n
  a3 : s.gpr .a3 = BitVec.ofNat 64 (dl s₀ - n)
  y1 : s.gpr Y1 = BitVec.ofNat 64 (kb s₀ + n)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀ + n) = Bf s₀ ++ Dt s₀ n
  acc : Acc s₀ [] s

/-- `Region.Disjoint` as `Mem.Sep`. -/
theorem sep_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) :
    Mem.Sep r₁.base r₁.len r₂.base r₂.len :=
  fun x hx hy => h x (by simp only [Region.Contains]; omega_using [hx]) (by simp only [Region.Contains]; omega_using [hy])

theorem copyFill_ok {s₀ : State} (hp : UPre s₀) {s : State} {n : Nat} (h : Counted s₀ n s) :
    WP isa (.ite (.zero X0) (.block []) (Impl.Words.RISCV64.copyLoop Y0 T1 X1 X0)) s
      (Filled s₀ n) := by
  obtain hdl := dl_lt s₀
  obtain hn := h.n_le; have hn' := h.n_le'
  refine WP.ite (decide (n = 0)) (by rw [eval_zero, h.x0, ofNat_beq_zero (by omega_using [hdl, hn])])
    (fun h0 => ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0
    subst h0
    exact WP.block_nil { h.toUCommon with
      n_le := hn, n_le' := hn', a2 := h.a2, a3 := h.a3, y1 := h.y1
      buf := by rw [Nat.add_zero, h.buf]; simp [Dt, bytesAt]
      acc := h.acc }
  · simp only [decide_eq_false_iff_not] at h0
    obtain hb : off (st s₀) 56 + BitVec.ofNat 64 (kb s₀) = s.gpr X1 := by
      rw [h.x1, off, Offset.add_add]
    obtain hsub : Region.Sub ⟨s.gpr X1, n⟩ (wR (st s₀)) := by
      rw [h.x1]; exact Offset.sub _ (by omega_using []) (by omega_using [hn'])
    obtain hsubS : Region.Sub ⟨s.gpr X1, n⟩ (sR (st s₀)) := by
      rw [h.x1]; exact Offset.sub_base _ (by omega_using [hn'])
    refine WP.mono (copyLoop_ok (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) s (N := n) (by omega_using [h0]) (by omega_using [hdl, hn]) h.x0
      (fun i hi => by
        rw [h.t1]
        have := hp.data_in h.toUCommon (c := i) (n := 1) (by omega_using [hi, hn])
        exact this)
      (fun i hi => ⟨_, by rw [h.wr, hp.wr]; exact List.mem_singleton_self _,
        hsubS _ (Offset.contains_base _ (d := i) (n := 1) (k := n) (by omega_using [hi])
          (by omega_using [hi, hn, hdl]))⟩)
      (by
        rw [h.t1]
        obtain hd := hp.st_d.sub_left hsubS
        obtain hd' := hd.sub_right (Region.sub_prefix (base := dp s₀) hn)
        exact sep_of_disjoint hd')) fun t ⟨hc, hf, hk⟩ => ?_
    obtain g : ∀ r ∈ kept ++ [.a2, .a3, Y1], t.gpr r = s.gpr r := fun r hr => hk.gpr (by
      revert r; decide)
    obtain hU : UCommon s₀ t :=
      { a0 := (g .a0 (by decide)).trans h.a0
        keys := h.keys.of_regs fun r hr => g r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)
        rd := hk.2.1.trans h.rd
        wr := hk.2.2.trans h.wr
        frame := h.frame.trans (hf.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_singleton_self _, hsub⟩) }
    refine { hU with
      n_le := hn, n_le' := hn'
      a2 := (g .a2 (by decide)).trans h.a2
      a3 := (g .a3 (by decide)).trans h.a3
      y1 := (g Y1 (by decide)).trans h.y1
      buf := ?_
      acc := fun hA => ?_ }
    · rw [bytesAt_after (base := off (st s₀) 56) hn' (by rw [hb]; exact hf)
        (fun i => s₀.mem (dp s₀ + BitVec.ofNat 64 i)) (fun i hi => by
          rw [hb, hc i hi, h.t1, hp.data h.frame (by omega_using [hi, hn])]), h.buf]
      rfl
    · obtain ⟨e, b⟩ := h.acc hA
      obtain e' : hv t = hv s := by
        simp only [hv, val3, g H0 (by decide), g H1 (by decide), g H2 (by decide)]
      refine ⟨by rw [e']; exact e, ?_⟩
      simp only [Bounds, g H2 (by decide)]
      exact b

/-- `min(16 - kb, dl)` bytes into the buffer, which is absorbed if that fills it. -/
theorem fill_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : Pre1 s₀ s) :
    WP isa fill s fun s' => (∃ c, Cons s₀ c s') ∨ (Done s₀ s' ∧ s'.gpr .a3 = 0) := by
  obtain hkl := kb_lt s₀
  obtain hdl := dl_lt s₀
  refine WP.seq (WP.mono (count_ok h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (copyFill_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (wp_subi (imm := 16) (by decide) fun s₄ u₄ => WP.block_nil ?_)
  obtain hn := h₂.n_le; have hn' := h₂.n_le'
  obtain ht : Temps s₂ s₄ := Temps.upd u₄
  obtain hU : UCommon s₀ s₄ := Temps.ucommon h₂.toUCommon ht
  obtain hx0 : (s₄.gpr X0 == 0) = decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16) := by
    rw [u₄.gpr, h₂.y1]
    exact Poly1305.sub_beq (by omega_using [hn']) (by decide)
  obtain hacc : Acc s₀ [] s₄ := Temps.acc h₂.acc ht
  obtain hbuf : bytesAt s₄.mem (off (st s₀) 56) (kb s₀ + min (16 - kb s₀) (dl s₀)) =
      Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)) := by rw [ht.2.1]; exact h₂.buf
  obtain hl : (Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀))).length = kb s₀ + min (16 - kb s₀) (dl s₀) := by
    simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]
  obtain ha2 : s₄.gpr .a2 = dp s₀ + BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀)) :=
    (u₄.other _ (by decide)).trans h₂.a2
  obtain ha3 : s₄.gpr .a3 = BitVec.ofNat 64 (dl s₀ - min (16 - kb s₀) (dl s₀)) :=
    (u₄.other _ (by decide)).trans h₂.a3
  refine WP.ite (decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16)) (by rw [eval_zero, hx0])
    (fun hf => ?_) (fun hf => ?_)
  · simp only [decide_eq_true_eq] at hf
    refine WP.mono (absorbBuf_ok s₄ true hU.keys (hU.in_st hp)) fun s' ⟨ha, k⟩ =>
      .inl ⟨min (16 - kb s₀) (dl s₀), ?_⟩
    refine { a0 := (k.gpr' (r := .a0)).trans hU.a0
             keys := Keeps.keys hU.keys k
             rd := k.2.2.1.trans hU.rd
             wr := k.2.2.2.1.trans hU.wr
             frame := by rw [k.2.1]; exact hU.frame
             c_le := hn, whole := by rw [hf]
             a2 := (k.gpr' (r := .a2)).trans ha2
             a3 := (k.gpr' (r := .a3)).trans ha3
             acc := fun hA => ?_ }
    obtain ⟨hv, hb⟩ := hacc hA
    obtain ⟨hv', hb'⟩ := ha hb
    refine ⟨?_, hb'⟩
    obtain e : leNum (Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)) ++ [0x01]) =
        leNum (Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀))) + 2 ^ 128 * true.toNat := by
      rw [Poly1305.leNum_append, hl, hf]; rfl
    rw [Poly1305.absorbAll_nil] at hv
    have hbuf16 := hbuf
    rw [hf] at hbuf16
    rw [hv', hU.a0, hbuf16, mod_step hv,
      Poly1305.absorbAll_block (by omega_using [hl, hf]) (by omega_using [hl, hf]), e]
  · simp only [decide_eq_false_iff_not] at hf
    obtain hnd : min (16 - kb s₀) (dl s₀) = dl s₀ := by omega_using [hkl, hn, hn', hl, hf]
    refine WP.block_nil (.inr ⟨{ hU with
      done := ⟨[], Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)), hacc, rfl,
        by omega_using [hn', hl, hf], ?_, ?_⟩ }, ?_⟩)
    · rw [hnd, List.nil_append]
    · rw [hl]; exact hbuf
    · rw [ha3, hnd, Nat.sub_self]; rfl

/-! ## Whole blocks of data -/

theorem srl4_toNat (x : BitVec 64) : (x >>> 4).toNat = x.toNat / 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The data's words, as numbers: its bytes from `dp + c`. -/
theorem data_value {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame [wR (st s₀)] s₀.mem m) {c : Nat}
    (hc : c + 16 ≤ dl s₀) :
    word m (dp s₀ + BitVec.ofNat 64 c) 0 + 2 ^ 64 * word m (dp s₀ + BitVec.ofNat 64 c) (0 + 8) +
        2 ^ 128 * true.toNat =
      leNum (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16 ++ [0x01]) := by
  obtain hdl := dl_lt s₀
  obtain hw : ∀ d : Nat, d + 8 ≤ 16 → m.readW (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 d) 64 =
      s₀.mem.readW (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 d) 64 := by
    intro d hd
    rw [Offset.add_add]
    refine hf.readW (r := dR s₀) (w := 64)
      (contains_off (n := 64 / 8) (by omega_using [hc, hd]) (by omega_using [hc, hdl, hd])) ?_
      (by omega_using [])
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_d.symm.sub_right (sub_sR _ (by decide))
  rw [← block_value]
  simp only [word]
  rw [hw 0 (by decide), hw (0 + 8) (by decide)]

/-- The block of data after `c` bytes. -/
abbrev wholeBody (wide : Bool) : List Instr :=
  absorb .a2 0 true wide ++
    ([.addi .a2 .a2 16, .addi .a3 .a3 (-16), .shift .srl .d X0 .a3 4] : List Instr)

/-- `x & 7 = 0`: `x` is a multiple of 8. -/
theorem and7_zero {x : BitVec 64} (h : x &&& BitVec.ofInt 64 7 = 0) : x.toNat % 8 = 0 := by
  obtain e := congrArg BitVec.toNat h
  rwa [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at e

/-- The data after `c + 16` bytes is aligned if it is after `c`. -/
theorem data_al16 {p : Addr} {c : Nat} (h : (p + BitVec.ofNat 64 c).toNat % 8 = 0) :
    (p + BitVec.ofNat 64 (c + 16)).toNat % 8 = 0 := by
  rw [← Offset.add_add]; exact st_al8 h (by decide)

/-- One whole block of data. -/
theorem whole_step {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : Cons s₀ c s)
    (hc : 16 ≤ dl s₀ - c) (wide : Bool)
    (hal : wide = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) :
    WP isa (.block (wholeBody wide)) s
      fun s' => Cons s₀ (c + 16) s' ∧ s'.gpr X0 = BitVec.ofNat 64 ((dl s₀ - (c + 16)) / 16) := by
  obtain hdl := dl_lt s₀
  obtain hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [h.a2, Offset.add_add]
    exact hp.data_in h.toUCommon (by omega_using [hc, hd])
  refine WP.block_append (WP.mono (absorb_key_ok s .a2 0 true wide h.keys (by decide) (hin 0 (by decide))
    (hin (0 + 8) (by decide)) (fun hw => by rw [h.a2, BitVec.add_zero]; exact hal hw))
    fun s₁ ⟨ha, k₁⟩ => ?_)
  refine wp_addi (imm := 16) (by decide) fun s₂ u₂ => wp_subi (imm := 16) (by decide) fun s₃ u₃ =>
    wp_srl (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain ht : Temps s₁ s₄ := ((Temps.upd u₂).trans (Temps.upd u₃)).trans (Temps.upd u₄)
  obtain hU₁ : UCommon s₀ s₁ :=
    { a0 := (k₁.gpr' (r := .a0)).trans h.a0
      keys := Keeps.keys h.keys k₁
      rd := k₁.2.2.1.trans h.rd
      wr := k₁.2.2.2.1.trans h.wr
      frame := by rw [k₁.2.1]; exact h.frame }
  obtain ha3 : s₄.gpr .a3 = BitVec.ofNat 64 (dl s₀ - (c + 16)) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), k₁.gpr' (r := .a3), h.a3,
      Poly1305.sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  refine ⟨{ Temps.ucommon hU₁ ht with
    c_le := by omega_using [hc]
    whole := by have := h.whole; omega_using [this]
    a2 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, k₁.gpr' (r := .a2), h.a2,
      Offset.add_add]
    a3 := ha3
    acc := fun hA => ?_ }, ?_⟩
  · obtain ⟨hv₀, hb⟩ := h.acc hA
    obtain ⟨hv', hb'⟩ := ha hb
    obtain b : Bounds s₄ := by simp only [Bounds, ht.1 H2 (by simp)]; exact hb'
    obtain e : hv s₄ = hv s₁ := by
      simp only [hv, val3, ht.1 H0 (by simp), ht.1 H1 (by simp), ht.1 H2 (by simp)]
    refine ⟨?_, b⟩
    obtain h16 : (Bf s₀ ++ Dt s₀ c).length % 16 = 0 := by
      simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]; exact h.whole
    obtain hb1 : 0 < (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16).length := by
      rw [Poly1305.length_bytesAt]; omega_using []
    obtain hb2 : (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16).length ≤ 16 := by
      rw [Poly1305.length_bytesAt]
    rw [e, hv', h.a2, data_value hp h.frame (by omega_using [hc]), mod_step hv₀,
      show Dt s₀ (c + 16) = Dt s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16 from
        Poly1305.bytesAt_add _ _ _ _, ← List.append_assoc, Poly1305.absorbAll_append h16,
      Poly1305.absorbAll_block hb1 hb2]
  · apply BitVec.eq_of_toNat_eq
    rw [u₄.gpr, srl4_toNat, ← u₄.other .a3 (by decide), ha3, toNat_ofNat_lt (by omega_using [hdl]),
      toNat_ofNat_lt (by omega_using [hdl])]

/-- The loop over the whole blocks of data. -/
theorem whole_loop {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : Cons s₀ c s)
    (hc : 16 ≤ dl s₀ - c) (wide : Bool)
    (hal : wide = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) :
    WP isa (wholeLoop wide) s fun s' =>
      ∃ c', Cons s₀ c' s' ∧ dl s₀ - c' < 16 := by
  obtain hdl := dl_lt s₀
  refine WP.loop (M := isa) (fun k s => ∃ c, k = dl s₀ - c ∧ Cons s₀ c s ∧ 16 ≤ dl s₀ - c ∧
    (wide = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0)) ?_ _ s ⟨c, rfl, h, hc, hal⟩
  rintro k s ⟨c, rfl, h, hc, hal⟩
  refine WP.mono (whole_step hp h hc wide hal) fun s' ⟨h', hx⟩ => ?_
  obtain hev := eval_nonzero_ofNat s' X0 (k := (dl s₀ - (c + 16)) / 16) (by omega_using [hdl]) hx
  by_cases hl : dl s₀ - (c + 16) < 16
  · exact .inl ⟨by rw [hev, decide_eq_false (show ¬ (dl s₀ - (c + 16)) / 16 ≠ 0 by omega_using [hl])],
      c + 16, h', hl⟩
  · exact .inr ⟨by rw [hev, decide_eq_true (show (dl s₀ - (c + 16)) / 16 ≠ 0 by omega_using [hl])],
      _, by omega_using [hl], c + 16, rfl, h', by omega_using [hl], fun hw => data_al16 (hal hw)⟩

theorem whole_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (h : (∃ c, Cons s₀ c s) ∨ (Done s₀ s ∧ s.gpr .a3 = 0)) :
    WP isa whole s fun s' => (∃ c, Cons s₀ c s' ∧ dl s₀ - c < 16) ∨ (Done s₀ s' ∧ s'.gpr .a3 = 0) := by
  obtain hdl := dl_lt s₀
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain ht : Temps s s₁ := Temps.upd u₁
  obtain ha3 : s₁.gpr .a3 = s.gpr .a3 := u₁.other _ (by decide)
  rcases h with ⟨c, hc⟩ | ⟨hd, hz⟩
  · have hb : Cons s₀ c s₁ := { Temps.ucommon hc.toUCommon ht with
      c_le := hc.c_le, whole := hc.whole
      a2 := (u₁.other _ (by decide)).trans hc.a2
      a3 := ha3.trans hc.a3, acc := Temps.acc hc.acc ht }
    obtain hq : s₁.gpr X0 = BitVec.ofNat 64 ((dl s₀ - c) / 16) := by
      apply BitVec.eq_of_toNat_eq
      rw [u₁.gpr, srl4_toNat, hc.a3, toNat_ofNat_lt (by omega_using [hdl]),
        toNat_ofNat_lt (by omega_using [hdl])]
    refine WP.ite (decide (dl s₀ - c < 16)) (by
      rw [eval_zero_ofNat _ _ (by omega_using [hdl]) hq]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [])))
      (fun hl => ?_) (fun hl => ?_)
    · simp only [decide_eq_true_eq] at hl
      exact WP.block_nil (.inl ⟨c, hb, hl⟩)
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hl
      refine WP.seq (wp_andi (by decide) fun s₂ u₂ => WP.block_nil ?_)
      obtain hb₂ : Cons s₀ c s₂ := { Temps.ucommon hb.toUCommon (Temps.upd u₂) with
        c_le := hb.c_le, whole := hb.whole
        a2 := (u₂.other _ (by decide)).trans hb.a2
        a3 := (u₂.other _ (by decide)).trans hb.a3, acc := Temps.acc hb.acc (Temps.upd u₂) }
      refine WP.ite (s₂.gpr T1 == 0) rfl (fun hz => ?_) fun _ =>
        WP.mono (whole_loop hp hb₂ hl false fun h => by cases h) fun s' h' => .inl h'
      obtain hz' := and7_zero (by rw [← u₂.gpr]; exact beq_iff_eq.mp hz)
      rw [u₁.other _ (by decide), hc.a2] at hz'
      exact WP.mono (whole_loop hp hb₂ hl true fun _ => hz') fun s' h' => .inl h'
  · have hq : s₁.gpr X0 = 0 := by rw [u₁.gpr, hz]; rfl
    refine WP.ite true (by rw [eval_zero, hq]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.block_nil (.inr ⟨Temps.done hd ht, ha3.trans hz⟩)

/-! ## The rest of the data -/

theorem rest_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (h : (∃ c, Cons s₀ c s ∧ dl s₀ - c < 16) ∨ (Done s₀ s ∧ s.gpr .a3 = 0)) :
    WP isa rest s (Done s₀) := by
  obtain hdl := dl_lt s₀
  rcases h with ⟨c, hc, hlt⟩ | ⟨hd, hz⟩
  · refine WP.ite (decide (dl s₀ - c = 0))
      (by rw [eval_zero, hc.a3, ofNat_beq_zero (by omega_using [hlt])]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      obtain hcd : c = dl s₀ := by have := hc.c_le; omega_using [hb, this]
      refine WP.block_nil { hc.toUCommon with
        done := ⟨Bf s₀ ++ Dt s₀ c, [], hc.acc, ?_, by simp, by rw [hcd, List.append_nil], rfl⟩ }
      simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]; exact hc.whole
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.seq (wp_addi (imm := 56) (by decide) fun s₂ u₂ => WP.block_nil ?_)
      obtain ht : Temps s s₂ := Temps.upd u₂
      obtain hU₂ : UCommon s₀ s₂ := Temps.ucommon hc.toUCommon ht
      obtain a2₂ : s₂.gpr .a2 = dp s₀ + BitVec.ofNat 64 c := (u₂.other _ (by decide)).trans hc.a2
      obtain x1₂ : s₂.gpr X1 = off (st s₀) 56 := by rw [u₂.gpr, hc.a0]
      have hn := hc.c_le
      obtain hsubS : Region.Sub ⟨s₂.gpr X1, dl s₀ - c⟩ (sR (st s₀)) := by
        rw [x1₂]; exact Offset.sub_base _ (by omega_using [hlt])
      refine WP.mono (copyLoop_ok (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) s₂ (N := dl s₀ - c) (by omega_using [hb]) (by omega_using [hdl])
        ((u₂.other _ (by decide)).trans hc.a3)
        (fun i hi => by
          rw [a2₂, Offset.add_add]
          exact hp.data_in hU₂ (n := 1) (by omega_using [hi, hn]))
        (fun i hi => ⟨_, by rw [hU₂.wr, hp.wr]; exact List.mem_singleton_self _,
          hsubS _ (Offset.contains_base _ (d := i) (n := 1) (k := dl s₀ - c) (by omega_using [hi])
            (by omega_using [hi, hdl]))⟩)
        (by
          rw [a2₂]
          obtain hd := hp.st_d.sub_left hsubS
          obtain hd' := hd.sub_right (Offset.sub_base (dp s₀) (d := c) (n := dl s₀ - c) (k := dl s₀)
            (by omega_using [hn]))
          exact sep_of_disjoint hd')) fun t ⟨hcp, hf, hk⟩ => ?_
      obtain g : ∀ r ∈ kept, t.gpr r = s₂.gpr r := fun r hr => hk.gpr (by revert r; decide)
      obtain hU : UCommon s₀ t :=
        { a0 := (g .a0 (by decide)).trans hU₂.a0
          keys := hU₂.keys.of_regs fun r hr => g r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide)
          rd := hk.2.1.trans hU₂.rd
          wr := hk.2.2.trans hU₂.wr
          frame := hU₂.frame.trans (hf.sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact ⟨_, List.mem_singleton_self _, by
              rw [x1₂]; exact Offset.sub _ (by omega_using []) (by omega_using [hlt])⟩) }
      obtain hacc : Acc s₀ (Bf s₀ ++ Dt s₀ c) t := by
        intro hA
        obtain ⟨e, b⟩ := Temps.acc hc.acc ht hA
        obtain e' : hv t = hv s₂ := by
          simp only [hv, val3, g H0 (by decide), g H1 (by decide), g H2 (by decide)]
        refine ⟨by rw [e']; exact e, ?_⟩
        simp only [Bounds, g H2 (by decide)]
        exact b
      obtain hY : (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (dl s₀ - c)).length = dl s₀ - c :=
        Poly1305.length_bytesAt _ _ _
      refine { hU with
        done := ⟨Bf s₀ ++ Dt s₀ c, bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (dl s₀ - c),
          hacc, ?_, by omega_using [hlt, hY], ?_, ?_⟩ }
      · simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]; exact hc.whole
      · rw [List.append_assoc, show Dt s₀ (dl s₀) = Dt s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c)
          (dl s₀ - c) by rw [Dt, Dt, ← Poly1305.bytesAt_add]; congr 1; omega_using [hlt, hb, hY]]
      · rw [hY]
        obtain e := bytesAt_after (m := s₂.mem) (base := off (st s₀) 56) (k := 0) (n := dl s₀ - c)
          (by omega_using [hlt]) (by rw [add_ofNat_zero, ← x1₂]; exact hf)
          (fun i => s₀.mem (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i)) (fun i hi => by
            rw [add_ofNat_zero, ← x1₂, hcp i hi, a2₂, Offset.add_add,
              hp.data hU₂.frame (by omega_using [hi, hn])])
        rw [Nat.zero_add] at e
        rw [e]
        rfl
  · refine WP.ite true (by rw [eval_zero, hz]; rfl) (fun _ => WP.block_nil hd)
      (fun h => absurd h (by decide))

/-! ## Epilogue -/

theorem storeHm_buf (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) {n : Nat} (hn : n ≤ 16) :
    bytesAt (storeHm m st w0 w1 w2) (off st 56) n = bytesAt m (off st 56) n := by
  obtain hf : Frame [hR st] m (storeHm m st w0 w1 w2) := by
    obtain c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd =>
      contains_off hd (by omega_using [hd])
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
      (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))
  refine Poly1305.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hn])
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base st (by decide) (by omega_using [hn])

theorem uepilogue_ok {s₀ : State} (hp : UPre s₀) {s : State} (hd : Done s₀ s) :
    WP isa (.block (reduce ++ storeH)) s fun s' => Proof.Poly1305.updateRISCV64.post s₀ s' := by
  refine WP.block_append (WP.mono (reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  obtain x0₁ : s₁.gpr .a0 = st s₀ := by rw [k₁.gpr', hd.a0]
  refine WP.mono (storeH_ok s₁ (by rw [k₁.2.2.2.1, hd.wr, x0₁, hp.wr]; exact List.mem_singleton_self _)
    (by rw [x0₁]; exact hp.st_al))
    fun s₂ ⟨m₂, _, _, _, _⟩ => ?_
  have mem₁ : s₁.mem = s.mem := k₁.2.1
  rw [x0₁, mem₁] at m₂
  obtain hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [m₂]; exact storeHm_frame (hd.frame.mono (by simp)) _ _ _
  intro key msg hbuf hcnt
  obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
  have hk : kb s₀ = (W ++ B).length % 16 := hcnt
  obtain hBf : Bf s₀ = B := by rw [Bf, hk, off_56]; exact hBb
  obtain ⟨X, Y, hacc, hX, hY, hXY, hbufY⟩ := hd.done
  obtain hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hacc hA
  obtain hN := hr hb
  have hlen := hrep.1
  change Buffered s₂.mem (st s₀) key (W ++ B ++ Dt s₀ (dl s₀))
  rw [List.append_assoc, ← hBf, hXY, ← List.append_assoc]
  refine Buffered.of ⟨?_, ?_, ?_⟩ hY ?_
  · rw [List.length_append]; omega_using [hX, hlen]
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₂, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    change hv s₁ = _
    rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
  · rw [← off_56, m₂, storeHm_buf _ _ _ _ _ (by omega_using [hY]), hbufY]

/-! ## The whole function -/

theorem update_correct {s₀ : State} (hp : UPre s₀) :
    WP isa update s₀ (Proof.Poly1305.updateRISCV64.post s₀) := by
  refine WP.seq (WP.mono (uprologue_ok hp) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (Q := fun s : State => (∃ c, Cons s₀ c s) ∨ (Done s₀ s ∧ s.gpr .a3 = 0)) ?_
    fun s₄ h₄ => ?_)
  · refine WP.ite (decide (kb s₀ = 0))
      (by rw [eval_zero, h₃.y1, ofNat_beq_zero (by have := kb_lt s₀; omega_using [this])])
      (fun h => ?_) (fun _ => fill_ok hp h₃)
    simp only [decide_eq_true_eq] at h
    exact WP.block_nil (.inl ⟨0, h₃.cons h⟩)
  refine WP.seq (WP.mono (whole_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (rest_ok hp h₅) fun s₆ h₆ => ?_)
  exact uepilogue_ok hp h₆

theorem update_ok (s : State) (hs : Proof.Poly1305.updateRISCV64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.updateRISCV64.post s s' := by
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (update_correct ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

theorem update_ct : ConstantTime isa Proof.Poly1305.updateRISCV64.pre
    Proof.Poly1305.updateRISCV64.pub update := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

/-- A state satisfying the precondition (with no data). -/
def updateSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem update_verified : Verified RISCV64.target update Proof.Poly1305.updateRISCV64 :=
  ⟨update_ok, update_ct, ⟨updateSat, rfl, rfl, Region.disjoint_of_sep (by decide), by decide⟩⟩

end VG.Proof.Poly1305.RISCV64

end

end

/-! ### `Poly1305.RISCV64.Finalize`, which the modules that import this one used -/

section

/-!
# Poly1305 on RISC-V: `finalize`

As on PPC64LE (`Proof/Poly1305/PPC64LE/Finalize.lean`): a non-empty buffer
is padded in place with `0x01` and zeros and absorbed without `pad`; then the
accumulator is reduced, `s` is added modulo `2¹²⁸`, and the sum stored is the
tag. The proof is for any writable regions holding the state and the tag,
so it serves both `vg_poly1305_finalize` and `vg_poly1305_finalize_scratch`,
whose `scratch` the code does not use.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.RISCV64.Steps VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-! ## The buffer, a byte at a time -/

/-- Byte `k` of the buffer. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (56 + k)

theorem bufB_eq (st : Addr) (k : Nat) : bufB st k = off st 56 + BitVec.ofNat 64 k := by
  rw [off, Offset.add_add]

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bufB st j ≠ bufB st k :=
  Offset.add_ofNat_ne st (by omega_using [hj]) (by omega_using [hk]) (by omega_using [h])

theorem bufB_in {s : State} {st : Addr} (hw : sR st ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB st k) 1 :=
  in_st hw (by omega_using [hk])

theorem bfR_bufB (st : Addr) {k : Nat} (hk : k < 16) : (bfR st).Contains (bufB st k) 1 := by
  rw [bufB_eq]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])

/-- The buffer's bytes are `f k`. -/
def BufHas (m : Mem) (st : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (bufB st k) = f k

theorem bytesAt_buf {m : Mem} {st : Addr} {f : Nat → Byte} (h : BufHas m st f) :
    bytesAt m (off st 56) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro k hk
  rw [← h k (List.mem_range.mp hk), bufB_eq]

/-! ## The precondition -/

section
variable (s₀ : State)
/-- The number of bytes buffered. -/
abbrev kf : Nat := (s₀.gpr .a1).toNat % 16
abbrev op : Addr := s₀.gpr .a2
abbrev oR' : Region := ⟨op s₀, 16⟩
/-- The bytes buffered. -/
abbrev tail : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kf s₀)
end

structure FPre (s₀ : State) : Prop where
  st_in : sR (st s₀) ∈ s₀.wr
  o_in : oR' s₀ ∈ s₀.wr
  st_o : (sR (st s₀)).Disjoint (oR' s₀)
  st_al : (st s₀).toNat % 8 = 0

theorem kf_lt (s₀ : State) : kf s₀ < 16 := Nat.mod_lt _ (by decide)

/-! ## Prologue -/

/-- The state after the prologue. -/
structure F0 (s₀ : State) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  y1 : s.gpr Y1 = BitVec.ofNat 64 (kf s₀)
  a2 : s.gpr .a2 = op s₀
  keys : Keys (Rn s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  acc : A0 s₀ < P → hv s = A0 s₀ ∧ Bounds s

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (.logicImm .and Y1 .a1 15 :: setup)) s₀ (F0 s₀) := by
  refine wp_andi (by decide) fun s₁ u₁ => WP.mono (setup_ok s₁ (by
    rw [u₁.other _ (by decide), u₁.rd, u₁.wr]
    exact List.mem_append_right _ hp.st_in) (by rw [u₁.other _ (by decide)]; exact hp.st_al))
    fun s₂ ⟨hk, ha, k⟩ => ?_
  have m₁ : s₁.mem = s₀.mem := u₁.mem
  have a0₁ : s₁.gpr .a0 = s₀.gpr .a0 := u₁.other _ (by decide)
  have hR : Rk s₁.mem (s₁.gpr .a0) = Rn s₀ := by rw [m₁, a0₁]
  have hA : A0 s₁ = A0 s₀ := by simp only [A0, st, m₁, a0₁]
  rw [hR] at hk
  rw [hA] at ha
  exact ⟨by rw [k.gpr' (r := .a0), a0₁], by rw [k.gpr' (r := Y1), u₁.gpr, and15],
    by rw [k.gpr' (r := .a2), u₁.other _ (by decide)], hk, by rw [k.2.2.1, u₁.rd],
    by rw [k.2.2.2.1, u₁.wr], by rw [k.2.1, m₁], ha⟩

/-! ## Padding the buffer in place -/

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < kf s₀ then (tail s₀).getD k 0 else if k = kf s₀ then 1 else 0

theorem tail_byte (s₀ : State) {k : Nat} (hk : k < kf s₀) :
    s₀.mem (bufB (st s₀) k) = (tail s₀).getD k 0 := by
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]
  rw [← bufB_eq]

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the
prologue. -/
structure ZInv (s₀ : State) (s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : kf s₀ ≤ j ∧ j ≤ 16
  x1 : s.gpr X1 = bufB (st s₀) j
  x0 : s.gpr X0 = BitVec.ofNat 64 (16 - j)
  y0 : s.gpr Y0 = 0
  keep : ∀ r, r ≠ X1 → r ≠ X0 → r ≠ Y0 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] s₀.mem s.mem
  buf : BufHas s.mem (st s₀) fun k =>
    if k < kf s₀ then (tail s₀).getD k 0 else if k < j then 0 else s₀.mem (bufB (st s₀) k)

theorem zinit_ok {s₀ : State} {s₁ : State} (h₁ : F0 s₀ s₁) :
    WP isa (.block [.li Y0 0, .addi X1 .a0 56, .add X1 X1 Y1, .li X0 16, .sub X0 X0 Y1]) s₁
      (ZInv s₀ s₁ (kf s₀)) := by
  have hk := kf_lt s₀
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => wp_addi (imm := 56) (by decide) fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_li (imm := 16) (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ =>
    WP.block_nil ?_
  have hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨Nat.le_refl _, Nat.le_of_lt hk⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_,
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr],
    by rw [hm, h₁.mem]; exact Frame.refl _ _, fun k hk' => ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₂.other _ (by decide), h₁.a0, h₁.y1, Offset.add_add]
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), h₁.y1, Poly1305.sub_ofNat (by omega_using [hk])]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]; rfl
  · rw [u₆.other r h2, u₅.other r h2, u₄.other r h1, u₃.other r h1, u₂.other r h3]
  · rw [hm, h₁.mem]
    by_cases hkf : k < kf s₀
    · simp only [hkf, ite_true]; exact tail_byte s₀ hkf
    · simp only [hkf, ite_false]

theorem zero_step {s₀ : State} (hp : FPre s₀) {s₁ : State} {j : Nat}
    (hj : j < 16) {s : State} (h : ZInv s₀ s₁ j s) :
    WP isa (.block zeroBody) s fun s' => ZInv s₀ s₁ (j + 1) s' := by
  refine wp_sb (t := Y0) (a := bufB (st s₀) j) (by decide) (by rw [h.x1, add_ofNat_zero])
    (by rw [h.wr]; exact bufB_in hp.st_in hj) fun s₂ m₂ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_subi (imm := 1) (by decide) fun s₄ u₄ =>
    WP.block_nil ?_
  refine ⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, ?_, ?_, ?_,
    fun r h1 h2 h3 => ?_, by rw [u₄.rd, u₃.rd, m₂.rd, h.rd], by rw [u₄.wr, u₃.wr, m₂.wr, h.wr], ?_,
    fun k hk => ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.x1, bufB, Offset.add_add, Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.x0, Poly1305.sub_ofNat (by omega_using [hj]),
      Nat.sub_sub]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.y0]
  · rw [u₄.other r h2, u₃.other r h1, m₂.gpr, h.keep r h1 h2 h3]
  · rw [u₄.mem, u₃.mem, m₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bfR_bufB _ hj)
  · rw [u₄.mem, u₃.mem, m₂.mem, WriteBytes.writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, h.y0, show ¬ k < kf s₀ by have := h.j_le.1; omega_using [this],
        show k < k + 1 by omega_using [], ite_false]
      rfl
    · simp only [bufB_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega_using [h2]]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega_using [hkj, h2]]

theorem zeroLoop_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} {s : State}
    (h : ZInv s₀ s₁ (kf s₀) s) :
    WP isa (.loop (.block zeroBody) (.nonzero X0)) s (ZInv s₀ s₁ 16) := by
  have hk := kf_lt s₀
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ ZInv s₀ s₁ j s) ?_ _ s
    ⟨kf s₀, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (zero_step hp hj hz) fun s' h' => ?_
  have hev := eval_nonzero_ofNat s' X0 (k := 16 - (j + 1)) (by omega_using [hj]) h'.x0
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [hev, decide_eq_false (show ¬ 16 - (j + 1) ≠ 0 by omega_using [hl])],
      hl ▸ h'⟩
  · exact .inr ⟨by rw [hev, decide_eq_true (show 16 - (j + 1) ≠ 0 by omega_using [hj, hl])],
      _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

/-- After the `0x01` byte. -/
structure PInv (s₀ : State) (s₁ : State) (s : State) : Prop where
  keep : ∀ r, r ≠ X1 → r ≠ X0 → r ≠ Y0 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] s₀.mem s.mem
  buf : BufHas s.mem (st s₀) (padded s₀)

theorem one_byte : ((BitVec.ofNat 64 1).setWidth 8 : Byte) = 1 := by decide

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : F0 s₀ s₁) {s : State}
    (h : ZInv s₀ s₁ 16 s) :
    WP isa (.block [.li Y0 1, .addi X1 .a0 56, .add X1 X1 Y1, .store .b Y0 X1 0]) s (PInv s₀ s₁) := by
  have hk := kf_lt s₀
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => wp_addi (imm := 56) (by decide) fun s₃ u₃ =>
    wp_add fun s₄ u₄ => ?_
  have hx1 : s₄.gpr X1 = bufB (st s₀) (kf s₀) := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide),
      h.keep _ (by decide) (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide),
      h₁.a0, h₁.y1, Offset.add_add]
  refine wp_sb (t := Y0) (a := bufB (st s₀) (kf s₀)) (by decide) (by rw [hx1, add_ofNat_zero])
    (by rw [u₄.wr, u₃.wr, u₂.wr, h.wr]; exact bufB_in hp.st_in hk) fun s₅ m₅ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => ?_, by rw [m₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [m₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr], ?_, fun k hk' => ?_⟩
  · rw [m₅.gpr, u₄.other r h1, u₃.other r h1, u₂.other r h3, h.keep r h1 h2 h3]
  · rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bfR_bufB _ hk)
  · rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem, WriteBytes.writeW8_apply, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, one_byte]
    by_cases hkj : k = kf s₀
    · subst hkj
      simp only [ite_true, padded, Nat.lt_irrefl, ite_false]
    · simp only [bufB_ne hk' hk hkj, ite_false]
      rw [h.buf k hk']
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true, padded]
      · simp only [h1, ite_false, hk', ite_true, padded, hkj]

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : BufHas m (st s₀) (padded s₀)) :
    leNum (bytesAt m (off (st s₀) 56) 16) + 2 ^ 128 * false.toNat = leNum (tail s₀ ++ [0x01]) := by
  have hk := kf_lt s₀
  have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
  have hl : (List.range 16).map (padded s₀) = (tail s₀ ++ [0x01]) ++ List.replicate (15 - kf s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen]; omega_using [hk, hlen]
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (kf s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']),
          List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show k < (tail s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [padded, show ¬ k < kf s₀ by omega_using [hlen, hk'],
          show k ≠ kf s₀ by omega_using [hlen, hk']]
  rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, bytesAt_buf h, hl,
    Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero,
    Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.a0, .a2], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] s₀.mem s.mem
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P ∧ Bounds s

theorem tail_nil {s₀ : State} (h : kf s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem lastBlock_eq : lastBlock =
    .seq (.block [.li Y0 0, .addi X1 .a0 56, .add X1 X1 Y1, .li X0 16, .sub X0 X0 Y1])
      (.seq (.loop (.block zeroBody) (.nonzero X0))
        (.block (([.li Y0 1, .addi X1 .a0 56, .add X1 X1 Y1, .store .b Y0 X1 0] : List Instr) ++
          absorb .a0 56 false))) := rfl

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : F0 s₀ s₁)
    (hpos : 0 < kf s₀) : WP isa lastBlock s₁ (Tail s₀ s₁) := by
  have hk := kf_lt s₀
  rw [lastBlock_eq]
  refine WP.seq (WP.mono (zinit_ok h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have g : ∀ r, r ≠ X1 → r ≠ X0 → r ≠ Y0 → s₄.gpr r = s₁.gpr r := h₄.keep
  have x0₄ : s₄.gpr .a0 = st s₀ := by rw [g .a0 (by decide) (by decide) (by decide), h₁.a0]
  have hk₄ : Keys (Rn s₀) s₄ := h₁.keys.of_regs fun r hr => g r (by revert r; decide)
    (by revert r; decide) (by revert r; decide)
  refine WP.mono (absorbBuf_ok s₄ false hk₄ (by rw [h₄.wr, x0₄]; exact hp.st_in))
    fun s₅ ⟨ha, k₅⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2.1, h₄.wr],
    by rw [k₅.2.1]; exact h₄.frame, fun hA => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [k₅.gpr', g _ (by decide) (by decide) (by decide)]
  · have hv₄ : hv s₄ = hv s₁ := by
      simp only [hv, val3, g H0 (by decide) (by decide) (by decide),
        g H1 (by decide) (by decide) (by decide), g H2 (by decide) (by decide) (by decide)]
    have hb₄ : Bounds s₁ → Bounds s₄ := by
      simp only [Bounds, g H2 (by decide) (by decide) (by decide)]; exact id
    obtain ⟨hv₁, hb₁⟩ := h₁.acc hA
    obtain ⟨hv, hb⟩ := ha (hb₄ hb₁)
    refine ⟨?_, hb⟩
    have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
    rw [hv, hv₄, hv₁, x0₄, padded_value h₄.buf,
      Poly1305.absorbAll_block (by omega_using [hpos, hk, hlen]) (by omega_using [hpos, hk, hlen]),
      Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : F0 s₀ s₁) {s : State}
    (ht : Tail s₀ s₁ s) :
    WP isa (.block (reduce ++ addS ++ storeTag)) s fun s' => Proof.Poly1305.finalizeRISCV64.post s₀ s' := by
  have x0 : s.gpr .a0 = st s₀ := by rw [ht.keep .a0 (by simp), h₁.a0]
  have x2 : s.gpr .a2 = op s₀ := by rw [ht.keep .a2 (by simp), h₁.a2]
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₂ ⟨hr, k₂⟩ => ?_)
  have x0₂ : s₂.gpr .a0 = st s₀ := by rw [k₂.gpr', x0]
  refine WP.block_append (WP.mono (addS_ok s₂ (by
    rw [k₂.2.2.1, k₂.2.2.2.1, ht.wr, x0₂]; exact List.mem_append_right _ hp.st_in)
    (by rw [x0₂]; exact hp.st_al))
    fun s₃ ⟨ha, k₃⟩ => ?_)
  have x2₃ : s₃.gpr .a2 = op s₀ := by rw [k₃.gpr', k₂.gpr', x2]
  refine WP.mono (storeTag_ok s₃ (by rw [k₃.2.2.2.1, k₂.2.2.2.1, ht.wr, x2₃]; exact hp.o_in))
    fun s₄ hm₄ => ?_
  intro key msg hbuf hcnt
  obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
  have hk : kf s₀ = (W ++ B).length % 16 := hcnt
  have htail : tail s₀ = B := by rw [tail, hk, off_56]; exact hBb
  rw [← htail]
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := ht.acc hA
  have hN := hr hb
  rw [hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)] at hN
  -- The key's `s`, unchanged since entry.
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [k₂.2.1]
    exact ht.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wR (st s₀), by simp, bfR_sub_wR _⟩
  have hS : word s₂.mem (s₂.gpr .a0) 40 + 2 ^ 64 * word s₂.mem (s₂.gpr .a0) 48 =
      leNum (((bytesAt s₀.mem (off (st s₀) 24) 32).drop 16).take 16) := by
    rw [key_drop, leNum_key, x0₂, word, word, word, word, add_ofNat_zero, off, Offset.add_add,
      key_word hf (d := 40) (by decide) (by decide), key_word hf (d := 48) (by decide) (by decide)]
  rw [hS] at ha
  have hH : (s₂.gpr H0).toNat + 2 ^ 64 * (s₂.gpr H1).toNat + 2 ^ 128 * (s₂.gpr H2).toNat =
      accumulate (clamp (leNum ((bytesAt s₀.mem (off (st s₀) 24) 32).take 16))) (W ++ tail s₀) := by
    rw [clamp_key, Poly1305.accumulate_append hrep.1, repr_acc hrep]
    exact hN
  simp only [mac]
  rw [repr_key hrep] at hH ha
  rw [hm₄, x2₃]
  refine tag_bytes _ _ _ _ _ ?_
  rw [ha, ← hH]
  omega_using []

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ (Proof.Poly1305.finalizeRISCV64.post s₀) := by
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := Tail s₀ s₁) ?_ fun s₃ h₃ => fepilogue_ok hp h₁ h₃)
  refine WP.ite (decide (kf s₀ = 0))
    (by rw [eval_zero, h₁.y1, ofNat_beq_zero (by have := kf_lt s₀; omega_using [this])])
    (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, by rw [h₁.mem]; exact Frame.refl _ _,
      fun hA => ?_⟩
    obtain ⟨e, b⟩ := h₁.acc hA
    refine ⟨?_, b⟩
    rw [tail_nil h, Poly1305.absorbAll_nil, e]
  · simp only [decide_eq_false_iff_not] at h
    exact lastBlock_ok hp h₁ (Nat.pos_of_ne_zero h)

theorem finalize_ok (s : State) (hp : FPre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.finalizeRISCV64.post s s' := by
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (finalize_correct hp) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

theorem finalize_ct {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
      s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp) :
    ConstantTime isa pre pub finalize := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h0, h1, h2, hsp⟩ := hpub s₁ s₂ h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-- A state satisfying the precondition. -/
def finalizeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩]

theorem finalize_verified : Verified RISCV64.target finalize Proof.Poly1305.finalizeRISCV64 :=
  ⟨fun s hs => finalize_ok s ⟨by rw [hs.2.1]; exact List.mem_cons_self,
      by rw [hs.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self, hs.2.2.1, hs.2.2.2⟩,
    finalize_ct fun _ _ h => h,
    ⟨finalizeSat, rfl, rfl, Region.disjoint_of_sep (by decide), by decide⟩⟩

end VG.Proof.Poly1305.RISCV64

end

end

/-!
# Poly1305 on RISC-V: `init`

The key is copied into the state a byte at a time, and the accumulator's 24
bytes are zeroed (`Proof/Framework/RISCV64/Bytes.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem byte_off (p : Addr) (d i : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (d + i) := Offset.add_add p d i

theorem init_correct (s : State) (hs : Proof.Poly1305.initRISCV64.pre s) :
    WP isa init s (Proof.Poly1305.initRISCV64.post s) := by
  obtain ⟨hrd, hwr, hdj⟩ := hs
  rw [init]
  refine WP.block_append (WP.mono (Bytes.copyBytes_ok (s := s) (tmp := .t0) (src := .a1) (dst := .a0)
    (soff := 0) (doff := 24) (n := 32) (by decide) (by decide) (by decide) (by decide)
    (fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      by rw [Nat.zero_add]; exact contains_off (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => in_st (by rw [hwr]; exact List.mem_singleton_self _) (by omega_using [hi]))
    (fun i hi hc => hdj (s.gpr .a1 + BitVec.ofNat 64 (0 + i))
      ((Offset.sub_base (s.gpr .a0) (d := 24) (n := 32) (k := 128) (by decide)) _ hc)
      (by rw [Nat.zero_add]; exact contains_off (by omega_using [hi]) (by omega_using [hi])))) fun s₁ h₁ => ?_)
  have a0₁ : s₁.gpr .a0 = s.gpr .a0 := h₁.gpr _ (by decide)
  refine WP.mono (Bytes.storeBytes_ok (s := s₁) (tmp := .t0) (dst := .a0) (doff := 0)
    (bs := List.replicate 24 0) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [h₁.wr, a0₁]
      exact in_st (by rw [hwr]; exact List.mem_singleton_self _)
        (by simp only [List.length_replicate] at hi; omega_using [hi]))) fun s₂ h₂ => ?_
  refine ⟨rfl, ?_, ?_⟩
  · simp only [bytesAt]
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    rw [show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl, byte_off, ← a0₁,
      h₂.frame _ fun r hr hc => ?_, a0₁, h₁.copied i hi, Nat.zero_add]
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [List.length_replicate, Region.Contains] at hc
    rw [add_ofNat_zero, Offset.add_sub_cancel_left, toNat_ofNat_lt (by omega_using [hi])] at hc
    omega_using [hc, hi]
  · rw [show bytesAt s₂.mem (s.gpr .a0) 24 = List.replicate 24 0 from ?_, Poly1305.leNum_replicate_zero]
    · rfl
    simp only [bytesAt]
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    have := h₂.stored i (by simp only [List.length_replicate]; omega_using [hi])
    rw [Nat.zero_add, a0₁] at this
    rw [this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi, ↓reduceIte, Option.getD_some]
    rfl

theorem init_ok (s : State) (hs : Proof.Poly1305.initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.initRISCV64.post s s' := by
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep [.t0] (init_correct s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

theorem init_ct : ConstantTime isa Proof.Poly1305.initRISCV64.pre
    Proof.Poly1305.initRISCV64.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified RISCV64.target init Proof.Poly1305.initRISCV64 :=
  ⟨init_ok, init_ct, ⟨initSat, rfl, rfl, Region.disjoint_of_sep (by decide)⟩⟩

end VG.Proof.Poly1305.RISCV64
