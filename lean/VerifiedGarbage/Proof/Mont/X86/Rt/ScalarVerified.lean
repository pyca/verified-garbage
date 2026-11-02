module

import VerifiedGarbage.Proof.Mont.X86.Rt.Body
meta import VerifiedGarbage.Proof.Mont.X86.Rt.Body
import VerifiedGarbage.Proof.Dsa.X86.PowABI
meta import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.Basic
meta import Init.Data.BitVec.Basic
public import Init.Data.List.BasicAux
meta import Init.Data.List.BasicAux
public import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import Init.Data.BitVec.BasicAux
meta import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.Isa

/-! # `vg_rsa_mont_mul_at` on x86 against its contract

Its correctness (`rt_scalar_correct`), from `body_ok`; its timing, from one taint
check of its code (`rt_scalar_constantTime`): every public value is in a register
or computed from the read-only arguments.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)

theorem numAt_val32 (m : Mem) (ws : Addr) (d n : Nat) : numAt m ws d (8 * n) = val32 m ws d (2 * n) := by
  unfold numAt
  rw [show 8 * n = 4 * (2 * n) by omega]
  exact VG.Proof.Dsa.X86.Pow.read_eq_val32 m ws (2 * n) d

theorem numAt_w32 (m : Mem) (ws : Addr) (d : Nat) : numAt m ws d 4 = w32 m ws d := by
  unfold numAt
  rw [show 4 = 4 * 1 from rfl, VG.Proof.Dsa.X86.Pow.read_eq_val32 m ws 1 d]
  simp [val32]

theorem rt_scalar_correct (s : State) (h : (Proof.Rsa.MontMul.mulContract abi 0).pre s) :
    ∃ tr t, Exec isa Rt.scalarBody s tr t ∧ abiPreserved s t ∧ (Proof.Rsa.MontMul.mulContract abi 0).post s t := by
  have A := rtAbi_of h
  have hso := A.so
  have hol := A.o_le
  have hscr := A.s_le
  have hinv := A.inv
  have hb := A.bLt
  simp only [Apart, scratchBytes] at hso hscr
  rw [numAt_val32, numAt_w32] at hinv
  rw [numAt_val32, numAt_val32] at hb
  obtain ⟨tr, t, E, O, lt, cong, ebx, esi, ebp, edi, esp, -, -⟩ :=
    scalarBody_ok A.ws A.args A.vals A.lay (by simp only [nOf]; have := A.pos; omega) A.n32
      (by simp only [nOf, lenOf]; omega) (by simp only [nOf]; omega) hinv hb
  have far : ∀ x, ¬ (⟨wsOf s, lenOf s⟩ : Region).Contains x 1 → t.mem x = s.mem x := fun x hx =>
    O x fun r hr => by
      have := Dynamic.ofs_far hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [nOf, lenOf] at this ⊢ <;> omega
  refine ⟨tr, t, E, ⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · exact Mem.readW_congr fun i hi => far _ fun hc =>
      A.retScratch _ (Offset.contains_base _ (by omega) (by omega)) hc
  · sig_post [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · rw [numAt_val32, numAt_val32]; exact lt
    · rw [numAt_val32, numAt_val32, numAt_val32, numAt_val32,
        show 64 * (arg s 2).toNat = 32 * nOf s by simp only [nOf]; omega]
      exact cong
    · intro i hi hj
      apply O _
      intro r hr
      rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, scratchBytes] at this
      rcases hr with rfl | rfl <;> simp only [nOf] <;> omega

/-! ## Timing -/

/-- The stack pointer and the 36 bytes of arguments above the return address are public. -/
def rtTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 40 }

theorem rtTaint_wf {s : State} (A : RtABI s) : VG.X86.Taint.Wf rtTaint s := by
  have hb := A.stackBound
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [rtTaint]; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  rw [A.wr]
  simp only [List.mem_singleton]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 36) (by omega) A.retScratch A.argScratch.symm

theorem rt_publicArgs {s t : State} (H : (Proof.Rsa.MontMul.mulContract abi 0).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 9, arg s i = arg t i := by
  sig_pub [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => with_reducible assumption
  | 1, _ => with_reducible assumption
  | 2, _ => with_reducible assumption
  | 3, _ => with_reducible assumption
  | 4, _ => with_reducible assumption
  | 5, _ => with_reducible assumption
  | 6, _ => with_reducible assumption
  | 7, _ => with_reducible assumption
  | 8, _ => with_reducible assumption

theorem rtTaint_agree {s₁ s₂ : State} (A₁ : RtABI s₁) (A₂ : RtABI s₂)
    (sp : s₁.gpr .esp = s₂.gpr .esp) (args : ∀ i < 9, arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree rtTaint s₁ s₂ := by
  have f₁ := A₁.stackBound; have f₂ := A₂.stackBound
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, rtTaint_wf A₁, rtTaint_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [rtTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [rtTaint] at hk
    rw [show VG.X86.Taint.depth rtTaint.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq (by omega) h4 hk, VG.X86.Taint.argByte_eq (by omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem rt_scalar_constantTime :
    ConstantTime isa (Proof.Rsa.MontMul.mulContract abi 0).pre (Proof.Rsa.MontMul.mulContract abi 0).pub Rt.scalarBody :=
  VG.Taint.constantTime (A := taint) rtTaint (fun _ _ h₁ h₂ hp =>
    rtTaint_agree (rtAbi_of h₁) (rtAbi_of h₂) (rt_publicArgs hp).1 (rt_publicArgs hp).2) (by taint_decide)

/-! ## A state meeting the precondition

At width 1: the working space of 15 words at `0x1000`, its inverse word `1`
at 0 and its modulus `2^64 - 1`, all bytes `0xFF`, at 8, whose inverse
modulo `2^32` is `-1`; the function's range at 16, the result at 96 and the
operands, zero, at 104 and 112. The arguments are above `esp = 0xf0000000`. -/

/-- The arguments' values. -/
def satArg (i : Nat) : BitVec 32 :=
  [0x1000, 15, 1, 8, 0, 16, 96, 104, 112].getD i 0

def satMem (x : Addr) : BitVec 8 :=
  if x.toNat < 0x10000 then
    (if x.toNat = 0x1000 then 1 else if 0x1008 ≤ x.toNat ∧ x.toNat < 0x1010 then 0xFF else 0)
  else if (x - 0xf0000004).toNat < 36 then
    (satArg ((x - 0xf0000004).toNat / 4)).extractLsb' (8 * ((x - 0xf0000004).toNat % 4)) 8
  else 0

def satState : State where
  gpr r := if r = .esp then 0xf0000000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0xf0000004, 36⟩]
  wr := [⟨0x1000, 120⟩]

theorem satMem_ws {d : Nat} (hd : d < 0xF000) :
    satMem (0x1000 + BitVec.ofNat 64 d) = if d = 0 then 1 else if 8 ≤ d ∧ d < 16 then 0xFF else 0 := by
  have ht : (0x1000 + BitVec.ofNat 64 d : Addr).toNat = 0x1000 + d := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x1000 : Addr).toNat = 0x1000 from rfl]; omega
  simp only [satMem, ht]
  repeat' split
  all_goals first | rfl | omega

theorem satArg_eq (i : Nat) (hi : i < 9) : arg satState i = satArg i := by
  show (Mem.read satMem (argAddr satState i) 4).setWidth 32 = _
  rw [BitVec.setWidth_eq]
  have t₀ : (0xf0000000 : BitVec 32).toNat = 4026531840 := rfl
  have t₁ : (0xf0000004 : Addr).toNat = 4026531844 := rfl
  have ha : argAddr satState i = 0xf0000004 + BitVec.ofNat 64 (4 * i) := by
    show ((0xf0000000 : BitVec 32) + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, t₀, t₁]
    omega
  rw [ha]
  apply Mem.read_eq_of_bytes
  intro j hj
  have hx : (0xf0000004 + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 j - 0xf0000004 : Addr).toNat = 4 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, t₁]
    omega
  have hlarge : ¬ (0xf0000004 + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 j : Addr).toNat < 0x10000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, t₁]; omega
  simp only [satMem, hlarge, hx, ↓reduceIte, show 4 * i + j < 36 by omega]
  rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega]

/-- `k` bytes of `0xFF`. -/
theorem read_ff (m : Mem) : ∀ (k : Nat) (a : Addr), (∀ i < k, m (a + BitVec.ofNat 64 i) = 0xFF) →
    (m.read a k).toNat = 2 ^ (8 * k) - 1
  | 0, _, _ => rfl
  | k + 1, a, h => by
    have h0 := h 0 (by omega)
    rw [BitVec.add_zero] at h0
    rw [read_toNat_succ, h0, read_ff m k (a + 1) fun i hi => by
      rw [BitVec.add_assoc, show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
        rw [Nat.add_comm, BitVec.ofNat_add]; rfl]
      exact h (i + 1) (by omega)]
    have : 1 ≤ 2 ^ (8 * k) := Nat.one_le_two_pow
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    show 255 + 2 ^ 8 * (2 ^ (8 * k) - 1) = 2 ^ (8 * k) * 2 ^ 8 - 1
    omega

theorem satModulus : numAt satMem 0x1000 8 8 = 2 ^ 64 - 1 := by
  unfold numAt
  rw [read_ff _ _ _ fun i hi => ?_]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, satMem_ws (by omega)]
  have h₁ : ¬8 + i = 0 := by omega
  have h₂ : 8 ≤ 8 + i ∧ 8 + i < 16 := by omega
  simp only [h₁, h₂, and_self, ↓reduceIte]

theorem satInv : numAt satMem 0x1000 0 4 = 1 := by
  unfold numAt
  rw [Mem.read_eq_of_bytes (v := (1 : BitVec 32)) fun j hj => ?_]
  · rfl
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, satMem_ws (by omega)]
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem satB : numAt satMem 0x1000 112 8 = 0 := by
  unfold numAt
  rw [Mem.read_eq_of_bytes (v := (0 : BitVec 64)) fun j hj => ?_]
  · rfl
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, satMem_ws (by omega)]
  have h₁ : ¬112 + j = 0 := by omega
  have h₂ : ¬(8 ≤ 112 + j ∧ 112 + j < 16) := by omega
  simp only [h₁, h₂, ↓reduceIte]
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

theorem rt_satisfiable : ∃ s, (Proof.Rsa.MontMul.mulContract abi 0).pre s := by
  refine ⟨satState, ?_⟩
  have a : ∀ i, i < 9 → arg satState i = satArg i := satArg_eq
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide)
  have a6 := a 6 (by decide); have a7 := a 7 (by decide); have a8 := a 8 (by decide)
  simp only [satArg, List.getD_cons_succ, List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8
  have e0 : argAddr satState 0 = 0xf0000004 := by decide
  have hw : BitVec.setWidth 64 (4096 : BitVec 32) = 4096 := by decide
  have hsp : BitVec.setWidth 64 (0xf0000000 : BitVec 32) = 0xf0000000 := by decide
  sig_pre [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, e0, hw, hsp]
  sig_and_intros
  all_goals try decide
  all_goals try exact Region.disjoint_of_sep (by decide)
  all_goals try (simp only [Apart, scratchBytes]; decide)
  all_goals try (rw [show (4096 : Addr) = 0x1000 from rfl, satModulus, satInv]; decide)
  all_goals try (rw [show (4096 : Addr) = 0x1000 from rfl, satModulus, satB]; decide)

theorem rt_scalar_verified : Verified target Rt.scalarBody (Proof.Rsa.MontMul.mulContract abi 0) :=
  ⟨rt_scalar_correct, rt_scalar_constantTime, rt_satisfiable⟩

end VG.Proof.Mont.X86.Rt
