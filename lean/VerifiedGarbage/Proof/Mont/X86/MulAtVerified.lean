module

public import VerifiedGarbage.Proof.Mont.X86.MulAtBody
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! # The callable multiplication against its contract

`verified n`: `mulAtBody n` meets `mulContract (ctxLayout n)` for `2 ≤ n`.
Its timing follows from one taint check of its code without offsets and
immediates, the same at every width (`check_erase`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Spec.Rsa.MontMulAt

theorem mulAt_correct {n : Nat} (hn : 2 ≤ n) (s : State) (h : (mulContract (ctxLayout n) abi 20).pre s) :
    ∃ tr t, Exec isa (mulAtBody n) s tr t ∧ abiPreserved s t ∧
      (mulContract (ctxLayout n) abi 20).post s t := by
  have A := mulAbi_of h
  obtain ⟨tr, t, E, R, -, -, O, L, C⟩ := mulAtBody_ok hn A
  have ediv := contextBytes_div n
  have nw := A.nowrap
  have F : Frame [⟨wsOf s, contextBytes n⟩] s.mem t.mem := by
    intro x hx
    apply O x
    have H := hx _ (List.mem_singleton_self _)
    have := A.o_le
    rw [show 8 * (contextBytes n / 8) = contextBytes n by omega] at this
    simp only [Region.Contains, ofs, List.mem_cons, List.not_mem_nil, or_false] at H ⊢
    rintro r (rfl | rfl) <;> simp only [contextBytes, slot, stride] at * <;> omega
  refine ⟨tr, t, E, ⟨R, ?_⟩, ?_⟩
  · have hr := A.retScratch
    rw [ediv] at hr
    exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
      (fun r hr' => by rw [List.mem_singleton.mp hr']; exact hr) (by decide)
  · sig_post [mulContract, sig, ctxLayout, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [numAt_eq8] using L
    · simpa only [numAt_eq8] using C
    · intro i hi hj
      apply O _
      intro r hr
      rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj r hr

/-- The stack pointer and the 16 bytes of arguments above the return address are public. -/
def mulAtTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 20 }

def mulAtHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint mulAtTaint (Code.erase (mulAtBody 2))

theorem mulAtTaint_wf {n : Nat} {s : State} (A : MulABI n s) : VG.X86.Taint.Wf mulAtTaint s := by
  have hb := A.stackBound
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [mulAtTaint]; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  rw [A.wr]
  simp only [List.mem_singleton]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) A.retScratch A.argScratch.symm

theorem mulAtTaint_agree {n : Nat} {s₁ s₂ : State} (A₁ : MulABI n s₁) (A₂ : MulABI n s₂)
    (sp : s₁.gpr .esp = s₂.gpr .esp) (args : ∀ i < 4, arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree mulAtTaint s₁ s₂ := by
  have f₁ := A₁.stackBound; have f₂ := A₂.stackBound
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, mulAtTaint_wf A₁, mulAtTaint_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [mulAtTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [mulAtTaint] at hk
    rw [show VG.X86.Taint.depth mulAtTaint.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq (by omega) h4 hk, VG.X86.Taint.argByte_eq (by omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem mulAt_publicArgs {n : Nat} {s t : State} (H : (mulContract (ctxLayout n) abi 20).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i := by
  sig_pub [mulContract, sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => with_reducible assumption
  | 1, _ => with_reducible assumption
  | 2, _ => with_reducible assumption
  | 3, _ => with_reducible assumption

/-- The code's analysis, without offsets and immediates, is the same at every width. -/
theorem mulAt_check (n : Nat) : (VG.Taint.check taint mulAtTaint (mulAtBody n) mulAtHint).isSome = true := by
  rw [check_of_erase_eq (mulAtBody n) (mulAtBody 2) mulAtTaint mulAtHint rfl rfl (by decide +kernel)]
  decide +kernel

theorem mulAt_constantTime (n : Nat) :
    ConstantTime isa (mulContract (ctxLayout n) abi 20).pre (mulContract (ctxLayout n) abi 20).pub
      (mulAtBody n) :=
  VG.Taint.constantTime (A := taint) mulAtTaint (fun _ _ h₁ h₂ hp =>
    mulAtTaint_agree (mulAbi_of h₁) (mulAbi_of h₂) (mulAt_publicArgs hp).1 (mulAt_publicArgs hp).2)
    (mulAt_check n)

/-! ## A state meeting the precondition

The working space at `0x1000`: its inverse word `1` and its modulus
`2^(64 n) - 1`, all bytes `0xFF`, whose inverse modulo `2^32` is `-1`. The
operands are at byte 4, apart from the function's slots, and below the
modulus since their lowest byte is zero; the result goes to slot 3. -/

def satMem (n : Nat) (x : Addr) : BitVec 8 :=
  if x.toNat < 0x10000 then
    (if x.toNat = 0x1000 then 1 else if 0x1040 ≤ x.toNat ∧ x.toNat < 0x1040 + 8 * n then 0xFF else 0)
  else if (x - 0xf0000008).toNat < 4 then
    (BitVec.ofNat 32 (slot n 3)).extractLsb' (8 * (x - 0xf0000008).toNat) 8
  else if x = 0xf0000005 then 0x10 else if x = 0xf000000c then 4 else if x = 0xf0000010 then 4 else 0

def satState (n : Nat) : State where
  gpr r := if r = .esp then 0xf0000000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem n
  rd := [⟨0xf0000004, 16⟩]
  wr := [⟨0x1000, contextBytes n / 8 * 8⟩]

theorem satMem_ws (n : Nat) {d : Nat} (hd : d < 0xF000) :
    satMem n (0x1000 + BitVec.ofNat 64 d) =
      if d = 0 then 1 else if 64 ≤ d ∧ d < 64 + 8 * n then 0xFF else 0 := by
  have ht : (0x1000 + BitVec.ofNat 64 d : Addr).toNat = 0x1000 + d := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x1000 : Addr).toNat = 0x1000 from rfl]; omega
  simp only [satMem, ht]
  split_ifs <;> first | rfl | omega

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

theorem disj_lit {a b n k : Nat} (h : a + n ≤ b) (hb : b + k < 2 ^ 64) :
    (⟨BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨BitVec.ofNat 64 b, k⟩ :=
  Offset.disjoint_of_le (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)

theorem satModulus {n : Nat} (hn : 2 ≤ n) (hn' : n ≤ 128) :
    numAt (satMem n) 4096 (slot n 0) (8 * n) = 2 ^ (64 * n) - 1 := by
  unfold numAt
  rw [read_ff _ _ _ fun i hi => ?_, show 8 * (8 * n) = 64 * n by omega]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show slot n 0 = 64 by unfold slot stride; omega,
    show (4096 : Addr) = 0x1000 from rfl, satMem_ws n (by omega)]
  have h₁ : ¬64 + i = 0 := by omega
  have h₂ : 64 ≤ 64 + i ∧ 64 + i < 64 + 8 * n := by omega
  simp only [h₁, h₂, and_self, ↓reduceIte]

theorem satInv (n : Nat) : numAt (satMem n) 4096 0 4 = 1 := by
  unfold numAt
  rw [show (4096 : Addr) + BitVec.ofNat 64 0 = 0x1000 + BitVec.ofNat 64 0 from rfl,
    Mem.read_eq_of_bytes (v := (1 : BitVec 32)) fun j hj => ?_]
  · rfl
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, satMem_ws n (by omega)]
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem satB {n : Nat} (hn : 2 ≤ n) (hn' : n ≤ 128) :
    numAt (satMem n) 4096 4 (8 * n) < 2 ^ (64 * n) - 1 := by
  unfold numAt
  obtain ⟨k, hk⟩ : ∃ k, 8 * n = k + 1 := ⟨8 * n - 1, by omega⟩
  rw [hk, read_toNat_succ, show (4096 : Addr) + BitVec.ofNat 64 4 = 0x1000 + BitVec.ofNat 64 4 from rfl,
    satMem_ws n (by omega), show 64 * n = 8 * (k + 1) by omega]
  have h₁ : ¬(4 = 0) := by omega
  have h₂ : ¬(64 ≤ 4 ∧ 4 < 64 + 8 * n) := by omega
  simp only [h₁, h₂, ↓reduceIte]
  have := (Mem.read (satMem n) (0x1000 + BitVec.ofNat 64 4 + 1) k).isLt
  rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
  show 0 + 2 ^ 8 * _ < _
  omega

theorem satisfiable {n : Nat} (hn : 2 ≤ n) (hn' : n ≤ 128) :
    ∃ s, (mulContract (ctxLayout n) abi 20).pre s := by
  refine ⟨satState n, ?_⟩
  have argAt : ∀ (i : Nat) (v : BitVec 32), argAddr (satState n) i = 0xf0000004 + BitVec.ofNat 64 (4 * i) →
      (∀ j < 4, satMem n (0xf0000004 + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8) →
      arg (satState n) i = v := by
    intro i v ha hb
    show (Mem.read (satMem n) (argAddr (satState n) i) 4).setWidth 32 = _
    rw [ha, BitVec.setWidth_eq]
    exact Mem.read_eq_of_bytes hb
  have a0 : arg (satState n) 0 = 0x1000 := argAt 0 _ (by rw [show argAddr (satState n) 0 = argAddr (satState 0) 0 from rfl]; decide) fun j hj => by
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  have a1 : arg (satState n) 1 = BitVec.ofNat 32 (slot n 3) := argAt 1 _ (by rw [show argAddr (satState n) 1 = argAddr (satState 0) 1 from rfl]; decide) fun j hj => by
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  have a2 : arg (satState n) 2 = 4 := argAt 2 _ (by rw [show argAddr (satState n) 2 = argAddr (satState 0) 2 from rfl]; decide) fun j hj => by
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  have a3 : arg (satState n) 3 = 4 := argAt 3 _ (by rw [show argAddr (satState n) 3 = argAddr (satState 0) 3 from rfl]; decide) fun j hj => by
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  have e0 : argAddr (satState n) 0 = 0xf0000004 := by
    rw [show argAddr (satState n) 0 = argAddr (satState 0) 0 from rfl]; decide
  clear argAt
  have hw : BitVec.setWidth 64 (4096 : BitVec 32) = 4096 := by decide
  have hsp : BitVec.setWidth 64 (0xf0000000 : BitVec 32) = 0xf0000000 := by decide
  have hlow : (0xf0000000 : Addr) - 20#64 = 0xefffffec := by decide
  have t4096 : (4096 : BitVec 32).toNat = 4096 := rfl
  have t4096' : (4096 : Addr).toNat = 4096 := rfl
  have t4 : (4 : BitVec 32).toNat = 4 := rfl
  have tv : (BitVec.ofNat 32 (slot n 3)).toNat = slot n 3 := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold slot stride; omega
  have hL : 4096 + contextBytes n / 8 * 8 ≤ 0xefffffec := by unfold contextBytes slot stride; omega
  sig_pre [mulContract, sig, ctxLayout, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [a0, a1, a2, a3, e0, hw, hsp, hlow]
  sig_and_intros
  all_goals try decide
  all_goals try exact Region.disjoint_of_sep (by decide)
  all_goals try (simp only [t4096, t4, Apart, contextBytes, slot, stride]; omega)
  all_goals try (rw [tv]; simp only [Apart, contextBytes, slot, stride]; omega)
  · exact disj_lit (a := 4096) (b := 4026531844) (by omega) (by omega)
  · exact (disj_lit (a := 4096) (b := 4026531840) (by omega) (by omega)).symm
  · exact (disj_lit (a := 4096) (b := 0xefffffec) (by omega) (by omega)).symm
  · rw [satModulus hn hn', satInv]
    have : 1 ≤ 2 ^ (64 * n) := Nat.one_le_two_pow
    rw [Nat.mul_one, Nat.sub_add_cancel this]
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
  · rw [satModulus hn hn', t4]
    exact satB hn hn'

theorem mulAt_spSafe (n : Nat) : (mulAtBody n).allInstrs (fun i => !isa.writesSp i) = true := by
  rw [Code.allInstrs_eq]
  simp only [mulAtBody, mulAt, instrs, List.all_append]
  rfl

theorem mulAt_verified (n : Nat) (hn : 2 ≤ n := by decide) (hn' : n ≤ 128 := by decide) :
    Verified target (mulAtBody n) (mulContract (ctxLayout n) abi 20) :=
  ⟨mulAt_correct hn, mulAt_constantTime n, satisfiable hn hn'⟩

theorem mulAt_verified_mem {n : Nat} (h : n ∈ mulWidths) :
    Verified target (mulAtBody n) (mulContract (ctxLayout n) abi 20) := by
  simp only [mulWidths, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact mulAt_verified (k + 4) (by omega) (by omega)

end VG.Proof.Mont.X86.Dynamic
