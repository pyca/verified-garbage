module

public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.TripleDes.X86.Bytes
public import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
public import VerifiedGarbage.Proof.Rc2.X86.KeySteps
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Reduce
public import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
public import VerifiedGarbage.Proof.TripleDes.X86.ConstantTime
import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
import VerifiedGarbage.Proof.TripleDes.Bytes
import Batteries.Logic
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `TripleDes.X86.Word`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86

theorem mask28 (x : BitVec 32) : x &&& 0x0fffffff = (x.setWidth 28).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 28 - 1) = x.toNat % 268435456 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem rotate28_word (x : BitVec 28) (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ((x.setWidth 32).rotateRight (32 - n) ^^^ (x.setWidth 32) >>> (28 - n)) &&& 0x0fffffff =
      (x.rotateLeft n).setWidth 32 := by
  rw [mask28]
  apply congrArg (BitVec.setWidth 32)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n32 : (32 - n) % 32 = 32 - n := Nat.mod_eq_of_lt (by omega_using [hn])
  have n28 : n % 28 = n := Nat.mod_eq_of_lt (by omega_using [hn'])
  rw [n32, n28]
  rw [show 32 - (32 - n) = n by omega_using [hn']]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (28 - n) < 32 by omega_using [hn', h], BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 32 by omega_using [hj],
      show j - n < 32 by omega_using [hj], BitVec.getLsbD_of_ge]


theorem packed48 (x : BitVec 48) :
    ((x >>> 32).setWidth 16).setWidth 32 ++ x.setWidth 32 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases hlo : i < 32
  · simp only [hlo, ite_true, decide_true, Bool.true_and]
  · simp (disch := omega) only [hlo, ite_false, decide_true, Bool.true_and,
      show i - 32 < 32 by omega_using [hi], show 32 + (i - 32) = i by omega_using [hlo]]
    by_cases h48 : i < 48
    · simp only [show i - 32 < 16 by omega_using [h48], decide_true, Bool.true_and]
    · simp only [show ¬i - 32 < 16 by omega_using [h48], decide_false, Bool.false_and,
        BitVec.getLsbD_of_ge x i (by omega_using [h48])]

end VG.Proof.TripleDes.X86

end

end

/-! ### `TripleDes.X86.Key.Verified`, which only this module used -/

section

/-! ### `TripleDes.X86.Key.ConstantTime`, which only this module used -/

section

/-! ### `TripleDes.X86.Key.Component`, which only this module used -/

section

/-! ### `TripleDes.X86.Key.Permutation`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.Impl.TripleDes.X86

theorem pc1_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx) s = some s' ∧
      s'.gpr .eax = ((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))).setWidth 28).setWidth 32 ∧
      s'.gpr .ebx = (((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))) >>> 28).setWidth 28).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) 32 28
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .esi .edi .eax .ebx (instrs keyPermutation1.lit) keyPermutation1_check (by decide +kernel) s
  obtain hcode : permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩


theorem pc2_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx) s = some s' ∧
      s'.gpr .eax = ((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .edi) (s.gpr .esi))).setWidth 32).setWidth 32 ∧
      s'.gpr .ebx = (((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .edi) (s.gpr .esi))) >>> 32).setWidth 16).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) 28 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .edi .esi .eax .ebx (instrs keyPermutation2.lit) keyPermutation2_check (by decide +kernel) s
  obtain hcode : permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.X86.Key

end

end

/-! ### `TripleDes.X86.Key.Compare`, which only this module used -/

section

/-! ### `TripleDes.X86.Key.Rotation`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Impl.TripleDes.X86.Key
open VG.Proof.Rc2.X86 (Keep)

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .eax)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ∃ s', runBlock isa (rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ Keep [r, .eax] s s' := by
  obtain hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega_using [hn, hn']
  obtain hright : 1 ≤ 28 - n ∧ 28 - n ≤ 31 := by omega_using [hn']
  refine ⟨_, by
    simp only [hleft, hright, and_self, rotate28, rr, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, Ne.symm hr, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact VG.Proof.TripleDes.X86.rotate28_word x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .esi = (c.rotateLeft n).setWidth 32
  d : s'.gpr .edi = (d.rotateLeft n).setWidth 32
  keep : Keep [.esi, .edi, .eax] s s'

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    WP isa (rotate n) s (RotatePost c d n s) := by
  rw [rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, keep₁⟩ := rotate28_ok s .esi (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain d₁ : s₁.gpr .edi = d.setWidth 32 := (keep₁.reg .edi (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, keep₂⟩ := rotate28_ok s₁ .edi (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(keep₂.reg .esi (by decide)).trans c₁, d₂, ?_⟩⟩
  refine ⟨?_, keep₂.mem.trans keep₁.mem, keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
  intro r hr
  simp only [List.mem_cons, not_or] at hr
  exact (keep₂.reg r (by simp only [List.mem_cons, hr.2.1,
    hr.2.2, or_self, not_false_eq_true])).trans
    (keep₁.reg r (by simp only [List.mem_cons, hr.1,
      hr.2.2, or_self, not_false_eq_true]))

end VG.Proof.TripleDes.X86.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    decide ((BitVec.ofNat 32 j).toNat < (BitVec.ofNat 32 2).toNat) = decide (j < 2) ∧
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 k) == (0 : BitVec 32)) = decide (j = k) := by
  decide

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .ebp 20)), .alu .cmp .eax (.imm 2)] s = some s' ∧
      isa.eval .b s' = some (decide (j < 2)) ∧
      s'.gpr .eax = BitVec.ofNat 32 j ∧ Keep [.eax] s s' := by
  obtain hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hok.slotIn 5 (by decide)
    exact ⟨r, List.mem_append_right _ h, hc⟩
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load32, State.ea, memOp, hr, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_⟩
  · change some (decide ((roundCount s).toNat < (BitVec.ofNat 32 2).toNat)) = _
    rw [hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1
  · exact hv
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .eax = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      isa.eval .e s' = some (decide (j = k)) ∧ s'.gpr .eax = BitVec.ofNat 32 j ∧ Keep [.eax] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some]
    rfl, ?_, ?_, ?_⟩
  · change some ((s.gpr .eax - BitVec.ofNat 32 k) == 0) = _
    rw [hv]
    exact congrArg some (comparison_values j hj k hk).2
  · exact hv
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (hjreg : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s) :
    WP isa Impl.TripleDes.X86.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.X86.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, eax₁, keep₁⟩ := lowTest_ok s j hj hjreg hok
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.eax] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 5)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.X86.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .esi (by simp)).trans hc)
      ((h.reg .edi (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    refine ⟨ht.c, ht.d, ⟨?_, ht.keep.mem.trans h.mem, ht.keep.rd.trans h.rd,
      ht.keep.wr.trans h.wr⟩⟩
    intro r hr
    obtain ha : r ∉ ([.eax] : List Reg) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact hr.2.2
    exact (ht.keep.reg r hr).trans (h.reg r ha)
  have combine {a b : State} (ha : Keep [.eax] s a) (hb : Keep [.eax] a b) : Keep [.eax] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simpa only [h2, decide_true] using cond₁)
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simpa only [h2, decide_false] using cond₁)
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cond₂, eax₂, keep₂⟩ := eqTest_ok s₁ j 8 hj (by decide)
        eax₁
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      obtain keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simpa only [h8, decide_true] using cond₂)
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simpa only [h8, decide_false] using cond₂)
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cond₃, _, keep₃⟩ := eqTest_ok s₂ j 15 hj (by decide)
            eax₂
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          obtain keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simpa only [h15, decide_true] using cond₃)
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simpa only [h15, decide_false] using cond₃)
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.X86.Key

end

end


/-! ## `Load` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

def keyArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 1) 32

def scheduleArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 3) 32

def keyAddr (s : State) (offset : Nat) : BitVec 64 :=
  (keyArg s + BitVec.ofNat 32 offset).setWidth 64

theorem readKey_ok (s : State) (offset : Nat)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadHead offset) s = some s' ∧
      s'.gpr .edi = bswap (s.mem.readW (keyAddr s offset) 32) ∧
      s'.gpr .esi = bswap (s.mem.readW (keyAddr s (offset + 4)) 32) ∧
      Keep [.edi, .esi, .edx] s s' := by
  obtain h0 := hr 0 (by decide)
  obtain h1 := hr 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, keyAddr, keyArg, wordAddr, addr] at h0
  simp only [Nat.mul_one, keyAddr, keyArg, wordAddr, addr] at h1
  simp only [wordAddr, addr] at harg
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.loadHead, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.load32, State.ea, memOp, harg, h0, h1, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

def loadMem (s : State) (component : Nat) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 5) (0 : BitVec 32)).writeW
    (wordAddr (s.gpr .ebp) 4) (scheduleArg s + BitVec.ofNat 32 (128 * component))

theorem loadTail_ok (s : State) (component : Nat) (hok : Ok sboxCfg s)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadTail component) s = some s' ∧
      s'.gpr .esi = s.gpr .ebx ∧ s'.gpr .edi = s.gpr .eax ∧
      s'.mem = loadMem s component ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) := by
  obtain hw4 := hok.slotIn 4 (by decide)
  obtain hw5 := hok.slotIn 5 (by decide)
  simp only [wordAddr, addr, sboxCfg] at hw4 hw5
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.loadTail, rr, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load32, State.store32, State.ea,
      memOp, hw4, hw5, hr, ite_true, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r ha hd hs hi
    simp only [gpr_setReg, gpr_arithFlags, ha, hd, hs, hi, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .esi = ((x >>> 28).setWidth 28).setWidth 32
  d : s'.gpr .edi = (x.setWidth 28).setWidth 32
  counter : roundCount s' = 0
  ptr : roundKeyPtr s' = scheduleArg s + BitVec.ofNat 32 (128 * component)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  base : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  frame : Frame [workRegion s] s.mem s'.mem

theorem loadMem_frame (s : State) (component : Nat)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Frame [workRegion s] s.mem (loadMem s component) := by
  obtain h4 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega_arith)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  obtain h5 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega_arith)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h5).writeW
    (List.mem_singleton_self _) _ h4

theorem load_ok (s : State) (offset component : Nat) (hok : Ok sboxCfg s)
    (fit : (keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (keyAddr s offset)))) component s) := by
  rw [Impl.TripleDes.X86.Key.load, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, keep₁⟩ := readKey_ok s offset (harg 1 (by decide)) hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain key₁ : packedInput 64 32 (s₁.gpr .esi) (s₁.gpr .edi) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (keyAddr s offset)) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    obtain ha : keyAddr s (offset + 4) = keyAddr s offset + 4 := by
      change VG.Proof.Rc2.X86.addr32 (keyArg s + BitVec.ofNat 32 (offset + 4)) =
        VG.Proof.Rc2.X86.addr32 (keyArg s + BitVec.ofNat 32 offset) + 4
      rw [VG.Proof.Rc2.X86.addr_add (by omega_arith), VG.Proof.Rc2.X86.addr_add (by omega_arith)]
      rw [← VG.Offset.add_ofNat_add_ofNat]
      rfl
    rw [ha]
  rw [key₁] at lo₂ hi₂
  obtain base₂ : s₂.gpr .ebp = s.gpr .ebp :=
    (reg₂ .ebp (by decide +kernel)).trans (keep₁.reg .ebp (by decide))
  obtain sp₂' : s₂.gpr .esp = s.gpr .esp := sp₂.trans (keep₁.reg .esp (by decide))
  obtain hok₂ : Ok sboxCfg s₂ := hok.congr base₂ base₂ (rd₂.trans keep₁.rd) (wr₂.trans keep₁.wr)
  obtain hr₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 3) 4 := by
    rw [sp₂', rd₂, wr₂, keep₁.rd, keep₁.wr]
    exact harg 3 (by decide)
  obtain ⟨s₃, run₃, c₃, d₃, mem₃, rd₃, wr₃, reg₃⟩ := loadTail_ok s₂ component hok₂ hr₂
  obtain base₃ : s₃.gpr .ebp = s.gpr .ebp := (reg₃ .ebp (by decide) (by decide)
    (by decide) (by decide)).trans base₂
  obtain sp₃ : s₃.gpr .esp = s.gpr .esp := (reg₃ .esp (by decide) (by decide)
    (by decide) (by decide)).trans sp₂'
  obtain sched₂ : scheduleArg s₂ = scheduleArg s := by
    unfold scheduleArg
    rw [sp₂', mem₂, keep₁.mem]
  obtain hm : s₃.mem = loadMem s component := by
    rw [mem₃, loadMem, base₂, sched₂, mem₂, keep₁.mem]
    rfl
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃.trans hi₂, d₃.trans lo₂, ?_, ?_,
    rd₃.trans (rd₂.trans keep₁.rd), wr₃.trans (wr₂.trans keep₁.wr), base₃, sp₃, ?_⟩⟩
  · unfold roundCount
    rw [base₃, hm, loadMem, Mem.readW_writeW_sep (counter_ptr_sep s hok.fit) (by decide),
      Mem.readW_writeW_self32]
  · unfold roundKeyPtr
    rw [base₃, hm, loadMem, Mem.readW_writeW_self32]
  · rw [hm]
    exact loadMem_frame s component hok.fit

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Store` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86

def storeMem (s : State) : Mem :=
  (((s.mem.writeW (wordAddr (roundKeyPtr s) 0) (s.gpr .eax)).writeW
    (wordAddr (roundKeyPtr s) 1) (s.gpr .ebx)).writeW
    (wordAddr (s.gpr .ebp) 4) (roundKeyPtr s + 8)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s + 1)

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (!(BitVec.ofNat 32 j + 1 - (16 : BitVec 32) == 0)) = decide (j ≠ 15) := by decide

theorem tail_ok (s : State) (hok : Ok sboxCfg s)
    (hw : ∀ t < 2, InRegions s.wr (wordAddr (roundKeyPtr s) t) 4)
    :
    ∃ s', runBlock isa Impl.TripleDes.X86.Key.storeTail s = some s' ∧
      s'.mem = storeMem s ∧ s'.zf = some ((roundCount s + 1 - 16) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  obtain hw4 := hok.slotIn 4 (by decide)
  obtain hw5 := hok.slotIn 5 (by decide)
  obtain hr4 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, h, hc⟩ := hw4; exact ⟨r, List.mem_append_right _ h, hc⟩
  obtain hr5 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hw5; exact ⟨r, List.mem_append_right _ h, hc⟩
  obtain hw0 := hw 0 (by decide)
  obtain hw1 := hw 1 (by decide)
  simp only [wordAddr, addr, sboxCfg, roundKeyPtr] at hw4 hw5 hr4 hr5 hw0 hw1
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.storeTail, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load32, State.store32, State.ea, memOp,
      hw4, hw5, hr4, hr5, hw0, hw1, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [mem_setReg, mem_arithFlags, storeMem, roundKeyPtr, roundCount,
    wordAddr, addr, gpr_setReg, gpr_arithFlags, rd_setReg, wr_setReg,
    rd_arithFlags, wr_arithFlags, zf_setReg, zf_arithFlags]
  all_goals try rfl
  all_goals
    intro r hc hd
    simp only [hc, hd, ite_false]

def keyStoreMem (s : State) (k : BitVec 64) : Mem :=
  ((s.mem.writeW (wordAddr (roundKeyPtr s) 0) k).writeW
    (wordAddr (s.gpr .ebp) 4) (roundKeyPtr s + 8)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s + 1)

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : roundKeyPtr s' = roundKeyPtr s + 8
  counter : roundCount s' = BitVec.ofNat 32 (j + 1)
  flag : isa.eval .ne s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (hcount : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s)
    (fit : (roundKeyPtr s).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (wordAddr (roundKeyPtr s) t) 4)
    :
    WP isa (.block Impl.TripleDes.X86.Key.storeRound) s (StorePost c d j s) := by
  rw [Impl.TripleDes.X86.Key.storeRound, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := pc2_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain input : packedInput 56 28 (s.gpr .edi) (s.gpr .esi) = c ++ d := by
    rw [hd, hc]; exact packed28 c d
  rw [input] at lo₁ hi₁
  obtain checks : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp],
      ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true := by decide +kernel
  obtain keep₁ : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s₁.gpr r = s.gpr r :=
    fun r hr => reg₁ r (checks r hr)
  obtain base₁ := keep₁ .ebp (by decide)
  obtain ptr₁ : roundKeyPtr s₁ = roundKeyPtr s := by unfold roundKeyPtr; rw [base₁, mem₁]
  obtain count₁ : roundCount s₁ = roundCount s := by unfold roundCount; rw [base₁, mem₁]
  obtain hok₁ : Ok sboxCfg s₁ := hok.congr base₁ base₁ rd₁ wr₁
  obtain hw₁ : ∀ t < 2, InRegions s₁.wr (wordAddr (roundKeyPtr s₁) t) 4 := by
    rw [wr₁, ptr₁]; exact hw
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, reg₂⟩ := tail_ok s₁ hok₁ hw₁
  obtain regs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s₂.gpr r = s.gpr r := by
    intro r hr
    obtain diffs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (reg₂ r (diffs r hr).1 (diffs r hr).2).trans (keep₁ r hr)
  obtain hm : s₂.mem = keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64) := by
    rw [mem₂, storeMem, ptr₁, count₁, base₁, mem₁, lo₁, hi₁, BitVec.setWidth_eq]
    obtain ha : wordAddr (roundKeyPtr s) 1 = wordAddr (roundKeyPtr s) 0 + 4 := by
      rw [show wordAddr (roundKeyPtr s) 0 = (roundKeyPtr s).setWidth 64 from by
        simp [wordAddr, addr]]
      exact VG.X86.addr_eq (x := roundKeyPtr s) (k := 4) (by omega_arith)
    rw [ha, writeW_pair, packed48]
    rfl
  refine WP.of_runBlock ⟨s₂, run₂, ⟨hm, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, regs⟩⟩
  · unfold roundKeyPtr
    rw [regs .ebp (by decide), hm, keyStoreMem,
      Mem.readW_writeW_sep (fun a h4 h5 => counter_ptr_sep s hok.fit a h5 h4) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold roundCount
    rw [regs .ebp (by decide), hm, keyStoreMem, Mem.readW_writeW_self32, hcount]
    exact (nextRound_values j hj).1
  · change s₂.zf.map (!·) = _
    rw [flag₂, count₁, hcount, Option.map_some]
    exact congrArg some (nextRound_values j hj).2

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Memory` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)

def scheduleRegion (base : BitVec 32) : Region := ⟨addr32 base, 128⟩

theorem pointer_fit (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j : Nat) (hj : j < 16) : (base + BitVec.ofNat 32 (8 * j)).toNat + 8 ≤ 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_arith : 8 * j < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_arith : base.toNat + 8 * j < 2 ^ 32)]
  omega_arith

theorem schedule_contains (base : BitVec 32) (j : Nat) (hj : j < 16) :
    (scheduleRegion base).Contains (addr32 base + BitVec.ofNat 64 (8 * j)) 8 :=
  Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem work_slot (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (k : Nat) (hk : k = 4 ∨ k = 5) :
    (workRegion s).Contains (wordAddr (s.gpr .ebp) k) 4 := by
  change (workRegion s).Contains (addr (s.gpr .ebp) (4 * k)) 4
  rw [addr_eq (by omega_arith)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem keyStore_frame (s : State) (base : BitVec 32) (j : Nat) (hj : j < 16)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (ptr : roundKeyPtr s = base + BitVec.ofNat 32 (8 * j)) (k : BitVec 64) :
    Frame [scheduleRegion base, workRegion s] s.mem (keyStoreMem s k) := by
  obtain hc : (scheduleRegion base).Contains (wordAddr (roundKeyPtr s) 0) 8 := by
    rw [ptr]
    obtain ha : wordAddr (base + BitVec.ofNat 32 (8 * j)) 0 =
        addr32 base + BitVec.ofNat 64 (8 * j) := by
      simpa [wordAddr, addr, addr32] using
        (VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega_arith))
    rw [ha]
    exact schedule_contains base j hj
  exact (((Frame.refl _ _).writeW (by simp) k hc).writeW (by simp) _
    (work_slot s scratchFit 4 (Or.inl rfl))).writeW (by simp) _
    (work_slot s scratchFit 5 (Or.inr rfl))

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Loop` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : BitVec 32) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .esi = (keyPrefix key j).1.setWidth 32
  d : s.gpr .edi = (keyPrefix key j).2.1.setWidth 32
  counter : roundCount s = BitVec.ofNat 32 j
  pointer : roundKeyPtr s = base + BitVec.ofNat 32 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (addr32 base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [scheduleRegion base, workRegion origin] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : BitVec 32) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem keyWordAddr (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j t : Nat) (hj : j < 16) (ht : t < 2) :
    wordAddr (base + BitVec.ofNat 32 (8 * j)) t =
      addr32 base + BitVec.ofNat 64 (8 * j + 4 * t) := by
  change addr (base + BitVec.ofNat 32 (8 * j)) (4 * t) = _
  rw [addr_eq (by have h := pointer_fit base fit j hj; omega_arith)]
  change addr32 (base + BitVec.ofNat 32 (8 * j)) + BitVec.ofNat 64 (4 * t) = _
  rw [VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega_arith), Offset.add_ofNat_add_ofNat]

theorem loopBody_ok (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion origin))
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => isa.eval .ne s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  obtain hoks : Ok sboxCfg s := hok.congr hs.bp hs.bp hs.rd hs.wr
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter hoks)
  intro s₁ h₁
  obtain bp₁ : s₁.gpr .ebp = origin.gpr .ebp := (h₁.keep.reg .ebp (by decide)).trans hs.bp
  obtain sp₁ : s₁.gpr .esp = origin.gpr .esp := (h₁.keep.reg .esp (by decide)).trans hs.sp
  obtain ptr₁ : roundKeyPtr s₁ = roundKeyPtr s := by
    unfold roundKeyPtr
    rw [h₁.keep.reg .ebp (by decide), h₁.keep.mem]
  obtain count₁ : roundCount s₁ = roundCount s := by
    unfold roundCount
    rw [h₁.keep.reg .ebp (by decide), h₁.keep.mem]
  obtain hok₁ : Ok sboxCfg s₁ := hok.congr bp₁ bp₁ (h₁.keep.rd.trans hs.rd) (h₁.keep.wr.trans hs.wr)
  obtain fit₁ : (roundKeyPtr s₁).toNat + 8 ≤ 2 ^ 32 := by
    rw [ptr₁, hs.pointer]; exact pointer_fit base fit j hj
  obtain write₁ : ∀ t < 2, InRegions s₁.wr (wordAddr (roundKeyPtr s₁) t) 4 := by
    intro t ht
    rw [h₁.keep.wr, hs.wr, ptr₁, hs.pointer, keyWordAddr base fit j t hj ht]
    exact hw j hj t ht
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d (count₁.trans hs.counter) hok₁ fit₁ write₁)
  intro s₂ h₂
  let k := (Spec.TripleDes.permute Spec.TripleDes.pc2
    ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
      (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64
  obtain addr₁ : wordAddr (roundKeyPtr s₁) 0 = addr32 base + BitVec.ofNat 64 (8 * j) := by
    rw [ptr₁, hs.pointer, keyWordAddr base fit j 0 hj (by decide)]
    simp only [Nat.mul_zero, Nat.add_zero]
  obtain hm : s₂.mem = ((s.mem.writeW (addr32 base + BitVec.ofNat 64 (8 * j)) k).writeW
      (wordAddr (origin.gpr .ebp) 4) (base + BitVec.ofNat 32 (8 * j) + 8)).writeW
      (wordAddr (origin.gpr .ebp) 5) (BitVec.ofNat 32 j + 1) := by
    rw [h₂.mem, keyStoreMem, addr₁, ptr₁, hs.pointer, count₁, hs.counter, bp₁, h₁.keep.mem]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.keep.rd.trans hs.rd),
    h₂.wr.trans (h₁.keep.wr.trans hs.wr), (h₂.reg .ebp (by decide)).trans bp₁,
    (h₂.reg .esp (by decide)).trans sp₁, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .esi (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .edi (by decide)).trans h₁.d
  · rw [h₂.ptr, ptr₁, hs.pointer]
    change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega_arith)
  · intro i hi hi16
    have hsep (t : Nat) (ht : t = 4 ∨ t = 5) :
        Mem.Sep (addr32 base + BitVec.ofNat 64 (8 * i)) 8 (wordAddr (origin.gpr .ebp) t) 4 :=
      hdis.sep (schedule_contains base i hi16) (work_slot origin hok.fit t ht)
    rw [hm, Mem.readW_writeW_sep (hsep 5 (Or.inr rfl)) (by decide),
      Mem.readW_writeW_sep (hsep 4 (Or.inl rfl)) (by decide), keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep (addr32 base) (by omega_arith) (by omega_arith)
        (by omega_arith)) (by decide), hs.keys i (by omega_arith) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · have fr := keyStore_frame s₁ base j hj fit hok₁.fit (ptr₁.trans hs.pointer) k
    rw [← h₂.mem] at fr
    obtain hreg : workRegion s₁ = workRegion origin := by unfold workRegion; rw [bp₁]
    rw [hreg, h₁.keep.mem] at fr
    exact hs.frame.trans fr

theorem loopStep (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion origin))
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin fit hok hw hdis (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    obtain idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simpa only [idx, ne_eq, not_true_eq_false, decide_false] using h.1
    · simpa only [idx] using h.2
  · right
    obtain idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simpa only [idx, ne_eq, not_false_eq_true, decide_true] using h.1
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      obtain eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : BitVec 32) (s : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg s)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion s))
    (hc : s.gpr .esi = (keyInitial key).1.setWidth 32)
    (hd : s.gpr .edi = (keyInitial key).2.1.setWidth 32)
    (hcount : roundCount s = 0) (hptr : roundKeyPtr s = base) :
    WP isa (.loop (.seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) .ne) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) (c := .ne)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s fit hok hw hdis) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega_arith

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Component` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : BitVec 32) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (addr32 base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  frame : Frame [scheduleRegion base, workRegion s] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hok : Ok sboxCfg s)
    (keyFit : (keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (scheduleFit : (scheduleArg s + BitVec.ofNat 32 (128 * component)).toNat + 128 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s)) :
    WP isa (Impl.TripleDes.X86.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (keyAddr s offset))))
        (scheduleArg s + BitVec.ofNat 32 (128 * component)) s) := by
  rw [Impl.TripleDes.X86.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hok keyFit harg hr)
  intro s₁ h₁
  obtain hok₁ : Ok sboxCfg s₁ := hok.congr h₁.base h₁.base h₁.rd h₁.wr
  obtain writes : ∀ j < 16, ∀ t < 2, InRegions s₁.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    rw [h₁.wr]; exact hw
  obtain work₁ : workRegion s₁ = workRegion s := by unfold workRegion; rw [h₁.base]
  obtain dis₁ : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s₁) := by
    rw [work₁]; exact hdis
  apply WP.mono (loop_ok _ _ s₁ scheduleFit hok₁ writes dis₁ h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.bp.trans h₁.base,
    h₂.sp.trans h₁.sp, ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · have hf := h₂.frame
    rw [work₁] at hf
    exact (h₁.frame.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).trans hf

end VG.Proof.TripleDes.X86.Key

end

end

end


/-! ## `Copy` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

def copyWord (a b : Nat) : List Instr :=
  [.mov .eax (.mem (memOp .edx a)), .store (memOp .edx b) .eax]

theorem copyWord_ok (s : State) (a b : Nat)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) a) 4)
    (hw : InRegions s.wr (addr (s.gpr .edx) b) 4) :
    ∃ s', runBlock isa (copyWord a b) s = some s' ∧
      Keep [.eax] {s with
        mem := (s.mem.writeW (addr (s.gpr .edx) b)
          (s.mem.readW (addr (s.gpr .edx) a) 32))} s' := by
  simp only [addr] at hr hw
  refine ⟨_, by
    simp only [copyWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, hr, hw, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [gpr_setReg, hr, ite_false]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  words : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 4 * i)) 32 =
    s.mem.readW (base + BitVec.ofNat 64 (4 * i)) 32
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 32)
    (fit : (s.gpr .edx).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (s.gpr .edx) (256 + 4 * i)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.copyWords n)) s (CopyPost (addr32 (s.gpr .edx)) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega_arith, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [Impl.TripleDes.X86.Key.copyWords, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega_arith))
    intro s₁ h₁
    obtain base₁ : s₁.gpr .edx = s.gpr .edx := h₁.reg .edx (by decide)
    obtain readable : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edx) (4 * n)) 4 := by
      rw [h₁.rd, h₁.wr, base₁]; exact hr n (by omega_arith)
    obtain writable : InRegions s₁.wr (addr (s₁.gpr .edx) (256 + 4 * n)) 4 := by
      rw [h₁.wr, base₁]; exact hw n (by omega_arith)
    obtain ⟨s₂, run₂, keep₂⟩ := copyWord_ok s₁ (4 * n) (256 + 4 * n) readable writable
    obtain source : s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 =
        s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 := by
      apply h₁.frame.readW (r := ⟨addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n), 4⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (addr32 (s.gpr .edx)) (by omega_arith) (by omega_arith) (by decide)
    obtain mem₂ : s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) := by
      have hm := keep₂.mem
      rw [base₁, addr_eq (by omega_arith : (s.gpr .edx).toNat + (256 + 4 * n) < 2 ^ 32),
        addr_eq (by omega_arith : (s.gpr .edx).toNat + 4 * n < 2 ^ 32)] at hm
      change s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) at hm
      rw [source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)).trans
        (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (addr32 (s.gpr .edx)) (by omega_arith) (by omega_arith)
          (by omega_arith)) (by decide)]
        exact h₁.words i (by omega_arith)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      obtain hc := Offset.contains_base (addr32 (s.gpr .edx) + BitVec.ofNat 64 256)
        (d := 4 * n) (n := 4) (k := 128) (by omega_arith) (by omega_arith)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

structure CopySchedulePost (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (addr32 (scheduleArg s) + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (addr32 (scheduleArg s) + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r
  frame : Frame [⟨addr32 (scheduleArg s) + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copyThird_ok (s : State) (fit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (scheduleArg s) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (scheduleArg s) (256 + 4 * i)) 4) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (CopySchedulePost s) := by
  rw [Impl.TripleDes.X86.Key.copyThird, WP.block_append_iff]
  let s₀ := s.setReg .edx (scheduleArg s)
  obtain he : exec (.mov .edx (.mem (memOp .esp 12))) s = some s₀ := by
    simp only [exec, readSrc, State.load32, State.ea, memOp]
    change (if InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4 then
      some (scheduleArg s) else none).map (s.setReg .edx) = some s₀
    rw [ite_eq_left harg, Option.map_some]
  refine WP.of_runBlock ⟨s₀, by simp only [runBlock_cons, he, runStep_some, runBlock_nil], ?_⟩
  obtain ptr₀ : s₀.gpr .edx = scheduleArg s := gpr_setReg_self _ _ _
  apply WP.mono (copy_ok s₀ 32 (by decide) (by rw [ptr₀]; exact fit)
    (by rw [ptr₀]; exact hr) (by rw [ptr₀]; exact hw))
  intro s₁ h₁
  refine ⟨?_, h₁.rd, h₁.wr, ?_, ?_⟩
  · intro i hi
    let p := addr32 (scheduleArg s)
    obtain h0 := h₁.words (2 * i) (by omega_arith)
    obtain h1 := h₁.words (2 * i + 1) (by omega_arith)
    rw [ptr₀] at h0 h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 64 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64
    rw [← readW_pair, ← readW_pair]
    obtain d0 : 256 + 4 * (2 * i) = 256 + 8 * i := by omega_arith
    obtain d1 : 256 + 4 * (2 * i + 1) = 256 + 8 * i + 4 := by omega_arith
    obtain a0 : 4 * (2 * i) = 8 * i := by omega_arith
    obtain a1 : 4 * (2 * i + 1) = 8 * i + 4 := by omega_arith
    rw [d0, a0] at h0
    rw [d1, a1, ← Offset.add_ofNat_add_ofNat (addr32 (scheduleArg s)) (256 + 8 * i) 4,
      ← Offset.add_ofNat_add_ofNat (addr32 (scheduleArg s)) (8 * i) 4] at h1
    change s₁.mem.readW ((p + BitVec.ofNat 64 (256 + 8 * i)) + 4) 32 =
      s.mem.readW ((p + BitVec.ofNat 64 (8 * i)) + 4) 32 at h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 32 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 32 at h0
    exact congrArg₂ (fun (hi lo : BitVec 32) => hi ++ lo) h1 h0
  · intro r ha hd
    exact (h₁.reg r ha).trans (gpr_setReg_of_ne s _ hd)
  · have hf := h₁.frame
    rw [ptr₀] at hf
    exact hf

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Composition` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.TripleDes (componentKeys componentOffset)

def keyLength (s : State) : Nat := (arg s 1).toNat
abbrev keyR (s : State) : Region := ⟨addr32 (keyArg s), keyLength s⟩
abbrev outputR (s : State) : Region := ⟨addr32 (scheduleArg s), 384⟩
def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (addr32 (scheduleArg origin)) c j) 64 =
    ((componentKeys origin.mem (addr32 (keyArg origin)) (keyLength origin) c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  args : ∀ i < 4, arg s i = arg origin i
  frame : Frame [outputR origin, workRegion origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  ok : Ok sboxCfg s
  reads : ∀ offset, offset + 4 ≤ keyLength s →
    InRegions (s.rd ++ s.wr) (addr32 (keyArg s) + BitVec.ofNat 64 offset) 4
  writes : ∀ offset, offset + 4 ≤ 384 →
    InRegions s.wr (addr32 (scheduleArg s) + BitVec.ofNat 64 offset) 4
  argRead : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4
  argOutput : (⟨argAddr s 0, 16⟩ : Region).Disjoint (outputR s)
  argWork : (⟨argAddr s 0, 16⟩ : Region).Disjoint (workRegion s)
  keyOutput : (keyR s).Disjoint (outputR s)
  keyWork : (keyR s).Disjoint (workRegion s)
  outputWork : (outputR s).Disjoint (workRegion s)
  valid : Spec.TripleDes.validKey (keyLength s)
  keyFit : (keyArg s).toNat + keyLength s ≤ 2 ^ 32
  outputFit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32
  spFit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem Components.keyArg {origin s : State} {done : Nat} (h : Components origin s done) :
    keyArg s = keyArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 1) 32 = _
  rw [← argument_word s 0, h.args 0 (by decide), argument_word origin 0]
  rfl

theorem Components.scheduleArg {origin s : State} {done : Nat} (h : Components origin s done) :
    scheduleArg s = Key.scheduleArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 3) 32 = _
  rw [← argument_word s 2, h.args 2 (by decide), argument_word origin 2]
  rfl

theorem Permissions.congr {s t : State} (hp : Permissions s)
    (args : ∀ i < 4, arg t i = arg s i) (bp : t.gpr .ebp = s.gpr .ebp)
    (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Permissions t := by
  obtain key : keyArg t = keyArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 1) 32 = _
    rw [← argument_word t 0, args 0 (by decide), argument_word s 0]
    rfl
  obtain output : scheduleArg t = scheduleArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 3) 32 = _
    rw [← argument_word t 2, args 2 (by decide), argument_word s 2]
    rfl
  obtain len : keyLength t = keyLength s := by unfold keyLength; rw [args 1 (by decide)]
  obtain work : workRegion t = workRegion s := by unfold workRegion; rw [bp]
  obtain argBase : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  refine ⟨hp.ok.congr bp bp rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro off ho; rw [rd, wr, key]; exact hp.reads off (by rwa [len] at ho)
  · intro off ho; rw [wr, output]; exact hp.writes off ho
  · intro i hi; rw [rd, wr, sp]; exact hp.argRead i hi
  · rw [argBase, outputR, output]; exact hp.argOutput
  · rw [argBase, work]; exact hp.argWork
  · rw [keyR, key, len, outputR, output]; exact hp.keyOutput
  · rw [keyR, key, len, work]; exact hp.keyWork
  · rw [outputR, output, work]; exact hp.outputWork
  · rw [len]; exact hp.valid
  · rw [key, len]; exact hp.keyFit
  · rw [output]; exact hp.outputFit
  · rw [sp]; exact hp.spFit

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (keyLength origin) c = 8 * c) :
    WP isa (Impl.TripleDes.X86.Key.component (8 * c) c) s (Components origin · (c + 1)) := by
  obtain offBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offBound
  obtain hok : Ok sboxCfg s := hp.ok.congr hs.bp hs.bp hs.rd hs.wr
  obtain kfit : (keyArg s).toNat + 8 * c + 8 ≤ 2 ^ 32 := by
    rw [hs.keyArg]; omega_using [hp.keyFit, offBound]
  obtain sfit : (scheduleArg s + BitVec.ofNat 32 (128 * c)).toNat + 128 ≤ 2 ^ 32 := by
    rw [hs.scheduleArg, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc] : 128 * c < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hp.outputFit, hc] : (Key.scheduleArg origin).toNat + 128 * c < 2 ^ 32)]
    omega_using [hp.outputFit, hc]
  obtain args : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead
  obtain reads : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (8 * c + 4 * t)) 4 := by
    intro t ht
    change InRegions (s.rd ++ s.wr) (addr32 (keyArg s + BitVec.ofNat 32 (8 * c + 4 * t))) 4
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound, ht]), hs.rd, hs.wr]
    exact hp.reads _ (by omega_using [offBound, ht])
  obtain writes : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * c)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    intro j hj t ht
    rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
      Offset.add_ofNat_add_ofNat, hs.wr]
    exact hp.writes _ (by omega_using [hc, hj, ht])
  obtain componentSub : Region.Sub
      (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * c))) (outputR origin) := by
    rw [scheduleRegion, hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])]
    exact Offset.sub_base _ (by omega_using [hc])
  obtain work : workRegion s = workRegion origin := by unfold workRegion; rw [hs.bp]
  obtain dis : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * c))).Disjoint (workRegion s) := by
    rw [work]; exact hp.outputWork.sub_left componentSub
  apply WP.mono (component_ok s (8 * c) c hok kfit sfit args reads writes dis)
  intro t ht
  obtain frame : Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (128 * c), 128⟩,
      workRegion origin] s.mem t.mem := by
    have h := ht.frame
    rw [work, scheduleRegion, hs.scheduleArg,
      VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])] at h
    exact h
  obtain targs := VG.Proof.Rc2.X86.arguments_frame 4 ht.frame ht.sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr
      rw [List.mem_cons, List.mem_singleton] at hr
      obtain a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]
      rcases hr with rfl | rfl
      · exact hp.argOutput.sub_right componentSub
      · rw [work]; exact hp.argWork)
  obtain key : Spec.TripleDes.blockAt s.mem (keyAddr s (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (addr32 (Key.keyArg origin) + BitVec.ofNat 64 (8 * c)) := by
    change Spec.TripleDes.blockAt s.mem (addr32 (keyArg s + BitVec.ofNat 32 (8 * c))) = _
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound])]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp.keyOutput.sub_left (Offset.sub_base _ offBound)
    · obtain rfl := List.mem_singleton.mp hr
      exact hp.keyWork.sub_left (Offset.sub_base _ offBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.bp.trans hs.bp, ht.sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (ht.frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      obtain h := ht.keys j hj
      rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
        Offset.add_ofNat_add_ofNat, key] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      obtain keySub : Region.Sub ⟨slot (addr32 (Key.scheduleArg origin)) k j, 8⟩ (outputR origin) :=
        Offset.sub_base _ (by omega_using [before, hc, hj])
      obtain hmem := frame.readW (a := slot (addr32 (Key.scheduleArg origin)) k j) (w := 64)
        (r := ⟨slot (addr32 (Key.scheduleArg origin)) k j, 8⟩) (Region.contains_self _ _) (by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Offset.disjoint _ (by omega_using [before, hj])
              (by omega_using [before, hc, hj]) (by omega_using [hc])
          · obtain rfl := List.mem_singleton.mp hr
            exact hp.outputWork.sub_left keySub) (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨outputR origin, by simp, componentSub⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨workRegion origin, by simp, by rw [work]; exact fun _ h => h⟩

theorem copyThirdStep_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : keyLength origin = 16) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (Components origin · 3) := by
  obtain fit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32 := by rw [hs.scheduleArg]; exact hp.outputFit
  obtain reads : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.X86.addr (scheduleArg s) (4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.rd, hs.wr]
    obtain ⟨r, hr, hc⟩ := hp.writes (4 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain writes : ∀ i < 32, InRegions s.wr (VG.X86.addr (scheduleArg s) (256 + 4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.wr]
    exact hp.writes _ (by omega_using [hi])
  obtain ar : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead 3 (by decide)
  apply WP.mono (copyThird_ok s fit ar reads writes)
  intro t ht
  obtain frame : Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    obtain h := ht.frame; rw [hs.scheduleArg] at h; exact h
  obtain sub : Region.Sub ⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩ (outputR origin) :=
    Offset.sub_base _ (by decide)
  obtain sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide) (by decide)
  obtain targs := VG.Proof.Rc2.X86.arguments_frame 4 frame sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      obtain a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]; exact hp.argOutput.sub_right sub)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide) (by decide)).trans hs.bp, sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      obtain hRepeat : componentKeys origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) 2 =
          componentKeys origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) 0 := by rw [hn]; rfl
      obtain h := ht.keys j hj
      rw [hs.scheduleArg] at h
      change t.mem.readW (addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      obtain first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      obtain hm := frame.readW (a := slot (addr32 (Key.scheduleArg origin)) c j) (w := 64)
        (r := ⟨slot (addr32 (Key.scheduleArg origin)) c j, 8⟩) (Region.contains_self _ _) (by
          intro r hr; obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint _ (by omega_using [before, hj])
            (by omega_using [before, hj]) (by decide)) (by decide)
      exact hm.trans (hs.keys c before j hj)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, sub⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (addr32 (Key.scheduleArg origin)) =
      VG.Proof.TripleDes.expandedMemory origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) := by
  apply Vector.ext
  intro i hi
  obtain fact := index_partition i hi
  obtain keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (addr32 (Key.scheduleArg origin)) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem lengthCompare (x : BitVec 32) : ((x - 16) == 0) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    obtain h' : x = 16 := by bv_omega_using [h]
    rw [h']; rfl
  · intro h
    obtain h' : x = 16 := BitVec.eq_of_toNat_eq h
    rw [h']; rfl

theorem cmpLength_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)] s = some s' ∧
      isa.eval .e s' = some (decide (keyLength s = 16)) ∧ Keep [.eax] s s' := by
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load32, State.ea, memOp, hr, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, ite_true]
    rfl, ?_, ?_⟩
  · change some ((s.mem.readW (wordAddr (s.gpr .esp) 2) 32 - 16) == 0) = _
    rw [← argument_word s 1]
    exact congrArg some (lengthCompare (arg s 1))
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [.eax] s t) : Components origin t n := by
  obtain sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide)
  refine ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide)).trans hs.bp, sp.trans hs.sp, ?_, ?_⟩
  · intro i hi
    unfold arg argAddr
    rw [sp, ht.mem]
    exact hs.args i hi
  · rw [ht.mem]; exact hs.frame

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (lenRead : InRegions (origin.rd ++ origin.wr) (wordAddr (origin.gpr .esp) 2) 4)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.X86.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86.Key.component 0 0)
      (.seq (Impl.TripleDes.X86.Key.component 8 1)
        (.seq (.block [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86.Key.copyThird)
            (Impl.TripleDes.X86.Key.component 16 2)) (.block Impl.TripleDes.X86.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
    (by rw [hs₂.rd, hs₂.wr, hs₂.sp]; exact lenRead)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  obtain hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (Components origin · 3)) ?_
  · intro t ht; exact finish t ht
  obtain flag : isa.eval .e s₃ = some (decide (keyLength origin = 16)) := by
    rw [flag₃, keyLength, hs₂.args 1 (by decide)]
    rfl
  by_cases h16 : keyLength origin = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThirdStep_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Entry` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32)

def preparedKey (s : State) : State := s.setReg .ebp (scratchArg s 4)
abbrev scratchR (s : State) : Region := ⟨addr32 (scratchArg s 4), 512⟩
abbrev savedR (s : State) : Region := ⟨addr32 (scratchArg s 4), 16⟩

structure HeadPre (s : State) : Prop where
  permissions : Permissions (preparedKey s)
  scratchFit : (scratchArg s 4).toNat + 512 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4
  lenRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4
  saveWrites : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) 4
  argsSave : (⟨argAddr s 0, 16⟩ : Region).Disjoint (savedR s)
  keyScratch : (keyR s).Disjoint (scratchR s)
  outputScratch : (outputR s).Disjoint (scratchR s)

structure ExpandPost (original s : State) : Prop where
  result : Spec.TripleDes.scheduleAt s.mem (addr32 (scheduleArg original)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt original.mem (addr32 (keyArg original)) (keyLength original))
  saved : ∀ r ∈ VG.Impl.TripleDes.X86.savedRegs, s.gpr r = original.gpr r
  sp : s.gpr .esp = original.gpr .esp
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  frame : Frame [outputR original, scratchR original] original.mem s.mem

theorem expandKey_ok (s : State) (hp : HeadPre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (ExpandPost s) := by
  rw [Impl.TripleDes.X86.Key.expandKey]
  apply WP.seq
  apply WP.mono (saveWithArg_ok s 4 hp.argRead hp.scratchFit hp.saveWrites)
  intro s₁ h₁
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := h₁.reg .esp (by decide) (by decide)
  obtain ghostSP : (preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  obtain args₁ := VG.Proof.Rc2.X86.arguments_frame 4 h₁.frame sp₁
    (by have h := hp.permissions.spFit; rw [ghostSP] at h; exact h)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.argsSave)
  obtain ghostArgs : ∀ i, arg (preparedKey s) i = arg s i := by
    intro i; unfold arg argAddr; rw [ghostSP]; rfl
  have permissions₁ : Permissions s₁ := hp.permissions.congr
    (fun i hi => (args₁ i hi).trans (ghostArgs i).symm)
    (by rw [preparedKey, gpr_setReg_self]; exact h₁.bp)
    (sp₁.trans ghostSP.symm) h₁.rd h₁.wr
  obtain init : Components s₁ s₁ 0 :=
    ⟨fun _ h => by omega_arith, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  apply body_ok s₁ s₁ permissions₁ init
    (by rw [h₁.rd, h₁.wr, sp₁]; exact hp.lenRead)
  intro s₂ h₂
  obtain bp₂ : s₂.gpr .ebp = scratchArg s 4 := h₂.bp.trans h₁.bp
  have args₂ (i : Nat) (hi : i < 4) : arg s₂ i = arg s i :=
    (h₂.args i hi).trans (args₁ i hi)
  obtain output₁ : outputR s₁ = outputR s := by
    unfold outputR
    change Region.mk (addr32 (s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32)) 384 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  obtain outputArg₁ : scheduleArg s₁ = scheduleArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  obtain keyArg₁ : keyArg s₁ = keyArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 1) 32 = _
    rw [← argument_word s₁ 0, args₁ 0 (by decide), argument_word s 0]; rfl
  obtain len₁ : keyLength s₁ = keyLength s := by unfold keyLength; rw [args₁ 1 (by decide)]
  have scratchSub (i : Nat) (hi : i < 4) :
      Region.Sub ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩ (scratchR s) :=
    Offset.sub_base _ (by omega_using [hi])
  obtain saved₂ : Saved s s₂ := by
    intro i hi
    rw [bp₂]
    obtain hm := h₂.frame.readW (a := addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) (w := 32)
      (r := ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩)
      (Region.contains_self _ _) (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [output₁]; exact (hp.outputScratch.sub_right (scratchSub i hi)).symm
        · obtain rfl := List.mem_singleton.mp hr
          obtain sep := savedSlot_work_disjoint s₁ i hi
          rw [h₁.bp] at sep
          exact sep) (by decide)
    obtain saved₁ := h₁.saved i hi
    rw [h₁.bp] at saved₁
    exact hm.trans saved₁
  obtain reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr)
      (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, bp₂]
    obtain ⟨r, hr, hc⟩ := hp.saveWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (blockRestore_ok s s₂ saved₂ (by rw [bp₂]; exact hp.scratchFit) reads₂)
  intro s₃ h₃
  obtain initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (addr32 (keyArg s)) (keyLength s)
    h₁.frame (by
      have fit := permissions₁.keyFit
      rw [keyArg₁, len₁] at fit
      obtain bound := (keyArg s).isLt
      omega_using [fit, bound]) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact hp.keyScratch.sub_right (Region.sub_prefix (by decide)))
  have result := h₂.schedule
  rw [outputArg₁, keyArg₁, len₁] at result
  rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (addr32 (keyArg s)) (keyLength s)
    (by have valid := permissions₁.valid; rw [len₁] at valid; exact valid), initialBytes] at result
  refine ⟨?_, h₃.saved, h₃.sp.trans (h₂.sp.trans sp₁), h₃.rd.trans (h₂.rd.trans h₁.rd),
    h₃.wr.trans (h₂.wr.trans h₁.wr), ?_⟩
  · rw [h₃.mem]; exact result
  · rw [h₃.mem]
    obtain first : Frame [outputR s, scratchR s] s.mem s₁.mem := h₁.frame.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨scratchR s, by simp, Region.sub_prefix (by decide)⟩)
    exact first.trans (h₂.frame.sub (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [output₁]; exact ⟨outputR s, by simp, fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        refine ⟨scratchR s, by simp, ?_⟩
        rw [workRegion, h₁.bp]
        exact Offset.sub_base _ (by decide)))

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), (arg s 1).toNat⟩
    let output : Region := ⟨addr32 (arg s 2), 384⟩
    let scratch : Region := ⟨addr32 (arg s 3), 512⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧
      key.Disjoint scratch ∧ output.Disjoint scratch ∧ args.Disjoint output ∧
      args.Disjoint scratch ∧ ret.Disjoint output ∧ ret.Disjoint scratch ∧
      Spec.TripleDes.validKey (arg s 1).toNat ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 512 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.scheduleAt s'.mem (addr32 (arg s 2)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Pre` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32 argContainsCount)

theorem key_argument (s : State) : keyArg s = arg s 0 := (argument_word s 0).symm
 theorem output_argument (s : State) : scheduleArg s = arg s 2 := (argument_word s 2).symm
 theorem scratch_argument (s : State) : scratchArg s 4 = arg s 3 := (argument_word s 3).symm

theorem headPre_of_contract (s : State) (hs : contract.pre s) : HeadPre s := by
  obtain ⟨rd, wr, keyOut, keyScratch, outScratch, argsOut, argsScratch, _, _,
    valid, keyFit, outputFit, scratchFit, spFit⟩ := hs
  obtain bp : (preparedKey s).gpr .ebp = arg s 3 := by rw [preparedKey, gpr_setReg_self, scratch_argument]
  obtain sp : (preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have args (i : Nat) : arg (preparedKey s) i = arg s i := by unfold arg argAddr; rw [sp]; rfl
  obtain key : keyArg (preparedKey s) = arg s 0 := by rw [key_argument, args]
  obtain output : scheduleArg (preparedKey s) = arg s 2 := by rw [output_argument, args]
  obtain len : keyLength (preparedKey s) = (arg s 1).toNat := by unfold keyLength; rw [args]
  obtain argBase : argAddr (preparedKey s) 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  obtain workSub : Region.Sub (workRegion (preparedKey s)) ⟨addr32 (arg s 3), 512⟩ := by
    rw [workRegion, bp]; exact Offset.sub_base _ (by decide)
  obtain saveSub : Region.Sub (savedR s) ⟨addr32 (arg s 3), 512⟩ := by
    rw [savedR, scratch_argument]; exact Region.sub_prefix (by decide)
  obtain contains : ∀ i, 1 ≤ i → i ≤ 4 → (⟨argAddr s 0, 16⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [wordAddr, addr_eq (by omega_using [spFit, hhi])]
    obtain h := argContainsCount s 4 spFit (i - 1) (by omega_using [hlo, hhi])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hlo]] at h
    exact h
  obtain readArg : ∀ i, 1 ≤ i → i ≤ 4 → InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [rd, wr]
    exact ⟨⟨argAddr s 0, 16⟩, by simp, contains i hlo hhi⟩
  obtain slots : ∀ i < 128, InRegions (preparedKey s).wr (wordAddr ((preparedKey s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega_using [scratchFit, hi])]
    change InRegions s.wr _ 4
    rw [wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain ok : Ok sboxCfg (preparedKey s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega_arith
    · change ((preparedKey s).gpr .ebp).toNat + 512 ≤ 2 ^ 32; rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega_arith
  refine ⟨?_, ?_, readArg 4 (by decide) (by decide), readArg 2 (by decide) (by decide), ?_,
    argsScratch.sub_right saveSub, ?_, ?_⟩
  · refine ⟨ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro off ho
      rw [len] at ho
      rw [key]
      change InRegions (s.rd ++ s.wr) _ 4
      rw [rd, wr]
      exact ⟨⟨addr32 (arg s 0), (arg s 1).toNat⟩, by simp,
        Offset.contains_base _ ho (by omega_using [ho, keyFit])⟩
    · intro off ho
      rw [output]
      change InRegions s.wr _ 4
      rw [wr]
      exact ⟨⟨addr32 (arg s 2), 384⟩, by simp, Offset.contains_base _ ho (by omega_using [ho])⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      change InRegions (s.rd ++ s.wr) (wordAddr ((preparedKey s).gpr .esp) i) 4
      rw [sp]
      rcases hi with rfl | rfl
      · exact readArg 1 (by decide) (by decide)
      · exact readArg 3 (by decide) (by decide)
    · rw [argBase, outputR, output]; exact argsOut
    · rw [argBase]; exact argsScratch.sub_right workSub
    · rw [keyR, key, len, outputR, output]; exact keyOut
    · rw [keyR, key, len]; exact keyScratch.sub_right workSub
    · rw [outputR, output]; exact outScratch.sub_right workSub
    · rw [len]; exact valid
    · rw [key, len]; exact keyFit
    · rw [output]; exact outputFit
    · rw [sp]; exact spFit
  · rw [scratch_argument]; exact scratchFit
  · intro i hi
    rw [scratch_argument, wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [keyR, key_argument, keyLength, scratchR, scratch_argument]; exact keyScratch
  · rw [outputR, output_argument, scratchR, scratch_argument]; exact outScratch

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Correct` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (fun s' => abiPreserved s s' ∧ contract.post s s') := by
  obtain hp := headPre_of_contract s hs
  obtain ⟨_, _, _, _, _, _, _, retOutput, retScratch, _⟩ := hs
  apply WP.mono (expandKey_ok s hp)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    obtain regs : ∀ r ∈ calleeSaved, r ∈ Impl.TripleDes.X86.savedRegs ∨ r = .esp := by decide
    rcases regs r hr with saved | rfl
    · exact hpost.saved r saved
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [outputR, output_argument]; exact retOutput
    · obtain rfl := List.mem_singleton.mp hr
      rw [scratchR, scratch_argument]; exact retScratch
  · have result := hpost.result
    rw [output_argument, key_argument, keyLength] at result
    exact result

end VG.Proof.TripleDes.X86.Key

end

/-! ## `ConstantTime` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem keyTaint_wf {s : State} (hs : contract.pre s) : VG.X86.Taint.Wf keyTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, argsData, argsScratch, retData, retScratch, _, _, dataFit, scratchFit, spFit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) retScratch argsScratch
  · intro p hp
    simp only [keyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]

theorem keyTaint_agree {s t : State} (hs : contract.pre s)
    (ht : contract.pre t) (hp : contract.pub s t) :
    VG.X86.Taint.Agree keyTaint s t := by
  obtain ⟨sp, args⟩ := hp
  obtain fit : ∀ s, contract.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, keyTaint_wf hs,
    keyTaint_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [keyTaint] at hk
    rw [show VG.X86.Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_arith))

end VG.Proof.TripleDes.X86.Key

end

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 16 else
    if a = 0x400d then 0x20 else if a = 0x4011 then 0x30 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem verified : Verified target Impl.TripleDes.X86.Key.expandKey
    (Proof.TripleDes.expandKeyScratchContract abi) := by
  refine Verified.of_correct expand_correct
    (expandKey_constantTime _ _ (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)) ?_
  sig_implies [Proof.TripleDes.expandKeyScratchContract, Proof.TripleDes.expandKeyScratchSig, Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argSlots, argVal,
    argBytes, addr32, contract]
    [satState, arg, argAddr, Mem.readW, Mem.read] using satState

end VG.Proof.TripleDes.X86.Key

end

end


/-!
# Triple DES key expansion and ECB on x86, with their working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and copies their three argument slots,
and zeroes it after the code (`Verified.stackScratchWiped`), since it may
hold the key schedule and the data: 532 bytes for key expansion (512 of
working space) and 1044 for ECB (1024). The copies are read only where the
postconditions read the buffers (`Proof/TripleDes/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86

open VG VG.X86

/-- A state satisfying `vg_triple_des_expand_key`'s precondition: a 16-byte
key at `0x1000` and the schedule at `0x2000`, as stack arguments at
`0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 384⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.TripleDes.expandKeyContract X86.abi 532).pre s := by
  implies_sat [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, Spec.TripleDes.validKey, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no blocks at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem ecbFrameSat_pre (d : Spec.TripleDes.Direction) :
    ∃ s, (Spec.TripleDes.ecbContract X86.abi d 1060).pre s := by
  implies_sat [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [ecbFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using ecbFrameSat

theorem expandKey_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey)
      (Spec.TripleDes.expandKeyContract X86.abi 532) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.TripleDes.expandKeyPre X86.abi.ptrBits)
    (post := Spec.TripleDes.expandKeyPost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 532) Key.verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.TripleDes.expandKeyPre_local _) (Proof.TripleDes.expandKeyPost_local _)
    (Proof.TripleDes.expandKeyPostOut_local _) expandKeyFrameSat_pre

theorem ecb_framed (d : Spec.TripleDes.Direction) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 (Impl.TripleDes.X86.Ecb.ecb d))
      (Spec.TripleDes.ecbContract X86.abi d 1060) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.ecbSig) (nm := "scratch") (e := .u64)
    (n := 128) (post := Spec.TripleDes.ecbPost d X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 1044) (Ecb.ecb_verified d) (by decide) (by cases d <;> lit_decide)
    (by cases d <;> lit_decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.ecbPost_local _ d) (Proof.TripleDes.ecbPostOut_local _ d) (ecbFrameSat_pre d)

end VG.Proof.TripleDes.X86
