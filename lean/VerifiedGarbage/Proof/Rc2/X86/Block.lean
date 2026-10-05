import VerifiedGarbage.Impl.Rc2.X86.Block
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Lit`. -/
section

namespace VG.Impl.Rc2.X86

materialize_value keyLookup

materialize_code encryptBlock
materialize_code decryptBlock

end VG.Impl.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.RoundSteps`. -/
section

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

theorem addr_eq_def (x : BitVec 32) : addr32 x = x.setWidth 64 := rfl

theorem keyStep_ok (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32)
    (i : Nat) (hi : i < 64)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i)) 1)
    (hhi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1)) 1) :
    ∃ s', runBlock isa (keyStep i) s = some s' ∧
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat = i then
          ((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
            (s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧
      Keep [.ebx, .ecx, .esi, .edx] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, keyStep, selectMask, loadKey, rr, memOp,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, VG.X86.readSrc, State.load8, State.ea, ← VG.Proof.Rc2.X86.addr_eq_def, addr_add (by omega : (s.gpr .edi).toNat + 2 * i < 2 ^ 32),
      addr_add (by omega : (s.gpr .edi).toNat + (2 * i + 1) < 2 ^ 32),
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags,
      mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
      wr_setReg, wr_arithFlags, wr_setFlags, hlo, hhi]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx, index_imm i (by omega)]
    rw [mask_neg]
    change s.gpr .ebx |||
      (((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i))).setWidth 32 |||
        ((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1))).setWidth 32).rotateRight 24) &&&
        (0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31))) = _
    rw [Word32.selectMask_eq, Word32.joinBytes]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.and_allOnes]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem keySteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 64)
    (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1) :
    WP isa (.block (is.flatMap keyStep)) s (fun s' =>
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat ∈ is then
          ((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * x.toNat))).setWidth 16 |||
            (s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * x.toNat + 1))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧ Keep [.ebx, .ecx, .esi, .edx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.keyStep_ok s x hx i bound fit
      (readable (2 * i) (by omega)) (readable (2 * i + 1) (by omega))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .eax (by decide)).trans hx
    have ptr₁ := keep₁.reg .edi (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 j) 1 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact readable
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁ (by rw [ptr₁]; exact fit) read₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, keep₁.mem, ptr₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]

theorem maskIndex (x : BitVec 32) :
    x &&& 63 = (x.setWidth 6).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 6 - 1) = x.toNat % 64 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem keyStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .eax (.imm 63), imm .ebx 0] s = some s' ∧
      s'.gpr .eax = ((s.gpr .eax).setWidth 6).setWidth 32 ∧ s'.gpr .ebx = 0 ∧
      Keep [.eax, .ebx, .ecx, .esi, .edx] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86.readSrc,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact VG.Proof.Rc2.X86.maskIndex _
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

theorem keyLookup_ok (s : State)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .eax = ((Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .edi))).getD
        ((s.gpr .eax).setWidth 6).toNat 0).setWidth 32 ∧
      Keep [.eax, .ebx, .ecx, .esi, .edx] s s') := by
  rw [keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := VG.Proof.Rc2.X86.keyStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ := keep₁.reg .edi (by decide)
  have read₁ : ∀ i < 128,
      InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]
    exact readable
  have inputByte : s₁.gpr .eax = (((s.gpr .eax).setWidth 6).setWidth 8).setWidth 32 := by
    rw [input₁]; simp
  apply WP.mono (VG.Proof.Rc2.X86.keySteps_ok (List.range 64) (fun i hi => List.mem_range.mp hi)
    s₁ (((s.gpr .eax).setWidth 6).setWidth 8) inputByte (by rw [ptr₁]; exact fit) read₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .ebx = ((Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .edi))).getD
      ((s.gpr .eax).setWidth 6).toNat 0).setWidth 32 := by
    rw [h₂.1, zero₁, keep₁.mem, ptr₁]
    simp only [List.mem_range, BitVec.toNat_setWidth]
    have bound := ((s.gpr .eax).setWidth 6).isLt
    simp only [BitVec.toNat_setWidth] at bound
    rw [Nat.mod_eq_of_lt (show (s.gpr .eax).toNat % 64 < 256 by omega),
      ite_eq_left bound, VG.Proof.Rc2.X86.scheduleAt_getD _ _ _ bound]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .eax (s₂.gpr .ebx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86.readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.eax, .ebx, .ecx, .esi, .edx] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _


end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .esi ∧ wordReg i ≠ .edi ∧ wordReg i ≠ .ebp ∧ wordReg i ≠ .esp := by
  have fact : ∀ j < 4, wordReg j ≠ .esi ∧ wordReg j ≠ .edi ∧ wordReg j ≠ .ebp ∧ wordReg j ≠ .esp := by decide
  simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_injective : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j ↔ i = j := by decide

theorem selectWord (a b c : BitVec 32) :
    ((b ^^^ c) &&& a) ^^^ c = (a &&& b) + (~~~a &&& c) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
    cases a.getLsbD j <;> cases b.getLsbD j <;> cases c.getLsbD j <;> rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hj, decide_true, Bool.true_and, BitVec.getLsbD_zero]
    cases a.getLsbD j <;> cases b.getLsbD j <;> cases c.getLsbD j <;> rfl

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .esi)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ Keep [r, .esi] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 16 - n ∧ 16 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [hleft, hright, and_self, rotate16, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, VG.X86.readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, Ne.symm hr, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact Word32.rotateWord x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem mixSelect_ok (s : State) (i : Nat) :
    ∃ s', runBlock isa (mixSelect i) s = some s' ∧
      s'.gpr .esi = (s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
        (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))) ∧ Keep [.esi] s s' := by
  have h1 := (VG.Proof.Rc2.X86.wordReg_separate (i + 1)).1
  have h3 := (VG.Proof.Rc2.X86.wordReg_separate (i + 3)).1
  refine ⟨_, by
    simp only [mixSelect, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, VG.X86.readSrc, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, h1, h3, ite_false, ite_true]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]; exact VG.Proof.Rc2.X86.selectWord _ _ _
  · constructor
    · intro r hr
      have hn : r ≠ .esi := by simpa only [List.mem_singleton] using hr
      simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
    · rfl
    · rfl
    · rfl

theorem mixKey_ok (s : State) (j : Nat) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (VG.X86.argAddr s 0) 4)
    (fit : (VG.X86.arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128, InRegions (s.rd ++ s.wr) (addr32 (VG.X86.arg s 0) + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (mixKey j) s = some s' ∧
      s'.gpr .esi = ((Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))).getD j 0).setWidth 32 ∧
      Keep [.esi, .edi] s s' := by
  have lo := readable (2 * j) (by omega)
  have hi := readable (2 * j + 1) (by omega)
  have loAddr := addr_add (by omega : (arg s 0).toNat + 2 * j < 2 ^ 32)
  have hiAddr := addr_add (by omega : (arg s 0).toNat + (2 * j + 1) < 2 ^ 32)
  simp only [VG.X86.arg, VG.X86.argAddr, Nat.mul_zero, Nat.add_zero, ← VG.Proof.Rc2.X86.addr_eq_def] at stackRead lo hi loAddr hiAddr ⊢
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, mixKey, memOp, State.ea, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, execShift, VG.X86.readSrc, State.load32, State.load8,
      gpr_setReg, gpr_setFlags, mem_setReg,
      rd_setReg, wr_setReg,
      stackRead, Option.map_some, Option.bind_some,
      ← VG.Proof.Rc2.X86.addr_eq_def, loAddr, hiAddr, lo, hi]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self, Word32.joinBytes, VG.Proof.Rc2.X86.scheduleAt_getD _ _ _ hj]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem adjust_ok (sub : Bool) (s : State) (r : Reg) :
    ∃ s', runBlock isa (adjust sub r) s = some s' ∧
      s'.gpr r = (if sub then s.gpr r - s.gpr .esi else s.gpr r + s.gpr .esi) ∧
      Keep [r] s s' := by
  cases sub <;>
    refine ⟨_, by simp only [adjust, Bool.false_eq_true, ite_false, ite_true,
      runBlock_cons, exec, execAlu, VG.X86.readSrc, Option.bind_some, runStep_some, runBlock_nil]; rfl, ?_⟩
  all_goals
    constructor
    · exact gpr_setReg_self _ _ _
    · constructor
      · intro r' hr
        have hn : r' ≠ r := by simpa only [List.mem_singleton] using hr
        simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
      · rfl
      · rfl
      · rfl

end VG.Proof.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.BlockArgs`. -/
section

section

/-! # RC2 words in scratch memory and temporary registers -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

def wordBase (s : State) : Addr := addr32 (s.gpr .ebp) + 64

def MemWords (m : Mem) (p : Addr) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = (v.getD i 0).setWidth 32

def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 32

def temps : List Reg := [.esi, .edi]
def wordRegs : List Reg := [.eax, .ebx, .ecx, .edx]
def roundWrites : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi]

theorem wordReg_mem (i : Nat) : wordReg i ∈ VG.Proof.Rc2.X86.wordRegs := by
  have fact : ∀ i < 4, wordReg i ∈ VG.Proof.Rc2.X86.wordRegs := by decide
  simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ VG.Proof.Rc2.X86.temps := by
  exact fun h => by
    have hs := VG.Proof.Rc2.X86.wordReg_separate i
    simp only [VG.Proof.Rc2.X86.temps, List.mem_cons, List.not_mem_nil, or_false] at h
    exact h.elim hs.1 hs.2.1

theorem wordOff_eq (s : State) (i : Nat) (hi : i < 4) :
    addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i) = VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i) := by
  simp only [wordOff, Nat.mod_eq_of_lt hi, VG.Proof.Rc2.X86.wordBase, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by simp [Vector.getD, hi]

theorem MemWords.update {m : Mem} {p : Addr} {v : Spec.Rc2.State}
    (h : VG.Proof.Rc2.X86.MemWords m p v) (i : Nat) (hi : i < 4) (x : BitVec 16) :
    VG.Proof.Rc2.X86.MemWords (m.writeW (p + BitVec.ofNat 64 (4 * i)) (x.setWidth 32)) p (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j
    rw [Mem.readW_writeW_self32]
    simp [Vector.getD, hi]
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide), h j hj]
    rw [VG.Proof.Rc2.X86.vector_getD _ j hj, VG.Proof.Rc2.X86.vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.at_mod {s : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.X86.Words s v) (i : Nat) :
    s.gpr (wordReg i) = (v.getD (i % 4) 0).setWidth 32 := by
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.X86.Words s v)
    (keep : Keep VG.Proof.Rc2.X86.temps s s') : VG.Proof.Rc2.X86.Words s' v := by
  intro i hi
  exact (keep.reg _ (VG.Proof.Rc2.X86.wordReg_not_temps i)).trans (h i hi)

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.X86.Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 32)
    (keep : Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s s') : VG.Proof.Rc2.X86.Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j; simpa [Vector.getD, hi] using out
  · rw [keep.reg _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((VG.Proof.Rc2.X86.wordReg_injective j hj i hi).mp e), VG.Proof.Rc2.X86.wordReg_not_temps j⟩), h j hj]
    rw [VG.Proof.Rc2.X86.vector_getD _ j hj, VG.Proof.Rc2.X86.vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

def wordIndex : Reg → Nat
  | .eax => 0 | .ebx => 1 | .ecx => 2 | .edx => 3 | _ => 0

theorem wordIndex_reg : ∀ i < 4, VG.Proof.Rc2.X86.wordIndex (wordReg i) = i := by decide

theorem loadWords_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (fit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block loadWords) s (fun s' => VG.Proof.Rc2.X86.Words s' v ∧ Keep VG.Proof.Rc2.X86.wordRegs s s') := by
  let regs := fun i => wordReg (i - 16)
  let values := fun r => (v.getD (VG.Proof.Rc2.X86.wordIndex r) 0).setWidth 32
  have code : loadWords = restoreCode .ebp regs [16, 17, 18, 19] := rfl
  have bounds : ∀ i ∈ [16, 17, 18, 19], 16 ≤ i ∧ i < 20 := by decide
  have addr (i : Nat) (hi : i ∈ [16, 17, 18, 19]) :
      addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i) = VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * (i - 16)) := by
    have h := bounds i hi
    unfold VG.Proof.Rc2.X86.wordBase
    rw [BitVec.add_assoc, show (64 : Addr) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => addr32 (s.gpr .ebp) + BitVec.ofNat 64 n) (by omega)
  rw [code]
  apply WP.mono (restoreCode_ok s .ebp regs [16, 17, 18, 19] values fit (by decide) (by decide)
    (fun i hi => by rw [addr i hi]; exact readable _ (by have := bounds i hi; omega))
    (fun i hi => by
      have h := bounds i hi
      rw [addr i hi, hv _ (by omega)]
      dsimp only [values, regs]
      rw [VG.Proof.Rc2.X86.wordIndex_reg _ (by omega)]))
  intro s' h
  constructor
  · intro i hi
    have mem : wordReg i ∈ [16, 17, 18, 19].map regs := VG.Proof.Rc2.X86.wordReg_mem i
    have out := h.1 (wordReg i) mem
    dsimp only [values] at out
    rw [VG.Proof.Rc2.X86.wordIndex_reg i hi] at out
    exact out
  · exact h.2

end VG.Proof.Rc2.X86

end

section

section

/-! # RC2 MIX arithmetic, including its inverse -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem mask16_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = ((s.gpr r).setWidth 16).setWidth 32 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, VG.X86.readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]; exact Word32.maskWord _
  · exact ⟨fun r' hr => (gpr_setReg_of_ne _ _ (by simpa using hr)), rfl, rfl, rfl⟩

theorem argAddr_keep {s s' : State} {rs : List Reg} (h : Keep rs s s')
    (sp : .esp ∉ rs) (i : Nat) : VG.X86.argAddr s' i = VG.X86.argAddr s i := by
  unfold VG.X86.argAddr; rw [h.reg .esp sp]

def mixValue (sub : Bool) (x c k : BitVec 32) : BitVec 16 :=
  (if sub then x - c - k else x + c + k).setWidth 16

theorem mixArithmetic_ok (sub : Bool) (s : State) (i j : Nat) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (VG.X86.argAddr s 0) 4)
    (fit : (VG.X86.arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (VG.X86.arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixArithmetic sub j i)) s (fun s' =>
      s'.gpr (wordReg i) = (VG.Proof.Rc2.X86.mixValue sub (s.gpr (wordReg i))
        ((s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
          (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))))
        (((Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))).getD j 0).setWidth 32)).setWidth 32 ∧
      Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s s') := by
  rw [mixArithmetic, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.mixSelect_ok s i
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := VG.Proof.Rc2.X86.adjust_ok sub s₁ (wordReg i)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  have k₁ : Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s s₁ := keep₁.weaken (by simp [VG.Proof.Rc2.X86.temps])
  have k₂ : Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s₁ s₂ := keep₂.weaken (by simp)
  have keep := k₁.trans k₂
  have sp : .esp ∉ wordReg i :: VG.Proof.Rc2.X86.temps := by
    simp only [List.mem_cons, VG.Proof.Rc2.X86.temps, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm (VG.Proof.Rc2.X86.wordReg_separate i).2.2.2, by decide, by decide⟩
  have args := arg_keep keep sp 0
  have stack := VG.Proof.Rc2.X86.argAddr_keep keep sp 0
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.X86.mixKey_ok s₂ j hj
    (by rw [keep.rd, keep.wr, stack]; exact stackRead)
    (by rw [args]; exact fit)
    (by rw [keep.rd, keep.wr, args]; exact readable)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := VG.Proof.Rc2.X86.adjust_ok sub s₃ (wordReg i)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  obtain ⟨s₅, run₅, out₅, keep₅⟩ := VG.Proof.Rc2.X86.mask16_ok s₄ (wordReg i)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  constructor
  · rw [out₅, out₄, keep₃.reg _ (VG.Proof.Rc2.X86.wordReg_not_temps i), out₂,
      keep₁.reg _ (by simp only [List.mem_singleton]; exact (VG.Proof.Rc2.X86.wordReg_separate i).1),
      out₁, out₃, keep.mem, args]
    cases sub <;> simp only [VG.Proof.Rc2.X86.mixValue, Bool.false_eq_true, ite_true, ite_false]
  · exact ((keep.trans (keep₃.weaken (by simp [VG.Proof.Rc2.X86.temps]))).trans
      (keep₄.weaken (by simp))).trans (keep₅.weaken (by simp))

theorem mixValue_add (x k a b c : BitVec 16) :
    VG.Proof.Rc2.X86.mixValue false (x.setWidth 32)
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))
      (k.setWidth 32) = x + k + (a &&& b) + (~~~a &&& c) := by
  simp only [VG.Proof.Rc2.X86.mixValue, Bool.false_eq_true, ite_false, BitVec.setWidth_add _ _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_and, BitVec.setWidth_not (show 16 ≤ 32 by decide), BitVec.setWidth_setWidth_of_le _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_eq]
  ac_rfl

theorem mixValue_sub (x k a b c : BitVec 16) :
    VG.Proof.Rc2.X86.mixValue true (x.setWidth 32)
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))
      (k.setWidth 32) = x - k - (a &&& b) - (~~~a &&& c) := by
  simp only [VG.Proof.Rc2.X86.mixValue, ite_true, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_neg_of_le (show 16 ≤ 32 by decide), BitVec.setWidth_and, BitVec.setWidth_not (show 16 ≤ 32 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 16 ≤ 32 by decide), BitVec.setWidth_eq]
  simp only [BitVec.neg_add, BitVec.sub_eq_add_neg]
  ac_rfl

end VG.Proof.Rc2.X86

end

section

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def mixResult (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : BitVec 16 :=
  let x := v.getD i 0
  let a := v.getD ((i + 3) % 4) 0
  let b := v.getD ((i + 2) % 4) 0
  let c := v.getD ((i + 1) % 4) 0
  match d with
  | .encrypt => (x + k.getD j 0 + (a &&& b) + (~~~a &&& c)).rotateLeft (Spec.Rc2.rotation i)
  | .decrypt => x.rotateRight (Spec.Rc2.rotation i) - k.getD j 0 - (a &&& b) - (~~~a &&& c)

theorem mixCore_encrypt_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (VG.X86.argAddr s 0) 4)
    (fit : (VG.X86.arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (VG.X86.arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore .encrypt j i)) s (fun s' =>
      s'.gpr (wordReg i) = (VG.Proof.Rc2.X86.mixResult .encrypt (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s s') := by
  rw [mixCore, WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.mixArithmetic_ok false s i j hj stackRead fit readable)
  intro s₁ h₁
  have out := h₁.1
  rw [hv i hi, hv.at_mod (i + 3), hv.at_mod (i + 2), hv.at_mod (i + 1), VG.Proof.Rc2.X86.mixValue_add] at out
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := VG.Proof.Rc2.X86.rotate16_ok s₁ (wordReg i) (VG.Proof.Rc2.X86.wordReg_separate i).1 _ out
    (Spec.Rc2.rotation i) (VG.Proof.Rc2.X86.rotation_bounds i).1 (VG.Proof.Rc2.X86.rotation_bounds i).2
  refine WP.of_runBlock ⟨s₂, run₂, out₂, h₁.2.trans (keep₂.weaken ?_)⟩
  simp [VG.Proof.Rc2.X86.temps]

theorem neighbor_ne : ∀ i < 4, ∀ n < 4, 1 ≤ n → wordReg (i + n) ≠ wordReg i := by decide

theorem mixCore_decrypt_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (VG.X86.argAddr s 0) 4)
    (fit : (VG.X86.arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (VG.X86.arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore .decrypt j i)) s (fun s' =>
      s'.gpr (wordReg i) = (VG.Proof.Rc2.X86.mixResult .decrypt (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s s') := by
  rw [mixCore, WP.block_append_iff]
  have bounds := VG.Proof.Rc2.X86.rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.rotate16_ok s (wordReg i) (VG.Proof.Rc2.X86.wordReg_separate i).1 _ (hv i hi)
    (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [Word32.rotateLeft_reverse _ _ bounds.1 bounds.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have sp : .esp ∉ [wordReg i, .esi] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm (VG.Proof.Rc2.X86.wordReg_separate i).2.2.2, by decide⟩
  have args := arg_keep keep₁ sp 0
  have stack := VG.Proof.Rc2.X86.argAddr_keep keep₁ sp 0
  apply WP.mono (VG.Proof.Rc2.X86.mixArithmetic_ok true s₁ i j hj
    (by rw [keep₁.rd, keep₁.wr, stack]; exact stackRead)
    (by rw [args]; exact fit)
    (by rw [keep₁.rd, keep₁.wr, args]; exact readable))
  intro s₂ h₂
  constructor
  · have nbr (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 3) :
        s₁.gpr (wordReg (i + n)) = (v.getD ((i + n) % 4) 0).setWidth 32 := by
      rw [keep₁.reg _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨VG.Proof.Rc2.X86.neighbor_ne i hi n (by omega) hn, (VG.Proof.Rc2.X86.wordReg_separate _).1⟩)]
      exact hv.at_mod _
    rw [h₂.1, out₁, nbr 3 (by decide) (by decide), nbr 2 (by decide) (by decide),
      nbr 1 (by decide) (by decide), keep₁.mem, args, VG.Proof.Rc2.X86.mixValue_sub]
    rfl
  · exact (keep₁.weaken (by simp [VG.Proof.Rc2.X86.temps])).trans h₂.2

theorem mixCore_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (VG.X86.argAddr s 0) 4)
    (fit : (VG.X86.arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (VG.X86.arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore d j i)) s (fun s' =>
      s'.gpr (wordReg i) = (VG.Proof.Rc2.X86.mixResult d (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s s') := by
  cases d
  · exact VG.Proof.Rc2.X86.mixCore_encrypt_ok s v hv i j hi hj stackRead fit readable
  · exact VG.Proof.Rc2.X86.mixCore_decrypt_ok s v hv i j hi hj stackRead fit readable

end VG.Proof.Rc2.X86

end

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

structure RoundEnv (s : State) : Prop where
  scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32
  keyFit : (VG.X86.arg s 0).toNat + 128 ≤ 2 ^ 32
  stackRead : InRegions (s.rd ++ s.wr) (VG.X86.argAddr s 0) 4
  keyRead : ∀ i < 128, InRegions (s.rd ++ s.wr) (addr32 (VG.X86.arg s 0) + BitVec.ofNat 64 i) 1
  wordWrite : ∀ i < 4, InRegions s.wr (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4
  keySep : (Region.mk (addr32 (VG.X86.arg s 0)) 128).Disjoint ⟨VG.Proof.Rc2.X86.wordBase s, 16⟩
  argSep : (Region.mk (VG.X86.argAddr s 0) 4).Disjoint ⟨VG.Proof.Rc2.X86.wordBase s, 16⟩

structure RoundFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ VG.Proof.Rc2.X86.roundWrites → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨VG.Proof.Rc2.X86.wordBase s₀, 16⟩] s₀.mem s.mem

theorem RoundFrame.refl (s : State) : VG.Proof.Rc2.X86.RoundFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem RoundFrame.base {s s' : State} (h : VG.Proof.Rc2.X86.RoundFrame s s') : VG.Proof.Rc2.X86.wordBase s' = VG.Proof.Rc2.X86.wordBase s := by
  unfold VG.Proof.Rc2.X86.wordBase; rw [h.reg .ebp (by decide)]

theorem RoundFrame.argAddr {s s' : State} (h : VG.Proof.Rc2.X86.RoundFrame s s') (i : Nat) : VG.X86.argAddr s' i = VG.X86.argAddr s i := by
  unfold VG.X86.argAddr; rw [h.reg .esp (by decide)]

theorem RoundFrame.arg {s s' : State} (h : VG.Proof.Rc2.X86.RoundFrame s s') (env : VG.Proof.Rc2.X86.RoundEnv s) : VG.X86.arg s' 0 = VG.X86.arg s 0 := by
  unfold VG.X86.arg
  rw [h.argAddr]
  exact h.mem.readW (Region.contains_self _ _) (by simpa using env.argSep) (by decide)

theorem RoundFrame.env {s s' : State} (h : VG.Proof.Rc2.X86.RoundFrame s s') (env : VG.Proof.Rc2.X86.RoundEnv s) : VG.Proof.Rc2.X86.RoundEnv s' := by
  have args := h.arg env
  constructor
  · rw [h.reg .ebp (by decide)]; exact env.scratchFit
  · rw [args]; exact env.keyFit
  · rw [h.rd, h.wr, h.argAddr]; exact env.stackRead
  · rw [h.rd, h.wr, args]; exact env.keyRead
  · rw [h.wr, h.base]; exact env.wordWrite
  · rw [args, h.base]; exact env.keySep
  · rw [h.argAddr, h.base]; exact env.argSep

theorem RoundFrame.schedule {s s' : State} (h : VG.Proof.Rc2.X86.RoundFrame s s') (env : VG.Proof.Rc2.X86.RoundEnv s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (VG.X86.arg s' 0)) = Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0)) := by
  rw [h.arg env]
  exact scheduleAt_frame h.mem _ (by simpa using env.keySep)

theorem RoundFrame.trans {s₀ s₁ s₂ : State} (h₁ : VG.Proof.Rc2.X86.RoundFrame s₀ s₁) (h₂ : VG.Proof.Rc2.X86.RoundFrame s₁ s₂) :
    VG.Proof.Rc2.X86.RoundFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame := h₂.mem
  rw [h₁.base] at frame
  exact h₁.mem.trans frame

theorem RoundFrame.of_keep {s s' : State} (h : Keep VG.Proof.Rc2.X86.roundWrites s s') : VG.Proof.Rc2.X86.RoundFrame s s' := by
  refine ⟨h.reg, h.rd, h.wr, ?_⟩
  rw [h.mem]; exact Frame.refl _ _

theorem keep_mix_round {s s' : State} {i : Nat} (h : Keep (wordReg i :: VG.Proof.Rc2.X86.temps) s s') :
    Keep VG.Proof.Rc2.X86.roundWrites s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with he | ht
  · subst r
    have fact : ∀ j < 4, wordReg j ∈ VG.Proof.Rc2.X86.roundWrites := by decide
    simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))
  · have sub : ∀ r ∈ VG.Proof.Rc2.X86.temps, r ∈ VG.Proof.Rc2.X86.roundWrites := by decide
    exact sub r ht)

theorem RoundEnv.wordRead {s : State} (h : VG.Proof.Rc2.X86.RoundEnv s) :
    ∀ i < 4, InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4 := by
  intro i hi
  obtain ⟨r, hr, hc⟩ := h.wordWrite i hi
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem storeWord32_ok (s : State) (r : Reg) (i : Nat) (hi : i < 4) (env : VG.Proof.Rc2.X86.RoundEnv s) :
    ∃ s', runBlock isa [.store (memOp .ebp (wordOff i)) r] s = some s' ∧
      s'.mem = s.mem.writeW (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) (s.gpr r) ∧
      VG.Proof.Rc2.X86.RoundFrame s s' := by
  have fit := env.scratchFit
  have write : InRegions s.wr (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i)) 4 := by
    rw [VG.Proof.Rc2.X86.wordOff_eq s i hi]; exact env.wordWrite i hi
  refine ⟨_, by
    rw [runBlock_cons, exec_store s r .ebp (wordOff i)
      (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega) write, runStep_some, runBlock_nil], ?_⟩
  constructor
  · rw [VG.Proof.Rc2.X86.wordOff_eq s i hi]
  · refine ⟨fun _ _ => rfl, rfl, rfl, ?_⟩
    rw [VG.Proof.Rc2.X86.wordOff_eq s i hi]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Rc2.X86

end

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def mixSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mix k j i v
  | .decrypt => Spec.Rc2.reverseMix k j i v

theorem mixSpec_eq (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : VG.Proof.Rc2.X86.mixSpec d k j i v = v.set! i (VG.Proof.Rc2.X86.mixResult d k j i v) := by
  cases d <;> rfl

theorem mixStep_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v) (env : VG.Proof.Rc2.X86.RoundEnv s)
    (i j : Nat) (hi : i < 4) (hj : j < 64) :
    WP isa (.block (loadWords ++ mixCore d j i ++
      ([.store (memOp .ebp (wordOff i)) (wordReg i)] : List Instr))) s (fun s' =>
        VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (VG.Proof.Rc2.X86.mixSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j i v) ∧
        VG.Proof.Rc2.X86.RoundFrame s s') := by
  rw [List.append_assoc, WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.loadWords_ok s v hv env.scratchFit env.wordRead)
  intro s₁ h₁
  have k₁ : Keep VG.Proof.Rc2.X86.roundWrites s s₁ := h₁.2.weaken (by decide)
  have f₁ := RoundFrame.of_keep k₁
  have e₁ := f₁.env env
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.mixCore_ok d s₁ v h₁.1 i j hi hj e₁.stackRead e₁.keyFit e₁.keyRead)
  intro s₂ h₂
  have k₂ := VG.Proof.Rc2.X86.keep_mix_round h₂.2
  have f₂ := RoundFrame.of_keep k₂
  have frame := f₁.trans f₂
  have keep := k₁.trans k₂
  obtain ⟨s₃, run₃, mem₃, frame₃⟩ := VG.Proof.Rc2.X86.storeWord32_ok s₂ (wordReg i) i hi (frame.env env)
  refine WP.of_runBlock ⟨s₃, run₃, ?_, frame.trans frame₃⟩
  rw [frame₃.base, frame.base, VG.Proof.Rc2.X86.mixSpec_eq, mem₃, frame.base, h₂.1, keep.mem,
    f₁.schedule env]
  exact hv.update i hi _

end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem wordOff_mod (s : State) (i : Nat) :
    addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i) = VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * (i % 4)) := by
  have e : wordOff i = wordOff (i % 4) := by simp [wordOff]
  rw [e]; exact VG.Proof.Rc2.X86.wordOff_eq s _ (Nat.mod_lt _ (by decide))

theorem loadScratchWord_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (env : VG.Proof.Rc2.X86.RoundEnv s) (r : Reg) (i : Nat) :
    ∃ s', runBlock isa [.mov r (.mem (memOp .ebp (wordOff i)))] s = some s' ∧
      s'.gpr r = (v.getD (i % 4) 0).setWidth 32 ∧ Keep [r] s s' := by
  have fit := env.scratchFit
  have valid : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i)) 4 := by
    rw [VG.Proof.Rc2.X86.wordOff_mod]; exact env.wordRead _ (Nat.mod_lt _ (by decide))
  refine ⟨s.setReg r ((v.getD (i % 4) 0).setWidth 32), ?_, gpr_setReg_self _ _ _, ?_⟩
  · rw [runBlock_cons, exec_load s r .ebp (wordOff i)
      (by simp only [wordOff]; have := Nat.mod_lt i (by decide : 0 < 4); omega) valid,
      VG.Proof.Rc2.X86.wordOff_mod, hv _ (Nat.mod_lt _ (by decide)), runStep_some, runBlock_nil]
  · exact ⟨fun _ hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem mashInput_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (env : VG.Proof.Rc2.X86.RoundEnv s) (i : Nat) :
    WP isa (.block (mashInput i)) s (fun s' =>
      s'.gpr .eax = (v.getD ((i + 3) % 4) 0).setWidth 32 ∧ s'.gpr .edi = VG.X86.arg s 0 ∧
      Keep [.eax, .edi] s s') := by
  change WP isa (.block (([.mov .eax (.mem (memOp .ebp (wordOff (i + 3))))] : List Instr) ++
    [.mov .edi (.mem (memOp .esp 4))])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.loadScratchWord_ok s v hv env .eax (i + 3)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := loadArg_ok s₁ .edi 0
    (by rw [keep₁.rd, keep₁.wr, VG.Proof.Rc2.X86.argAddr_keep keep₁ (by decide)]; exact env.stackRead)
  refine WP.of_runBlock ⟨s₂, run₂, ?_, ?_, ?_⟩
  · exact (keep₂.reg .eax (by decide)).trans out₁
  · exact out₂.trans (arg_keep keep₁ (by decide) 0)
  · exact (keep₁.weaken (by simp)).trans (keep₂.weaken (by simp))

def mashResult (d : Spec.Rc2.Direction) (x k : BitVec 16) : BitVec 16 :=
  match d with
  | .encrypt => x + k
  | .decrypt => x - k

theorem mashAdjustReg_ok (d : Spec.Rc2.Direction) (s : State) (x k : BitVec 16)
    (hx : s.gpr .edx = x.setWidth 32) (hk : s.gpr .eax = k.setWidth 32) :
    ∃ s', runBlock isa [if d == .decrypt then .alu .sub .edx (.reg .eax) else .alu .add .edx (.reg .eax),
      .alu .and .edx (.imm 65535)] s = some s' ∧
      s'.gpr .edx = (VG.Proof.Rc2.X86.mashResult d x k).setWidth 32 ∧ Keep [.edx] s s' := by
  cases d <;> refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, VG.X86.readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags, ite_true, ite_false]
    rfl, ?_⟩
  all_goals
    constructor
    · rw [gpr_setReg_self, hx, hk, Word32.maskWord]
      simp [VG.Proof.Rc2.X86.mashResult, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
    · constructor
      · intro r hr
        have hn : r ≠ .edx := by simpa only [List.mem_singleton] using hr
        simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
      · rfl
      · rfl
      · rfl

theorem mashAdjust_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v) (env : VG.Proof.Rc2.X86.RoundEnv s) (i : Nat) (hi : i < 4)
    (k : BitVec 16) (hk : s.gpr .eax = k.setWidth 32) :
    WP isa (.block (mashAdjust d i)) s (fun s' =>
      s'.gpr .edx = (VG.Proof.Rc2.X86.mashResult d (v.getD i 0) k).setWidth 32 ∧ Keep [.edx] s s') := by
  change WP isa (.block (([.mov .edx (.mem (memOp .ebp (wordOff i)))] : List Instr) ++
    [if d == .decrypt then .alu .sub .edx (.reg .eax) else .alu .add .edx (.reg .eax),
      .alu .and .edx (.imm 65535)])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.X86.loadScratchWord_ok s v hv env .edx i
  rw [Nat.mod_eq_of_lt hi] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := VG.Proof.Rc2.X86.mashAdjustReg_ok d s₁ _ k out₁ ((keep₁.reg .eax (by decide)).trans hk)
  exact WP.of_runBlock ⟨s₂, run₂, out₂, keep₁.trans keep₂⟩

end VG.Proof.Rc2.X86

end

section

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem indexWord (x : BitVec 16) :
    ((x.setWidth 32).setWidth 6).toNat = (x &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 4294967296 % 64 = x.toNat &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 4294967296 by have := x.isLt; omega)]

def mashSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mashSpec_eq (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (i : Nat)
    (v : Spec.Rc2.State) : VG.Proof.Rc2.X86.mashSpec d k i v = v.set! i
      (VG.Proof.Rc2.X86.mashResult d (v.getD i 0) (k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0)) := by
  cases d <;> rfl

theorem mash_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v) (env : VG.Proof.Rc2.X86.RoundEnv s) (i : Nat) (hi : i < 4) :
    WP isa (.block (mash d i)) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (VG.Proof.Rc2.X86.mashSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) i v) ∧
      VG.Proof.Rc2.X86.RoundFrame s s') := by
  rw [mash, List.append_assoc, List.append_assoc, WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.mashInput_ok s v hv env i)
  intro s₁ ⟨index₁, key₁, keep₁⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.keyLookup_ok s₁ (by rw [key₁]; exact env.keyFit)
    (by rw [keep₁.rd, keep₁.wr, key₁]; exact env.keyRead))
  intro s₂ h₂
  have k₁ : Keep VG.Proof.Rc2.X86.roundWrites s s₁ := keep₁.weaken (by decide)
  have k₂ : Keep VG.Proof.Rc2.X86.roundWrites s₁ s₂ := h₂.2.weaken (by decide)
  have keep := k₁.trans k₂
  have frame := RoundFrame.of_keep keep
  have env₂ := frame.env env
  have words₂ : VG.Proof.Rc2.X86.MemWords s₂.mem (VG.Proof.Rc2.X86.wordBase s₂) v := by rw [keep.mem, frame.base]; exact hv
  have key₂ : s₂.gpr .eax = ((Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))).getD
      ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0).setWidth 32 := by
    rw [h₂.1, keep₁.mem, key₁, index₁, VG.Proof.Rc2.X86.indexWord]
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.mashAdjust_ok d s₂ v words₂ env₂ i hi _ key₂)
  intro s₃ h₃
  have k₃ : Keep VG.Proof.Rc2.X86.roundWrites s₂ s₃ := h₃.2.weaken (by decide)
  have frame₃ := frame.trans (RoundFrame.of_keep k₃)
  obtain ⟨s₄, run₄, mem₄, frame₄⟩ := VG.Proof.Rc2.X86.storeWord32_ok s₃ .edx i hi (frame₃.env env)
  refine WP.of_runBlock ⟨s₄, run₄, ?_, frame₃.trans frame₄⟩
  rw [frame₄.base, frame₃.base, mem₄, frame₃.base, h₃.1, h₃.2.mem, keep.mem, VG.Proof.Rc2.X86.mashSpec_eq]
  exact hv.update i hi _

end VG.Proof.Rc2.X86

end

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v → VG.Proof.Rc2.X86.RoundEnv s →
      WP isa (.block (code i)) s (fun s' =>
        VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (step (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) i v) ∧ VG.Proof.Rc2.X86.RoundFrame s s'))
    (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (env : VG.Proof.Rc2.X86.RoundEnv s) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) i v) v) ∧
      VG.Proof.Rc2.X86.RoundFrame s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, RoundFrame.refl s⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv env)
    intro s₁ h₁
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 (h₁.2.env env))
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.schedule env] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (j : Nat) (hj : j < 16)
    (env : VG.Proof.Rc2.X86.RoundEnv s) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j v) ∧
      VG.Proof.Rc2.X86.RoundFrame s s') := by
  apply VG.Proof.Rc2.X86.foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound := List.mem_range.mp hi
  exact VG.Proof.Rc2.X86.mixStep_ok .encrypt s v hv env i (4 * j + i) bound (by omega)

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (j : Nat) (hj : j < 16)
    (env : VG.Proof.Rc2.X86.RoundEnv s) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j v) ∧
      VG.Proof.Rc2.X86.RoundFrame s s') := by
  apply VG.Proof.Rc2.X86.foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  exact VG.Proof.Rc2.X86.mixStep_ok .decrypt s v hv env i (4 * j + i) bound (by omega)

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (env : VG.Proof.Rc2.X86.RoundEnv s) :
    WP isa (.block ((VG.Proof.Rc2.X86.order d).flatMap (mash d))) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (VG.Proof.Rc2.X86.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) v) ∧
      VG.Proof.Rc2.X86.RoundFrame s s') := by
  have he (k : Spec.Rc2.Schedule) : VG.Proof.Rc2.X86.mashRoundSpec d k v =
      (VG.Proof.Rc2.X86.order d).foldl (fun v i => VG.Proof.Rc2.X86.mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply VG.Proof.Rc2.X86.foldWords_ok (step := fun k i v => VG.Proof.Rc2.X86.mashSpec d k i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [VG.Proof.Rc2.X86.order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  exact VG.Proof.Rc2.X86.mash_ok d s v hv env i bound

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then VG.Proof.Rc2.X86.mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (j : Nat) (hj : j < 16)
    (env : VG.Proof.Rc2.X86.RoundEnv s) :
    WP isa (.block (round d j)) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (VG.Proof.Rc2.X86.roundSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j v) ∧
      VG.Proof.Rc2.X86.RoundFrame s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : VG.Proof.Rc2.X86.MemWords s₁.mem (VG.Proof.Rc2.X86.wordBase s₁) v₁ ∧ VG.Proof.Rc2.X86.RoundFrame s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (VG.Proof.Rc2.X86.order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        VG.Proof.Rc2.X86.MemWords s₂.mem (VG.Proof.Rc2.X86.wordBase s₂) (if j = 4 ∨ j = 10 then VG.Proof.Rc2.X86.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) v₁
          else v₁) ∧ VG.Proof.Rc2.X86.RoundFrame s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      apply WP.mono (VG.Proof.Rc2.X86.mashRound_ok d s₁ v₁ h₁.1 (h₁.2.env env))
      intro s₂ h₂
      rw [h₁.2.schedule env] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.X86.mixRound_ok s v hv j hj env)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.X86.reverseMixRound_ok s v hv (15 - j) (by omega) env)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (env : VG.Proof.Rc2.X86.RoundEnv s) :
    WP isa (.block ((List.range 16).flatMap (round d))) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') ((List.range 16).foldl (fun v j => VG.Proof.Rc2.X86.roundSpec d
        (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j v) v) ∧ VG.Proof.Rc2.X86.RoundFrame s s') := by
  apply VG.Proof.Rc2.X86.foldWords_ok (step := fun k j v => VG.Proof.Rc2.X86.roundSpec d k j v) _ _ _ s v hv env
  intro j hj s v hv env
  exact VG.Proof.Rc2.X86.round_ok d s v hv j (List.mem_range.mp hj) env

end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem decode_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  rw [Spec.Rc2.decodeBlock, getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  rw [Spec.Rc2.blockAt, getD_ofFn _ _ (by omega), getD_ofFn _ _ (by omega)]

theorem loadWord_ok (s : State) (i : Nat) (hi : i < 4)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1)
    (writable : InRegions s.wr (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ s', runBlock isa (loadWord i) s = some s' ∧
      Keep [.eax, .edx] {s with mem := (s.mem.writeW (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i))
        (((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD i 0).setWidth 32))} s' := by
  have lo := readable (2 * i) (by omega)
  have high := readable (2 * i + 1) (by omega)
  have a := addr_add (x := s.gpr .edi) (k := 2 * i) (by omega)
  have b := addr_add (x := s.gpr .edi) (k := 2 * i + 1) (by omega)
  have c : addr32 (s.gpr .ebp + BitVec.ofNat 32 (wordOff i)) = VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega), VG.Proof.Rc2.X86.wordOff_eq s i hi]
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, loadWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, VG.X86.readSrc, State.ea, memOp, State.load8, State.store32,
      ← VG.Proof.Rc2.X86.addr_eq_def, a, b, c, lo, high, writable,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags, gpr_arithFlags,
      mem_setReg, mem_setFlags, mem_arithFlags, rd_setReg, rd_setFlags, rd_arithFlags,
      wr_setReg, wr_setFlags, wr_arithFlags]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr.1, hr.2, ite_false]
  · rw [VG.Proof.Rc2.X86.decode_word _ _ i hi, Word32.joinBytes]
  · rfl
  · rfl

theorem loadBlockWords_ok (n : Nat) (hn : n ≤ 4) (s : State)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1)
    (writable : ∀ i < 4, InRegions s.wr (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (addr32 (s.gpr .edi)) 8).Disjoint ⟨VG.Proof.Rc2.X86.wordBase s, 16⟩) :
    WP isa (.block ((List.range n).flatMap loadWord)) s (fun s' =>
      Keep [.eax, .edx] {s with mem := (saveMem s.mem (VG.Proof.Rc2.X86.wordBase s)
        (fun i => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD i 0).setWidth 32) n)} s') := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ keep₁
    have ptr₁ := keep₁.reg .edi (by decide)
    have scratch₁ := keep₁.reg .ebp (by decide)
    have base₁ : VG.Proof.Rc2.X86.wordBase s₁ = VG.Proof.Rc2.X86.wordBase s := by unfold VG.Proof.Rc2.X86.wordBase; rw [scratch₁]
    have frame₁ : Frame [⟨VG.Proof.Rc2.X86.wordBase s, 16⟩] s.mem s₁.mem := by
      rw [keep₁.mem]
      exact saveMem_frame_le _ _ _ n 4 (by omega) (by decide)
    have block₁ : Spec.Rc2.blockAt s₁.mem (addr32 (s₁.gpr .edi)) = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)) := by
      rw [ptr₁]
      exact blockAt_frame frame₁ _ (by simpa using sep)
    obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.Rc2.X86.loadWord_ok s₁ n (by omega)
      (by rw [ptr₁]; exact fit) (by rw [scratch₁]; exact scratchFit)
      (by rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable)
      (by rw [keep₁.wr, base₁]; exact writable n (by omega))
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, block₁, keep₁.mem, base₁, saveMem_succ]

theorem blockLoad_ok (s : State)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1)
    (writable : ∀ i < 4, InRegions s.wr (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (addr32 (s.gpr .edi)) 8).Disjoint ⟨VG.Proof.Rc2.X86.wordBase s, 16⟩) :
    WP isa (.block ((List.range 4).flatMap loadWord)) s (fun s' =>
      VG.Proof.Rc2.X86.MemWords s'.mem (VG.Proof.Rc2.X86.wordBase s') (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))) ∧
      VG.Proof.Rc2.X86.RoundFrame s s') := by
  apply WP.mono (VG.Proof.Rc2.X86.loadBlockWords_ok 4 (by decide) s fit scratchFit readable writable sep)
  intro s' h
  have base : VG.Proof.Rc2.X86.wordBase s' = VG.Proof.Rc2.X86.wordBase s := by unfold VG.Proof.Rc2.X86.wordBase; rw [h.reg .ebp (by decide)]
  constructor
  · intro i hi
    rw [base, h.mem]
    exact saveMem_read s.mem (VG.Proof.Rc2.X86.wordBase s)
      (fun j => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD j 0).setWidth 32)
      4 (by decide) i hi
  · refine ⟨fun r hr => h.reg r (fun hm => hr ((by decide : ∀ r ∈ [.eax, .edx], r ∈ roundWrites) r hm)),
      h.rd, h.wr, ?_⟩
    rw [h.mem]
    exact saveMem_frame s.mem (VG.Proof.Rc2.X86.wordBase s)
      (fun j => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD j 0).setWidth 32)
      4 (by decide)

end VG.Proof.Rc2.X86

end

section

/-! # Writing the four RC2 words as little-endian bytes -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.WriteBytes VG.Proof.Rc2.Word32

theorem storeWord_ok (s : State) (i : Nat) (hi : i < 4) (v : BitVec 16)
    (value : s.mem.readW (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 32 = v.setWidth 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (storeWord i) s = some s' ∧
      Keep [.eax] {s with
        mem := (s.mem.writeW (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i)) (v.setWidth 8)).writeW
          (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1)) ((v >>> 8).setWidth 8)} s' := by
  have lo := writable (2 * i) (by omega)
  have high := writable (2 * i + 1) (by omega)
  have a := addr_add (x := s.gpr .edi) (k := 2 * i) (by omega)
  have b := addr_add (x := s.gpr .edi) (k := 2 * i + 1) (by omega)
  have c : addr32 (s.gpr .ebp + BitVec.ofNat 32 (wordOff i)) = VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega), VG.Proof.Rc2.X86.wordOff_eq s i hi]
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, and_self, storeWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, execShift, VG.X86.readSrc, State.ea, memOp, Reg8.reg, State.load32, State.store8,
      ← VG.Proof.Rc2.X86.addr_eq_def, a, b, c, lo, high, readable, value,
      Option.map_some, gpr_setReg, gpr_setFlags, mem_setReg, mem_setFlags,
      rd_setReg, rd_setFlags, wr_setReg, wr_setFlags]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [gpr_setReg, gpr_setFlags, hr, ite_false]
  · simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    have byte : ((v.setWidth 32) >>> 8).setWidth 8 = (v >>> 8).setWidth 8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj,
        show 8 + j < 32 by omega, decide_true, Bool.true_and]
    rw [byte]
  · rfl
  · rfl

theorem storeWords_ok (n : Nat) (hn : n ≤ 4) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (VG.Proof.Rc2.X86.wordBase s) 16).Disjoint ⟨addr32 (s.gpr .edi), 8⟩)
    (writable : ∀ j < 8, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range n).flatMap storeWord)) s (fun s' =>
      Keep [.eax] {s with mem := writeBytes s.mem (addr32 (s.gpr .edi)) (outputBytes v n)} s') := by
  induction n generalizing s with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => rfl, (writeBytes_nil s.mem (addr32 (s.gpr .edi))).symm, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    apply WP.mono (ih (by omega) s hv fit scratchFit readable sep writable)
    intro s₁ keep₁
    have ptr₁ := keep₁.reg .edi (by decide)
    have scratch₁ := keep₁.reg .ebp (by decide)
    have base₁ : VG.Proof.Rc2.X86.wordBase s₁ = VG.Proof.Rc2.X86.wordBase s := by unfold VG.Proof.Rc2.X86.wordBase; rw [scratch₁]
    have frame₁ : Frame [⟨addr32 (s.gpr .edi), 8⟩] s.mem s₁.mem := by
      rw [keep₁.mem]
      exact writeBytes_frame _ _ _ (by
        simpa only [BitVec.add_zero] using Offset.contains_base (addr32 (s.gpr .edi))
          (d := 0) (n := (outputBytes v n).length) (by rw [outputBytes_length]; omega) (by decide))
    have val₁ : s₁.mem.readW (VG.Proof.Rc2.X86.wordBase s₁ + BitVec.ofNat 64 (4 * n)) 32 = (v.getD n 0).setWidth 32 := by
      rw [base₁, frame₁.readW (r := ⟨VG.Proof.Rc2.X86.wordBase s, 16⟩)
        (Offset.contains_base _ (by omega) (by omega)) (by simpa using sep) (by decide)]
      exact hv n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.Rc2.X86.storeWord_ok s₁ n (by omega) _ val₁
      (by rw [scratch₁]; exact scratchFit)
      (by rw [keep₁.rd, keep₁.wr, base₁]; exact readable n (by omega))
      (by rw [ptr₁]; exact fit) (by rw [keep₁.wr, ptr₁]; exact writable)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, keep₁.mem, ptr₁, outputBytes_write _ _ _ n (by omega)]

theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.X86.MemWords s.mem (VG.Proof.Rc2.X86.wordBase s) v)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (VG.Proof.Rc2.X86.wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (VG.Proof.Rc2.X86.wordBase s) 16).Disjoint ⟨addr32 (s.gpr .edi), 8⟩)
    (writable : ∀ j < 8, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range 4).flatMap storeWord)) s (fun s' =>
      Keep [.eax] {s with mem := s.mem.writeW (addr32 (s.gpr .edi)) (pack v)} s') := by
  apply WP.mono (VG.Proof.Rc2.X86.storeWords_ok 4 (by decide) s v hv fit scratchFit readable sep writable)
  intro s' h
  rw [outputBytes_pack] at h
  exact h

end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem argContainsCount (s : State) (count : Nat) (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (i : Nat) (hi : i < count) :
    (Region.mk (VG.X86.argAddr s 0) (4 * count)).Contains
      (addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i)) 4 := by
  rw [argAddr_eq s 0 (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arguments_frame (count : Nat) {s s' : State} {rs : List Region}
    (frame : Frame rs s.mem s'.mem) (sp : s'.gpr .esp = s.gpr .esp)
    (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (sep : ∀ r ∈ rs, (Region.mk (VG.X86.argAddr s 0) (4 * count)).Disjoint r) :
    ∀ i < count, VG.X86.arg s' i = VG.X86.arg s i := by
  intro i hi
  unfold VG.X86.arg
  have e : VG.X86.argAddr s' i = VG.X86.argAddr s i := by unfold VG.X86.argAddr; rw [sp]
  rw [e, argAddr_eq s i (by omega)]
  exact frame.readW (VG.Proof.Rc2.X86.argContainsCount s count fit i hi) sep (by decide)

theorem pinBlock_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (VG.X86.argAddr s 1) 4) :
    ∃ s', runBlock isa [rr .ebp .eax, .mov .edi (.mem (memOp .esp 8))] s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .edi = VG.X86.arg s 1 ∧ Keep [.ebp, .edi] s s' := by
  simp only [VG.X86.argAddr, Nat.reduceMul, Nat.reduceAdd] at readable
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, rr, memOp, State.ea, runBlock_cons,
      runStep_some, runBlock_nil, exec, VG.X86.readSrc, State.load32, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, readable]
    rfl, ?_⟩
  refine ⟨?_, rfl, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem blockScratchBase_ok (s : State) :
    ∃ s', runBlock isa [rr .eax .ebp] s = some s' ∧
      s'.gpr .eax = s.gpr .ebp ∧ Keep [.eax] s s' := by
  refine ⟨s.setReg .eax (s.gpr .ebp), rfl, rfl, ?_⟩
  exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

end VG.Proof.Rc2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Block`. -/
section

section

/-! # RC2 block correctness and the x86 calling convention -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def blockSavedReg (i : Nat) : Reg := blockSaved.getD i .eax

theorem blockSave_eq : blockSave = saveCode .eax VG.Proof.Rc2.X86.blockSavedReg 5 := rfl

theorem blockRestore_eq : blockRestore = restoreCode .eax VG.Proof.Rc2.X86.blockSavedReg (List.range 5) := rfl

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (VG.X86.arg s 0), 128⟩
    let data : Region := ⟨addr32 (VG.X86.arg s 1), 8⟩
    let scratch : Region := ⟨addr32 (VG.X86.arg s 2), 256⟩
    let args : Region := ⟨VG.X86.argAddr s 0, 12⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (VG.X86.arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 2).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := s'.gpr .ecx = s.gpr .ecx ∧ Spec.Rc2.blockAt s'.mem (addr32 (VG.X86.arg s 1)) =
    VG.Proof.Rc2.X86.cipher d (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) (Spec.Rc2.blockAt s.mem (addr32 (VG.X86.arg s 1)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, VG.X86.arg s₁ i = VG.X86.arg s₂ i

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    VG.Proof.Rc2.X86.cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => VG.Proof.Rc2.X86.roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.X86.blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => abiPreserved s s' ∧ (VG.Proof.Rc2.X86.blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, retData, retScratch, keyFit, dataFit, scratchFit, spFit⟩ := hs
  have argRead (st : State) (rd : st.rd = s.rd) (wr : st.wr = s.wr)
      (sp : st.gpr .esp = s.gpr .esp) : ∀ i < 3, InRegions (st.rd ++ st.wr) (VG.X86.argAddr st i) 4 := by
    intro i hi
    have fit : (st.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by rw [sp]; exact spFit
    rw [argAddr_eq st i (by omega), sp, rd, wr, hrd, hwr]
    exact ⟨⟨VG.X86.argAddr s 0, 12⟩, by simp, VG.Proof.Rc2.X86.argContainsCount s 3 spFit i hi⟩
  have writes : ∀ i < 5, InRegions s.wr (addr32 (VG.X86.arg s 2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨addr32 (VG.X86.arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadArg_ok s .eax 2 (argRead s rfl rfl rfl 2 (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  rw [WP.block_append_iff, VG.Proof.Rc2.X86.blockSave_eq]
  apply WP.mono (saveCode_ok s₀ .eax VG.Proof.Rc2.X86.blockSavedReg 5 (by decide)
    (by rw [scratch₀]; exact scratchFit) (by rw [keep₀.wr, scratch₀]; exact writes))
  intro s₁ h₁
  have gpr₀ (r : Reg) (hr : r ≠ .eax) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := by rw [h₁.1]; exact gpr₀ .esp (by decide)
  have savedFrame : Frame [⟨addr32 (VG.X86.arg s 2), 256⟩] s.mem s₁.mem := by
    rw [h₁.2.2.2, keep₀.mem, scratch₀]
    exact saveMem_frame_le s.mem (addr32 (VG.X86.arg s 2)) (fun i => s₀.gpr (VG.Proof.Rc2.X86.blockSavedReg i)) 5 64 (by decide) (by decide)
  have args₁ := VG.Proof.Rc2.X86.arguments_frame 3 savedFrame sp₁ spFit (by simpa using argsScratch)
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, scratch₂, data₂, keep₂⟩ := VG.Proof.Rc2.X86.pinBlock_ok s₁
    (argRead s₁ (h₁.2.1.trans keep₀.rd) (h₁.2.2.1.trans keep₀.wr) sp₁ 1 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [h₁.1, scratch₀] at scratch₂
  rw [args₁ 1 (by decide)] at data₂
  have sp₂ : s₂.gpr .esp = s.gpr .esp := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  have frame₂ : Frame [⟨addr32 (VG.X86.arg s 2), 256⟩] s.mem s₂.mem := by rw [keep₂.mem]; exact savedFrame
  have args₂ := VG.Proof.Rc2.X86.arguments_frame 3 frame₂ sp₂ spFit (by simpa using argsScratch)
  have base₂ : VG.Proof.Rc2.X86.wordBase s₂ = addr32 (VG.X86.arg s 2) + 64 := by unfold VG.Proof.Rc2.X86.wordBase; rw [scratch₂]
  have wordsSub : Region.Sub ⟨VG.Proof.Rc2.X86.wordBase s₂, 16⟩ ⟨addr32 (VG.X86.arg s 2), 256⟩ := by
    rw [base₂]; exact Offset.sub_base (addr32 (VG.X86.arg s 2)) (d := 64) (n := 16) (k := 256) (by decide)
  have dataWords : (Region.mk (addr32 (VG.X86.arg s 1)) 8).Disjoint ⟨VG.Proof.Rc2.X86.wordBase s₂, 16⟩ := by
    intro a ha hb; exact dataSep a ha (wordsSub a hb)
  have env₂ : VG.Proof.Rc2.X86.RoundEnv s₂ := by
    constructor
    · rw [scratch₂]; exact scratchFit
    · rw [args₂ 0 (by decide)]; exact keyFit
    · exact argRead s₂ rd₂ wr₂ sp₂ 0 (by decide)
    · intro i hi
      rw [args₂ 0 (by decide), rd₂, wr₂, hrd, hwr]
      exact ⟨⟨addr32 (VG.X86.arg s 0), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · intro i hi
      rw [wr₂, hwr, base₂, BitVec.add_assoc, show (64 : Addr) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]
      exact ⟨⟨addr32 (VG.X86.arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [args₂ 0 (by decide)]
      intro a ha hb; exact keySep a ha (wordsSub a hb)
    · have ae : VG.X86.argAddr s₂ 0 = VG.X86.argAddr s 0 := by unfold VG.X86.argAddr; rw [sp₂]
      rw [ae]
      intro a ha hb
      exact argsScratch a (Region.sub_prefix (by decide : 4 ≤ 12) a ha) (wordsSub a hb)
  have input₂ : Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .edi)) = Spec.Rc2.blockAt s.mem (addr32 (VG.X86.arg s 1)) := by
    rw [data₂]; exact blockAt_frame frame₂ _ (by simpa using dataSep)
  have schedule₂ : Spec.Rc2.scheduleAt s₂.mem (addr32 (VG.X86.arg s₂ 0)) = Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0)) := by
    rw [args₂ 0 (by decide)]; exact scheduleAt_frame frame₂ _ (by simpa using keySep)
  have dataRead₂ : ∀ i < 8, InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, data₂, hrd, hwr]
    exact ⟨⟨addr32 (VG.X86.arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.blockLoad_ok s₂ (by rw [data₂]; exact dataFit) env₂.scratchFit dataRead₂ env₂.wordWrite
    (by rw [data₂]; exact dataWords))
  intro s₃ h₃
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.rounds_ok d s₃ _ h₃.1 (h₃.2.env env₂))
  intro s₄ h₄
  have core := h₃.2.trans h₄.2
  have env₄ := core.env env₂
  have sp₄ : s₄.gpr .esp = s.gpr .esp := (core.reg .esp (by decide)).trans sp₂
  have scratch₄ : s₄.gpr .ebp = VG.X86.arg s 2 := (core.reg .ebp (by decide)).trans scratch₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have frame₄ : Frame [⟨addr32 (VG.X86.arg s 2), 256⟩] s.mem s₄.mem :=
    frame₂.trans (core.mem.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_cons_self, wordsSub⟩))
  have args₄ := VG.Proof.Rc2.X86.arguments_frame 3 frame₄ sp₄ spFit (by simpa using argsScratch)
  let v := (List.range 16).foldl (fun v j => VG.Proof.Rc2.X86.roundSpec d
    (Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0))) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (VG.X86.arg s 1))))
  have words₄ : VG.Proof.Rc2.X86.MemWords s₄.mem (VG.Proof.Rc2.X86.wordBase s₄) v := by
    have h := h₄.1
    rw [h₃.2.schedule env₂, schedule₂, input₂] at h
    exact h
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, data₅, keep₅⟩ := loadArg_ok s₄ .edi 1 (argRead s₄ rd₄ wr₄ sp₄ 1 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [args₄ 1 (by decide)] at data₅
  have base₅ : VG.Proof.Rc2.X86.wordBase s₅ = VG.Proof.Rc2.X86.wordBase s₄ := by unfold VG.Proof.Rc2.X86.wordBase; rw [keep₅.reg .ebp (by decide)]
  have writable₅ : ∀ i < 8, InRegions s₅.wr (addr32 (s₅.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [keep₅.wr, wr₄, data₅, hwr]
    exact ⟨⟨addr32 (VG.X86.arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.X86.blockStore_ok s₅ v (by rw [keep₅.mem, base₅]; exact words₄)
    (by rw [data₅]; exact dataFit) (by rw [keep₅.reg .ebp (by decide)]; exact env₄.scratchFit)
    (by rw [keep₅.rd, keep₅.wr, base₅]; exact env₄.wordRead)
    (by rw [base₅, core.base, data₅]; exact dataWords.symm) writable₅)
  intro s₆ h₆
  have mem₆ : s₆.mem = s₄.mem.writeW (addr32 (VG.X86.arg s 1)) (pack v) := by rw [h₆.mem, keep₅.mem, data₅]
  have scratch₆ : s₆.gpr .ebp = VG.X86.arg s 2 := (h₆.reg .ebp (by decide)).trans ((keep₅.reg .ebp (by decide)).trans scratch₄)
  have sp₆ : s₆.gpr .esp = s.gpr .esp := (h₆.reg .esp (by decide)).trans ((keep₅.reg .esp (by decide)).trans sp₄)
  have rd₆ := h₆.rd.trans (keep₅.rd.trans rd₄)
  have wr₆ := h₆.wr.trans (keep₅.wr.trans wr₄)
  rw [WP.block_append_iff]
  obtain ⟨s₇, run₇, base₇, keep₇⟩ := VG.Proof.Rc2.X86.blockScratchBase_ok s₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  rw [scratch₆] at base₇
  have reads₇ : ∀ i ∈ List.range 5, InRegions (s₇.rd ++ s₇.wr) (addr32 (s₇.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [keep₇.rd, keep₇.wr, rd₆, wr₆, base₇, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨addr32 (VG.X86.arg s 2), 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored₇ : ∀ i ∈ List.range 5, s₇.mem.readW (addr32 (s₇.gpr .eax) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (VG.Proof.Rc2.X86.blockSavedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [keep₇.mem, mem₆, base₇, Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _)) (by decide)]
    have sep : (Region.mk (addr32 (VG.X86.arg s 2)) 20).Disjoint ⟨VG.Proof.Rc2.X86.wordBase s₂, 16⟩ := by
      rw [base₂]; exact (Offset.disjoint_base (addr32 (VG.X86.arg s 2)) (d := 64) (n := 16) (k := 20) (by decide) (by decide)).symm
    rw [core.mem.readW (r := ⟨addr32 (VG.X86.arg s 2), 20⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using sep) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀, saveMem_read _ _ _ 5 (by decide) i bound]
    exact gpr₀ _ (by
      have fact : ∀ i ∈ List.range 5, VG.Proof.Rc2.X86.blockSavedReg i ≠ .eax := by decide
      exact fact i hi)
  rw [VG.Proof.Rc2.X86.blockRestore_eq]
  apply WP.mono (restoreCode_ok s₇ .eax VG.Proof.Rc2.X86.blockSavedReg (List.range 5) s.gpr
    (by rw [base₇]; exact scratchFit) (by decide) (by decide) reads₇ stored₇)
  intro s₈ h₈
  constructor
  · constructor
    · intro r hr
      by_cases he : r = .esp
      · subst r
        exact (h₈.2.reg .esp (by decide)).trans ((keep₇.reg .esp (by decide)).trans sp₆)
      · exact h₈.1 r (by
          have fact : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ (List.range 5).map VG.Proof.Rc2.X86.blockSavedReg := by decide
          exact fact r hr he)
    · rw [h₈.2.mem, keep₇.mem, mem₆, Mem.readW_writeW_sep
        (retData.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
      exact frame₄.readW (Region.contains_self _ _) (by simpa [addr32] using retScratch) (by decide)
  · refine ⟨h₈.1 .ecx (by decide), ?_⟩
    change Spec.Rc2.blockAt s₈.mem (addr32 (VG.X86.arg s 1)) = _
    rw [h₈.2.mem, keep₇.mem, mem₆, blockAt_write64, VG.Proof.Rc2.X86.cipher_rounds]

end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def blockTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 16 }

theorem blockTaint_wf {d : Spec.Rc2.Direction} {s : State} (h : (VG.Proof.Rc2.X86.blockContract d).pre s) : VG.X86.Taint.Wf VG.Proof.Rc2.X86.blockTaint s := by
  obtain ⟨_, wr, _, _, ao, asc, ro, rsc, _, _, _, spfit⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [VG.Proof.Rc2.X86.blockTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (n := 12) (by omega) ro ao
  · exact Taint.frame_disjoint (n := 12) (by omega) rsc asc

theorem blockTaint_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h₁ : (VG.Proof.Rc2.X86.blockContract d).pre s₁) (h₂ : (VG.Proof.Rc2.X86.blockContract d).pre s₂)
    (hp : (VG.Proof.Rc2.X86.blockContract d).pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Rc2.X86.blockTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (VG.Proof.Rc2.X86.blockContract d).pre s → (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    VG.Proof.Rc2.X86.blockTaint_wf h₁, VG.Proof.Rc2.X86.blockTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Rc2.X86.blockTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [VG.Proof.Rc2.X86.blockTaint] at hk
    rw [show Taint.depth blockTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem encryptBlock_constantTime : ConstantTime isa (VG.Proof.Rc2.X86.blockContract .encrypt).pre (VG.Proof.Rc2.X86.blockContract .encrypt).pub encryptBlock := by
  exact VG.Taint.constantTime (A := taint) VG.Proof.Rc2.X86.blockTaint (fun _ _ h₁ h₂ hp => VG.Proof.Rc2.X86.blockTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlock_constantTime : ConstantTime isa (VG.Proof.Rc2.X86.blockContract .decrypt).pre (VG.Proof.Rc2.X86.blockContract .decrypt).pub decryptBlock := by
  exact VG.Taint.constantTime (A := taint) VG.Proof.Rc2.X86.blockTaint (fun _ _ h₁ h₂ hp => VG.Proof.Rc2.X86.blockTaint_agree h₁ h₂ hp)
    (by taint_decide)

def blockSatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x400d then 0x30 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_verified : Verified target encryptBlock (Spec.Rc2.encryptBlockContract abi) := by
  refine Verified.of_correct (VG.Proof.Rc2.X86.block_correct .encrypt) VG.Proof.Rc2.X86.encryptBlock_constantTime ?_
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · sig_implies_pre [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, VG.Proof.Rc2.X86.blockContract, VG.Proof.Rc2.X86.cipher]
  · intro s s' _ h
    sig_post [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal, argBytes]
    exact h.2
  · sig_implies_pub [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, VG.Proof.Rc2.X86.blockContract, VG.Proof.Rc2.X86.cipher]
  · sig_implies_sat [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, VG.Proof.Rc2.X86.blockContract, VG.Proof.Rc2.X86.cipher]
      [blockSatState, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.blockSatState

theorem decrypt_verified : Verified target decryptBlock (Spec.Rc2.decryptBlockContract abi) := by
  refine Verified.of_correct (VG.Proof.Rc2.X86.block_correct .decrypt) VG.Proof.Rc2.X86.decryptBlock_constantTime ?_
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · sig_implies_pre [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, VG.Proof.Rc2.X86.blockContract, VG.Proof.Rc2.X86.cipher]
  · intro s s' _ h
    sig_post [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal, argBytes]
    exact h.2
  · sig_implies_pub [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, VG.Proof.Rc2.X86.blockContract, VG.Proof.Rc2.X86.cipher]
  · sig_implies_sat [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argSlots, argVal,
      argBytes, addr32, VG.Proof.Rc2.X86.blockContract, VG.Proof.Rc2.X86.cipher]
      [blockSatState, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.blockSatState

end VG.Proof.Rc2.X86

end
