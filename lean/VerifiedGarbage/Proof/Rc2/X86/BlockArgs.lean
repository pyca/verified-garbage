import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps

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

theorem wordReg_mem (i : Nat) : wordReg i ∈ wordRegs := by
  have fact : ∀ i < 4, wordReg i ∈ wordRegs := by decide
  simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ temps := by
  exact fun h => by
    have hs := wordReg_separate i
    simp only [temps, List.mem_cons, List.not_mem_nil, or_false] at h
    exact h.elim hs.1 hs.2.1

theorem wordOff_eq (s : State) (i : Nat) (hi : i < 4) :
    addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i) = wordBase s + BitVec.ofNat 64 (4 * i) := by
  simp only [wordOff, Nat.mod_eq_of_lt hi, wordBase, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by simp [Vector.getD, hi]

theorem MemWords.update {m : Mem} {p : Addr} {v : Spec.Rc2.State}
    (h : MemWords m p v) (i : Nat) (hi : i < 4) (x : BitVec 16) :
    MemWords (m.writeW (p + BitVec.ofNat 64 (4 * i)) (x.setWidth 32)) p (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j
    rw [Mem.readW_writeW_self32]
    simp [Vector.getD, hi]
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide), h j hj]
    rw [vector_getD _ j hj, vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.at_mod {s : State} {v : Spec.Rc2.State} (h : Words s v) (i : Nat) :
    s.gpr (wordReg i) = (v.getD (i % 4) 0).setWidth 32 := by
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (keep : Keep temps s s') : Words s' v := by
  intro i hi
  exact (keep.reg _ (wordReg_not_temps i)).trans (h i hi)

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 32)
    (keep : Keep (wordReg i :: temps) s s') : Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j; simpa [Vector.getD, hi] using out
  · rw [keep.reg _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((wordReg_injective j hj i hi).mp e), wordReg_not_temps j⟩), h j hj]
    rw [vector_getD _ j hj, vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

def wordIndex : Reg → Nat
  | .eax => 0 | .ebx => 1 | .ecx => 2 | .edx => 3 | _ => 0

theorem wordIndex_reg : ∀ i < 4, wordIndex (wordReg i) = i := by decide

theorem loadWords_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (fit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block loadWords) s (fun s' => Words s' v ∧ Keep wordRegs s s') := by
  let regs := fun i => wordReg (i - 16)
  let values := fun r => (v.getD (wordIndex r) 0).setWidth 32
  have code : loadWords = restoreCode .ebp regs [16, 17, 18, 19] := rfl
  have bounds : ∀ i ∈ [16, 17, 18, 19], 16 ≤ i ∧ i < 20 := by decide
  have addr (i : Nat) (hi : i ∈ [16, 17, 18, 19]) :
      addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i) = wordBase s + BitVec.ofNat 64 (4 * (i - 16)) := by
    have h := bounds i hi
    unfold wordBase
    rw [BitVec.add_assoc, show (64 : Addr) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => addr32 (s.gpr .ebp) + BitVec.ofNat 64 n) (by omega)
  rw [code]
  apply WP.mono (restoreCode_ok s .ebp regs [16, 17, 18, 19] values fit (by decide) (by decide)
    (fun i hi => by rw [addr i hi]; exact readable _ (by have := bounds i hi; omega))
    (fun i hi => by
      have h := bounds i hi
      rw [addr i hi, hv _ (by omega)]
      dsimp only [values, regs]
      rw [wordIndex_reg _ (by omega)]))
  intro s' h
  constructor
  · intro i hi
    have mem : wordReg i ∈ [16, 17, 18, 19].map regs := wordReg_mem i
    have out := h.1 (wordReg i) mem
    dsimp only [values] at out
    rw [wordIndex_reg i hi] at out
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
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]; exact Word32.maskWord _
  · exact ⟨fun r' hr => (gpr_setReg_of_ne _ _ (by simpa using hr)), rfl, rfl, rfl⟩

theorem argAddr_keep {s s' : State} {rs : List Reg} (h : Keep rs s s')
    (sp : .esp ∉ rs) (i : Nat) : argAddr s' i = argAddr s i := by
  unfold argAddr; rw [h.reg .esp sp]

def mixValue (sub : Bool) (x c k : BitVec 32) : BitVec 16 :=
  (if sub then x - c - k else x + c + k).setWidth 16

theorem mixArithmetic_ok (sub : Bool) (s : State) (i j : Nat) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixArithmetic sub j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixValue sub (s.gpr (wordReg i))
        ((s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
          (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))))
        (((Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))).getD j 0).setWidth 32)).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mixArithmetic, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := mixSelect_ok s i
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := adjust_ok sub s₁ (wordReg i)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  have k₁ : Keep (wordReg i :: temps) s s₁ := keep₁.weaken (by simp [temps])
  have k₂ : Keep (wordReg i :: temps) s₁ s₂ := keep₂.weaken (by simp)
  have keep := k₁.trans k₂
  have sp : .esp ∉ wordReg i :: temps := by
    simp only [List.mem_cons, temps, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm (wordReg_separate i).2.2.2, by decide, by decide⟩
  have args := arg_keep keep sp 0
  have stack := argAddr_keep keep sp 0
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := mixKey_ok s₂ j hj
    (by rw [keep.rd, keep.wr, stack]; exact stackRead)
    (by rw [args]; exact fit)
    (by rw [keep.rd, keep.wr, args]; exact readable)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := adjust_ok sub s₃ (wordReg i)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  obtain ⟨s₅, run₅, out₅, keep₅⟩ := mask16_ok s₄ (wordReg i)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  constructor
  · rw [out₅, out₄, keep₃.reg _ (wordReg_not_temps i), out₂,
      keep₁.reg _ (by simp only [List.mem_singleton]; exact (wordReg_separate i).1),
      out₁, out₃, keep.mem, args]
    cases sub <;> simp only [mixValue, Bool.false_eq_true, ite_true, ite_false]
  · exact ((keep.trans (keep₃.weaken (by simp [temps]))).trans
      (keep₄.weaken (by simp))).trans (keep₅.weaken (by simp))

theorem mixValue_add (x k a b c : BitVec 16) :
    mixValue false (x.setWidth 32)
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))
      (k.setWidth 32) = x + k + (a &&& b) + (~~~a &&& c) := by
  simp only [mixValue, Bool.false_eq_true, ite_false, BitVec.setWidth_add _ _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_and, BitVec.setWidth_not (show 16 ≤ 32 by decide), BitVec.setWidth_setWidth_of_le _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_eq]
  ac_rfl

theorem mixValue_sub (x k a b c : BitVec 16) :
    mixValue true (x.setWidth 32)
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))
      (k.setWidth 32) = x - k - (a &&& b) - (~~~a &&& c) := by
  simp only [mixValue, ite_true, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ (show 16 ≤ 32 by decide),
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

theorem mixCore_encrypt_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore .encrypt j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixResult .encrypt (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mixCore, WP.block_append_iff]
  apply WP.mono (mixArithmetic_ok false s i j hj stackRead fit readable)
  intro s₁ h₁
  have out := h₁.1
  rw [hv i hi, hv.at_mod (i + 3), hv.at_mod (i + 2), hv.at_mod (i + 1), mixValue_add] at out
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := rotate16_ok s₁ (wordReg i) (wordReg_separate i).1 _ out
    (Spec.Rc2.rotation i) (rotation_bounds i).1 (rotation_bounds i).2
  refine WP.of_runBlock ⟨s₂, run₂, out₂, h₁.2.trans (keep₂.weaken ?_)⟩
  simp [temps]

theorem neighbor_ne : ∀ i < 4, ∀ n < 4, 1 ≤ n → wordReg (i + n) ≠ wordReg i := by decide

theorem mixCore_decrypt_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore .decrypt j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixResult .decrypt (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mixCore, WP.block_append_iff]
  have bounds := rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := rotate16_ok s (wordReg i) (wordReg_separate i).1 _ (hv i hi)
    (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [Word32.rotateLeft_reverse _ _ bounds.1 bounds.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have sp : .esp ∉ [wordReg i, .esi] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm (wordReg_separate i).2.2.2, by decide⟩
  have args := arg_keep keep₁ sp 0
  have stack := argAddr_keep keep₁ sp 0
  apply WP.mono (mixArithmetic_ok true s₁ i j hj
    (by rw [keep₁.rd, keep₁.wr, stack]; exact stackRead)
    (by rw [args]; exact fit)
    (by rw [keep₁.rd, keep₁.wr, args]; exact readable))
  intro s₂ h₂
  constructor
  · have nbr (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 3) :
        s₁.gpr (wordReg (i + n)) = (v.getD ((i + n) % 4) 0).setWidth 32 := by
      rw [keep₁.reg _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨neighbor_ne i hi n (by omega) hn, (wordReg_separate _).1⟩)]
      exact hv.at_mod _
    rw [h₂.1, out₁, nbr 3 (by decide) (by decide), nbr 2 (by decide) (by decide),
      nbr 1 (by decide) (by decide), keep₁.mem, args, mixValue_sub]
    rfl
  · exact (keep₁.weaken (by simp [temps])).trans h₂.2

theorem mixCore_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore d j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixResult d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  cases d
  · exact mixCore_encrypt_ok s v hv i j hi hj stackRead fit readable
  · exact mixCore_decrypt_ok s v hv i j hi hj stackRead fit readable

end VG.Proof.Rc2.X86

end

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

structure RoundEnv (s : State) : Prop where
  scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32
  keyFit : (arg s 0).toNat + 128 ≤ 2 ^ 32
  stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4
  keyRead : ∀ i < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 i) 1
  wordWrite : ∀ i < 4, InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4
  keySep : (Region.mk (addr32 (arg s 0)) 128).Disjoint ⟨wordBase s, 16⟩
  argSep : (Region.mk (argAddr s 0) 4).Disjoint ⟨wordBase s, 16⟩

structure RoundFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ roundWrites → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨wordBase s₀, 16⟩] s₀.mem s.mem

theorem RoundFrame.refl (s : State) : RoundFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem RoundFrame.base {s s' : State} (h : RoundFrame s s') : wordBase s' = wordBase s := by
  unfold wordBase; rw [h.reg .ebp (by decide)]

theorem RoundFrame.argAddr {s s' : State} (h : RoundFrame s s') (i : Nat) : argAddr s' i = argAddr s i := by
  unfold VG.X86.argAddr; rw [h.reg .esp (by decide)]

theorem RoundFrame.arg {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) : arg s' 0 = arg s 0 := by
  unfold VG.X86.arg
  rw [h.argAddr]
  exact h.mem.readW (Region.contains_self _ _) (by simpa using env.argSep) (by decide)

theorem RoundFrame.env {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) : RoundEnv s' := by
  have args := h.arg env
  constructor
  · rw [h.reg .ebp (by decide)]; exact env.scratchFit
  · rw [args]; exact env.keyFit
  · rw [h.rd, h.wr, h.argAddr]; exact env.stackRead
  · rw [h.rd, h.wr, args]; exact env.keyRead
  · rw [h.wr, h.base]; exact env.wordWrite
  · rw [args, h.base]; exact env.keySep
  · rw [h.argAddr, h.base]; exact env.argSep

theorem RoundFrame.schedule {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (VG.X86.arg s' 0)) = Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0)) := by
  rw [h.arg env]
  exact scheduleAt_frame h.mem _ (by simpa using env.keySep)

theorem RoundFrame.trans {s₀ s₁ s₂ : State} (h₁ : RoundFrame s₀ s₁) (h₂ : RoundFrame s₁ s₂) :
    RoundFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame := h₂.mem
  rw [h₁.base] at frame
  exact h₁.mem.trans frame

theorem RoundFrame.of_keep {s s' : State} (h : Keep roundWrites s s') : RoundFrame s s' := by
  refine ⟨h.reg, h.rd, h.wr, ?_⟩
  rw [h.mem]; exact Frame.refl _ _

theorem keep_mix_round {s s' : State} {i : Nat} (h : Keep (wordReg i :: temps) s s') :
    Keep roundWrites s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with he | ht
  · subst r
    have fact : ∀ j < 4, wordReg j ∈ roundWrites := by decide
    simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))
  · have sub : ∀ r ∈ temps, r ∈ roundWrites := by decide
    exact sub r ht)

theorem RoundEnv.wordRead {s : State} (h : RoundEnv s) :
    ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4 := by
  intro i hi
  obtain ⟨r, hr, hc⟩ := h.wordWrite i hi
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem storeWord32_ok (s : State) (r : Reg) (i : Nat) (hi : i < 4) (env : RoundEnv s) :
    ∃ s', runBlock isa [.store (memOp .ebp (wordOff i)) r] s = some s' ∧
      s'.mem = s.mem.writeW (wordBase s + BitVec.ofNat 64 (4 * i)) (s.gpr r) ∧
      RoundFrame s s' := by
  have fit := env.scratchFit
  have write : InRegions s.wr (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i)) 4 := by
    rw [wordOff_eq s i hi]; exact env.wordWrite i hi
  refine ⟨_, by
    rw [runBlock_cons, exec_store s r .ebp (wordOff i)
      (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega) write, runStep_some, runBlock_nil], ?_⟩
  constructor
  · rw [wordOff_eq s i hi]
  · refine ⟨fun _ _ => rfl, rfl, rfl, ?_⟩
    rw [wordOff_eq s i hi]
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
    (v : Spec.Rc2.State) : mixSpec d k j i v = v.set! i (mixResult d k j i v) := by
  cases d <;> rfl

theorem mixStep_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : MemWords s.mem (wordBase s) v) (env : RoundEnv s)
    (i j : Nat) (hi : i < 4) (hj : j < 64) :
    WP isa (.block (loadWords ++ mixCore d j i ++
      ([.store (memOp .ebp (wordOff i)) (wordReg i)] : List Instr))) s (fun s' =>
        MemWords s'.mem (wordBase s') (mixSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v) ∧
        RoundFrame s s') := by
  rw [List.append_assoc, WP.block_append_iff]
  apply WP.mono (loadWords_ok s v hv env.scratchFit env.wordRead)
  intro s₁ h₁
  have k₁ : Keep roundWrites s s₁ := h₁.2.weaken (by decide)
  have f₁ := RoundFrame.of_keep k₁
  have e₁ := f₁.env env
  rw [WP.block_append_iff]
  apply WP.mono (mixCore_ok d s₁ v h₁.1 i j hi hj e₁.stackRead e₁.keyFit e₁.keyRead)
  intro s₂ h₂
  have k₂ := keep_mix_round h₂.2
  have f₂ := RoundFrame.of_keep k₂
  have frame := f₁.trans f₂
  have keep := k₁.trans k₂
  obtain ⟨s₃, run₃, mem₃, frame₃⟩ := storeWord32_ok s₂ (wordReg i) i hi (frame.env env)
  refine WP.of_runBlock ⟨s₃, run₃, ?_, frame.trans frame₃⟩
  rw [frame₃.base, frame.base, mixSpec_eq, mem₃, frame.base, h₂.1, keep.mem,
    f₁.schedule env]
  exact hv.update i hi _

end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem wordOff_mod (s : State) (i : Nat) :
    addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i) = wordBase s + BitVec.ofNat 64 (4 * (i % 4)) := by
  have e : wordOff i = wordOff (i % 4) := by simp [wordOff]
  rw [e]; exact wordOff_eq s _ (Nat.mod_lt _ (by decide))

theorem loadScratchWord_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (env : RoundEnv s) (r : Reg) (i : Nat) :
    ∃ s', runBlock isa [.mov r (.mem (memOp .ebp (wordOff i)))] s = some s' ∧
      s'.gpr r = (v.getD (i % 4) 0).setWidth 32 ∧ Keep [r] s s' := by
  have fit := env.scratchFit
  have valid : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i)) 4 := by
    rw [wordOff_mod]; exact env.wordRead _ (Nat.mod_lt _ (by decide))
  refine ⟨s.setReg r ((v.getD (i % 4) 0).setWidth 32), ?_, gpr_setReg_self _ _ _, ?_⟩
  · rw [runBlock_cons, exec_load s r .ebp (wordOff i)
      (by simp only [wordOff]; have := Nat.mod_lt i (by decide : 0 < 4); omega) valid,
      wordOff_mod, hv _ (Nat.mod_lt _ (by decide)), runStep_some, runBlock_nil]
  · exact ⟨fun _ hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem mashInput_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (env : RoundEnv s) (i : Nat) :
    WP isa (.block (mashInput i)) s (fun s' =>
      s'.gpr .eax = (v.getD ((i + 3) % 4) 0).setWidth 32 ∧ s'.gpr .edi = arg s 0 ∧
      Keep [.eax, .edi] s s') := by
  change WP isa (.block (([.mov .eax (.mem (memOp .ebp (wordOff (i + 3))))] : List Instr) ++
    [.mov .edi (.mem (memOp .esp 4))])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := loadScratchWord_ok s v hv env .eax (i + 3)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := loadArg_ok s₁ .edi 0
    (by rw [keep₁.rd, keep₁.wr, argAddr_keep keep₁ (by decide)]; exact env.stackRead)
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
      s'.gpr .edx = (mashResult d x k).setWidth 32 ∧ Keep [.edx] s s' := by
  cases d <;> refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags, ite_true, ite_false]
    rfl, ?_⟩
  all_goals
    constructor
    · rw [gpr_setReg_self, hx, hk, Word32.maskWord]
      simp [mashResult, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
    · constructor
      · intro r hr
        have hn : r ≠ .edx := by simpa only [List.mem_singleton] using hr
        simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
      · rfl
      · rfl
      · rfl

theorem mashAdjust_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : MemWords s.mem (wordBase s) v) (env : RoundEnv s) (i : Nat) (hi : i < 4)
    (k : BitVec 16) (hk : s.gpr .eax = k.setWidth 32) :
    WP isa (.block (mashAdjust d i)) s (fun s' =>
      s'.gpr .edx = (mashResult d (v.getD i 0) k).setWidth 32 ∧ Keep [.edx] s s') := by
  change WP isa (.block (([.mov .edx (.mem (memOp .ebp (wordOff i)))] : List Instr) ++
    [if d == .decrypt then .alu .sub .edx (.reg .eax) else .alu .add .edx (.reg .eax),
      .alu .and .edx (.imm 65535)])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := loadScratchWord_ok s v hv env .edx i
  rw [Nat.mod_eq_of_lt hi] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := mashAdjustReg_ok d s₁ _ k out₁ ((keep₁.reg .eax (by decide)).trans hk)
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
    (v : Spec.Rc2.State) : mashSpec d k i v = v.set! i
      (mashResult d (v.getD i 0) (k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0)) := by
  cases d <;> rfl

theorem mash_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : MemWords s.mem (wordBase s) v) (env : RoundEnv s) (i : Nat) (hi : i < 4) :
    WP isa (.block (mash d i)) s (fun s' =>
      MemWords s'.mem (wordBase s') (mashSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) i v) ∧
      RoundFrame s s') := by
  rw [mash, List.append_assoc, List.append_assoc, WP.block_append_iff]
  apply WP.mono (mashInput_ok s v hv env i)
  intro s₁ ⟨index₁, key₁, keep₁⟩
  rw [WP.block_append_iff]
  apply WP.mono (keyLookup_ok s₁ (by rw [key₁]; exact env.keyFit)
    (by rw [keep₁.rd, keep₁.wr, key₁]; exact env.keyRead))
  intro s₂ h₂
  have k₁ : Keep roundWrites s s₁ := keep₁.weaken (by decide)
  have k₂ : Keep roundWrites s₁ s₂ := h₂.2.weaken (by decide)
  have keep := k₁.trans k₂
  have frame := RoundFrame.of_keep keep
  have env₂ := frame.env env
  have words₂ : MemWords s₂.mem (wordBase s₂) v := by rw [keep.mem, frame.base]; exact hv
  have key₂ : s₂.gpr .eax = ((Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))).getD
      ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0).setWidth 32 := by
    rw [h₂.1, keep₁.mem, key₁, index₁, indexWord]
  rw [WP.block_append_iff]
  apply WP.mono (mashAdjust_ok d s₂ v words₂ env₂ i hi _ key₂)
  intro s₃ h₃
  have k₃ : Keep roundWrites s₂ s₃ := h₃.2.weaken (by decide)
  have frame₃ := frame.trans (RoundFrame.of_keep k₃)
  obtain ⟨s₄, run₄, mem₄, frame₄⟩ := storeWord32_ok s₃ .edx i hi (frame₃.env env)
  refine WP.of_runBlock ⟨s₄, run₄, ?_, frame₃.trans frame₄⟩
  rw [frame₄.base, frame₃.base, mem₄, frame₃.base, h₃.1, h₃.2.mem, keep.mem, mashSpec_eq]
  exact hv.update i hi _

end VG.Proof.Rc2.X86

end

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), MemWords s.mem (wordBase s) v → RoundEnv s →
      WP isa (.block (code i)) s (fun s' =>
        MemWords s'.mem (wordBase s') (step (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) i v) ∧ RoundFrame s s'))
    (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (env : RoundEnv s) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      MemWords s'.mem (wordBase s') (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) i v) v) ∧
      RoundFrame s s') := by
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

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (j : Nat) (hj : j < 16)
    (env : RoundEnv s) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      MemWords s'.mem (wordBase s') (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j v) ∧
      RoundFrame s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound := List.mem_range.mp hi
  exact mixStep_ok .encrypt s v hv env i (4 * j + i) bound (by omega)

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (j : Nat) (hj : j < 16)
    (env : RoundEnv s) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      MemWords s'.mem (wordBase s') (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j v) ∧
      RoundFrame s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  exact mixStep_ok .decrypt s v hv env i (4 * j + i) bound (by omega)

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (env : RoundEnv s) :
    WP isa (.block ((order d).flatMap (mash d))) s (fun s' =>
      MemWords s'.mem (wordBase s') (mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) v) ∧
      RoundFrame s s') := by
  have he (k : Spec.Rc2.Schedule) : mashRoundSpec d k v =
      (order d).foldl (fun v i => mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply foldWords_ok (step := fun k i v => mashSpec d k i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  exact mash_ok d s v hv env i bound

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (j : Nat) (hj : j < 16)
    (env : RoundEnv s) :
    WP isa (.block (round d j)) s (fun s' =>
      MemWords s'.mem (wordBase s') (roundSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j v) ∧
      RoundFrame s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : MemWords s₁.mem (wordBase s₁) v₁ ∧ RoundFrame s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        MemWords s₂.mem (wordBase s₂) (if j = 4 ∨ j = 10 then mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) v₁
          else v₁) ∧ RoundFrame s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      apply WP.mono (mashRound_ok d s₁ v₁ h₁.1 (h₁.2.env env))
      intro s₂ h₂
      rw [h₁.2.schedule env] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (mixRound_ok s v hv j hj env)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (reverseMixRound_ok s v hv (15 - j) (by omega) env)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (env : RoundEnv s) :
    WP isa (.block ((List.range 16).flatMap (round d))) s (fun s' =>
      MemWords s'.mem (wordBase s') ((List.range 16).foldl (fun v j => roundSpec d
        (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j v) v) ∧ RoundFrame s s') := by
  apply foldWords_ok (step := fun k j v => roundSpec d k j v) _ _ _ s v hv env
  intro j hj s v hv env
  exact round_ok d s v hv j (List.mem_range.mp hj) env

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
    (writable : InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ s', runBlock isa (loadWord i) s = some s' ∧
      Keep [.eax, .edx] {s with mem := (s.mem.writeW (wordBase s + BitVec.ofNat 64 (4 * i))
        (((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD i 0).setWidth 32))} s' := by
  have lo := readable (2 * i) (by omega)
  have high := readable (2 * i + 1) (by omega)
  have a := addr_add (x := s.gpr .edi) (k := 2 * i) (by omega)
  have b := addr_add (x := s.gpr .edi) (k := 2 * i + 1) (by omega)
  have c : addr32 (s.gpr .ebp + BitVec.ofNat 32 (wordOff i)) = wordBase s + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega), wordOff_eq s i hi]
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, loadWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, State.ea, memOp, State.load8, State.store32,
      ← addr_eq_def, a, b, c, lo, high, writable, 
      Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags, gpr_arithFlags,
      mem_setReg, mem_setFlags, mem_arithFlags, rd_setReg, rd_setFlags, rd_arithFlags,
      wr_setReg, wr_setFlags, wr_arithFlags]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr.1, hr.2, ite_false]
  · rw [decode_word _ _ i hi, Word32.joinBytes]
  · rfl
  · rfl

theorem loadBlockWords_ok (n : Nat) (hn : n ≤ 4) (s : State)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1)
    (writable : ∀ i < 4, InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (addr32 (s.gpr .edi)) 8).Disjoint ⟨wordBase s, 16⟩) :
    WP isa (.block ((List.range n).flatMap loadWord)) s (fun s' =>
      Keep [.eax, .edx] {s with mem := (saveMem s.mem (wordBase s)
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
    have base₁ : wordBase s₁ = wordBase s := by unfold wordBase; rw [scratch₁]
    have frame₁ : Frame [⟨wordBase s, 16⟩] s.mem s₁.mem := by
      rw [keep₁.mem]
      exact saveMem_frame_le _ _ _ n 4 (by omega) (by decide)
    have block₁ : Spec.Rc2.blockAt s₁.mem (addr32 (s₁.gpr .edi)) = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)) := by
      rw [ptr₁]
      exact blockAt_frame frame₁ _ (by simpa using sep)
    obtain ⟨s₂, run₂, keep₂⟩ := loadWord_ok s₁ n (by omega)
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
    (writable : ∀ i < 4, InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (addr32 (s.gpr .edi)) 8).Disjoint ⟨wordBase s, 16⟩) :
    WP isa (.block ((List.range 4).flatMap loadWord)) s (fun s' =>
      MemWords s'.mem (wordBase s') (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))) ∧
      RoundFrame s s') := by
  apply WP.mono (loadBlockWords_ok 4 (by decide) s fit scratchFit readable writable sep)
  intro s' h
  have base : wordBase s' = wordBase s := by unfold wordBase; rw [h.reg .ebp (by decide)]
  constructor
  · intro i hi
    rw [base, h.mem]
    exact saveMem_read s.mem (wordBase s)
      (fun j => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD j 0).setWidth 32)
      4 (by decide) i hi
  · refine ⟨fun r hr => h.reg r (fun hm => hr ((by decide : ∀ r ∈ [.eax, .edx], r ∈ roundWrites) r hm)),
      h.rd, h.wr, ?_⟩
    rw [h.mem]
    exact saveMem_frame s.mem (wordBase s)
      (fun j => ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .edi)))).getD j 0).setWidth 32)
      4 (by decide)

end VG.Proof.Rc2.X86

end

section

/-! # Writing the four RC2 words as little-endian bytes -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.WriteBytes VG.Proof.Rc2.Word32

theorem storeWord_ok (s : State) (i : Nat) (hi : i < 4) (v : BitVec 16)
    (value : s.mem.readW (wordBase s + BitVec.ofNat 64 (4 * i)) 32 = v.setWidth 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
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
  have c : addr32 (s.gpr .ebp + BitVec.ofNat 32 (wordOff i)) = wordBase s + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega), wordOff_eq s i hi]
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, and_self, storeWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, execShift, readSrc, State.ea, memOp, Reg8.reg, State.load32, State.store8,
      ← addr_eq_def, a, b, c, lo, high, readable, value, 
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

theorem storeWords_ok (n : Nat) (hn : n ≤ 4) (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (wordBase s) 16).Disjoint ⟨addr32 (s.gpr .edi), 8⟩)
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
    have base₁ : wordBase s₁ = wordBase s := by unfold wordBase; rw [scratch₁]
    have frame₁ : Frame [⟨addr32 (s.gpr .edi), 8⟩] s.mem s₁.mem := by
      rw [keep₁.mem]
      exact writeBytes_frame _ _ _ (by
        simpa only [BitVec.add_zero] using Offset.contains_base (addr32 (s.gpr .edi))
          (d := 0) (n := (outputBytes v n).length) (by rw [outputBytes_length]; omega) (by decide))
    have val₁ : s₁.mem.readW (wordBase s₁ + BitVec.ofNat 64 (4 * n)) 32 = (v.getD n 0).setWidth 32 := by
      rw [base₁, frame₁.readW (r := ⟨wordBase s, 16⟩)
        (Offset.contains_base _ (by omega) (by omega)) (by simpa using sep) (by decide)]
      exact hv n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := storeWord_ok s₁ n (by omega) _ val₁
      (by rw [scratch₁]; exact scratchFit)
      (by rw [keep₁.rd, keep₁.wr, base₁]; exact readable n (by omega))
      (by rw [ptr₁]; exact fit) (by rw [keep₁.wr, ptr₁]; exact writable)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, keep₁.mem, ptr₁, outputBytes_write _ _ _ n (by omega)]

theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (fit : (s.gpr .edi).toNat + 8 ≤ 2 ^ 32)
    (scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4)
    (sep : (Region.mk (wordBase s) 16).Disjoint ⟨addr32 (s.gpr .edi), 8⟩)
    (writable : ∀ j < 8, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range 4).flatMap storeWord)) s (fun s' =>
      Keep [.eax] {s with mem := s.mem.writeW (addr32 (s.gpr .edi)) (pack v)} s') := by
  apply WP.mono (storeWords_ok 4 (by decide) s v hv fit scratchFit readable sep writable)
  intro s' h
  rw [outputBytes_pack] at h
  exact h

end VG.Proof.Rc2.X86

end

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem argContainsCount (s : State) (count : Nat) (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (i : Nat) (hi : i < count) :
    (Region.mk (argAddr s 0) (4 * count)).Contains
      (addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i)) 4 := by
  rw [argAddr_eq s 0 (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arguments_frame (count : Nat) {s s' : State} {rs : List Region}
    (frame : Frame rs s.mem s'.mem) (sp : s'.gpr .esp = s.gpr .esp)
    (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (sep : ∀ r ∈ rs, (Region.mk (argAddr s 0) (4 * count)).Disjoint r) :
    ∀ i < count, arg s' i = arg s i := by
  intro i hi
  unfold arg
  have e : argAddr s' i = argAddr s i := by unfold argAddr; rw [sp]
  rw [e, argAddr_eq s i (by omega)]
  exact frame.readW (argContainsCount s count fit i hi) sep (by decide)

theorem pinBlock_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (argAddr s 1) 4) :
    ∃ s', runBlock isa [rr .ebp .eax, .mov .edi (.mem (memOp .esp 8))] s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .edi = arg s 1 ∧ Keep [.ebp, .edi] s s' := by
  simp only [argAddr, Nat.reduceMul, Nat.reduceAdd] at readable
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, rr, memOp, State.ea, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load32, Option.map_some,
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
