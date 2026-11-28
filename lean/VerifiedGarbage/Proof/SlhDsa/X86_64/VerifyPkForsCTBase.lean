module

-- separate module: the taint checks of `forsPk`, rebuilt only when its blocks change

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsV
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsV
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on x86-64: `forsPk` is constant time, its blocks

The taint analysis checks each block of `forsPk` from the registers both runs
agree on and the variables of frame 2 both runs hold the same values in
(`fT`, `fT_agree`), for each of the six parameter sets (`P6`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.ForsCT

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (Layout)

/-- The six SHAKE parameter sets' `n`, `a` and `k` (Table 2). -/
def P6 (p : Params) : Prop :=
  (p.n = 16 ∧ p.a = 12 ∧ p.k = 14) ∨ (p.n = 16 ∧ p.a = 6 ∧ p.k = 33) ∨ (p.n = 24 ∧ p.a = 14 ∧ p.k = 17) ∨
    (p.n = 24 ∧ p.a = 8 ∧ p.k = 33) ∨ (p.n = 32 ∧ p.a = 14 ∧ p.k = 22) ∨ (p.n = 32 ∧ p.a = 9 ∧ p.k = 35)

/-- The taint: `rbx` and `rs` public, `rbx` the base of `scratch` (the first
writable region), and the 8-byte variables at the offsets `sl` public. -/
def fT (rs : List Reg) (sl : List Nat) : X86_64.Taint.T :=
  { regs := .ofList (.rbx :: rs), flags := false, lens := [65536, 0], bases := [(.rbx, 0, 0)],
    slots := sl.map fun o => (0, o, 8) }

/-- Byte `j` of a word. -/
theorem fbyte_readW64 (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← VG.Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

theorem fT_agree {rs : List Reg} {sl : List Nat} {S : Addr} {s₁ s₂ : State}
    (hw₁ : s₁.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]) (hw₂ : s₂.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩])
    (hb₁ : s₁.gpr .rbx = S) (hb₂ : s₂.gpr .rbx = S) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsl : ∀ o ∈ sl, o + 8 ≤ 65536)
    (hm : ∀ o ∈ sl, s₁.mem.readW (at' S o) 64 = s₂.mem.readW (at' S o) 64) :
    X86_64.Taint.Agree (fT rs sl) s₁ s₂ := by
  have hd : Region.Disjoint ⟨S, scratchLen⟩ ⟨S, 0⟩ := fun _ _ h => by
    simp only [Region.Contains] at h; omega
  have wf : ∀ {s : State}, s.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩] → s.gpr .rbx = S → X86_64.Taint.Wf (fT rs sl) s :=
    fun hw hb => by
      refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
      · rw [hw]; exact .cons (by show 65536 ≤ scratchLen; decide) (.cons (Nat.le_refl _) .nil)
      · rw [hw]; exact List.pairwise_pair.mpr hd
      · rw [hw]; intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · show scratchLen ≤ 2 ^ 64; decide
        · show 0 ≤ 2 ^ 64; decide
      · simp only [fT, List.mem_singleton] at hq; subst hq
        simp only [X86_64.Taint.region, hw, List.getD_cons_zero]
        rw [hb, BitVec.add_zero]
  have hba : ∀ {s : State}, s.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩] → ∀ k, X86_64.Taint.byteAddr s 0 k = at' S k :=
    fun hw k => by simp only [Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_zero]
  refine ⟨⟨fun r h => ?_, fun hf => by cases hf⟩, fun _ => by rw [hw₁, hw₂], wf hw₁ hb₁, wf hw₂ hb₂,
    fun q hq => ?_, fun q hq k hk₁ hk₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_cons.mp (RegSet.mem_ofList.mp h) with rfl | h
    · rw [hb₁, hb₂]
    · exact hr r h
  · simp only [fT, List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    simpa [fT] using hsl o ho
  · simp only [fT, List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    simp only at hk₁ hk₂
    have e : at' S k = at' S o + BitVec.ofNat 64 (k - o) := by
      rw [at', at', BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [hba hw₁, hba hw₂, e, fbyte_readW64 s₁.mem _ (show k - o < 8 by omega),
      fbyte_readW64 s₂.mem _ (show k - o < 8 by omega), hm o ho]

/-- Code the taint analysis checks from `fT rs sl`. -/
theorem taintF {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (sl : List Nat)
    (hp : ∀ x y, P x y → X86_64.Taint.Agree (fT rs sl) x y) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (fT rs sl) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (fT rs sl) hp h

section
variable {P : State → State → Prop} {p : Params} (hp : P6 p)
include hp

/-- The prologue and the indices. -/
theorem ct_fpro (h : ∀ x y, P x y → ∀ r ∈ [Reg.rdi], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Fors.pro ++ Impl.SlhDsa.X86_64.Fors.indices p.a p.k)) fun _ _ => True := by
  rcases hp with ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ <;> rw [ha, hk] <;>
    exact Levels.taintR _ h (by taint_decide)

/-- The leaves' block. -/
theorem ct_leaves (h : ∀ x y, P x y → X86_64.Taint.Agree (fT [.r14] [Layout.oVar 2 0]) x y) :
    RelCT isa P (.block ((List.range 4).flatMap fun k' => Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
      Impl.SlhDsa.X86_64.setField .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 3 ++
      Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      Impl.SlhDsa.X86_64.setField .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
      Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11 ++
      Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8)))
      fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Verify.treeOf, Impl.SlhDsa.X86_64.Shake.layout, Impl.SlhDsa.X86_64.Layout.adrsOff,
    Impl.SlhDsa.X86_64.Layout.msgOff]
  rcases hp with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    rw [hn, ha, hk] <;> exact taintF _ _ h (by taint_decide)

/-- The first block of a lane's height: its tree, its leaf's bit, the path's node. -/
theorem ct_uhead {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → X86_64.Taint.Agree (fT [.r14] [Layout.oVar 2 0, Layout.oVar 2 1]) x y) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.treeOf p k' ++ ([.mov .rcx (.mem (Impl.SlhDsa.X86_64.Fors.var 1)),
      .mov .rax (.reg .r11), .shiftCl .shr .rax, .mov .rdx (.mem (Impl.SlhDsa.X86_64.Fors.var 1))] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rsi (.reg .rdx),
      .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)), .alu .and .rax (.imm 1)] : List Instr))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Verify.treeOf]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hp with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    rw [hn, ha, hk] <;> exact taintF _ _ h (by taint_decide)

/-- A lane's copies when bit `z` is 0. -/
theorem ct_ucopy0 {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rsi], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n)
      .rsi 0 (p.n / 8))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Shake.layout, Impl.SlhDsa.X86_64.Layout.msgOff]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    rw [hn] <;> exact Levels.taintR _ h (by taint_decide)

/-- A lane's copies when bit `z` is 1. -/
theorem ct_ucopy1 {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .rsi], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n)
      .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8) ++
      Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8)))
      fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Shake.layout, Impl.SlhDsa.X86_64.Layout.msgOff]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    rw [hn] <;> exact Levels.taintR _ h (by taint_decide)

/-- A lane's height `z + 1` and tree index. -/
theorem ct_ufields {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → X86_64.Taint.Agree (fT [] [Layout.oVar 2 1]) x y) :
    RelCT isa P (.block (([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Fors.var 1)), .alu .add .r10 (.imm 1)] : List Instr) ++
        Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        ([.mov .rcx (.reg .r10), .shiftCl .shr .r11] : List Instr) ++
        Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11))
      fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Shake.layout, Impl.SlhDsa.X86_64.Layout.adrsOff]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    rw [hn] <;> exact taintF _ _ h (by taint_decide)

/-- Lane `k`'s root, to lane 0 of `B`. -/
theorem ct_root {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → X86_64.Taint.Agree (fT [] [Layout.oVar 2 0]) x y) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
        ([.mov .rdx (.reg .r10)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        Impl.SlhDsa.X86_64.copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
          (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Verify.treeOf, Impl.SlhDsa.X86_64.Shake.layout, Impl.SlhDsa.X86_64.Layout.msgOff]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hp with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    rw [hn, ha, hk] <;> exact taintF _ _ h (by taint_decide)

/-- `pkFors`'s fields. -/
theorem ct_pkf (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 4 ++
      Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
      Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) 0))
      fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Shake.layout, Impl.SlhDsa.X86_64.Layout.adrsOff]
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    rw [hn] <;> exact Levels.taintR _ h (by taint_decide)

/-- `pkFors`'s copy to `oMsg`, and the epilogue. -/
theorem ct_pkc (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r15], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.copyWords .r15 0 .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff)
      (p.n / 8))) fun _ _ => True := by
  simp only [Impl.SlhDsa.X86_64.Shake.layout, Impl.SlhDsa.X86_64.Layout.msgOff]
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    rw [hn] <;> exact Levels.taintR _ h (by taint_decide)

/-- The arguments of a call of `thash4` on the lanes `A` or `B`. -/
theorem ct_fargs {o st : Nat} (hl' : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (len : Nat) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ o st len)) fun _ _ => True := by
  rcases hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hp with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;> rw [hn] <;>
    exact Levels.taintR _ h (hc := .block []) (by kernel_rfl)

end

section
variable {P : State → State → Prop}

/-- Variable 1 ← 0. -/
theorem ct_v1z (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Fors.var 1) .rax]) fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

/-- The last block of a height. -/
theorem ct_ufin (a : Nat) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Fors.var 1)), .alu .add .rax (.imm 1),
      .store (Impl.SlhDsa.X86_64.Fors.var 1) .rax, .alu .cmp .rax (.imm (BitVec.ofNat 32 a))]) fun _ _ => True :=
  Levels.taintR _ h (hc := .block []) (by kernel_rfl)

/-- The epilogue. -/
theorem ct_rest (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.restoreRegs 2)) fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

/-- The last block of a group. -/
theorem ct_rfin (k : Nat) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Fors.var 0)), .alu .add .rax (.imm 4),
        .store (Impl.SlhDsa.X86_64.Fors.var 0) .rax, .alu .cmp .rax (.imm (BitVec.ofNat 32 k))] : List Instr))
      fun _ _ => True :=
  Levels.taintR _ h (hc := .block []) (by kernel_rfl)

end

end VG.Proof.SlhDsa.X86_64.ForsCT
