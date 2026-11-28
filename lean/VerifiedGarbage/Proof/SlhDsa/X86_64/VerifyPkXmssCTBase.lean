module
-- separate module: the taint checks of `xmssPk`'s parts, which a change to its relational proof need not rebuild

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmssV
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmssV
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on x86-64: `xmssPk` is constant time, its parts

The taint analysis checks each part of `xmssPk` between its calls, from the
registers both runs agree on and the variables of its frame both runs hold
the same values in (`xT`, `xT_agree`): what each run holds there comes from
its correctness (`VerifyPkXmssCT.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.XmssCT

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (Layout)

/-- The parameters of the code: those of `p` but `n` and `h′` play no part
in it, and `len` follows from `n` and `lg_w = 4`. -/
def cp (n hp : Nat) : Params :=
  { n := n, h := 0, d := 0, hp := hp, a := 0, k := 0, lgw := 4, m := 0, category := 0, family := .shake }

/-- The taint: `rbx` and `rs` public, `rbx` the base of `scratch` (the first
writable region), and the 8-byte variables at the offsets `sl` public. -/
def xT (rs : List Reg) (sl : List Nat) : X86_64.Taint.T :=
  { regs := .ofList (.rbx :: rs), flags := false, lens := [65536, 0], bases := [(.rbx, 0, 0)],
    slots := sl.map fun o => (0, o, 8) }

/-- Byte `j` of a word. -/
theorem byte_readW64 (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← VG.Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

theorem xT_agree {rs : List Reg} {sl : List Nat} {S : Addr} {s₁ s₂ : State}
    (hw₁ : s₁.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩]) (hw₂ : s₂.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩])
    (hb₁ : s₁.gpr .rbx = S) (hb₂ : s₂.gpr .rbx = S) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsl : ∀ o ∈ sl, o + 8 ≤ 65536)
    (hm : ∀ o ∈ sl, s₁.mem.readW (at' S o) 64 = s₂.mem.readW (at' S o) 64) :
    X86_64.Taint.Agree (xT rs sl) s₁ s₂ := by
  have hd : Region.Disjoint ⟨S, scratchLen⟩ ⟨S, 0⟩ := fun _ _ h => by
    simp only [Region.Contains] at h; omega
  have wf : ∀ {s : State}, s.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩] → s.gpr .rbx = S → X86_64.Taint.Wf (xT rs sl) s :=
    fun hw hb => by
      refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
      · rw [hw]; exact .cons (by show 65536 ≤ scratchLen; decide) (.cons (Nat.le_refl _) .nil)
      · rw [hw]; exact List.pairwise_pair.mpr hd
      · rw [hw]; intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · show scratchLen ≤ 2 ^ 64; decide
        · show 0 ≤ 2 ^ 64; decide
      · simp only [xT, List.mem_singleton] at hq; subst hq
        simp only [X86_64.Taint.region, hw, List.getD_cons_zero]
        rw [hb, BitVec.add_zero]
  have hba : ∀ {s : State}, s.wr = [⟨S, scratchLen⟩, ⟨S, 0⟩] → ∀ k, X86_64.Taint.byteAddr s 0 k = at' S k :=
    fun hw k => by simp only [Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_zero]
  refine ⟨⟨fun r h => ?_, fun hf => by cases hf⟩, fun _ => by rw [hw₁, hw₂], wf hw₁ hb₁, wf hw₂ hb₂,
    fun q hq => ?_, fun q hq k hk₁ hk₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_cons.mp (RegSet.mem_ofList.mp h) with rfl | h
    · rw [hb₁, hb₂]
    · exact hr r h
  · simp only [xT, List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    simpa [xT] using hsl o ho
  · simp only [xT, List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    simp only at hk₁ hk₂
    have e : at' S k = at' S o + BitVec.ofNat 64 (k - o) := by
      rw [at', at', BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [hba hw₁, hba hw₂, e, byte_readW64 s₁.mem _ (show k - o < 8 by omega),
      byte_readW64 s₂.mem _ (show k - o < 8 by omega), hm o ho]

/-- Code the taint analysis checks from `xT rs sl`. -/
theorem taintX {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (sl : List Nat)
    (hp : ∀ x y, P x y → X86_64.Taint.Agree (xT rs sl) x y) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (xT rs sl) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (xT rs sl) hp h

/-! ## The parts, for each `n` -/

@[simp] theorem cp_n (n hp : Nat) : (cp n hp).n = n := rfl

theorem cp_len {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32) (hp : Nat) : (cp n hp).len = 2 * n + 3 :=
  len_eq (cp n hp) rfl hn

section
variable {P : State → State → Prop} {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
  (hl : p.len = 2 * p.n + 3)
include hn hl

omit hn in
theorem layout_eq : Impl.SlhDsa.X86_64.Shake.layout p = ⟨p.n, 2 * p.n + 3⟩ := by
  simp only [Impl.SlhDsa.X86_64.Shake.layout, hl]

omit hl in
theorem layout_cp : Impl.SlhDsa.X86_64.Shake.layout (cp p.n 0) = ⟨p.n, 2 * p.n + 3⟩ := by
  simp only [Impl.SlhDsa.X86_64.Shake.layout, cp_n, cp_len hn]

/-- The prologue and the digits. -/
theorem ct_pro (h : ∀ x y, P x y → ∀ r ∈ [Reg.rdi], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.xpro ++ Impl.SlhDsa.X86_64.Xmss.digits (Impl.SlhDsa.X86_64.Shake.layout p) ++
      ([.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Verify.xv 0) .rax] : List Instr))) fun _ _ => True := by
  rw [layout_eq hl]
  rcases hn with h' | h' | h' <;> rw [h'] <;> exact Levels.taintR _ h (by taint_decide)

theorem ct_lanes (h : ∀ x y, P x y → X86_64.Taint.Agree (xT [.r13] [Layout.oVar 1 0]) x y) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.chainLanes p)) fun _ _ => True := by
  have e : Impl.SlhDsa.X86_64.Verify.chainLanes p = Impl.SlhDsa.X86_64.Verify.chainLanes (cp p.n 0) := by
    simp only [Impl.SlhDsa.X86_64.Verify.chainLanes, Impl.SlhDsa.X86_64.Verify.chainOf, Impl.SlhDsa.X86_64.Verify.chainSig, layout_eq hl, layout_cp hn, hl, cp_n, cp_len hn]
  rw [e]
  rcases hn with h' | h' | h' <;> rw [h'] <;> exact taintX _ _ h (by taint_decide)

/-- The first block of a step: the hash addresses. -/
theorem ct_h28 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.xv 1)) :: (List.range 4).flatMap fun k' =>
      Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r10)) fun _ _ => True := by
  rw [layout_eq hl]
  rcases hn with h' | h' | h' <;> rw [h'] <;> exact Levels.taintR _ h (by taint_decide)

/-- The arguments of a call of `thash4` on the lanes `A` or `B`. -/
theorem ct_args {o st : Nat} (hl' : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (len : Nat) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ o st len)) fun _ _ => True := by
  rw [hl]
  rcases hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hn with h' | h' | h' <;> rw [h'] <;>
    exact Levels.taintR _ h (hc := .block []) (by kernel_rfl)

/-- The first block of a lane's restore: its chain and digit, compared with the step. -/
theorem ct_rhead {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → X86_64.Taint.Agree (xT [] [Layout.oVar 1 0]) x y) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.chainOf p k' ++ ([.alu .cmp .r11 (.mem (Impl.SlhDsa.X86_64.Verify.xv 1))] : List Instr))) fun _ _ => True := by
  have e : Impl.SlhDsa.X86_64.Verify.chainOf p k' = Impl.SlhDsa.X86_64.Verify.chainOf (cp p.n 0) k' := by
    simp only [Impl.SlhDsa.X86_64.Verify.chainOf, hl, cp_len hn]
  rw [e]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases hn with h' | h' | h' <;> rw [h'] <;> exact taintX _ _ h (by taint_decide)

/-- A lane's restore of its signature value. -/
theorem ct_rsig {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r10, .r13], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.chainSig p ++ Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0
      (p.n / 8))) fun _ _ => True := by
  rw [layout_eq hl]
  simp only [Impl.SlhDsa.X86_64.Verify.chainSig]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases hn with h' | h' | h' <;> rw [h'] <;> exact Levels.taintR _ h (by taint_decide)

/-- A lane's end, to lane 0 of `B`. -/
theorem ct_end {k' : Nat} (hk : k' < 4) (h : ∀ x y, P x y → X86_64.Taint.Agree (xT [] [Layout.oVar 1 0]) x y) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.chainOf p k' ++ ([.mov .rdx (.reg .r10)] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      Impl.SlhDsa.X86_64.copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
        (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8))) fun _ _ => True := by
  have e : Impl.SlhDsa.X86_64.Verify.chainOf p k' = Impl.SlhDsa.X86_64.Verify.chainOf (cp p.n 0) k' := by
    simp only [Impl.SlhDsa.X86_64.Verify.chainOf, hl, cp_len hn]
  rw [e, layout_eq hl]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases hn with h' | h' | h' <;> rw [h'] <;> exact taintX _ _ h (by taint_decide)

/-- The fields of `wotsPk`'s address. -/
theorem ct_wf (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 1 ++
      Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
      Impl.SlhDsa.X86_64.setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) 0)) fun _ _ => True := by
  rw [layout_eq hl]
  rcases hn with h' | h' | h' <;> rw [h'] <;> exact Levels.taintR _ h (by taint_decide)

/-- `wotsPk`'s copy of its key. -/
theorem ct_wcp (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
      (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8))) fun _ _ => True := by
  rw [layout_eq hl]
  rcases hn with h' | h' | h' <;> rw [h'] <;> exact Levels.taintR _ h (by taint_decide)

/-- A height of the path, up to its call: the node and the path's node in
their order, and the address. -/
theorem ct_ppre (h : ∀ x y, P x y → X86_64.Taint.Agree (xT [.r12, .r13] [Layout.oVar 1 3]) x y) :
    RelCT isa P (.seq (.seq (.block (([.mov .rcx (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .mov .rax (.reg .r12), .shiftCl .shr .rax,
        .mov .rsi (.reg .rcx)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rsi .rdx ++
        ([.alu .add .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (p.len * p.n))), .alu .and .rax (.imm 1)] : List Instr)))
      (.ite .e
        (.block (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n) .rsi 0 (p.n / 8)))
        (.block (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff + p.n) .rbx
            (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8) ++
          Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8)))))
      (.block (Impl.SlhDsa.X86_64.setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 2 ++
        Impl.SlhDsa.X86_64.setField .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) 0 ++
        ([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .alu .add .r10 (.imm 1)] : List Instr) ++
        Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        ([.mov .rcx (.reg .r10), .mov .r11 (.reg .r12), .shiftCl .shr .r11] : List Instr) ++
        Impl.SlhDsa.X86_64.setFieldR .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11))) fun _ _ => True := by
  rw [layout_eq hl, hl]
  rcases hn with h' | h' | h' <;> rw [h'] <;> exact taintX _ _ h (by taint_decide)

/-- The epilogue: the root to `oMsg`, the registers back. -/
theorem ct_epi (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r14], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.copyWords .r14 0 .rbx (Layout.laneA 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8) ++
      Impl.SlhDsa.X86_64.restoreRegs 1)) fun _ _ => True := by
  rw [layout_eq hl]
  rcases hn with h' | h' | h' <;> rw [h'] <;> exact Levels.taintR _ h (by taint_decide)

end

section
variable {P : State → State → Prop}

/-- The block between a group's lanes and its steps. -/
theorem ct_mid (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .store (Impl.SlhDsa.X86_64.Verify.xv 1) .rax, .alu .cmp .rax (.imm 15)])
      fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

/-- The last block of a group. -/
theorem ct_endfin (len : Nat) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 0)), .alu .add .rax (.imm 4), .store (Impl.SlhDsa.X86_64.Verify.xv 0) .rax,
      .alu .cmp .rax (.imm (BitVec.ofNat 32 len))] : List Instr)) fun _ _ => True :=
  Levels.taintR _ h (hc := .block []) (by kernel_rfl)

/-- The last block of a step. -/
theorem ct_sfin (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 1)), .alu .add .rax (.imm 1), .store (Impl.SlhDsa.X86_64.Verify.xv 1) .rax,
      .alu .cmp .rax (.imm 15)]) fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

/-- Variable 3 ← 0. -/
theorem ct_b4 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Verify.xv 3) .rax]) fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

/-- The last block of a height of the path. -/
theorem ct_pfin (hp : Nat) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 3)), .alu .add .rax (.imm 1), .store (Impl.SlhDsa.X86_64.Verify.xv 3) .rax,
      .alu .cmp .rax (.imm (BitVec.ofNat 32 hp))]) fun _ _ => True :=
  Levels.taintR _ h (hc := .block []) (by kernel_rfl)

end

end VG.Proof.SlhDsa.X86_64.XmssCT
