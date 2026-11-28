module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopPro
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCTBase
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopPro
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCTBase
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: its blocks are constant time

Untrusted: everything here is checked by Lean. The taint analysis, from the
public registers each block's addresses use, checks every block of
`verify` (`ct_*`); the frame's prologue loads `scratch` and the key from the
frame's public slots (`proT`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (Layout)

/-- The taint of the prologue: `rsp` the base of the frame, whose slots of
`scratch` and the key are public. -/
def proT : X86_64.Taint.T :=
  { regs := .ofList [.rsp], flags := false, lens := [72, 65536], bases := [(.rsp, 0, 0)],
    slots := [(0, 8, 8), (0, 64, 8)] }

/-- The arguments of `hashM'`'s calls. -/
def verifyArgLists (p : Params) : List (List Impl.SlhDsa.X86_64.Shake.Arg) :=
  [[.scr Layout.oStream, .imm 136, .imm (p.n * 0), .slot Impl.SlhDsa.X86_64.Verify.fVSig, .imm p.n,
      .scr (Layout.oStream + 200)],
    [.scr Layout.oStream, .imm 136, .imm (p.n * (0 + 1)), .scr Layout.oPkSeed, .imm p.n, .scr (Layout.oStream + 200)],
    [.scr Layout.oStream, .imm 136, .imm (p.n * (0 + 1 + 1)), .scr Layout.oPkRoot, .imm p.n,
      .scr (Layout.oStream + 200)],
    [.scr Layout.oStream, .imm 136, .imm (p.n * (0 + 1 + 1 + 1)), .sp, .imm 2, .scr (Layout.oStream + 200)],
    [.scr Layout.oStream, .imm 136, .ret, .slot Impl.SlhDsa.X86_64.Shake.fCtx, .slot Impl.SlhDsa.X86_64.Shake.fCtxLen,
      .scr (Layout.oStream + 200)],
    [.scr Layout.oStream, .imm 136, .ret, .slot Impl.SlhDsa.X86_64.Shake.fMsg, .slot Impl.SlhDsa.X86_64.Shake.fLen,
      .scr (Layout.oStream + 200)],
    [.scr Layout.oStream, .imm 136, .ret, .imm 0x1f, .scr (Layout.oStream + 200)],
    [.scr Layout.oStream, .imm 136, .imm 0, .scr Layout.oDigest, .imm p.m, .scr (Layout.oStream + 200)]]

theorem ct_top1 {P : State → State → Prop} (h : ∀ x y, P x y → ∀ r ∈ [Reg.rsp], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .r10 (.mem (Impl.SlhDsa.X86_64.Shake.stk 8)), .mov .r11 (.mem (Impl.SlhDsa.X86_64.Shake.stk 16)),
      .mov32 .rax (.imm 0), .alu .cmp .r8 (.imm 256)]) fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

theorem ct_zero {P : State → State → Prop} (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block Impl.SlhDsa.X86_64.Shake.zeroState) fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

theorem ct_res1 {P : State → State → Prop} :
    RelCT isa P (.block [.mov32 .rax (.imm 1)]) fun _ _ => True :=
  Levels.taintR [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)

theorem ct_res0 {P : State → State → Prop} :
    RelCT isa P (.block [.mov32 .rax (.imm 0)]) fun _ _ => True :=
  Levels.taintR [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)

theorem ct_epi {P : State → State → Prop} (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (.mov .r10 (.reg .rax) :: Impl.SlhDsa.X86_64.Shake.kgRestore ++ ([.mov .rax (.reg .r10)] : List Instr)))
      fun _ _ => True :=
  Levels.taintR _ h (by taint_decide)

/-- Two runs after the frame's push, with the same layout, agree on the prologue's taint. -/
theorem pushed_agree {L : VL} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} {a b : State}
    (ha : Pushed L g₁ m₁ a) (hb : Pushed L g₂ m₂ b) : X86_64.Taint.Agree proT a b := by
  have hd : Region.Disjoint L.FR L.SCR := by
    have := hL.fr_scr (d := 0) (n := 72) (by omega); simpa using this
  have wf : ∀ {g m₀} {s : State}, Pushed L g m₀ s → X86_64.Taint.Wf proT s := fun hs => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun q hq => ?_⟩
    · rw [hs.wr]; exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
    · rw [hs.wr]; exact List.pairwise_pair.mpr hd
    · rw [hs.wr]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 72 ≤ 2 ^ 64; decide
      · show 65536 ≤ 2 ^ 64; decide
    · simp only [proT, List.mem_singleton] at hq; subst hq
      simp only [X86_64.Taint.region, hs.wr, List.getD_cons_zero]
      rw [hs.rsp, BitVec.add_zero]
  have hba : ∀ {g m₀} {s : State}, Pushed L g m₀ s → ∀ k, X86_64.Taint.byteAddr s 0 k = L.SP + BitVec.ofNat 64 k :=
    fun hs k => by simp only [Taint.byteAddr, X86_64.Taint.region, hs.wr, List.getD_cons_zero]
  refine ⟨⟨fun r h => ?_, fun hf => by cases hf⟩, fun _ => by rw [ha.wr, hb.wr], wf ha, wf hb,
    fun q hq => ?_, fun q hq k hk₁ hk₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_cons.mp (RegSet.mem_ofList.mp h) with rfl | h
    · rw [ha.rsp, hb.rsp]
    · simp at h
  · simp only [proT, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> decide
  · simp only [proT, List.mem_cons, List.not_mem_nil, or_false] at hq
    have sl : ∀ j (hj : j < 9), a.mem.readW (L.SP + BitVec.ofNat 64 (8 * j)) 64 =
        b.mem.readW (L.SP + BitVec.ofNat 64 (8 * j)) 64 := fun j hj => (ha.slot j hj).trans (hb.slot j hj).symm
    rcases hq with rfl | rfl <;> simp only at hk₁ hk₂
    · have e : L.SP + BitVec.ofNat 64 k = L.SP + BitVec.ofNat 64 (8 * 1) + BitVec.ofNat 64 (k - 8) :=
        ((BitVec.add_assoc L.SP _ _).trans (by rw [BitVec.ofNat_add_ofNat, show 8 * 1 + (k - 8) = k by omega])).symm
      rw [hba ha, hba hb, e, ForsCT.fbyte_readW64 a.mem _ (show k - 8 < 8 by omega),
        ForsCT.fbyte_readW64 b.mem _ (show k - 8 < 8 by omega), sl 1 (by omega)]
    · have e : L.SP + BitVec.ofNat 64 k = L.SP + BitVec.ofNat 64 (8 * 8) + BitVec.ofNat 64 (k - 64) :=
        ((BitVec.add_assoc L.SP _ _).trans (by rw [BitVec.ofNat_add_ofNat, show 8 * 8 + (k - 64) = k by omega])).symm
      rw [hba ha, hba hb, e, ForsCT.fbyte_readW64 a.mem _ (show k - 64 < 8 by omega),
        ForsCT.fbyte_readW64 b.mem _ (show k - 64 < 8 by omega), sl 8 (by omega)]

section
variable {P : State → State → Prop} {p : Params} (hS : S6 p)
include hS

theorem ct_cmpSig (h : ∀ x y, P x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r) :
    RelCT isa P (.block [.alu .cmp .r10 (.imm (BitVec.ofNat 32 p.sigLen))]) fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ h (by taint_decide)

/-- The moves of a sponge function's arguments. -/
theorem ct_args (as : List Impl.SlhDsa.X86_64.Shake.Arg)
    (has : as ∈ verifyArgLists p) (h : ∀ x y, P x y → ∀ r ∈ [Reg.rsp, .rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip as).flatMap fun (d, a) => a.mov d))
      fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [verifyArgLists, List.mem_cons, List.not_mem_nil, or_false] at has
    rcases has with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ h (by taint_decide)

theorem ct_b2 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rsp, .rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (Impl.SlhDsa.X86_64.Verify.vParseIdx p ++
        ([.mov32 .r10 (.imm 0), .mov .r9 (.mem (Impl.SlhDsa.X86_64.Verify.vvar 0))] : List Instr) ++
        Impl.SlhDsa.X86_64.Shake.treeLanes p .r10 .r9 ++ ([.mov .rdi (.reg .rbx),
          .mov .rsi (.mem (Impl.SlhDsa.X86_64.Shake.stk Impl.SlhDsa.X86_64.Verify.fVSig)),
          .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)), .mov .rdx (.mem (Impl.SlhDsa.X86_64.Verify.vvar 1))] : List Instr)))
      fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ h (by taint_decide)

theorem ct_b3 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rsp, .rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Verify.vvar 2) .rax,
        .mov .rax (.mem (Impl.SlhDsa.X86_64.Shake.stk Impl.SlhDsa.X86_64.Verify.fVSig)),
        .alu .add .rax (.imm (BitVec.ofNat 32 (p.n + p.forsSigLen))), .store (Impl.SlhDsa.X86_64.Verify.vvar 3) .rax])
      fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ h (by taint_decide)

theorem ct_lb1 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.vvar 2)),
        .mov .r9 (.mem (Impl.SlhDsa.X86_64.Verify.vvar 0))] : List Instr) ++ Impl.SlhDsa.X86_64.Shake.treeLanes p .r10 .r9 ++
        ([.mov .rdi (.reg .rbx), .mov .rsi (.mem (Impl.SlhDsa.X86_64.Verify.vvar 1)),
          .mov .rdx (.mem (Impl.SlhDsa.X86_64.Verify.vvar 3))] : List Instr))) fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ h (by taint_decide)

theorem ct_lb2 (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block [.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.vvar 3)),
        .alu .add .rax (.imm (BitVec.ofNat 32 p.xmssSigLen)), .store (Impl.SlhDsa.X86_64.Verify.vvar 3) .rax,
        .mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.vvar 0)), .mov .rcx (.reg .rax),
        .alu .and .rcx (.imm (BitVec.ofNat 32 (2 ^ p.hp - 1))),
        .store (Impl.SlhDsa.X86_64.Verify.vvar 1) .rcx, .shift .shr .rax p.hp, .store (Impl.SlhDsa.X86_64.Verify.vvar 0) .rax,
        .mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.vvar 2)), .alu .add .rax (.imm 1),
        .store (Impl.SlhDsa.X86_64.Verify.vvar 2) .rax, .alu .cmp .rax (.imm (BitVec.ofNat 32 p.d))]) fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ h (by taint_decide)

theorem ct_cmp (h : ∀ x y, P x y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) :
    RelCT isa P (.block (.mov32 .rax (.imm 0) :: (List.range (p.n / 8)).flatMap (fun w =>
        [.mov .rcx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oMsg + 8 * w))),
          .alu .xor .rcx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oPkRoot + 8 * w))),
          .alu .or .rax (.reg .rcx)]) ++ ([.alu .test .rax (.reg .rax)] : List Instr))) fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR _ h (by taint_decide)

theorem ct_pro (h : ∀ x y, P x y → X86_64.Taint.Agree proT x y) :
    RelCT isa P (.block (proCode p)) fun _ _ => True := by
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact RelCT.taint (A := taint) proT h (by taint_decide)

end

end VG.Proof.SlhDsa.X86_64.VerifyTop
