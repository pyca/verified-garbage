import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.Avx512

/-!
# x86-64: AVX-512 blocks as SSE blocks on each lane

As `LaneSse.lean` for VEX.256: EVEX.512 `vop zmm, zmm, zmm` instructions of
`ZBinOp`, `vpclmulqdq` and `vpshufd` act on each 128-bit lane as an SSE
instruction does on a register, and `vpternlogd` with the immediate `0x96`
(the XOR of its three operands, `ternlog_96`) as two `pxor`s. For a block of them (`zlaneSseBlock`), what it leaves in lane
`l` (of four) of the vector registers is what the corresponding SSE block
leaves in the SSE registers of `s.zproj l`, the state with lane `l` of each
vector register as its SSE register (`WP.zlanes`).
-/

namespace VG.X86_64

/-- `s` with lane `l` (of four) of each vector register as its SSE register,
and no upper halves. -/
def State.zproj (s : State) (l : Nat) : State :=
  { s with xmm := fun r => s.zlane r l, ymmHi := fun _ => 0, zmmHi := fun _ => 0 }

@[simp] theorem State.zproj_xmm (s : State) (l : Nat) (r : XReg) : (s.zproj l).xmm r = s.zlane r l := rfl
@[simp] theorem State.zproj_gpr (s : State) (l : Nat) : (s.zproj l).gpr = s.gpr := rfl
@[simp] theorem State.zproj_mem (s : State) (l : Nat) : (s.zproj l).mem = s.mem := rfl
@[simp] theorem State.zproj_rd (s : State) (l : Nat) : (s.zproj l).rd = s.rd := rfl
@[simp] theorem State.zproj_wr (s : State) (l : Nat) : (s.zproj l).wr = s.wr := rfl
@[simp] theorem State.zproj_mxcsr (s : State) (l : Nat) : (s.zproj l).mxcsr = s.mxcsr := rfl

/-- On lanes 0 and 1, `zproj` is `proj`. -/
theorem State.zproj_eq_proj (s : State) {l : Nat} (hl : l < 2) : s.zproj l = s.proj l := by
  simp only [State.zproj, State.proj, State.zlane, hl, ite_true]

/-- `vpternlogd`'s immediate `0x96` selects the XOR of its three operands. -/
theorem ternlog_96 (a b c : BitVec 128) : ternlog a b c 0x96 = a ^^^ b ^^^ c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ternlog, List.range, List.range.loop, List.foldl, BitVec.reduceGetLsb, Bool.false_eq_true, ↓reduceIte]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    hi, decide_true, Bool.true_and, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.false_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-- The SSE instructions that do to one lane what a lane-wise EVEX.512
instruction does to each, if it is one: `vop d, a, b` is `movdqa d, a` then
`op d, b` (just `op d, b` if `a` is `d`; not if only `b` is); `vpshufd d, r`
is `pshufd d, r`; and `vpternlogd d, a, b, 0x96` is `pxor d, a` then `pxor d,
b`, if neither `a` nor `b` is `d`. -/
def zlaneSseZ : ZOp → Option (List Instr)
  | .zbin op d a b =>
    if a = d then some [.xop (.bin op.sse d b)]
    else if b = d then none else some [.xop (.bin .movdqa d a), .xop (.bin op.sse d b)]
  | .vpclmulqdq d a b n =>
    if a = d then some [.xop (.pclmulqdq d b n)]
    else if b = d then none else some [.xop (.bin .movdqa d a), .xop (.pclmulqdq d b n)]
  | .vpshufd d r o => some [.xop (.pshufd d r o)]
  | .vpternlogd d a b n =>
    if n = 0x96 ∧ a ≠ d ∧ b ≠ d then some [.xop (.bin .pxor d a), .xop (.bin .pxor d b)] else none
  | _ => none

@[inherit_doc zlaneSseZ]
def zlaneSse : Instr → Option (List Instr)
  | .zop o => zlaneSseZ o
  | _ => none

/-- The SSE block of a block of lane-wise EVEX.512 instructions. -/
def zlaneSseBlock : List Instr → Option (List Instr)
  | [] => some []
  | i :: is => match zlaneSse i, zlaneSseBlock is with
    | some a, some b => some (a ++ b)
    | _, _ => none

theorem zproj_setZ (s : State) (d : XReg) (f : Nat → BitVec 128) {l : Nat} (hl : l < 4) :
    (s.setZ d (f 0) (f 1) (f 2) (f 3)).zproj l = (s.zproj l).setXmm d (f l) := by
  have e : ∀ r, (s.setZ d (f 0) (f 1) (f 2) (f 3)).zlane r l = if r = d then f l else s.zlane r l := by
    intro r; rw [State.zlane_setZ _ _ _ _ _ _ _ hl, pick4_lanes f hl]
  unfold State.zproj State.setXmm
  rw [show (fun r => (s.setZ d (f 0) (f 1) (f 2) (f 3)).zlane r l) =
    (fun r' => if r' = d then f l else s.zlane r' l) from funext e]
  cases s; rfl

theorem VKeep.setZ (s : State) (d : XReg) (a b c e : BitVec 128) : VKeep s (s.setZ d a b c e) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zlaneSse_ok {i : Instr} {ss : List Instr} (h : zlaneSse i = some ss) (s : State) :
    ∃ s', exec i s = some s' ∧ VKeep s s' ∧ ∀ l < 4, runBlock isa ss (s.zproj l) = some (s'.zproj l) := by
  cases i
  all_goals try (simp only [zlaneSse, reduceCtorEq] at h)
  rename_i o
  cases o
  all_goals try (simp only [zlaneSseZ, reduceCtorEq] at h)
  case zbin op d a b =>
    refine ⟨_, rfl, VKeep.setZ .., fun l hl => ?_⟩
    rw [show (ZOp.zbin op d a b).exec s = s.setZ d (op.sse.eval (s.zlane a 0) (s.zlane b 0))
      (op.sse.eval (s.zlane a 1) (s.zlane b 1)) (op.sse.eval (s.zlane a 2) (s.zlane b 2))
      (op.sse.eval (s.zlane a 3) (s.zlane b 3)) from rfl,
      zproj_setZ _ _ (fun i => op.sse.eval (s.zlane a i) (s.zlane b i)) hl]
    split at h
    · subst_vars; cases h
      simp only [runBlock, exec, XOp.exec, Option.bind_some, State.zproj_xmm]
    · split at h
      · cases h
      · rename_i h1 h2; cases h
        simp only [runBlock, exec, XOp.exec, Option.bind_some, State.zproj_xmm]
        rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ h2, setXmm_setXmm, eval_movdqa]; rfl
  case vpclmulqdq d a b n =>
    refine ⟨_, rfl, VKeep.setZ .., fun l hl => ?_⟩
    rw [show (ZOp.vpclmulqdq d a b n).exec s = s.setZ d (pclmul (s.zlane a 0) (s.zlane b 0) n)
      (pclmul (s.zlane a 1) (s.zlane b 1) n) (pclmul (s.zlane a 2) (s.zlane b 2) n)
      (pclmul (s.zlane a 3) (s.zlane b 3) n) from rfl,
      zproj_setZ _ _ (fun i => pclmul (s.zlane a i) (s.zlane b i) n) hl]
    split at h
    · subst_vars; cases h
      simp only [runBlock, exec, XOp.exec, Option.bind_some, State.zproj_xmm]
    · split at h
      · cases h
      · rename_i h1 h2; cases h
        simp only [runBlock, exec, XOp.exec, Option.bind_some, State.zproj_xmm]
        rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ h2, setXmm_setXmm, eval_movdqa]; rfl
  case vpshufd d r o =>
    cases h
    refine ⟨_, rfl, VKeep.setZ .., fun l hl => ?_⟩
    rw [show (ZOp.vpshufd d r o).exec s = s.setZ d (shufDwords (s.zlane r 0) o) (shufDwords (s.zlane r 1) o)
      (shufDwords (s.zlane r 2) o) (shufDwords (s.zlane r 3) o) from rfl,
      zproj_setZ _ _ (fun i => shufDwords (s.zlane r i) o) hl]
    simp only [runBlock, exec, XOp.exec, Option.bind_some, State.zproj_xmm]
  case vpternlogd d a b n =>
    split at h
    · rename_i hc; obtain ⟨rfl, ha, hb⟩ := hc; cases h
      refine ⟨_, rfl, VKeep.setZ .., fun l hl => ?_⟩
      rw [show (ZOp.vpternlogd d a b 0x96).exec s = s.setZ d (ternlog (s.zlane d 0) (s.zlane a 0) (s.zlane b 0) 0x96)
        (ternlog (s.zlane d 1) (s.zlane a 1) (s.zlane b 1) 0x96) (ternlog (s.zlane d 2) (s.zlane a 2) (s.zlane b 2) 0x96)
        (ternlog (s.zlane d 3) (s.zlane a 3) (s.zlane b 3) 0x96) from rfl,
        zproj_setZ _ _ (fun i => ternlog (s.zlane d i) (s.zlane a i) (s.zlane b i) 0x96) hl]
      simp only [runBlock, exec, XOp.exec, Option.bind_some, State.zproj_xmm]
      rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hb, setXmm_setXmm, ternlog_96]; rfl
    · cases h

theorem zlaneSseBlock_ok {vs ss : List Instr} (h : zlaneSseBlock vs = some ss) (s : State) :
    ∃ s', runBlock isa vs s = some s' ∧ VKeep s s' ∧
      ∀ l < 4, runBlock isa ss (s.zproj l) = some (s'.zproj l) := by
  induction vs generalizing ss s with
  | nil =>
    simp only [zlaneSseBlock, Option.some.injEq] at h; subst h
    exact ⟨s, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  | cons i is ih =>
    simp only [zlaneSseBlock] at h
    split at h
    · rename_i a b ha hb
      cases h
      obtain ⟨s₁, e₁, k₁, p₁⟩ := zlaneSse_ok ha s
      obtain ⟨s₂, e₂, k₂, p₂⟩ := ih hb s₁
      refine ⟨s₂, by show (exec i s).bind _ = _; rw [e₁, Option.bind_some]; exact e₂, k₁.trans k₂,
        fun l hl => ?_⟩
      rw [runBlock_append, p₁ l hl, Option.bind_some, p₂ l hl]
    · cases h

/-- A block of lane-wise EVEX.512 instructions does to each lane what its SSE
block does to the SSE registers. -/
theorem WP.zlanes {vs ss : List Instr} (h : zlaneSseBlock vs = some ss) {s : State} {Q : Nat → State → Prop}
    (hq : ∀ l < 4, WP isa (.block ss) (s.zproj l) (Q l)) :
    WP isa (.block vs) s fun s' => VKeep s s' ∧ ∀ l < 4, Q l (s'.zproj l) := by
  obtain ⟨s', e, k, p⟩ := zlaneSseBlock_ok h s
  refine WP.of_runBlock ⟨s', e, k, fun l hl => ?_⟩
  obtain ⟨t, et, qt⟩ := WP.runBlock_of (hq l hl)
  rw [p l hl, Option.some.injEq] at et
  exact et ▸ qt

end VG.X86_64
