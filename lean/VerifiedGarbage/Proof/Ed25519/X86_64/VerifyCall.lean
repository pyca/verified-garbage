module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MxcsrInline
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT
public import VerifiedGarbage.Proof.Ed25519.X86_64.DecodePowers
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyPoints
public import VerifiedGarbage.Proof.X25519.X86_64.Setup
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT
meta import VerifiedGarbage.Proof.Ed25519.X86_64.DecodePowers
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyPoints
meta import VerifiedGarbage.Proof.X25519.X86_64.Setup
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
meta import VerifiedGarbage.Proof.Ed25519.ScalarBytes
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import Mathlib.FieldTheory.Finite.Basic
meta import Mathlib.Tactic.NormNum.Prime
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr
meta import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Block
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Framework.Block
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring

/-! ### `Ed25519.X86_64.VerifyVerified`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86_64.RecodeCT`, which only this module used -/

section

/-!
# The recoding: what its trace depends on

The recoding branches on the scalars' bits and the carry, and addresses the copies and the
digits' array by the bit's position, so its trace depends on the recoding's state alone (`St`),
the same in both runs of the same scalar: both runs are followed at the same state.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Recode
open VG.Proof.X25519.X86_64 (off ofs Keeps)
open VG.Impl.X25519.X86_64 (sc at_)

theorem agree_rdi_rsi {x y : State} (h : x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

theorem agree_none {x y : State} : VG.X86_64.Taint.Agree (Taint.ofRegs []) x y :=
  Taint.agree_ofRegs (by simp)

/-- A state at the bit `i`: the scratch's, `rsi = i`. -/
def AtBit (base : Addr) (i : Nat) (x : State) : Prop := Scratch x base ∧ x.gpr .rsi = BitVec.ofNat 64 i

/-- Code whose trace depends on `rdi` and `rsi`, from states at the same bit. -/
theorem atBit_ct {P : State → Prop} {base : Addr} {i : Nat} {c : Prog isa} (hP : ∀ x, P x → AtBit base i x)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi) c (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => ⟨((hP x hh.1).1.rdi).trans (hP y hh.2).1.rdi.symm,
    ((hP x hh.1).2).trans (hP y hh.2).2.symm⟩) (fun _ _ h => h)

/-- The two recodings: `k`'s and `S`'s. -/
def RecParams (src w dst : Nat) : Prop := (src = 3104 ∧ w = 5 ∧ dst = 0) ∨ (src = 3176 ∧ w = 8 ∧ dst = 1)

theorem bitsTest_ct {src w dst : Nat} (hp : RecParams src w dst) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi)
    (.block (recodeBits src ++ recodeTest)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rsi]) (fun _ _ h => agree_rdi_rsi h)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeStore_ct {src w dst : Nat} (hp : RecParams src w dst) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi)
    (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx,
      .alu .add .rsi (.imm (BitVec.ofNat 32 w))]) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rsi]) (fun _ _ h => agree_rdi_rsi h)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeLast_ct {src w dst : Nat} (hp : RecParams src w dst) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi)
    (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax), .mov32 .rbx (.imm 1),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx])
    (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rsi]) (fun _ _ h => agree_rdi_rsi h)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeW_ct {P : State → State → Prop} {src w dst : Nat} (hp : RecParams src w dst) :
    RelCT isa P (.block [.alu .and .rbx (.imm (BitVec.ofNat 32 (2 ^ w - 1))), .alu .add .rbx (.reg .r8),
      .alu .cmp .rbx (.imm (BitVec.ofNat 32 (2 ^ (w - 1))))]) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs []) (fun _ _ _ => agree_none)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeNeg_ct {P : State → State → Prop} {src w dst : Nat} (hp : RecParams src w dst) :
    RelCT isa P (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (2 ^ w + 1))), .alu .sub .rax (.reg .rbx),
      .mov .rbx (.reg .rax), .mov32 .r8 (.imm 1)]) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs []) (fun _ _ _ => agree_none)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

/-- Code that accesses no memory and does not branch. -/
theorem noMem_ct {P : State → State → Prop} (l : List Instr)
    (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
      (VG.X86_64.taint.check (Taint.ofRegs []) (.block l) hc).isSome = true) :
    RelCT isa P (.block l) (fun _ _ => True) :=
  taintFld (Taint.ofRegs []) (fun _ _ _ => agree_none) h

section
variable (base : Addr) (src nb X w dst : Nat) (bound : List Instr)

/-- Where the recoding may start from: the scratch, the copy of `X`, the bound and the digits'
array zeroed. -/
structure RecStart (s : State) : Prop where
  scratch : Scratch s base
  copied : Copied s.mem base src nb X
  bound : BoundSpec s base dst nb bound

/-- A run of the recoding at the state `st`. -/
def RecRun (st : St) (x : State) : Prop :=
  ∃ s₀, RecStart base src nb X dst bound s₀ ∧ RecInv s₀ base nb X w dst st x

end

theorem RecRun.atBit {base : Addr} {src nb X w dst : Nat} {bound : List Instr} {st : St} {x : State}
    (h : RecRun base src nb X w dst bound st x) : AtBit base st.i x := by
  obtain ⟨s₀, h₀, h⟩ := h
  exact ⟨h.keep.scratch h₀.scratch, h.rsi⟩

/-- One step: its branches are on the bit and on the window, functions of `X` and `st`. -/
theorem recodeStep_ct {base : Addr} {src nb X w dst : Nat} {bound : List Instr} {st : St}
    (hp : RecParams src w dst) (hw : 2 ≤ w ∧ w ≤ 8) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192) (hi : st.i < 8 * nb)
    (hnb : 8 * nb ≤ 512) :
    RelCT isa (fun x y => RecRun base src nb X w dst bound st x ∧ RecRun base src nb X w dst bound st y)
      (recodeStep src w dst) (fun _ _ => True) := by
  let W := X / 2 ^ st.i % 2 ^ w
  have hWl : W < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h8 : 2 ^ w ≤ 256 := (Nat.pow_le_pow_right (by decide) hw.2 : 2 ^ w ≤ 2 ^ 8)
  -- After the bits and the test.
  let F1 : State → Prop := fun u => u.zf = some (decide (X / 2 ^ st.i % 2 = st.c)) ∧ AtBit base st.i u ∧
    u.gpr .r8 = BitVec.ofNat 64 st.c ∧ (u.gpr .rbx).toNat % 2 ^ w = W ∧ st.c ≤ 1
  have w1 (x : State) (h : RecRun base src nb X w dst bound st x) :
      WP isa (.block (recodeBits src ++ recodeTest)) x F1 := by
    obtain ⟨s₀, h₀, ht⟩ := h
    have hs : Scratch x base := ht.keep.scratch h₀.scratch
    have hX : Copied x.mem base src nb X := h₀.copied.of_keep hsrc hfit fun y hy => ht.keep.mem y (by omega_arith)
    have hc1 := ht.good.c
    rw [WP.block_append_iff]
    refine WP.mono (recodeBits_ok hs hfit hX hi ht.rsi (by omega_arith)) fun a ⟨ab, ka⟩ => ?_
    have hbit : (a.gpr .rbx).toNat % 2 = X / 2 ^ st.i % 2 := by
      rw [ab]; exact bits_mod X st.i 1 (by decide)
    have hwin : (a.gpr .rbx).toNat % 2 ^ w = W := by
      rw [ab]; exact bits_mod X st.i w (by omega_arith)
    refine WP.mono (recodeTest_ok a hbit hc1 (by rw [ka.1 _ (by decide)]; exact ht.r8)) fun b ⟨bz, kb⟩ => ?_
    have kab : Keeps [.rax, .rbx, .rcx, .rdx] x b := ka.trans (kb.mono (by decide))
    refine ⟨bz, ⟨hs.of_keeps kab (by decide), by rw [kab.1 _ (by decide)]; exact ht.rsi⟩,
      by rw [kab.1 _ (by decide)]; exact ht.r8, by rw [kb.1 _ (by decide)]; exact hwin, hc1⟩
  rw [recodeStep]
  refine seq_same (atBit_ct (fun x h => h.atBit) (bitsTest_ct hp)) w1 ?_
  have e1 (x : State) (h : F1 x) : isa.eval .e x = some (decide (X / 2 ^ st.i % 2 = st.c)) := by
    show eval .e x = _; simp only [eval, h.1]
  refine VG.RelCT.ite (fun x y h => (e1 x h.1).trans (e1 y h.2).symm) (noMem_ct _ ⟨_, by taint_decide⟩) ?_
  -- The window.
  rw [recodeWindow]
  let F1' : State → Prop := fun u => F1 u ∧ X / 2 ^ st.i % 2 ≠ st.c
  refine (show RelCT isa (fun x y => F1' x ∧ F1' y) _ _ from ?_).mono (fun x y h => by
    have hne : X / 2 ^ st.i % 2 ≠ st.c := by
      have := (e1 x h.1.1).symm.trans h.2
      simpa using this
    exact ⟨⟨h.1.1, hne⟩, ⟨h.1.2, hne⟩⟩) (fun _ _ h => h)
  let F2 : State → Prop := fun u => u.cf = some (decide (W + st.c < 2 ^ (w - 1))) ∧ AtBit base st.i u ∧
    u.gpr .rbx = BitVec.ofNat 64 (W + st.c) ∧ st.c ≤ 1
  have w2 (x : State) (h : F1' x) : WP isa (.block [.alu .and .rbx (.imm (BitVec.ofNat 32 (2 ^ w - 1))),
      .alu .add .rbx (.reg .r8), .alu .cmp .rbx (.imm (BitVec.ofNat 32 (2 ^ (w - 1))))]) x F2 := by
    obtain ⟨⟨_, ⟨hs, hr⟩, h8', hb, hc1⟩, _⟩ := h
    refine WP.mono (recodeW_ok x (by omega_arith) hb hc1 h8') fun c ⟨cb, ccf, kc⟩ => ?_
    exact ⟨ccf, ⟨hs.of_keeps kc (by decide), by rw [kc.1 _ (by decide)]; exact hr⟩, cb, hc1⟩
  refine seq_same (recodeW_ct hp) w2 ?_
  have e2 (x : State) (h : F2 x) : isa.eval .b x = some (decide (W + st.c < 2 ^ (w - 1))) := by
    show eval .b x = _; simp only [eval, h.1]
  refine VG.RelCT.seq (R := fun x y => AtBit base st.i x ∧ AtBit base st.i y)
    (VG.RelCT.ite (fun x y h => (e2 x h.1).trans (e2 y h.2).symm) ?_ ?_)
    (atBit_ct (fun _ h => h) (recodeStore_ct hp))
  · have wp (x : State) (h : F2 x) : WP isa (.block [.mov32 .r8 (.imm 0)]) x (AtBit base st.i) :=
      WP.mono (recodePos_ok x) fun u ⟨_, _, ku⟩ =>
        ⟨h.2.1.1.of_keeps ku (by decide), by rw [ku.1 _ (by decide)]; exact h.2.1.2⟩
    exact ((VG.RelCT.wp (noMem_ct _ ⟨_, by taint_decide⟩) fun x y h => ⟨wp x h.1.1, wp y h.1.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2))
  · have wn (x : State) (h : F2 x) : WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (2 ^ w + 1))),
        .alu .sub .rax (.reg .rbx), .mov .rbx (.reg .rax), .mov32 .r8 (.imm 1)]) x (AtBit base st.i) :=
      WP.mono (recodeNeg_ok x (W := W + st.c) (by omega_arith) (by have := h.2.2.2; omega_arith) h.2.2.1)
        fun u ⟨_, _, ku⟩ => ⟨h.2.1.1.of_keeps ku (by decide), by rw [ku.1 _ (by decide)]; exact h.2.1.2⟩
    exact ((VG.RelCT.wp (recodeNeg_ct hp) fun x y h => ⟨wn x h.1.1, wn y h.1.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2))

/-- The recoding: its loop at the same state in both runs, then the last carry. -/
theorem recode_ct {P : State → Prop} {base : Addr} {src nb X w dst : Nat} {bound : List Instr}
    (hp : RecParams src w dst) (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hnb : 0 < nb ∧ 8 * nb ≤ 512)
    (hP : ∀ x, P x → RecStart base src nb X dst bound x ∧ ∀ j < 528, dig x.mem base dst j = 0)
    (hbct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block bound) (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) (recode src w dst bound) (fun _ _ => True) := by
  have w0 (x : State) (h : P x) : WP isa (.block [.mov32 .rsi (.imm 0), .mov32 .r8 (.imm 0)]) x
      (RecRun base src nb X w dst bound init) := by
    obtain ⟨h₀, hz⟩ := hP x h
    refine WP.mono (recodeStart_ok x) fun a ⟨arsi, ar8, ka⟩ => ⟨x, h₀, ?_⟩
    exact ⟨reach_init w X _, init_good w X, by simp only [init]; omega_arith, arsi, ar8,
      fun j hj => by rw [ka.2.1]; exact hz j hj, RecKeep.of_keeps ka (by decide)⟩
  rw [recode]
  refine seq_same (noMem_ct _ ⟨_, by taint_decide⟩) w0 ?_
  -- The loop.
  let F := run w X (8 * nb) (8 * nb) init
  refine VG.RelCT.seq (R := fun x y => RecRun base src nb X w dst bound F x ∧
    RecRun base src nb X w dst bound F y) ?_ ?_
  · refine (VG.RelCT.loop (M := isa) (fun m x y => ∃ st, st.i < 8 * nb ∧ m = 8 * nb - st.i ∧
      RecRun base src nb X w dst bound st x ∧ RecRun base src nb X w dst bound st y) ?_ (8 * nb - init.i)).mono
      (fun x y h => ⟨init, by simp only [init]; omega_arith, rfl, h⟩) (fun _ _ h => h)
    intro m
    refine VG.RelCT.exists_ fun st => ?_
    refine (VG.RelCT.exists_ (P := fun (hh : st.i < 8 * nb ∧ m = 8 * nb - st.i) x y =>
      RecRun base src nb X w dst bound st x ∧ RecRun base src nb X w dst bound st y) fun hh => ?_).mono
      (fun x y h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
    obtain ⟨hi, hm⟩ := hh
    have hsi := step_i (K := X) (by omega_arith : 1 ≤ w) st
    have wb (x : State) (h : RecRun base src nb X w dst bound st x) :
        WP isa (.seq (recodeStep src w dst) (.block bound)) x fun v =>
          RecRun base src nb X w dst bound (step w X st) v ∧
          v.cf = some (decide ((step w X st).i < 8 * nb)) := by
      obtain ⟨s₀, h₀, ht⟩ := h
      exact WP.mono (recodeBody_ok h₀.scratch hw hdst hsrc hfit h₀.copied hnb.2 h₀.bound hi ht)
        fun v ⟨hv, vcf⟩ => ⟨⟨s₀, h₀, hv⟩, vcf⟩
    have bodyCT : RelCT isa (fun x y => RecRun base src nb X w dst bound st x ∧
        RecRun base src nb X w dst bound st y) (.seq (recodeStep src w dst) (.block bound)) (fun _ _ => True) :=
      seq_same (recodeStep_ct hp hw hsrc hfit hi hnb.2) (F := fun u => u.gpr .rdi = base)
        (fun x h => by
          obtain ⟨s₀, h₀, ht⟩ := h
          exact WP.mono (recodeStep_ok (ht.keep.scratch h₀.scratch) hw hdst hfit
            (h₀.copied.of_keep hsrc hfit fun y hy => ht.keep.mem y (by omega_arith)) hi hnb.2 ht.good.c ht.rsi ht.r8
            ht.dig) fun u ⟨_, _, _, ku⟩ => (ku.scratch (ht.keep.scratch h₀.scratch)).rdi)
        (rdi_ct (fun _ h => h) hbct)
    refine (VG.RelCT.wp bodyCT fun x y h => ⟨wb x h.1, wb y h.2⟩).mono (fun x y h => h) ?_
    intro x y ⟨_, ⟨xr, xc⟩, ⟨yr, yc⟩⟩
    have ex : isa.eval .b x = some (decide ((step w X st).i < 8 * nb)) := by
      show eval .b x = _; simp only [eval, xc]
    have ey : isa.eval .b y = some (decide ((step w X st).i < 8 * nb)) := by
      show eval .b y = _; simp only [eval, yc]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have hlt : ¬ (step w X st).i < 8 * nb := by rw [ex] at he; simpa using he
      have e := reach_end (by obtain ⟨_, _, ht⟩ := xr; exact ht.reach) (by omega_arith : 8 * nb ≤ (step w X st).i)
      show RecRun base src nb X w dst bound (run w X (8 * nb) (8 * nb) init) x ∧ RecRun base src nb X w dst bound (run w X (8 * nb) (8 * nb) init) y
      rw [← e]
      exact ⟨xr, yr⟩
    · have hlt : (step w X st).i < 8 * nb := by rw [ex] at he; simpa using he
      exact ⟨8 * nb - (step w X st).i, by omega_arith, step w X st, hlt, rfl, xr, yr⟩
  -- The last carry.
  rw [recodeEnd]
  let G : State → Prop := fun u => u.zf = some (decide (F.c = 0)) ∧ AtBit base F.i u
  have wt (x : State) (h : RecRun base src nb X w dst bound F x) :
      WP isa (.block [.alu .test .r8 (.reg .r8)]) x G := by
    obtain ⟨s₀, h₀, hb'⟩ := h
    exact WP.mono (testR8_ok x hb'.good.c hb'.r8) fun t ⟨tz, kt⟩ =>
      ⟨tz, (hb'.keep.scratch h₀.scratch).of_keeps kt (by decide), by rw [kt.1 _ (by decide)]; exact hb'.rsi⟩
  refine seq_same (noMem_ct _ ⟨_, by taint_decide⟩) wt ?_
  have eG (x : State) (h : G x) : isa.eval .ne x = some (!decide (F.c = 0)) := by
    show eval .ne x = _; simp only [eval, h.1, Option.map_some]
  refine VG.RelCT.ite (fun x y h => (eG x h.1).trans (eG y h.2).symm) ?_ (VG.RelCT.block_nil fun _ _ _ => trivial)
  exact (atBit_ct (fun _ h => h) (recodeLast_ct hp)).mono (fun x y h => ⟨h.1.1.2, h.1.2.2⟩) (fun _ _ h => h)

/-! ## The copies -/

/-- A state with the scratch and `rsi = P`. -/
def AtPtr (base P : Addr) (x : State) : Prop := Scratch x base ∧ x.gpr .rsi = P

/-- What the copies need: the scratch, the scalars' pointers and their regions. -/
structure CopyPre (base kp sp : Addr) (x : State) : Prop where
  scratch : Scratch x base
  kPtr : x.mem.readW (off base 7952) 64 = kp
  sPtr : x.mem.readW (off base 7944) 64 = sp
  kr : ∀ j < 8, InRegions (x.rd ++ x.wr) (off kp (8 * j)) 8
  sr : ∀ j < 4, InRegions (x.rd ++ x.wr) (off sp (32 + 8 * j)) 8

theorem atPtr_ct {P : State → Prop} {base Q : Addr} {c : Prog isa} (hP : ∀ x, P x → AtPtr base Q x)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi) c (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => ⟨((hP x hh.1).1.rdi).trans (hP y hh.2).1.rdi.symm,
    ((hP x hh.1).2).trans (hP y hh.2).2.symm⟩) (fun _ _ h => h)

/-- The copies load through the scalars' pointers, the same in both runs. -/
theorem recodeCopy_ct {P : State → Prop} {base kp sp : Addr}
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j)) (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j)))
    (hP : ∀ x, P x → CopyPre base kp sp x) :
    RelCT isa (fun x y => P x ∧ P y) (.block (zeroDigits ++ copyScalars)) (fun _ _ => True) := by
  rw [show zeroDigits ++ copyScalars = (zeroDigits ++ [.mov .rsi (.mem (sc 7952))]) ++
      (((List.range 8).flatMap fun j =>
        [.mov .rax (.mem (at_ .rsi (0 + 8 * j))), .store (sc (3104 + 8 * j)) .rax]) ++
      ([.mov .rsi (.mem (sc 7944))] ++ (((List.range 4).flatMap fun j =>
        [.mov .rax (.mem (at_ .rsi (32 + 8 * j))), .store (sc (3176 + 8 * j)) .rax]) ++
      [.mov32 .rax (.imm 0), .store (sc 3168) .rax, .store (sc 3208) .rax]))) by
    simp only [copyScalars, Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append]]
  -- Up to `k`'s pointer.
  let Q1 : State → Prop := fun u => AtPtr base kp u ∧ u.mem.readW (off base 7944) 64 = sp ∧
    (∀ j < 8, InRegions (u.rd ++ u.wr) (off kp (8 * j)) 8) ∧
    (∀ j < 4, InRegions (u.rd ++ u.wr) (off sp (32 + 8 * j)) 8)
  have w1 (x : State) (h : P x) : WP isa (.block (zeroDigits ++ [.mov .rsi (.mem (sc 7952))])) x Q1 := by
    have c := hP x h
    have hs := c.scratch
    rw [WP.block_append_iff]
    refine WP.mono (zeroDigits_ok hs) fun a ⟨⟨_, ao⟩, ag, _, ar, aw⟩ => ?_
    have ha : Scratch a base := ⟨by rw [ag _ (by decide)]; exact hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
    have hb := hs.nowrap
    have aread (d : Nat) (hd : 3104 ≤ d) (hd' : d + 8 ≤ 8192) :
        a.mem.readW (off base d) 64 = x.mem.readW (off base d) 64 :=
      Mem.readW_congr fun i hi => ao _ (Or.inr (by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
    refine WP.mono (loadSc_ok ha .rsi 7952 (by decide)) fun u ⟨up, ku⟩ => ?_
    refine ⟨⟨ha.of_keeps ku (by decide), by rw [up, aread 7952 (by decide) (by decide)]; exact c.kPtr⟩,
      by rw [ku.2.1, aread 7944 (by decide) (by decide)]; exact c.sPtr,
      fun j hj => by rw [ku.2.2.1, ku.2.2.2, ar, aw]; exact c.kr j hj,
      fun j hj => by rw [ku.2.2.1, ku.2.2.2, ar, aw]; exact c.sr j hj⟩
  apply RelCT.block_append
  refine seq_same (rdi_ct (fun x h => (hP x h).scratch.rdi)
    (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩)) w1 ?_
  -- `k`'s copy.
  let Q2 : State → Prop := fun u => Scratch u base ∧ u.mem.readW (off base 7944) 64 = sp ∧
    (∀ j < 4, InRegions (u.rd ++ u.wr) (off sp (32 + 8 * j)) 8)
  have w2 (x : State) (h : Q1 x) : WP isa (.block ((List.range 8).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (0 + 8 * j))), .store (sc (3104 + 8 * j)) .rax])) x Q2 := by
    obtain ⟨⟨hs, hr⟩, hsp, hkr, hsr⟩ := h
    have hb := hs.nowrap
    refine WP.mono (copyPrefix_ok hs hr 0 3104 8 (by decide) (fun j hj => by simpa using hkr j hj)
      (fun j hj => by simpa using hkf j hj)) fun b ⟨⟨_, bo⟩, bg, br, bw⟩ => ?_
    refine ⟨⟨by rw [bg _ (by decide)]; exact hs.rdi, bw ▸ hs.wr, hb⟩, ?_,
      fun j hj => by rw [br, bw]; exact hsr j hj⟩
    rw [← hsp]
    exact Mem.readW_congr fun i hi => bo _ (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
  apply RelCT.block_append
  refine seq_same (atPtr_ct (fun x h => h.1) (taintFld (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => agree_rdi_rsi h) ⟨_, by taint_decide⟩)) w2 ?_
  -- `S`'s pointer.
  let Q3 : State → Prop := fun u => AtPtr base sp u ∧ (∀ j < 4, InRegions (u.rd ++ u.wr) (off sp (32 + 8 * j)) 8)
  have w3 (x : State) (h : Q2 x) : WP isa (.block [.mov .rsi (.mem (sc 7944))]) x Q3 := by
    obtain ⟨hs, hsp, hsr⟩ := h
    refine WP.mono (loadSc_ok hs .rsi 7944 (by decide)) fun u ⟨up, ku⟩ =>
      ⟨⟨hs.of_keeps ku (by decide), by rw [up]; exact hsp⟩, fun j hj => by rw [ku.2.2.1, ku.2.2.2]; exact hsr j hj⟩
  apply RelCT.block_append
  refine seq_same (rdi_ct (fun x h => h.1.rdi)
    (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩)) w3 ?_
  -- `S`'s copy, then the zeros after the copies.
  have w4 (x : State) (h : Q3 x) : WP isa (.block ((List.range 4).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (32 + 8 * j))), .store (sc (3176 + 8 * j)) .rax])) x (Scratch · base) := by
    obtain ⟨⟨hs, hr⟩, hsr⟩ := h
    exact WP.mono (copyPrefix_ok hs hr 32 3176 4 (by decide) hsr hsf) fun b ⟨_, bg, _, bw⟩ =>
      ⟨by rw [bg _ (by decide)]; exact hs.rdi, bw ▸ hs.wr, hs.nowrap⟩
  apply RelCT.block_append
  exact seq_same (atPtr_ct (fun x h => h.1) (taintFld (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => agree_rdi_rsi h) ⟨_, by taint_decide⟩)) w4
    (rdi_ct (fun x h => h.rdi) (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩))

/-! ## Both recodings -/

/-- `k`'s and `S`'s recodings, of the same scalars in both runs, after the same number `c` of
`k`'s bytes: their trace depends on those alone. -/
theorem recodeAll_ct {P : State → Prop} {base kp sp : Addr} {c K S : Nat} (hc32 : 32 ≤ c) (hc64 : c ≤ 64)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j)) (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j)))
    (hP : ∀ x, P x → CopyPre base kp sp x ∧ x.mem.readW (off base 56) 64 = BitVec.ofNat 64 c ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt x.mem kp 64) = K ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt x.mem (off sp 32) 32) = S) :
    RelCT isa (fun x y => P x ∧ P y) recodeAll (fun _ _ => True) := by
  have w1 (x : State) (h : P x) : WP isa (.block (zeroDigits ++ copyScalars)) x (Copies base c K S) := by
    obtain ⟨cp, hc, hK, hS⟩ := hP x h
    refine WP.mono (recodeCopy_ok cp.scratch hc hc64 cp.kPtr cp.sPtr cp.kr cp.sr hkf hsf) fun b hb => ?_
    rw [hK, hS] at hb
    exact hb.1
  rw [recodeAll]
  refine seq_same (recodeCopy_ct hkf hsf fun x h => (hP x h).1) w1 ?_
  -- `k`'s digits.
  let F2 : State → Prop := fun u => Scratch u base ∧ u.mem.readW (off base 56) 64 = BitVec.ofNat 64 c ∧
    Copied u.mem base 3176 32 S ∧ ∀ j < 528, dig u.mem base 1 j = 0
  have w2 (x : State) (h : Copies base c K S x) : WP isa (recode 3104 5 0 boundK) x F2 := by
    have hb := h.scratch.nowrap
    refine WP.mono (recode_ok h.scratch (by decide) (by decide) (by decide) (by omega_arith) h.cK (by omega_arith)
      (boundK_spec h.scratch hc64 h.counter 0) (h.zero 0 (by decide))) fun d ⟨_, kd⟩ => ?_
    refine ⟨kd.scratch h.scratch, ?_, h.cS.of_keep (by decide) (by decide) fun y hy => kd.mem y (by omega_arith),
      fun j hj => ?_⟩
    · rw [← h.counter]
      exact Mem.readW_congr fun i hi => kd.mem _ (Or.inl (by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
    · simp only [dig]
      rw [kd.mem _ (Or.inr (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith)))]
      exact h.zero 1 (by decide) j hj
  have boundK_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block boundK) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩
  refine seq_same (recode_ct (Or.inl ⟨rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by omega_arith) (by omega_arith)
    (fun x h => ⟨⟨h.scratch, h.cK, boundK_spec h.scratch hc64 h.counter 0⟩, h.zero 0 (by decide)⟩) boundK_ct)
    w2 ?_
  -- `S`'s digits.
  have w3 (x : State) (h : F2 x) : WP isa (recode 3176 8 1 boundS) x (Scratch · base) :=
    WP.mono (recode_ok h.1 (by decide) (by decide) (by decide) (by decide) h.2.2.1 (by decide)
      (boundS_spec x base 1) h.2.2.2) fun _ ⟨_, ke⟩ => ke.scratch h.1
  refine seq_same (recode_ct (Or.inr ⟨rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun x h => ⟨⟨h.1, h.2.2.1, boundS_spec x base 1⟩, h.2.2.2⟩)
    (noMem_ct _ ⟨_, by taint_decide⟩)) w3 ?_
  exact rdi_ct (fun x h => h.rdi) (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩)

end VG.Proof.Ed25519.X86_64

end

end

/-! ### `Ed25519.X86_64.BaseHeld`, which this module and modules that import it used -/

section

/-!
# The static's words are its entries

Word `16 j + 4 f + w` of `baseOddWords` is word `w` of field `f` of entry `j`, so a memory
holding the words at `T` holds entry `j` at `T + 128 j` (`baseTbl_entry`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs fe val4 F)

/-- The words of an entry: `X`, `Y`, `Z`, `T`. -/
abbrev entry4Words (p : Spec.Ed25519.Point) : List (BitVec 64) :=
  [p.X, p.Y, p.Z, p.T].flatMap feWords

theorem feWords_length (v : Spec.X25519.Fe) : (feWords v).length = 4 := by simp [feWords]

theorem entry4Words_length (p : Spec.Ed25519.Point) : (entry4Words p).length = 16 := by
  rw [entry4Words, length_flatMap_const _ 4 _ (fun v _ => feWords_length v)]
  rfl

theorem entry4Words_getD (p : Spec.Ed25519.Point) {f w : Nat} (hf : f < 4) (hw : w < 4) :
    (entry4Words p).getD (f * 4 + w) 0 = feWord ([p.X, p.Y, p.Z, p.T].getD f 0) w := by
  rw [entry4Words, getD_flatMap_const _ 4 0 [p.X, p.Y, p.Z, p.T] 0 (fun v _ => feWords_length v) f hf w hw,
    feWords_getD _ hw]

theorem baseOddWords_eq :
    baseOddWords = baseOddAffine.flatMap fun q => entry4Words (baseOddCached q) := by
  unfold baseOddWords
  congr 1

theorem baseOddWords_length : baseOddWords.length = 2048 := by
  rw [baseOddWords_eq, length_flatMap_const _ 16 _ (fun q _ => entry4Words_length _),
    baseOddAffine_length]

theorem baseOddWords_getD {j f w : Nat} (hj : j < 128) (hf : f < 4) (hw : w < 4) :
    baseOddWords.getD (j * 16 + (f * 4 + w)) 0 =
      feWord ([(baseOddCached (baseOddAffine.getD j (0, 1))).X,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Y,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Z,
        (baseOddCached (baseOddAffine.getD j (0, 1))).T].getD f 0) w := by
  rw [baseOddWords_eq, getD_flatMap_const _ 16 0 baseOddAffine (0, 1)
      (fun q _ => entry4Words_length _) j (by rw [baseOddAffine_length]; exact hj) _ (by omega_using [hf, hw]),
    entry4Words_getD _ hf hw]

/-- Field `f` of entry `j`, from the words at `T`. -/
theorem baseField {m : Mem} {T : Addr}
    (hheld : ∀ i < 2048, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = baseOddWords.getD i 0)
    {j f : Nat} (hj : j < 128) (hf : f < 4) :
    F m (off T (128 * j)) (32 * f) =
      [(baseOddCached (baseOddAffine.getD j (0, 1))).X,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Y,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Z,
        (baseOddCached (baseOddAffine.getD j (0, 1))).T].getD f 0 := by
  have hword : ∀ w < 4, Proof.X25519.X86_64.word m (off T (128 * j)) (32 * f + 8 * w) =
      feWord ([(baseOddCached (baseOddAffine.getD j (0, 1))).X,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Y,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Z,
        (baseOddCached (baseOddAffine.getD j (0, 1))).T].getD f 0) w := by
    intro w hw
    simp only [Proof.X25519.X86_64.word, off, Offset.add_add]
    rw [show 128 * j + (32 * f + 8 * w) = 8 * (j * 16 + (f * 4 + w)) by omega_using [],
      hheld _ (by omega_using [hj, hf, hw]), baseOddWords_getD hj hf hw]
  simp only [F, fe]
  have h0 := hword 0 (by decide)
  have h1 := hword 1 (by decide)
  have h2 := hword 2 (by decide)
  have h3 := hword 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
  rw [h0, h1, h2, h3, feWord_val, Proof.X25519.toFe_self]

/-- The words of `baseOddWords` at `T` are the entries. -/
theorem baseTbl_entry {m : Mem} {T : Addr}
    (hheld : ∀ i < 2048, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = baseOddWords.getD i 0)
    (j : Nat) (hj : j < 128) :
    tablePoint m (off T (128 * j)) 0 = baseOddCached (baseOddAffine.getD j (0, 1)) := by
  have h0 := baseField hheld hj (f := 0) (by decide)
  have h1 := baseField hheld hj (f := 1) (by decide)
  have h2 := baseField hheld hj (f := 2) (by decide)
  have h3 := baseField hheld hj (f := 3) (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
  simp only [tablePoint, Nat.zero_add, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.X86_64

end

end

/-! Merged from `Proof.Ed25519.X86_64.VerifyCTPublic`. -/

@[expose] public section

section
/-! The verification inputs are public, and the equation's trace depends on them alone. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

structure VerifyPublic (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr)
    (s : State) : Prop where
  context : VerifyContext s base pk sig challenge
  pkBytes : Spec.Ed25519.bytesAt s.mem pk 32 = pkbs
  rBytes : Spec.Ed25519.bytesAt s.mem sig 32 = rbs
  sBytes : Spec.Ed25519.bytesAt s.mem (off sig 32) 32 = sbs
  kBytes : Spec.Ed25519.bytesAt s.mem challenge 64 = kbs
  bAddr : s.mem.readW (off base 7960) 64 = T

theorem VerifyPublic.of_keep {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr} {s t : State}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) (kt : VerifyKeep base s t) :
    VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t :=
  ⟨h.context.of_keep kt, (verifyKeep_bytes kt h.context.pkFar).trans h.pkBytes,
    (verifyKeep_bytes kt h.context.rFar).trans h.rBytes,
    (verifyKeep_bytes kt h.context.scalarFar).trans h.sBytes,
    (verifyKeep_bytes kt h.context.challengeFar).trans h.kBytes,
    (kt.header (by decide) (by decide) (by decide)).trans h.bAddr⟩

def PointsCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr)
    (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
    tablePoint s.mem base 7424 = a ∧ tablePoint s.mem base 7552 = r

theorem pointTableWrite_ct (base : Addr) (o : Nat) (ho : o ∈ [7424, 7552]) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (pointTableWrite o)) (fun _ _ => True) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  all_goals
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1 h.2

theorem verifyEquationPoints_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr}
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r s ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r t) (verifyEquationPoints fld (Point64.bodies fld) win) (fun _ _ => True) := by
  let K := Spec.Ed25519.decodeLE kbs
  let S := Spec.Ed25519.decodeLE sbs
  let R₀ : State → Prop := fun s₀ => tablePoint s₀.mem base 7552 = r
  have w (x : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x) :
      WP isa (windowPrep fld (Point64.bodies fld)) x (SkipLoopRun R₀ base challenge sig T Aa K S 64) := by
    have c := h.1.context
    refine WP.mono (windowPrep_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader c.scalarBytes c.scalarFar
      c.challengeRead c.challengeFar c.kRead8 c.sRead8 (by rw [h.2.1]; exact hA) h.1.bAddr
      (h.1.bAddr ▸ c.bTab)) fun e ⟨we, _, eR⟩ => ?_
    rw [h.1.kBytes, h.1.sBytes] at we
    exact ⟨e, eR.trans h.2.2, we⟩
  obtain prepCT : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (windowPrep fld (Point64.bodies fld)) (fun _ _ => True) := by
    rw [windowPrep]
    exact taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h)
      (by fld_taint_decide)
  obtain negRCT : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (negR fld)) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)
  rw [verifyEquationPoints]
  apply RelCT.assoc; apply RelCT.assoc
  refine seq_same (c₁ := windowPrep fld (Point64.bodies fld)) (rdi_ct (fun x h => h.1.context.scratch.rdi) prepCT) w ?_
  have toSkip (x : State) (h : SkipLoopRun R₀ base challenge sig T Aa K S 64 x) :
      SkipRun R₀ base challenge sig T Aa K S 32 x := by
    obtain ⟨s₀, r₀, h⟩ := h
    exact ⟨s₀, r₀, h, Nat.div_eq_of_lt (h.kVal ▸ decodeLE_lt64 _ _), by decide, by decide⟩
  refine VG.RelCT.seq (skipZero_ct.mono (fun x y h => ⟨toSkip x h.1, toSkip y h.2⟩) (fun _ _ h => h)) ?_
  -- From `c` bytes of `k` left: what the runs share.
  refine VG.RelCT.exists_ fun c => ?_
  refine (VG.RelCT.exists_ (P := fun (hc : (32 ≤ c ∧ c ≤ 64 ∧ K / 256 ^ c = 0) ∧
      (∀ j < 64, 8192 ≤ ofs base (off challenge j)) ∧ (∀ j < 32, 8192 ≤ ofs base (off sig (32 + j))) ∧
      S < 2 ^ (8 * 32)) x y =>
      SkipLoopRun R₀ base challenge sig T Aa K S c x ∧ SkipLoopRun R₀ base challenge sig T Aa K S c y)
    fun hc => ?_).mono (fun x y h => by
      obtain ⟨_, _, hf⟩ := h.2.2.2.1
      refine ⟨⟨⟨h.1, h.2.1, h.2.2.1⟩, hf.ctx.kFar, fun j hj => ?_, hf.sVal ▸ decodeLE_lt32 _ _⟩, h.2.2.2⟩
      rw [show off sig (32 + j) = off (off sig 32) j from (Offset.add_add _ _ _).symm]
      exact hf.ctx.sFar j hj) (fun _ _ h => h)
  obtain ⟨⟨hc32, hc64, hK⟩, hkf, hsf, hSlt⟩ := hc
  let fA := Recode.digits 5 K (8 * c)
  let fB := Recode.digits 8 S (8 * 32)
  obtain hdg : Digits fA fB (8 * c + 8) :=
    ⟨by omega_arith, fun p => Recode.digits_le (by decide) p, fun p => Recode.digits_le (by decide) p⟩
  -- The digits.
  have wr (x : State) (h : SkipLoopRun R₀ base challenge sig T Aa K S c x) :
      WP isa recodeAll x (StartRun R₀ base challenge sig T Aa fA fB (8 * c + 8)) := by
    obtain ⟨s₀, r₀, hf'⟩ := h
    have fctx := hf'.ctx
    refine WP.mono (recodeAll_ok fctx.scratch hf'.counter hc32 hc64 fctx.kHeader fctx.sHeader
      fctx.kRead8 fctx.sRead8 fctx.kFar hsf) fun g ⟨gA, gB, gc, kg⟩ => ?_
    rw [hf'.kVal] at gA
    rw [hf'.sVal] at gB
    obtain tf : TableFrame base 56 3160 x.mem g.mem := fun p _ hp => kg.mem p (by omega_arith)
    refine ⟨g, ?_, skipAt_of_recode hf' hK hc32 hc64 kg (fun p hp => ⟨gA p hp, gB p hp⟩) gc⟩
    show tablePoint g.mem base 7552 = r
    rw [tf.point (by decide) (Or.inr (by decide)) (by decide),
      win_tablePoint hf'.keep.mem (by decide) (by decide), r₀]
  refine VG.RelCT.seq (R := fun x y => StartRun R₀ base challenge sig T Aa fA fB (8 * c + 8) x ∧
    StartRun R₀ base challenge sig T Aa fA fB (8 * c + 8) y)
    ((VG.RelCT.wp (recodeAll_ct hc32 hc64 hkf hsf fun x h => by
        obtain ⟨s₀, r₀, hf'⟩ := h
        have fctx := hf'.ctx
        exact ⟨⟨fctx.scratch, fctx.kHeader, fctx.sHeader, fctx.kRead8, fctx.sRead8⟩, hf'.counter, hf'.kVal,
          hf'.sVal⟩) fun x y h => ⟨wr x h.1, wr y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  -- The windows.
  refine VG.RelCT.seq (EdWindows.ct (win := win) hdg) ?_
  obtain hKlt : K < 2 ^ (8 * c) := by
    have := Nat.lt_of_div_eq_zero (by positivity) hK
    rwa [show (256 : Nat) ^ c = 2 ^ (8 * c) by rw [Nat.pow_mul]] at this
  have wn (x : State) (h : LoopRun R₀ base challenge sig T Aa fA fB (8 * c + 8) 0 x) :
      WP isa (.block (negR fld)) x (EqRepPre base (K • Aa + S • (-baseAff)) (-Ra)) := by
    obtain ⟨s₀, r₀, hx⟩ := h
    have gv := hx.value
    simp only [winVal, hiVal, Nat.sub_zero] at gv
    rw [Recode.digits_sum (by decide) hKlt (by omega_arith), Recode.digits_sum (by decide) hSlt (by omega_arith),
      natCast_zsmul, natCast_zsmul] at gv
    refine WP.mono (negR_ok hx.ctx.scratch) fun u ⟨ku, u0, u4⟩ =>
      ⟨hx.ctx.scratch.of_keep ku, by rw [u0]; exact gv, ?_⟩
    rw [u4, win_tablePoint hx.keep.mem (by decide) (by decide), r₀]
    exact hR.neg.proj
  exact seq_same (rdi_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.rdi) negRCT) wn
    (pointEqualRep_ct base _ _)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyCTBody`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RecoverCTRoot`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RecoverCTAdjust`. -/
section
/-! Sign adjustment branches only on the shared public coordinate and sign. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def SignCTPre (base : Addr) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) s fun t =>
      Keep base s t ∧ t.zf = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeWide_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.1 _ (by decide)).trans hb)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kt (by decide)), ?_⟩
  rw [tz, ax]

theorem adjustTail_ct (base : Addr) :
    RelCT isa (fun x y => Scratch x base ∧ Scratch y base ∧ x.zf = y.zf)
      (.seq (.ite .e (.block []) (.block (fieldCode fld [.const 5 0, .sub 0 5 0])))
        (.block (recoverSuccess fld))) (fun _ _ => True) := by
  refine VG.RelCT.seq (M := isa) (R := fun x y => x.gpr .rdi = base ∧ y.gpr .rdi = base)
    (VG.RelCT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · have ht : RelCT isa (fun _ _ => True) (.block []) (fun _ _ => True) := by
      apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
      exact fun _ _ _ => Taint.agree_ofRegs (by simp)
    obtain hw := VG.RelCT.wp (ht.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some true) =>
        And.intro (WP.block_nil h.1.1.rdi) (WP.block_nil h.1.2.1.rdi))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)
  · have ht := (negateBlock_ct (fld := fld) base).mono
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some false) =>
        ⟨h.1.1.rdi, h.1.2.1.rdi⟩) (fun _ _ h => h)
    obtain hw := VG.RelCT.wp ht
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some false) =>
        And.intro (WP.mono (fieldCodeWide_ok h.1.1 [.const 5 0, .sub 0 5 0]) fun _ k => (h.1.1.of_keep k.1).rdi)
          (WP.mono (fieldCodeWide_ok h.1.2.1 [.const 5 0, .sub 0 5 0]) fun _ k => (h.1.2.1.of_keep k.1).rdi))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (recoverAdjustSign fld) (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) s fun t =>
        Scratch t base ∧ t.zf = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨h.1.of_keep kt, by rw [tz, h.2.2]⟩
  obtain ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.rdi, h.2.1.rdi⟩)
    (fun _ _ h => h)
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.X86_64
end

/-! The negative-zero check leaks only the public coordinate and sign. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem testThenSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block [.alu .test .rsi (.reg .rsi)]) (.ite .ne recoverInvalid (recoverAdjustSign fld)))
      (fun _ _ => True) := by
  obtain ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block [.alu .test .rsi (.reg .rsi)]) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block [.alu .test .rsi (.reg .rsi)]) s fun t =>
        SignCTPre base b x t ∧ t.zf = some (!b) := by
    refine WP.mono (testSign_ok b h.2.1) fun t ⟨tz, kt⟩ => ?_
    refine ⟨⟨h.1.of_keeps kt (by simp), (kt.1 _ (by simp)).trans h.2.1, ?_⟩, tz⟩
    rw [kt.2.1]; exact h.2.2
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2, h.2.2.2]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

theorem recoverSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (recoverSign fld) (fun _ _ => True) := by
  obtain ht := (zeroBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.rdi, h.2.1.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldZero 0)) s fun t =>
        SignCTPre base b x t ∧ t.zf = some (decide (x = 0)) := by
    refine WP.mono (fieldZero_ok h.1 0) fun t ⟨tz, kt, tm⟩ => ?_
    refine ⟨⟨h.1.of_keep kt, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩, ?_⟩
    · rw [tm]; exact h.2.2
    · rw [tz, h.2.2]
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverSign]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    exact h.2.1.2.trans h.2.2.2.symm
  · exact (testThenSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-! The two square-root checks branch on public field values. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def RootCTState (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual fld 11 (if minus then 12 else 6)))
      (fun s t => (RootCTState base b y s ∧ s.zf = some (rootCheckValue y minus)) ∧
        (RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus))) := by
  obtain ht : RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual fld 11 (if minus then 12 else 6))) (fun _ _ => True) := by
    cases minus
    · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
      exact fun _ _ h => rdi_agree h.1.1.1.rdi h.2.1.1.rdi
    · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
      exact fun _ _ h => rdi_agree h.1.1.1.rdi h.2.1.1.rdi
  have hw (s : State) (h : RootCTState base b y s) :
      WP isa (.block (fieldEqual fld 11 (if minus then 12 else 6))) s fun t =>
        RootCTState base b y t ∧ t.zf = some (rootCheckValue y minus) := by
    refine WP.mono (fieldEqual_ok h.1.1 11 (if minus then 12 else 6)) fun t ⟨tz, kt, te⟩ => ?_
    refine ⟨⟨⟨h.1.1.of_keep kt, (kt.gpr _ (by decide)).trans h.1.2.1,
      (te 0 (by decide)).trans h.1.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]
  exact (VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem rootAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (recoverSign fld))
      (fun _ _ => True) := by
  obtain ht : RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) s fun t =>
        SignCTPre base b (x * Spec.Ed25519.sqrtM1) t := by
    refine WP.mono (fieldCodeWide_ok h.1 [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) fun t ⟨kt, te⟩ => ?_
    refine ⟨h.1.of_keep kt, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩
    rw [te]
    change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
    rw [h.2.2]
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual fld 11 12)) (.ite .e
        (.seq (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (recoverSign fld)) recoverInvalid))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y true) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual fld 11 6)) (.ite .e (recoverSign fld)
        (.seq (.block (fieldEqual fld 11 12)) (.ite .e
          (.seq (.block (fieldCode fld [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (recoverSign fld)) recoverInvalid))))
      (fun _ _ => True) := by
  refine VG.RelCT.seq (rootCheck_ct base b y false) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (recoverSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = signWord b ∧ env s.mem base 1 = y ∧ env s.mem base 15 = rootPow y

theorem recoverPoint_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    RelCT isa (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      (recoverPoint fld) (fun _ _ => True) := by
  obtain ht := (recoverCandidate_ct (fld := fld) base).mono
    (fun _ _ (h : RecoverCTPre base b y _ ∧ RecoverCTPre base b y _) => ⟨h.1.1.rdi, h.2.1.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RecoverCTPre base b y s) :
      WP isa (recoverCandidate fld) s (RootCTState base b y) := by
    refine WP.mono (recoverCandidate_ok h.1 (by rw [h.2.2.1]; exact h.2.2.2))
      fun t ⟨kt, tx, _, _, tu, _, tv, tn⟩ => ?_
    refine ⟨⟨kt.scratch h.1, (kt.gpr _ (by decide) (by decide)).trans h.2.1, ?_⟩, ?_, ?_, ?_⟩
    · rw [tx, h.2.2.1]
    · rw [tv, h.2.2.1]
    · rw [tu, h.2.2.1]
    · rw [tn, h.2.2.1]
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverPoint]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) (recoverChecks_ct base b y)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyCTDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyCTDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.PointDecodeCT`. -/
section
/-! Canonical point decoding leaks only its public bytes. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]

def DecodeCTPre (base p : Addr) (bs : List Byte) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rdx = p ∧
    (∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) ∧ Spec.Ed25519.bytesAt s.mem p 32 = bs ∧
    env s.mem base 15 = rootPow (decodedY bs)

theorem pointDecode_ct (base p : Addr) (bs : List Byte) :
    RelCT isa (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      (pointDecode fld) (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  obtain ht : RelCT isa (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      (.block pointDecodeLoad) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rdx]) _ (by fld_taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base p bs s) :
      WP isa (.block pointDecodeLoad) s fun t => RecoverCTPre base b y t ∧
        t.zf = some (decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P)) := by
    refine WP.mono (pointDecodeLoad_ok h.1 h.2.1 h.2.2.1) fun t ⟨kt, tb, ty, tz, t15⟩ => ?_
    refine ⟨⟨kt.scratch h.1, ?_, ?_, ?_⟩, ?_⟩
    · rw [tb, h.2.2.2.1]
    · rw [ty, h.2.2.2.1]
    · exact t15.trans h.2.2.2.2
    · rw [tz, h.2.2.2.1]
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : Addr} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .rax = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.X86_64
end

/-! A decoder's public success flag selects the continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem DecodeResult.of_keeps {base : Addr} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (kt : Keeps [] s t) : DecodeResult base p t := by
  cases p with
  | none => exact (kt.1 _ (by simp)).trans h
  | some p => exact ⟨(kt.1 _ (by simp)).trans h.1, by rw [kt.2.1]; exact h.2⟩

theorem decodedThen_ct (base : Addr) (p : Option Spec.Ed25519.Point) (P : State → Prop) (next : Prog isa)
    (hP : ∀ s t, Keeps [] s t → P s → P t)
    (hn : ∀ a, p = some a → RelCT isa
      (fun s t => (P s ∧ point (env s.mem base) 0 1 2 3 = a) ∧
        (P t ∧ point (env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    RelCT isa (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  obtain ht : RelCT isa (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (.block [.alu .test .rax (.reg .rax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)
  have hw (s : State) (h : P s ∧ DecodeResult base p s) :
      WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
        P t ∧ DecodeResult base p t ∧ t.zf = some (!p.isSome) := by
    refine WP.mono (testResult_ok p.isSome (decodeResult_flag h.2)) fun t ⟨tz, kt⟩ => ?_
    exact ⟨hP s t kt h.1, h.2.of_keeps kt, tz⟩
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [decodedThen]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2.2, h.2.2.2.2]
  · cases p with
    | none =>
      apply VG.RelCT.of_false
      intro s t h
      have he := h.2
      simp only [eval, h.1.2.1.2.2, Option.isSome_none, Bool.not_false,
        Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at he
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.1.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-! Decoding R and selecting the public equation continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

def DecodeRCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr)
    (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧ tablePoint s.mem base 7424 = a

theorem verifyStoreR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr}
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a s ∧
      point (env s.mem base) 0 1 2 3 = r) ∧ (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a t ∧
      point (env t.mem base) 0 1 2 3 = r))
      (.seq (.block (pointTableWrite 7552)) (verifyEquationPoints fld (Point64.bodies fld) win)) (fun _ _ => True) := by
  obtain ht := (pointTableWrite_ct base 7552 (by decide)).mono
    (fun s t (h : (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a s ∧
      point (env s.mem base) 0 1 2 3 = r) ∧ (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a t ∧
      point (env t.mem base) 0 1 2 3 = r)) => ⟨h.1.1.1.context.scratch.rdi, h.2.1.1.context.scratch.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a s ∧
      point (env s.mem base) 0 1 2 3 = r) :
      WP isa (.block (pointTableWrite 7552)) s (PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r) := by
    refine WP.mono (pointTableWrite_ok h.1.1.context.scratch 7552 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
    refine ⟨h.1.1.of_keep (kt.mono (by decide) (by decide)), ?_, tv.trans h.2⟩
    exact (kt.mem.point (by decide) (Or.inl (by decide)) (by decide)).trans h.1.2
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (verifyEquationPoints_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR)

/-- R's decoding, with its power in slot 15. -/
theorem decodeRThen_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr}
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun s t => (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a s ∧
      env s.mem base 15 = rootPow (decodedY rbs)) ∧ (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a t ∧
      env t.mem base 15 = rootPow (decodedY rbs))) (decodeRThen fld (Point64.bodies fld) win) (fun _ _ => True) := by
  let P := DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a
  obtain loadCT : RelCT isa (fun s t => (P s ∧ env s.mem base 15 = rootPow (decodedY rbs)) ∧
      (P t ∧ env t.mem base 15 = rootPow (decodedY rbs)))
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))]) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.1.context.scratch.rdi h.2.1.1.context.scratch.rdi
  have loadWP (s : State) (h : P s ∧ env s.mem base 15 = rootPow (decodedY rbs)) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))]) s fun t =>
        P t ∧ DecodeCTPre base sig rbs t := by
    refine WP.mono (loadPointer_ok h.1.1.context.scratch .rdx 7944 (by decide)) fun t ⟨tp, kt⟩ => ?_
    obtain kp : VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    obtain hp := h.1.1.of_keep kp
    exact ⟨⟨hp, by rw [kt.2.1]; exact h.1.2⟩,
      hp.context.scratch, tp.trans h.1.1.context.sigHeader, hp.context.rRead, hp.rBytes,
      by rw [kt.2.1]; exact h.2⟩
  obtain hl := VG.RelCT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  obtain decodeCT := (pointDecode_ct (fld := fld) base sig rbs).mono
    (fun s t (h : (P s ∧ DecodeCTPre base sig rbs s) ∧ (P t ∧ DecodeCTPre base sig rbs t)) =>
      ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : P s ∧ DecodeCTPre base sig rbs s) :
      WP isa (pointDecode fld) s fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint rbs) t := by
    obtain hd := pointDecode_ok (fld := fld) (base := base) (p := sig) h.2.1 h.2.2.1 h.2.2.2.1
      (by rw [h.2.2.2.2.1]; exact h.2.2.2.2.2)
    rw [h.2.2.2.2.1] at hd
    with_reducible apply WP.mono hd
    intro t ht
    have kt := ht.1
    exact ⟨⟨h.1.1.of_keep (PowersKeep.of_decode kt),
      (workspace_tablePoint kt.mem (by decide) (by decide)).trans h.1.2⟩, ht.2⟩
  obtain hd := VG.RelCT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [decodeRThen]
  refine VG.RelCT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply decodedThen_ct base (Spec.Ed25519.decodePoint rbs) P _
  · intro s t kt h
    exact ⟨h.1.of_keep (PowersKeep.of_keeps kt (by simp)), by rw [kt.2.1]; exact h.2⟩
  · intro r hr
    obtain ⟨Ra, hR⟩ := decodePoint_rep hr
    exact verifyStoreR_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR

/-- R's power, at byte 7680. -/
abbrev PowR (base : Addr) (rbs : List Byte) (s : State) : Prop :=
  Proof.X25519.X86_64.F s.mem base 7680 = rootPow (decodedY rbs)

theorem verifyDecodeR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr}
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun s t => (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a s ∧ PowR base rbs s) ∧
      (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a t ∧ PowR base rbs t))
      (verifyDecodeR fld (Point64.bodies fld) win) (fun _ _ => True) := by
  obtain ht := (powerRestore_ct base).mono
    (fun s t (h : (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a s ∧ PowR base rbs s) ∧
      (DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a t ∧ PowR base rbs t)) =>
      ⟨h.1.1.1.context.scratch.rdi, h.2.1.1.context.scratch.rdi⟩) (fun _ _ h => h)
  have hw (s : State) (h : DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a s ∧ PowR base rbs s) :
      WP isa (.block powerRestore) s fun t => DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a t ∧
        env t.mem base 15 = rootPow (decodedY rbs) := by
    refine WP.mono (powerRestore_ok h.1.1.context.scratch) fun t ⟨kt, vt⟩ => ?_
    refine ⟨⟨h.1.1.of_keep (PowersKeep.of_keep kt),
      (workspace_tablePoint kt.mem (by decide) (by decide)).trans h.1.2⟩, ?_⟩
    rw [vt, Function.update_self]
    exact h.2
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [verifyDecodeR]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (decodeRThen_ct base pk sig challenge pkbs rbs sbs kbs a hA)

end VG.Proof.Ed25519.X86_64
end

/-! Decoding the public key selects the public verification continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

theorem verifyStoreA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr}
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    RelCT isa (fun s t => ((VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧ PowR base rbs s) ∧
      point (env s.mem base) 0 1 2 3 = a) ∧ ((VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t ∧
      PowR base rbs t) ∧ point (env t.mem base) 0 1 2 3 = a))
      (.seq (.block (pointTableWrite 7424)) (verifyDecodeR fld (Point64.bodies fld) win)) (fun _ _ => True) := by
  obtain ht := (pointTableWrite_ct base 7424 (by decide)).mono
    (fun s t (h : ((VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧ PowR base rbs s) ∧
      point (env s.mem base) 0 1 2 3 = a) ∧ ((VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t ∧
      PowR base rbs t) ∧ point (env t.mem base) 0 1 2 3 = a)) =>
      ⟨h.1.1.1.context.scratch.rdi, h.2.1.1.context.scratch.rdi⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : (VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧ PowR base rbs s) ∧
      point (env s.mem base) 0 1 2 3 = a) :
      WP isa (.block (pointTableWrite 7424)) s fun t =>
        DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs T a t ∧ PowR base rbs t := by
    refine WP.mono (pointTableWrite_ok h.1.1.context.scratch 7424 (by decide) (by decide))
      fun t ⟨kt, tv, _⟩ => ?_
    refine ⟨⟨h.1.1.of_keep (kt.mono (by decide) (by decide)), tv.trans h.2⟩, ?_⟩
    rw [PowR, kt.mem.field (d := 7680) (by decide) (Or.inr (by decide)) (by decide)]
    exact h.1.2
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (verifyDecodeR_ct base pk sig challenge pkbs rbs sbs kbs a hA)

theorem verifyDecodeA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr} :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t) (verifyDecodeA fld (Point64.bodies fld) win) (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs T
  let Q := fun s => (P s ∧ PowR base rbs s) ∧ env s.mem base 15 = rootPow (decodedY pkbs)
  obtain powCT := decodePowers_ct (fld := fld) base pk sig challenge P (fun _ h => h.context)
    (fun _ _ h k => h.of_keep k)
  have powWP (s : State) (h : P s) : WP isa (decodePowers fld) s Q := by
    refine WP.mono (decodePowers_ok h.context) fun t ⟨kt, t15, tf⟩ => ?_
    exact ⟨⟨h.of_keep kt, by rw [PowR, tf, h.rBytes]⟩, by rw [t15, h.pkBytes]⟩
  obtain hpw := VG.RelCT.wp powCT (fun s t h => ⟨powWP s h.1, powWP t h.2⟩)
  obtain loadCT : RelCT isa (fun s t => Q s ∧ Q t)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7936))]) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.1.context.scratch.rdi h.2.1.1.context.scratch.rdi
  have loadWP (s : State) (h : Q s) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7936))]) s fun t =>
        (P t ∧ PowR base rbs t) ∧ DecodeCTPre base pk pkbs t := by
    refine WP.mono (loadPointer_ok h.1.1.context.scratch .rdx 7936 (by decide)) fun t ⟨tp, kt⟩ => ?_
    obtain kp : VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    obtain hp := h.1.1.of_keep kp
    exact ⟨⟨hp, by rw [PowR, kt.2.1]; exact h.1.2⟩, hp.context.scratch,
      tp.trans h.1.1.context.pkHeader, hp.context.pkRead, hp.pkBytes, by rw [kt.2.1]; exact h.2⟩
  obtain hl := VG.RelCT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  obtain decodeCT := (pointDecode_ct (fld := fld) base pk pkbs).mono
    (fun s t (h : ((P s ∧ PowR base rbs s) ∧ DecodeCTPre base pk pkbs s) ∧
      ((P t ∧ PowR base rbs t) ∧ DecodeCTPre base pk pkbs t)) => ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : (P s ∧ PowR base rbs s) ∧ DecodeCTPre base pk pkbs s) :
      WP isa (pointDecode fld) s fun t =>
        (P t ∧ PowR base rbs t) ∧ DecodeResult base (Spec.Ed25519.decodePoint pkbs) t := by
    obtain hd := pointDecode_ok (fld := fld) (base := base) (p := pk) h.2.1 h.2.2.1 h.2.2.2.1
      (by rw [h.2.2.2.2.1]; exact h.2.2.2.2.2)
    rw [h.2.2.2.2.1] at hd
    with_reducible apply WP.mono hd
    intro t ht
    refine ⟨⟨h.1.1.of_keep (PowersKeep.of_decode ht.1), ?_⟩, ht.2⟩
    rw [PowR, Outside_F ht.1.mem (d := 7680) (by decide) (Or.inr (by decide))]
    exact h.1.2
  obtain hd := VG.RelCT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [verifyDecodeA]
  refine VG.RelCT.seq (hpw.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  rw [decodeAThen]
  refine VG.RelCT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply decodedThen_ct base (Spec.Ed25519.decodePoint pkbs) (fun s => P s ∧ PowR base rbs s) _
  · intro s t kt h
    exact ⟨h.1.of_keep (PowersKeep.of_keeps kt (by simp)), by rw [PowR, kt.2.1]; exact h.2⟩
  · intro a ha
    obtain ⟨Aa, hA⟩ := decodePoint_rep ha
    exact verifyStoreA_ct base pk sig challenge pkbs rbs sbs kbs a hA

end VG.Proof.Ed25519.X86_64
end

/-! The canonical scalar check depends only on the public signature. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

theorem verifyScalar_ct (base pk sig challenge : Addr) :
    RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block verifyScalar) (fun _ _ => True) := by
  obtain ht : RelCT isa (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rdx (.imm 32)])
      (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.scratch.rdi h.2.scratch.rdi
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944)), .alu .add .rdx (.imm 32)]) s
        (fun t => t.gpr .rdx = off sig 32) := by
    change WP isa (.block (([.mov .rdx (.mem (Impl.X25519.X86_64.sc 7944))] : List Instr) ++
      [.alu .add .rdx (.imm 32)])) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .rdx 7944 (by decide)) fun a ⟨ap, _⟩ => ?_
    refine WP.mono (add32_ok a .rdx) fun t ⟨tp, _⟩ => ?_
    rw [tp, ap, h.sigHeader]
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  obtain tailCT : RelCT isa (fun s t => s.gpr .rdx = off sig 32 ∧ t.gpr .rdx = off sig 32)
      (.block (loadScalarWords ++ scalarSubtract)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdx]) _ (by fld_taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.trans h.2.symm
  rw [verifyScalar, List.append_assoc]
  exact blockAppend_ct (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) tailCT

theorem verifyBody_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr} :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t)
      (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld (Point64.bodies fld) win) recoverInvalid)) (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs T
  obtain ht := (verifyScalar_ct base pk sig challenge).mono
    (fun _ _ (h : P _ ∧ P _) => ⟨h.1.context, h.2.context⟩) (fun _ _ h => h)
  have hw (s : State) (h : P s) : WP isa (.block verifyScalar) s fun t =>
      P t ∧ t.cf = some (decide (Spec.Ed25519.decodeLE sbs < Spec.Ed25519.L)) := by
    refine WP.mono (verifyScalar_ok h.context.scratch h.context.sigHeader h.context.scalarRead) fun t ⟨kt, _, tc⟩ => ?_
    exact ⟨h.of_keep (PowersKeep.of_keep kt), by rw [tc, h.sBytes]⟩
  obtain hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (verifyDecodeA_ct base pk sig challenge pkbs rbs sbs kbs).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyMain`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifySetup`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyBody`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.VerifyDecodeR`. -/
section
/-! Reject an invalid R encoding or evaluate the complete equation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 Edwards
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

def equationWithR (r : Option Spec.Ed25519.Point) (a : Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match r with
  | none => false
  | some r => Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul challenge a))

/-- R's decoding, with its power in slot 15 (`hpow`). -/
theorem decodeRThen_ok {s : State} {base pk sig challenge : Addr}
    {Aa : EPoint dZ} (h : VerifyContext s base pk sig challenge)
    (hA : Rep (tablePoint s.mem base 7424) Aa)
    (hpow : env s.mem base 15 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem sig 32))) :
    WP isa (decodeRThen fld (Point64.bodies fld) win) s fun t => VerifyKeep base s t ∧
      t.gpr .rax = signWord (equationWithR
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (tablePoint s.mem base 7424)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [decodeRThen]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_)
  obtain kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  obtain ha := h.of_keep kap
  apply WP.seq
  obtain hd := pointDecode_ok (fld := fld) (base := base) (p := sig) ha.scratch (ap.trans h.sigHeader) ha.rRead
    (by rw [ka.2.1]; exact hpow)
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem sig 32) = decoded at hd
  rw [ka.2.1] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  obtain kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  obtain kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c r kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, equationWithR, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    obtain kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7552 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    obtain kabcd := kabc.trans (kd.mono (by decide) (by decide))
    obtain hd := h.of_keep kabcd
    obtain da : tablePoint d.mem base 7424 = tablePoint s.mem base 7424 := by
      rw [kd.mem.point (by decide) (Or.inl (by decide)) (by decide), kc.2.1,
        workspace_tablePoint kb.mem (by decide) (by decide), ka.2.1]
    obtain ⟨Ra, hRa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyEquationPoints_ok hd.scratch hd.sigHeader hd.challengeHeader
      hd.scalarBytes hd.scalarFar hd.challengeRead hd.challengeFar hd.kRead8 hd.sRead8 (by rw [da]; exact hA)
      (by rw [dp, cp]; exact hRa) rfl hd.bTab) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, da, verifyKeep_bytes kabcd h.scalarFar, verifyKeep_bytes kabcd h.challengeFar,
      hp, hy, equationWithR]

/-- R's decoding, with its power at byte 7680 (`hR`). -/
theorem verifyDecodeR_ok {s : State} {base pk sig challenge : Addr}
    {Aa : EPoint dZ} (h : VerifyContext s base pk sig challenge)
    (hA : Rep (tablePoint s.mem base 7424) Aa)
    (hR : Proof.X25519.X86_64.F s.mem base 7680 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem sig 32))) :
    WP isa (verifyDecodeR fld (Point64.bodies fld) win) s fun t => VerifyKeep base s t ∧
      t.gpr .rax = signWord (equationWithR
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (tablePoint s.mem base 7424)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeR]
  refine WP.seq (WP.mono (powerRestore_ok h.scratch) fun r ⟨kr, vr⟩ => ?_)
  obtain krp : VerifyKeep base s r := PowersKeep.of_keep kr
  obtain ra : tablePoint r.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint kr.mem (by decide) (by decide)
  refine WP.mono (decodeRThen_ok (h.of_keep krp) (by rw [ra]; exact hA)
    (by rw [vr, Function.update_self, verifyKeep_bytes krp h.rFar]; exact hR)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨krp.trans kt, ?_⟩
  rw [tv, ra, verifyKeep_bytes krp h.rFar, verifyKeep_bytes krp h.scalarFar,
    verifyKeep_bytes krp h.challengeFar]

end VG.Proof.Ed25519.X86_64
end

/-! Reject an invalid public key encoding before computing the equation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

def decodedEquation (a r : Option Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match a with
  | none => false
  | some a => equationWithR r a scalar challenge

/-- A's decoding, with its power in slot 15 (`hpow`) and R's at byte 7680 (`hR`). -/
theorem decodeAThen_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge)
    (hpow : env s.mem base 15 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem pk 32)))
    (hR : Proof.X25519.X86_64.F s.mem base 7680 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem sig 32))) :
    WP isa (decodeAThen fld (Point64.bodies fld) win) s fun t => VerifyKeep base s t ∧
      t.gpr .rax = signWord (decodedEquation
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [decodeAThen]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .rdx 7936 (by decide)) fun a ⟨ap, ka⟩ => ?_)
  obtain kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  obtain ha := h.of_keep kap
  apply WP.seq
  obtain hd := pointDecode_ok (fld := fld) (base := base) (p := pk) ha.scratch (ap.trans h.pkHeader) ha.pkRead
    (by rw [ka.2.1]; exact hpow)
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem pk 32) = decoded at hd
  rw [ka.2.1] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  obtain kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  obtain kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c p kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, decodedEquation, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    obtain kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7424 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    obtain kabcd := kabc.trans (kd.mono (by decide) (by decide))
    obtain ⟨Aa, hAa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyDecodeR_ok (h.of_keep kabcd) (by rw [dp, cp]; exact hAa)
      (by rw [kd.mem.field (d := 7680) (by decide) (Or.inr (by decide)) (by decide), kc.2.1,
        Outside_F kb.mem (d := 7680) (by decide) (Or.inr (by decide)), ka.2.1, verifyKeep_bytes kabcd h.rFar]
          exact hR))
      fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, verifyKeep_bytes kabcd h.rFar, verifyKeep_bytes kabcd h.scalarFar,
      verifyKeep_bytes kabcd h.challengeFar, hp, hy, decodedEquation]

theorem verifyDecodeA_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (verifyDecodeA fld (Point64.bodies fld) win) s fun t => VerifyKeep base s t ∧
      t.gpr .rax = signWord (decodedEquation
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeA]
  refine WP.seq (WP.mono (decodePowers_ok h) fun p ⟨kp, p15, pf⟩ => ?_)
  refine WP.mono (decodeAThen_ok (h.of_keep kp) (by rw [verifyKeep_bytes kp h.pkFar]; exact p15)
    (by rw [verifyKeep_bytes kp h.rFar]; exact pf)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨kp.trans kt, ?_⟩
  rw [tv, verifyKeep_bytes kp h.pkFar, verifyKeep_bytes kp h.rFar, verifyKeep_bytes kp h.scalarFar,
    verifyKeep_bytes kp h.challengeFar]

end VG.Proof.Ed25519.X86_64
end

/-! The strict scalar check and decoding branches implement verifyEquation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

private theorem decodedEquation_order (a r : Option Spec.Ed25519.Point) (s k : Nat) :
    (match a, r with
      | some a, some r => decide (s < Spec.Ed25519.L) &&
          Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))
      | _, _ => false) = (decide (s < Spec.Ed25519.L) && decodedEquation a r s k) := by
  cases a <;> cases r <;> simp only [decodedEquation, equationWithR, Bool.and_false]

private theorem verifyEquation_order (pk sig challenge : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : challenge.length = 64) :
    Spec.Ed25519.verifyEquation pk sig challenge =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        decodedEquation (Spec.Ed25519.decodePoint pk) (Spec.Ed25519.decodePoint (sig.take 32))
          (Spec.Ed25519.decodeLE (sig.drop 32)) (Spec.Ed25519.decodeLE challenge)) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  exact decodedEquation_order _ _ _ _

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : Addr) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m pk 32)
      (Spec.Ed25519.bytesAt m sig 64) (Spec.Ed25519.bytesAt m challenge 64) =
    (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32) < Spec.Ed25519.L) &&
      decodedEquation (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m challenge 64))) := by
  rw [verifyEquation_order _ _ _ (bytesAt_length ..) (bytesAt_length ..) (bytesAt_length ..),
    signatureBytes_take, signatureBytes_drop]

theorem verifyBody_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld (Point64.bodies fld) win) recoverInvalid)) s fun t =>
      VerifyKeep base s t ∧ t.gpr .rax = signWord
        (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem pk 32)
          (Spec.Ed25519.bytesAt s.mem sig 64) (Spec.Ed25519.bytesAt s.mem challenge 64)) := by
  refine WP.seq (WP.mono (verifyScalar_ok h.scratch h.sigHeader h.scalarRead) fun a ⟨ka, am, ac⟩ => ?_)
  obtain kap : VerifyKeep base s a := PowersKeep.of_keep ka
  apply WP.ite _ ac
  · intro ht
    refine WP.mono (verifyDecodeA_ok (h.of_keep kap)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans kt, ?_⟩
    rw [am] at tv
    rw [verifyEquation_bytes, ht, Bool.true_and]
    exact tv
  · intro hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans (PowersKeep.of_keep kt), ?_⟩
    rw [verifyEquation_bytes, hf, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.X86_64
end

/-! Save the ABI registers and retain the three public input pointers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside ea_at word_writeW_sep word_writeW_self)

theorem verifyPrepare_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdx), .mov .rdx (.reg .rcx)]) s fun t =>
      t.gpr .rax = s.gpr .rdx ∧ t.gpr .rdx = s.gpr .rcx ∧ Keeps [.rax, .rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem verifyHeaders_ok {s : State} {base : Addr} (hb : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t =>
      t.gpr .rdi = base ∧ (∀ r, r ≠ .rdi → r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base 7936 32 s.mem t.mem ∧
      t.mem.readW (off base 7936) 64 = s.gpr .rdi ∧
      t.mem.readW (off base 7944) 64 = s.gpr .rsi ∧
      t.mem.readW (off base 7952) 64 = s.gpr .rax ∧
      t.mem.readW (off base 7960) 64 = s.syms baseOddSym := by
  have hw' (d : Nat) (hd : d + 8 ≤ 8192) : InRegions s.wr (off base d) 8 :=
    ⟨_, hw, Offset.contains_base _ hd (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [verifyHeaders, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, Proof.X25519.X86_64.ea_sc, hb, hw' 7936 (by decide), hw' 7944 (by decide),
    hw' 7952 (by decide), hw' 7960 (by decide), RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], rfl, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((Outside.refl base 7936 32 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _
  all_goals simp (disch := decide) only [word_writeW_sep, word_writeW_self]
  rfl

theorem verifyFinishArgs_ok (s : State) :
    WP isa (.block [.mov .rdx (.reg .rdi)]) s fun t =>
      t.gpr .rdx = s.gpr .rdi ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg_self,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Ed25519.X86_64
end

/-! Verification preserves the ABI and checks the original input buffers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Saved)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

def verifyLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 64⟩,
      ⟨s.syms baseOddSym, 16384⟩] ∧
    s.wr = [⟨s.gpr .rcx, 8192⟩] ∧
    (⟨s.gpr .rdi, 32⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsi, 64⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rdx, 64⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧
    (⟨s.syms baseOddSym, 16384⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    ∀ i < 2048, s.mem.readW (s.syms baseOddSym + BitVec.ofNat 64 (8 * i)) 64 = baseOddWords.getD i 0
  post s t := t.gpr .rax = signWord (Spec.Ed25519.verifyEquation
    (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 64) (bytesAt s.mem (s.gpr .rdx) 64))
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧
    bytesAt s.mem (s.gpr .rdi) 32 = bytesAt t.mem (t.gpr .rdi) 32 ∧
    bytesAt s.mem (s.gpr .rsi) 64 = bytesAt t.mem (t.gpr .rsi) 64 ∧
    bytesAt s.mem (s.gpr .rdx) 64 = bytesAt t.mem (t.gpr .rdx) 64 ∧
    s.syms baseOddSym = t.syms baseOddSym

/-- The static of `-B`'s multiples, from the contract: its words, where it can be read, and
apart from the scratch. -/
theorem baseTbl_of_contract {s : State} {base : Addr}
    (hrd : (⟨s.syms baseOddSym, 16384⟩ : Region) ∈ s.rd)
    (hd : (⟨s.syms baseOddSym, 16384⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hheld : ∀ i < 2048,
      s.mem.readW (s.syms baseOddSym + BitVec.ofNat 64 (8 * i)) 64 = baseOddWords.getD i 0) :
    BaseTbl s base (s.syms baseOddSym) :=
  ⟨fun j hj => baseTbl_entry hheld j hj,
    fun d n hdn => ⟨_, List.mem_append_left _ hrd, Offset.contains_base _ hdn (by omega_arith)⟩,
    fun i hi => farScratch hd hi (by decide)⟩

theorem verifyBytes_frame {m m' : Mem} {base p : Addr} {n : Nat}
    (hf : Frame [⟨base, 8192⟩] m m') (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) (by simpa only [List.mem_singleton, forall_eq]) hn (List.mem_range.mp hi)

structure VerifyStarted (s t : State) : Prop where
  context : VerifyContext t (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
  saved : Saved (s.gpr .rcx) s.gpr t.mem
  frame : Frame [⟨s.gpr .rcx, 8192⟩] s.mem t.mem
  rsp : t.gpr .rsp = s.gpr .rsp
  header : t.mem.readW (off (s.gpr .rcx) 7960) 64 = s.syms baseOddSym

theorem verifySetup_state_ok {s : State} (hs : verifyLocal.pre s) :
    WP isa (.block verifySetup) s (VerifyStarted s) := by
  obtain ⟨hr, hw, hpk, hsig, hchallenge, hret, hn, hbd, hheld⟩ := hs
  obtain hbt : BaseTbl s (s.gpr .rcx) (s.syms baseOddSym) :=
    baseTbl_of_contract (by rw [hr]; simp) hbd hheld
  obtain hws : (⟨s.gpr .rcx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_singleton_self _
  rw [verifySetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (verifyPrepare_ok s) fun a ⟨ach, asc, ka⟩ asy => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok asc (ka.2.2.2 ▸ hws)) fun b ⟨gb, rb, wb, mb, svb⟩ bsy => ?_
  obtain bs : b.gpr .rdx = s.gpr .rcx := (congrFun gb _).trans asc
  refine WP.mono (verifyHeaders_ok bs (by rw [wb, ka.2.2.2]; exact hws))
    fun c ⟨cs, gc, rc, wc, mc, cp, cr, cc, cT⟩ => ?_
  obtain fm : Frame [⟨s.gpr .rcx, 8192⟩] s.mem c.mem := by
    obtain f := (scratchFrame mb (by decide)).trans (scratchFrame mc (by decide))
    rw [ka.2.1] at f
    exact f
  obtain sv : Saved (s.gpr .rcx) s.gpr c.mem := by
    obtain v := svb.outside mc (by decide)
    intro rd hrd
    rw [v rd hrd]
    apply ka.1
    simp only [Impl.X25519.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hc : VerifyContext c (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) := by
    obtain rr : c.rd = s.rd := rc.trans (rb.trans ka.2.2.1)
    obtain ww : c.wr = s.wr := wc.trans (wb.trans ka.2.2.2)
    refine ⟨⟨cs, ww ▸ hws, hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cp, gb, ka.1 .rdi (by decide)]
    · rw [cr, gb, ka.1 .rsi (by decide)]
    · rw [cc, gb, ach]
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega_arith)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show d + 8 ≤ 64 by omega_arith) (by omega_arith)⟩
    · intro d hd
      rw [show off (off (s.gpr .rsi) 32) d = off (s.gpr .rsi) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 8 ≤ 64 by omega_arith) (by omega_arith)⟩
    · intro i hi
      rw [show off (off (s.gpr .rsi) 32) i = off (s.gpr .rsi) (32 + i) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + i + 1 ≤ 64 by omega_arith) (by omega_arith)⟩
    · intro i hi
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show i + 1 ≤ 64 by omega_arith) (by omega_arith)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega_arith)⟩
    · intro i hi; exact farScratch hpk hi (by decide)
    · intro i hi; exact farScratch hsig (by omega_arith) (by decide)
    · intro i hi
      rw [show off (off (s.gpr .rsi) 32) i = off (s.gpr .rsi) (32 + i) from Offset.add_add ..]
      exact farScratch hsig (by omega_arith) (by decide)
    · intro i hi; exact farScratch hchallenge hi (by decide)
    · rw [cT, bsy, asy]
      exact hbt.of_mem rr ww fun p hp => fm p fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        change ¬ (p - s.gpr .rcx).toNat + 1 ≤ 8192
        change 8192 ≤ (p - s.gpr .rcx).toNat at hp
        omega_arith
  exact ⟨hc, sv, fm, by rw [gc _ (by decide) (by decide), gb, ka.1 _ (by decide)], by rw [cT, bsy, asy]⟩

theorem verify_correct {s : State} (hs : verifyLocal.pre s) :
    WP isa (verifyEquationWith fld (Point64.bodies fld) win) s fun t => gprPreserved s t ∧ verifyLocal.post s t := by
  have hpk := hs.2.2.1
  have hsig := hs.2.2.2.1
  have hchallenge := hs.2.2.2.2.1
  have hret := hs.2.2.2.2.2.1
  rw [verifyEquationWith]
  refine WP.seq (WP.mono (verifySetup_state_ok hs) fun c hc0 => ?_)
  have hc := hc0.context
  have sv := hc0.saved
  have fm := hc0.frame
  refine WP.seq (WP.mono (verifyBody_ok hc) fun d ⟨kd, dv⟩ => ?_)
  obtain md := tableFrame_work kd.mem (by decide) (by decide)
  obtain svd := sv.outside md (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFinishArgs_ok d) fun e ⟨es, ke⟩ => ?_
  obtain er : e.gpr .rdx = s.gpr .rcx := es.trans (kd.scratch hc.scratch).rdi
  refine WP.mono (scalarRestore_ok (g := s.gpr) er (by rw [ke.2.2.2, kd.wr]; exact hc.scratch.wr)
    (by rw [ke.2.1]; exact svd)) fun t ⟨tr, gt, mt, _, _⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.rbx, 0) (by decide)
    · exact tr (.rbp, 8) (by decide)
    · rw [gt _ (by decide), ke.1 _ (by decide), kd.gpr _ (by decide) (by decide) (by decide),
        hc0.rsp]
    · exact tr (.r12, 16) (by decide)
    · exact tr (.r13, 24) (by decide)
    · exact tr (.r14, 32) (by decide)
    · exact tr (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rcx, 8192⟩] s.mem t.mem := by
      rw [mt, ke.2.1]; exact fm.trans (scratchFrame md (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton, forall_eq]) (by decide)
  · change t.gpr .rax = _
    rw [gt _ (by decide), ke.1 _ (by decide), dv,
      verifyBytes_frame fm hpk (by decide), verifyBytes_frame fm hsig (by decide),
      verifyBytes_frame fm hchallenge (by decide)]

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyCT`. -/
section
/-! Complete verification leaks only the inputs declared public by its contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

theorem VerifyStarted.public {s t : State} (hs : verifyLocal.pre s) (h : VerifyStarted s t) :
    VerifyPublic (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 32)
      (bytesAt s.mem (off (s.gpr .rsi) 32) 32) (bytesAt s.mem (s.gpr .rdx) 64)
      (s.syms baseOddSym) t := by
  obtain hm := verifyBytes_frame h.frame hs.2.2.2.1 (by decide)
  obtain hr := congrArg (List.take 32) hm
  obtain hscalar := congrArg (List.drop 32) hm
  rw [signatureBytes_take, signatureBytes_take] at hr
  rw [signatureBytes_drop, signatureBytes_drop] at hscalar
  exact ⟨h.context, verifyBytes_frame h.frame hs.2.2.1 (by decide), hr, hscalar,
    verifyBytes_frame h.frame hs.2.2.2.2.1 (by decide), h.header⟩

theorem VerifyStarted.public_right {s u t : State} (hu : verifyLocal.pre u)
    (hp : verifyLocal.pub s u) (h : VerifyStarted u t) :
    VerifyPublic (s.gpr .rcx) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 32)
      (bytesAt s.mem (off (s.gpr .rsi) 32) 32) (bytesAt s.mem (s.gpr .rdx) 64)
      (s.syms baseOddSym) t := by
  obtain ht := h.public hu
  obtain ⟨_, pk, sig, challenge, base, pbs, sigbs, kbs, sy⟩ := hp
  obtain rbs := congrArg (List.take 32) sigbs
  obtain sbs := congrArg (List.drop 32) sigbs
  rw [signatureBytes_take, signatureBytes_take] at rbs
  rw [signatureBytes_drop, signatureBytes_drop] at sbs
  rw [← pbs, ← rbs, ← sbs, ← kbs, ← pk, ← sig, ← challenge, ← base, ← sy] at ht
  exact ht

theorem verifyFinish_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

theorem verifyBody_rdi_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) {T : Addr} :
    RelCT isa (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t)
      (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld (Point64.bodies fld) win) recoverInvalid))
      (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) := by
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) :
      WP isa (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld (Point64.bodies fld) win) recoverInvalid)) s
        (fun t => t.gpr .rdi = base) :=
    WP.mono (verifyBody_ok h.context) fun _ kt => (kt.1.scratch h.context.scratch).rdi
  exact (VG.RelCT.wp (verifyBody_ct base pk sig challenge pkbs rbs sbs kbs)
    (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub (verifyEquationWith fld (Point64.bodies fld) win) := by
  obtain setupCT : RelCT isa (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      (.block verifySetup) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rcx]) _ (by fld_taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.2.2.2.2.2.2.1
  obtain hp := withRuns setupCT (fun s t h => ⟨verifySetup_state_ok h.1, verifySetup_state_ok h.2.1⟩)
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  rw [verifyEquationWith]
  refine VG.RelCT.seq hp ?_
  intro s t ts tt s' t' ⟨_, a, b, hab, ha, hb⟩ es et
  obtain pa := ha.public hab.1
  obtain pb := hb.public_right hab.2.1 hab.2.2
  exact VG.RelCT.seq
    (verifyBody_rdi_ct (a.gpr .rcx) (a.gpr .rdi) (a.gpr .rsi) (a.gpr .rdx)
      (bytesAt a.mem (a.gpr .rdi) 32) (bytesAt a.mem (a.gpr .rsi) 32)
      (bytesAt a.mem (off (a.gpr .rsi) 32) 32) (bytesAt a.mem (a.gpr .rdx) 64))
    (verifyFinish_ct (a.gpr .rcx)) _ _ _ _ _ _ ⟨pa, pb⟩ es et

end VG.Proof.Ed25519.X86_64
end

/-! The complete verifier satisfies the merged specification and leakage contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]
variable {win : Prog isa} [EdWindows win]

/-- Every load of MXCSR by the code is between saving it in `r11` and loading
it back (`ctlOk`): checked by evaluating it, for each `fld` and `win` it is
registered with. -/
abbrev MxcsrOk (c : Prog isa) : Prop := ctlOk c = true

theorem verify_ok (hmx : MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)) (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa (verifyEquationWith fld (Point64.bodies fld) win) s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verify_correct (fld := fld) (win := win) hs
  exact ⟨t, s', he, abiPreserved_of_ctl hmx he h.1, h.2⟩

end VG.Proof.Ed25519.X86_64

end

end

/-!
# Verification calling the decoding and point functions: `Verified`

Untrusted: everything here is checked by Lean. The registered code,
`verifyEquation fld win'`, calls the decoding stages and point functions (`Point64.calls`); its
calls run as their bodies would inlined (`Code.inline`), which gives
`verifyEquationWith fld (Point64.bodies fld) win` for the windows `win` that
`win'` inlines to (`verifyEquation_inline`), the code `VerifyVerified.lean`
proves correct and constant time. `Verified.of_inline` moves the proof to the
calls, with 8 bytes of stack for their return address, which no buffer
overlaps (`Sig.clear_of_pre_consts`); the postcondition reads only `rax`.
`verify_ok_calls` is the same for a caller of the checker, which provides the
8 bytes (`verifyLocal8`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld] {win : Prog isa} [EdWindows win]

omit [EdArith fld] [EdWindows win] in
/-- The registered code, its calls inlined. -/
theorem verifyEquation_inline {win' : Prog isa} (h : win'.inline = win) :
    (verifyEquation fld win').inline = verifyEquationWith fld (Point64.bodies fld) win := by
  subst h
  rfl

/-- `verifyLocal`, with the 8 bytes below `rsp` apart from every region: room for a call's return
address. -/
def verifyLocal8 : Contract isa where
  pre s := verifyLocal.pre s ∧ Clear (hole (s.gpr .rsp)) s
  post := verifyLocal.post
  pub := verifyLocal.pub

/-- The registered code meets `verifyLocal8`. -/
theorem verify_ok_calls {win' : Prog isa} (hinl : win'.inline = win)
    (hok : (verifyEquation fld win').InlineOk = true)
    (hmx : MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)) (s : State) (hs : verifyLocal8.pre s) :
    ∃ t s', Exec isa (verifyEquation fld win') s t s' ∧ abiPreserved s s' ∧ verifyLocal8.post s s' := by
  obtain ⟨t, b, he, ha, hp⟩ := verify_ok hmx s hs.1
  rw [← verifyEquation_inline hinl] at he
  obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inline hok he hs.2
  exact ⟨ta, _, ha', abiPreserved_patch hv u ha, hp⟩

/-- The registered code is constant time under `verifyLocal8`. -/
theorem verify_ct_calls {win' : Prog isa} (hinl : win'.inline = win)
    (hok : (verifyEquation fld win').InlineOk = true)
    (hmx : MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)) :
    ConstantTime isa verifyLocal8.pre verifyLocal8.pub (verifyEquation fld win') := by
  have e := verifyEquation_inline (fld := fld) hinl
  refine ConstantTime.of_inline hok (fun s hs => ?_) (fun _ h => h.2) (fun _ _ _ _ hp => hp.1) ?_
  · obtain ⟨t, s', he, -⟩ := verify_ok hmx s hs.1
    exact ⟨t, s', e ▸ he⟩
  · rw [e]
    exact fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => verify_ct s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

/-- What a caller of the checker `verifyEquation fld win'` needs of its code: the windows `win` its
calls inline to, with their proofs, the inlining's condition and MXCSR's restores. Decided for each
checker in the registration file. -/
structure CallCode (fld : Arith) (win' : Prog isa) : Prop where
  ok : ∃ win : Prog isa, EdWindows win ∧ win'.inline = win ∧ (verifyEquation fld win').InlineOk = true ∧
    MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)

theorem CallCode.verified {win' : Prog isa} (h : CallCode fld win') :
    (∀ s, verifyLocal8.pre s → ∃ t s', Exec isa (verifyEquation fld win') s t s' ∧ abiPreserved s s' ∧
      verifyLocal8.post s s') ∧
    ConstantTime isa verifyLocal8.pre verifyLocal8.pub (verifyEquation fld win') := by
  obtain ⟨win, hw, hinl, hok, hmx⟩ := h.ok
  exact ⟨verify_ok_calls (win := win) hinl hok hmx, verify_ct_calls (win := win) hinl hok hmx⟩

end VG.Proof.Ed25519.X86_64
