module

public import VerifiedGarbage.Proof.X25519.RISCV64.Base
public import VerifiedGarbage.Proof.Ed25519.RISCV64.BaseContract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.RISCV64.Base
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.BaseContract
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_x25519_base` on RISC-V, verified

The function meets `x25519BaseContract` under `abi.withConsts combConsts`
(the comb's table), with no stack: the proof against the contract's facts
by register (`baseC`: `baseR` without the table, and what the table adds),
which it implies (`consts_implies`), and a state satisfying it, with the
table at `0x100000`. Only the pointers and the table's address are public
(`x25519Base_ct`, by taint tracking: the scalar's digits select the table's
entries and the signs only by masks).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64.Base

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64 VG.Impl.X25519.RISCV64.Base
open VG.Proof.Ed25519.RISCV64

/-- `x25519BaseContract` by register, without the table: `out` in `a0`, `scalar` in `a1`,
`scratch` in `a2`. -/
def baseR : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 32⟩
    let sc : Region := ⟨s.gpr .a1, 32⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ (s.gpr .a2).toNat % 8 = 0 ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .a0) 32 =
    Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem (s.gpr .a1) 32) Spec.X25519.basePoint
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

/-- `baseR` with the comb's table (`abi.withConsts`). -/
def baseC : Contract isa where
  pre s := baseR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 0 s
  post := baseR.post
  pub s₁ s₂ := baseR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem base_ok' (s : State) (hs : baseC.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseC.post s s' := by
  obtain ⟨⟨a, b, c, d, e⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at *
  obtain ⟨-, tal, tfit, words, twr, -⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .a1, 32⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := x25519Base_ok
    ⟨hrd, b, c, d, e, tal, tfit, words, twr _ (by rw [b]; simp)⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

theorem x25519Base_ct : ConstantTime isa baseC.pre baseC.pub x25519Base :=
  VG.Taint.constantTime (A := taintSym [combSym]) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨⟨h0, h1, h2, hsp⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

/-- A state satisfying the precondition, without the table. -/
def baseSat : State where
  gpr r := match r with | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem baseR_implies : baseR.Implies (Spec.X25519.x25519BaseContract RISCV64.abi) := by
  contract_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, baseR,
    RISCV64.abi, RISCV64.argRegs] [baseSat] using baseSat

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  have h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- `baseSat` with the table. -/
def baseSatC : State :=
  { baseSat with mem := tblMem, rd := baseSat.rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem baseC_sat : (Spec.X25519.x25519BaseContract (RISCV64.abi.withConsts combConsts)).pre baseSatC := by
  have hl := combWords_length
  have held := tblMem_held
  change (Spec.X25519.x25519BaseContract (RISCV64.abi.withConsts [(combSym, combWords)])).pre baseSatC
  generalize combWords = W' at hl held ⊢
  generalize e : baseSatC = s
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, RISCV64.abi, RISCV64.argRegs,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem x25519Base_verified :
    Verified RISCV64.target x25519Base (Spec.X25519.x25519BaseContract (RISCV64.abi.withConsts combConsts)) :=
  Verified.of_correct base_ok' x25519Base_ct
    (consts_implies (kR := baseR) baseR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨baseSatC, baseC_sat⟩)

end VG.Proof.X25519.RISCV64.Base
