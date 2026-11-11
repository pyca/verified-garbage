module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
public import VerifiedGarbage.Proof.Bignum.RISCV64.Reach
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Reach
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: constant time, the front

The public data of a run (`dataOf`): the argument registers, the stack
arguments and `n`'s bytes. Two runs are related by `Two` for the same public
data. The taint analysis keeps memory secret, so the working space's
address, from the stack, is pinned once loaded (`L1`); the code's list of
programs (`crtF`) is cut after each later block that loads the header's
words (`Reach.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum.RISCV64 (Scr add_ofNat_zero)

variable {pc : Bool}

/-- The argument registers of `vg_rsa_private_crt`, and with `pc`, of
`vg_rsa_private_crt_precomputed`: `s1` too. -/
abbrev argRegsG (pc : Bool) : List Reg := if pc then argRegs ++ [.s1] else argRegs

/-- The public data of a run. -/
def dataOf (pc : Bool) (s : State) : List (BitVec 64) × List (BitVec 64) × List Byte :=
  ((argRegsG pc).map s.gpr, (List.range 10).map (stackArg s),
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)

/-- The precondition: `fnContract`'s, or with `pc`, `fnContractP`'s. -/
def preG : Bool → State → Prop
  | false => fnContract.pre
  | true => fnContractP.pre

/-- The regions read beyond `baseRd`: with `pc`, the cached values'. -/
def xRd : Bool → State → List Region
  | false, _ => []
  | true, s => [r2R s]

theorem preG_core {s : State} (h : preG pc s) : preCore (baseRd s ++ xRd pc s) s := by
  cases pc
  · show preCore (baseRd s ++ []) s; rw [List.append_nil]; exact h
  · exact h.1

/-- On entry. -/
def C0 (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  preG pc s ∧ dataOf pc s = d

theorem C0.pf {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s : State} (h : C0 pc d s) : PF s :=
  pre_factsG (preG_core h.1)

/-- What the public data fixes. -/
structure DataEq (pc : Bool) (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a3 : s₀.gpr .a3 = s₀'.gpr .a3
  a4 : s₀.gpr .a4 = s₀'.gpr .a4
  a5 : s₀.gpr .a5 = s₀'.gpr .a5
  a6 : s₀.gpr .a6 = s₀'.gpr .a6
  a7 : s₀.gpr .a7 = s₀'.gpr .a7
  s1 : pc = true → s₀.gpr .s1 = s₀'.gpr .s1
  sa : ∀ i < 10, stackArg s₀ i = stackArg s₀' i
  nb : Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat =
    Spec.Rsa.bytesAt s₀'.mem (s₀'.gpr .a2) (s₀'.gpr .a3).toNat

theorem dataEq_of {s₀ s₀' : State} (h : dataOf pc s₀ = dataOf pc s₀') : DataEq pc s₀ s₀' := by
  have h1 : (argRegsG pc).map s₀.gpr = (argRegsG pc).map s₀'.gpr := congrArg Prod.fst h
  have h2 : (List.range 10).map (stackArg s₀) = (List.range 10).map (stackArg s₀') :=
    congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  have m := List.map_inj_left.mp h1
  have a : ∀ r ∈ argRegs, r ∈ argRegsG pc := fun r hr => by
    cases pc
    · exact hr
    · exact List.mem_append_left _ hr
  exact ⟨m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)),
    m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)),
    fun hp => m _ (by subst hp; decide), fun i hi => List.map_inj_left.mp h2 i (List.mem_range.mpr hi), h3⟩

theorem two_data {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') : DataEq pc s₀ s₀' := dataEq_of (h.2.trans h'.2.symm)

theorem pins_C0 : Pins (C0 pc) [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  have E := two_data h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.a0, E.a1, E.a2, E.a3, E.a4, E.a5, E.a6, E.a7]

/-- After loading the working space's address. -/
def L1 (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  ∃ s₀, C0 pc d s₀ ∧ s.gpr .t0 = stackArg s₀ 8 ∧ Keep [.t0] s₀ s

theorem pins_L1 : Pins (L1 pc) [.t0, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] := by
  rintro d s₁ s₂ ⟨s₀, h₀, a0', k⟩ ⟨s₀', h₀', b0', k'⟩ r hr
  have E := two_data h₀ h₀'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0', b0', E.sa 8 (by decide)]
  all_goals rw [k.gpr (by decide), k'.gpr (by decide)]
  exacts [E.a0, E.a1, E.a2, E.a3, E.a4, E.a5, E.a6, E.a7]

theorem loadS_L1 {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s : State} (h : C0 pc d s) :
    WP isa (.block [.addSp .t0 64, .load .d .t0 .t0 0]) s (L1 pc d) := by
  have hp := preG_core h.1
  obtain ⟨hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl, alS, alsp⟩ := hp
  have hst : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := by
    refine ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; exact List.mem_append_left _ (by simp [baseRd])), ?_⟩
    show (s.sp + BitVec.ofNat 64 64 - (s.sp + BitVec.ofNat 64 (8 * 0))).toNat + 8 ≤ 80
    rw [show 8 * 0 = 0 from rfl, Offset.sub_toNat s.sp (by omega) (by omega)]; omega
  have hsa : (s.sp + BitVec.ofNat 64 64).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = stackArg s 8) ?_ (by rfl) (by rfl))
    fun t ⟨a0, k⟩ => ⟨s, h, a0, k⟩
  brun [exec_addSp (show 64 < 2048 by decide), add_ofNat_zero, hst, hsa]
  rfl

/-- The code's list of programs. -/
abbrev crtF (pc : Bool) : List (Prog isa) := Code.flat (crtG pc)

theorem crt_run (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) (h : C0 pc d s) :
    WP isa (Code.seqL (crtF pc)) s fun _ => True := by
  cases pc
  · let ⟨tr, t, e, _⟩ := fn_correct s h.1
    exact ⟨tr, t, exec_flat.mp e, trivial⟩
  · let ⟨tr, t, e, _⟩ := fn_correctP s h.1
    exact ⟨tr, t, exec_flat.mp e, trivial⟩

theorem front_rel : RelCT isa (Two (C0 pc)) (.block (Crt.save ++ argsG pc ++ setupX)) fun _ _ => True := by
  unfold Crt.save
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.block_append (M := isa) (l₁ := ([.addSp .t0 64, .load .d .t0 .t0 0] : List Instr)) ?_
  cases pc
  · exact RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
      (two_taint _ pins_L1 (by taint_decide))
  · exact RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
      (two_taint _ pins_L1 (by taint_decide))

end VG.Proof.Bignum.RISCV64.Crt
