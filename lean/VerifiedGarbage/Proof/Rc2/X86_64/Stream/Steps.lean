module

public import VerifiedGarbage.Impl.Rc2.X86_64.Stream
import VerifiedGarbage.Proof.Rc2.Stream
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Rc2.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime
public import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.X86_64.Lit

@[expose] public section

section

/-! # Streaming RC2-CBC on x86-64: the function-level contracts -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64

/-- `vg_rc2_cbc_init(key = rdi, key_len = rsi, effective_bits = rdx, iv = rcx,
iv_len = r8, ctx = r9, scratch = [rsp + 8])`, which calls key expansion. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let iv : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let ctx : Region := ⟨s.gpr .r9, 144⟩
    let buf : Region := ⟨stackArg s 0, 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [key, iv, args] ∧ s.wr = [ctx, buf] ∧
      key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
      ctx.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint key ∧ ret.Disjoint iv ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧ ret.Disjoint args ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 144 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) direction (s.gpr .rdx).toNat with
      | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .r9) direction 0 = c
      | .error e => ((s'.gpr .rax).setWidth 32).toNat = e.code
  pub s₁ s₂ := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ∧ stackArg s₁ 0 = stackArg s₂ 0

def initSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rcx => 0x2000 | .r9 => 0x3000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6008, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem publicRegs_seven (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem args_getD (s : State) : (s.gpr .rdi :: s.gpr .rsi :: s.gpr .rdx :: s.gpr .rcx :: s.gpr .r8 :: s.gpr .r9 ::
    List.map (stackArg s) (List.range 1)).getD 6 0 = stackArg s 0 := rfl

theorem init_implies : initContract.Implies (Proof.Rc2.cbcInitScratchContract abi 8) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_pre [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
  post := by sig_implies_post [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨(publicRegs_seven _ _).2 ⟨h2, h3, h4, h5, h6, h7, h1⟩, h⟩
  sat := by sig_implies_sat [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] [initSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using initSatState

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: `test` -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem toNat_eq (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem test_ok (s : State) (r : Reg) {n : Nat} (hn : s.gpr r = BitVec.ofNat 64 n) (hn' : n < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (decide (n = 0)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ⟨fun r _ => by rw [gpr_arithFlags], rfl, rfl, rfl⟩⟩
  rw [zf_arithFlags, hn, BitVec.and_self, beq_zero hn']

end VG.Proof.Rc2.X86_64.Stream
