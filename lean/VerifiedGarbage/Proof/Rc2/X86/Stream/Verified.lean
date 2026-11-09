module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Rc2.X86.Stream.InitCorrect
meta import VerifiedGarbage.Proof.Rc2.X86.Stream.InitCorrect
import VerifiedGarbage.Proof.Rc2.X86.Key
meta import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
public import VerifiedGarbage.Proof.Rc2.Scratch
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Stream
meta import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Loop
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.Rc2.Select
meta import VerifiedGarbage.Proof.Rc2.Select32
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.Rc2.Word32
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Loop
meta import VerifiedGarbage.Proof.Rc2.X86.KeyIO
meta import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
meta import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the public arguments on the stack

The taint analysis starts from the public arguments on the stack (`τ0`).
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- The arguments on the stack are public, and only read. -/
def τ0 : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 32 }

theorem τ0_wf {s : State} (f : (s.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d : ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r) :
    VG.X86.Taint.Wf τ0 s :=
  Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨f, fun r hr => Taint.frame_disjoint (n := 28) (by omega_arith) (d r hr).1 (d r hr).2⟩,
    fun _ h => (List.not_mem_nil h).elim⟩

theorem τ0_agree {s₁ s₂ : State} (f₁ : (s₁.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨(s₁.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₁ 0, 28⟩ r)
    (d₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨(s₂.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₂ 0, 28⟩ r)
    (sp : s₁.gpr .esp = s₂.gpr .esp) (args : ∀ i < 7, arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree τ0 s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τ0_wf f₁ d₁, τ0_wf f₂ d₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp,
    fun k h4 hk => ?_⟩
  · simp only [τ0, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [τ0] at hk
    rw [show Taint.depth τ0.stk = 0 from rfl, Nat.zero_add, Taint.argByte_eq f₁ h4 hk,
      Taint.argByte_eq f₂ h4 hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_arith))

end VG.Proof.Rc2.X86.Stream

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the shared contracts

The shared contract (`Proof.Rc2.cbcInitScratchContract`) lets the code
write its arguments; `wideInit` is the per-target contract with that
permission, which implies the shared one. `narrow*` drop it again, for the
proofs against `initContract`.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- `initContract`, with the arguments writable. -/
def wideInit : Contract isa :=
  { initContract with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
      let iv : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let ctx : Region := ⟨(arg s 5).setWidth 64, 144⟩
      let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 28⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 24
      s.rd = [key, iv] ∧ s.wr = [ctx, buf, args] ∧
        key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
        args.Disjoint ctx ∧ args.Disjoint buf ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧
        stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧
        (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
        (arg s 5).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
        24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 }

/-- `init(0x1000, 1, 8, 0x2000, 8, 0x3000, 0x4000)`. -/
def initSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 1 else if a = 0x600c then 8 else
    if a = 0x6011 then 0x20 else if a = 0x6014 then 8 else if a = 0x6019 then 0x30 else
    if a = 0x601d then 0x40 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩, ⟨0x6004, 28⟩]

tactic_template "wide_pre " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
    intro s h
    sig_pre [$ls,*] at h
    sig_split h
    sig_reduce [$ls,*]
    sig_simp [$ls,*] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [Taint.sub_setWidth (by omega_arith)]
         first
           | with_reducible assumption
           | with_reducible exact Region.Disjoint.symm ‹_›)))

theorem init_implies : wideInit.Implies (Proof.Rc2.cbcInitScratchContract abi 24) where
  pre := by
    wide_pre [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  post := by
    sig_implies_post [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  pub := by
    sig_implies_pub [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  sat := by
    sig_implies_sat [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below] [initSat, arg, argAddr, Mem.readW, Mem.read] using initSat

end VG.Proof.Rc2.X86.Stream

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` is constant time

The taint analysis proves the checks and
the copy of the IV, `RelCT.callWith` the call of the key expansion, and the
restore of our caller's registers through `ebx`, public again by correctness.
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

def Rel (s₁ s₂ : State) : Prop := initContract.pre s₁ ∧ initContract.pre s₂ ∧ initContract.pub s₁ s₂

theorem Pre.disj {s₀ s : State} (hp : Pre s₀) (hc : Common s₀ s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r := by
  have e : argAddr s 0 = argAddr s₀ 0 := by unfold argAddr; rw [hc.esp]
  rw [hc.wr, hp.wr, hc.esp, e]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  exacts [⟨hp.r_c, hp.a_c⟩, ⟨hp.r_s, hp.a_s⟩]

/-- The arguments, from a state whose memory is the entry state's. -/
theorem arg_eq {s₀ s : State} (hc : Common s₀ s) (hm : s.mem = s₀.mem) (i : Nat) : arg s i = arg s₀ i := by
  unfold arg argAddr; rw [hc.esp, hm]

theorem agree_mid {σ₁ σ₂ s₁ s₂ : State} (h : Rel σ₁ σ₂) (c₁ : Common σ₁ s₁) (c₂ : Common σ₂ s₂)
    (m₁ : s₁.mem = σ₁.mem) (m₂ : s₂.mem = σ₂.mem) : VG.X86.Taint.Agree τ0 s₁ s₂ := by
  have hp₁ := pre_of h.1
  have hp₂ := pre_of h.2.1
  refine τ0_agree (by rw [c₁.esp]; exact hp₁.sp_fit) (by rw [c₂.esp]; exact hp₂.sp_fit) (hp₁.disj c₁)
    (hp₂.disj c₂) (by rw [c₁.esp, c₂.esp]; exact h.2.2.1) fun i hi => ?_
  rw [arg_eq c₁ m₁, arg_eq c₂ m₂]; exact h.2.2.2 i hi

theorem code_eq {σ₁ σ₂ : State} (args : ∀ i < 7, arg σ₁ i = arg σ₂ i) : code σ₁ = code σ₂ := by
  simp only [code, kl, eb, il, args 1 (by decide), args 2 (by decide), args 4 (by decide)]

/-- After the checks and the test of their result. -/
structure Checked (s₀ s : State) : Prop where
  common : Common s₀ s
  mem : s.mem = s₀.mem
  zf : s.zf = some (decide (code s₀ = 0))
  ebx : s.gpr .ebx = s₀.gpr .ebx
  esi : s.gpr .esi = s₀.gpr .esi

theorem checked_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.seq checks (.block [.alu .test .eax (.reg .eax)])) s₀ (Checked s₀) := by
  refine WP.seq (checks_ok hp fun s c m a b e => wp_test fun s₁ f₁ hz => WP.block_nil ?_)
  refine ⟨c.fupd f₁, by rw [f₁.mem, m], ?_, by rw [f₁.gpr]; exact b, by rw [f₁.gpr]; exact e⟩
  rw [hz, a, BitVec.and_self, ofNat_beq_zero (by have := code_lt s₀; omega_arith)]

/-- Before the call. -/
structure Args (s₀ s : State) : Prop where
  common : Common s₀ s
  eax : s.gpr .eax = key s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = arg s₀ 2
  esi : s.gpr .esi = ctx s₀
  ebx : s.gpr .ebx = scr s₀

def CheckedRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, Rel σ₁ σ₂ ∧ Checked σ₁ s₁ ∧ Checked σ₂ s₂

def ArgsRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, Rel σ₁ σ₂ ∧ code σ₁ = 0 ∧ Args σ₁ s₁ ∧ Args σ₂ s₂

theorem args_ct :
    RelCT isa (fun s₁ s₂ => CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs) ArgsRel := by
  have ct : RelCT isa (fun s₁ s₂ => CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs)
      (fun _ _ => True) := by
    refine RelCT.taint (A := taint) τ0 (fun s₁ s₂ h => ?_) (by taint_decide)
    obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, -⟩ := h
    exact agree_mid hσ k₁.common k₂.common k₁.mem k₂.mem
  have code0 : ∀ {σ s : State}, Checked σ s → isa.eval .ne s = some false → code σ = 0 := fun k z => by
    have : isa.eval .ne _ = _ := congrArg (Option.map (!·)) k.zf
    rw [z] at this
    exact of_decide_eq_true (by revert this; cases decide (code _ = 0) <;> simp)
  have h : ∀ σ : State × State, RelCT isa (fun s₁ s₂ =>
      (CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) ∧ Rel σ.1 σ.2 ∧ Checked σ.1 s₁ ∧ Checked σ.2 s₂ ∧
        code σ.1 = 0) (.block initArgs) ArgsRel := fun σ => by
    refine ((ct.mono (fun _ _ h => h.1) (fun _ _ h => h)).wp
      (F₁ := fun (s : State) => Rel σ.1 σ.2 ∧ code σ.1 = 0 ∧ Args σ.1 s) (F₂ := Args σ.2) fun s₁ s₂ h => ?_).mono
      (fun _ _ h => h) fun _ _ h => ⟨σ.1, σ.2, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2⟩
    obtain ⟨-, hσ, k₁, k₂, h0⟩ := h
    have hp₁ := pre_of hσ.1
    have hp₂ := pre_of hσ.2.1
    have h0' : code σ.2 = 0 := (code_eq hσ.2.2.2).symm.trans h0
    exact ⟨initArgs_ok hp₁ (code_ok h0).2.2 k₁.common k₁.mem k₁.ebx k₁.esi
        fun t c ea ec ed es eb _ _ _ => ⟨hσ, h0, c, ea, ec, ed, es, eb⟩,
      initArgs_ok hp₂ (code_ok h0').2.2 k₂.common k₂.mem k₂.ebx k₂.esi
        fun t c ea ec ed es eb _ _ _ => ⟨c, ea, ec, ed, es, eb⟩⟩
  refine (RelCT.exists_ h).mono (fun s₁ s₂ hh => ?_) (fun _ _ h => h)
  obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩ := hh
  exact ⟨(σ₁, σ₂), ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩, hσ, k₁, k₂, code0 k₁ z⟩

theorem call_ct : RelCT isa ArgsRel keyCall (fun s₁ s₂ => s₁.gpr .ebx = s₂.gpr .ebx) := by
  rintro s₁ s₂ t₁ t₂ u₁ u₂ ⟨σ₁, σ₂, ⟨h₁, h₂, sp, args⟩, h0, a₁, a₂⟩ e₁ e₂
  have hp₁ := pre_of h₁
  have hp₂ := pre_of h₂
  have h0' : code σ₂ = 0 := (code_eq args).symm.trans h0
  obtain ⟨hk₁, he₁, -⟩ := code_ok h0
  obtain ⟨hk₂, he₂, -⟩ := code_ok h0'
  have pre₁ := keyCallPre_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
  have pre₂ := keyCallPre_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
  have fit (s : State) (σ : State) (hp : Pre σ) (c : Common σ s) : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [c.esp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega_arith
  have hrs : Reg.esp ∉ rs5 := by decide
  have esp : s₁.gpr .esp = s₂.gpr .esp := by rw [a₁.common.esp, a₂.common.esp]; exact sp
  have rd : callRd σ₂ s₂ = callRd σ₁ s₁ := by
    simp only [callRd, callEntry_argAddr0, esp, keyR, kA, kl, key, args 0 (by decide), args 1 (by decide)]
  have wr : callWr σ₂ = callWr σ₁ := by
    simp only [callWr, schR, cA, sA, ctx, scr, args 5 (by decide), args 6 (by decide)]
  have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) keyCall (fun _ _ => True) := by
    apply RelCT.callWith key_body_correct expandKey_constantTime (callRd σ₁ s₁) (callWr σ₁)
    intro a b hab
    rw [hab.1, hab.2]
    refine ⟨pre₁, by rw [← rd, ← wr]; exact pre₂, esp, ?_, ?_⟩
    · simp only [State.withRegions_gpr, callEntry_esp', esp]
    · intro i hi
      simp only [arg_withRegions]
      rw [callEntry_arg (fit _ _ hp₁ a₁.common) hrs (by simpa using hi),
        callEntry_arg (fit _ _ hp₂ a₂.common) hrs (by simpa using hi)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_arith) with rfl | rfl | rfl | rfl | rfl
      · show s₁.gpr .eax = s₂.gpr .eax; rw [a₁.eax, a₂.eax, key, key, args 0 (by decide)]
      · show s₁.gpr .ecx = s₂.gpr .ecx; rw [a₁.ecx, a₂.ecx, args 1 (by decide)]
      · show s₁.gpr .edx = s₂.gpr .edx; rw [a₁.edx, a₂.edx, args 2 (by decide)]
      · show s₁.gpr .esi = s₂.gpr .esi; rw [a₁.esi, a₂.esi, ctx, ctx, args 5 (by decide)]
      · show s₁.gpr .ebx = s₂.gpr .ebx; rw [a₁.ebx, a₂.ebx, scr, scr, args 6 (by decide)]
  obtain ⟨ht, -, b₁, b₂⟩ := (ct.wp (F₁ := fun (s : State) => s.gpr .ebx = scr σ₁) (F₂ := fun (s : State) => s.gpr .ebx = scr σ₂)
    fun a b ⟨ha, hb⟩ => by
      subst ha hb
      exact ⟨keyCall_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₁.ebx,
        keyCall_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₂.ebx⟩) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, show u₁.gpr .ebx = u₂.gpr .ebx by rw [b₁, b₂, scr, scr, args 6 (by decide)]⟩

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold init
  apply RelCT.assoc
  have hA : RelCT isa Rel (.seq checks (.block [.alu .test .eax (.reg .eax)])) (fun _ _ => True) :=
    RelCT.taint (A := taint) τ0 (fun s₁ s₂ h => agree_mid h (Common.refl _) (Common.refl _) rfl rfl)
      (by taint_decide)
  refine ((hA.wpDep (F := Checked) fun s₁ s₂ (h : Rel s₁ s₂) =>
    ⟨checked_ok (pre_of h.1), checked_ok (pre_of h.2.1)⟩).mono (fun _ _ h => h)
      (Q' := CheckedRel) fun _ _ h => h.2).seq ?_
  apply RelCT.ite
  · rintro s₁ s₂ ⟨σ₁, σ₂, ⟨-, -, -, args⟩, k₁, k₂⟩
    show s₁.zf.map (!·) = s₂.zf.map (!·)
    rw [k₁.zf, k₂.zf, code_eq args]
  · exact RelCT.nil fun _ _ _ => trivial
  · unfold initBody
    refine args_ct.seq (call_ct.seq ?_)
    exact RelCT.taint (A := taint) (τr [.ebx])
      (fun _ _ h => agree_regs (fun r hr => by rw [List.mem_singleton.mp hr]; exact h)) (by taint_decide)

end VG.Proof.Rc2.X86.Stream.Init

end

/-!
# Streaming RC2-CBC on x86 (32-bit): `Verified`

`init` meets `initContract`, with its arguments only read; the shared
contract lets the code write them too (`wideInit`), which
`Verified.narrowTo` allows, and `init_implies` takes the proof to the shared
contract.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-! ## `init` -/

def initRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 28⟩]
def initWr (s : State) : List Region := [⟨(arg s 5).setWidth 64, 144⟩, ⟨(arg s 6).setWidth 64, 576⟩]

tactic_template "rc2_stream_narrow" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [VG.Proof.Rc2.X86.Stream.initContract, VG.Proof.Rc2.X86.Stream.wideInit,
                     VG.Proof.Rc2.X86.Stream.initRd, VG.Proof.Rc2.X86.Stream.initWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)
tactic_template "rc2_stream_narrow" : tactic => `(tactic| rc2_stream_narrow at ⊢)

theorem wideInit_pre (s : State) (h : wideInit.pre s) : initContract.pre (s.withRegions (initRd s) (initWr s)) := by
  obtain ⟨_, _, h⟩ := h
  rc2_stream_narrow
  exact ⟨trivial, trivial, h⟩

theorem init_verified : Verified target Impl.Rc2.X86.Stream.init (Proof.Rc2.cbcInitScratchContract abi 24) := by
  have hsat := init_implies.sat_left
  have narrowSat : ∃ s, initContract.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideInit_pre s hs⟩
  apply Verified.of_implies _ init_implies
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => Init.init_correct s hs) Init.init_constantTime (.refl narrowSat))
    initRd initWr wideInit_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    rc2_stream_narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    rc2_stream_narrow
    exact h

end VG.Proof.Rc2.X86.Stream
