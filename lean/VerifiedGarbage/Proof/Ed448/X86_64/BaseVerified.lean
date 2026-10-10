import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# Ed448 base-point multiplication on x86-64: `Verified`

Correctness including the ABI of the code with `vg_gf448_r64_pow223`'s
inlined, given that the reference ladder encodes `[k]B` (`BaseLadderOk`,
which the registration files pass in), constant time (by taint tracking,
which follows the call: the only branches are on the loop counters, and every
address is an argument plus a constant or a counter), and a concrete state
satisfying the signature's contract, with 8 bytes of stack for the call's
return address (`Verified.of_inline_ct`). Callers get the code's correctness
for states that keep their buffers off those 8 bytes (`scalarBase_ok`,
`scalarBaseLocal.clear`).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def scalarBaseSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `rdx`): the output's address, at `OUT`. -/
def scalarBaseτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rsp], flags := false, lens := [0, 8192], bases := [(.rdx, 1, 0)] }

theorem scalarBase_agree {s₁ s₂ : State} (h₁ : scalarBaseLocal.pre s₁)
    (h₂ : scalarBaseLocal.pre s₂) (hpub : scalarBaseLocal.pub s₁ s₂) :
    X86_64.Taint.Agree scalarBaseτ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  have wf : ∀ s, scalarBaseLocal.pre s → X86_64.Taint.Wf scalarBaseτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, scalarBaseτ], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [scalarBaseτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [scalarBaseτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3]
  · exact VG.X86_64.Taint.slotsOk_empty
  · exact VG.X86_64.Taint.slotsAgree_empty

theorem scalarBase_inlineOk : scalarBase.InlineOk = true := by lit_decide

theorem scalarBase_okI (hL : Proof.Ed448.BaseLadderOk) (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase.inline s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_inline hL hs
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he h.1, h.2⟩

/-- The output is apart from the call's return address. -/
theorem scalarBase_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : scalarBaseLocal.pre s)
    (hcl : Clear (hole (s.gpr .rsp)) s) (hp : scalarBaseLocal.post s b) :
    scalarBaseLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hw, -⟩ := hs
  have hb := Clear.wr_bytes hcl (p := s.gpr .rdi) (n := 57) (by rw [hw]; simp) (by decide)
  show Spec.Ed448.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 57 = _
  rw [show Spec.Ed448.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 57 = Spec.Ed448.bytesAt b.mem (s.gpr .rdi) 57
    from bytes_patch hb]
  exact hp

/-- The code's correctness, for callers. -/
theorem scalarBase_ok (hL : Proof.Ed448.BaseLadderOk) :
    ∀ s, scalarBaseLocal.clear.pre s →
      ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  ok_of_inline scalarBase_inlineOk (scalarBase_okI hL) scalarBase_patch

theorem scalarBase_ct0 : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine VG.Taint.constantTime (A := taint) scalarBaseτ
    (fun _ _ h₁ h₂ hp => scalarBase_agree h₁ h₂ hp) (by taint_decide)

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub scalarBase :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => scalarBase_ct0 s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

theorem scalarBase_implies : scalarBaseLocal.Implies (Spec.Ed448.scalarBaseContract X86_64.abi) := by
  sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
    Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, scalarBaseLocal]
    [scalarBaseSat] using scalarBaseSat

/-- The contract with 8 bytes of stack, for the call's return address. -/
theorem scalarBase_implies8 : scalarBaseLocal.Implies (Spec.Ed448.scalarBaseContract X86_64.abi 8) :=
  scalarBase_implies.stack8_abi (by
    sig_implies_sat [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, scalarBaseSat] [scalarBaseSat] using scalarBaseSat)

theorem scalarBase_verified (hL : Proof.Ed448.BaseLadderOk) : Verified X86_64.target scalarBase
    (Spec.Ed448.scalarBaseContract X86_64.abi 8) :=
  Verified.of_inline_ct scalarBase_inlineOk (scalarBase_okI hL) scalarBase_ct0 scalarBase_implies8
    (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => scalarBase_patch s b hv u (scalarBase_implies8.pre s hs) (Sig.clear_of_pre hs) hp)

end VG.Proof.Ed448.X86_64
