module

public import VerifiedGarbage.Proof.Mont.X86.CallMul
public import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # The trace of a multiplication by a call

Two runs of `callMul` leak the same trace when both are ready for it
(`CallReady` once its offsets are in registers) from the same stack pointer
and the same context: the callee's precondition holds in both, and its public
data, the stack pointer and the arguments, agree (`RelCT.callWith`). -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Spec.Rsa.MontMulAt

theorem mulPub_of {n : Nat} {s t : State} (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i < 4, arg s i = arg t i) :
    (mulContract (ctxLayout n) abi 20).pub s t := by
  have a0 := args 0 (by decide); have a1 := args 1 (by decide)
  have a2 := args 2 (by decide); have a3 := args 3 (by decide)
  sig_pub [mulContract, sig, abi, argSlots, argVal, argBytes]
  sig_and_intros
  all_goals with_reducible assumption

theorem CallReady.edi_eq {n m₁ m₂ size₁ size₂ o a b : Nat} {base : Addr} {s t : State}
    (C₁ : CallReady n m₁ base size₁ o a b s) (C₂ : CallReady n m₂ base size₂ o a b t) :
    s.gpr .edi = t.gpr .edi :=
  BitVec.eq_of_toNat_eq (C₁.ctx.scr.edi_toNat.trans C₂.ctx.scr.edi_toNat.symm)

/-- The call in its frame of arguments. -/
theorem callFrame_relCT {n o a b : Nat} (hn : 2 ≤ n) (sp : BitVec 32) (base : Addr) :
    RelCT isa (fun s t => s.gpr .esp = sp ∧ t.gpr .esp = sp ∧ (∃ m size, CallReady n m base size o a b s) ∧
        ∃ m size, CallReady n m base size o a b t)
      (.frame (.push [.eax, .ecx, .edx, .edi]) (.call (mulAtName n) (mulAtBody n)) (.pop .eax 4))
      (fun _ _ => True) := by
  refine RelCT.callWith (fun u hu => mulAt_correct hn u hu) (mulAt_constantTime n) [below sp 16]
    [⟨base, contextBytes n⟩] ?_
  rintro s t ⟨hs, ht, ⟨m₁, z₁, C₁⟩, ⟨m₂, z₂, C₂⟩⟩
  have hsp : s.gpr .esp = t.gpr .esp := hs.trans ht.symm
  refine ⟨hs ▸ C₁.pre, ht ▸ C₂.pre, hsp, mulPub_of ?_ fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', hsp]
  · show arg (pushed [Reg.eax, .ecx, .edx, .edi] s).callEntry i = arg (pushed [Reg.eax, .ecx, .edx, .edi] t).callEntry i
    refine callEntry_arg_eq (by decide) C₁.fit hsp (fun r hr => ?_) (by simpa using hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [C₁.eax, C₂.eax]
    · rw [C₁.ecx, C₂.ecx]
    · rw [C₁.edx, C₂.edx]
    · exact C₁.edi_eq C₂

/-- The call, its offsets loaded into registers. -/
theorem callMul_relCT {n o a b : Nat} (hn : 2 ≤ n) (sp : BitVec 32) (base : Addr) :
    RelCT isa (fun s t => s.gpr .esp = sp ∧ t.gpr .esp = sp ∧ (∃ m size, MulReady n m base size o a b s) ∧
        ∃ m size, MulReady n m base size o a b t)
      (callMul n (slot n o) (slot n a) (slot n b)) (fun _ _ => True) := by
  unfold callMul
  refine RelCT.seq ?_ (callFrame_relCT (o := o) (a := a) (b := b) hn sp base)
  refine (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun r hr => absurd hr List.not_mem_nil)
    (hc := .block []) (by rfl)).wpDep
    (F := fun (σ u : State) => Keeps [.eax, .ecx, .edx] σ u ∧ u.mem = σ.mem ∧ u.gpr .eax = BitVec.ofNat 32 (slot n b) ∧
        u.gpr .ecx = BitVec.ofNat 32 (slot n a) ∧ u.gpr .edx = BitVec.ofNat 32 (slot n o))
    (fun _ _ _ => ⟨callArgs_ok o a b, callArgs_ok o a b⟩) |>.mono (fun _ _ h => h) ?_
  rintro u w ⟨-, σ₁, σ₂, ⟨h₁, h₂, ⟨m₁, z₁, M₁⟩, ⟨m₂, z₂, M₂⟩⟩, ⟨K₁, e₁, a₁, c₁, d₁⟩, ⟨K₂, e₂, a₂, c₂, d₂⟩⟩
  exact ⟨(K₁.1 _ (by decide)).trans h₁, (K₂.1 _ (by decide)).trans h₂, ⟨m₁, z₁, M₁.args K₁ e₁ a₁ c₁ d₁⟩,
    ⟨m₂, z₂, M₂.args K₂ e₂ a₂ c₂ d₂⟩⟩

theorem Context.edi_eq {n m₁ m₂ size₁ size₂ : Nat} {base : Addr} {s t : State}
    (C₁ : Context n m₁ base size₁ s) (C₂ : Context n m₂ base size₂ t) : s.gpr .edi = t.gpr .edi :=
  BitVec.eq_of_toNat_eq (C₁.scr.edi_toNat.trans C₂.scr.edi_toNat.symm)

/-- Two runs in contexts at the same working space agree on what is public
in the working space's taint. -/
theorem Context.agree {n m₁ m₂ size₁ size₂ : Nat} {base : Addr} {s t : State}
    (C₁ : Context n m₁ base size₁ s) (C₂ : Context n m₂ base size₂ t) :
    VG.X86.Taint.Agree (workspaceTaint false) s t :=
  agree_regs fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact C₁.edi_eq C₂

/-- The call, with what each run gives after it (`G`, which keeps a context). -/
theorem callMul_ws {n o a b : Nat} (hn : 2 ≤ n) (sp : BitVec 32) (base : Addr) {G : State → Prop}
    (hG : ∀ σ m size, σ.gpr .esp = sp → MulReady n m base size o a b σ →
      WP isa (callMul n (slot n o) (slot n a) (slot n b)) σ G)
    (hC : ∀ σ, G σ → ∃ m size, Context n m base size σ) :
    RelCT isa (fun s t => s.gpr .esp = sp ∧ t.gpr .esp = sp ∧ (∃ m size, MulReady n m base size o a b s) ∧
        ∃ m size, MulReady n m base size o a b t)
      (callMul n (slot n o) (slot n a) (slot n b))
      (fun s t => VG.X86.Taint.Agree (workspaceTaint false) s t ∧ G s ∧ G t) :=
  ((callMul_relCT (o := o) (a := a) (b := b) hn sp base).wp
    (fun _ _ ⟨hs, ht, ⟨_, _, M₁⟩, ⟨_, _, M₂⟩⟩ => ⟨hG _ _ _ hs M₁, hG _ _ _ ht M₂⟩)).mono
    (fun _ _ h => h) fun _ _ ⟨_, g₁, g₂⟩ => by
      obtain ⟨_, _, C₁⟩ := hC _ g₁
      obtain ⟨_, _, C₂⟩ := hC _ g₂
      exact ⟨C₁.agree C₂, g₁, g₂⟩

end VG.Proof.Mont.X86.Dynamic
