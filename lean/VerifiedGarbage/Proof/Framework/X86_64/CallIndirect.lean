module

public import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Indirect calls (x86-64)

An indirect call (`Code.icall`) stores its return address at `rsp - 8`, as a
call does (`State.callEntry`), and runs the function at the address in `r11`
(`fnAt`), which keeps what the calling convention keeps and changes memory
only within its writable regions and the stack below its return address
(`callOk`). What that function does is known only from what a contract says
of it (`FnMeets`): `WP.icall` runs an indirect call from the function's
result on the state of the call, with its permissions narrowed to `rd` and
`wr`, as `WP.call` does from a callee's `Verified` proof.
-/

@[expose] public section

namespace VG.X86_64

/-- Calling the function at the address in `r11` indirectly: if the function
`f` there, from the state the call enters it in (`State.callEntry`) with its
permissions narrowed to `rd` and `wr`, returns in a state `s₂` it allows
(`callOk`) satisfying `P`, the call returns in a state that has the
permissions of `s`, its callee-saved registers and `rsp`; that differs from
`s` in memory only within `wr` and the `n + 8` bytes below `rsp`; and whose
memory and registers (`rsp` aside) are those of such an `s₂`. -/
theorem WP.icall {n : Nat} {s : State} {f : State → Option (State × List Leak)}
    (hf : fnAt s (s.gpr .r11) = some f) {rd wr : List Region} {P : State → State → Prop}
    (hK : ∃ s₂ t, f (s.callEntry.withRegions rd wr) = some (s₂, t) ∧
      callOk n (s.callEntry.withRegions rd wr) s₂ ∧ P (s.callEntry.withRegions rd wr) s₂)
    (hw : Covers wr s.wr) (hn : n + 8 < 2 ^ 64) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (n + 8)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        P (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.icall n) s Q := by
  obtain ⟨s₂, t, hr, hk, hp⟩ := hK
  obtain ⟨-, w₂, hr'⟩ := regionModel.fn_widen hf hr
  -- The function's run from the state of the call.
  have hrun : f s.callEntry = some (s₂.withRegions s.rd s.wr, t) := by
    have := hr' s.rd s.wr
    rwa [show regionModel.withRegions (s.callEntry.withRegions rd wr) s.rd s.wr = s.callEntry from
      rfl] at this
  have hk' : callOk n ((s.callEntry.withRegions rd wr).withRegions s.rd s.wr)
      (s₂.withRegions s.rd s.wr) :=
    regionModel.callOk_widen (r := s.rd) (w := s.wr) hk hw
  rw [State.withRegions_withRegions,
    show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at hk'
  let s₃ := s₂.withRegions s.rd s.wr
  have hsp₃ : s₃.gpr .rsp = s.gpr .rsp - 8 := by
    rw [show s₃.gpr .rsp = s₂.gpr .rsp from rfl, hk.1.1 .rsp (by simp [calleeSaved])]; simp
  have hret : isa.ret s.callEntry s₃ = some (s₃.setReg .rsp (s₃.gpr .rsp + 8)) := by
    simp only [isa, ret]
    refine ite_eq_left ⟨by rw [hsp₃, State.callEntry_rsp], ?_⟩
    have := hk'.1.2.1
    rw [hsp₃, State.callEntry_rsp]; exact this
  have hrsp : (s₃.setReg .rsp (s₃.gpr .rsp + 8)).gpr .rsp = s.gpr .rsp := by
    simp only [State.setReg, ite_true, hsp₃]; exact BitVec.sub_add_cancel _ _
  have hkeep : ∀ r, r ≠ .rsp → (s₃.setReg .rsp (s₃.gpr .rsp + 8)).gpr r = s₃.gpr r :=
    fun r h => by simp [State.setReg, h]
  refine ⟨_, _, .icall (by rw [show isa.icallTarget s = s.gpr .r11 from rfl]; exact hf)
    (call_callEntry s) hrun hk' hret, hQ _ rfl rfl (fun r hr => ?_) ?_
    ⟨s₂, rfl, fun r h => (hkeep r h).symm, hp⟩⟩
  · by_cases h : r = .rsp
    · subst h; exact hrsp
    · rw [hkeep r h, show s₃.gpr r = s₂.gpr r from rfl, hk.1.1 r hr, State.withRegions_gpr,
        State.callEntry_gpr _ h]
  · -- The return address, then what the function may write.
    have f₀ : Frame (wr ++ [below (s.gpr .rsp) (n + 8)]) s.mem s.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega) (by omega))
    have f₁ : Frame (wr ++ [below (s.gpr .rsp) (n + 8)]) s.callEntry.mem s₂.mem := by
      intro x hx
      refine hk.2 x (fun r hr => hx r (List.mem_append_left _ (by simpa using hr))) fun hc => ?_
      apply hx _ (List.mem_append_right _ (List.mem_singleton_self _))
      simp only [State.withRegions_gpr, State.callEntry_rsp] at hc
      exact below_callee _ _ _ hc
    exact Frame.trans f₀ f₁

end VG.X86_64
