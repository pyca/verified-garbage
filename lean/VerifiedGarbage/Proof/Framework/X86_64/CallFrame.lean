import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-!
# Calling verified code that has stack frames (x86-64)

`WP.call_mx` calls code that never writes `rsp` (`NoSp`). `WP.callF` calls
code that writes it only in the pushes and pops of its frames (`SpSafe`,
what `Artifact.spSafe` checks): memory then changes only within the regions
the callee may write and the `c.x86_64Depth` bytes of stack below the return
address that its frames and calls use (`Exec.stackFrame`).
-/

namespace VG.X86_64

/-- Calling verified code with frames: as `WP.call_mx`, with the stack the
callee uses below its return address, `c.x86_64Depth` bytes. -/
theorem WP.callF {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : SpSafe c) (hd : c.x86_64Depth + 16 < 2 ^ 64)
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (c.x86_64Depth + 8)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have hf := Exec.stackFrame hsp he (by omega)
  simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_rsp] at hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  let s₂ := s₁.withRegions s.rd s.wr
  have hs₂ : s₂ = s₁.withRegions s.rd s.wr := rfl
  have hsp₂ : s₂.gpr .rsp = s.gpr .rsp - 8 := by
    rw [hs₂, State.withRegions_gpr, habi.1 .rsp (by simp [calleeSaved])]; simp
  have hret : isa.ret s.callEntry s₂ = some (s₂.setReg .rsp (s₂.gpr .rsp + 8)) := by
    simp only [isa, ret]
    refine ite_eq_left ⟨by rw [hsp₂, State.callEntry_rsp], ?_⟩
    have := habi.2.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp] at this
    rw [hsp₂, State.callEntry_rsp]; exact this
  have hrsp : (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr .rsp = s.gpr .rsp := by
    simp only [State.setReg, ite_true, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hkeep : ∀ r, r ≠ .rsp → (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr r = s₂.gpr r :=
    fun r h => by simp [State.setReg, h]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl (fun r hr' => ?_) ?_
    ⟨s₁, rfl, fun r h => (hkeep r h).symm, hpost⟩ habi.2.2⟩
  · by_cases h : r = .rsp
    · subst h; exact hrsp
    · rw [hkeep r h, hs₂, State.withRegions_gpr, habi.1 r hr', State.withRegions_gpr,
        State.callEntry_gpr _ h]
  · -- The return address, then the callee.
    have f₀ : Frame (wr ++ [below (s.gpr .rsp) (c.x86_64Depth + 8)]) s.mem s.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega) (by omega))
    have f₁ : Frame (wr ++ [below (s.gpr .rsp) (c.x86_64Depth + 8)]) s.callEntry.mem s₁.mem :=
      Frame.sub hf fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_callee _ _⟩
    exact Frame.trans f₀ f₁

/-- Code without calls or frames uses no stack below `rsp`. -/
theorem x86_64Depth_zero : ∀ {c : Prog isa}, NoSp c → c.depth = 0 → c.x86_64Depth = 0
  | .block _, _, _ => rfl
  | .seq a b, h, hd => by
    simp only [Code.depth, Nat.max_eq_zero_iff] at hd
    simp only [Code.x86_64Depth, x86_64Depth_zero (fun i hi => h i (List.mem_append_left _ hi)) hd.1,
      x86_64Depth_zero (fun i hi => h i (List.mem_append_right _ hi)) hd.2, Nat.max_self]
  | .ite _ a b, h, hd => by
    simp only [Code.depth, Nat.max_eq_zero_iff] at hd
    simp only [Code.x86_64Depth, x86_64Depth_zero (fun i hi => h i (List.mem_append_left _ hi)) hd.1,
      x86_64Depth_zero (fun i hi => h i (List.mem_append_right _ hi)) hd.2, Nat.max_self]
  | .loop b _, h, hd => x86_64Depth_zero (c := b) h hd
  | .call _ _, _, hd => by simp [Code.depth] at hd
  | .frame i b _, h, hd => by
    have hi := h i (List.mem_cons_self ..)
    have hb : b.x86_64Depth = 0 :=
      x86_64Depth_zero (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_left _ hj))) hd
    simp only [Code.x86_64Depth, hb, Nat.zero_add]
    cases i <;> simp_all [X86_64.Instr.frameBytes, Taint.clobbers]

/-- Code without frames uses the return addresses of its calls: 8 bytes for
each level. -/
theorem x86_64Depth_noSp : ∀ {c : Prog isa}, NoSp c → c.x86_64Depth = 8 * c.depth
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.x86_64Depth, Code.depth, x86_64Depth_noSp (fun i hi => h i (List.mem_append_left _ hi)),
      x86_64Depth_noSp (fun i hi => h i (List.mem_append_right _ hi)), Nat.mul_max_mul_left]
  | .ite _ a b, h => by
    simp only [Code.x86_64Depth, Code.depth, x86_64Depth_noSp (fun i hi => h i (List.mem_append_left _ hi)),
      x86_64Depth_noSp (fun i hi => h i (List.mem_append_right _ hi)), Nat.mul_max_mul_left]
  | .loop b _, h => x86_64Depth_noSp (c := b) h
  | .call _ b, h => by
    simp only [Code.x86_64Depth, Code.depth, x86_64Depth_noSp (c := b) h, Nat.mul_add, Nat.mul_one]
  | .frame i b _, h => by
    have hi := h i (List.mem_cons_self ..)
    have hb : b.x86_64Depth = 8 * b.depth :=
      x86_64Depth_noSp (fun j hj => h j (List.mem_cons_of_mem _ (List.mem_append_left _ hj)))
    simp only [Code.x86_64Depth, Code.depth, hb]
    cases i <;> simp_all [X86_64.Instr.frameBytes, Taint.clobbers]

/-- What `Exec.stackFrame` adds to a weakest precondition: memory changes
only within the writable regions and the stack below `rsp` the code uses. -/
theorem WP.stackFrame {c : Prog isa} (hc : SpSafe c) (hd : c.x86_64Depth < 2 ^ 64) {s : State}
    {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ Frame (s.wr ++ [below (s.gpr .rsp) c.x86_64Depth]) s.mem s'.mem := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.stackFrame hc he hd⟩

end VG.X86_64
