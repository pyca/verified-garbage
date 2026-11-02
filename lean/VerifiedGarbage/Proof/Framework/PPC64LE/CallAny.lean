module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-!
# Calls of code with any frames (PPC64LE)

Untrusted: everything here is checked by Lean.

`WP.callF` calls code whose frames all save a register (`push`, 48 bytes).
Code may also allocate a buffer on the stack (`alloc bytes`, as
`withStackScratch` does): `sdepth` is the number of bytes of stack below the
stack pointer that code and its callees use, counting each frame's bytes,
and `Exec.frameAny` bounds what it changes in memory by the regions it may
write and those bytes. `WP.callAny` calls verified code with any frames, and `WP.frameRegAny` runs
such code in a frame saving a register.
-/

@[expose] public section

namespace VG.PPC64LE

/-- The bytes a frame's push moves the stack pointer down by. -/
def Instr.frameBytes : Instr → Nat
  | .push _ => 48
  | .alloc n => n
  | _ => 0

/-- The bytes of stack below the stack pointer that the code and its callees
use. -/
def sdepth : Prog isa → Nat
  | .block _ => 0
  | .seq a b => max (sdepth a) (sdepth b)
  | .ite _ t e => max (sdepth t) (sdepth e)
  | .loop b _ => sdepth b
  | .call _ b => sdepth b
  | .frame i b _ => i.frameBytes + sdepth b
  | .icall _ _ b n => max (sdepth b) (sdepth n)

/-- Code whose frames all save a register uses `48` bytes of stack per frame. -/
theorem sdepth_le_fdepth : ∀ c : Prog isa, pushFrames c = true → sdepth c ≤ 48 * c.fdepth
  | .block _, _ => Nat.zero_le _
  | .seq a b, h => by
    simp only [pushFrames, Bool.and_eq_true] at h
    have := sdepth_le_fdepth a h.1; have := sdepth_le_fdepth b h.2
    simp only [sdepth, Code.fdepth]; omega
  | .ite _ t e, h => by
    simp only [pushFrames, Bool.and_eq_true] at h
    have := sdepth_le_fdepth t h.1; have := sdepth_le_fdepth e h.2
    simp only [sdepth, Code.fdepth]; omega
  | .loop b _, h => by simp only [pushFrames] at h; simpa [sdepth, Code.fdepth] using sdepth_le_fdepth b h
  | .call _ b, h => by simp only [pushFrames] at h; simpa [sdepth, Code.fdepth] using sdepth_le_fdepth b h
  | .frame i b _, h => by
    simp only [pushFrames, Bool.and_eq_true] at h
    have := sdepth_le_fdepth b h.2
    cases i <;> simp only [Instr.isPush, Bool.false_eq_true, false_and] at h
    simp only [sdepth, Instr.frameBytes, Code.fdepth]; omega
  | .icall _ _ b n, h => by
    simp only [pushFrames, Bool.and_eq_true] at h
    have := sdepth_le_fdepth b h.1; have := sdepth_le_fdepth n h.2
    simp only [sdepth, Code.fdepth]; omega

/-- The stack a frame's body uses is below the frame. -/
theorem below_body' (sp : Addr) (a n : Nat) :
    Region.Sub (below (sp - BitVec.ofNat 64 a) n) (below sp (n + a)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 (n + a)) = x - (sp - BitVec.ofNat 64 a - BitVec.ofNat 64 n) by
    rw [BitVec.ofNat_add]; bv_omega]
  omega

/-- What a frame's push changes: the stack pointer moves down by the frame's
bytes, memory changes only in them, and its region, in them, is added at the
head of `wr`. -/
theorem push_any {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    s₁.sp = s.sp - BitVec.ofNat 64 i.frameBytes ∧ 32 < i.frameBytes ∧
      Frame [below s.sp i.frameBytes] s.mem s₁.mem ∧
      ∃ r, s₁.wr = r :: s.wr ∧ Region.Sub r (below s.sp i.frameBytes) := by
  cases i with
  | push r =>
    simp only [isa, push] at h
    split at h <;> cases h
    rename_i hsp
    simp only [Instr.frameBytes]
    have c : ∀ off, off + 8 ≤ 48 →
        (below s.sp 48).Contains (s.sp - 48 + BitVec.ofNat 64 off) 8 := fun off ho => by
      simp only [Region.Contains]
      rw [show s.sp - 48 + BitVec.ofNat 64 off - (s.sp - BitVec.ofNat 64 48) = BitVec.ofNat 64 off by
        bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    refine ⟨rfl, by decide, ?_, _, rfl, fun x hx => ?_⟩
    · refine Frame.write (Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ ?_)
        (List.mem_singleton_self _) _ (c 32 (by omega))
      simpa using c 0 (by omega)
    · simp only [Region.Contains] at hx ⊢
      rw [show x - (s.sp - BitVec.ofNat 64 48) = (x - (s.sp - 48 + 32)) + BitVec.ofNat 64 32 by
        bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 32) (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  | alloc n =>
    simp only [isa, push] at h
    split at h <;> cases h
    rename_i hc
    obtain ⟨h1, h2, -, h4⟩ := hc
    simp only [Instr.frameBytes]
    refine ⟨trivial, h1, ?_, _, rfl, fun x hx => ?_⟩
    · refine Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
      simp only [Region.Contains]
      rw [BitVec.sub_self, BitVec.toNat_zero]
      omega
    · simp only [Region.Contains] at hx ⊢
      rw [show x - (s.sp - BitVec.ofNat 64 n) = (x - (s.sp - BitVec.ofNat 64 n + 32)) +
          BitVec.ofNat 64 32 by bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := 32) (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  | _ => simp [isa, push] at h

/-- Code changes memory only within the regions it may write and within the
`sdepth c` bytes below the stack pointer (its frames). -/
theorem Exec.frameAny {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hd : sdepth c < 2 ^ 64) : Frame (s.wr ++ [below s.sp (sdepth c)]) s.mem s'.mem := by
  induction h with
  | icall hi => nomatch hi
  | icallNext hi => nomatch hi
  | block h => exact Frame.mono (execBlock_regions h).2.2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    simp only [sdepth] at hd ⊢
    have f₁ := Frame.below_mono (ih₁ (by omega)) (b := max (sdepth c₁) (sdepth c₂)) (by omega)
      (by omega)
    have f₂ := Frame.below_mono (ih₂ (by omega)) (b := max (sdepth c₁) (sdepth c₂)) (by omega)
      (by omega)
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    rw [w₁, p₁] at f₂
    exact Frame.trans f₁ f₂
  | iteT _ _ ih =>
    simp only [sdepth] at hd ⊢
    exact Frame.below_mono (ih (by omega)) (by omega) (by omega)
  | iteF _ _ ih =>
    simp only [sdepth] at hd ⊢
    exact Frame.below_mono (ih (by omega)) (by omega) (by omega)
  | loopExit _ _ ih => exact ih hd
  | loopNext h₁ _ _ ih₁ ih₂ =>
    have f₂ := ih₂ hd
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    rw [w₁, p₁] at f₂
    exact Frame.trans (ih₁ hd) f₂
  | call hc _ hr ih =>
    simp only [sdepth] at hd ⊢
    obtain ⟨-, w₁, p₁, m₁, -⟩ := call_eq hc
    rw [ret_eq hr]
    have := ih hd
    rwa [w₁, p₁, m₁] at this
  | @frame i _ b s₀ s₁ s₂ _ _ hp _ hq ih =>
    simp only [sdepth] at hd ⊢
    obtain ⟨p₁, -, f₀, r, w₁, hr⟩ := push_any hp
    rw [pop_mem hq]
    have f₁ := ih (by omega)
    rw [w₁, p₁] at f₁
    have hsub : Region.Sub (below s₀.sp i.frameBytes) (below s₀.sp (i.frameBytes + sdepth b)) :=
      below_sub (by omega) hd
    refine Frame.trans (f₀.sub fun r' hr' => ?_) (Frame.sub f₁ fun r' hr' => ?_)
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hsub⟩
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | hr' | rfl
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun x hx => hsub x (hr x hx)⟩
      · exact ⟨r', List.mem_append_left _ hr', fun _ h => h⟩
      · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun x hx => ?_⟩
        have := below_body' s₀.sp i.frameBytes (sdepth b) x hx
        rwa [Nat.add_comm] at this

/-- Calling verified code with any frames: as `WP.callF`, but the callee may
change the `sdepth c` bytes below the stack pointer. -/
theorem WP.callAny {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [below s.sp (sdepth c)]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hd : sdepth c < 2 ^ 64 := by decide +kernel) : WP isa (.call name c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  have hf := Exec.frameAny he hd
  obtain ⟨hr, hwr, -⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_sp, State.callEntry_mem, State.callEntry_sp] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  have e₀ : (s.callEntry.withRegions rd wr).withRegions s.rd s.wr = s.callEntry := rfl
  rw [e₀] at he'
  have hlr : s₁.lr = s.callEntry.lr := habi.2.2
  have hret : isa.ret s.callEntry (s₁.withRegions s.rd s.wr) = some (s₁.withRegions s.rd s.wr) := by
    simp only [isa, ret]
    exact ite_eq_left_of_eq_true _ _ (eq_true hlr)
  refine ⟨_, _, Exec.call (call_callEntry s) he' hret, hQ _ rfl rfl ?_ hf ?_ ?_⟩
  · simp only [State.withRegions_sp]; exact habi.2.1
  · intro r hr'
    have hl : r ∉ linkRegs := preserved_not_link r hr'
    simp only [State.withRegions_gpr]
    rw [habi.1 r hr', State.withRegions_gpr, State.callEntry_gpr s hl]
  · have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
    rw [this]; exact hpost

/-- `WP.narrowF` for code with any frames: it differs from `s` in memory only
within `wr` and the `sdepth c` bytes below the stack pointer. -/
theorem WP.narrowAny {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [below s.sp (sdepth c)]) s.mem s'.mem → P (s'.withRegions rd wr) → Q s')
    (hd : sdepth c < 2 ^ 64) : WP isa c s Q := by
  obtain ⟨t, s₁, he, hp⟩ := h
  have hf := Exec.frameAny he hd
  obtain ⟨hr, hwr, hsp⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_sp] at hr hwr hf hsp
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨t, _, he', hQ _ rfl rfl hsp hf ?_⟩
  have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  rw [this]; exact hp

/-- `WP.frameReg` for a body with any frames. -/
theorem WP.frameRegAny {r : Reg} {main : Prog isa} {s₀ : State} {Q : State → Prop}
    (hsp : 48 ≤ s₀.sp.toNat) (hd : ∀ R ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 48 + 32, 16⟩ R)
    (hmain : WP isa main (framed r s₀) fun s₂ => Q { s₂.write r (s₀.gpr r) with sp := s₀.sp })
    (hn : sdepth main + 48 < 2 ^ 64) :
    WP isa (.frame (.push r) main (.pop r)) s₀ Q := by
  refine WP.frame hsp (WP.narrowAny (rd := s₀.rd) (wr := s₀.wr) hmain ?_ ?_ ?_ (by omega))
  · intro a n hi
    exact InRegions_append_cons.mpr (.inr hi)
  · intro a n hi
    exact InRegions_append_cons (xs := []).mpr (.inr hi)
  · intro s' hrd hwr hsp' hf hq
    have hread : s'.mem.read (s'.sp + 32) 8 = s₀.gpr r := by
      rw [hsp', show (pushed r s₀).sp = s₀.sp - 48 from rfl,
        hf.read (r := ⟨s₀.sp - 48 + 32, 16⟩) (by simp [Region.Contains]) (fun R hR => ?_) (by decide)]
      · exact read_write_self _ _ _
      · rcases List.mem_append.mp hR with hR | hR
        · exact hd R hR
        · simp only [List.mem_singleton] at hR; subst hR
          exact frame_not_below s₀.sp hn
    have e : popped r s' = { (s'.withRegions s₀.rd s₀.wr).write r (s₀.gpr r) with sp := s₀.sp } := by
      simp only [popped, hread]
      simp only [hsp', hwr, pushed, List.tail_cons, BitVec.sub_add_cancel]
      cases s'
      simp only [pushed] at hrd
      subst hrd
      rfl
    rw [e]; exact hq

end VG.PPC64LE
