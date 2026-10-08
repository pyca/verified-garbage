import VerifiedGarbage.Proof.Blowfish.X86_64.KeyEnc
import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb

/-!
# The key expansion function

The initial schedule written, the P-array keyed, the constants set, and
the 521 encryptions run (`expandKey_correct`).
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem EncInv.of_upd {key : List Byte} {S B : Addr} {s₀ : State} {j : Nat} {u v : State}
    (I : EncInv key S B s₀ j u) (hv : UpdM u v) (hm : v.mem = u.mem) (hx : v.xmm = u.xmm)
    (hg : ∀ g, EncRegs g → v.gpr g = u.gpr g) : EncInv key S B s₀ j v :=
  ⟨I.le, by rw [hm]; exact I.sched, by rw [hx]; exact I.xl, by rw [hx]; exact I.xr,
    fun g h => (hg g h).trans (I.gpr g h), fun d h => by rw [hx]; exact I.xmm d h, by rw [hm]; exact I.frame,
    hv.trans I.eq⟩

theorem setReg32_upd (t : State) (r : Reg) (v : BitVec 32) : UpdM t (t.setReg32 r v) := by
  unfold UpdM; simp only [State.setReg32, State.setReg]

/-- The nine encryptions replacing the P-array. -/
theorem encryptP_run {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {u : State}
    (I : EncInv key S B s₀ 0 u) : WP isa encryptP u (EncInv key S B s₀ 9) := by
  rw [encryptP]
  apply WP.seq
  let u₁ := (u.setReg32 .rdi 0).setReg32 .rsi 9
  refine WP.of_runBlock ⟨u₁, by
    rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil], ?_⟩
  have I₁ : EncInv key S B s₀ 0 u₁ :=
    I.of_upd ((setReg32_upd _ _ _).trans (setReg32_upd _ _ _)) rfl rfl fun g ⟨_, h2, h3, _⟩ => by
      simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h3]
  have hd₁ : u₁.gpr .rdi = BitVec.ofNat 64 (8 * 0) := by
    simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rdi ≠ Reg.rsi by decide), gpr_setReg_self]; rfl
  have hs₁ : u₁.gpr .rsi = BitVec.ofNat 64 (9 - 0) := by simp only [u₁, State.setReg32, gpr_setReg_self]; rfl
  refine WP.loop (M := isa) (fun m v => ∃ j, j < 9 ∧ m = 9 - j ∧ EncInv key S B s₀ j v ∧
      v.gpr .rdi = BitVec.ofNat 64 (8 * j) ∧ v.gpr .rsi = BitVec.ofNat 64 (9 - j)) ?_ 9 u₁
    ⟨0, by omega, rfl, I₁, hd₁, hs₁⟩
  intro m v ⟨j, hj, hm, I, hd, hs⟩
  refine WP.mono (encP_step E hj I hd hs) fun v' ⟨I', d', s', z'⟩ => ?_
  have ev : isa.eval .ne v' = some (!(BitVec.ofNat 64 (9 - (j + 1)) == 0)) := by
    show v'.zf.map (!·) = _; rw [z']; rfl
  by_cases h : j + 1 = 9
  · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
  · right
    have nz : BitVec.ofNat 64 (9 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    exact ⟨by rw [ev, show (BitVec.ofNat 64 (9 - (j + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
      9 - (j + 1), by omega, j + 1, by omega, rfl, I', d', s'⟩

/-- The other 512, replacing the S-boxes. -/
theorem encryptS_run {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {u : State}
    (I : EncInv key S B s₀ 9 u) : WP isa encryptS u (EncInv key S B s₀ 521) := by
  rw [encryptS]
  apply WP.seq
  let u₁ := (u.setReg32 .rdi 0).setReg32 .rsi 512
  refine WP.of_runBlock ⟨u₁, by
    rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil], ?_⟩
  have I₁ : EncInv key S B s₀ 9 u₁ :=
    I.of_upd ((setReg32_upd _ _ _).trans (setReg32_upd _ _ _)) rfl rfl fun g ⟨_, h2, h3, _⟩ => by
      simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h3]
  have hd₁ : u₁.gpr .rdi = BitVec.ofNat 64 (sOff 9) := by
    simp only [u₁, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rdi ≠ Reg.rsi by decide), gpr_setReg_self]; rfl
  have hs₁ : u₁.gpr .rsi = BitVec.ofNat 64 (521 - 9) := by simp only [u₁, State.setReg32, gpr_setReg_self]; rfl
  refine WP.loop (M := isa) (fun m v => ∃ j, 9 ≤ j ∧ j < 521 ∧ m = 521 - j ∧ EncInv key S B s₀ j v ∧
      v.gpr .rdi = BitVec.ofNat 64 (sOff j) ∧ v.gpr .rsi = BitVec.ofNat 64 (521 - j)) ?_ 512 u₁
    ⟨9, by omega, by omega, rfl, I₁, hd₁, hs₁⟩
  intro m v ⟨j, h9, hj, hm, I, hd, hs⟩
  refine WP.mono (encS_step E h9 hj I hd hs) fun v' ⟨I', d', s', z'⟩ => ?_
  have ev : isa.eval .ne v' = some (!(BitVec.ofNat 64 (521 - (j + 1)) == 0)) := by
    show v'.zf.map (!·) = _; rw [z']; rfl
  by_cases h : j + 1 = 521
  · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
  · right
    have nz : BitVec.ofNat 64 (521 - (j + 1)) ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
    exact ⟨by rw [ev, show (BitVec.ofNat 64 (521 - (j + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
      521 - (j + 1), by omega, j + 1, by omega, by omega, rfl, I', d', s'⟩

/-- What key expansion may assume. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .rsi).toNat
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]
  wr : s.wr = [⟨s.gpr .rdx, 4168⟩, ⟨s.gpr .rcx, 32⟩]
  keySch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, 4168⟩
  schBuf : (⟨s.gpr .rdx, 4168⟩ : Region).Disjoint ⟨s.gpr .rcx, 32⟩
  fitK : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  fitS : (s.gpr .rdx).toNat + 4168 ≤ 2 ^ 64
  fitB : (s.gpr .rcx).toNat + 32 ≤ 2 ^ 64

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : scheduleAt s'.mem (s.gpr .rdx) = expandKey (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  gpr : ∀ g, EncRegs g → s'.gpr g = s.gpr g
  frame : Frame [⟨s.gpr .rdx, 4168⟩, ⟨s.gpr .rcx, 32⟩] s.mem s'.mem

theorem pxor_self_run (t : State) (d : XReg) :
    ∃ t', runBlock isa [bin .pxor d d] t = some t' ∧ dword (t'.xmm d) 0 = 0 ∧
      (∀ d', d' ≠ d → t'.xmm d' = t.xmm d') ∧ t'.gpr = t.gpr ∧ Upd t t' := by
  refine ⟨(XOp.bin .pxor d d).exec t, by rw [bin, runBlock_cons, exec_xop, runStep_some, runBlock_nil], ?_,
    fun d' h => ?_, rfl, ?_⟩
  · simp only [XOp.exec, xmm_setXmm_self, XBinOp.eval, BitVec.xor_self]; rfl
  · simp only [XOp.exec, xmm_setXmm_of_ne _ _ h]
  · unfold Upd; simp only [XOp.exec, State.setXmm]

theorem expandKey_correct {s : State} (P : KeyPre s) :
    WP isa Impl.Blowfish.X86_64.expandKey s (KeyPost s) := by
  let K := s.gpr .rdi
  let L := (s.gpr .rsi).toNat
  let S := s.gpr .rdx
  let B := s.gpr .rcx
  have fitS := P.fitS
  have fitB := P.fitB
  have hL : 4 ≤ L ∧ L ≤ 56 := P.valid
  have hL64 : L < 2 ^ 64 := (s.gpr .rsi).isLt
  have mS : (⟨S, 4168⟩ : Region) ∈ s.wr := by rw [P.wr]; exact List.mem_cons_self
  rw [Impl.Blowfish.X86_64.expandKey]
  -- the initial schedule
  apply WP.seq
  obtain ⟨t₁, r₁, d₁, f₁, g₁, e₁⟩ := initSteps_run (S := S) (t := s) rfl (SchedW.of_mem mS) 521 (by omega)
  refine WP.of_runBlock ⟨t₁, by rw [initSchedule_eq]; exact r₁, ?_⟩
  have rd₁ : t₁.rd = s.rd := by rw [e₁]
  have wr₁ : t₁.wr = s.wr := by rw [e₁]
  have hT : ∀ o < 4168, t₁.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o :=
    fun o ho => table_byte (fun i hi => by rw [initWords_getD hi]; exact d₁ i hi) ho
  have keyS : ∀ c < L, ¬ (⟨S, 4168⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1 := fun c hc h =>
    P.keySch _ (Offset.contains_base K (by omega) (by omega)) h
  have hB₁ : bytesAt t₁.mem K L = bytesAt s.mem K L := bytesAt_frame f₁ fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact keyS c hc
  -- the keyed P-array
  apply WP.seq
  have KE : KeyPEnv S K L t₁ :=
    ⟨by omega, hL64, fun c hc => by
        rw [rd₁, wr₁, P.rd]; exact ⟨_, List.mem_cons_self, Offset.contains_base K (by omega) (by omega)⟩,
      by rw [g₁ _ (by decide)], by rw [g₁ _ (by decide)]; simp [L],
      by rw [g₁ _ (by decide)], SchedW.of_mem (by rw [wr₁]; exact mS), fitS, keyS⟩
  refine WP.mono (keyP_run KE) fun t₂ I₂ => ?_
  have hK : scheduleAt t₂.mem S = keyed (bytesAt s.mem K L) := by
    refine keyed_of_mem (fun o ho => ?_) (fun i hi => ?_)
    · rw [I₂.frame.bytes (R := ⟨S, 4096⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint S (by omega) (by omega)) (by show 4096 ≤ 2 ^ 64; decide) ho]
      exact hT o (by omega)
    · rw [I₂.done i hi, table_P hT hi, hB₁]
  -- the constants and the zero block
  apply WP.seq
  obtain ⟨t₃, r₃, o₃, x₃, l₃, k₃, g₃, up₃⟩ := constants_run t₂
  obtain ⟨t₄, r₄, z₄, k₄, g₄, up₄⟩ := pxor_self_run t₃ xL
  obtain ⟨t₅, r₅, z₅, k₅, g₅, up₅⟩ := pxor_self_run t₄ xR
  refine WP.of_runBlock ⟨t₅, cat_run r₃ (cat_run r₄ r₅), ?_⟩
  have U₅ : UpdM t₂ t₅ := UpdM.trans (UpdM.of_upd up₅) (UpdM.trans (UpdM.of_upd up₄) (UpdM.of_upd up₃))
  have m₅ : t₅.mem = t₂.mem := by
    rw [show t₅.mem = t₄.mem by rw [up₅], show t₄.mem = t₃.mem by rw [up₄], up₃]
  have G₅ : ∀ g, g ≠ .r11 → t₅.gpr g = t₂.gpr g := fun g h => by rw [g₅, g₄, g₃ _ h]
  have G₂ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r10 → g ≠ .r11 → t₂.gpr g = s.gpr g := fun g h1 h2 h3 h4 => by
    rw [I₂.gpr g h1 h2 h3 h4, g₁ g h4]
  have EE : EncEnv S B t₅ := by
    refine ⟨by rw [G₅ _ (by decide), G₂ _ (by decide) (by decide) (by decide) (by decide)],
      by rw [G₅ _ (by decide), G₂ _ (by decide) (by decide) (by decide) (by decide)],
      SchedW.of_mem (by rw [U₅, I₂.eq, wr₁]; exact mS),
      by rw [U₅, I₂.eq, wr₁, P.wr]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩,
      P.schBuf, fitS, fitB, ?_, ?_, ?_⟩
    · rw [k₅ _ (by decide), k₄ _ (by decide), o₃]
    · rw [k₅ _ (by decide), k₄ _ (by decide), x₃]
    · rw [k₅ _ (by decide), k₄ _ (by decide), l₃]
  have I₅ : EncInv (bytesAt s.mem K L) S B t₅ 0 t₅ :=
    ⟨by omega, by rw [m₅, hK]; rfl, by rw [k₅ _ (by decide), z₄]; rfl, by rw [z₅]; rfl,
      fun _ _ => rfl, fun _ _ => rfl, Frame.refl _ _, by unfold UpdM; rfl⟩
  -- the encryptions
  apply WP.seq
  refine WP.mono (encryptP_run EE I₅) fun t₆ I₆ => ?_
  refine WP.mono (encryptS_run EE I₆) fun t₇ I₇ => ?_
  refine ⟨by rw [I₇.sched, ← expandKey_eq], fun g hg => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
    rw [I₇.gpr g ⟨h1, h2, h3, h4, h5, h6, h7⟩, G₅ g h7, G₂ g h1 h4 h6 h7]
  · refine Frame.trans ?_ (I₇.frame.trans (Frame.refl _ _))
    rw [m₅]
    refine Frame.trans (f₁.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self) ?_
    refine Frame.sub I₂.frame fun r hr => ⟨⟨S, 4168⟩, List.mem_cons_self, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base S (by omega)

end VG.Proof.Blowfish.X86_64
