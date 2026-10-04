import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT3
import VerifiedGarbage.Proof.Argon2.X86.Derive.ReduceCT
import VerifiedGarbage.Proof.Argon2.X86.Derive.InitialCT
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT1

section

section

/-!
# Argon2 on x86 (32-bit): memory initialization, in two runs

`memoryInit_rel`: clearing the matrix and the calls of H′ for the first two
blocks of every lane leak the same trace in two runs with the same public
data: the calls' arguments are H₀'s place in the locals and the blocks'
addresses, which only the lane fixes.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_addi)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (argOff columnOff laneWordOff)

/-- The state before block `c` of lane `l`. -/
def IB (s₀ : State) (h0 : List Byte) (l c : Nat) (s : State) : Prop :=
  Inv s₀ s ∧ Prm s₀ s ∧ bytesAt s.mem ((E s₀).setWidth 64) 64 = h0 ∧ s.gpr .esi = BitVec.ofNat 32 l ∧
    s.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem initBlock_w {h0 : List Byte} {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2) {s : State}
    (h : IB s₀ h0 l c s) : WP isa (Impl.Argon2.X86.Derive.initBlock c) s (IB s₀ h0 l c) :=
  (initBlock_ok hp h.1 h.2.1 h.2.2.1 hl hc h.2.2.2.1 h.2.2.2.2).mono fun _ ⟨i, p, b, e, d, _, _⟩ =>
    ⟨i, p, b, e.trans h.2.2.2.1, d.trans h.2.2.2.2⟩

omit hp in
theorem nextBlock_w {h0 : List Byte} {l : Nat} {s : State} (h : IB s₀ h0 l 0 s) :
    WP isa (.block [.alu .add .edi (.imm 1024)]) s (IB s₀ h0 l 1) :=
  wp_addi fun t u => WP.block_nil ⟨h.1.upd u (by decide) (by decide), h.2.1.of_mem u.mem,
    by rw [u.mem]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1, by
      rw [u.gpr, h.2.2.2.2, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, show (l * (prm s₀).laneLen + 0) * 1024 + 1024 = (l * (prm s₀).laneLen + 1) * 1024 by
          rw [Nat.add_mul, Nat.add_mul]]⟩

/-- The instructions before `initBlock`'s call of H′. -/
theorem ibBlk_ok {s : State} (h : Inv s₀ s) (c : Nat) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 c)), .store (at_ .ebp columnOff) .eax,
      .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72), .mov .ecx (.imm 1024),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi := by
  refine wp_movi fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ _ _ g₂ _ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ _ _ g₃ _ => ?_
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => wp_ldarg hp ((i₃.upd u₄ (by decide) (by decide)).upd u₅
    (by decide) (by decide)) (i := 15) (by decide) fun s₆ u₆ => WP.block_nil
    ⟨((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide) (by decide),
      u₆.gpr, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr],
      by rw [u₆.other _ (by decide), u₅.gpr],
      by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃, g₂,
        u₁.other _ (by decide)]⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `initBlock c` leaks the same trace in two runs at the same lane. -/
theorem initBlock_rel {h₁ h₂ : List Byte} {l c : Nat} (hl : l < lanesN s₀₁) (hc : c < 2)
    (hchk : ∃ hc, (VG.Taint.check taint (τB [] []) (.block [.mov .eax (.imm (BitVec.ofNat 32 c)),
      .store (at_ .ebp columnOff) .eax, .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72),
      .mov .ecx (.imm 1024), .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => IB s₀₁ h₁ l c s₁ ∧ IB s₀₂ h₂ l c s₂) (Impl.Argon2.X86.Derive.initBlock c)
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have cellF : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ →
      (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 ∧ l * (prm s₀).laneLen + c < blocksN s₀ :=
    fun {s₀} hp hl => by
      have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
      have : l * (prm s₀).laneLen + c < blocksN s₀ := by
        rw [hp.blocks_eq]
        have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega)
        rw [Nat.succ_mul] at this
        omega
      exact ⟨by omega, this⟩
  have pre : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ → ∀ {s t : State}, IB s₀ h₁ l c s ∨ IB s₀ h₂ l c s →
      Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧ t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi →
      Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, (t.gpr .ebp).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .eax).toNat ≤ R.len) ∧ (t.gpr .ebp).toNat + (t.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, outR s₀], ∃ off, (t.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .ecx).toNat ≤ R.len) ∧ (t.gpr .edi).toNat + (t.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .ecx).toNat := fun {s₀} hp hl {s t} hs ⟨i, d, a, c', e⟩ => by
    have hE := E_hi hp
    have hm := hp.mem_fits
    obtain ⟨hc', hk⟩ := cellF hp hl
    have ed : t.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024) := by
      rw [e]; rcases hs with hs | hs <;> exact hs.2.2.2.2
    have an : (memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)).toNat =
        (memP s₀).toNat + (l * (prm s₀).laneLen + c) * 1024 := add_nat (by omega)
    refine ⟨i, d, ⟨locR s₀, by simp, 0, by rw [i.ebp]; simp, by rw [a]; show 0 + 72 ≤ 144; decide⟩,
      by rw [i.ebp, a]; show (E s₀).toNat + 72 ≤ 2 ^ 32; omega,
      ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [ed, cell_addr hp hk]; rfl,
        by rw [c']; exact hc'⟩, by rw [ed, c', an]; show _ + 1024 ≤ 2 ^ 32; omega,
      by rw [c']; decide⟩
  unfold Impl.Argon2.X86.Derive.initBlock Impl.Argon2.X86.Derive.hPrimeCall
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) hchk)
    (G₁ := fun t => ∃ s, IB s₀₁ h₁ l c s ∧ Inv s₀₁ t ∧ t.gpr .edx = scrP s₀₁ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (G₂ := fun t => ∃ s, IB s₀₂ h₂ l c s ∧ Inv s₀₂ t ∧ t.gpr .edx = scrP s₀₂ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (fun s h => (ibBlk_ok T.hp₁ h.1 c).mono fun t ht => ⟨s, h, ht⟩)
    (fun s h => (ibBlk_ok T.hp₂ h.1 c).mono fun t ht => ⟨s, h, ht⟩) ?_
  refine T.hcall_rel (r := .ebp) (by decide) fun s₁ s₂ ⟨a₁, g₁, k₁⟩ ⟨a₂, g₂, k₂⟩ =>
    ⟨pre T.hp₁ hl (.inl g₁) k₁, pre T.hp₂ (T.pb.lanesN_eq ▸ hl) (.inr g₂) k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.1.ebp, k₂.1.ebp, T.pb.E]
  · rw [k₁.2.2.1, k₂.2.2.1]
  · rw [k₁.2.2.2.2, k₂.2.2.2.2, g₁.2.2.2.2, g₂.2.2.2.2, pe, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]

/-- `initLane` leaks the same trace in two runs at the same lane. -/
theorem initLane_rel {h₁ h₂ : List Byte} {l : Nat} (hl : l < lanesN s₀₁) :
    RelCT isa (fun s₁ s₂ => LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) Impl.Argon2.X86.Derive.initLane fun _ _ => True := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have ib : ∀ {s₀ s : State} {h0 : List Byte}, LI s₀ h0 l s → IB s₀ h0 l 0 s := fun h =>
    ⟨h.inv, h.pr, h.b0, h.esi, by rw [Nat.add_zero]; exact h.edi⟩
  unfold Impl.Argon2.X86.Derive.initLane
  refine (RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_).mono (fun _ _ h => ⟨ib h.1, ib h.2⟩) fun _ _ h => h
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => nextBlock_w h) (fun s h => nextBlock_w h) ?_
  refine RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `memoryInit` leaks the same trace in two runs. -/
theorem memoryInit_rel {h₁ h₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ bytesAt s₁.mem ((E s₀₁).setWidth 64) 64 = h₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ bytesAt s₂.mem ((E s₀₂).setWidth 64) 64 = h₂))
      Impl.Argon2.X86.Derive.memoryInit fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.X86.Derive.memoryInit
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => clearW_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => clearW_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => laneStart_ok T.hp₁ h) (fun s h => laneStart_ok T.hp₂ h) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := HPrime.rel_wp (T.initLane_rel (by rw [hN]; exact hl))
    (fun s h => lane_ok T.hp₁ (by rw [hN]; exact hl) h) (fun s h => lane_ok T.hp₂ (by rw [hN₂]; exact hl) h)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, e, k₁, k₂⟩

end Two

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveX86.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frames.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- The parameters' block leaks the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)) fun _ _ => True := by
  rw [← List.singleton_append]
  refine RelCT.block_split (RelCT.seqW (F₁ := fun s => s = entry s₀₁) (F₂ := fun s => s = entry s₀₂)
    (RelCT.taint (A := taint) (τr [.esp]) (fun s₁ s₂ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2, entry_esp, entry_esp, T.pb.E]) (by taint_decide))
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i) ?_)
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.X86.Derive.body fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)
    (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  unfold Impl.Argon2.X86.Derive.body
  refine RelCT.seqW T.parameters_rel (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t)
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₁ fun t i p => WP.block_nil ⟨i, p⟩)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.mov .ebp (.reg .esp) :: Impl.Argon2.X86.Derive.parameters)]
      exact parameters_ok T.hp₂ fun t i p => WP.block_nil ⟨i, p⟩) ?_
  refine RelCT.seqW T.code_rel (fun s h => code_ok T.hp₁ h.1 h.2) (fun s h => code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (prm s₀₁)
      (Spec.Argon2.initialHash (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (prm s₀₂)
      (Spec.Argon2.initialHash (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
  exact T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end Two

/-- A frame around code related from the pushed states. -/
theorem frame_chain {P : State → State → Prop} {f : State → State} {rs : List Reg} {r : Reg} {k : Nat}
    {body : Prog isa} {Q : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → (f s₁).gpr .esp = (f s₂).gpr .esp)
    (h : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed rs (f s₁) ∧ b = pushed rs (f s₂)) body Q) :
    RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = f s₁ ∧ b = f s₂) (.frame (.push rs) body (.pop r k))
      fun _ _ => True :=
  RelCT.frame (fun a b ⟨s₁, s₂, hp, ha, hb⟩ => by subst ha hb; exact hsp s₁ s₂ hp)
    (h.mono (fun a b ⟨x, y, ⟨s₁, s₂, hp, hx, hy⟩, ha, hb⟩ => ⟨s₁, s₂, hp, by rw [ha, hx], by rw [hb, hy]⟩)
      fun _ _ h => h)

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => deriveX86.pre s₁ ∧ deriveX86.pre s₂ ∧ deriveX86.pub s₁ s₂)
      Impl.Argon2.X86.Derive.derive fun _ _ => True := by
  have esp : ∀ s₁ s₂ : State, s₁.gpr .esp = s₂.gpr .esp → ∀ rs : List Reg,
      (pushed rs s₁).gpr .esp = (pushed rs s₂).gpr .esp := fun s₁ s₂ h rs => by
    rw [pushed_esp, pushed_esp, h]
  refine (frame_chain (f := id) (fun s₁ s₂ h => h.2.2.1.1) (frame_chain (f := fun s => pushed [.ebp] s)
    (fun s₁ s₂ h => esp _ _ h.2.2.1.1 _) (frame_chain (f := fun s => pushed [.edi] (pushed [.ebp] s))
    (fun s₁ s₂ h => esp _ _ (esp _ _ h.2.2.1.1 _) _)
    (frame_chain (f := fun s => pushed [.esi] (pushed [.edi] (pushed [.ebp] s)))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _)
    (frame_chain (Q := fun _ _ => True) (f := fun s => pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s))))
    (fun s₁ s₂ h => esp _ _ (esp _ _ (esp _ _ (esp _ _ h.2.2.1.1 _) _) _) _) ?_))))).mono
    (fun s₁ s₂ h => ⟨s₁, s₂, h, rfl, rfl⟩) fun _ _ h => h
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, ha, hb⟩ e₁ e₂
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 a b t₁ t₂ a' b' ⟨ha, hb⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveX86.pre deriveX86.pub Impl.Argon2.X86.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation is verified

`derive_verified`: the derivation against `deriveX86` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, which also lets the code write
its arguments, by narrowing (`deriveWide`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86

/-! ## A state satisfying the precondition -/

/-- The arguments: Argon2d, empty inputs, one pass over 8 KiB in one lane, a
4-byte tag. -/
def satArgs : List Nat := [0, 0, 0, 0, 0, 1, 8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satArgs` at `0x40004`. -/
def satMem (a : Addr) : Byte :=
  if 0x40004 ≤ a.toNat ∧ a.toNat < 0x4004C then
    ((BitVec.ofNat 32 (satArgs[(a.toNat - 0x40004) / 4]?.getD 0)) >>> (8 * ((a.toNat - 0x40004) % 4))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .esp => 0x40000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40004, 72⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem sat_args : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre satState := by
  have a : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
  have e : argAddr satState 0 = 0x40004 := by decide
  have esp : satState.gpr .esp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, scrR, outR, argR, retR, stkR, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, E0, kindV, itersN, mcostN, lanesN, threadsN, prm,
    a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
    a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), a 16 (by decide), a 17 (by decide),
    e, esp]
  all_goals first
    | rfl
    | decide
    | (intro r hr w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
         exact Region.disjoint_of_sep (by decide))
    | (intro w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
       rcases hw with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | exact Region.disjoint_of_sep (by decide)

theorem derive_verified : Verified X86.target Impl.Argon2.X86.Derive.derive deriveX86 :=
  ⟨fun _ hs => correct hs, derive_ct, ⟨satState, sat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `deriveX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def deriveWide : Contract X86.isa :=
  { deriveX86 with
    pre := fun s =>
      let pw : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
      let salt : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let sec : Region := ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩
      let ad : Region := ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩
      let mem : Region := ⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩
      let scr : Region := ⟨(arg s 15).setWidth 64, 16384⟩
      let out : Region := ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩
      let args : Region := ⟨argAddr s 0, 72⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩
      s.rd = [pw, salt, sec, ad] ∧ s.wr = [mem, scr, out, args] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      ret.Disjoint mem ∧ ret.Disjoint scr ∧ ret.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32 ∧
      (arg s 13).toNat + (arg s 14).toNat * 1024 ≤ 2 ^ 32 ∧ (arg s 15).toNat + 16384 ≤ 2 ^ 32 ∧
      (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 32 ∧ 244 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 72 ≤ 2 ^ 32 ∧ (arg s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat) (arg s 2).toNat (arg s 4).toNat (arg s 10).toNat (arg s 12).toNat ∧
      1 ≤ (arg s 8).toNat ∧ (arg s 8).toNat < 2 ^ 24 ∧
      (arg s 14).toNat = (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat).blocks }

/-- A state satisfying `deriveWide.pre`. -/
def satWide : State where
  gpr := satState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩, ⟨0x40004, 72⟩]

macro "dnarrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [deriveX86, deriveWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem deriveWide_pre {s : State} (h : deriveWide.pre s) :
    DPre (s.withRegions [⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
      ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩]
      [⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩]) := by
  obtain ⟨_, _, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃, r₁, r₂, r₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, kd, vd, t₁, t₂, bl⟩ := h
  have e : (⟨((s.gpr .esp) - BitVec.ofNat 32 244).setWidth 64, 244⟩ : Region) =
      ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ := by rw [Taint.sub_setWidth lo]; rfl
  refine
    { rd := rfl
      wr := rfl
      ro_w := ?_
      mem_scr := m₁
      mem_out := m₂
      scr_out := m₃
      ret_w := ?_
      stk_all := ?_
      pw_fits := f₁
      salt_fits := f₂
      sec_fits := f₃
      ad_fits := f₄
      mem_fits := f₅
      scr_fits := f₆
      out_fits := f₇
      esp_lo := lo
      esp_hi := (by show (s.gpr .esp).toNat + 76 ≤ 2 ^ 32; omega)
      kind_le := kd
      valid := vd
      threads := ⟨t₁, t₂⟩
      blocks := bl }
  · show ∀ r ∈ [(⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ : Region), ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
        ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩],
      ∀ w ∈ [(⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩ : Region), ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], r.Disjoint w
    intro r hr w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ w ∈ [(⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩ : Region), ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint w
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ r ∈ [(⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ : Region), ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
        ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩,
        ⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], (below (s.gpr .esp) 244).Disjoint r
    rw [show below (s.gpr .esp) 244 = ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ from e]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem deriveWide_verified : Verified X86.target Impl.Argon2.X86.Derive.derive deriveWide :=
  Verified.narrowTo derive_verified
    (fun s => [⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
      ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩])
    (fun s => [⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
      ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩])
    (fun _ h => deriveWide_pre h)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩)
    (fun _ _ _ h => by dnarrow at h ⊢; exact h)
    (fun _ _ _ _ h => by dnarrow; exact h)
    ⟨satWide, by
      have a : ∀ i < 18, arg satWide i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
      have e : argAddr satWide 0 = 0x40004 := by decide
      simp only [deriveWide, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
        a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
        a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide),
        a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem derive_implies : deriveWide.Implies (Spec.Argon2.deriveContract X86.abi 244) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, deriveWide, deriveX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [satWide, satState, satMem, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read, Spec.Argon2.params,
      Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen] using satWide

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified X86.target Impl.Argon2.X86.Derive.derive (Spec.Argon2.deriveContract X86.abi 244) :=
  deriveWide_verified.of_implies derive_implies

end VG.Proof.Argon2.X86.Derive
