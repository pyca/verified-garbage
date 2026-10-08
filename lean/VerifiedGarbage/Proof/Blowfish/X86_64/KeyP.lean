import VerifiedGarbage.Proof.Blowfish.X86_64.KeyInit

/-!
# Key expansion: the keyed P-array

`keyP_run`: the 18 P-array entries XORed in place with the key's words,
cycling through the key's bytes.
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- `u` is `t` with other registers, flags and memory. -/
def UpdM (c a : State) : Prop :=
  a = { c with gpr := a.gpr, xmm := a.xmm, cf := a.cf, zf := a.zf, sf := a.sf, of := a.of, mem := a.mem }

theorem UpdM.trans {a b c : State} (h1 : UpdM b a) (h2 : UpdM c b) : UpdM c a := by
  unfold UpdM at *; rw [h1]; rw [h2]

theorem UpdM.of_upd {a c : State} (h : Upd c a) : UpdM c a := by
  unfold UpdM; unfold Upd at h; rw [h]

theorem UpdM.store {c : State} (m : Mem) : UpdM c { c with mem := m } := rfl

theorem ea_idx (t : State) (b i : Reg) (B : Addr) (n d : Nat) (h1 : t.gpr b = B)
    (h2 : t.gpr i = BitVec.ofNat 64 n) :
    t.ea { base := b, index := some i, disp := Int.ofNat d } = B + BitVec.ofNat 64 (d + n) := by
  simp only [State.ea, h1, h2, BitVec.mul_one, Rc2.X86_64.offset_nat]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem ea_idx0 (t : State) (b i : Reg) (B : Addr) (n : Nat) (h1 : t.gpr b = B)
    (h2 : t.gpr i = BitVec.ofNat 64 n) : t.ea { base := b, index := some i } = B + BitVec.ofNat 64 n := by
  simp only [State.ea, h1, h2, BitVec.mul_one, show BitVec.ofInt 64 0 = 0 from rfl]
  exact BitVec.add_zero _

theorem exec_movzx8 {s : State} {m : MemOp} {d : Reg} (h : InRegions (s.rd ++ s.wr) (s.ea m) 1) :
    exec (.movzx8 d m) s = some (s.setReg d ((s.mem (s.ea m)).setWidth 64)) := by
  simp only [exec, State.load8, h, ite_true, Option.map_some]

theorem shift32_run (t : State) (op : ShiftOp) (d : Reg) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 31) (hop : op ≠ .ror) :
    ∃ t', exec (.shift32 op d n) t = some t' ∧
      t'.gpr d = ((if op = .shl then (t.gpr d).setWidth 32 <<< n else (t.gpr d).setWidth 32 >>> n)).setWidth 64 ∧
      (∀ g, g ≠ d → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ Upd t t' := by
  cases op with
  | ror => exact absurd rfl hop
  | shr =>
    refine ⟨_, by simp only [exec, execShift32, hn, and_self, ↓reduceIte]; rfl, ?_, fun g hg => ?_, ?_, ?_⟩
    · simp only [State.setReg32, gpr_setReg_self, reduceCtorEq, ↓reduceIte]
    · simp only [State.setReg32, gpr_setReg_of_ne _ _ hg, gpr_setFlags]
    · rfl
    · unfold Upd; simp only [State.setReg32, State.setReg, State.setFlags]
  | shl =>
    refine ⟨_, by simp only [exec, execShift32, hn, and_self, ↓reduceIte]; rfl, ?_, fun g hg => ?_, ?_, ?_⟩
    · simp only [State.setReg32, gpr_setReg_self, ↓reduceIte]
    · simp only [State.setReg32, gpr_setReg_of_ne _ _ hg, gpr_setFlags]
    · rfl
    · unfold Upd; simp only [State.setReg32, State.setReg, State.setFlags]

theorem logic32_run (t : State) (op : AluOp) (d r : Reg) (hop : op = .or ∨ op = .xor) :
    ∃ t', exec (.alu32 op d (.reg r)) t = some t' ∧
      t'.gpr d = ((if op = .or then (t.gpr d).setWidth 32 ||| (t.gpr r).setWidth 32
        else (t.gpr d).setWidth 32 ^^^ (t.gpr r).setWidth 32)).setWidth 64 ∧
      (∀ g, g ≠ d → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  rcases hop with rfl | rfl
  · refine ⟨_, rfl, ?_, fun g hg => ?_, ?_⟩
    · simp only [State.setReg32, gpr_setReg_self, ↓reduceIte]
    · simp only [State.setReg32, gpr_setReg_of_ne _ _ hg, gpr_arithFlags]
    · unfold Upd; simp only [State.setReg32, State.setReg, arithFlags, State.setFlags]
  · refine ⟨_, rfl, ?_, fun g hg => ?_, ?_⟩
    · simp only [State.setReg32, gpr_setReg_self, reduceCtorEq, ↓reduceIte]
    · simp only [State.setReg32, gpr_setReg_of_ne _ _ hg, gpr_arithFlags]
    · unfold Upd; simp only [State.setReg32, State.setReg, arithFlags, State.setFlags]

theorem cmp_run (t : State) (d : Reg) (src : Src) (hs : ∀ m, src ≠ .mem m) :
    ∃ t' b, exec (.alu .cmp d src) t = some t' ∧ readSrc t src = some b ∧
      t'.zf = some (t.gpr d - b == 0) ∧ t'.gpr = t.gpr ∧ Upd t t' := by
  cases src with
  | mem m => exact absurd rfl (hs m)
  | reg r => exact ⟨_, _, rfl, rfl, rfl, rfl, by unfold Upd; simp only [arithFlags, State.setFlags]⟩
  | imm v => exact ⟨_, _, rfl, rfl, rfl, rfl, by unfold Upd; simp only [arithFlags, State.setFlags]⟩

theorem byte_zext (b : BitVec 8) : (b.setWidth 64).setWidth 32 = b.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth]
  by_cases h : i < 8 <;> simp [h, show i < 64 by omega]

theorem ofNat_sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := by
      intro e
      have e' := congrArg (· + BitVec.ofNat 64 b) e
      simp only [BitVec.sub_add_cancel] at e'
      rw [show (0 : BitVec 64) + BitVec.ofNat 64 b = BitVec.ofNat 64 b from BitVec.zero_add _] at e'
      have := congrArg BitVec.toNat e'
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      exact h this
    simp only [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

/-- The key's bytes are readable. -/
def KeyIn (s : State) (K : Addr) (L : Nat) : Prop := ∀ c < L, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1

theorem KeyIn.of_eq {s t : State} {K : Addr} {L : Nat} (h : KeyIn s K L) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    KeyIn t K L := by
  intro c hc; rw [hrd, hwr]; exact h c hc

theorem keyByte_run {s : State} {K : Addr} {L c : Nat} (hc : c < L) (hL : L < 2 ^ 64)
    (hK : KeyIn s K L) (h0 : s.gpr .rdi = K) (h1 : s.gpr .rsi = BitVec.ofNat 64 L)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 c) :
    WP isa keyByte s fun s' =>
      (s'.gpr .r11).setWidth 32 = ((s.gpr .r11).setWidth 32 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).zeroExtend 32 ∧
      s'.gpr .r10 = BitVec.ofNat 64 ((c + 1) % L) ∧
      (∀ g, g ≠ .rax → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) ∧ Upd s s' := by
  rw [keyByte]
  apply WP.seq
  have ea₀ : s.ea { base := .rdi, index := some .r10 } = K + BitVec.ofNat 64 c := ea_idx0 s _ _ _ _ h0 h10
  let s₁ := s.setReg .rax ((s.mem (K + BitVec.ofNat 64 c)).setWidth 64)
  have e₁ : exec (.movzx8 .rax { base := .rdi, index := some .r10 }) s = some s₁ := by
    rw [exec_movzx8 (by rw [ea₀]; exact hK c hc), ea₀]
  obtain ⟨s₂, e₂, r₂, g₂, -, u₂⟩ := shift32_run s₁ .shl .r11 8 (by decide) (by decide)
  obtain ⟨s₃, e₃, r₃, g₃, u₃⟩ := logic32_run s₂ .or .r11 .rax (.inl rfl)
  obtain ⟨s₄, e₄, r₄, g₄, -, u₄⟩ := add_imm_run s₃ .r10 1
  obtain ⟨s₅, b₅, e₅, rb₅, z₅, g₅, u₅⟩ := cmp_run s₄ .r10 (.reg .rsi) (fun _ => by simp)
  refine WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil], ?_⟩
  have up₅ : Upd s s₅ := Upd.trans u₅ (Upd.trans u₄ (Upd.trans u₃ (Upd.trans u₂ (by
    unfold Upd; simp only [s₁, State.setReg]))))
  have gk : ∀ g, g ≠ .rax → g ≠ .r10 → g ≠ .r11 → s₅.gpr g = s.gpr g := fun g h1 h2 h3 => by
    rw [g₅, g₄ _ h2, g₃ _ h3, g₂ _ h3]; simp only [s₁, gpr_setReg_of_ne _ _ h1]
  have x11 : (s₅.gpr .r11).setWidth 32 =
      ((s.gpr .r11).setWidth 32 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).zeroExtend 32 := by
    rw [g₅, g₄ _ (by decide), r₃, r₂, g₂ .rax (by decide)]
    simp only [s₁, gpr_setReg_self, gpr_setReg_of_ne _ _ (show Reg.r11 ≠ Reg.rax by decide), ↓reduceIte,
      setWidth_setWidth_32, byte_zext]
  have x10 : s₅.gpr .r10 = BitVec.ofNat 64 (c + 1) := by
    rw [g₅, r₄, g₃ _ (by decide), g₂ _ (by decide)]
    simp only [s₁, gpr_setReg_of_ne _ _ (show Reg.r10 ≠ Reg.rax by decide), h10]
    apply BitVec.eq_of_toNat_eq; simp
  have b₅' : b₅ = BitVec.ofNat 64 L := by
    simp only [readSrc, Option.some.injEq] at rb₅
    rw [← rb₅, g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]
    simp only [s₁, gpr_setReg_of_ne _ _ (show Reg.rsi ≠ Reg.rax by decide), h1]
  have zf : isa.eval .e s₅ = some (c + 1 == L) := by
    show s₅.zf = _
    rw [z₅, show s₄.gpr .r10 = s₅.gpr .r10 by rw [g₅], x10, b₅', ofNat_sub_beq (by omega) hL]
  apply WP.ite _ zf
  · intro h
    have hL' : c + 1 = L := by simpa using h
    refine WP.of_runBlock ⟨s₅.setReg32 .r10 0, by rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil],
      ?_, ?_, fun g h1 h2 h3 => ?_, ?_⟩
    · simp only [State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r11 ≠ Reg.r10 by decide)]; exact x11
    · simp only [State.setReg32, gpr_setReg_self, ← hL', Nat.mod_self]; rfl
    · simp only [State.setReg32, gpr_setReg_of_ne _ _ h2]; exact gk g h1 h2 h3
    · exact Upd.trans (by unfold Upd; simp only [State.setReg32, State.setReg]) up₅
  · intro h
    have hL' : c + 1 ≠ L := by simpa using h
    exact WP.block_nil ⟨x11, by rw [x10, Nat.mod_eq_of_lt (by omega)], gk, up₅⟩

/-- What a P-array entry's code needs. -/
structure KeyWordEnv (S K : Addr) (L i : Nat) (s : State) : Prop where
  lt : i < 18
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : KeyIn s K L
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 L
  rdx : s.gpr .rdx = S
  r10 : s.gpr .r10 = BitVec.ofNat 64 ((4 * i) % L)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * i)
  wrS : InRegions s.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4

theorem keyWord_run {S K : Addr} {L i : Nat} {s : State} (E : KeyWordEnv S K L i s) :
    WP isa Impl.Blowfish.X86_64.keyWord s fun s' =>
      s'.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      s'.gpr .r10 = BitVec.ofNat 64 ((4 * (i + 1)) % L) ∧ s'.gpr .r8 = BitVec.ofNat 64 (4 * (i + 1)) ∧
      s'.zf = some (4 * (i + 1) == 72) ∧
      (∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) ∧ UpdM s s' := by
  have hL0 := E.L0
  have hi := E.lt
  rw [Impl.Blowfish.X86_64.keyWord]
  apply WP.seq
  let s₀ := s.setReg32 .r11 0
  refine WP.of_runBlock ⟨s₀, by rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil], ?_⟩
  have g₀ : ∀ g, g ≠ .r11 → s₀.gpr g = s.gpr g := fun g h => by
    simp only [s₀, State.setReg32, gpr_setReg_of_ne _ _ h]
  have x11₀ : (s₀.gpr .r11).setWidth 32 = 0 := by
    simp only [s₀, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]
  have u₀ : Upd s s₀ := by unfold Upd; simp only [s₀, State.setReg32, State.setReg]
  -- the four key bytes
  have step : ∀ (t : State) (m : Nat), Upd s t → t.gpr .rdi = K → t.gpr .rsi = BitVec.ofNat 64 L →
      t.gpr .r10 = BitVec.ofNat 64 ((4 * i + m) % L) →
      ∀ {Q : State → Prop}, (∀ t', (t'.gpr .r11).setWidth 32 = ((t.gpr .r11).setWidth 32 <<< 8) |||
        ((bytesAt s.mem K L).getD ((4 * i + m) % L) 0).zeroExtend 32 →
        t'.gpr .r10 = BitVec.ofNat 64 ((4 * i + (m + 1)) % L) →
        (∀ g, g ≠ .rax → g ≠ .r10 → g ≠ .r11 → t'.gpr g = t.gpr g) → Upd s t' → Q t') →
      WP isa keyByte t Q := by
    intro t m ht h0 h1 h10 Q k
    have kt : KeyIn t K L := E.key.of_eq (by rw [ht]) (by rw [ht])
    refine WP.mono (keyByte_run (Nat.mod_lt _ hL0) E.L64 kt h0 h1 h10) fun t' ⟨a, b, c, d⟩ => k t' ?_ ?_ c (d.trans ht)
    · rw [a, bytesAt_getD _ _ (Nat.mod_lt _ hL0), show t.mem = s.mem by rw [ht]]
    · rw [b, mod_succ _ _ hL0, Nat.add_assoc]
  have hlen : (bytesAt s.mem K L).length = L := by simp [bytesAt]
  apply WP.seq
  refine step s₀ 0 u₀ (by rw [g₀ _ (by decide), E.rdi]) (by rw [g₀ _ (by decide), E.rsi])
    (by rw [g₀ _ (by decide), E.r10]; rfl) fun t₁ a₁ b₁ c₁ d₁ => ?_
  apply WP.seq
  refine step t₁ 1 d₁ (by rw [c₁ _ (by decide) (by decide) (by decide), g₀ _ (by decide), E.rdi])
    (by rw [c₁ _ (by decide) (by decide) (by decide), g₀ _ (by decide), E.rsi]) b₁ fun t₂ a₂ b₂ c₂ d₂ => ?_
  apply WP.seq
  refine step t₂ 2 d₂ (by rw [c₂ _ (by decide) (by decide) (by decide), c₁ _ (by decide) (by decide) (by decide),
      g₀ _ (by decide), E.rdi])
    (by rw [c₂ _ (by decide) (by decide) (by decide), c₁ _ (by decide) (by decide) (by decide), g₀ _ (by decide),
      E.rsi]) b₂ fun t₃ a₃ b₃ c₃ d₃ => ?_
  apply WP.seq
  refine step t₃ 3 d₃ (by rw [c₃ _ (by decide) (by decide) (by decide), c₂ _ (by decide) (by decide) (by decide),
      c₁ _ (by decide) (by decide) (by decide), g₀ _ (by decide), E.rdi])
    (by rw [c₃ _ (by decide) (by decide) (by decide), c₂ _ (by decide) (by decide) (by decide),
      c₁ _ (by decide) (by decide) (by decide), g₀ _ (by decide), E.rsi]) b₃ fun t₄ a₄ b₄ c₄ d₄ => ?_
  -- the word
  have kw : (t₄.gpr .r11).setWidth 32 = keyWord (bytesAt s.mem K L) i := by
    rw [a₄, a₃, a₂, a₁, x11₀, keyWord_eq, hlen]
  have g₄ : ∀ g, g ≠ .rax → g ≠ .r10 → g ≠ .r11 → t₄.gpr g = s.gpr g := fun g h1 h2 h3 => by
    rw [c₄ g h1 h2 h3, c₃ g h1 h2 h3, c₂ g h1 h2 h3, c₁ g h1 h2 h3, g₀ g h3]
  have m₄ : t₄.mem = s.mem := by rw [d₄]
  have rw₄ : t₄.rd = s.rd ∧ t₄.wr = s.wr := ⟨by rw [d₄], by rw [d₄]⟩
  have ea₄ : t₄.ea { base := .rdx, index := some .r8, disp := Int.ofNat pOff } = S + BitVec.ofNat 64 (4096 + 4 * i) :=
    ea_idx t₄ _ _ _ _ _ (by rw [g₄ _ (by decide) (by decide) (by decide), E.rdx])
      (by rw [g₄ _ (by decide) (by decide) (by decide), E.r8])
  let P := s.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32
  let t₅ := t₄.setReg32 .rax P
  have e₅ : exec (.mov32 .rax (.mem { base := .rdx, index := some .r8, disp := Int.ofNat pOff })) t₄ = some t₅ := by
    rw [exec_mov32_mem (by rw [ea₄, rw₄.1, rw₄.2]; exact inRegions_append_right E.wrS), ea₄, m₄]
  obtain ⟨t₆, e₆, r₆, g₆, u₆⟩ := logic32_run t₅ .xor .rax .r11 (.inr rfl)
  have ea₆ : t₆.ea { base := .rdx, index := some .r8, disp := Int.ofNat pOff } = S + BitVec.ofNat 64 (4096 + 4 * i) := by
    rw [← ea₄]; simp only [State.ea, g₆ _ (show Reg.rdx ≠ Reg.rax by decide), g₆ _ (show Reg.r8 ≠ Reg.rax by decide),
      t₅, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rdx ≠ Reg.rax by decide),
      gpr_setReg_of_ne _ _ (show Reg.r8 ≠ Reg.rax by decide)]
  have wr₆ : t₆.wr = s.wr := by rw [u₆]; simp only [t₅, State.setReg32, wr_setReg]; exact rw₄.2
  let t₇ : State := { t₆ with mem := t₆.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i)) ((t₆.gpr .rax).setWidth 32) }
  have e₇ : exec (.store32 { base := .rdx, index := some .r8, disp := Int.ofNat pOff } .rax) t₆ = some t₇ := by
    rw [exec_store32 (by rw [ea₆, wr₆]; exact E.wrS), ea₆]
  obtain ⟨t₈, e₈, r₈, g₈, -, u₈⟩ := add_imm_run t₇ .r8 4
  obtain ⟨t₉, b₉, e₉, rb₉, z₉, g₉, u₉⟩ := cmp_run t₈ .r8 (.imm 72) (fun _ => by simp)
  refine WP.of_runBlock ⟨t₉, by
    rw [runBlock_cons, e₅, runStep_some, runBlock_cons, e₆, runStep_some, runBlock_cons, e₇, runStep_some,
      runBlock_cons, e₈, runStep_some, runBlock_cons, e₉, runStep_some, runBlock_nil], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hv : (t₆.gpr .rax).setWidth 32 = P ^^^ keyWord (bytesAt s.mem K L) i := by
      rw [r₆]
      simp only [reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, t₅, State.setReg32, gpr_setReg_self,
        gpr_setReg_of_ne _ _ (show Reg.r11 ≠ Reg.rax by decide), kw]
    rw [show t₉.mem = t₇.mem by rw [u₉, u₈]]
    show t₆.mem.writeW _ ((t₆.gpr .rax).setWidth 32) = _
    rw [hv,
      show t₆.mem = s.mem by rw [u₆]; simp only [t₅, State.setReg32, mem_setReg]; exact m₄]
  · rw [g₉, g₈ _ (by decide), show t₇.gpr = t₆.gpr from rfl, g₆ _ (by decide)]
    simp only [t₅, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r10 ≠ Reg.rax by decide)]
    rw [b₄, show 4 * i + (3 + 1) = 4 * (i + 1) by omega]
  · rw [g₉, r₈, show t₇.gpr = t₆.gpr from rfl, g₆ _ (by decide)]
    simp only [t₅, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r8 ≠ Reg.rax by decide)]
    rw [g₄ _ (by decide) (by decide) (by decide), E.r8]
    apply BitVec.eq_of_toNat_eq; simp; omega
  · have r8₈ : t₈.gpr .r8 = BitVec.ofNat 64 (4 * (i + 1)) := by
      rw [r₈, show t₇.gpr = t₆.gpr from rfl, g₆ _ (by decide)]
      simp only [t₅, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r8 ≠ Reg.rax by decide)]
      rw [g₄ _ (by decide) (by decide) (by decide), E.r8]
      apply BitVec.eq_of_toNat_eq; simp; omega
    simp only [readSrc, Option.some.injEq] at rb₉
    rw [z₉, r8₈, ← rb₉, show BitVec.signExtend 64 (72 : BitVec 32) = BitVec.ofNat 64 72 from rfl,
      ofNat_sub_beq (by omega) (by decide)]
  · intro g h1 h2 h3 h4
    rw [g₉, g₈ _ h2, show t₇.gpr = t₆.gpr from rfl, g₆ _ h1]
    simp only [t₅, State.setReg32, gpr_setReg_of_ne _ _ h1]
    exact g₄ g h1 h3 h4
  · exact UpdM.trans (UpdM.of_upd u₉) (UpdM.trans (UpdM.of_upd u₈) (UpdM.trans (UpdM.store _)
      (UpdM.trans (UpdM.of_upd u₆) (UpdM.trans (UpdM.of_upd (by unfold Upd; simp only [t₅, State.setReg32, State.setReg]))
        (UpdM.of_upd d₄)))))

/-- What the P-array loop needs, of the state it starts in. -/
structure KeyPEnv (S K : Addr) (L : Nat) (s : State) : Prop where
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : KeyIn s K L
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 L
  rdx : s.gpr .rdx = S
  wrS : SchedW S s
  fitS : S.toNat + 4168 ≤ 2 ^ 64
  keyS : ∀ c < L, ¬ (⟨S, 4168⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1

/-- After `i` entries. -/
structure KeyPInv (S K : Addr) (L : Nat) (s₀ : State) (i : Nat) (u : State) : Prop where
  le : i ≤ 18
  r10 : u.gpr .r10 = BitVec.ofNat 64 ((4 * i) % L)
  r8 : u.gpr .r8 = BitVec.ofNat 64 (4 * i)
  done : ∀ j < i, u.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    s₀.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * j)) 32 ^^^ keyWord (bytesAt s₀.mem K L) j
  frame : Frame [⟨S + BitVec.ofNat 64 4096, 4 * i⟩] s₀.mem u.mem
  gpr : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r10 → g ≠ .r11 → u.gpr g = s₀.gpr g
  eq : UpdM s₀ u

theorem keyP_step {S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv S K L s₀) {i : Nat} (hi : i < 18)
    {u : State} (I : KeyPInv S K L s₀ i u) :
    WP isa Impl.Blowfish.X86_64.keyWord u (fun u' => KeyPInv S K L s₀ (i + 1) u' ∧
      u'.zf = some (4 * (i + 1) == 72)) := by
  have fit := E.fitS
  have hrd : u.rd = s₀.rd := by rw [I.eq]
  have hwr : u.wr = s₀.wr := by rw [I.eq]
  have W : KeyWordEnv S K L i u := by
    refine ⟨hi, E.L0, E.L64, E.key.of_eq hrd hwr,
      (I.gpr _ (by decide) (by decide) (by decide) (by decide)).trans E.rdi,
      (I.gpr _ (by decide) (by decide) (by decide) (by decide)).trans E.rsi,
      (I.gpr _ (by decide) (by decide) (by decide) (by decide)).trans E.rdx, I.r10, I.r8, ?_⟩
    rw [hwr]; exact E.wrS _ _ (by omega)
  refine WP.mono (keyWord_run W) fun u' ⟨m', r10', r8', z', g', e'⟩ => ⟨?_, z'⟩
  have hT : u.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      s₀.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * i)) 32 :=
    I.frame.readW (r := ⟨S + BitVec.ofNat 64 (4096 + 4 * i), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint S (.inr (by omega)) (by omega) (by omega)) (by decide)
  have hB : bytesAt u.mem K L = bytesAt s₀.mem K L :=
    bytesAt_frame I.frame fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.keyS c hc (Offset.sub_base S (d := 4096) (n := 4 * i) (k := 4168) (by omega) _ hcon)
  refine ⟨by omega, r10', r8', fun j hj => ?_, ?_, fun g h1 h2 h3 h4 => (g' g h1 h2 h3 h4).trans (I.gpr g h1 h2 h3 h4),
    e'.trans I.eq⟩
  · rw [m', hT, hB]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep S (by omega) (by omega) (by omega)) (by decide)]
      exact I.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m']
    refine Frame.writeW (Frame.sub I.frame fun r hr => ⟨⟨S + BitVec.ofNat 64 4096, 4 * (i + 1)⟩,
      List.mem_singleton_self _, ?_⟩) (List.mem_singleton_self _) _
      (Offset.contains S (by omega) (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub S (by omega) (by omega)

theorem keyP_run {S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv S K L s₀) :
    WP isa keyP s₀ (KeyPInv S K L s₀ 18) := by
  rw [keyP]
  apply WP.seq
  let s₁ := (s₀.setReg32 .r10 0).setReg32 .r8 0
  refine WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil], ?_⟩
  have I₀ : KeyPInv S K L s₀ 0 s₁ := by
    refine ⟨by omega, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun g _ h2 h3 _ => ?_, ?_⟩
    · simp only [s₁, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r10 ≠ Reg.r8 by decide), gpr_setReg_self]
      rfl
    · simp only [s₁, State.setReg32, gpr_setReg_self]; rfl
    · simp only [s₁, State.setReg32, gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h3]
    · unfold UpdM; simp only [s₁, State.setReg32, State.setReg]
  refine WP.loop (M := isa) (fun m u => ∃ i, i < 18 ∧ m = 18 - i ∧ KeyPInv S K L s₀ i u)
    ?_ 18 s₁ ⟨0, by omega, rfl, I₀⟩
  intro m u ⟨i, hi, hm, I⟩
  refine WP.mono (keyP_step E hi I) fun u' ⟨I', z'⟩ => ?_
  have ev : isa.eval .ne u' = some (!(4 * (i + 1) == 72)) := by
    show u'.zf.map (!·) = _; rw [z']; rfl
  by_cases h : i + 1 = 18
  · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
  · right
    exact ⟨by rw [ev, show (4 * (i + 1) == 72) = false from by simp; omega]; rfl,
      18 - (i + 1), by omega, i + 1, by omega, rfl, I'⟩

end VG.Proof.Blowfish.X86_64
