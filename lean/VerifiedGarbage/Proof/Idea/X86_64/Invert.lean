import VerifiedGarbage.Proof.Idea.X86_64.Key
import VerifiedGarbage.Proof.Idea.Inverse

/-!
# IDEA decryption subkeys on x86-64

Each decryption subkey is a copy, the negation or the inverse of an
encryption subkey (`invertKey_getD`, `Impl.Idea.invOp`), computed into
`rdx` (`invWord_ok`; the inverse by a loop of fifteen steps of
`t := (t ⊙ t) ⊙ a`, `invLoop_ok`), placed in its 16 bits of `r10`
(`invPlace`), and stored a quadword at a time (`invQuad_ok`).
-/

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64 VG.Impl.Idea

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.rax, .rcx, .rdx, .r8, .r9, .r11]

theorem signExtend_fifteen : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide

theorem loadKey_run (z : Spec.Idea.Schedule) (r : Reg) {k : Nat} (hk : k < 52) (t : State)
    (hz : KeyOk z t) :
    ∃ t', runBlock isa (loadKey r k) t = some t' ∧ (t'.gpr r).setWidth 16 = z.getD k 0 ∧
      Keep [r] t t' := by
  unfold loadKey
  split
  · rename_i h
    have k₁ := hz.low k h
    refine ⟨t.setReg r (t.mem.readW (t.ea (at_ .rdi (2 * k))) 64), ?_, ?_, ?_⟩
    · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, isa, k₁.1,
        ↓reduceIte, Option.map_some]
    · rw [RegUpd.gpr_setReg_self, k₁.2]
    · refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
      simp only [List.mem_singleton] at hq
      exact RegUpd.gpr_setReg_of_ne _ _ hq
  · rename_i h
    have k₁ := hz.low 48 (by decide)
    simp only [Nat.reduceMul] at k₁
    have l := hz.last (k - 48) (by omega)
    rw [show 48 + (k - 48) = k by omega] at l
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc, State.load64, isa,
      k₁.1, ↓reduceIte, Option.map_some, RegUpd.gpr_setReg_self, show 1 ≤ 16 * (k - 48) by omega,
      show 16 * (k - 48) ≤ 63 by omega, and_self,
      Option.some.injEq, exists_eq_left', l, true_and]
    refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
    simp only [List.mem_singleton] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq, ite_false]

theorem invStep_run (t : State) :
    ∃ t', runBlock isa invStep t = some t' ∧
      t'.gpr .r9 = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .r9).setWidth 16) ((t.gpr .r9).setWidth 16))
        ((t.gpr .r8).setWidth 16)).setWidth 64 ∧
      t'.gpr .rcx = t.gpr .rcx - 1 ∧ t'.zf = some (t.gpr .rcx - 1 == 0) ∧
      Keep [.rax, .rcx, .rdx, .r9] t t' := by
  have h₁ : runBlock isa [.mov .rax (.reg .r9), .mov .rdx (.reg .r9)] t =
      some ((t.setReg .rax (t.gpr .r9)).setReg .rdx (t.gpr .r9)) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
  obtain ⟨t₂, h₂, v₂, e₂⟩ := mul_run ((t.setReg .rax (t.gpr .r9)).setReg .rdx (t.gpr .r9))
  have h₃ : runBlock isa [.mov .rax (.reg .rdx), .mov .rdx (.reg .r8)] t₂ =
      some ((t₂.setReg .rax (t₂.gpr .rdx)).setReg .rdx (t₂.gpr .r8)) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
  obtain ⟨t₄, h₄, v₄, e₄⟩ := mul_run ((t₂.setReg .rax (t₂.gpr .rdx)).setReg .rdx (t₂.gpr .r8))
  obtain ⟨t₅, h₅, r9₅, rcx₅, zf₅, e₅⟩ : ∃ t₅, runBlock isa [.mov .r9 (.reg .rdx), .alu .sub .rcx (.imm 1)] t₄ =
      some t₅ ∧ t₅.gpr .r9 = t₄.gpr .rdx ∧ t₅.gpr .rcx = t₄.gpr .rcx - 1 ∧
      t₅.zf = some (t₄.gpr .rcx - 1 == 0) ∧ Keep [.rcx, .r9] t₄ t₅ := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
      Option.map_some, Option.bind_some, signExtend_one, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      RegUpd.zf_setReg, RegUpd.zf_arithFlags, reduceCtorEq, ↓reduceIte, Option.some.injEq,
      exists_eq_left', true_and]
    refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]
  have r8₂ : t₂.gpr .r8 = t.gpr .r8 := by
    rw [e₂.reg .r8 (by decide)]; rfl
  have rcx₄ : t₄.gpr .rcx = t.gpr .rcx := by
    rw [e₄.reg .rcx (by decide)]
    show t₂.gpr .rcx = _
    rw [e₂.reg .rcx (by decide)]; rfl
  refine ⟨t₅, run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅, ?_, ?_, ?_, ?_⟩
  · rw [r9₅, v₄, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_self, v₂, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_self, setWidth_setWidth16, r8₂]
  · rw [rcx₅, rcx₄]
  · rw [zf₅, rcx₄]
  · refine ⟨fun q hq => ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [e₅.reg q (by simp [hq.2.1, hq.2.2.2]), e₄.reg q (by simp [hq.1, hq.2.2.1]),
        RegUpd.gpr_setReg_of_ne _ _ hq.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hq.1,
        e₂.reg q (by simp [hq.1, hq.2.2.1]), RegUpd.gpr_setReg_of_ne _ _ hq.2.2.1,
        RegUpd.gpr_setReg_of_ne _ _ hq.1]
    · rw [e₅.mem, e₄.mem]; exact e₂.mem
    · rw [e₅.rd, e₄.rd]; exact e₂.rd
    · rw [e₅.wr, e₄.wr]; exact e₂.wr

/-- `c` steps remain: `r9` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  rcx : t.gpr .rcx = BitVec.ofNat 64 c
  r8 : (t.gpr .r8).setWidth 16 = a
  r9 : (t.gpr .r9).setWidth 16 = chain a (15 - c)
  keep : Keep [.rax, .rcx, .rdx, .r9] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) .ne) t (fun t' =>
      t'.gpr .r9 = (Spec.Idea.inv a).setWidth 64 ∧ Keep [.rax, .rcx, .rdx, .r9] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  obtain ⟨t', h', r9', rcx', zf', e'⟩ := invStep_run t
  refine WP.of_runBlock ⟨t', h', ?_⟩
  have hv : t'.gpr .r9 = (chain a (15 - c + 1)).setWidth 64 := by
    rw [r9', hi.r9, hi.r8]; rfl
  have hc : t.gpr .rcx - 1 = BitVec.ofNat 64 (c - 1) := by
    rw [hi.rcx]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  have keep' : Keep [.rax, .rcx, .rdx, .r9] t₀ t' := hi.keep.trans e'
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨?_, ?_, keep'⟩
    · simp only [eval, zf', hc]; rfl
    · rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨?_, c - 1, by omega, by omega, by omega, rcx'.trans hc, ?_, ?_, keep'⟩
    · simp only [eval, zf', hc, Option.map_some, Option.some.injEq]
      have h : (BitVec.ofNat 64 (c - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega
      rw [h]; rfl
    · rw [e'.reg .r8 (by decide)]; exact hi.r8
    · rw [hv, setWidth_setWidth16, show 15 - c + 1 = 15 - (c - 1) by omega]

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : KeyOk z t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .rdx = ((Spec.Idea.invertKey z).getD n 0).setWidth 64 ∧ Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  have hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .rdx hk t hz
    refine WP.of_runBlock ⟨(arithFlags t₁ (t₁.gpr .rdx &&& 65535) false false).setReg .rdx
      (t₁.gpr .rdx &&& 65535), run_append h₁ (by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
          Option.bind_some, signExtend_mask]), ?_, ?_⟩
    · rw [RegUpd.gpr_setReg_self, mask_setWidth, v₁]; rfl
    · refine (e₁.mono (by decide)).trans ⟨fun q hq => ?_, rfl, rfl, rfl⟩
      rw [RegUpd.gpr_setReg_of_ne _ _ (by intro h; subst h; exact hq (by decide))]; rfl
  | neg =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .r11 hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ : ∃ t₂, runBlock isa [.mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .r11),
        .alu .and .rdx (.imm 0xffff)] t₁ = some t₂ ∧
        t₂.gpr .rdx = (0 - t₁.gpr .r11) &&& 65535 ∧ Keep [.rdx] t₁ t₂ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, isa,
        Option.map_some, Option.bind_some, signExtend_mask, State.setReg32, RegUpd.gpr_setReg,
        reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
      refine ⟨by rfl, keep_reg_of (fun q hq => ?_) rfl rfl rfl⟩
      simp only [List.mem_singleton] at hq
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, ?_⟩
    · rw [v₂, neg_mask, v₁]; rfl
    · exact (e₁.mono (by decide)).trans (e₂.mono (by decide))
  | inv =>
    apply WP.seq
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .r8 hk t hz
    obtain ⟨t₂, h₂, r8₂, r9₂, rcx₂, e₂⟩ : ∃ t₂, runBlock isa [.mov .r9 (.reg .r8), .mov32 .rcx (.imm 15)] t₁ =
        some t₂ ∧ t₂.gpr .r8 = t₁.gpr .r8 ∧ t₂.gpr .r9 = t₁.gpr .r8 ∧ t₂.gpr .rcx = 15 ∧
        Keep [.r9, .rcx] t₁ t₂ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, isa,
        Option.map_some, State.setReg32, RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte,
        Option.some.injEq, exists_eq_left', true_and]
      refine ⟨by rfl, keep_reg_of (fun q hq => ?_) rfl rfl rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp only [RegUpd.gpr_setReg, hq.1, hq.2, ite_false]
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
    apply WP.seq
    refine WP.mono (invLoop_ok (z.getD k 0) t₂ 15 t₂ ⟨by decide, by decide, rcx₂, by rw [r8₂, v₁],
      by rw [r9₂, v₁]; rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩) fun t₃ ⟨r9₃, e₃⟩ => ?_
    refine WP.of_runBlock ⟨t₃.setReg .rdx (t₃.gpr .r9), by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some], ?_, ?_⟩
    · rw [RegUpd.gpr_setReg_self, r9₃]; rfl
    · refine (e₁.mono (by decide)).trans ((e₂.mono (by decide)).trans ((e₃.mono (by decide)).trans
        ⟨fun q hq => ?_, rfl, rfl, rfl⟩))
      exact RegUpd.gpr_setReg_of_ne _ _ (by intro h; subst h; exact hq (by decide))

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- `r10` holds the first `i` decryption subkeys of quadword `q`, and zeros above. -/
def Acc (z : Spec.Idea.Schedule) (q i : Nat) (t : State) : Prop :=
  ∀ p < 64, (t.gpr .r10).getLsbD p =
    if p < 16 * i then (dk z (4 * q + p / 16)).getLsbD (p % 16) else false

theorem invPlace_run (z : Spec.Idea.Schedule) (q i : Nat) (hi : i < 4) (t : State)
    (hrdx : t.gpr .rdx = (dk z (4 * q + i)).setWidth 64) (hacc : i = 0 ∨ Acc z q i t) :
    ∃ t', runBlock isa (invPlace (4 * q + i)) t = some t' ∧ Acc z q (i + 1) t' ∧
      Keep [.rdx, .r10] t t' := by
  unfold invPlace
  split
  · rename_i h
    have hi0 : i = 0 := by omega
    subst hi0
    refine ⟨t.setReg .r10 (t.gpr .rdx), by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some], ?_, ?_⟩
    · intro p hp
      rw [RegUpd.gpr_setReg_self, hrdx, BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and,
        Nat.add_zero]
      by_cases hp16 : p < 16
      · rw [ite_eq_left (by omega), Nat.div_eq_of_lt hp16, Nat.mod_eq_of_lt hp16, Nat.add_zero]
      · rw [ite_eq_right (by omega)]; exact BitVec.getLsbD_of_ge _ _ (by omega)
    · refine keep_reg_of (fun r hr => ?_) rfl rfl rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact RegUpd.gpr_setReg_of_ne _ _ hr.2
  · rename_i h
    have hi0 : i ≠ 0 := by omega
    have hacc' := hacc.resolve_left hi0
    have hm : (4 * q + i) % 4 = i := by omega
    rw [hm]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc, isa,
      Option.bind_some, show 1 ≤ 16 * i by omega, show 16 * i ≤ 63 by omega, and_self, ↓reduceIte,
      RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, keep_reg_of (fun r hr => ?_) rfl rfl rfl⟩
    · rw [RegUpd.gpr_setReg_self, BitVec.getLsbD_or, hacc' p hp, hrdx, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth]
      by_cases h1 : p < 16 * i
      · simp [h1, show p < 16 * (i + 1) by omega]
      · by_cases h2 : p < 16 * (i + 1)
        · simp [h1, h2, hp, show p - 16 * i < 64 by omega, show 4 * q + p / 16 = 4 * q + i by omega,
            show p % 16 = p - 16 * i by omega]
        · simp only [h1, h2, ↓reduceIte, Bool.false_or]
          rw [BitVec.getLsbD_of_ge (dk z (4 * q + i)) _ (by omega)]
          simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- The registers computing a quadword of decryption subkeys writes. -/
abbrev quadWrites : List Reg := [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11]

theorem quadWord_ok (z : Spec.Idea.Schedule) (q i : Nat) (hq : q < 13) (hi : i < 4) (t : State)
    (hz : KeyOk z t) (hacc : i = 0 ∨ Acc z q i t) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t', Acc z q (i + 1) t' → Keep quadWrites t t' → WP isa rest t' Q) :
    WP isa (.seq (invWord (4 * q + i)) (.seq (.block (invPlace (4 * q + i))) rest)) t Q := by
  apply WP.seq
  refine WP.mono (invWord_ok z (by omega) t hz) fun t₁ ⟨v₁, e₁⟩ => ?_
  apply WP.seq
  have hacc₁ : i = 0 ∨ Acc z q i t₁ := by
    rcases hacc with h | h
    · exact Or.inl h
    · right; intro p hp; rw [e₁.reg .r10 (by decide)]; exact h p hp
  obtain ⟨t₂, h₂, a₂, e₂⟩ := invPlace_run z q i hi t₁ v₁ hacc₁
  exact WP.of_runBlock ⟨t₂, h₂, hrest t₂ a₂ ((e₁.mono (by decide)).trans (e₂.mono (by decide)))⟩

/-- What `vg_idea_invert_key` needs of its state: the encryption subkeys (104
bytes at `rdi`) readable, the decryption subkeys (104 bytes at `rsi`)
writable, apart. -/
structure InvPre (s : State) : Prop where
  sched : ⟨s.gpr .rdi, 104⟩ ∈ s.rd ++ s.wr
  out : ⟨s.gpr .rsi, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .rdi, 104⟩ : Region).Disjoint ⟨s.gpr .rsi, 104⟩

/-- After `q` quadwords of decryption subkeys. -/
structure QInv (s₀ : State) (q : Nat) (t : State) : Prop where
  rdi : t.gpr .rdi = s₀.gpr .rdi
  rsi : t.gpr .rsi = s₀.gpr .rsi
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  regs : ∀ r ∈ [Reg.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr .rsi, 8 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 64, (t.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64).getLsbD p =
    (dk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)) (4 * i + p / 16)).getLsbD (p % 16)

theorem QInv.keyOk {s₀ t : State} {q : Nat} (hp : InvPre s₀) (hi : QInv s₀ q t) (hq : q ≤ 13) :
    KeyOk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)) t := by
  have h := keyOk_of t (by rw [hi.rdi, hi.rd, hi.wr]; exact hp.sched)
  rwa [hi.rdi, scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep.sub_right (Region.sub_prefix (by omega))) (by decide))] at h

theorem invQuad_ok (s₀ : State) (hp : InvPre s₀) (q : Nat) (hq : q < 13) (t : State)
    (hi : QInv s₀ q t) : WP isa (invQuad q) t (QInv s₀ (q + 1)) := by
  have hz := hi.keyOk hp (by omega)
  simp only [invQuad, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldr_cons, List.foldr_nil]
  refine quadWord_ok _ q 0 hq (by decide) t hz (Or.inl rfl) fun t₁ a₁ e₁ => ?_
  refine quadWord_ok _ q 1 hq (by decide) t₁ (hz.keep e₁ (by decide)) (Or.inr a₁) fun t₂ a₂ e₂ => ?_
  refine quadWord_ok _ q 2 hq (by decide) t₂ ((hz.keep e₁ (by decide)).keep e₂ (by decide)) (Or.inr a₂)
    fun t₃ a₃ e₃ => ?_
  refine quadWord_ok _ q 3 hq (by decide) t₃
    (((hz.keep e₁ (by decide)).keep e₂ (by decide)).keep e₃ (by decide)) (Or.inr a₃)
    fun t₄ a₄ e₄ => ?_
  have e := e₁.trans (e₂.trans (e₃.trans e₄))
  have hw : InRegions t₄.wr (t₄.ea (at_ .rsi (8 * q))) 8 := by
    rw [ea_at, e.reg .rsi (by decide), e.wr, hi.wr, hi.rsi]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega) (by omega)⟩
  have ea₄ : t₄.ea (at_ .rsi (8 * q)) = s₀.gpr .rsi + BitVec.ofNat 64 (8 * q) := by
    rw [ea_at, e.reg .rsi (by decide), hi.rsi]
  refine WP.of_runBlock ⟨{ t₄ with mem := t₄.mem.writeW (t₄.ea (at_ .rsi (8 * q))) (t₄.gpr .r10) },
    by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, isa, hw, ↓reduceIte],
    ?_⟩
  have sub : ∀ r ∈ [Reg.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], r ∉ quadWrites := by decide
  refine ⟨(e.reg .rdi (by decide)).trans hi.rdi, (e.reg .rsi (by decide)).trans hi.rsi,
    e.rd.trans hi.rd, e.wr.trans hi.wr, fun r hr => (e.reg r (sub r hr)).trans (hi.regs r hr), ?_, ?_⟩
  · show Frame _ s₀.mem (t₄.mem.writeW _ _)
    rw [e.mem, ea₄]
    refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)
  · intro i hiq p hp64
    show ((t₄.mem.writeW _ _).readW _ 64).getLsbD p = _
    rw [e.mem, ea₄]
    by_cases he : i = q
    · subst he
      rw [Mem.readW_writeW_self64, a₄ p hp64, ite_eq_left (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hi.words i (by omega) p hp64

/-- Quadwords `q … q + n - 1`. -/
def quads (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun q rest => .seq (invQuad q) rest) (.block [])

theorem quads_ok (s₀ : State) (hp : InvPre s₀) :
    ∀ n q, q + n = 13 → ∀ t, QInv s₀ q t → WP isa (quads q n) t (QInv s₀ 13)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [quads, List.range'_succ, List.foldr_cons]
    apply WP.seq
    exact WP.mono (invQuad_ok s₀ hp q (by omega) t hi) fun t₁ h₁ =>
      quads_ok s₀ hp n (q + 1) (by omega) t₁ h₁

theorem invertKey_eq : invertKey = quads 0 13 := rfl

/-- `vg_idea_invert_key` on x86-64. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 104⟩
    let out : Region := ⟨s.gpr .rsi, 104⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [out] ∧ sched.Disjoint out ∧ ret.Disjoint out
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .rsi) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem (s.gpr .rdi))
  pub := PublicRegs [.rdi, .rsi]

theorem invert_correct (s : State) (hs : invertContract.pre s) :
    ∃ t s', Exec isa invertKey s t s' ∧ abiPreserved s s' ∧ invertContract.post s s' := by
  obtain ⟨hrd, hwr, hsep, hret⟩ := hs
  have hp : InvPre s := ⟨by rw [hrd]; simp, by rw [hwr]; simp, hsep⟩
  obtain ⟨tr, s', he, hi⟩ := quads_ok s hp 13 0 rfl s ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl,
    Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  rw [← invertKey_eq] at he
  refine ⟨tr, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hi.regs _ (by decide)
  · exact hi.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact hret) (by decide)
  · show Spec.Idea.scheduleAt s'.mem (s.gpr .rsi) = _
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [scheduleAt_getLsbD _ _ hn hb, hi.words (n / 4) (by omega) _ (by omega),
      show 4 * (n / 4) + (16 * (n % 4) + b) / 16 = n by omega,
      show (16 * (n % 4) + b) % 16 = b by omega]

def invertSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 104⟩]

theorem invertKey_verified : Verified target invertKey (Spec.Idea.invertKeyContract abi) := by
  refine Verified.of_correct invert_correct (invertKey_constantTime _) ?_
  sig_implies [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost, abi,
    argRegs, invertContract, publicRegs_two] [invertSat] using invertSat

end VG.Proof.Idea.X86_64
