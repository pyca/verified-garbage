import VerifiedGarbage.Proof.X25519.X86_64.Mem
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Spec

/-!
# X25519 on x86-64, inversion by divsteps: packed divsteps

A batch's divsteps are the short Weierstrass curves' packed chunks
(`Proof/Weierstrass/X86_64/InvPacked.lean`, whose proofs these repeat for
this code's copy): a packed step's block computes `Proof/Divstep/PackedDef.lean`'s
`pstep` (`pkStep_ok`), a chunk's steps its `psteps` (`pkSteps_ok`), and a
chunk (`pkChunk_ok`) starts the rows from the low words of `f` and `g` at
`dsT`, runs its steps, takes the matrix from the rows (`pkExt_ok`), updates
the low words by it (`pkLow_ok`) and multiplies the batch's matrix by it
(`pkComp_ok`): `pkChunkV`, for any words. That the four chunks are 59
divsteps is the theory of divsteps (`Divstep/Sound.lean`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.Divstep (pstep)

theorem pk_ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) {x y : α} : (if c then x else y) = x :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

theorem pk_ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {x y : α} : (if c then x else y) = y :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

theorem pk_word_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 _ _ _

/-! ## Loads and stores -/

/-- The registers but `rs` and the regions are unchanged (memory may change). -/
structure PKeep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem PKeep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : PKeep rs s₁ s₂) (h₂ : PKeep rs s₂ s₃) :
    PKeep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem PKeep.mono {rs rs' : List Reg} {s s' : State} (h : PKeep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    PKeep rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

theorem Keeps.pk {rs : List Reg} {s s' : State} (h : Keeps rs s s') : PKeep rs s s' := ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem Scr.of_pk {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base) (h : PKeep rs s s')
    (hr : .rdi ∉ rs) : Scr s' base :=
  ⟨(h.gpr _ hr).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem pk_store {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) (v : BitVec 64) :
    s.store64 (s.ea (sc d)) v = some { s with mem := s.mem.writeW (off base d) v } := by
  rw [ea_sc, hs.rdi, State.store64, ite_eq_left ⟨_, hs.wr, contains_sc hd⟩]

/-- `r = [d]`. -/
theorem pkMov_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat} (hd : d + 8 ≤ 4096) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun s' => s'.gpr r = word s.mem base d ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, hq, ite_false]

/-- `[d] = r`. -/
theorem pkStore_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat} (hd : d + 8 ≤ 4096) :
    WP isa (.block [.store (sc d) r]) s fun s' =>
      s'.mem = s.mem.writeW (off base d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ PKeep [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, pk_store hs hd, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, ⟨fun _ _ => rfl, rfl, rfl⟩⟩

theorem pk_sextm2 : (-2 : BitVec 32).signExtend 64 = -2 := by decide
theorem pk_sext16k : (16384 : BitVec 32).signExtend 64 = 16384 := by decide
theorem pk_sext7fff : (0x7fff : BitVec 32).signExtend 64 = 0x7fff := by decide

theorem pk_zf (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).zf = c := rfl

/-- `rax` after `mul`: the low word of the product. -/
theorem pk_mul_lo (a b : BitVec 64) : BitVec.ofNat 64 (a.toNat * b.toNat) = a * b := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_mul]

/-- The registers a chunk's steps write. -/
abbrev pkRegs : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r13]

/-! ## A step -/

/-- A packed step's block, for each kind of step. -/
theorem pkStep_ok (s : State) {j : Nat} (hj : j ≤ 62) {g t : Reg}
    (hg : g = .r13 ∧ t = .rax ∨ g = .rax ∧ t = .r13) :
    WP isa (.block (pkStep j g t)) s fun s' =>
      (s'.gpr .rbx, s'.gpr .r8, s'.gpr t) = pstep j (s.gpr .rbx, s.gpr .r8, s.gpr g) ∧ Keeps pkRegs s s' := by
  have h63 : 1 ≤ 63 - j ∧ 63 - j ≤ 63 := ⟨by omega, by omega⟩
  obtain ⟨E, hE⟩ : ∃ E, s.gpr .rbx = E := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, s.gpr .r8 = F := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, s.gpr g = G := ⟨_, rfl⟩
  rw [hE, hF, hG]
  unfold pstep
  simp only
  by_cases hsw : 2 ^ 64 ≤ (G <<< (63 - j)).toNat + E.toNat
  · have hz : (G <<< (63 - j) == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h; rw [h] at hsw; have := E.isLt; simp at hsw; omega
    rw [pk_ite_t hsw]
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · drun [pkStep, h63, hE, hF, hG, hsw, hz, pk_zf, pk_sextm2, RegUpd.cf_setFlags, decide_true]
      refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, h5, h6, h7,
        ↓reduceIte]
  · rw [pk_ite_f hsw]
    by_cases hz0 : G <<< (63 - j) = 0
    · have hz : (G <<< (63 - j) == 0) = true := by rw [hz0]; rfl
      rw [pk_ite_t hz0]
      rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · drun [pkStep, h63, hE, hF, hG, hsw, hz, pk_zf, pk_sextm2, RegUpd.cf_setFlags, decide_false]
        refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, h5, h6, h7,
          ↓reduceIte]
    · have hz : (G <<< (63 - j) == 0) = false := by rw [beq_eq_false_iff_ne]; exact hz0
      rw [pk_ite_f hz0]
      rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · drun [pkStep, h63, hE, hF, hG, hsw, hz, pk_zf, pk_sextm2, RegUpd.cf_setFlags, decide_false]
        refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, h5, h6, h7,
          ↓reduceIte]

theorem pkReg_cases (j : Nat) :
    pkReg j = .r13 ∧ pkReg (j + 1) = .rax ∨ pkReg j = .rax ∧ pkReg (j + 1) = .r13 := by
  unfold pkReg
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · left; exact ⟨pk_ite_t h, pk_ite_f (by omega)⟩
  · right; exact ⟨pk_ite_f (by omega), pk_ite_t (by omega)⟩

/-- Steps `0 … n - 1`, the `g` row in `pkReg n`. -/
theorem pkStepsList_ok (s : State) : ∀ n ≤ 63,
    WP isa (.block ((List.range n).flatMap fun j => pkStep j (pkReg j) (pkReg (j + 1)))) s fun s' =>
      (s'.gpr .rbx, s'.gpr .r8, s'.gpr (pkReg n)) = Divstep.psteps n (s.gpr .rbx, s.gpr .r8, s.gpr .r13) ∧
        Keeps pkRegs s s'
  | 0, _ => WP.block_nil_iff.mpr ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (pkStepsList_ok s n (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
    refine WP.mono (pkStep_ok s₁ (j := n) (by omega) (pkReg_cases n)) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    rw [e₂, Divstep.psteps, ← e₁]

/-- A chunk's `n ≤ 15` steps, the `g` row back in `r13`. -/
theorem pkSteps_ok (s : State) {n : Nat} (hn : n ≤ 15) :
    WP isa (.block (pkSteps n)) s fun s' =>
      (s'.gpr .rbx, s'.gpr .r8, s'.gpr .r13) = Divstep.psteps n (s.gpr .rbx, s.gpr .r8, s.gpr .r13) ∧
        Keeps pkRegs s s' := by
  rw [pkSteps, WP.block_append_iff]
  refine WP.mono (pkStepsList_ok s n (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [pk_ite_f (by omega)]
    have hg : pkReg n = .r13 := pk_ite_t h
    rw [hg] at e₁
    exact WP.block_nil_iff.mpr ⟨e₁, k₁⟩
  · rw [pk_ite_t h]
    have hg : pkReg n = .rax := pk_ite_f (by omega)
    rw [hg] at e₁
    drun
    refine ⟨e₁, k₁.trans ?_⟩
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.2.2.2.2.2.2, ↓reduceIte]

/-! ## A chunk's rows and matrix -/

/-- A row's start. -/
theorem pkSetRow_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t + 8 ≤ 4096)
    (r : Reg) (hr : r ∉ [Reg.rax]) (c : BitVec 64) :
    WP isa (.block (pkSetRow r t c)) s fun s' =>
      s'.gpr r = (word s.mem base t &&& 0x7fff) + c ∧ Keeps [.rax, r] s s' := by
  have h1 : ¬ r = .rax := fun h => hr (by simp [h])
  have h2 : ¬ Reg.rax = r := fun h => h1 h.symm
  drun [pkSetRow, load_sc hs ht, pk_sext7fff, h1, h2, RegUpd.gpr_setReg_self]
  refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2, ↓reduceIte]

/-- The rows' start. -/
theorem pkSet_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t + 16 ≤ 4096) :
    WP isa (.block (pkSet t)) s fun s' =>
      s'.gpr .r8 = (word s.mem base t &&& 0x7fff) + 2 ^ 31 ∧
      s'.gpr .r13 = (word s.mem base (t + 8) &&& 0x7fff) + 2 ^ 47 ∧ Keeps [.rax, .r8, .r13] s s' := by
  rw [pkSet, WP.block_append_iff]
  refine WP.mono (pkSetRow_ok hs (t := t) (by omega) .r8 (by decide) _) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (pkSetRow_ok (hs.of_keeps k₁ (by decide)) (t := t + 8) (by omega) .r13 (by decide) _)
    fun s₂ ⟨e₂, k₂⟩ => ⟨?_, by rw [e₂, k₁.2.1], (k₁.mono (by decide)).trans (k₂.mono (by decide))⟩
  rw [k₂.1 _ (by decide), e₁]

/-- The matrix from the rows. -/
theorem pkExt_ok (s : State) :
    WP isa (.block pkExt) s fun s' =>
      s'.gpr .r8 = Divstep.pextLo (s.gpr .r8) ∧ s'.gpr .rcx = Divstep.pextHi (s.gpr .r8) ∧
      s'.gpr .r13 = Divstep.pextLo (s.gpr .r13) ∧ s'.gpr .rbp = Divstep.pextHi (s.gpr .r13) ∧
      Keeps [.rcx, .rbp, .r8, .r13] s s' := by
  drun [pkExt, pkExtC, Divstep.pextLo, Divstep.pextHi, Divstep.pextC, pk_sext16k]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
    ↓reduceIte]

/-! ## A chunk's low words and matrix -/

/-- `rax = [d] r`. -/
theorem pkLdMul_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096)
    (r : Reg) (hr : r ∉ [Reg.rax, .rdx]) :
    WP isa (.block (pkLdMul d r)) s fun s' => s'.gpr .rax = word s.mem base d * s.gpr r ∧ Keeps [.rax, .rdx] s s' := by
  have h1 : ¬ r = .rax := fun h => hr (by simp [h])
  drun [pkLdMul, load_sc hs hd, pk_mul_lo, h1]
  refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq.1, hq.2, ↓reduceIte]

/-- `[e] = (rax + [d]) >> n`. -/
theorem pkAddShr_ok {s : State} {base : Addr} (hs : Scr s base) {d n e : Nat}
    (hd : d + 8 ≤ 4096) (he : e + 8 ≤ 4096) (hn : 1 ≤ n ∧ n ≤ 63) :
    WP isa (.block (pkAddShr d n e)) s fun s' =>
      s'.mem = s.mem.writeW (off base e) ((s.gpr .rax + word s.mem base d) >>> n) ∧ PKeep [.rax] s s' := by
  rw [pkAddShr, WP.block_append_iff]
  have h : WP isa (.block [.alu .add .rax (.mem (sc d)), .shift .shr .rax n]) s fun s₁ =>
      s₁.gpr .rax = (s.gpr .rax + word s.mem base d) >>> n ∧ Keeps [.rax] s s₁ := by
    drun [load_sc hs hd, hn]
    refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hq, ↓reduceIte]
  refine WP.mono h fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (pkStore_ok (hs.of_keeps k₁ (by decide)) .rax he) fun s₂ ⟨m₂, _, k₂⟩ =>
    ⟨by rw [m₂, e₁, k₁.2.1], (Keeps.pk k₁).trans (k₂.mono (by simp))⟩

theorem pk_apart (m : Mem) (base : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hn : d + 8 ≤ 4096) (hn' : e + 8 ≤ 4096) : word (m.writeW (off base e) v) base d = word m base d :=
  (writeW_outside m base v (by omega)).word h (by omega)

/-- A chunk's update of the low words at `[t]`, `[t + 8]`. -/
theorem pkLow_ok {s : State} {base : Addr} (hs : Scr s base) {n t : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (ht : t + 24 ≤ 4096) :
    WP isa (.block (pkLow n t)) s fun s' =>
      word s'.mem base t = (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n ∧
      word s'.mem base (t + 8) =
        (word s.mem base (t + 8) * s.gpr .rbp + word s.mem base t * s.gpr .r13) >>> n ∧
      PKeep [.rax, .rdx] s s' ∧ Outside base t 24 s.mem s'.mem := by
  simp only [pkLow, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pkLdMul_ok hs (d := t) (by omega) .r8 (by decide)) fun s₁ ⟨a₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkStore_ok hs₁ .rax (d := t + 16) (by omega)) fun s₂ ⟨m₂, g₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_pk k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkLdMul_ok hs₂ (d := t + 8) (by omega) .rcx (by decide)) fun s₃ ⟨a₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkAddShr_ok hs₃ (d := t + 16) (e := t + 16) (by omega) (by omega) hn) fun s₄ ⟨m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_pk k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkLdMul_ok hs₄ (d := t) (by omega) .r13 (by decide)) fun s₅ ⟨a₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkStore_ok hs₅ .rax (d := t) (by omega)) fun s₆ ⟨m₆, g₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_pk k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkLdMul_ok hs₆ (d := t + 8) (by omega) .rbp (by decide)) fun s₇ ⟨a₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkAddShr_ok hs₇ (d := t) (e := t + 8) (by omega) (by omega) hn) fun s₈ ⟨m₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_pk k₈ (by decide)
  rw [show [Instr.mov .rax (.mem (sc (t + 16))), .store (sc t) .rax] =
    [Instr.mov .rax (.mem (sc (t + 16)))] ++ [.store (sc t) .rax] from rfl, WP.block_append_iff]
  refine WP.mono (pkMov_ok hs₈ .rax (d := t + 16) (by omega)) fun s₉ ⟨a₉, k₉⟩ => ?_
  refine WP.mono (pkStore_ok (hs₈.of_keeps k₉ (by decide)) .rax (d := t) (by omega)) fun u ⟨mu, _, ku⟩ => ?_
  have R2 : ∀ r ∉ [Reg.rax, .rdx], s₂.gpr r = s.gpr r := fun r hr => by rw [g₂, k₁.1 r hr]
  have R4 : ∀ r ∉ [Reg.rax, .rdx], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; simp [h])), k₃.1 r hr, R2 r hr]
  have R6 : ∀ r ∉ [Reg.rax, .rdx], s₆.gpr r = s.gpr r := fun r hr => by rw [g₆, k₅.1 r hr, R4 r hr]
  have ap : ∀ (m : Mem) (d e : Nat) (v : BitVec 64), d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ 4096 → e + 8 ≤ 4096 →
      word (m.writeW (off base e) v) base d = word m base d := fun m d e v h hd he =>
    pk_apart m base v h hd he
  have ou : ∀ (m : Mem) (e : Nat) (v : BitVec 64), t ≤ e → e + 8 ≤ t + 24 →
      Outside base t 24 m (m.writeW (off base e) v) := fun m e v h1 h2 x hx =>
    writeW_outside m base v (by omega) x (by omega)
  have w2_0 : word s₂.mem base t = word s.mem base t := by rw [m₂, ap _ _ _ _ (by omega) (by omega) (by omega), k₁.2.1]
  have w2_8 : word s₂.mem base (t + 8) = word s.mem base (t + 8) := by
    rw [m₂, ap _ _ _ _ (by omega) (by omega) (by omega), k₁.2.1]
  have w2_16 : word s₂.mem base (t + 16) = word s.mem base t * s.gpr .r8 := by rw [m₂, pk_word_self, a₁]
  have hF : (s₃.gpr .rax + word s₃.mem base (t + 16)) >>> n =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [a₃, k₃.2.1, w2_8, w2_16, R2 .rcx (by decide)]
  have w4_0 : word s₄.mem base t = word s.mem base t := by
    rw [m₄, ap _ _ _ _ (by omega) (by omega) (by omega), k₃.2.1, w2_0]
  have w4_8 : word s₄.mem base (t + 8) = word s.mem base (t + 8) := by
    rw [m₄, ap _ _ _ _ (by omega) (by omega) (by omega), k₃.2.1, w2_8]
  have w4_16 : word s₄.mem base (t + 16) =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [m₄, pk_word_self, hF]
  have w6_0 : word s₆.mem base t = word s.mem base t * s.gpr .r13 := by
    rw [m₆, pk_word_self, a₅, w4_0, R4 .r13 (by decide)]
  have w6_8 : word s₆.mem base (t + 8) = word s.mem base (t + 8) := by
    rw [m₆, ap _ _ _ _ (by omega) (by omega) (by omega), k₅.2.1, w4_8]
  have w6_16 : word s₆.mem base (t + 16) =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [m₆, ap _ _ _ _ (by omega) (by omega) (by omega), k₅.2.1, w4_16]
  have hG : (s₇.gpr .rax + word s₇.mem base t) >>> n =
      (word s.mem base (t + 8) * s.gpr .rbp + word s.mem base t * s.gpr .r13) >>> n := by
    rw [a₇, k₇.2.1, w6_8, w6_0, R6 .rbp (by decide)]
  have w8_8 : word s₈.mem base (t + 8) =
      (word s.mem base (t + 8) * s.gpr .rbp + word s.mem base t * s.gpr .r13) >>> n := by
    rw [m₈, pk_word_self, hG]
  have w8_16 : word s₈.mem base (t + 16) =
      (word s.mem base (t + 8) * s.gpr .rcx + word s.mem base t * s.gpr .r8) >>> n := by
    rw [m₈, ap _ _ _ _ (by omega) (by omega) (by omega), k₇.2.1, w6_16]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mu, pk_word_self, a₉, w8_16]
  · rw [mu, ap _ _ _ _ (by omega) (by omega) (by omega), k₉.2.1, w8_8]
  · exact ((((((((((Keeps.pk k₁).trans (k₂.mono (by simp))).trans (Keeps.pk k₃)).trans
      (k₄.mono (by simp))).trans (Keeps.pk k₅)).trans (k₆.mono (by simp))).trans (Keeps.pk k₇)).trans
      (k₈.mono (by simp))).trans ((Keeps.pk k₉).mono (by simp))).trans (ku.mono (by simp)))
  · rw [mu, k₉.2.1, m₈, k₇.2.1, m₆, k₅.2.1, m₄, k₃.2.1, m₂, k₁.2.1]
    exact (((((ou _ (t + 16) _ (by omega) (by omega)).trans (ou _ (t + 16) _ (by omega) (by omega))).trans
      (ou _ t _ (by omega) (by omega))).trans (ou _ (t + 8) _ (by omega) (by omega))).trans
      (ou _ t _ (by omega) (by omega)))

/-- The first chunk's matrix into `r9`–`r12`. -/
theorem pkFirst_ok (s : State) :
    WP isa (.block pkFirst) s fun s' =>
      s'.gpr .r9 = s.gpr .r8 ∧ s'.gpr .r10 = s.gpr .rcx ∧ s'.gpr .r11 = s.gpr .r13 ∧ s'.gpr .r12 = s.gpr .rbp ∧
        Keeps [.r9, .r10, .r11, .r12] s s' := by
  drun [pkFirst]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ↓reduceIte]

/-- A column of the batch's matrix times the chunk's. -/
theorem pkCol_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t + 8 ≤ 4096)
    {x y : Reg} (hx : x = .r9 ∧ y = .r11 ∨ x = .r10 ∧ y = .r12) :
    WP isa (.block (pkCol x y t)) s fun s' =>
      s'.gpr x = s.gpr .r8 * s.gpr x + s.gpr .rcx * s.gpr y ∧
      s'.gpr y = s.gpr .rbp * s.gpr y + s.gpr .r13 * s.gpr x ∧
      PKeep [.rax, .rdx, x, y] s s' ∧ Outside base t 8 s.mem s'.mem := by
  have hN := hs.nowrap
  have F : ∀ r ∈ [Reg.rax, .rdx, .r8, .rcx, .rbp, .r13, .rdi], (¬ r = x ∧ ¬ x = r) ∧ (¬ r = y ∧ ¬ y = r) := by
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hxy : ¬ x = y ∧ ¬ y = x := by rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := F .rax (by simp)
  obtain ⟨⟨d1, d2⟩, d3, d4⟩ := F .rdx (by simp)
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := F .r8 (by simp)
  obtain ⟨⟨c1, c2⟩, c3, c4⟩ := F .rcx (by simp)
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := F .rbp (by simp)
  obtain ⟨⟨f1, f2⟩, f3, f4⟩ := F .r13 (by simp)
  obtain ⟨⟨i1, i2⟩, i3, i4⟩ := F .rdi (by simp)
  rw [pkCol, WP.block_append_iff, WP.block_append_iff,
    show [Instr.mov .rax (.reg .r13), .mul x, .store (sc t) .rax] =
      [Instr.mov .rax (.reg .r13), .mul x] ++ [.store (sc t) .rax] from rfl, WP.block_append_iff]
  have h0 : WP isa (.block [.mov .rax (.reg .r13), .mul x]) s fun s₁ =>
      s₁.gpr .rax = s.gpr .r13 * s.gpr x ∧ Keeps [.rax, .rdx] s s₁ := by
    drun [pk_mul_lo, a1, a2]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ↓reduceIte]
  refine WP.mono h0 fun s₁ ⟨a₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (pkStore_ok hs₁ .rax (d := t) ht) fun s₂ ⟨m₂, g₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_pk k₂ (by decide)
  have h1 : WP isa (.block [.mov .rax (.reg .r8), .mul x, .mov x (.reg .rax), .mov .rax (.reg .rcx), .mul y,
      .alu .add x (.reg .rax), .mov .rax (.reg .rbp), .mul y]) s₂ fun s₃ =>
      s₃.gpr x = s₂.gpr .r8 * s₂.gpr x + s₂.gpr .rcx * s₂.gpr y ∧ s₃.gpr .rax = s₂.gpr .rbp * s₂.gpr y ∧
        Keeps [.rax, .rdx, x] s₂ s₃ := by
    drun [pk_mul_lo, a1, a2, a3, a4, d1, d2, d3, d4, e1, e2, c1, c2, b1, b2, b3, b4, hxy.1, hxy.2,
      RegUpd.gpr_setReg_self]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ↓reduceIte]
  refine WP.mono h1 fun s₃ ⟨x₃, a₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by simp [i1])
  have R : ∀ r, r ∉ [Reg.rax, .rdx] → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂, k₁.1 r hr]
  have y3 : s₃.gpr y = s.gpr y := by rw [k₃.1 y (by simp [a4, d4, hxy.2]), R y (by simp [a4, d4])]
  have t3 : word s₃.mem base t = s.gpr .r13 * s.gpr x := by rw [k₃.2.1, m₂, pk_word_self, a₁]
  have xx : s₃.gpr x = s.gpr .r8 * s.gpr x + s.gpr .rcx * s.gpr y := by
    rw [x₃, R .r8 (by decide), R x (by simp [a2, d2]), R .rcx (by decide), R y (by simp [a4, d4])]
  have ra : s₃.gpr .rax = s.gpr .rbp * s.gpr y := by rw [a₃, R .rbp (by decide), R y (by simp [a4, d4])]
  drun [load_sc hs₃ ht, a1, a2, a3, a4, hxy.1, hxy.2, RegUpd.gpr_setReg_self, t3, xx, ra]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne (h := hr.2.2.2), RegUpd.gpr_setReg_of_ne (h := hr.1), RegUpd.gpr_arithFlags,
      k₃.1 r (by simp [hr.1, hr.2.1, hr.2.2.1]), R r (by simp [hr.1, hr.2.1])]
  · exact k₃.2.2.1.trans (k₂.rd.trans k₁.2.2.1)
  · exact k₃.2.2.2.trans (k₂.wr.trans k₁.2.2.2)
  · rw [k₃.2.1, m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)

/-- The batch's matrix times the chunk's. -/
theorem pkComp_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t + 8 ≤ 4096) :
    WP isa (.block (pkComp t)) s fun s' =>
      s'.gpr .r9 = s.gpr .r8 * s.gpr .r9 + s.gpr .rcx * s.gpr .r11 ∧
      s'.gpr .r11 = s.gpr .rbp * s.gpr .r11 + s.gpr .r13 * s.gpr .r9 ∧
      s'.gpr .r10 = s.gpr .r8 * s.gpr .r10 + s.gpr .rcx * s.gpr .r12 ∧
      s'.gpr .r12 = s.gpr .rbp * s.gpr .r12 + s.gpr .r13 * s.gpr .r10 ∧
      PKeep [.rax, .rdx, .r9, .r10, .r11, .r12] s s' ∧ Outside base t 8 s.mem s'.mem := by
  rw [pkComp, WP.block_append_iff]
  refine WP.mono (pkCol_ok hs ht (Or.inl ⟨rfl, rfl⟩)) fun s₁ ⟨x₁, y₁, k₁, o₁⟩ => ?_
  refine WP.mono (pkCol_ok (hs.of_pk k₁ (by decide)) ht (Or.inr ⟨rfl, rfl⟩)) fun s₂ ⟨x₂, y₂, k₂, o₂⟩ => ?_
  have g : ∀ r ∈ [Reg.r8, .rcx, .rbp, .r13, .r10, .r12], s₁.gpr r = s.gpr r := fun r hr => k₁.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
  have g' : ∀ r ∈ [Reg.r9, .r11], s₂.gpr r = s₁.gpr r := fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> subst h <;> decide)
  refine ⟨?_, ?_, ?_, ?_, (k₁.mono (by simp)).trans (k₂.mono (by simp)), o₁.trans o₂⟩
  · rw [g' .r9 (by simp), x₁]
  · rw [g' .r11 (by simp), y₁]
  · rw [x₂, g .r8 (by simp), g .r10 (by simp), g .rcx (by simp), g .r12 (by simp)]
  · rw [y₂, g .rbp (by simp), g .r12 (by simp), g .r13 (by simp), g .r10 (by simp)]

/-! ## A chunk -/

/-- The registers a chunk writes. -/
abbrev pkChunkRegs : List Reg := [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13]

/-- The words of a chunk's state in `s`: `~d` in `rbx`, the low words at
`[t]`, `[t + 8]`, and the batch's matrix in `r9`–`r12`. -/
def pkOf (s : State) (base : Addr) (t : Nat) : PkSt :=
  ⟨s.gpr .rbx, word s.mem base t, word s.mem base (t + 8), s.gpr .r9, s.gpr .r10, s.gpr .r11, s.gpr .r12⟩

/-- A chunk of `n` steps: `pkChunkV` of the state's words. -/
theorem pkChunk_ok {s : State} {base : Addr} (hs : Scr s base) {t n : Nat} {first last : Bool}
    (hn : 1 ≤ n ∧ n ≤ 15) (ht : t + 24 ≤ 4096) :
    WP isa (.block (pkChunk t n first last)) s fun s' =>
      pkOf s' base t = pkChunkV n first last (pkOf s base t) ∧
      PKeep pkChunkRegs s s' ∧ Outside base t 24 s.mem s'.mem := by
  have hN := hs.nowrap
  simp only [pkChunk, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pkSet_ok hs (t := t) (by omega)) fun s₁ ⟨r8₁, r13₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pkSteps_ok s₁ hn.2) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [r8₁, r13₁, k₁.1 _ (by decide)] at e₂
  rw [WP.block_append_iff]
  refine WP.mono (pkExt_ok s₂) fun s₃ ⟨u₃, v₃, q₃, r₃, k₃⟩ => ?_
  have hs₃ : Scr s₃ base := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have mem₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  have keep₃ : ∀ r ∈ [Reg.r9, .r10, .r11, .r12], s₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [k₃.1 r (by rcases hr with h | h | h | h <;> subst h <;> decide),
      k₂.1 r (by rcases hr with h | h | h | h <;> subst h <;> decide),
      k₁.1 r (by rcases hr with h | h | h | h <;> subst h <;> decide)]
  -- The chunk's steps, as `pkChunkV` names them.
  generalize hP : Divstep.psteps n (s.gpr .rbx, (word s.mem base t &&& 0x7fff) + 2 ^ 31,
    (word s.mem base (t + 8) &&& 0x7fff) + 2 ^ 47) = P at e₂
  obtain ⟨E', R1, R2⟩ := P
  simp only [Prod.mk.injEq] at e₂
  obtain ⟨d₂, f₂, g₂⟩ := e₂
  rw [f₂] at u₃ v₃
  rw [g₂] at q₃ r₃
  have rbx₃ : s₃.gpr .rbx = E' := by rw [k₃.1 _ (by decide), d₂]
  rw [WP.block_append_iff]
  have hlow : WP isa (.block (if last = true then [] else pkLow n t)) s₃ fun s₄ =>
      (∀ r ∈ [Reg.rbx, .r8, .rcx, .r13, .rbp, .r9, .r10, .r11, .r12], s₄.gpr r = s₃.gpr r) ∧
      word s₄.mem base t = (if last then word s.mem base t else
        (word s.mem base (t + 8) * Divstep.pextHi R1 + word s.mem base t * Divstep.pextLo R1) >>> n) ∧
      word s₄.mem base (t + 8) = (if last then word s.mem base (t + 8) else
        (word s.mem base (t + 8) * Divstep.pextHi R2 + word s.mem base t * Divstep.pextLo R2) >>> n) ∧
      PKeep [.rax, .rdx] s₃ s₄ ∧ Outside base t 24 s₃.mem s₄.mem := by
    cases last
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have kr : ∀ r ∈ [Reg.rbx, .r8, .rcx, .r13, .rbp, .r9, .r10, .r11, .r12], r ∉ [Reg.rax, .rdx] := by decide
      refine WP.mono (pkLow_ok hs₃ ⟨hn.1, by omega⟩ ht) fun s₄ ⟨w0, w1, k₄, o₄⟩ =>
        ⟨fun r hr => k₄.gpr r (kr r hr), ?_, ?_, k₄, o₄⟩
      · rw [w0, mem₃, u₃, v₃]
      · rw [w1, mem₃, q₃, r₃]
    · simp only [↓reduceIte]
      exact WP.block_nil_iff.mpr ⟨fun _ _ => rfl, by rw [mem₃], by rw [mem₃], ⟨fun _ _ => rfl, rfl, rfl⟩,
        Outside.refl _ _ _ _⟩
  refine WP.mono hlow fun s₄ ⟨R₄, w₄, w₄', k₄, o₄⟩ => ?_
  have hs₄ := hs₃.of_pk k₄ (by decide)
  have k34 : PKeep pkChunkRegs s s₄ := ((((Keeps.pk k₁).mono (by decide)).trans ((Keeps.pk k₂).mono
    (by decide))).trans ((Keeps.pk k₃).mono (by decide))).trans (k₄.mono (by decide))
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (pkComp_ok hs₄ (t := t + 16) (by omega)) fun s₅ ⟨x9, x11, x10, x12, k₅, o₅⟩ =>
      ⟨?_, k34.trans (k₅.mono (by decide)), ?_⟩
    · have w5 : word s₅.mem base t = word s₄.mem base t := o₅.word (by omega) (by omega)
      have w5' : word s₅.mem base (t + 8) = word s₄.mem base (t + 8) := o₅.word (by omega) (by omega)
      simp only [pkOf, pkChunkV, hP, Bool.false_eq_true, ↓reduceIte, PkSt.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [k₅.gpr _ (by decide), R₄ _ (by simp), rbx₃]
      · rw [w5, w₄]
      · rw [w5', w₄']
      · rw [x9, R₄ .r8 (by simp), R₄ .rcx (by simp), R₄ .r9 (by simp), R₄ .r11 (by simp), u₃, v₃,
          keep₃ .r9 (by simp), keep₃ .r11 (by simp)]
      · rw [x10, R₄ .r8 (by simp), R₄ .rcx (by simp), R₄ .r10 (by simp), R₄ .r12 (by simp), u₃, v₃,
          keep₃ .r10 (by simp), keep₃ .r12 (by simp)]
      · rw [x11, R₄ .rbp (by simp), R₄ .r13 (by simp), R₄ .r9 (by simp), R₄ .r11 (by simp), q₃, r₃,
          keep₃ .r9 (by simp), keep₃ .r11 (by simp)]
      · rw [x12, R₄ .rbp (by simp), R₄ .r13 (by simp), R₄ .r10 (by simp), R₄ .r12 (by simp), q₃, r₃,
          keep₃ .r10 (by simp), keep₃ .r12 (by simp)]
    · rw [← mem₃]; exact o₄.trans (fun x hx => o₅ x (by omega))
  · simp only [↓reduceIte]
    refine WP.mono (pkFirst_ok s₄) fun s₅ ⟨x9, x10, x11, x12, k₅⟩ =>
      ⟨?_, k34.trans ((Keeps.pk k₅).mono (by decide)), by rw [k₅.2.1, ← mem₃]; exact o₄⟩
    simp only [pkOf, pkChunkV, hP, ↓reduceIte, PkSt.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k₅.1 _ (by decide), R₄ _ (by simp), rbx₃]
    · rw [k₅.2.1, w₄]
    · rw [k₅.2.1, w₄']
    · rw [x9, R₄ .r8 (by simp), u₃]
    · rw [x10, R₄ .rcx (by simp), v₃]
    · rw [x11, R₄ .r13 (by simp), q₃]
    · rw [x12, R₄ .rbp (by simp), r₃]

end VG.Proof.X25519.X86_64
