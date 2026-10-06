import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Batch
import VerifiedGarbage.Proof.X25519.X86_64.Freeze

/-!
# X25519 on x86-64, inversion by divsteps: the whole inversion

`invertDS F` leaves in slot 17 (`T1`) `byAlg` of slot 4 (`Z2`), changing
only the working area `[512, 768)` and the registers `clob` and `rbx`
(`invertDS_ok`): the start holds `drun x 0` for the fully reduced `x`
(`dinit_ok`), each batch takes it to the next (`dbatch_ok`), and the end
multiplies `a` by the constant `kSel f` (`dsel_ok`). With `DivstepInv`, that
is `[Z2]^(p-2)` (`invertDS_pow`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The words of `p` stored at `F`, and `a`, `b`, `d` and the count. -/
abbrev dinitB : List Instr :=
  ((List.range 4).flatMap fun i =>
    [.movImm64 .rax (BitVec.ofNat 64 (pNat >>> (64 * i))), .store (sc (dsF + 8 * i)) .rax]) ++
  [.mov32 .rax (.imm 0)] ++ stores dsA .rax .rax .rax .rax ++ stores dsB .rax .rax .rax .rax ++
  [.mov32 .rax (.imm 1), .store (sc dsB) .rax, .store (sc dsD) .rax, .mov32 .rbp (.imm 2560)]

theorem dinit_eq : dinit = freeze Z2 ++ (store4 dsG ++ dinitB) := by
  simp only [dinit, dinitB, List.append_assoc]

/-- A word written in the working area. -/
theorem Outside.writeW_in {base : Addr} {m₀ m : Mem} (h : Outside base 512 256 m₀ m) {d : Nat} {v : BitVec 64}
    (hd : 512 ≤ d) (hd' : d + 8 ≤ 768) : Outside base 512 256 m₀ (m.writeW (off base d) v) :=
  fun x hx => (writeW_outside m base v (by omega) x (by omega)).trans (h x hx)

theorem z2560 : (2560 : BitVec 32).setWidth 64 = BitVec.ofNat 64 (256 * 10) := by decide

/-- `f = p`, `a = 0`, `b = 1`, `d = 1`, the count `10`. -/
theorem dinitB_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block dinitB) s fun t =>
      fe t.mem base dsF = Spec.X25519.P ∧ fe t.mem base dsA = 0 ∧ fe t.mem base dsB = 1 ∧
      word t.mem base dsD = 1 ∧ t.gpr .rbp = BitVec.ofNat 64 (256 * 10) ∧
      fe t.mem base dsG = fe s.mem base dsG ∧ Outside base 512 256 s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbp → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  simp only [dinitB, stores, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, dsF, dsG, dsA, dsB, dsD, Nat.reduceMul, Nat.reduceAdd]
  drun [State.store64, ea_sc, hs.rdi, inW hs (show 576 + 8 ≤ 4096 by decide),
    inW hs (show 584 + 8 ≤ 4096 by decide), inW hs (show 592 + 8 ≤ 4096 by decide),
    inW hs (show 600 + 8 ≤ 4096 by decide), inW hs (show 544 + 8 ≤ 4096 by decide),
    inW hs (show 552 + 8 ≤ 4096 by decide), inW hs (show 560 + 8 ≤ 4096 by decide),
    inW hs (show 568 + 8 ≤ 4096 by decide), inW hs (show 512 + 8 ≤ 4096 by decide),
    inW hs (show 520 + 8 ≤ 4096 by decide), inW hs (show 528 + 8 ≤ 4096 by decide),
    inW hs (show 536 + 8 ≤ 4096 by decide), inW hs (show 704 + 8 ≤ 4096 by decide), z1, zs0, z2560,
    RegUpd.gpr_setReg_self]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr hr' => ?_⟩
  all_goals try simp (disch := omega) only [X86_64.fe, val4, dword_writeW_ne, dword_writeW_self]
  · simp only [pNat]; decide
  · rfl
  · rfl
  · repeat refine Outside.writeW_in ?_ (by omega) (by omega)
    exact Outside.refl _ _ _ _
  · simp only [hr, hr', ↓reduceIte]

/-- The start: the state `drun x 0` for the fully reduced `x`, and the count. -/
theorem dinit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block dinit) s fun t =>
      DMem t.mem base (drun (fe s.mem base Z2 % Spec.X25519.P) 0) ∧ t.gpr .rbp = BitVec.ofNat 64 (256 * 10) ∧
      Outside base 512 256 s.mem t.mem ∧ (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  rw [dinit_eq, WP.block_append_iff]
  refine WP.mono (freeze_ok hs (by unfold Slot; decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₁ (by unfold Slot; decide)) fun s₂ ⟨m2, g2, r2, w2⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨(g2 _).trans hs₁.rdi, w2 ▸ hs₁.wr, hs.nowrap⟩
  refine WP.mono (dinitB_ok hs₂) fun t ⟨fF, fA, fB, wD, wC, fG, O, gt, rt, wt⟩ =>
    ⟨⟨wD, fF, ?_, fA, fB⟩, wC, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [fG, m2, fe_st4 _ _ (by decide), e1]; rfl
  · have O2 : Outside base 512 256 s.mem s₂.mem := by
      rw [m2, k1.2.1]
      exact Outside.wide (st4_outside _ _ (by decide) _ _ _ _) (by decide) (by decide)
    exact O2.trans O
  · have h' : r ≠ .rax := by intro h; subst h; exact hr (by decide)
    have h'' : r ≠ .rbp := by intro h; subst h; exact hr (by decide)
    rw [gt r h' h'', g2, k1.1 r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))]
  · rw [rt, r2, k1.2.2.1]
  · rw [wt, w2, k1.2.2.2]

/-- The batches: from `drun x 0` and the count `10`, `drun x 10`. -/
theorem dloops_ok {s : State} {base : Addr} (hs : Scr s base) {x : Nat} (hm : DMem s.mem base (drun x 0))
    (hc : s.gpr .rbp = BitVec.ofNat 64 (256 * 10)) :
    WP isa (.loop dbatch .ne) s fun t =>
      DMem t.mem base (drun x 10) ∧ Outside base 512 256 s.mem t.mem ∧
      (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine cntLoop_ok (n := 10)
    (Inv := fun j t => DMem t.mem base (drun x (10 - j)) ∧ t.gpr .rbp = BitVec.ofNat 64 (256 * j) ∧
      Outside base 512 256 s.mem t.mem ∧ (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr)
    (fun j t hj1 hjN ⟨mt, ct, Ot, gt, rt, wt⟩ => ?_) (fun t ⟨mt, _, Ot, gt, rt, wt⟩ => ⟨mt, Ot, gt, rt, wt⟩)
    (by decide) ⟨hm, hc, Outside.refl _ _ _ _, fun _ _ => rfl, rfl, rfl⟩
  have ht : Scr t base := ⟨(gt _ (by decide)).trans hs.rdi, wt ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (dbatch_ok ht mt hj1 hjN ct) fun u ⟨mu, cu, zu, Ou, gu, ru, wu⟩ =>
    ⟨⟨?_, cu, Ot.trans Ou, fun r hr => (gu r hr).trans (gt r hr), ru.trans rt, wu.trans wt⟩, zu⟩
  rw [show 10 - (j - 1) = (10 - j) + 1 by omega]
  exact mu

theorem sel_mask (a b m : BitVec 64) (hm : m = 0 ∨ m = BitVec.allOnes 64) :
    a ^^^ ((b ^^^ a) &&& m) = if m = 0 then a else b := by
  rcases hm with rfl | rfl
  · simp
  · have : BitVec.allOnes 64 ≠ 0 := by decide
    simp only [BitVec.and_allOnes, this, ↓reduceIte]
    rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem top_mask (w : BitVec 64) : (0 : BitVec 64) - (w >>> 63) = if 2 ^ 63 ≤ w.toNat then BitVec.allOnes 64 else 0 := by
  rw [maskW_eq]; unfold maskW
  by_cases h : 2 ^ 63 ≤ w.toNat
  · simp only [(msb_iff w).2 h, h, ↓reduceIte]
  · have h' : ¬ w.msb = true := fun h' => h ((msb_iff w).1 h')
    simp only [h', h, Bool.false_eq_true, ↓reduceIte]

/-- `[dsK] = kSel f`. -/
theorem dsel_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block dsel) s fun t =>
      fe t.mem base dsK = kSel (fe s.mem base dsF) ∧ Outside base dsK 32 s.mem t.mem ∧
      (∀ r, r ∉ [.rax, .rcx, .rdx] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  simp only [dsel, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, dsF, dsK, Nat.reduceMul, Nat.reduceAdd]
  drun [State.load64, State.store64, ea_sc, hs.rdi, inR hs (show 600 + 8 ≤ 4096 by decide),
    inW hs (show 640 + 8 ≤ 4096 by decide), inW hs (show 648 + 8 ≤ 4096 by decide),
    inW hs (show 656 + 8 ≤ 4096 by decide), inW hs (show 664 + 8 ≤ 4096 by decide), zs0,
    RegUpd.gpr_setReg_self, top_mask]
  have hm : ∀ w : BitVec 64, (if 2 ^ 63 ≤ w.toNat then BitVec.allOnes 64 else 0) = 0 ∨
      (if 2 ^ 63 ≤ w.toNat then BitVec.allOnes 64 else 0) = BitVec.allOnes 64 := fun w => by
    split <;> simp
  simp only [sel_mask _ _ _ (hm _)]
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · simp (disch := omega) only [X86_64.fe, val4, dword_writeW_ne, dword_writeW_self]
    have h3 := (word s.mem base 600).isLt
    have e : (fe s.mem base 576 < 2 ^ 255) = ¬ 2 ^ 63 ≤ (word s.mem base 600).toNat := by
      simp only [X86_64.fe, val4, Nat.reduceAdd]
      have := (word s.mem base 576).isLt; have := (word s.mem base 584).isLt; have := (word s.mem base 592).isLt
      apply propext; omega
    unfold kSel
    rw [show (576 : Nat) = dsF from rfl] at e
    simp only [dsF] at e ⊢
    by_cases h : 2 ^ 63 ≤ (word s.mem base 600).toNat
    · have hn : ¬ (fe s.mem base 576 < 2 ^ 255) := by rw [e]; exact fun h' => h' h
      have : BitVec.allOnes 64 ≠ 0 := by decide
      simp only [h, hn, ↓reduceIte, this]
      decide
    · have hn : fe s.mem base 576 < 2 ^ 255 := by rw [e]; exact h
      simp only [h, hn, ↓reduceIte]
      decide
  · intro x hx
    rw [writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2, ↓reduceIte]

variable {fld : Field} (hf : FieldOk fld)

include hf in
/-- The inversion by divsteps: slot 17 becomes `byAlg` of slot 4, and only the
working area `[512, 768)` and the registers `clob` and `rbx` change. -/
theorem invertDS_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (invertDS fld) s fun t =>
      (∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 512 256 s.mem t.mem ∧ E t.mem base 17 = byAlg (E s.mem base 4) := by
  have hn := hs.nowrap
  have hc : ∀ r, r ∉ clob → r ≠ .rbx → r ∉ dsClob := fun r h1 h2 h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact h2 rfl | exact h1 (by decide)
  refine WP.seq (WP.mono (dinit_ok hs) fun s₁ ⟨m1, c1, O1, g1, r1, w1⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨(g1 _ (by decide)).trans hs.rdi, w1 ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (dloops_ok hs₁ m1 c1) fun s₂ ⟨m2, O2, g2, r2, w2⟩ => ?_)
  have hs₂ : Scr s₂ base := ⟨(g2 _ (by decide)).trans hs₁.rdi, w2 ▸ hs₁.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (dsel_ok hs₂) fun s₃ ⟨k3, O3, g3, r3, w3⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g3 _ (by decide)).trans hs₂.rdi, w3 ▸ hs₂.wr, hs.nowrap⟩
  refine WP.mono (hf.mul hs₃ (by unfold Slot; decide) (by unfold Slot; decide) (by unfold Slot; decide))
    fun t ⟨op, ft⟩ => ⟨fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [op.gpr r h1, g3 r (fun h => h1 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide)), g2 r (hc r h1 h2), g1 r (hc r h1 h2)]
  · rw [op.rd, r3, r2, r1]
  · rw [op.wr, w3, w2, w1]
  · exact ((O1.trans O2).trans (Outside.wide O3 (by decide) (by decide))).trans
      (Outside.wide op.mem (by decide) (by decide))
  · show F t.mem base T1 = _
    rw [ft, show (T1 : Nat) = dsA from rfl]
    show toFe (fe s₃.mem base dsA) * toFe (fe s₃.mem base dsK) = _
    rw [O3.fe (d := dsA) (by decide) (by decide), k3, m2.a, m2.f]
    unfold byAlg
    have hx : (E s.mem base 4).val = fe s.mem base Z2 % Spec.X25519.P := by
      simp only [E, F, toFe, Fin.val_ofNat]; rfl
    rw [hx]

include hf in
/-- With the theory of divsteps, the inversion is `[Z2]^(p-2)`. -/
theorem invertDS_pow [DivstepInv] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (invertDS fld) s fun t =>
      (∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 512 256 s.mem t.mem ∧
      E t.mem base 17 = Spec.X25519.pow (E s.mem base 4) (Spec.X25519.P - 2) :=
  WP.mono (invertDS_ok hf hs) fun _ ⟨g, r, w, o, e⟩ => ⟨g, r, w, o, e.trans (DivstepInv.eq _)⟩

end VG.Proof.X25519.X86_64
