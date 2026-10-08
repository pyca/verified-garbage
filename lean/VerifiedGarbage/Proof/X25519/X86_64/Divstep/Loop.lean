import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Packed

/-!
# X25519 on x86-64, inversion by divsteps: the 59 divsteps of a batch

`dsteps` copies the low words of `f` and `g` to `dsT` and loads `~d`
(`dstart_ok`), runs four packed chunks (`pkChunk_ok`), and stores `d` and the
matrix (`dsteps_ok`): `pkBatchV`'s words. A loop counted down by its body's
last instruction is `cntLoop_ok`; the batches' loop uses it.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- A loop whose body takes the invariant from `j` to `j - 1` and sets `ZF`
when `j - 1 = 0`, run from `n ≥ 1`. -/
theorem cntLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.zf = some (decide (j - 1 = 0)))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show s'.zf.map (!·) = some false
    rw [hz, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show s'.zf.map (!·) = some true
    rw [hz]; simp [hj]

/-- `x - 1` on words, for `1 ≤ j`. -/
theorem ofNat_sub_one {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) :
    BitVec.ofNat 64 j - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1
    by decide, Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega : j - 1 < 2 ^ 64)]
  omega

theorem ofNat_eq_zero {j : Nat} (hj' : j < 2 ^ 64) : (BitVec.ofNat 64 j == 0) = decide (j = 0) := by
  by_cases h : j = 0
  · subst h; rfl
  · rw [decide_eq_false h]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj'] at this
    exact h this

theorem z1 : (1 : BitVec 32).setWidth 64 = 1 := by decide

theorem inR {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (off base d) 8 := ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

theorem inW {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    InRegions s.wr (off base d) 8 := ⟨_, hs.wr, contains_sc hd⟩

theorem dword_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 _ _ _

theorem dword_writeW_ne (m : Mem) (base : Addr) {d e : Nat} (v : BitVec 64) (h : e + 8 ≤ d ∨ d + 8 ≤ e)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) : word (m.writeW (off base d) v) base e = word m base e :=
  Mem.readW_writeW_sep (sep_off base h he hd) (by decide)

theorem sm1 : (-1 : BitVec 32).signExtend 64 = BitVec.allOnes 64 := by decide

theorem xor_ones (x : BitVec 64) : x ^^^ BitVec.allOnes 64 = ~~~x := BitVec.xor_allOnes

/-- A batch's start: the count of batches into `r14`, the low words of `f` and
`g` copied to `dsT`, and `~d` into `rbx`. -/
theorem dstart_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block dstart) s fun t =>
      t.gpr .rbx = ~~~word s.mem base dsD ∧ t.gpr .r14 = s.gpr .rbp ∧
      word t.mem base dsT = word s.mem base dsF ∧ word t.mem base (dsT + 8) = word s.mem base dsG ∧
      Outside base dsT 16 s.mem t.mem ∧ PKeep [.rax, .rbx, .r14] s t := by
  have hn := hs.nowrap
  drun [dstart, State.load64, State.store64, ea_sc, hs.rdi, inR hs (show dsD + 8 ≤ 4096 by decide),
    inR hs (show dsF + 8 ≤ 4096 by decide), inR hs (show dsG + 8 ≤ 4096 by decide),
    inW hs (show dsT + 8 ≤ 4096 by decide), inW hs (show dsT + 8 + 8 ≤ 4096 by decide), sm1, xor_ones,
    RegUpd.gpr_setReg_self]
  simp only [dsD, dsF, dsG, dsT]
  refine ⟨?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp (disch := omega) only [dword_writeW_ne]
  · simp (disch := omega) only [dword_writeW_ne, dword_writeW_self]
  · simp (disch := omega) only [dword_writeW_ne, dword_writeW_self]
  · intro x hx
    rw [writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ↓reduceIte]

/-- `d` and the matrix stored, the count back in `rbp`. -/
theorem dstore_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.alu .xor .rbx (.imm (-1)), .store (sc dsD) .rbx, .store (sc dsU) .r9, .store (sc dsV) .r10,
      .store (sc dsQ) .r11, .store (sc dsR) .r12, .mov .rbp (.reg .r14)]) s fun t =>
      word t.mem base dsD = ~~~s.gpr .rbx ∧ word t.mem base dsU = s.gpr .r9 ∧ word t.mem base dsV = s.gpr .r10 ∧
      word t.mem base dsQ = s.gpr .r11 ∧ word t.mem base dsR = s.gpr .r12 ∧ Outside base dsD 40 s.mem t.mem ∧
      t.gpr .rbp = s.gpr .r14 ∧ (∀ r, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  drun [State.store64, ea_sc, hs.rdi, inW hs (show dsD + 8 ≤ 4096 by decide), inW hs (show dsU + 8 ≤ 4096 by decide),
    inW hs (show dsV + 8 ≤ 4096 by decide), inW hs (show dsQ + 8 ≤ 4096 by decide),
    inW hs (show dsR + 8 ≤ 4096 by decide), sm1, xor_ones, RegUpd.gpr_setReg_self]
  simp only [dsD, dsU, dsV, dsQ, dsR]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr hr' => by simp only [hr, hr', ↓reduceIte]⟩
  · rw [dword_writeW_ne _ _ _ (by omega) (by omega) (by omega), dword_writeW_ne _ _ _ (by omega) (by omega) (by omega),
      dword_writeW_ne _ _ _ (by omega) (by omega) (by omega), dword_writeW_ne _ _ _ (by omega) (by omega) (by omega),
      dword_writeW_self]
  · rw [dword_writeW_ne _ _ _ (by omega) (by omega) (by omega), dword_writeW_ne _ _ _ (by omega) (by omega) (by omega),
      dword_writeW_ne _ _ _ (by omega) (by omega) (by omega), dword_writeW_self]
  · rw [dword_writeW_ne _ _ _ (by omega) (by omega) (by omega), dword_writeW_ne _ _ _ (by omega) (by omega) (by omega),
      dword_writeW_self]
  · rw [dword_writeW_ne _ _ _ (by omega) (by omega) (by omega), dword_writeW_self]
  · rw [dword_writeW_self]
  · intro x hx
    rw [writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega)]

theorem ofNat_fe (m : Mem) (base : Addr) (o : Nat) : BitVec.ofNat 64 (fe m base o) = word m base o := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [fe, val4]
  omega

/-- The words of a batch's packed divsteps from `d` and the low words of `f`, `g` in memory. -/
def pkW (m : Mem) (base : Addr) : PkSt := pkBatchV (word m base dsD) (word m base dsF) (word m base dsG)

/-- The first chunk ignores the matrix it starts from. -/
theorem pkChunkV_first (n : Nat) (last : Bool) (E F G U V Q R : BitVec 64) :
    pkChunkV n true last ⟨E, F, G, U, V, Q, R⟩ = pkChunkV n true last ⟨E, F, G, 0, 0, 0, 0⟩ := by
  simp only [pkChunkV, ↓reduceIte]

/-- A chunk at `dsT`, from a state whose words are `w`. -/
theorem pkChunkT_ok {s : State} {base : Addr} (hs : Scr s base) {n : Nat} {first last : Bool}
    (hn : 1 ≤ n ∧ n ≤ 15) {w : PkSt} (hw : pkOf s base dsT = w) :
    WP isa (.block (pkChunk dsT n first last)) s fun t =>
      pkOf t base dsT = pkChunkV n first last w ∧ PKeep pkChunkRegs s t ∧ Outside base dsT 24 s.mem t.mem :=
  WP.mono (pkChunk_ok hs hn (by decide)) fun t ⟨e, k, o⟩ => ⟨e.trans (by rw [hw]), k, o⟩

/-- A batch's divsteps: `d` and the matrix of its packed chunks, stored; the
count of batches kept in `rbp`. -/
theorem dsteps_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa dsteps s fun t =>
      word t.mem base dsD = ~~~(pkW s.mem base).E ∧ word t.mem base dsU = (pkW s.mem base).U ∧
      word t.mem base dsV = (pkW s.mem base).V ∧ word t.mem base dsQ = (pkW s.mem base).Q ∧
      word t.mem base dsR = (pkW s.mem base).R ∧ Outside base dsD 64 s.mem t.mem ∧
      t.gpr .rbp = s.gpr .rbp ∧
      (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  rw [dsteps, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (dstart_ok hs) fun s₁ ⟨b1, c1, f1, g1, O1, k1⟩ => ?_
  have hs₁ := hs.of_pk k1 (by decide)
  have w1 : pkOf s₁ base dsT =
      ⟨~~~word s.mem base dsD, word s.mem base dsF, word s.mem base dsG, s₁.gpr .r9, s₁.gpr .r10, s₁.gpr .r11,
        s₁.gpr .r12⟩ := by
    simp only [pkOf, b1, f1, g1]
  rw [WP.block_append_iff]
  refine WP.mono (pkChunkT_ok hs₁ (first := true) (last := false) (n := 15) (by decide) w1)
    fun s₂ ⟨e2, k2, O2⟩ => ?_
  rw [pkChunkV_first] at e2
  have hs₂ := hs₁.of_pk k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkChunkT_ok hs₂ (first := false) (last := false) (n := 15) (by decide) e2)
    fun s₃ ⟨e3, k3, O3⟩ => ?_
  have hs₃ := hs₂.of_pk k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkChunkT_ok hs₃ (first := false) (last := false) (n := 15) (by decide) e3)
    fun s₄ ⟨e4, k4, O4⟩ => ?_
  have hs₄ := hs₃.of_pk k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pkChunkT_ok hs₄ (first := false) (last := true) (n := 14) (by decide) e4)
    fun s₅ ⟨e5, k5, O5⟩ => ?_
  have hs₅ := hs₄.of_pk k5 (by decide)
  refine WP.mono (dstore_ok hs₅) fun t ⟨eD, eU, eV, eQ, eR, O, eb, gt, rt, wt⟩ => ?_
  have hW : pkOf s₅ base dsT = pkW s.mem base := e5
  have cE := congrArg PkSt.E hW; have cU := congrArg PkSt.U hW; have cV := congrArg PkSt.V hW
  have cQ := congrArg PkSt.Q hW; have cR := congrArg PkSt.R hW
  simp only [pkOf] at cE cU cV cQ cR
  have kc : ∀ r, r ∉ dsClob → s₅.gpr r = s.gpr r := fun r hr => by
    have h1 : r ∉ pkChunkRegs := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have h2 : r ∉ [Reg.rax, .rbx, .r14] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide)
    rw [k5.gpr r h1, k4.gpr r h1, k3.gpr r h1, k2.gpr r h1, k1.gpr r h2]
  have r14 : s₅.gpr .r14 = s.gpr .rbp := by
    rw [k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), c1]
  refine ⟨eD.trans (by rw [cE]), eU.trans cU, eV.trans cV, eQ.trans cQ, eR.trans cR, ?_, eb.trans r14,
    fun r hr => ?_, ?_, ?_⟩
  · have Ow : ∀ {o n : Nat} {m m' : Mem}, Outside base o n m m' → dsD ≤ o → o + n ≤ dsD + 64 →
        Outside base dsD 64 m m' := fun h h1 h2 x hx => h x (by omega)
    exact (Ow O1 (by decide) (by decide)).trans <| (Ow O2 (by decide) (by decide)).trans <|
      (Ow O3 (by decide) (by decide)).trans <| (Ow O4 (by decide) (by decide)).trans <|
      (Ow O5 (by decide) (by decide)).trans (Ow O (by decide) (by decide))
  · have h1 : r ≠ .rbp := by intro h; subst h; exact hr (by decide)
    have h2 : r ≠ .rbx := by intro h; subst h; exact hr (by decide)
    rw [gt r h1 h2, kc r hr]
  · rw [rt, k5.rd, k4.rd, k3.rd, k2.rd, k1.rd]
  · rw [wt, k5.wr, k4.wr, k3.wr, k2.wr, k1.wr]

end VG.Proof.X25519.X86_64
