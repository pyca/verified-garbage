import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow

/-!
# X25519 on x86-64, inversion by divsteps: the 59 divsteps of a batch

`dsteps` loads `d` and the low words of `f` and `g`, runs 59 word divsteps
(`dstep_ok`) counted down in `r8`, and stores `d` and the matrix
(`dsteps_ok`). A loop counted down by its body's last instruction is
`cntLoop_ok`; the batches' loop uses it too.
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

theorem s59 : (59 : BitVec 32).signExtend 64 = BitVec.ofNat 64 59 := by decide
theorem s255 : (255 : BitVec 32).signExtend 64 = BitVec.ofNat 64 255 := by decide

/-- A batch's start: `d`, the low words of `f` and `g`, the identity, `d ≥ 0`, and the
counts of batches and steps in `r8`. -/
theorem dstart_ok {s : State} {base : Addr} (hs : Scr s base) {B : Nat} (hB : B ≤ 10)
    (hb : s.gpr .rbp = BitVec.ofNat 64 (256 * B)) :
    WP isa (.block dstart) s fun t =>
      regsD t = ⟨word s.mem base dsD, word s.mem base dsF, word s.mem base dsG, 1, 0, 0, 1⟩ ∧
      t.gpr .r13 = dmOf (t.gpr .rbx) ∧ t.gpr .r8 = BitVec.ofNat 64 (256 * B + 59) ∧
      Keeps [.rbx, .rcx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13] s t := by
  have e : BitVec.ofNat 64 (256 * B) + BitVec.ofNat 64 59 = BitVec.ofNat 64 (256 * B + 59) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hB
    omega
  drun [dstart, State.load64, ea_sc, hs.rdi, inR hs (show dsD + 8 ≤ 4096 by decide),
    inR hs (show dsF + 8 ≤ 4096 by decide), inR hs (show dsG + 8 ≤ 4096 by decide), z1, zs0, s59,
    RegUpd.gpr_setReg_self, regsD, dmOf, hb, e]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    ↓reduceIte]

/-- `r8 -= 1`, its zero flag whether the low byte (the count of steps) is now zero. -/
theorem decR8T_ok (s : State) {B j : Nat} (hB : B ≤ 10) (hj : 1 ≤ j) (hj' : j ≤ 59)
    (hb : s.gpr .r8 = BitVec.ofNat 64 (256 * B + j)) :
    WP isa (.block [.alu .sub .r8 (.imm 1), .alu .test .r8 (.imm 255)]) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (256 * B + (j - 1)) ∧ t.zf = some (decide (j - 1 = 0)) ∧ Keeps [.r8] s t := by
  have e : BitVec.ofNat 64 (256 * B + j) - BitVec.signExtend 64 (1 : BitVec 32) =
      BitVec.ofNat 64 (256 * B + (j - 1)) := by
    rw [ofNat_sub_one (by omega) (by omega)]; congr 1; omega
  have z : (BitVec.ofNat 64 (256 * B + (j - 1)) &&& BitVec.ofNat 64 255 == 0) = decide (j - 1 = 0) := by
    have : BitVec.ofNat 64 (256 * B + (j - 1)) &&& BitVec.ofNat 64 255 = BitVec.ofNat 64 (j - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (255 : Nat) % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [this, ofNat_eq_zero (by omega)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.zf_arithFlags, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq,
    exists_eq_left', hb, e, s255, z]
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The 59 divsteps, from `regsD` with `r8 = 256 B + 59`. -/
theorem dloop_ok (s : State) {B : Nat} (hB : B ≤ 10) (h13 : s.gpr .r13 = dmOf (s.gpr .rbx))
    (h8 : s.gpr .r8 = BitVec.ofNat 64 (256 * B + 59)) :
    WP isa (.loop (.block (dstep ++
      ([.alu .sub .r8 (.imm 1), .alu .test .r8 (.imm 255)] : List Instr))) .ne) s fun t =>
      regsD t = Divstep.wsteps 59 (regsD s) ∧ t.gpr .r8 = BitVec.ofNat 64 (256 * B) ∧
      Keeps (.r8 :: dRegs) s t := by
  refine cntLoop_ok (n := 59)
    (Inv := fun j t => regsD t = Divstep.wsteps (59 - j) (regsD s) ∧ t.gpr .r13 = dmOf (t.gpr .rbx) ∧
      t.gpr .r8 = BitVec.ofNat 64 (256 * B + j) ∧ Keeps (.r8 :: dRegs) s t)
    (fun j t hj1 hjN ⟨rt, t13, t8, kt⟩ => ?_) (fun t ⟨rt, _, t8, kt⟩ => ⟨by simpa using rt, by simpa using t8, kt⟩)
    (by decide) ⟨by rw [Nat.sub_self]; rfl, h13, h8, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (dstep_ok t t13) fun u ⟨ru, u13, ku⟩ => ?_
  refine WP.mono (decR8T_ok u hB hj1 hjN (by rw [ku.1 .r8 (by decide), t8])) fun w ⟨xw, zw, kw⟩ =>
    ⟨⟨?_, ?_, xw, kt.trans ((ku.mono (by decide)).trans (kw.mono (by decide)))⟩, zw⟩
  · have ew : regsD w = regsD u := by
      simp only [regsD, kw.1 .rbx (by decide), kw.1 .rcx (by decide), kw.1 .rbp (by decide),
        kw.1 .r9 (by decide), kw.1 .r10 (by decide), kw.1 .r11 (by decide), kw.1 .r12 (by decide)]
    rw [ew, ru, rt, show 59 - (j - 1) = (59 - j) + 1 by omega, Divstep.wsteps_succ]
  · rw [kw.1 .r13 (by decide), kw.1 .rbx (by decide), u13]

theorem dword_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 _ _ _

theorem dword_writeW_ne (m : Mem) (base : Addr) {d e : Nat} (v : BitVec 64) (h : e + 8 ≤ d ∨ d + 8 ≤ e)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) : word (m.writeW (off base d) v) base e = word m base e :=
  Mem.readW_writeW_sep (sep_off base h he hd) (by decide)

/-- `d` and the matrix stored. -/
theorem dstore_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.store (sc dsD) .rbx, .store (sc dsU) .r9, .store (sc dsV) .r10, .store (sc dsQ) .r11,
      .store (sc dsR) .r12, .mov .rbp (.reg .r8)]) s fun t =>
      word t.mem base dsD = s.gpr .rbx ∧ word t.mem base dsU = s.gpr .r9 ∧ word t.mem base dsV = s.gpr .r10 ∧
      word t.mem base dsQ = s.gpr .r11 ∧ word t.mem base dsR = s.gpr .r12 ∧ Outside base dsD 40 s.mem t.mem ∧
      t.gpr .rbp = s.gpr .r8 ∧ (∀ r, r ≠ .rbp → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  drun [State.store64, ea_sc, hs.rdi, inW hs (show dsD + 8 ≤ 4096 by decide), inW hs (show dsU + 8 ≤ 4096 by decide),
    inW hs (show dsV + 8 ≤ 4096 by decide), inW hs (show dsQ + 8 ≤ 4096 by decide),
    inW hs (show dsR + 8 ≤ 4096 by decide), RegUpd.gpr_setReg_self]
  simp only [dsD, dsU, dsV, dsQ, dsR]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => by simp only [hr, ↓reduceIte]⟩
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

/-- The words of 59 divsteps from `d` and the low words of `f`, `g` in memory. -/
def wOf (m : Mem) (base : Addr) : Divstep.WSt :=
  Divstep.wsteps 59 ⟨word m base dsD, word m base dsF, word m base dsG, 1, 0, 0, 1⟩

/-- A batch's divsteps: `d` and the matrix of 59 divsteps, stored; the count of
batches kept in `rbp`. -/
theorem dsteps_ok {s : State} {base : Addr} (hs : Scr s base) {B : Nat} (hB : B ≤ 10)
    (hb : s.gpr .rbp = BitVec.ofNat 64 (256 * B)) :
    WP isa dsteps s fun t =>
      word t.mem base dsD = (wOf s.mem base).D ∧ word t.mem base dsU = (wOf s.mem base).U ∧
      word t.mem base dsV = (wOf s.mem base).V ∧ word t.mem base dsQ = (wOf s.mem base).Q ∧
      word t.mem base dsR = (wOf s.mem base).R ∧ Outside base dsD 40 s.mem t.mem ∧
      t.gpr .rbp = BitVec.ofNat 64 (256 * B) ∧
      (∀ r, r ∉ dsClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.seq (WP.mono (dstart_ok hs hB hb) fun s₁ ⟨r1, h13, h8, k1⟩ => ?_)
  refine WP.seq (WP.mono (dloop_ok s₁ hB h13 h8) fun s₂ ⟨r2, e8, k2⟩ => ?_)
  have hs₂ := (hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)
  refine WP.mono (dstore_ok hs₂) fun t ⟨eD, eU, eV, eQ, eR, O, eb, gt, rt, wt⟩ => ?_
  have r2' : regsD s₂ = wOf s.mem base := by rw [r2, r1]; rfl
  have cD := congrArg Divstep.WSt.D r2'; have cU := congrArg Divstep.WSt.U r2'
  have cV := congrArg Divstep.WSt.V r2'; have cQ := congrArg Divstep.WSt.Q r2'
  have cR := congrArg Divstep.WSt.R r2'
  simp only [regsD] at cD cU cV cQ cR
  have M : s₂.mem = s.mem := k2.2.1.trans k1.2.1
  rw [M] at O
  refine ⟨eD.trans cD, eU.trans cU, eV.trans cV, eQ.trans cQ, eR.trans cR, O, eb.trans e8, fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt r hr.2.2.2.2.1, k2.1 r (by simp_all), k1.1 r (by simp_all)]
  · rw [rt, k2.2.2.1, k1.2.2.1]
  · rw [wt, k2.2.2.2, k1.2.2.2]

end VG.Proof.X25519.X86_64
