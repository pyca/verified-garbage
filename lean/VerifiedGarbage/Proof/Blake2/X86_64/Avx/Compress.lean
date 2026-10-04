import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Round
import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Compress

/-!
# BLAKE2s compression function on x86-64 with AVX

The proof that `Impl.Blake2.X86_64.Avx.compress` meets `compressX86_64 s`
(`Proof/Blake2/X86_64/Contract.lean`), as the scalar code does
(`Proof/Blake2/X86_64/Compress.lean`, whose description of the precondition
and of the work vector before the rounds, `V0`, this proof shares): the
masks and the IV in registers (`setup_ok`), then for each block the work
vector (`init_ok`), the rounds (`rounds_ok`), the XOR into the state
(`finish_ok`) and the next block (`advance_ok`). Constant time is checked
by evaluation.
-/

namespace VG.Proof.Blake2.X86_64.Avx

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx
open VG.Impl.Blake2.X86_64 (at_)
open VG.Proof.Blake2.X86_64 (Pre pre_of stA bpA nb t₀ fl stR blR H₀ blkAddr V0 V0_get F_eq flagW
  zf_last τ₀ agree₀ satState lo32_ofNat hi32_ofNat)

/-- Word `q` of BLAKE2s's IV. -/
def ivAt (q : Nat) : W := if h : q < 8 then Spec.Blake2.s.IV[q] else 0

/-- The masks and the IV, in their registers. -/
structure Consts (s : State) : Prop where
  masks : Masks s
  iv0 : ∀ q < 4, dword (s.xmm .xmm11) q = ivAt q
  iv1 : ∀ q < 4, dword (s.xmm .xmm12) q = ivAt (4 + q)

theorem Consts.of_xf {rs : List XReg} {s t : State} (h : Consts s) (hv : XF rs s t)
    (h11 : .xmm11 ∉ rs) (h12 : .xmm12 ∉ rs) (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : Consts t :=
  ⟨h.masks.of_xf hv h14 h15, fun q hq => (dw_of_xf hv h11 q).trans (h.iv0 q hq),
    fun q hq => (dw_of_xf hv h12 q).trans (h.iv1 q hq)⟩

/-! ## Values of 128 bits made of two quadwords -/

theorem qword_app0 (a b : BitVec 64) : qword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
    Bool.true_and, Nat.mul_zero, Nat.zero_add, ite_true]

theorem unpck_app (lo hi : BitVec 64) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ lo) ((0 : BitVec 64) ++ hi) = hi ++ lo := by
  simp only [XBinOp.eval, qword_app0]

theorem dword_app (a b : BitVec 64) {q : Nat} (hq : q < 4) :
    dword (a ++ b) q = if q < 2 then b.extractLsb' (32 * q) 32 else a.extractLsb' (32 * (q - 2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
  · simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
      Bool.true_and, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMul]
    split <;> first | rfl | omega | (exact congrArg _ (by omega))

/-! ## The set-up -/

/-- `d := (lo, hi)`, through `rax` and `xmm4`. -/
theorem pair64_ok {d : XReg} (hd : d ≠ .xmm4) (lo hi : BitVec 64) (s : State) :
    WP isa (.block (pair64 d lo hi)) s fun u =>
      u.xmm d = hi ++ lo ∧ (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
        u.wr = s.wr ∧ (∀ r, r ≠ d → r ≠ .xmm4 → u.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [pair64, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [xmm_vbin, xmm_vmovq, ↓reduceIte, hd, RegUpd.xmm_setReg,
      RegUpd.gpr_setReg_self, VBinOp.sse]
    exact unpck_app lo hi
  · simp only [VOp.exec_gpr, RegUpd.gpr_setReg, hr, ite_false]
  · simp only [xmm_vbin, xmm_vmovq, h1, h2, ite_false, RegUpd.xmm_setReg]

theorem mask16_eq : (rot16Hi ++ rot16Lo : BitVec 128) = rot16Mask := by decide
theorem mask8_eq : (rotr8Hi ++ rotr8Lo : BitVec 128) = rotr8Mask := by decide

theorem iv0_eq : ∀ q < 4, dword (ivPair 2 ++ ivPair 0 : BitVec 128) q = ivAt q := by decide
theorem iv1_eq : ∀ q < 4, dword (ivPair 6 ++ ivPair 4 : BitVec 128) q = ivAt (4 + q) := by decide

theorem setup_eq : setup = ([.mov32 .r8 (.reg .r8)] : List Instr) ++
    (pair64 .xmm14 rot16Lo rot16Hi ++ (pair64 .xmm15 rotr8Lo rotr8Hi ++
      (pair64 .xmm11 (ivPair 0) (ivPair 2) ++ (pair64 .xmm12 (ivPair 4) (ivPair 6) ++
        ([.alu .test .r8 (.reg .r8)] : List Instr))))) := by
  simp only [setup, List.append_assoc]

/-- What a block of general-purpose instructions leaves: memory, permissions
and vector registers. -/
structure GF (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : t.xmm = s.xmm

theorem GF.trans {s t u : State} (h : GF s t) (h' : GF t u) : GF s u :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.xmm.trans h.xmm⟩

theorem Consts.of_gf {s t : State} (h : Consts s) (hg : GF s t) : Consts t :=
  ⟨⟨by rw [hg.xmm]; exact h.masks.m16, by rw [hg.xmm]; exact h.masks.m8⟩,
    fun q hq => by rw [hg.xmm]; exact h.iv0 q hq,
    fun q hq => by rw [hg.xmm]; exact h.iv1 q hq⟩

theorem setup_ok (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧
      t.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.zf = some (((s.gpr .r8).setWidth 32).setWidth 64 &&& ((s.gpr .r8).setWidth 32).setWidth 64 == 0) := by
  rw [setup_eq]
  apply WP.block_append
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  generalize hs0 : s.setReg .r8 (((s.gpr .r8).setWidth 32).setWidth 64) = s0
  have g0 : ∀ r, r ≠ .r8 → s0.gpr r = s.gpr r := fun r hr => by
    rw [← hs0, RegUpd.gpr_setReg, ifn hr]
  have r80 : s0.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := by
    rw [← hs0, RegUpd.gpr_setReg_self]
  have mem0 : s0.mem = s.mem := by rw [← hs0]; rfl
  have rd0 : s0.rd = s.rd := by rw [← hs0]; rfl
  have wr0 : s0.wr = s.wr := by rw [← hs0]; rfl
  apply WP.block_append
  refine (pair64_ok (d := .xmm14) (by decide) _ _ s0).mono fun u1 ⟨x1, g1, m1, rd1, wr1, k1⟩ => ?_
  apply WP.block_append
  refine (pair64_ok (d := .xmm15) (by decide) _ _ u1).mono fun u2 ⟨x2, g2, m2, rd2, wr2, k2⟩ => ?_
  apply WP.block_append
  refine (pair64_ok (d := .xmm11) (by decide) _ _ u2).mono fun u3 ⟨x3, g3, m3, rd3, wr3, k3⟩ => ?_
  apply WP.block_append
  refine (pair64_ok (d := .xmm12) (by decide) _ _ u3).mono fun u4 ⟨x4, g4, m4, rd4, wr4, k4⟩ => ?_
  have c4 : Consts u4 := by
    refine ⟨⟨?_, ?_⟩, fun q hq => ?_, fun q hq => ?_⟩
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), k2 _ (by decide) (by decide),
        x1, mask16_eq]
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), x2, mask8_eq]
    · rw [k4 _ (by decide) (by decide), x3]; exact iv0_eq q hq
    · rw [x4]; exact iv1_eq q hq
  have g4' : ∀ r, r ≠ .rax → u4.gpr r = s0.gpr r := fun r hr =>
    (g4 r hr).trans ((g3 r hr).trans ((g2 r hr).trans (g1 r hr)))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e8 : u4.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := (g4' _ (by decide)).trans r80
  refine ⟨c4.of_gf ⟨rfl, rfl, rfl, rfl⟩, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, e8]
  · exact (g4' r h1).trans (g0 r h2)
  · rw [m4, m3, m2, m1, mem0]
  · rw [rd4, rd3, rd2, rd1, rd0]
  · rw [wr4, wr3, wr2, wr1, wr0]

theorem flag_ok {s₀ s₁ : State} (h8 : s₁.gpr .r8 = ((s₀.gpr .r8).setWidth 32).setWidth 64)
    (hzf : s₁.zf = some (((s₀.gpr .r8).setWidth 32).setWidth 64 &&&
      ((s₀.gpr .r8).setWidth 32).setWidth 64 == 0)) :
    WP isa flag s₁ fun s₂ => s₂.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64 ∧
      s₂.zf = some (s₁.gpr .rdx &&& s₁.gpr .rdx == 0) ∧ (∀ r, r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧
      GF s₁ s₂ := by
  refine WP.seq (WP.mono (Q := fun s : State => s.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64 ∧
      (∀ r, r ≠ .r8 → s.gpr r = s₁.gpr r) ∧ GF s₁ s) ?_ fun s h => ?_)
  · refine WP.ite (!(fl s₀)) (by simp only [eval, hzf, zf_last]) (fun h => ?_) (fun h => ?_)
    · have hf : fl s₀ = false := by simpa using h
      refine WP.block_nil ⟨?_, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
      have hx : (s₀.gpr .r8).setWidth 32 = 0 := by simpa [fl] using hf
      rw [h8, hx, hf]; rfl
    · have hf : fl s₀ = true := by simpa using h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
        RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', hf]
      exact ⟨by decide, fun r h => by simp only [h, ite_false], rfl, rfl, rfl, rfl⟩
  · obtain ⟨h8', hg, hf⟩ := h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, hg .rdx (by decide), Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨h8', trivial, hg, hf.trans ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## The work vector -/

/-- The fourth row's counter and flag words, `(t₀, t₁, f, 0)`. -/
def ctr (T : Nat) (f : Bool) (q : Nat) : W :=
  if q = 0 then BitVec.ofNat 32 T else if q = 1 then BitVec.ofNat 32 (T / 2 ^ 32)
  else if q = 2 then flagW 32 f else 0

theorem ctr_dword (T : Nat) (f : Bool) {q : Nat} (hq : q < 4) :
    dword ((flagW 32 f).setWidth 64 ++ BitVec.ofNat 64 T) q = ctr T f q := by
  rw [dword_app _ _ hq]
  rcases cases4 hq with rfl | rfl | rfl | rfl
  · simp only [Nat.reduceLT, ↓reduceIte, Nat.mul_zero, ctr]
    exact lo32_ofNat T
  · simp only [Nat.reduceLT, ↓reduceIte, Nat.mul_one, ctr, Nat.one_ne_zero]
    exact hi32_ofNat T
  · simp only [Nat.reduceLT, ↓reduceIte, ctr, Nat.reduceSub, Nat.mul_zero, Nat.reduceEqDiff]
    cases f <;> decide
  · simp only [Nat.reduceLT, ↓reduceIte, ctr, Nat.reduceSub, Nat.mul_one, Nat.reduceEqDiff]
    cases f <;> decide

/-- A 16-byte load, word by word. -/
theorem mw_load16 (m : Mem) (st : Addr) {e q : Nat} (hq : q < 4) :
    dword (m.readW (st + BitVec.ofNat 64 e) 128) q = m.readW (st + BitVec.ofNat 64 (e + 4 * q)) 32 := by
  rw [dword_readW _ _ hq, Offset.add_add]

theorem init_ok {s : State} {st : Addr} {T : Nat} {f : Bool} (hdi : s.gpr .rdi = st)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 T) (h8 : s.gpr .r8 = (flagW 32 f).setWidth 64)
    (hc : Consts s)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 16)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 16) 16) :
    WP isa (.block init) s fun t =>
      words t = V0 Spec.Blake2.s (Spec.Blake2.stateAt 32 s.mem st) T f ∧
      XF [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm13] s t := by
  apply WP.of_runBlock
  simp only [init, v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_at, hdi,
    hin0, hin1, State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr => ?_⟩⟩
  · apply Vector.ext; intro j hj
    rw [words_get _ _ hj, V0_get _ _ _ _ _ hj]
    have hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
      simp only [row, dw, xmm_vbin, xmm_vmovq, xmm_vmovdqa, RegUpd.xmm_setV, VOp.exec_gpr,
        State.setV_gpr, ↓reduceIte, reduceCtorEq, VBinOp.sse]
    · rw [mw_load16 _ _ hq, dite_eq_left_of_eq_true (eq_true (by omega)), Spec.Blake2.stateAt,
        Vector.getElem_ofFn]
      exact congrArg (fun x => s.mem.readW (st + BitVec.ofNat 64 x) 32) (by dsimp only; omega)
    · rw [mw_load16 _ _ hq, dite_eq_left_of_eq_true (eq_true (by omega)), Spec.Blake2.stateAt,
        Vector.getElem_ofFn]
      exact congrArg (fun x => s.mem.readW (st + BitVec.ofNat 64 x) 32) (by dsimp only; omega)
    · rw [hc.iv0 _ hq, dite_eq_right_of_eq_false (eq_false (by omega)), ifn (by omega),
        ifn (by omega), ifn (by omega), ivAt, dite_eq_left_of_eq_true (eq_true (by omega))]
      simp only [show j % 4 = j - 8 by omega]
    · rw [dword_pxor, unpck_app, hcx, h8, ctr_dword _ _ hq, hc.iv1 _ hq,
        dite_eq_right_of_eq_false (eq_false (by omega))]
      have : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
      rcases this with rfl | rfl | rfl | rfl <;>
        simp only [ivAt, ctr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte,
          ↓reduceIte, Nat.reduceEqDiff]
      exact BitVec.xor_zero
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h13⟩ := hr
    simp only [xmm_vbin, xmm_vmovq, xmm_vmovdqa, RegUpd.xmm_setV, h0, h1, h2, h3, h4, h13,
      ite_false]

/-! ## The new state -/

/-- A read of a word of the state after a 16-byte store into it. -/
theorem read_write128 (m : Mem) (st : Addr) {d e : Nat} (hd : d + 4 ≤ 32) (he : e + 16 ≤ 32)
    (h4 : d % 4 = 0) (he4 : e % 4 = 0) (v : BitVec 128) :
    (m.writeW (st + BitVec.ofNat 64 e) v).readW (st + BitVec.ofNat 64 d) 32 =
      if e ≤ d ∧ d < e + 16 then dword v ((d - e) / 4) else m.readW (st + BitVec.ofNat 64 d) 32 := by
  split
  · rename_i h
    rw [show st + BitVec.ofNat 64 d = st + BitVec.ofNat 64 e + BitVec.ofNat 64 (4 * ((d - e) / 4)) from
      (Offset.add_add_eq st (by omega)).symm]
    refine (readW_writeW_inside _ _ v (k := 4 * ((d - e) / 4)) (n := 4) (by omega) (by decide)).trans ?_
    rw [dword_eq, show 8 * (4 * ((d - e) / 4)) = 32 * ((d - e) / 4) by omega]
  · exact VG.X86_64.readW_writeW_off m st v (n := 4) (by omega) (by omega) (by omega)

theorem finish_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 16)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 16) 16)
    (hout0 : InRegions s.wr (st + BitVec.ofNat 64 0) 16)
    (hout1 : InRegions s.wr (st + BitVec.ofNat 64 16) 16) :
    WP isa (.block finish) s fun t =>
      (∀ j (hj : j < 8), t.mem.readW (st + BitVec.ofNat 64 (4 * j)) 32 =
        s.mem.readW (st + BitVec.ofNat 64 (4 * j)) 32 ^^^ (words s)[j]'(Nat.lt_trans hj (by decide)) ^^^
          (words s)[j + 8]'(Nat.add_lt_add_right hj 8)) ∧
      Frame [⟨st, 32⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → t.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [finish, v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128,
    State.store128_eq, ea_at, hdi, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, VOp.exec_mem,
    xmm_vbin, RegUpd.xmm_setV, State.setMem_xmm, VBinOp.sse, ↓reduceIte, reduceCtorEq,
    State.setV_gpr, State.setV_rd, State.setV_wr, State.setV_mem, State.setMem_gpr,
    State.setMem_rd, State.setMem_wr, State.setMem_mem, hin0, hin1, hout0, hout1,
    Option.map_some, Option.some.injEq, exists_eq_left']
  have sep : (s.mem.writeW (st + 0#64)
      (XBinOp.eval .pxor (XBinOp.eval .pxor (s.xmm .xmm0) (s.xmm .xmm2))
        (s.mem.readW (st + 0#64) 128))).readW (st + 16#64) 128 =
      s.mem.readW (st + 16#64) 128 :=
    VG.X86_64.readW_writeW_off _ st _ (d := 16) (e := 0) (n := 16) (by omega) (by omega) (by omega)
  refine ⟨fun j hj => ?_, ?_, trivial, trivial, trivial, fun r h0 h1 h4 => ?_⟩
  · rw [read_write128 _ st (d := 4 * j) (e := 16) (by omega) (by omega) (by omega) (by omega)]
    by_cases hj4 : j < 4
    · rw [ifn (by omega), read_write128 _ st (d := 4 * j) (e := 0) (by omega) (by omega) (by omega)
        (by omega), ifp (by omega), Nat.sub_zero, show 4 * j / 4 = j by omega,
        words_get _ _ (by omega), words_get _ _ (by omega), show j / 4 = 0 by omega,
        show (j + 8) / 4 = 2 by omega, show j % 4 = j by omega, show (j + 8) % 4 = j by omega]
      simp only [row, dw, dword_pxor]
      rw [mw_load16 _ _ hj4, Nat.zero_add, BitVec.xor_comm _ (s.mem.readW _ 32), BitVec.xor_assoc]
    · rw [ifp (by omega), show (4 * j - 16) / 4 = j - 4 by omega,
        words_get _ _ (by omega), words_get _ _ (by omega), show j / 4 = 1 by omega,
        show (j + 8) / 4 = 3 by omega, show j % 4 = j - 4 by omega, show (j + 8) % 4 = j - 4 by omega]
      simp only [row, dw, dword_pxor]
      rw [sep, mw_load16 _ _ (by omega), show 16 + 4 * (j - 4) = 4 * j by omega,
        BitVec.xor_comm _ (s.mem.readW _ 32), BitVec.xor_assoc]
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))
  · simp only [h0, h1, h4, ite_false]

/-! ## The next block -/

theorem advance_ok {s : State} {T : Nat} (hcx : s.gpr .rcx = BitVec.ofNat 64 T) :
    WP isa (.block advance) s fun t => t.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 64 ∧
      t.gpr .rcx = BitVec.ofNat 64 (T + 64) ∧
      t.gpr .rdx = s.gpr .rdx - 1 ∧ t.zf = some (s.gpr .rdx - 1 == 0) ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧ GF s t := by
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, e64, e1,
    ↓reduceIte, reduceCtorEq, Option.bind_some, Option.some.injEq, exists_eq_left', hcx]
  refine ⟨trivial, ?_, trivial, trivial, fun r h1 h2 h3 => ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.ofNat_add_ofNat]
  · simp only [h1, h2, h3, ite_false]

/-! ## One block -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = blkAddr 32 s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 32)
  r8 : s.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64
  keep : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rax → r ≠ .rdx → r ≠ .r8 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR 32 s₀] s₀.mem s.mem
  state : Spec.Blake2.stateAt 32 s.mem (stA s₀) =
    Spec.Blake2.compressBlocks Spec.Blake2.s (H₀ 32 s₀) s₀.mem (bpA s₀) i (t₀ s₀) (fl s₀)
  consts : Consts s

namespace PreX
variable {s₀ : State} (hp : Pre 32 s₀)
include hp

theorem st_in {d : Nat} (hd : d + 16 ≤ 32) :
    InRegions (s₀.rd ++ s₀.wr) (stA s₀ + BitVec.ofNat 64 d) 16 :=
  ⟨stR 32 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega)⟩

theorem st_out {d : Nat} (hd : d + 16 ≤ 32) : InRegions s₀.wr (stA s₀ + BitVec.ofNat 64 d) 16 :=
  ⟨stR 32 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega)⟩

theorem blk_in {i : Nat} (hi : i < nb s₀) {k : Nat} (hk : k ≤ 12) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr 32 s₀ i + BitVec.ofNat 64 (4 * k)) 16 := by
  have := hp.nb_lt (.inr rfl)
  refine ⟨blR 32 s₀, by simp [hp.rd], ?_⟩
  rw [blkAddr, Offset.add_add]
  have hb : Spec.Blake2.blockBytes 32 = 64 := rfl
  rw [hb] at this ⊢
  exact Offset.contains_base _ (by rw [hb]; omega) (by omega)

/-- The block is not in the state. -/
theorem blk_frame {i : Nat} (hi : i < nb s₀) {m : Mem} (hf : Frame [stR 32 s₀] s₀.mem m) :
    Spec.Blake2.blockAt 32 m (blkAddr 32 s₀ i) = Spec.Blake2.blockAt 32 s₀.mem (blkAddr 32 s₀ i) := by
  have := hp.nb_lt (.inr rfl)
  funext j
  rw [show j = ⟨j.val, j.isLt⟩ from rfl, Proof.Blake2.blockAt_word _ _ _ j.isLt,
    Proof.Blake2.blockAt_word _ _ _ j.isLt]
  refine hf.readW (r := blR 32 s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [blkAddr, Offset.add_add]
    have hb : Spec.Blake2.blockBytes 32 = 64 := rfl
    rw [hb] at this ⊢
    exact Offset.contains_base _ (by rw [hb]; omega) (by omega)
  · simp only [List.mem_singleton] at hr
    subst hr; exact hp.bl_st

end PreX

theorem body_ok {s₀ : State} (hp : Pre 32 s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hc : Common s₀ i s) :
    WP isa body s fun s' =>
      Common s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) := by
  have hdi : s.gpr .rdi = stA s₀ := hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hc.rd, hc.wr]
  refine WP.seq ((init_ok hdi hc.rcx hc.r8 hc.consts (hrw ▸ PreX.st_in hp (by decide))
    (hrw ▸ PreX.st_in hp (by decide))).mono fun t1 ⟨w1, f1⟩ => ?_)
  have c1 := hc.consts.of_xf f1 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq ((rounds_ok 10 (pa := blkAddr 32 s₀ i)
    ⟨by rw [f1.gpr]; exact hc.rsi, fun k hk => by rw [f1.rd, f1.wr, hrw]; exact PreX.blk_in hp hi hk⟩
    c1.masks).mono fun t2 ⟨w2, f2, m2⟩ => ?_)
  have c2 := c1.of_xf f2 (by decide) (by decide) (by decide) (by decide)
  apply WP.block_append
  refine (finish_ok (st := stA s₀) (by rw [f2.gpr, f1.gpr]; exact hdi)
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreX.st_in hp (by decide))
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreX.st_in hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreX.st_out hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreX.st_out hp (by decide))).mono
    fun t3 ⟨x3, fr3, g3, rd3, wr3, l3⟩ => ?_
  have gs : ∀ r, t3.gpr r = s.gpr r := fun r => by rw [g3, f2.gpr, f1.gpr]
  refine (advance_ok (T := t₀ s₀ + i * Spec.Blake2.blockBytes 32) (by rw [gs]; exact hc.rcx)).mono fun t4 ⟨si4, cx4, dx4, zf4, g4, gf4⟩ => ?_
  have hb : Spec.Blake2.blockBytes 32 = 64 := rfl
  have dx : t4.gpr .rdx = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [dx4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]
  have mem2 : t2.mem = s.mem := f2.mem.trans f1.mem
  refine ⟨⟨?_, dx, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [si4, gs, hc.rsi]; exact Proof.Blake2.X86_64.blkAddr_succ (w := 32) s₀ i
  · rw [cx4, hb]; congr 1; omega
  · rw [g4 _ (by decide) (by decide) (by decide), gs]; exact hc.r8
  · rw [g4 _ h1 h2 h4, gs]; exact hc.keep r h1 h2 h3 h4 h5
  · rw [gf4.rd, rd3, f2.rd, f1.rd, hc.rd]
  · rw [gf4.wr, wr3, f2.wr, f1.wr, hc.wr]
  · rw [gf4.mem]
    exact hc.frame.trans (by rw [← mem2]; exact fr3)
  · rw [Proof.Blake2.compressBlocks_succ, ← hc.state, F_eq]
    apply Vector.ext; intro j hj
    rw [Vector.getElem_ofFn, Spec.Blake2.stateAt, Vector.getElem_ofFn, gf4.mem]
    simp only [Nat.reduceDiv]
    rw [x3 j hj, mem2, w2, w1, f1.mem, PreX.blk_frame hp hi hc.frame,
      show Spec.Blake2.s.r = 10 from rfl, Fin.getElem_fin, Fin.getElem_fin]
    have hst : (Spec.Blake2.stateAt 32 s.mem (stA s₀))[j] =
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32 := by
      simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, Nat.reduceDiv]
    rw [hst]
  · refine Consts.of_gf ⟨⟨?_, ?_⟩, fun q hq => ?_, fun q hq => ?_⟩ gf4
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.masks.m16
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.masks.m8
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.iv0 q hq
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.iv1 q hq
  · rw [zf4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]

/-! ## The whole function -/

theorem common0 {s₀ s₂ : State} (h8 : s₂.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64)
    (hg : ∀ r, r ≠ .rax → r ≠ .r8 → s₂.gpr r = s₀.gpr r)
    (hm : s₂.mem = s₀.mem) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr) (hc : Consts s₂) :
    Common s₀ 0 s₂ := by
  refine ⟨?_, ?_, ?_, h8, fun r _ _ h3 _ h5 => hg r h3 h5, hrd, hwr, ?_, ?_, hc⟩
  · rw [hg _ (by decide) (by decide), blkAddr, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [hg _ (by decide) (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hg _ (by decide) (by decide), Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hm]; exact Frame.refl _ _
  · rw [Proof.Blake2.compressBlocks_zero, hm]

theorem correct {s₀ : State} (hp : Pre 32 s₀) :
    WP isa compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ (compressX86_64 Spec.Blake2.s).post s₀ s' := by
  refine WP.seq ((setup_ok s₀).mono fun s₁ ⟨c1, r81, g1, m1, rd1, wr1, zf1⟩ => ?_)
  refine WP.seq ((flag_ok (s₀ := s₀) r81 zf1).mono fun s₂ ⟨r82, zf2, g2, f2⟩ => ?_)
  have hc₀ : Common s₀ 0 s₂ := common0 r82
    (fun r h1 h2 => (g2 r h2).trans (g1 r h1 h2))
    (f2.mem.trans m1) (f2.rd.trans rd1) (f2.wr.trans wr1) (c1.of_gf f2)
  have hdx : s₁.gpr .rdx = s₀.gpr .rdx := g1 _ (by decide) (by decide)
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₃ hc => ?_
  · refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp only [eval, zf2, hdx])
      (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp only [nb, h]; rfl
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Common s₀ i s
      have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
          (isa.eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
          (isa.eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hc⟩
        refine WP.mono (body_ok hp hi hc) fun s' ⟨hc', hz⟩ => ?_
        by_cases hlast : i + 1 = nb s₀
        · left
          refine ⟨?_, hlast ▸ hc'⟩
          simp only [eval, hz, ← hlast, Nat.sub_self, Option.map_some]; rfl
        · right
          have hne : nb s₀ - (i + 1) ≠ 0 := by omega
          refine ⟨?_, nb s₀ - (i + 1), by omega, i + 1, rfl, by omega, hc'⟩
          have h0 : (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) = false := by
            rw [beq_eq_false_iff_ne]
            intro h'
            have h'' := congrArg BitVec.toNat h'
            rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s₀.gpr .rdx).isLt)] at h''
            exact hne (h''.trans rfl)
          simp only [eval, hz, h0, Option.map_some]; rfl
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₂ ⟨0, rfl, hpos, hc₀⟩
  · refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hc.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
    · exact hc.state

/-! ## Results -/

theorem compress_correct (s : State) (hs : (compressX86_64 Spec.Blake2.s).pre s) :
    ∃ t s', Exec isa Impl.Blake2.X86_64.Avx.compress s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 Spec.Blake2.s).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem compress_ct : ConstantTime isa (compressX86_64 Spec.Blake2.s).pre
    (compressX86_64 Spec.Blake2.s).pub Impl.Blake2.X86_64.Avx.compress :=
  VG.Taint.constantTime (A := taint) (τ₀ 32) (fun _ _ h₁ h₂ hp => agree₀ (.inr rfl) h₁ h₂ hp)
    (by taint_decide)

theorem compress_verified :
    Verified X86_64.target Impl.Blake2.X86_64.Avx.compress (Spec.Blake2.compressSContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct (by
    sig_implies [Spec.Blake2.compressSContract, Spec.Blake2.compressSSig, compressX86_64,
      X86_64.abi, X86_64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 32)

end VG.Proof.Blake2.X86_64.Avx
