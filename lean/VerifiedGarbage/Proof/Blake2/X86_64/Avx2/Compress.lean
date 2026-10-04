import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Round
import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Compress

/-!
# BLAKE2b compression function on x86-64 with AVX2

The proof that `Impl.Blake2.X86_64.Avx2.compress` meets `compressX86_64 b`
(`Proof/Blake2/X86_64/Contract.lean`), as the scalar code does
(`Proof/Blake2/X86_64/Compress.lean`, whose description of the precondition
and of the work vector before the rounds, `V0`, this proof shares): the
masks and the IV in registers (`setup_ok`), then for each block the work
vector (`init_ok`), the rounds (`rounds_ok`), the XOR into the state
(`finish_ok`) and the next block (`advance_ok`). Constant time is checked
by evaluation.
-/

namespace VG.Proof.Blake2.X86_64.Avx2

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx2
open VG.Impl.Blake2.X86_64 (at_)
open VG.Proof.Blake2.X86_64 (Pre pre_of stA bpA nb t₀ fl scA stR blR H₀ blkAddr V0 V0_get F_eq
  flagW stateAt_get carry_ofNat zf_last τ₀ agree₀ satState off off_eq)
open VG.Proof.Argon2.X86_64.Avx2 (vrun Masks words words_get cases_div4 x0 x1 x2 x3 ifp ifn
  read_write256)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qw_vbin qw_lane qw_setV256 qw_setV128 qword_punpcklqdq
  qw_vmovq cases4)

/-- Word `q` of BLAKE2b's IV. -/
def ivAt (q : Nat) : W := if h : q < 8 then Spec.Blake2.b.IV[q] else 0

/-- The masks and the IV, in their registers. -/
structure Consts (s : State) : Prop where
  masks : Masks s
  iv0 : ∀ q < 4, qw s .xmm11 q = ivAt q
  iv1 : ∀ q < 4, qw s .xmm12 q = ivAt (4 + q)

theorem Consts.of_vf {rs : List XReg} {s t : State} (h : Consts s) (hv : VF rs s t)
    (h11 : .xmm11 ∉ rs) (h12 : .xmm12 ∉ rs) (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : Consts t :=
  ⟨masks_of_vf h.masks hv h14 h15, fun q hq => (qw_eq_of_vf hv h11 hq).trans (h.iv0 q hq),
    fun q hq => (qw_eq_of_vf hv h12 hq).trans (h.iv1 q hq)⟩

/-! ## Quadwords of registers after the other instructions -/

/-- What the set-up code leaves: everything but `rax`, the flags and the
vector registers `rs`. -/
structure SF (rs : List XReg) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  lane : ∀ r, r ∉ rs → ∀ l, t.lane r l = s.lane r l

theorem SF.trans {rs : List XReg} {s t u : State} (h : SF rs s t) (h' : SF rs t u) : SF rs s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, fun r hr l => (h'.lane r hr l).trans (h.lane r hr l)⟩

theorem SF.of_mem {rs rs' : List XReg} {s t : State} (h : SF rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    SF rs' s t := ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.lane r fun h' => hr (hs r h')⟩

theorem qw_eq_of_sf {rs : List XReg} {s t : State} (h : SF rs s t) {r : XReg} (hr : r ∉ rs) (k : Nat) :
    qw t r k = qw s r k := by
  simp only [qw, h.lane r hr (k / 2)]

theorem unpck_eq (lo hi : W) :
    XBinOp.punpcklqdq.eval ((0 : W) ++ lo) ((0 : W) ++ hi) = hi ++ lo := by
  apply VG.Proof.Argon2.X86_64.Avx2.eq_of_qwords <;>
    simp only [qword_punpcklqdq _ _ (show 0 < 2 by decide), qword_punpcklqdq _ _ (show 1 < 2 by decide),
      VG.Proof.Poly1305.X86_64.Avx2.qword_app0, VG.Proof.Poly1305.X86_64.Avx2.qword_app1,
      ↓reduceIte, Nat.one_ne_zero]

/-- `d := (lo, hi)` in its low 128 bits, through `rax` and `t`. -/
theorem pair_ok {d t : XReg} (hdt : d ≠ t) (lo hi : W) (s : State) :
    WP isa (.block (pair d t lo hi)) s fun u =>
      u.lane d 0 = hi ++ lo ∧ u.lane d 1 = 0 ∧ SF [d, t] s u := by
  apply WP.of_runBlock
  simp only [pair, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr l => ?_⟩⟩
  · simp only [VOp.exec, State.lane_setV128, RegUpd.gpr_setReg, ↓reduceIte, hdt,
      VG.Proof.Argon2.X86_64.Avx2.lane_setReg, VBinOp.sse]
    exact unpck_eq lo hi
  · simp only [VOp.exec, State.lane_setV128, ↓reduceIte, VG.Proof.Argon2.X86_64.Avx2.lane_setReg,
      Nat.one_ne_zero]
  · simp only [VOp.exec_gpr, RegUpd.gpr_setReg, hr, ite_false]
  · simp only [VOp.exec_mem, RegUpd.mem_setReg]
  · simp only [VOp.exec_rd, RegUpd.rd_setReg]
  · simp only [VOp.exec_wr, RegUpd.wr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VOp.exec, State.lane_setV128, VG.Proof.Argon2.X86_64.Avx2.lane_setReg, hr.1, hr.2,
      ite_false]

theorem qw_of_lanes {s : State} {r : XReg} {a b c e : W} (h0 : s.lane r 0 = b ++ a)
    (h1 : s.lane r 1 = e ++ c) :
    qw s r 0 = a ∧ qw s r 1 = b ∧ qw s r 2 = c ∧ qw s r 3 = e := by
  simp only [qw, Nat.reduceDiv, Nat.reduceMod, h0, h1, VG.Proof.Poly1305.X86_64.Avx2.qword_app0,
    VG.Proof.Poly1305.X86_64.Avx2.qword_app1, and_self]

/-- `d := (a, b, c, e)`, through `rax`, `ymm10` and `ymm13`. -/
theorem quad_ok {d : XReg} (hd10 : d ≠ .xmm10) (hd13 : d ≠ .xmm13) (a b c e : W) (s : State) :
    WP isa (.block (quad d a b c e)) s fun u =>
      (qw u d 0 = a ∧ qw u d 1 = b ∧ qw u d 2 = c ∧ qw u d 3 = e) ∧ SF [d, .xmm10, .xmm13] s u := by
  unfold quad
  rw [List.append_assoc]
  apply WP.block_append
  refine (pair_ok hd13 a b s).mono fun u1 ⟨l10, _, f1⟩ => ?_
  apply WP.block_append
  refine (pair_ok (by decide) c e u1).mono fun u2 ⟨l20, _, f2⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  have hd : u2.lane d 0 = b ++ a := (f2.lane d (by simp [hd10, hd13]) 0).trans l10
  refine ⟨qw_of_lanes ?_ ?_, ?_⟩
  · simp only [VOp.exec, show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte,
      State.lane_setV256, hd]
  · simp only [VOp.exec, show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte,
      State.lane_setV256, Nat.one_ne_zero]
    exact l20
  · refine (f1.of_mem (by simp)).trans ((f2.of_mem (by simp)).trans
      ⟨fun r _ => by rw [VOp.exec_gpr], VOp.exec_mem _ _, VOp.exec_rd _ _, VOp.exec_wr _ _,
        fun r hr l => ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VOp.exec, show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte,
      State.lane_setV256, hr.1]

theorem Consts.of_lanes {s t : State} (h : Consts s) (h11 : ∀ l, t.lane .xmm11 l = s.lane .xmm11 l)
    (h12 : ∀ l, t.lane .xmm12 l = s.lane .xmm12 l) (h14 : ∀ l, t.lane .xmm14 l = s.lane .xmm14 l)
    (h15 : ∀ l, t.lane .xmm15 l = s.lane .xmm15 l) : Consts t :=
  ⟨fun l hl => by rw [h14, h15]; exact h.masks l hl,
    fun k hk => (show qw t _ k = qw s _ k by simp only [qw, h11]).trans (h.iv0 k hk),
    fun k hk => (show qw t _ k = qw s _ k by simp only [qw, h12]).trans (h.iv1 k hk)⟩

theorem Consts.of_regs {s t : State} (h : Consts s) (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) :
    Consts t := by
  have e : ∀ r l, t.lane r l = s.lane r l := fun r l => by simp only [State.lane, hx, hy]
  have q : ∀ r k, qw t r k = qw s r k := fun r k => by simp only [qw, e]
  exact ⟨fun l hl => by rw [e, e]; exact h.masks l hl, fun k hk => (q _ _).trans (h.iv0 k hk),
    fun k hk => (q _ _).trans (h.iv1 k hk)⟩

theorem setup_eq : setup = ([.mov32 .r8 (.reg .r8)] : List Instr) ++
    (Impl.Argon2.X86_64.Avx2.masks ++ (quad .xmm11 (ivAt 0) (ivAt 1) (ivAt 2) (ivAt 3) ++
      (quad .xmm12 (ivAt 4) (ivAt 5) (ivAt 6) (ivAt 7) ++
        ([.mov32 .rax (.imm 0), .alu .test .r8 (.reg .r8)] : List Instr)))) := by
  simp only [setup, List.append_assoc]; rfl

theorem setup_ok (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧ t.gpr .rax = 0 ∧
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
  refine WP.mono (VG.Proof.Argon2.X86_64.Avx2.masks_ok s0) ?_
  rintro u1 ⟨m1, mem1, g1, rd1, wr1, -⟩
  apply WP.block_append
  refine (quad_ok (d := .xmm11) (by decide) (by decide) _ _ _ _ u1).mono fun u2 ⟨q2, f2⟩ => ?_
  apply WP.block_append
  refine (quad_ok (d := .xmm12) (by decide) (by decide) _ _ _ _ u2).mono fun u3 ⟨q3, f3⟩ => ?_
  have c3 : Consts u3 := by
    refine ⟨fun l hl => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [f3.lane _ (by decide), f3.lane _ (by decide), f2.lane _ (by decide), f2.lane _ (by decide)]
      exact m1 l hl
    · rw [qw_eq_of_sf f3 (by decide)]
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl
      exacts [q2.1, q2.2.1, q2.2.2.1, q2.2.2.2]
    · rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl
      exacts [q3.1, q3.2.1, q3.2.2.1, q3.2.2.2]
  have g3 : ∀ r, r ≠ .rax → u3.gpr r = s0.gpr r := fun r hr =>
    (f3.gpr r hr).trans ((f2.gpr r hr).trans (g1 r hr))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.setReg32, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  have e8 : u3.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := (g3 _ (by decide)).trans r80
  have m3 : u3.mem = s.mem := f3.mem.trans (f2.mem.trans (mem1.trans mem0))
  have rd3 : u3.rd = s.rd := f3.rd.trans (f2.rd.trans (rd1.trans rd0))
  have wr3 : u3.wr = s.wr := f3.wr.trans (f2.wr.trans (wr1.trans wr0))
  refine ⟨c3.of_regs rfl rfl, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, ↓reduceIte, reduceCtorEq, e8, m3, rd3, wr3]
  · rfl
  · simp only [h1, ite_false]; exact (g3 r h1).trans (g0 r h2)

/-- What a block of general-purpose instructions leaves: memory, permissions
and vector registers. -/
structure GF (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : t.xmm = s.xmm
  ymmHi : t.ymmHi = s.ymmHi

theorem GF.trans {s t u : State} (h : GF s t) (h' : GF t u) : GF s u :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.xmm.trans h.xmm,
    h'.ymmHi.trans h.ymmHi⟩

theorem flag_ok {s₀ s₁ : State} (h8 : s₁.gpr .r8 = ((s₀.gpr .r8).setWidth 32).setWidth 64)
    (hzf : s₁.zf = some (((s₀.gpr .r8).setWidth 32).setWidth 64 &&&
      ((s₀.gpr .r8).setWidth 32).setWidth 64 == 0)) :
    WP isa flag s₁ fun s₂ => s₂.gpr .r8 = flagW 64 (fl s₀) ∧
      s₂.zf = some (s₁.gpr .rdx &&& s₁.gpr .rdx == 0) ∧ (∀ r, r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧
      GF s₁ s₂ := by
  refine WP.seq (WP.mono (Q := fun s : State => s.gpr .r8 = flagW 64 (fl s₀) ∧
      (∀ r, r ≠ .r8 → s.gpr r = s₁.gpr r) ∧ GF s₁ s) ?_ fun s h => ?_)
  · refine WP.ite (!(fl s₀)) (by simp only [eval, hzf, zf_last]) (fun h => ?_) (fun h => ?_)
    · have hf : fl s₀ = false := by simpa using h
      refine WP.block_nil ⟨?_, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      have hx : (s₀.gpr .r8).setWidth 32 = 0 := by simpa [fl] using hf
      rw [h8, hx, hf]; rfl
    · have hf : fl s₀ = true := by simpa using h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, RegUpd.gpr_setReg,
        ite_true, Option.map_some, Option.some.injEq, exists_eq_left', hf]
      exact ⟨by decide, fun r h => by simp only [h, ite_false], rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨h8', hg, hf⟩ := h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
      RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, hg .rdx (by decide), Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨h8', trivial, hg, hf.trans ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## The work vector -/

def initOps : List VOp :=
  [.vmovdqa .l256 x2 .xmm11, .vmovq .xmm13 .rcx, .vmovq .xmm4 .rax,
    .vbin .vpunpcklqdq .l128 .xmm13 .xmm13 .xmm4, .vmovq .xmm4 .r8,
    .vinserti128 .xmm13 .xmm13 .xmm4 1, .vbin .vpxor .l256 x3 .xmm12 .xmm13]

theorem init_eq : init =
    ([.vmovdquLoad .l256 x0 (at_ .rdi 0), .vmovdquLoad .l256 x1 (at_ .rdi 32)] : List Instr) ++
      initOps.map .vop := rfl

/-- The fourth row's counter and flag: `ymm13` before the XOR. -/
theorem x13_lanes (s : State) :
    (vrun (initOps.take 6) s).lane .xmm13 0 = s.gpr .rax ++ s.gpr .rcx ∧
    (vrun (initOps.take 6) s).lane .xmm13 1 = (0 : W) ++ s.gpr .r8 := by
  simp only [initOps, List.take, vrun, VOp.exec, State.lane_setV128, State.lane_setV256,
    show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte, reduceCtorEq, Nat.one_ne_zero,
    VBinOp.sse, State.setV_gpr, RegUpd.xmm_setV]
  exact ⟨unpck_eq _ _, trivial⟩

theorem qword_pxor' (x y : BitVec 128) (i : Nat) :
    qword (XBinOp.eval .pxor x y) i = qword x i ^^^ qword y i :=
  VG.Proof.Argon2.X86_64.Avx2.qword_pxor x y i

/-- The rows after `initOps`, quadword by quadword. -/
theorem initOps_qw (s : State) {k : Nat} (hk : k < 4) :
    qw (vrun initOps s) x0 k = qw s x0 k ∧ qw (vrun initOps s) x1 k = qw s x1 k ∧
    qw (vrun initOps s) x2 k = qw s .xmm11 k ∧
    qw (vrun initOps s) x3 k = qw s .xmm12 k ^^^ qw (vrun (initOps.take 6) s) .xmm13 k := by
  have e : vrun initOps s = (VOp.vbin .vpxor .l256 x3 .xmm12 .xmm13).exec (vrun (initOps.take 6) s) :=
    rfl
  rw [e, qw_vbin, qw_vbin, qw_vbin, qw_vbin]
  simp only [↓reduceIte, reduceCtorEq, VBinOp.sse, qword_pxor', qw_lane]
  simp only [qw, initOps, List.take, vrun, VOp.exec, State.lane_setV128, State.lane_setV256,
    show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte, reduceCtorEq,
    VG.Proof.Poly1305.X86_64.Avx2.lane_sel _ _ hk, and_self]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, ofInt_natCast]

/-- The fourth row's counter and flag words, `(t₀, t₁, f, 0)`. -/
def ctr (T : Nat) (f : Bool) (q : Nat) : W :=
  if q = 0 then BitVec.ofNat 64 T else if q = 1 then BitVec.ofNat 64 (T / 2 ^ 64)
  else if q = 2 then flagW 64 f else 0

theorem init_ok {s : State} {st : Addr} {T : Nat} {f : Bool} (hdi : s.gpr .rdi = st)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 T) (hax : s.gpr .rax = BitVec.ofNat 64 (T / 2 ^ 64))
    (h8 : s.gpr .r8 = flagW 64 f) (hc : Consts s)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 32) 32) :
    WP isa (.block init) s fun t =>
      (∀ q < 4, qw t x0 q = s.mem.readW (st + BitVec.ofNat 64 (8 * q)) 64) ∧
      (∀ q < 4, qw t x1 q = s.mem.readW (st + BitVec.ofNat 64 (8 * (4 + q))) 64) ∧
      (∀ q < 4, qw t x2 q = ivAt q) ∧ (∀ q < 4, qw t x3 q = ivAt (4 + q) ^^^ ctr T f q) ∧
      VF [x0, x1, x2, x3, .xmm4, .xmm13] s t := by
  rw [init_eq]
  apply WP.block_append
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, ea_at, hdi, hin0,
    State.setV_gpr, State.setV_rd, State.setV_wr, State.setV_mem, hin1, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine block_vops_ok _ _ ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, ?_⟩
  · rw [(initOps_qw _ hq).1, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq,
      ifp rfl, VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, Offset.add_add, Nat.zero_add]
  · rw [(initOps_qw _ hq).2.1, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, Offset.add_add,
      show 32 + 8 * q = 8 * (4 + q) by omega]
  · rw [(initOps_qw _ hq).2.2.1, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq,
      ifn (by decide)]
    exact hc.iv0 q hq
  · rw [(initOps_qw _ hq).2.2.2, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq,
      ifn (by decide), hc.iv1 q hq]
    obtain ⟨l0, l1⟩ := x13_lanes ((s.setV .l256 x0 ((s.mem.readW (st + BitVec.ofNat 64 0) 256).extractLsb' 0 128)
      ((s.mem.readW (st + BitVec.ofNat 64 0) 256).extractLsb' 128 128)).setV .l256 x1
      ((s.mem.readW (st + BitVec.ofNat 64 32) 256).extractLsb' 0 128)
      ((s.mem.readW (st + BitVec.ofNat 64 32) 256).extractLsb' 128 128))
    obtain ⟨c0, c1, c2, c3⟩ := qw_of_lanes l0 l1
    simp only [State.setV_gpr, hcx, hax, h8] at c0 c1 c2
    rcases VG.X86_64.cases4 hq with rfl | rfl | rfl | rfl
    · rw [c0]; rfl
    · rw [c1]; rfl
    · rw [c2]; rfl
    · rw [c3]; rfl
  · refine ⟨by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_gpr, State.setV_gpr],
      by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_mem, State.setV_mem],
      by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_rd, State.setV_rd],
      by simp only [VG.Proof.Argon2.X86_64.Avx2.vrun_wr, State.setV_wr], fun r hr l _ => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h13⟩ := hr
    simp only [initOps, vrun, VOp.exec, State.lane_setV128, State.lane_setV256,
      show (1 : BitVec 8).getLsbD 0 = true from rfl, ↓reduceIte, h0, h1, h2, h3, h4, h13]

/-- The rows after `init` are the work vector before the rounds. -/
theorem words_init {t : State} {m : Mem} {st : Addr} {T : Nat} {f : Bool}
    (h0 : ∀ q < 4, qw t x0 q = m.readW (st + BitVec.ofNat 64 (8 * q)) 64)
    (h1 : ∀ q < 4, qw t x1 q = m.readW (st + BitVec.ofNat 64 (8 * (4 + q))) 64)
    (h2 : ∀ q < 4, qw t x2 q = ivAt q) (h3 : ∀ q < 4, qw t x3 q = ivAt (4 + q) ^^^ ctr T f q) :
    words t = V0 Spec.Blake2.b (Spec.Blake2.stateAt 64 m st) T f := by
  apply Vector.ext; intro j hj
  rw [words_get _ _ hj, V0_get _ _ _ _ _ hj]
  have hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [Impl.Argon2.X86_64.Avx2.vreg]
  · rw [h0 _ hq, dite_eq_left_of_eq_true (eq_true (by omega)), Spec.Blake2.stateAt,
      Vector.getElem_ofFn]
    exact congrArg (fun x => m.readW (st + BitVec.ofNat 64 x) 64) (by dsimp only; omega)
  · rw [h1 _ hq, dite_eq_left_of_eq_true (eq_true (by omega)), Spec.Blake2.stateAt,
      Vector.getElem_ofFn]
    exact congrArg (fun x => m.readW (st + BitVec.ofNat 64 x) 64) (by dsimp only; omega)
  · rw [h2 _ hq, dite_eq_right_of_eq_false (eq_false (by omega)), ifn (by omega), ifn (by omega),
      ifn (by omega), ivAt, dite_eq_left_of_eq_true (eq_true (by omega))]
    simp only [show j % 4 = j - 8 by omega]
  · rw [h3 _ hq, dite_eq_right_of_eq_false (eq_false (by omega))]
    have : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      simp only [ivAt, ctr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte,
        ↓reduceIte, Nat.reduceEqDiff]
    exact BitVec.xor_zero

/-! ## The new state -/

theorem qw_xor (s : State) (d a b r : XReg) (k : Nat) :
    qw ((VOp.vbin .vpxor .l256 d a b).exec s) r k = if r = d then qw s a k ^^^ qw s b k else qw s r k := by
  rw [qw_vbin]
  split
  · simp only [VBinOp.sse, qword_pxor', qw_lane]
  · rfl

theorem finish_eq : finish =
    ([v .vpxor x0 x0 x2, v .vpxor x1 x1 x3, .vmovdquLoad .l256 .xmm4 (at_ .rdi 0),
      v .vpxor x0 x0 .xmm4, .vmovdquStore .l256 (at_ .rdi 0) x0] : List Instr) ++
    ([.vmovdquLoad .l256 .xmm4 (at_ .rdi 32), v .vpxor x1 x1 .xmm4,
      .vmovdquStore .l256 (at_ .rdi 32) x1] : List Instr) := rfl

/-- The first half of the new state. -/
theorem finish0_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 32)
    (hout : InRegions s.wr (st + BitVec.ofNat 64 0) 32) :
    WP isa (.block [v .vpxor x0 x0 x2, v .vpxor x1 x1 x3, .vmovdquLoad .l256 .xmm4 (at_ .rdi 0),
      v .vpxor x0 x0 .xmm4, .vmovdquStore .l256 (at_ .rdi 0) x0]) s fun t => ∃ y : BitVec 256,
      (∀ q < 4, qword256 y q = qw s x0 q ^^^ qw s x2 q ^^^
        s.mem.readW (st + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * q)) 64) ∧
      t.mem = s.mem.writeW (st + BitVec.ofNat 64 0) y ∧
      (∀ q < 4, qw t x1 q = qw s x1 q ^^^ qw s x3 q) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ x0 → r ≠ x1 → r ≠ .xmm4 → ∀ l, t.lane r l = s.lane r l) := by
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, ea_at, hdi, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, VOp.exec_mem,
    State.setV_gpr, State.setV_wr, State.setV_mem, hin, hout, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, fun q hq => ?_, rfl, rfl, rfl, fun r h0 h1 h4 l => ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm _ _ hq, qw_xor, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, qw_xor, ifn (by decide), qw_xor, ifp rfl]
  · rw [VG.Proof.Argon2.X86_64.Avx2.qw_setMem, qw_xor, ifn (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide), qw_xor, ifp rfl, qw_xor,
      ifn (by decide), qw_xor, ifn (by decide)]
  · simp only [State.setMem_lane, lane_vbin256, State.lane_setV256, h0, h1, h4, ite_false]

/-- The second half of the new state. -/
theorem finish1_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 32) 32)
    (hout : InRegions s.wr (st + BitVec.ofNat 64 32) 32) :
    WP isa (.block [.vmovdquLoad .l256 .xmm4 (at_ .rdi 32), v .vpxor x1 x1 .xmm4,
      .vmovdquStore .l256 (at_ .rdi 32) x1]) s fun t => ∃ y : BitVec 256,
      (∀ q < 4, qword256 y q = qw s x1 q ^^^
        s.mem.readW (st + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * q)) 64) ∧
      t.mem = s.mem.writeW (st + BitVec.ofNat 64 32) y ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r, r ≠ x1 → r ≠ .xmm4 → ∀ l, t.lane r l = s.lane r l) := by
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, ea_at, hdi, VOp.exec_gpr, VOp.exec_wr, VOp.exec_mem,
    State.setV_gpr, State.setV_wr, State.setV_mem, hin, hout, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, rfl, rfl, rfl, fun r h1 h4 l => ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm _ _ hq, qw_xor, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifn (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ifp rfl,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq]
  · simp only [State.setMem_lane, lane_vbin256, State.lane_setV256, h1, h4, ite_false]

theorem finish_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 32) 32)
    (hout0 : InRegions s.wr (st + BitVec.ofNat 64 0) 32)
    (hout1 : InRegions s.wr (st + BitVec.ofNat 64 32) 32) :
    WP isa (.block finish) s fun t =>
      (∀ j (hj : j < 8), t.mem.readW (st + BitVec.ofNat 64 (8 * j)) 64 =
        s.mem.readW (st + BitVec.ofNat 64 (8 * j)) 64 ^^^ (words s)[j]'(Nat.lt_trans hj (by decide)) ^^^
          (words s)[j + 8]'(Nat.add_lt_add_right hj 8)) ∧
      Frame [⟨st, 64⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ x0 → r ≠ x1 → r ≠ .xmm4 → ∀ l, t.lane r l = s.lane r l) := by
  rw [finish_eq]
  apply WP.block_append
  refine (finish0_ok hdi hin0 hout0).mono fun u ⟨y0, hy0, m0, x1u, gu, rdu, wru, lu⟩ => ?_
  refine (finish1_ok (st := st) (by rw [gu]; exact hdi) (by rw [rdu, wru]; exact hin1)
    (by rw [wru]; exact hout1)).mono fun t ⟨y1, hy1, m1, gt, rdt, wrt, lt⟩ => ?_
  have u32 : ∀ q < 4, u.mem.readW (st + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * q)) 64 =
      s.mem.readW (st + BitVec.ofNat 64 (8 * (4 + q))) 64 := fun q hq => by
    rw [Offset.add_add, m0, show 32 + 8 * q = 8 * (4 + q) by omega,
      read_write256 _ st (d := 8 * (4 + q)) (e := 0) (by omega) (by omega) (by omega) (by omega),
      ifn (by omega)]
  refine ⟨fun j hj => ?_, ?_, gt.trans gu, rdt.trans rdu, wrt.trans wru, fun r h0 h1 h4 l =>
    (lt r h1 h4 l).trans (lu r h0 h1 h4 l)⟩
  · rw [m1, read_write256 _ st (d := 8 * j) (e := 32) (by omega) (by omega) (by omega) (by omega)]
    by_cases hj4 : j < 4
    · rw [ifn (by omega), m0,
        read_write256 _ st (d := 8 * j) (e := 0) (by omega) (by omega) (by omega) (by omega), ifp (by omega),
        Nat.sub_zero, show 8 * j / 8 = j by omega, hy0 j hj4, Offset.add_add, Nat.zero_add,
        words_get _ _ (by omega), words_get _ _ (by omega), show j / 4 = 0 by omega,
        show (j + 8) / 4 = 2 by omega, show j % 4 = j by omega, show (j + 8) % 4 = j by omega]
      simp only [Impl.Argon2.X86_64.Avx2.vreg]
      rw [BitVec.xor_comm _ (s.mem.readW _ 64), BitVec.xor_assoc]
    · rw [ifp (by omega), show (8 * j - 32) / 8 = j - 4 by omega, hy1 _ (by omega), x1u _ (by omega),
        u32 _ (by omega), show 4 + (j - 4) = j by omega,
        words_get _ _ (by omega), words_get _ _ (by omega), show j / 4 = 1 by omega,
        show (j + 8) / 4 = 3 by omega, show j % 4 = j - 4 by omega, show (j + 8) % 4 = j - 4 by omega]
      simp only [Impl.Argon2.X86_64.Avx2.vreg]
      rw [BitVec.xor_comm _ (s.mem.readW _ 64), BitVec.xor_assoc]
  · rw [m1, m0]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))

/-! ## The next block -/

theorem advance_ok {s : State} {T : Nat} (hcx : s.gpr .rcx = BitVec.ofNat 64 T)
    (hax : s.gpr .rax = BitVec.ofNat 64 (T / 2 ^ 64)) :
    WP isa (.block advance) s fun t => t.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 128 ∧
      t.gpr .rcx = BitVec.ofNat 64 (T + 128) ∧ t.gpr .rax = BitVec.ofNat 64 ((T + 128) / 2 ^ 64) ∧
      t.gpr .rdx = s.gpr .rdx - 1 ∧ t.zf = some (s.gpr .rdx - 1 == 0) ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ GF s t := by
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  have e0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    RegUpd.zf_setReg, RegUpd.zf_arithFlags, e128, e0, e1, ↓reduceIte, reduceCtorEq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', hcx, hax]
  refine ⟨trivial, ?_, ?_, trivial, trivial, fun r h1 h2 h3 h4 => ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.ofNat_add_ofNat]
  · rw [show ∀ x : W, x + (0 : W) = x from fun x => BitVec.add_zero x]
    exact carry_ofNat T 128 (by decide)
  · simp only [h1, h2, h3, h4, ite_false]

/-! ## One block -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = blkAddr 64 s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 64)
  rax : s.gpr .rax = BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes 64) / 2 ^ 64)
  r8 : s.gpr .r8 = flagW 64 (fl s₀)
  keep : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rax → r ≠ .rdx → r ≠ .r8 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR 64 s₀] s₀.mem s.mem
  state : Spec.Blake2.stateAt 64 s.mem (stA s₀) =
    Spec.Blake2.compressBlocks Spec.Blake2.b (H₀ 64 s₀) s₀.mem (bpA s₀) i (t₀ s₀) (fl s₀)
  consts : Consts s

namespace PreY
variable {s₀ : State} (hp : Pre 64 s₀)
include hp

theorem st_in {d : Nat} (hd : d + 32 ≤ 64) :
    InRegions (s₀.rd ++ s₀.wr) (stA s₀ + BitVec.ofNat 64 d) 32 :=
  ⟨stR 64 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega)⟩

theorem st_out {d : Nat} (hd : d + 32 ≤ 64) : InRegions s₀.wr (stA s₀ + BitVec.ofNat 64 d) 32 :=
  ⟨stR 64 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega)⟩

theorem blk_in {i : Nat} (hi : i < nb s₀) {k : Nat} (hk : k ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr 64 s₀ i + BitVec.ofNat 64 (8 * k)) 16 := by
  have := hp.nb_lt (.inl rfl)
  refine ⟨blR 64 s₀, by simp [hp.rd], ?_⟩
  rw [blkAddr, Offset.add_add]
  have hb : Spec.Blake2.blockBytes 64 = 128 := rfl
  rw [hb] at this ⊢
  exact Offset.contains_base _ (by rw [hb]; omega) (by omega)

/-- The block is not in the state. -/
theorem blk_frame {i : Nat} (hi : i < nb s₀) {m : Mem} (hf : Frame [stR 64 s₀] s₀.mem m) :
    Spec.Blake2.blockAt 64 m (blkAddr 64 s₀ i) = Spec.Blake2.blockAt 64 s₀.mem (blkAddr 64 s₀ i) := by
  have := hp.nb_lt (.inl rfl)
  funext j
  rw [show j = ⟨j.val, j.isLt⟩ from rfl, Proof.Blake2.blockAt_word _ _ _ j.isLt,
    Proof.Blake2.blockAt_word _ _ _ j.isLt]
  refine hf.readW (r := blR 64 s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [blkAddr, Offset.add_add]
    have hb : Spec.Blake2.blockBytes 64 = 128 := rfl
    rw [hb] at this ⊢
    exact Offset.contains_base _ (by rw [hb]; omega) (by omega)
  · simp only [List.mem_singleton] at hr
    subst hr; exact hp.bl_st

end PreY

theorem body_ok {s₀ : State} (hp : Pre 64 s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hc : Common s₀ i s) :
    WP isa body s fun s' =>
      Common s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) := by
  have hdi : s.gpr .rdi = stA s₀ := hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hc.rd, hc.wr]
  refine WP.seq ((init_ok hdi hc.rcx hc.rax hc.r8 hc.consts (hrw ▸ PreY.st_in hp (by decide))
    (hrw ▸ PreY.st_in hp (by decide))).mono fun t1 ⟨h0, h1, h2, h3, f1⟩ => ?_)
  have w1 := words_init h0 h1 h2 h3
  have c1 := hc.consts.of_vf f1 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq ((rounds_ok 12 (p := blkAddr 64 s₀ i) (by rw [f1.gpr]; exact hc.rsi)
    (fun k hk => by rw [f1.rd, f1.wr, hrw]; exact PreY.blk_in hp hi hk) c1.masks).mono
    fun t2 ⟨w2, f2, m2⟩ => ?_)
  have c2 := c1.of_vf f2 (by decide) (by decide) (by decide) (by decide)
  apply WP.block_append
  refine (finish_ok (st := stA s₀) (by rw [f2.gpr, f1.gpr]; exact hdi)
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreY.st_in hp (by decide))
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreY.st_in hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreY.st_out hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreY.st_out hp (by decide))).mono
    fun t3 ⟨x3, fr3, g3, rd3, wr3, l3⟩ => ?_
  have cx3 : t3.gpr .rcx = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 64) := by
    rw [g3, f2.gpr, f1.gpr]; exact hc.rcx
  have ax3 : t3.gpr .rax = BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes 64) / 2 ^ 64) := by
    rw [g3, f2.gpr, f1.gpr]; exact hc.rax
  refine (advance_ok cx3 ax3).mono fun t4 ⟨si4, cx4, ax4, dx4, zf4, g4, gf4⟩ => ?_
  have hb : Spec.Blake2.blockBytes 64 = 128 := rfl
  have gs : ∀ r, t3.gpr r = s.gpr r := fun r => by rw [g3, f2.gpr, f1.gpr]
  have dx : t4.gpr .rdx = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [dx4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]
  have mem2 : t2.mem = s.mem := f2.mem.trans f1.mem
  refine ⟨⟨?_, dx, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [si4, gs, hc.rsi]; exact Proof.Blake2.X86_64.blkAddr_succ (w := 64) s₀ i
  · rw [cx4, hb]; congr 1; omega
  · rw [ax4, hb, show t₀ s₀ + i * 128 + 128 = t₀ s₀ + (i + 1) * 128 by omega]
  · rw [g4 _ (by decide) (by decide) (by decide) (by decide), gs]; exact hc.r8
  · rw [g4 _ h1 h2 h3 h4, gs]; exact hc.keep r h1 h2 h3 h4 h5
  · rw [gf4.rd, rd3, f2.rd, f1.rd, hc.rd]
  · rw [gf4.wr, wr3, f2.wr, f1.wr, hc.wr]
  · rw [gf4.mem]
    exact hc.frame.trans (by rw [← mem2]; exact fr3)
  · rw [Proof.Blake2.compressBlocks_succ, ← hc.state, F_eq]
    apply Vector.ext; intro j hj
    rw [Vector.getElem_ofFn, Spec.Blake2.stateAt, Vector.getElem_ofFn, gf4.mem]
    simp only [Nat.reduceDiv]
    rw [x3 j hj, mem2, w2, w1, f1.mem, PreY.blk_frame hp hi hc.frame,
      show Spec.Blake2.b.r = 12 from rfl, Fin.getElem_fin, Fin.getElem_fin]
    have hst : (Spec.Blake2.stateAt 64 s.mem (stA s₀))[j] =
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * j)) 64 := by
      simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, Nat.reduceDiv]
    rw [hst]
  · exact (c2.of_lanes (l3 _ (by decide) (by decide) (by decide))
      (l3 _ (by decide) (by decide) (by decide)) (l3 _ (by decide) (by decide) (by decide))
      (l3 _ (by decide) (by decide) (by decide))).of_regs gf4.xmm gf4.ymmHi
  · rw [zf4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]

/-! ## The whole function -/

theorem common0 {s₀ s₂ : State} (h8 : s₂.gpr .r8 = flagW 64 (fl s₀))
    (hg : ∀ r, r ≠ .rax → r ≠ .r8 → s₂.gpr r = s₀.gpr r) (hax : s₂.gpr .rax = 0)
    (hm : s₂.mem = s₀.mem) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr) (hc : Consts s₂) :
    Common s₀ 0 s₂ := by
  refine ⟨?_, ?_, ?_, ?_, h8, fun r _ _ h3 _ h5 => hg r h3 h5, hrd, hwr, ?_, ?_, hc⟩
  · rw [hg _ (by decide) (by decide), blkAddr, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [hg _ (by decide) (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hg _ (by decide) (by decide), Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hax, Nat.zero_mul, Nat.add_zero, Nat.div_eq_of_lt (s₀.gpr .rcx).isLt]; rfl
  · rw [hm]; exact Frame.refl _ _
  · rw [Proof.Blake2.compressBlocks_zero, hm]

theorem correct {s₀ : State} (hp : Pre 64 s₀) :
    WP isa compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ (compressX86_64 Spec.Blake2.b).post s₀ s' := by
  refine WP.seq ((setup_ok s₀).mono fun s₁ ⟨c1, ax1, r81, g1, m1, rd1, wr1, zf1⟩ => ?_)
  refine WP.seq ((flag_ok (s₀ := s₀) r81 zf1).mono fun s₂ ⟨r82, zf2, g2, f2⟩ => ?_)
  have hc₀ : Common s₀ 0 s₂ := common0 r82
    (fun r h1 h2 => (g2 r h2).trans (g1 r h1 h2)) ((g2 _ (by decide)).trans ax1)
    (f2.mem.trans m1) (f2.rd.trans rd1) (f2.wr.trans wr1) (c1.of_regs f2.xmm f2.ymmHi)
  have hdx : s₁.gpr .rdx = s₀.gpr .rdx := g1 _ (by decide) (by decide)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₃ hc => ?_)
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
  · refine (VG.Proof.Argon2.X86_64.Avx2.vzeroupper_ok s₃).mono fun s' ⟨m', g', _, _, _⟩ => ?_
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · rw [g']
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [m']
      exact hc.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
    · show Spec.Blake2.stateAt _ _ _ = _
      rw [m']; exact hc.state

/-! ## Results -/

theorem compress_correct (s : State) (hs : (compressX86_64 Spec.Blake2.b).pre s) :
    ∃ t s', Exec isa Impl.Blake2.X86_64.Avx2.compress s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 Spec.Blake2.b).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem compress_ct : ConstantTime isa (compressX86_64 Spec.Blake2.b).pre
    (compressX86_64 Spec.Blake2.b).pub Impl.Blake2.X86_64.Avx2.compress :=
  VG.Taint.constantTime (A := taint) (τ₀ 64) (fun _ _ h₁ h₂ hp => agree₀ (.inl rfl) h₁ h₂ hp)
    (by taint_decide)

theorem compress_verified :
    Verified X86_64.target Impl.Blake2.X86_64.Avx2.compress (Spec.Blake2.compressBContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct (by
    sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, compressX86_64,
      X86_64.abi, X86_64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 64)

end VG.Proof.Blake2.X86_64.Avx2
