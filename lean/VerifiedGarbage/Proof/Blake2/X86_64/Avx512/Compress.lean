import VerifiedGarbage.Proof.Blake2.X86_64.Avx512.Round
import VerifiedGarbage.Proof.Blake2.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Compress

/-!
# BLAKE2b compression function on x86-64 with AVX-512

The proof that `Impl.Blake2.X86_64.Avx512.compress` meets `compressX86_64 b`
(`Proof/Blake2/X86_64/Contract.lean`), as the AVX2 code does
(`Proof/Blake2/X86_64/Avx2/Compress.lean`, whose proofs of the code the two
share, the work vector, `init_ok`, the XOR into the state, `Avx2.finish_ok`, and
the next block, `Avx2.advance_ok`, this proof uses): the IV in registers
(`setup_ok`), then for each block the work vector, the rounds (`rounds_ok`),
the XOR into the state and the next block. There are no masks to keep.
Constant time is checked by evaluation.
-/

namespace VG.Proof.Blake2.X86_64.Avx512

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx512
open VG.Impl.Blake2.X86_64 (at_)
open VG.Impl.Blake2.X86_64.Avx2 (quad)
open VG.Proof.Blake2.X86_64 (Pre pre_of stA bpA nb t₀ fl scA stR blR H₀ blkAddr V0 V0_get F_eq
  flagW stateAt_get carry_ofNat zf_last τ₀ agree₀ satState off off_eq)
open VG.Proof.Argon2.X86_64.Avx2 (vrun words words_get cases_div4 x0 x1 x2 x3 ifp ifn
  read_write256)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qw_vbin qw_lane qw_setV256 qw_setV128 qword_punpcklqdq
  qw_vmovq cases4)
open VG.Proof.Blake2.X86_64.Avx2 (W VF qw_eq_of_vf ivAt SF qw_eq_of_sf quad_ok GF initOps initOps_qw
  x13_lanes qw_of_lanes ctr words_init roundRegs block_vops_ok)

/-- The IV, in its registers. -/
structure Consts (s : State) : Prop where
  iv0 : ∀ q < 4, qw s .xmm11 q = ivAt q
  iv1 : ∀ q < 4, qw s .xmm12 q = ivAt (4 + q)

theorem Consts.of_vf {rs : List XReg} {s t : State} (h : Consts s) (hv : VF rs s t)
    (h11 : .xmm11 ∉ rs) (h12 : .xmm12 ∉ rs) : Consts t :=
  ⟨fun q hq => (qw_eq_of_vf hv h11 hq).trans (h.iv0 q hq),
    fun q hq => (qw_eq_of_vf hv h12 hq).trans (h.iv1 q hq)⟩

theorem Consts.of_lanes {s t : State} (h : Consts s) (h11 : ∀ l, t.lane .xmm11 l = s.lane .xmm11 l)
    (h12 : ∀ l, t.lane .xmm12 l = s.lane .xmm12 l) : Consts t :=
  ⟨fun k hk => (show qw t _ k = qw s _ k by simp only [qw, h11]).trans (h.iv0 k hk),
    fun k hk => (show qw t _ k = qw s _ k by simp only [qw, h12]).trans (h.iv1 k hk)⟩

theorem Consts.of_regs {s t : State} (h : Consts s) (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) :
    Consts t := by
  have e : ∀ r l, t.lane r l = s.lane r l := fun r l => by simp only [State.lane, hx, hy]
  have q : ∀ r k, qw t r k = qw s r k := fun r k => by simp only [qw, e]
  exact ⟨fun k hk => (q _ _).trans (h.iv0 k hk), fun k hk => (q _ _).trans (h.iv1 k hk)⟩

theorem setup_eq : Impl.Blake2.X86_64.Avx512.setup = ([.mov32 .r8 (.reg .r8)] : List Instr) ++
    (quad .xmm11 (ivAt 0) (ivAt 1) (ivAt 2) (ivAt 3) ++
      (quad .xmm12 (ivAt 4) (ivAt 5) (ivAt 6) (ivAt 7) ++
        ([.mov32 .rax (.imm 0), .alu .test .r8 (.reg .r8)] : List Instr))) := by
  simp only [Impl.Blake2.X86_64.Avx512.setup, List.append_assoc]; rfl

theorem setup_ok (s : State) :
    WP isa (.block Impl.Blake2.X86_64.Avx512.setup) s fun t => Consts t ∧ t.gpr .rax = 0 ∧
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
  refine (quad_ok (d := .xmm11) (by decide) (by decide) _ _ _ _ s0).mono fun u2 ⟨q2, f2⟩ => ?_
  apply WP.block_append
  refine (quad_ok (d := .xmm12) (by decide) (by decide) _ _ _ _ u2).mono fun u3 ⟨q3, f3⟩ => ?_
  have c3 : Consts u3 := by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [qw_eq_of_sf f3 (by decide)]
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl
      exacts [q2.1, q2.2.1, q2.2.2.1, q2.2.2.2]
    · rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl
      exacts [q3.1, q3.2.1, q3.2.2.1, q3.2.2.2]
  have g3 : ∀ r, r ≠ .rax → u3.gpr r = s0.gpr r := fun r hr => (f3.gpr r hr).trans (f2.gpr r hr)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.setReg32, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  have e8 : u3.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := (g3 _ (by decide)).trans r80
  have m3 : u3.mem = s.mem := f3.mem.trans (f2.mem.trans mem0)
  have rd3 : u3.rd = s.rd := f3.rd.trans (f2.rd.trans rd0)
  have wr3 : u3.wr = s.wr := f3.wr.trans (f2.wr.trans wr0)
  refine ⟨c3.of_regs rfl rfl, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, ↓reduceIte, reduceCtorEq, e8, m3, rd3, wr3]
  · rfl
  · simp only [h1, ite_false]; exact (g3 r h1).trans (g0 r h2)

/-! ## The work vector -/

theorem init_ok {s : State} {st : Addr} {T : Nat} {f : Bool} (hdi : s.gpr .rdi = st)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 T) (hax : s.gpr .rax = BitVec.ofNat 64 (T / 2 ^ 64))
    (h8 : s.gpr .r8 = flagW 64 f) (hc : Consts s)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 32) 32) :
    WP isa (.block Impl.Blake2.X86_64.Avx2.init) s fun t =>
      (∀ q < 4, qw t x0 q = s.mem.readW (st + BitVec.ofNat 64 (8 * q)) 64) ∧
      (∀ q < 4, qw t x1 q = s.mem.readW (st + BitVec.ofNat 64 (8 * (4 + q))) 64) ∧
      (∀ q < 4, qw t x2 q = ivAt q) ∧ (∀ q < 4, qw t x3 q = ivAt (4 + q) ^^^ ctr T f q) ∧
      VF [x0, x1, x2, x3, .xmm4, .xmm13] s t := by
  rw [Avx2.init_eq]
  apply WP.block_append
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, Avx2.ea_at, hdi, hin0,
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


/-! ## One block -/

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


theorem body_ok {s₀ : State} (hp : Pre 64 s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hc : Common s₀ i s) :
    WP isa Impl.Blake2.X86_64.Avx512.body s fun s' =>
      Common s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) := by
  have hdi : s.gpr .rdi = stA s₀ := hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hc.rd, hc.wr]
  refine WP.seq ((init_ok hdi hc.rcx hc.rax hc.r8 hc.consts (hrw ▸ Avx2.PreY.st_in hp (by decide))
    (hrw ▸ Avx2.PreY.st_in hp (by decide))).mono fun t1 ⟨h0, h1, h2, h3, f1⟩ => ?_)
  have w1 := words_init h0 h1 h2 h3
  have c1 := hc.consts.of_vf f1 (by decide) (by decide)
  refine WP.seq ((rounds_ok 12 (p := blkAddr 64 s₀ i) (by rw [f1.gpr]; exact hc.rsi)
    (fun k hk => by rw [f1.rd, f1.wr, hrw]; exact Avx2.PreY.blk_in hp hi hk)).mono
    fun t2 ⟨w2, f2⟩ => ?_)
  have c2 := c1.of_vf f2 (by decide) (by decide)
  apply WP.block_append
  refine (Avx2.finish_ok (st := stA s₀) (by rw [f2.gpr, f1.gpr]; exact hdi)
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact Avx2.PreY.st_in hp (by decide))
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact Avx2.PreY.st_in hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact Avx2.PreY.st_out hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact Avx2.PreY.st_out hp (by decide))).mono
    fun t3 ⟨x3, fr3, g3, rd3, wr3, l3⟩ => ?_
  have cx3 : t3.gpr .rcx = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 64) := by
    rw [g3, f2.gpr, f1.gpr]; exact hc.rcx
  have ax3 : t3.gpr .rax = BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes 64) / 2 ^ 64) := by
    rw [g3, f2.gpr, f1.gpr]; exact hc.rax
  refine (Avx2.advance_ok cx3 ax3).mono fun t4 ⟨si4, cx4, ax4, dx4, zf4, g4, gf4⟩ => ?_
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
    rw [x3 j hj, mem2, w2, w1, f1.mem, Avx2.PreY.blk_frame hp hi hc.frame,
      show Spec.Blake2.b.r = 12 from rfl, Fin.getElem_fin, Fin.getElem_fin]
    have hst : (Spec.Blake2.stateAt 64 s.mem (stA s₀))[j] =
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * j)) 64 := by
      simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, Nat.reduceDiv]
    rw [hst]
  · exact (c2.of_lanes (l3 _ (by decide) (by decide) (by decide))
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
    WP isa Impl.Blake2.X86_64.Avx512.compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ (compressX86_64 Spec.Blake2.b).post s₀ s' := by
  refine WP.seq ((setup_ok s₀).mono fun s₁ ⟨c1, ax1, r81, g1, m1, rd1, wr1, zf1⟩ => ?_)
  refine WP.seq ((Avx2.flag_ok (s₀ := s₀) r81 zf1).mono fun s₂ ⟨r82, zf2, g2, f2⟩ => ?_)
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
      have hstep : ∀ m s, Inv m s → WP isa Impl.Blake2.X86_64.Avx512.body s (fun s' =>
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
    ∃ t s', Exec isa Impl.Blake2.X86_64.Avx512.compress s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 Spec.Blake2.b).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem compress_ct : ConstantTime isa (compressX86_64 Spec.Blake2.b).pre
    (compressX86_64 Spec.Blake2.b).pub Impl.Blake2.X86_64.Avx512.compress :=
  VG.Taint.constantTime (A := taint) (τ₀ 64) (fun _ _ h₁ h₂ hp => agree₀ (.inl rfl) h₁ h₂ hp)
    (by taint_decide)

theorem compress_verified :
    Verified X86_64.target Impl.Blake2.X86_64.Avx512.compress (Spec.Blake2.compressBContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct (by
    sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, compressX86_64,
      X86_64.abi, X86_64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 64)


end VG.Proof.Blake2.X86_64.Avx512
