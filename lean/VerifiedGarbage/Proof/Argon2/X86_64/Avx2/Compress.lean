import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Ends
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# Verified Argon2 block compression on x86-64 with AVX2

`vg_argon2_compress_avx2` meets `compressContract`, as `vg_argon2_compress`
does: the masks, the initial XOR (`init_prefix`), the eight rows and eight
columns (`row_ok`, `col_ok`) and the final XOR (`finish_prefix`) compose to
`Spec.Argon2.compress`, between Intel's MXCSR prologue and epilogue, which
keep MXCSR's control bits (`ctlOk`). Constant time is checked by evaluation,
as for the scalar code.
-/

namespace VG.Proof.Argon2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx2
open VG.Proof.Argon2.X86_64 (off word working working_get Scratch ea_at Inputs blockAt_get
  xorBlock_get compressLocal initial_agree initialTaint compress_implies original_preserved
  round_frame)
open VG.Proof.Argon2 (rowIndex_injective colIndex_injective)
open VG.Proof.Poly1305.X86_64.Avx2 (qword256_perm sel4 qword_app0 qword_app1)

/-! ## The masks -/

theorem eq_of_qwords {a b : BitVec 128} (h0 : qword a 0 = qword b 0) (h1 : qword a 1 = qword b 1) :
    a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : i < 64
  · have := congrArg (·.getLsbD i) h0
    simpa [qword, h] using this
  · have := congrArg (·.getLsbD (i - 64)) h1
    simp [qword, show i - 64 < 64 by omega] at this
    rwa [show 64 + (i - 64) = i by omega] at this

theorem qword_ext (Y : BitVec 256) (k : Nat) {i : Nat} (hi : i < 2) :
    qword (Y.extractLsb' (128 * k) 128) i = qword256 Y (2 * k + i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * i + j < 128 by omega)]
  congr 1; omega

theorem qword256_lo (z : BitVec 128) {i : Nat} (hi : i < 2) : qword256 (0#128 ++ z) i = qword z i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    BitVec.getLsbD_append, show 64 * i + j < 128 by omega, ite_true]

theorem ext_zero_app (x : BitVec 64) : BitVec.extractLsb' 0 64 (0#64 ++ x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
    Nat.zero_add, ite_true]

theorem perm44 (lo hi : BitVec 64) {k : Nat} (hk : k < 2) :
    (permQwords (0#128 ++ (BitVec.extractLsb' 0 64 (0#64 ++ hi) ++ BitVec.extractLsb' 0 64 (0#64 ++ lo))) 0x44).extractLsb' (128 * k) 128 = hi ++ lo := by
  have e : ∀ i < 2, sel4 (0x44 : BitVec 8).toNat (2 * k + i) = i := by
    intro i hi; rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  apply eq_of_qwords
  · rw [qword_ext _ _ (by decide), qword256_perm _ _ (by omega), e 0 (by decide),
      qword256_lo _ (by decide)]
    simp only [qword_app0, ext_zero_app]
  · rw [qword_ext _ _ (by decide), qword256_perm _ _ (by omega), e 1 (by decide),
      qword256_lo _ (by decide)]
    simp only [qword_app1, ext_zero_app]

theorem perm44_0 (lo hi : BitVec 64) :
    (permQwords (0#128 ++ (BitVec.extractLsb' 0 64 (0#64 ++ hi) ++ BitVec.extractLsb' 0 64 (0#64 ++ lo))) 0x44).extractLsb' 0 128 = hi ++ lo :=
  perm44 lo hi (k := 0) (by decide)

theorem perm44_1 (lo hi : BitVec 64) :
    (permQwords (0#128 ++ (BitVec.extractLsb' 0 64 (0#64 ++ hi) ++ BitVec.extractLsb' 0 64 (0#64 ++ lo))) 0x44).extractLsb' 128 128 = hi ++ lo :=
  perm44 lo hi (k := 1) (by decide)


theorem lane_setReg (s : State) (r : Reg) (v : BitVec 64) (x : XReg) (l : Nat) :
    (s.setReg r v).lane x l = s.lane x l := rfl

theorem mask_eq (d : XReg) (lo hi : BitVec 64) : mask d lo hi =
    [.movImm64 .rax lo, .vop (.vmovq d .rax), .movImm64 .rax hi, .vop (.vmovq .xmm13 .rax),
      .vop (.vbin .vpunpcklqdq .l128 d d .xmm13), .vop (.vpermq d d 0x44)] := rfl

theorem mask_ok {d : XReg} (hd : d ≠ .xmm13) (lo hi : BitVec 64) (s : State) :
    WP isa (.block (mask d lo hi)) s fun t => (∀ l < 2, t.lane d l = hi ++ lo) ∧
      (∀ x, x ≠ d → x ≠ .xmm13 → ∀ l, t.lane x l = s.lane x l) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [mask_eq, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun l hl => ?_, fun x h1 h2 l => ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp only [VOp.exec, State.lane_setV256, State.lane_setV128, State.ymm_eq, RegUpd.gpr_setReg,
        lane_setReg, hd, ↓reduceIte, reduceCtorEq, VBinOp.sse, XBinOp.eval, qword]
    · exact perm44_0 lo hi
    · exact perm44_1 lo hi
  · simp only [VOp.exec, State.lane_setV256, State.lane_setV128, lane_setReg, h1, h2, ite_false]
  · simp only [VOp.exec_mem, RegUpd.mem_setReg]
  · simp only [VOp.exec_gpr, RegUpd.gpr_setReg, hr, ite_false]
  · simp only [VOp.exec_rd, RegUpd.rd_setReg]
  · simp only [VOp.exec_wr, RegUpd.wr_setReg]
  · simp only [VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr, RegUpd.mxcsr_setReg]

theorem masks_ok (s : State) :
    WP isa (.block masks) s fun t => Masks t ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  unfold masks
  rw [WP.block_append_iff]
  refine (mask_ok (d := .xmm14) (by decide) rot24Lo rot24Hi s).mono ?_
  rintro t ⟨l1, -, m1, g1, r1, w1, x1⟩
  refine (mask_ok (d := .xmm15) (by decide) rot16Lo rot16Hi t).mono ?_
  rintro u ⟨l2, o2, m2, g2, r2, w2, x2⟩
  refine ⟨fun l hl => ⟨?_, ?_⟩, m2.trans m1, fun r hr => (g2 r hr).trans (g1 r hr), r2.trans r1,
    w2.trans w1, x2.trans x1⟩
  · rw [o2 _ (by decide) (by decide), l1 l hl]; decide
  · rw [l2 l hl]; decide

/-! ## The rows and the columns -/

theorem fold_ok {p : Addr} (index : Fin 8 → Fin 16 → Fin 128) (code : Fin 8 → Prog isa)
    (hcode : ∀ i (s : State), Scratch s p → Masks s → WP isa (code i) s (Permuted (index i) p s))
    (is : List (Fin 8)) (s : State) (hs : Scratch s p) (hm : Masks s) :
    WP isa (is.foldr (fun i rest => .seq (code i) rest) (.block [])) s fun t =>
      working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧ Masks t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, VKeep.refl s, hm⟩
  | cons i is ih =>
    apply WP.seq
    refine (hcode i s hs hm).mono ?_
    rintro t ⟨hw, hf, hk, hmt⟩
    refine (ih t (hs.of_vkeep hk) hmt).mono ?_
    rintro u ⟨hu, hf', hk', hm'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk', hm'⟩
    simpa only [List.foldl_cons, hw] using hu

theorem rows_eq : rows = (List.finRange 8).foldr (fun i rest => .seq (row i.val) rest) (.block []) :=
  rfl

theorem cols_eq : cols = (List.finRange 8).foldr (fun i rest => .seq (col i.val) rest) (.block []) :=
  rfl

/-- Both halves of scratch, initialized. -/
theorem initialized_all {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r 32) :
    blockAt m p = r ∧ working m p = r := by
  constructor
  · apply Vector.ext; intro i hi
    have := (h ⟨i, hi⟩ (by simp only; omega)).1
    rw [← blockAt_get m p ⟨i, hi⟩] at this
    exact this
  · apply Vector.ext; intro i hi
    have := (h ⟨i, hi⟩ (by simp only; omega)).2
    rw [← working_get m p ⟨i, hi⟩] at this
    exact this

theorem vzeroupper_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun t => t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    VOp.exec_mem, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr,
    and_self]

/-- G between the MXCSR prologue and epilogue. -/
theorem body_ok {s : State} {p x y out : Addr} (hs : Scratch s p) (hin : Inputs s x y p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa body s fun t => blockAt t.mem out = Spec.Argon2.compress (blockAt s.mem x) (blockAt s.mem y) ∧
      Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s.mem t.mem ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  unfold body
  apply WP.seq
  rw [WP.block_append_iff]
  refine (masks_ok s).mono ?_
  rintro s0 ⟨hm0, hmem0, hg0, hr0, hw0, hx0⟩
  have hs0 : Scratch s0 p := ⟨(hg0 .rcx (by decide)).trans hs.reg, hw0 ▸ hs.wr⟩
  have hin0 : Inputs s0 x y p := ⟨(hg0 .rdi (by decide)).trans hin.xreg,
    (hg0 .rsi (by decide)).trans hin.yreg, by rw [hr0, hw0]; exact hin.xread,
    by rw [hr0, hw0]; exact hin.yread, hin.xsep, hin.ysep⟩
  refine (init_prefix 32 (by decide) hs0 hin0).mono ?_
  rintro s1 ⟨hi1, hf1, hk1, hm1⟩
  obtain ⟨horig, hwork⟩ := initialized_all hi1
  have hs1 := hs0.of_vkeep hk1
  apply WP.seq
  rw [rows_eq]
  refine (fold_ok rowIndex (fun i => row i.val) (fun i s hs hm => row_ok i.isLt hs hm)
    (List.finRange 8) s1 hs1 (hm1 hm0)).mono ?_
  rintro s2 ⟨hrow, hf2, hk2, hm2⟩
  apply WP.seq
  rw [cols_eq]
  refine (fold_ok colIndex (fun i => col i.val) (fun i s hs hm => col_ok i.isLt hs hm)
    (List.finRange 8) s2 (hs1.of_vkeep hk2) hm2).mono ?_
  rintro s3 ⟨hcol, hf3, hk3, -⟩
  have hk13 := hk1.trans (hk2.trans hk3)
  rw [WP.block_append_iff]
  refine (finish_prefix 32 (by decide) ((hs1.of_vkeep hk2).of_vkeep hk3)
    (by rw [hk13.gpr, hg0 .rdx (by decide)]; exact ho)
    (by rw [hk13.wr, hw0]; exact hw) hd).mono ?_
  rintro s4 ⟨hfin, hf4, hk4, -⟩
  refine (vzeroupper_ok s4).mono ?_
  rintro t ⟨hmt, hgt, hrt, hwt, hxt⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · apply Vector.ext; intro i hi
    have e := hfin ⟨i, hi⟩ (by simp only; omega)
    have ho3 := original_preserved (hf2.trans hf3)
    rw [horig] at ho3
    show (blockAt t.mem out)[(⟨i, hi⟩ : Fin 128)] =
      (compress (blockAt s.mem x) (blockAt s.mem y))[(⟨i, hi⟩ : Fin 128)]
    rw [blockAt_get, hmt, e, hcol, hrow, hwork, ho3, hmem0]
    rfl
  · rw [hmt]
    have f1 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s0.mem s1.mem :=
      hf1.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    have f4 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s3.mem s4.mem :=
      hf4.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    rw [← hmem0]
    exact ((f1.trans (round_frame hf2)).trans (round_frame hf3)).trans f4
  · rw [hgt, hk4.gpr, hk13.gpr, hg0 r hr]
  · rw [hrt, hk4.rd, hk13.rd, hr0]
  · rw [hwt, hk4.wr, hk13.wr, hw0]
  · rw [hxt, hk4.mxcsr, hk13.mxcsr, hx0]

/-! ## MXCSR -/

/-- The eight bytes of scratch through which MXCSR is saved and loaded. -/
abbrev mxR (p : Addr) : Region := ⟨off p 2048, 8⟩

theorem mx_write {s : State} {p : Addr} (hs : Scratch s p) {d : Nat} (hd : 2048 ≤ d ∧ d ≤ 2052) :
    InRegions s.wr (off p d) 4 :=
  hs.write (by omega)

theorem mx_read {s : State} {p : Addr} (hs : Scratch s p) {d : Nat} (hd : 2048 ≤ d ∧ d ≤ 2052) :
    InRegions (s.rd ++ s.wr) (off p d) 4 :=
  hs.read (by omega)

theorem mx_contains (p : Addr) {d : Nat} (hd : 2048 ≤ d ∧ d ≤ 2052) : (mxR p).Contains (off p d) 4 :=
  Offset.contains p (by omega) (by omega) (by omega)

theorem save_ok {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block [.stmxcsr (at_ .rcx mxcsrOff), .mov32 .r11 (.mem (at_ .rcx mxcsrOff)),
      .alu32 .and .r11 (.imm 0xFFFF)]) s fun t =>
      t.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧ Frame [mxR p] s.mem t.mem := by
  apply WP.of_runBlock
  have hr := mx_read hs (d := 2048) (by decide)
  simp only [mxcsrOff, runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, ea_at, hs.reg,
    mx_write hs (d := 2048) (by decide), ite_true, readSrc32, State.load32, hr, Option.map_some,
    Mem.readW_writeW_self32, execAlu32, Option.bind_some, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.mxcsr_setReg,
    Option.some.injEq, exists_eq_left', ite_true, RegUpd.setWidth_setWidth_32]
  refine ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (mx_contains p (by decide))⟩


theorem set_ok {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rcx (mxcsrOff + 4)) .rax,
      .ldmxcsr (at_ .rcx (mxcsrOff + 4)), .lfence]) s fun t =>
      t.mxcsr = 0x1FBF ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [mxR p] s.mem t.mem := by
  have hr := mx_read hs (d := 2052) (by decide)
  have hz : BitVec.extractLsb' 16 16 (8127 : BitVec 32) = 0 := by decide
  apply WP.of_runBlock
  simp only [mxcsrOff, runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, ea_at,
    readSrc32, State.setReg32, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, hs.reg, Option.map_some, Option.bind_some, State.load32,
    Mem.readW_writeW_self32, mx_write hs (d := 2052) (by decide), hr, RegUpd.setWidth_setWidth_32,
    reduceCtorEq, ↓reduceIte, Nat.reduceAdd, hz, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (mx_contains p (by decide))⟩


theorem restore_ok {s : State} {p : Addr} (hs : Scratch s p)
    (hz : BitVec.extractLsb' 16 16 ((s.gpr .r11).setWidth 32) = 0) :
    WP isa (.block [.store32 (at_ .rcx mxcsrOff) .r11, .ldmxcsr (at_ .rcx mxcsrOff)]) s fun t =>
      t.mxcsr = (s.gpr .r11).setWidth 32 ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [mxR p] s.mem t.mem := by
  have hr := mx_read hs (d := 2048) (by decide)
  apply WP.of_runBlock
  simp only [mxcsrOff, runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, ea_at,
    hs.reg, State.load32, Mem.readW_writeW_self32, mx_write hs (d := 2048) (by decide), hr,
    ↓reduceIte, Option.bind_some, hz, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (mx_contains p (by decide))⟩

theorem mxR_sub (p : Addr) : Region.Sub (mxR p) ⟨p, 4096⟩ := Offset.sub_base p (by decide)

/-- A block outside scratch is unchanged by writes to `mxR`. -/
theorem blockAt_mx {m m' : Mem} {p q : Addr} (hf : Frame [mxR p] m m')
    (hd : (⟨q, 1024⟩ : Region).Disjoint ⟨p, 4096⟩) : blockAt m' q = blockAt m q := by
  have d1 : (⟨q, 1024⟩ : Region).Disjoint ⟨off p 2048, 8⟩ := hd.sub_right (mxR_sub p)
  apply Vector.ext
  intro i hi
  have he : m'.readW (off q (8 * i)) 64 = m.readW (off q (8 * i)) 64 :=
    hf.readW (r := ⟨q, 1024⟩) (Offset.contains_base q (by omega) (by omega))
      (fun r hr => (List.mem_singleton.mp hr) ▸ d1) (by decide)
  rw [← blockAt_get m' q ⟨i, hi⟩, ← blockAt_get m q ⟨i, hi⟩] at he
  exact he

theorem ldmxcsr_ok (v : BitVec 32) :
    BitVec.extractLsb' 16 16 (BitVec.setWidth 32 (BitVec.setWidth 64 (v &&& 0xFFFF))) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp


/-! ## G -/

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.X86_64.Avx2.compress s fun t =>
      compressLocal.post s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame s.wr s.mem t.mem := by
  obtain ⟨hrd, hwr, hout, hx, hy, _, _⟩ := hs
  have scr : Scratch s (s.gpr .rcx) := ⟨rfl, by simp [hwr]⟩
  unfold Impl.Argon2.X86_64.Avx2.compress
  apply WP.seq
  refine (save_ok scr).mono ?_
  rintro s1 ⟨h11, hg1, hr1, hw1, -, hf1⟩
  have scr1 : Scratch s1 (s.gpr .rcx) := ⟨hg1 .rcx (by decide), hw1 ▸ scr.wr⟩
  apply WP.seq
  apply WP.seq
  refine (set_ok scr1).mono ?_
  rintro s2 ⟨-, hg2, hr2, hw2, hf2⟩
  have hg12 : ∀ r, r ≠ .rax → r ≠ .r11 → s2.gpr r = s.gpr r :=
    fun r h0 h11 => (hg2 r h0).trans (hg1 r h11)
  have scr2 : Scratch s2 (s.gpr .rcx) := ⟨hg12 .rcx (by decide) (by decide), hw2 ▸ scr1.wr⟩
  have hf12 := hf1.trans hf2
  have inputs : Inputs s2 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) :=
    ⟨hg12 .rdi (by decide) (by decide), hg12 .rsi (by decide) (by decide),
      by rw [hr2, hw2, hr1, hw1]; simp [hrd], by rw [hr2, hw2, hr1, hw1]; simp [hrd], hx, hy⟩
  apply WP.seq
  refine (body_ok scr2 inputs (out := s.gpr .rdx) (hg12 .rdx (by decide) (by decide))
    (by rw [hw2, hw1, hwr]; simp) hout.symm).mono ?_
  rintro s3 ⟨hpost, hf3, hg3, hr3, hw3, -⟩
  refine WP.of_runBlock ⟨s3, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec], ?_⟩
  have scr3 : Scratch s3 (s.gpr .rcx) := ⟨(hg3 .rcx (by decide)).trans scr2.reg, hw3 ▸ scr2.wr⟩
  have h113 : s3.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 := by
    rw [hg3 .r11 (by decide), hg2 .r11 (by decide), h11]
  refine (restore_ok scr3 (by rw [h113]; exact ldmxcsr_ok _)).mono ?_
  rintro t ⟨-, hgt, -, -, hft⟩
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · change blockAt t.mem (s.gpr .rdx) = Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    rw [blockAt_mx hft hout, hpost, blockAt_mx hf12 hx, blockAt_mx hf12 hy]
  · have h0 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h1 : r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hgt, hg3 r h0, hg12 r h0 h1]
  · have hmx : ∀ {m m' : Mem}, Frame [mxR (s.gpr .rcx)] m m' →
        Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] m m' := fun h =>
      h.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨_, by simp, mxR_sub _⟩
    rw [hwr]
    exact ((hmx hf12).trans hf3).trans (hmx hft)

theorem compress_ctl : ctlOk Impl.Argon2.X86_64.Avx2.compress = true := by lit_decide

/-- Correctness, termination, memory safety, and the System V ABI. -/
theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.X86_64.Avx2.compress s tr t ∧ abiPreserved s t ∧ compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk, hf⟩ := compress_wp s hs
  refine ⟨tr, t, he, abiPreserved_of_ctl compress_ctl he ⟨hk, ?_⟩, hp⟩
  apply hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [hs.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.X86_64.Avx2.compress :=
  VG.Taint.constantTime (A := taint) initialTaint (fun _ _ hs ht hp => initial_agree hs ht hp)
    (by taint_decide)

/-- `vg_argon2_compress_avx2` meets the contract of `vg_argon2_compress`. -/
theorem compress_verified : Verified X86_64.target Impl.Argon2.X86_64.Avx2.compress
    (Spec.Argon2.compressContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies

end VG.Proof.Argon2.X86_64.Avx2
