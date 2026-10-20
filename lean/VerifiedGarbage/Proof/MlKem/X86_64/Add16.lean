module

public import VerifiedGarbage.Impl.MlKem.X86_64.Arith16
import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
public import VerifiedGarbage.Proof.MlKem.X86_64.InlinePrim
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
meta import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: a polynomial of `u16`s added to one of `u32`s (`add16Y`)

Each iteration loads 16 `u16`s of `g` and brings quadwords `0, 2` to lane 0
and `1, 3` to lane 1 (`vpermq`, `word_permD8`); then each half
(`add16Half`, `half_ok`) widens four words of each lane against zero
(`punpck{l,h}wd`, `dword_punpck{l,h}wd0'`), which are coefficients `4l` to
`4l + 3` of the half, and adds them to eight coefficients of `f` as
`addArith` does (`addArith_ok`). The loop leaves `f + g` at `f`
(`Add16.fn_ok`), which the K-PKE functions run inline (`add16In_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Proof.MlKem VG.Spec.MlKem

/-- `f = rdi` (`u32`s) becomes `f + g`, `g = rsi` (`u16`s). -/
def add16K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 512⟩] ∧ s.wr = [pR (s.gpr .rdi)] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rsi, 512⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rsi, 512⟩ ∧ Reduced s.mem (s.gpr .rdi) ∧ ReducedW 16 s.mem (s.gpr .rsi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (Spec.MlKem.add (polyAt s.mem (s.gpr .rdi)) (polyAtW 16 s.mem (s.gpr .rsi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## A half -/

/-- The widening and the arithmetic of a lane. -/
theorem unpackAdd_ok (op : XBinOp) (s : State) (hq : s.xmm .xmm15 = qD) :
    WP isa (.block (xmov .xmm1 .xmm2 :: xb op .xmm1 .xmm14 :: addArith)) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j =
        cadd32 (dword (s.xmm .xmm0) j + dword (XBinOp.eval op (s.xmm .xmm2) (s.xmm .xmm14)) j - 3329#32)) ∧
        XOnly [.xmm0, .xmm1] s s' := by
  simp only [addArith, dcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  refine ⟨fun j hj => ?_, by xonly⟩
  simp only [dword_paddd _ _ hj, dword_psubd _ _ hj, dword_pand, dword_psrad31 _ hj, hq, dword_qD hj]
  rfl

theorem lane_unpackLo :
    laneSseBlock (toY (xmov .xmm1 .xmm2 :: xb .punpcklwd .xmm1 .xmm14 :: addArith)) =
      some (xmov .xmm1 .xmm2 :: xb .punpcklwd .xmm1 .xmm14 :: addArith) := by decide +kernel

theorem lane_unpackHi :
    laneSseBlock (toY (xmov .xmm1 .xmm2 :: xb .punpckhwd .xmm1 .xmm14 :: addArith)) =
      some (xmov .xmm1 .xmm2 :: xb .punpckhwd .xmm1 .xmm14 :: addArith) := by decide +kernel

/-- `add16Half op o`: the eight coefficients at `rdi + o` plus the words `op`
widens from `ymm2`, stored back. -/
theorem half_ok {op : XBinOp}
    (hY : laneSseBlock (toY (xmov .xmm1 .xmm2 :: xb op .xmm1 .xmm14 :: addArith)) =
      some (xmov .xmm1 .xmm2 :: xb op .xmm1 .xmm14 :: addArith))
    {o : Nat} {s : State} (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 o) 32)
    (hq : ∀ l < 2, s.lane .xmm15 l = qD) :
    WP isa (.block (add16Half op o)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 o) (s'.ymm .xmm0) ∧
      (∀ l < 2, ∀ e < 4, dword (s'.lane .xmm0 l) e =
        cadd32 (dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 o + BitVec.ofNat 64 (16 * l)) 128) e +
          dword (XBinOp.eval op (s.lane .xmm2 l) (s.lane .xmm14 l)) e - 3329#32)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∉ [XReg.xmm0, .xmm1], ∀ l < 2, s'.lane r l = s.lane r l := by
  rw [add16Half, List.cons_append, wp_cons_iff]
  refine WP.mono (yld_ok (p := .rdi) (off := o) (d := .xmm0)
    (let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩)) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t => ∀ j < 4, dword (t.xmm .xmm0) j =
      cadd32 (dword ((s1.proj l).xmm .xmm0) j +
        dword (XBinOp.eval op ((s1.proj l).xmm .xmm2) ((s1.proj l).xmm .xmm14)) j - 3329#32))
    fun l hl => unpackAdd_ok op _ (by rw [State.proj_xmm, o1.lane _ (by decide) l hl]; exact hq l hl))
    fun s2 ⟨B2, o2⟩ => ?_
  have o12 := o1.trans o2
  refine WP.mono (yst_ok (h := .xmm0) (off := o) (by rw [o12.wr, o12.gpr]; exact hw)) fun s3 e3 => ?_
  subst e3
  refine ⟨by simp only [State.setMem_mem, State.setMem_ymm, o12.mem, o12.gpr], fun l hl e he => ?_,
    by simp only [State.setMem_gpr, o12.gpr], by simp only [State.setMem_rd, o12.rd],
    by simp only [State.setMem_wr, o12.wr], fun r hr l hl => ?_⟩
  · rw [State.setMem_lane, ← State.proj_xmm, B2 l hl e he, State.proj_xmm, State.proj_xmm, State.proj_xmm, L1 l hl,
      o1.lane _ (by decide) l hl, o1.lane _ (by decide) l hl]
  · rw [State.setMem_lane, o12.lane r (by simpa using hr) l hl]

/-! ## The loop -/

namespace Add16

/-- Coefficient `k` of `f + g`, as the code computes it. -/
def V (s₀ : State) (k : Nat) : BitVec 32 :=
  cadd32 (coeffAt s₀.mem (s₀.gpr .rdi) k + (coeffAtW 16 s₀.mem (s₀.gpr .rsi) k).setWidth 32 - 3329#32)

/-- After `i` blocks of 16 coefficients. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (16 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qD
  z : ∀ l < 2, s.lane .xmm14 l = 0
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 16 * i then V s₀ k else coeffAt s₀.mem (s₀.gpr .rdi) k

/-- Word `t` of lane `l` of 32 bytes at `a`, after `vpermq` with `0xD8`. -/
theorem word_perm {m : Mem} {a : Addr} {x : BitVec 128} {l t : Nat} (hl : l < 2) (ht : t < 8)
    (hx : x = (if l = 0 then XBinOp.eval .punpcklqdq (m.readW (a + BitVec.ofNat 64 (16 * 0)) 128)
        (m.readW (a + BitVec.ofNat 64 (16 * 1)) 128)
      else XBinOp.eval .punpckhqdq (m.readW (a + BitVec.ofNat 64 (16 * 0)) 128)
        (m.readW (a + BitVec.ofNat 64 (16 * 1)) 128))) :
    word x t = m.readW (a + BitVec.ofNat 64 (2 * (8 * (t / 4) + 4 * l + t % 4))) 16 := by
  rw [hx]; exact word_permD8 m a hl ht

section
variable {s₀ : State} (hp : add16K.pre s₀)
include hp

/-- An iteration: coefficients `16i` to `16i + 15`. -/
theorem step {i : Nat} (hi : i < 16) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block (add16Body ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 16 * i + 16 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : (⟨s₀.gpr .rsi, 512⟩ : Region) ∈ s.rd ++ s.wr := by rw [hI.rd, hp.1]; simp
  -- `g` is where it was
  have hg : ∀ k < 256, coeffAtW 16 s.mem (s₀.gpr .rsi) k = coeffAtW 16 s₀.mem (s₀.gpr .rsi) k := fun k hk =>
    coeffAtW16_congr (bytes_frame hI.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.2.2.1.symm) (by decide)) (by rw [n_eq]; exact hk)
  rw [add16Body, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (p := .rsi) (off := 0) (d := .xmm2) (by
    rw [add_ofNat_zero, hI.rsi]; exact ⟨_, hr, Offset.contains_base _ (by omega) (by omega)⟩)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (ypermq_ok (d := .xmm2) (r := .xmm2) s1) fun s2 ⟨P2a, P2b, o2⟩ => ?_
  have o12 := o1.trans o2
  -- the words of `g` in `ymm2`
  have W : ∀ l < 2, ∀ t < 8, word (s2.lane .xmm2 l) t =
      coeffAtW 16 s₀.mem (s₀.gpr .rsi) (16 * i + 8 * (t / 4) + 4 * l + t % 4) := fun l hl t ht => by
    rw [word_perm (m := s.mem) (a := s.gpr .rsi + BitVec.ofNat 64 0) hl ht (by
        rcases lane01 hl with rfl | rfl
        · rw [P2a, L1 0 (by decide), L1 1 (by decide)]; rfl
        · rw [P2b, L1 0 (by decide), L1 1 (by decide)]; rfl),
      ← hg _ (by omega), coeffAtW16_eq, add_ofNat_zero, hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun x => s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 x) 16) (by omega)
  have g2r : s2.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (16 * i) := by
    rw [add_ofNat_zero, o12.gpr, hI.rdi]
  rw [WP.block_append_iff]
  refine WP.mono (half_ok lane_unpackLo (o := 0) (by
      rw [o12.wr, g2r]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hI.q l hl)) fun s3 ⟨m3, H3, g3, r3, w3, l3⟩ => ?_
  have g3r : s3.gpr .rdi + BitVec.ofNat 64 32 = coeffAddr (s₀.gpr .rdi) (16 * i + 8) := by
    rw [g3, o12.gpr, hI.rdi, show (32 : Nat) = 4 * 8 from rfl, coeffAddr_off]
  rw [WP.block_append_iff]
  refine WP.mono (half_ok lane_unpackHi (o := 32) (by
      rw [w3, o12.wr, g3r]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun l hl => by rw [l3 _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact hI.q l hl))
    fun s4 ⟨m4, H4, g4, r4, w4, l4⟩ => ?_
  have ga : ∀ r, s4.gpr r = s.gpr r := fun r => by rw [g4, g3, o12.gpr]
  have z3 : ∀ l < 2, s3.lane .xmm14 l = 0 := fun l hl => by
    rw [l3 _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact hI.z l hl
  have z2 : ∀ l < 2, s2.lane .xmm14 l = 0 := fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hI.z l hl
  -- what each half stored
  have A3 : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm0 l) e = V s₀ (16 * i + 4 * l + e) := fun l hl e he => by
    rw [H3 l hl e he, z2 l hl, Cbd.dword_punpcklwd0' _ he, W l hl e (by omega), Nat.div_eq_of_lt he,
      Nat.mod_eq_of_lt he, Nat.mul_zero, Nat.add_zero, o12.mem, g2r, YAddSub.lane_coeff _ _ _ _ _ he,
      hI.coeff _ (by omega), ifn (by omega), V]
  have A4 : ∀ l < 2, ∀ e < 4, dword (s4.lane .xmm0 l) e = V s₀ (16 * i + 8 + 4 * l + e) := fun l hl e he => by
    rw [H4 l hl e he, z3 l hl, l3 _ (by decide) l hl, Cbd.dword_punpckhwd0' _ he, W l hl (4 + e) (by omega),
      show (4 + e) / 4 = 1 by omega, show (4 + e) % 4 = e by omega, Nat.mul_one, g3r, YAddSub.lane_coeff _ _ _ _ _ he, m3,
      g2r, o12.mem, coeffAt_write256 _ _ (by omega) _ (by omega), ifn (by omega),
      hI.coeff _ (by omega), ifn (by omega), V]
  have m4' : s4.mem = (s.mem.writeW (coeffAddr (s₀.gpr .rdi) (16 * i)) (s3.ymm .xmm0)).writeW
      (coeffAddr (s₀.gpr .rdi) (16 * i + 8)) (s4.ymm .xmm0) := by
    rw [m4, g3r, m3, g2r, o12.mem]
  vrunm [sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_, ?_, fun k hk => ?_⟩, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [ga, hI.rdi, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) from rfl, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [ga, hI.rsi, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.mul_succ]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [r4, r3, o12.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [w4, w3, o12.wr, hI.wr]
  · simp only [lane_setReg, lane_setFlags]
    rw [l4 _ (by decide) l hl, l3 _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact hI.q l hl
  · simp only [lane_setReg, lane_setFlags]; rw [l4 _ (by decide) l hl]; exact z3 l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m4']
    exact (hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m4', coeffAt_write256 _ _ (by omega) _ hk, coeffAt_write256 _ _ (by omega) _ hk]
    by_cases h2 : 16 * i + 8 ≤ k ∧ k < 16 * i + 8 + 8
    · rw [ifp h2, ifp (by omega)]
      obtain ⟨l, e, hl, he, rfl⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ k = 16 * i + 8 + 4 * l + e :=
        ⟨(k - 16 * i - 8) / 4, (k - 16 * i - 8) % 4, by omega, by omega, by omega⟩
      rw [show 8 * (4 * (16 * i + 8 + 4 * l + e - (16 * i + 8))) = 8 * (16 * l + 4 * e) by omega,
        extract_ymm _ _ hl he, A4 l hl e he]
    · rw [ifn h2]
      by_cases h1 : 16 * i ≤ k ∧ k < 16 * i + 8
      · rw [ifp h1, ifp (by omega)]
        obtain ⟨l, e, hl, he, rfl⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ k = 16 * i + 4 * l + e :=
          ⟨(k - 16 * i) / 4, (k - 16 * i) % 4, by omega, by omega, by omega⟩
        rw [show 8 * (4 * (16 * i + 4 * l + e - 16 * i)) = 8 * (16 * l + 4 * e) by omega,
          extract_ymm _ _ hl he, A3 l hl e he]
      · rw [ifn h1, hI.coeff k hk]
        by_cases h' : k < 16 * i
        · rw [ifp h', ifp (by omega)]
        · rw [ifn h', ifn (by omega)]
  · rw [ga]
  · rw [ga]


omit hp in
/-- The constants: `q` in `ymm15`, zero in `ymm14`. -/
theorem init_ok (s₀ : State) :
    WP isa (.block (yconst .xmm15 3329 ++ [yb .vpxor .xmm14 .xmm14 .xmm14])) s₀ fun w =>
      (∀ l < 2, w.lane .xmm15 l = qD) ∧ (∀ l < 2, w.lane .xmm14 l = 0) ∧ Keep [.rax] s₀ w ∧ w.mem = s₀.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, _⟩ => ?_
  refine WP.mono (ylanes RowY.lane_zero14 (P := fun _ t => t.xmm .xmm14 = 0) fun l _ => FinY.zero14_ok _)
    fun w2 ⟨Z, o⟩ => ⟨fun l hl => by rw [o.lane _ (by decide) l hl, lq l hl]; decide, Z,
      ⟨fun r hr => by rw [o.gpr, k1.gpr hr], by rw [o.rd, k1.2.1], by rw [o.wr, k1.2.2]⟩, by rw [o.mem, m1]⟩

/-- The whole function, from its precondition. -/
theorem fn_ok (hc : writesOnly [.rax, .rdi, .rsi, .rcx] add16Y = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (add16Y : Prog isa) = true) :
    ∃ tr s', Exec isa add16Y s₀ tr s' ∧ abiPreserved s₀ s' ∧ add16K.post s₀ s' := by
  have hW : WP isa add16Y s₀ fun s' =>
      Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧ ∀ k < 256, coeffAt s'.mem (s₀.gpr .rdi) k = V s₀ k := by
    refine WP.seq (WP.mono (init_ok s₀) fun w ⟨lq, lz, k1, m1⟩ => ?_)
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide) _ (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.2.1, k1.2.1], by rw [o.keep.2.2, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy]]; exact lq l hl,
        fun l hl => by
          rw [show u.lane .xmm14 l = w.lane .xmm14 l by simp only [State.lane]; rw [o.xmm, hy]]; exact lz l hl,
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, ifn (by omega)]⟩)
      fun i hi u hI => step hp hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrunm; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, fun k hk => by rw [hI.coeff k hk, ifp (by omega)]⟩
  obtain ⟨tr, s', he, ⟨hf, hco⟩, hk⟩ := WP.keep _ hW hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hf ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    have hG : PolyIsW 16 s₀.mem (s₀.gpr .rsi) (polyAtW 16 s₀.mem (s₀.gpr .rsi)) := ⟨hp.2.2.2.2.2.2, rfl⟩
    have hb := hp.2.2.2.2.2.2 k (by rw [n_eq]; exact hk)
    rw [hco k hk, V, add_lane (hp.2.2.2.2.2.1 k (by rw [n_eq]; exact hk))
        (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hb),
      add_get _ _ (by rw [n_eq]; exact hk), val_add, polyAt_val hp.2.2.2.2.2.1 (by rw [n_eq]; exact hk),
      ← polyIsW_toNat hG (by rw [n_eq]; exact hk), BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]

end

end Add16

theorem add16_correct (s : State) (hs : add16K.pre s) :
    ∃ t s', Exec isa add16Y s t s' ∧ abiPreserved s s' ∧ add16K.post s s' :=
  Add16.fn_ok hs (by decide +kernel) (by decide +kernel)

/-- What inline code of `f ← f + g`, `g` of `u16`s, needs. -/
structure Add16Hi (f g : Ptr) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31
  redF : Reduced s.mem (pa s f)
  redG : ReducedW 16 s.mem (pa s g)
  d : (pR (pa s f)).Disjoint ⟨pa s g, 512⟩
  rF : (retR s).Disjoint (pR (pa s f))
  rG : (retR s).Disjoint ⟨pa s g, 512⟩
  c : Covers ([⟨pa s g, 512⟩] ++ [pR (pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (pa s f)] s.wr

/-- `f ← f + g` inline, `g` of `u16`s. -/
theorem add16In_ok {f g : Ptr} (hgr : g.1 ≠ .rdi) {s : State} (h : Add16Hi f g s) :
    WP isa (.seq (.block (lea .rdi f ++ lea .rsi g)) add16Y) s fun s' =>
      IPost s s' [pR (pa s f)] ∧
        PolyIs s'.mem (pa s f) (Spec.MlKem.add (polyAt s.mem (pa s f)) (polyAtW 16 s.mem (pa s g))) := by
  refine WP.mono (glueIn_ok add16_correct (by decide) (accGlue_ok f g h.off.1 h.off.2 hgr s)
    (rd := [⟨pa s g, 512⟩]) (wr := [pR (pa s f)])
    (fun s1 hv hm k => by
      simp only [add16K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        hv.1, hv.2, hm]
      exact ⟨trivial, trivial, h.d, retR_keep k h.rF _ _, retR_keep k h.rG _ _, h.redF, h.redG⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [add16K, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2, hm] at hq
  exact hq

end VG.Proof.MlKem.X86_64
