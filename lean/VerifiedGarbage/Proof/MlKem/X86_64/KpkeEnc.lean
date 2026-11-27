module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kpke16
public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
public import VerifiedGarbage.Proof.MlKem.X86_64.DcDec
public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
public import VerifiedGarbage.Proof.MlKem.X86_64.VMem
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
public import VerifiedGarbage.Impl.MlKem.X86_64.Arith16
import VerifiedGarbage.Proof.MlKem.X86_64.FinY
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
meta import VerifiedGarbage.Proof.MlKem.X86_64.FinY
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `MlKem.X86_64.Add16`, which only this module used -/

section

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
  have j0 : 16 * i + 16 ≤ 256 := by omega_arith
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : (⟨s₀.gpr .rsi, 512⟩ : Region) ∈ s.rd ++ s.wr := by rw [hI.rd, hp.1]; simp
  -- `g` is where it was
  have hg : ∀ k < 256, coeffAtW 16 s.mem (s₀.gpr .rsi) k = coeffAtW 16 s₀.mem (s₀.gpr .rsi) k := fun k hk =>
    coeffAtW16_congr (bytes_frame hI.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.2.2.1.symm) (by decide)) (by rw [n_eq]; exact hk)
  rw [add16Body, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (p := .rsi) (off := 0) (d := .xmm2) (by
    rw [add_ofNat_zero, hI.rsi]; exact ⟨_, hr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (ypermq_ok (d := .xmm2) (r := .xmm2) s1) fun s2 ⟨P2a, P2b, o2⟩ => ?_
  have o12 := o1.trans o2
  -- the words of `g` in `ymm2`
  have W : ∀ l < 2, ∀ t < 8, word (s2.lane .xmm2 l) t =
      coeffAtW 16 s₀.mem (s₀.gpr .rsi) (16 * i + 8 * (t / 4) + 4 * l + t % 4) := fun l hl t ht => by
    rw [word_perm (m := s.mem) (a := s.gpr .rsi + BitVec.ofNat 64 0) hl ht (by
        rcases lane01 hl with rfl | rfl
        · rw [P2a, L1 0 (by decide), L1 1 (by decide)]; rfl
        · rw [P2b, L1 0 (by decide), L1 1 (by decide)]; rfl),
      ← hg _ (by omega_arith), coeffAtW16_eq, add_ofNat_zero, hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun x => s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 x) 16) (by omega_arith)
  have g2r : s2.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (16 * i) := by
    rw [add_ofNat_zero, o12.gpr, hI.rdi]
  rw [WP.block_append_iff]
  refine WP.mono (half_ok lane_unpackLo (o := 0) (by
      rw [o12.wr, g2r]; exact ⟨_, hw, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hI.q l hl)) fun s3 ⟨m3, H3, g3, r3, w3, l3⟩ => ?_
  have g3r : s3.gpr .rdi + BitVec.ofNat 64 32 = coeffAddr (s₀.gpr .rdi) (16 * i + 8) := by
    rw [g3, o12.gpr, hI.rdi, show (32 : Nat) = 4 * 8 from rfl, coeffAddr_off]
  rw [WP.block_append_iff]
  refine WP.mono (half_ok lane_unpackHi (o := 32) (by
      rw [w3, o12.wr, g3r]; exact ⟨_, hw, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun l hl => by rw [l3 _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact hI.q l hl))
    fun s4 ⟨m4, H4, g4, r4, w4, l4⟩ => ?_
  have ga : ∀ r, s4.gpr r = s.gpr r := fun r => by rw [g4, g3, o12.gpr]
  have z3 : ∀ l < 2, s3.lane .xmm14 l = 0 := fun l hl => by
    rw [l3 _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact hI.z l hl
  have z2 : ∀ l < 2, s2.lane .xmm14 l = 0 := fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hI.z l hl
  -- what each half stored
  have A3 : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm0 l) e = V s₀ (16 * i + 4 * l + e) := fun l hl e he => by
    rw [H3 l hl e he, z2 l hl, Cbd.dword_punpcklwd0' _ he, W l hl e (by omega_arith), Nat.div_eq_of_lt he,
      Nat.mod_eq_of_lt he, Nat.mul_zero, Nat.add_zero, o12.mem, g2r, YAddSub.lane_coeff _ _ _ _ _ he,
      hI.coeff _ (by omega_arith), ifn (by omega_arith), V]
  have A4 : ∀ l < 2, ∀ e < 4, dword (s4.lane .xmm0 l) e = V s₀ (16 * i + 8 + 4 * l + e) := fun l hl e he => by
    rw [H4 l hl e he, z3 l hl, l3 _ (by decide) l hl, Cbd.dword_punpckhwd0' _ he, W l hl (4 + e) (by omega_arith),
      show (4 + e) / 4 = 1 by omega_arith, show (4 + e) % 4 = e by omega_arith, Nat.mul_one, g3r, YAddSub.lane_coeff _ _ _ _ _ he, m3,
      g2r, o12.mem, coeffAt_write256 _ _ (by omega_arith) _ (by omega_arith), ifn (by omega_arith),
      hI.coeff _ (by omega_arith), ifn (by omega_arith), V]
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
    exact (hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m4', coeffAt_write256 _ _ (by omega_arith) _ hk, coeffAt_write256 _ _ (by omega_arith) _ hk]
    by_cases h2 : 16 * i + 8 ≤ k ∧ k < 16 * i + 8 + 8
    · rw [ifp h2, ifp (by omega_arith)]
      obtain ⟨l, e, hl, he, rfl⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ k = 16 * i + 8 + 4 * l + e :=
        ⟨(k - 16 * i - 8) / 4, (k - 16 * i - 8) % 4, by omega_arith, by omega_arith, by omega_arith⟩
      rw [show 8 * (4 * (16 * i + 8 + 4 * l + e - (16 * i + 8))) = 8 * (16 * l + 4 * e) by omega_arith,
        extract_ymm _ _ hl he, A4 l hl e he]
    · rw [ifn h2]
      by_cases h1 : 16 * i ≤ k ∧ k < 16 * i + 8
      · rw [ifp h1, ifp (by omega_arith)]
        obtain ⟨l, e, hl, he, rfl⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ k = 16 * i + 4 * l + e :=
          ⟨(k - 16 * i) / 4, (k - 16 * i) % 4, by omega_arith, by omega_arith, by omega_arith⟩
        rw [show 8 * (4 * (16 * i + 4 * l + e - 16 * i)) = 8 * (16 * l + 4 * e) by omega_arith,
          extract_ymm _ _ hl he, A3 l hl e he]
      · rw [ifn h1, hI.coeff k hk]
        by_cases h' : k < 16 * i
        · rw [ifp h', ifp (by omega_arith)]
        · rw [ifn h', ifn (by omega_arith)]
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
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, ifn (by omega_using [])]⟩)
      fun i hi u hI => step hp hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrunm; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, fun k hk => by rw [hI.coeff k hk, ifp (by omega_using [hk])]⟩
  obtain ⟨tr, s', he, ⟨hf, hco⟩, hk⟩ := WP.keep _ hW hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hf ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    have hG : PolyIsW 16 s₀.mem (s₀.gpr .rsi) (polyAtW 16 s₀.mem (s₀.gpr .rsi)) := ⟨hp.2.2.2.2.2.2, rfl⟩
    have hb := hp.2.2.2.2.2.2 k (by rw [n_eq]; exact hk)
    rw [hco k hk, V, add_lane (hp.2.2.2.2.2.1 k (by rw [n_eq]; exact hk))
        (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [])]; exact hb),
      add_get _ _ (by rw [n_eq]; exact hk), val_add, polyAt_val hp.2.2.2.2.2.1 (by rw [n_eq]; exact hk),
      ← polyIsW_toNat hG (by rw [n_eq]; exact hk), BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [])]

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

end

end

/-! ### `MlKem.X86_64.Widen`, which only this module used -/

section

/-!
# ML-KEM on x86-64: a polynomial of `u16`s as `u32`s (`vunpack`)

`vunpack` (`Impl/MlKem/X86_64/Vec.lean`) stores the 256 words at `rdx` as
`u32`s at `r9`, eight at a time. `widen_ok`: of a polynomial of `u16`s
anywhere the code may read (`PolyIsW 16`), the polynomial of `u32`s
(`PolyIs`), as `vunpack_ok` does for the words of the NTT's working space.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Proof.MlKem VG.Spec.MlKem

theorem s16_of_polyIsW {m : Mem} {p : Addr} {F : Poly} (h : PolyIsW 16 m p F) : S16 m p F :=
  fun i hi => polyIsW_toNat h (by rw [n_eq]; exact hi)

/-- `vunpack`: the polynomial `F` of `u16`s at `src` as `u32`s at `dP`. -/
theorem widen_ok {dP src : Addr} {F : Poly} {s : State} (hS : PolyIsW 16 s.mem src F)
    (h9 : s.gpr .r9 = dP) (hdx : s.gpr .rdx = src) (hwf : pR dP ∈ s.wr)
    (hin : InRegions (s.rd ++ s.wr) src 512) (hd : (pR dP).Disjoint ⟨src, 512⟩) :
    WP isa vunpack s fun s' => PolyIs s'.mem dP F ∧ Frame [pR dP] s.mem s'.mem ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → s'.xmm r = s.xmm r) ∧ Keep [.r9, .rdx, .rcx] s s' ∧
      s'.mxcsr = s.mxcsr := by
  obtain hS16 := s16_of_polyIsW hS
  refine WP.seq (WP.mono (Q := fun (w : State) => w.xmm .xmm4 = 0 ∧ XOnly [.xmm4] s w)
    (by vrunm; exact ⟨by simp only [XBinOp.eval, BitVec.xor_self]; rfl, by xonly⟩) fun w0 ⟨hz, o0⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 32) (by decide) (by decide)
    (fun u w => PolyP w.mem dP F (8 * u) ∧ w.gpr .r9 = coeffAddr dP (8 * u) ∧
      w.gpr .rdx = wAddr src (8 * u) ∧ Frame [pR dP] s.mem w.mem ∧ w.xmm .xmm4 = 0 ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → w.xmm r = s.xmm r) ∧ Keep [.r9, .rdx, .rcx] s w ∧
      w.mxcsr = s.mxcsr)
    (fun w o hcx => ⟨fun _ h => absurd h (by bdd_omega),
      by rw [o.keep.gpr (by decide), o0.gpr, h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), o0.gpr, hdx, wAddr]; simp, by rw [o.mem, o0.mem]; exact Frame.refl _ _,
      by rw [o.xmm, hz], fun r h0 h1 h4 => by rw [o.xmm, o0.xmm r (by simp [h4])],
      Keep.trans (⟨fun r _ => by rw [o0.gpr], o0.rd, o0.wr⟩ : Keep [] s w0) (o.keep) |>.mono (by simp),
      by rw [o.mxcsr, o0.mxcsr]⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hz', hx', hk', hm'⟩ => ?_))
    fun w ⟨hP, _, _, hf, _, hx', hk', hm'⟩ => ⟨polyIs_of_toNat fun i hi => hP i (by rw [n_eq] at hi; omega_using [hi]),
      hf, hx', hk', hm'⟩
  obtain hS' : S16 w.mem src F := hS16.frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm
  obtain hwf' : pR dP ∈ w.wr := by rw [hk'.2.2]; exact hwf
  obtain r0 : InRegions (w.rd ++ w.wr) (wAddr src (8 * u)) 16 := by
    rw [hk'.2.1, hk'.2.2, wAddr]; exact CallLay.inRegions_sub hin (by bdd_omega) (by bdd_omega)
  obtain w0 : InRegions w.wr (coeffAddr dP (8 * u)) 16 := ⟨_, hwf', polyR_contains dP (by bdd_omega)⟩
  obtain w1 : InRegions w.wr (coeffAddr dP (8 * u + 4)) 16 := ⟨_, hwf', polyR_contains dP (by bdd_omega)⟩
  obtain a1 : coeffAddr dP (8 * u) + BitVec.ofNat 64 16 = coeffAddr dP (8 * u + 4) := coeffAddr_off _ _ 4
  obtain ll := lanes_load hS' (j := 8 * u) (by bdd_omega)
  vrunm [h9', hdx', r0, w0, w1, a1, sx32, hz']
  refine ⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off,
      Nat.mul_succ],
    by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add, Nat.mul_succ], ?_, ?_, ?_, ?_⟩
  · rw [coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega), coeffAt_write128 _ _ (by bdd_omega) _ (by bdd_omega)]
    split
    · rw [dword_punpckhwd0 _ (by bdd_omega), word_movdqa, ll _ (by bdd_omega)]; dsimp only
      rw [show 8 * u + (4 + (j - (8 * u + 4))) = j by bdd_omega]
    · split
      · rw [dword_punpcklwd0 _ (by bdd_omega), ll _ (by bdd_omega)]; dsimp only
        rw [show 8 * u + (j - 8 * u) = j by bdd_omega]
      · exact hP j (by bdd_omega)
  · exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (polyR_contains dP (by bdd_omega))).writeW
      (List.mem_singleton_self _) _ (polyR_contains dP (by bdd_omega)))
  · intro r h0 h1 h4
    simp only [h0, h1, ite_false]
    exact hx' r h0 h1 h4
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
    exact hk'.gpr (by simp [hr])
  · exact hm'

end VG.Proof.MlKem.X86_64

end

end


/-!
# ML-KEM on x86-64: `vg_mlkem*_kpke_encrypt`

The contract (`kpkeEncK`), what holds throughout the function (`KT`: the
pointers, the saved registers, and that only `scratch` and `ct` change),
and the steps: the prologue, each polynomial primitive inline (`KT.step`
keeps `KT` across one that writes only below the saved registers or to
`ct`), the product (the code of `vg_mlkem*_encrypt_mul` reading `Â` as
`u16`s, inline), and the epilogue. `y` becomes `u32`s with `vunpack`
(`widenIn_ok`); `e₁` and `e₂` are added as `u16`s (`add16In_ok`). `u` and `v`
are compressed by code that multiplies (`EncCE`), in an MXCSR region of
their own (`post_wp`, with `noMx_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The size of `vg_mlkem*_kpke_encrypt`'s `scratch`. -/
abbrev kScrE : Nat := 20480

/-- The ciphertext of `K-PKE.Encrypt` of the inputs in `m`. -/
def encCt (L : Kem) (m : Mem) (a t r msg : Addr) : List Byte :=
  let tHat := decodeVec L.k (bytesAt m t (384 * L.k))
  let ŷ := (vecAtW 16 m r L.k).map ntt
  let e₁ := vecAtW 16 m (r + BitVec.ofNat 64 (512 * L.k)) L.k
  let e₂ := polyAtW 16 m (r + BitVec.ofNat 64 (1024 * L.k))
  let u := addVec ((mulMatTVec L.k (matAtW 16 m a L.k) ŷ).map nttInv) e₁
  let μ := decodeDecompress 1 (bytesAt m msg 32)
  let v := add (add (nttInv (dot tHat ŷ)) e₂) μ
  u.flatMap (compressEncode L.du) ++ compressEncode L.dv v

/-- `vg_mlkem*_kpke_encrypt(ct = rdi, a = rsi, t = rdx, r = rcx, m = r8, scratch = r9)` of the
parameter set `L`. -/
def kpkeEncK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 512 * (L.k * L.k)⟩, ⟨s.gpr .rdx, 384 * L.k⟩, ⟨s.gpr .r8, 32⟩] ∧
    s.wr = [⟨s.gpr .rdi, L.ctLen⟩, ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩, ⟨s.gpr .r9, kScrE⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .rdx, 384 * L.k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .r8, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 384 * L.k⟩ ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 384 * L.k⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨s.gpr .r8, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .r8, 32⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 384 * L.k⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .r9, kScrE⟩ ∧
    (s.gpr .rdi).toNat + L.ctLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 384 * L.k ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 512 * (2 * L.k + 1) ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + kScrE ≤ 2 ^ 64 ∧
    VecReducedW 16 s.mem (s.gpr .rsi) (L.k * L.k) ∧ VecReducedW 16 s.mem (s.gpr .rcx) (2 * L.k + 1)
  post s s' := bytesAt s'.mem (s.gpr .rdi) L.ctLen =
    encCt L s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## `vunpack` inline -/

theorem widenGlue_ok (b f : Ptr) (hb : b.2 < 2 ^ 31) (hf : f.2 < 2 ^ 31) (hfr : f.1 ≠ .rdx) (s : State) :
    WP isa (.block (lea .rdx b ++ lea .r9 f)) s fun s1 =>
      ((s1.gpr .rdx = pa s b ∧ s1.gpr .r9 = pa s f) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat hb, sx_ofNat hf, hfr, List.cons_append, List.nil_append]

theorem vunpack_cs : ∀ r ∈ calleeSaved, ∀ i ∈ instrs vunpack, X86_64.Taint.clobbers i r = false := by
  decide

/-- `widenIn b f`: the polynomial of `u16`s at `b` as `u32`s at `f`. -/
theorem widenIn_ok {b f : Ptr} (hb : b.2 < 2 ^ 31) (hf : f.2 < 2 ^ 31) (hfr : f.1 ≠ .rdx) {s : State} {F : Poly}
    (hS : PolyIsW 16 s.mem (pa s b) F) (hd : (pR (pa s f)).Disjoint ⟨pa s b, 512⟩)
    (hc : Covers ([⟨pa s b, 512⟩] ++ [pR (pa s f)]) (s.rd ++ s.wr)) (hw : Covers [pR (pa s f)] s.wr) :
    WP isa (Kpke16.widenIn b f) s fun s' => IPost s s' [pR (pa s f)] ∧ PolyIs s'.mem (pa s f) F := by
  unfold Kpke16.widenIn
  refine WP.seq (WP.mono (widenGlue_ok b f hb hf hfr s) fun s1 ⟨⟨⟨h1dx, h19⟩, hm1⟩, k1⟩ => ?_)
  refine WP.narrowIn (rd := [⟨pa s b, 512⟩]) (wr := [pR (pa s f)])
    (widen_ok (s := s1.withRegions [⟨pa s b, 512⟩] [pR (pa s f)]) (dP := pa s f) (src := pa s b) (F := F)
      (by simp only [State.withRegions_mem, hm1]; exact hS) (by simp only [State.withRegions_gpr, h19])
      (by simp only [State.withRegions_gpr, h1dx]) (by simp only [State.withRegions_wr]; exact List.mem_singleton_self _)
      (by simp only [State.withRegions_rd, State.withRegions_wr]
          exact ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩) hd)
    (by rw [k1.2.1, k1.2.2]; exact hc) (by rw [k1.2.2]; exact hw) (by decide) fun s' hrd hwr hfr' hg ⟨hP, _⟩ => ?_
  refine ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2, fun r hr => by
      rw [hg r (vunpack_cs r hr), k1.gpr (argRegs_cs r hr)], by rw [hm1] at hfr'; exact hfr'⟩, ?_⟩
  simpa only [State.withRegions_mem] using hP

namespace KpkeEnc

open VG.Impl.MlKem.X86_64.Kpke16

/-- The polynomials and the working space lie below this offset of `scratch`. -/
abbrev oTop : Nat := 19456

/-- The facts of the precondition, by name. -/
structure EP (L : Kem) (σ : State) : Prop where
  rd : σ.rd = [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩, ⟨σ.gpr .rdx, 384 * L.k⟩, ⟨σ.gpr .r8, 32⟩]
  wr : σ.wr = [⟨σ.gpr .rdi, L.ctLen⟩, ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩, ⟨σ.gpr .r9, kScrE⟩]
  cA : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩
  cT : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .rdx, 384 * L.k⟩
  cR : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  cM : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .r8, 32⟩
  cS : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .r9, kScrE⟩
  aR : Region.Disjoint ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  aS : Region.Disjoint ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨σ.gpr .r9, kScrE⟩
  tR : Region.Disjoint ⟨σ.gpr .rdx, 384 * L.k⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  tS : Region.Disjoint ⟨σ.gpr .rdx, 384 * L.k⟩ ⟨σ.gpr .r9, kScrE⟩
  rM : Region.Disjoint ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨σ.gpr .r8, 32⟩
  rS : Region.Disjoint ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨σ.gpr .r9, kScrE⟩
  mS : Region.Disjoint ⟨σ.gpr .r8, 32⟩ ⟨σ.gpr .r9, kScrE⟩
  xC : (retR σ).Disjoint ⟨σ.gpr .rdi, L.ctLen⟩
  xA : (retR σ).Disjoint ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩
  xT : (retR σ).Disjoint ⟨σ.gpr .rdx, 384 * L.k⟩
  xR : (retR σ).Disjoint ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  xM : (retR σ).Disjoint ⟨σ.gpr .r8, 32⟩
  xS : (retR σ).Disjoint ⟨σ.gpr .r9, kScrE⟩
  nC : (σ.gpr .rdi).toNat + L.ctLen ≤ 2 ^ 64
  nA : (σ.gpr .rsi).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64
  nT : (σ.gpr .rdx).toNat + 384 * L.k ≤ 2 ^ 64
  nR : (σ.gpr .rcx).toNat + 512 * (2 * L.k + 1) ≤ 2 ^ 64
  nM : (σ.gpr .r8).toNat + 32 ≤ 2 ^ 64
  nS : (σ.gpr .r9).toNat + kScrE ≤ 2 ^ 64
  redA : VecReducedW 16 σ.mem (σ.gpr .rsi) (L.k * L.k)
  redR : VecReducedW 16 σ.mem (σ.gpr .rcx) (2 * L.k + 1)

theorem ep {L : Kem} {σ : State} (hp : (kpkeEncK L).pre σ) : EP L σ :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27⟩ := hp
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26, h27⟩

/-- The regions of `σ` that the function may change. -/
abbrev chg (L : Kem) (σ : State) : List Region := [⟨σ.gpr .r9, kScrE⟩, ⟨σ.gpr .rdi, L.ctLen⟩]

/-- What holds throughout the function entered in `σ`. -/
structure KT (L : Kem) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = σ.gpr .r9
  rbp : s.gpr .rbp = σ.gpr .rsi
  r12 : s.gpr .r12 = σ.gpr .rdx
  r13 : s.gpr .r13 = σ.gpr .rcx
  r14 : s.gpr .r14 = σ.gpr .r8
  r15 : s.gpr .r15 = σ.gpr .rdi
  saved : ∀ i < 6, s.mem.readW (σ.gpr .r9 + BitVec.ofNat 64 (oKSE + 8 * i)) 64 = σ.gpr (kRegs.getD i .rbx)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  fr : Frame (chg L σ) σ.mem s.mem

section
variable {L : Kem} {σ : State} (E : EP L σ)
include E

omit E in
theorem sub_top : Region.Sub ⟨σ.gpr .r9, oTop⟩ ⟨σ.gpr .r9, kScrE⟩ := Region.sub_prefix (by decide)

/-- A region the steps write: below `oTop` in `scratch`, or in `ct`. -/
abbrev WOk (L : Kem) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨σ.gpr .r9, oTop⟩ ∨ Region.Sub r ⟨σ.gpr .rdi, L.ctLen⟩

/-- A region the steps write is apart from the saved registers and the return address. -/
theorem wok_disj {r : Region} (hr : WOk L σ r) :
    (retR σ).Disjoint r ∧ ∀ i < 6, Region.Disjoint ⟨σ.gpr .r9 + BitVec.ofNat 64 (oKSE + 8 * i), 8⟩ r := by
  rcases hr with hr | hr
  · refine ⟨(E.xS.sub_right sub_top).sub_right hr, fun i hi => ?_⟩
    exact (Offset.disjoint_base (σ.gpr .r9) (d := oKSE + 8 * i) (n := 8) (k := oTop)
      (by simp only [oKSE, oTop]; omega_arith) (by have := E.nS; simp only [oKSE, kScrE] at *; omega_arith)).sub_right hr
  · refine ⟨E.xC.sub_right hr, fun i hi => ?_⟩
    obtain hs : Region.Sub ⟨σ.gpr .r9 + BitVec.ofNat 64 (oKSE + 8 * i), 8⟩ ⟨σ.gpr .r9, kScrE⟩ :=
      Offset.sub_base _ (by simp only [oKSE, kScrE]; omega_arith)
    exact ((E.cS.symm.sub_left hs).sub_right hr)

omit E in
theorem wok_chg {r : Region} (hr : WOk L σ r) : ∃ r' ∈ chg L σ, Region.Sub r r' := by
  rcases hr with hr | hr
  · exact ⟨_, List.mem_cons_self .., fun x hx => sub_top x (hr x hx)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hr⟩

theorem KT.stepF {s s' : State} (h : KT L σ s) {W : List Region} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (hcs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s.gpr r)
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, WOk L σ r) : KT L σ s' := by
  obtain D := fun r hr => wok_disj E (r := r) (hW r hr)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, (hcs .rbx (by simp)).trans h.rbx,
    (hcs .rbp (by simp)).trans h.rbp, (hcs .r12 (by simp)).trans h.r12, (hcs .r13 (by simp)).trans h.r13,
    (hcs .r14 (by simp)).trans h.r14, (hcs .r15 (by simp)).trans h.r15, fun i hi => ?_, ?_,
    h.fr.trans (hf.sub fun r hr => wok_chg (hW r hr))⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (D r hr).2 i hi) (by decide)]
    exact h.saved i hi
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (D r hr).1) (by decide)]
    exact h.ret

theorem KT.step {s s' : State} (h : KT L σ s) {W : List Region} (hP : IPost s s' W)
    (hW : ∀ r ∈ W, WOk L σ r) : KT L σ s' :=
  h.stepF E hP.rd hP.wr hP.rsp (fun r hr => hP.cs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hP.frame hW

/-! ## Inputs -/

omit E in
/-- Bytes apart from `scratch` and `ct` are as on entry. -/
theorem KT.bytes {s : State} (h : KT L σ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ chg L σ, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt σ.mem p n :=
  bytesAt_frame h.fr hd hn

theorem KT.bT {s : State} (h : KT L σ s) : bytesAt s.mem (σ.gpr .rdx) (384 * L.k) = bytesAt σ.mem (σ.gpr .rdx) (384 * L.k) :=
  h.bytes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.tS, E.cT.symm]) (by have := E.nT; omega_arith)

theorem KT.bM {s : State} (h : KT L σ s) : bytesAt s.mem (σ.gpr .r8) 32 = bytesAt σ.mem (σ.gpr .r8) 32 :=
  h.bytes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.mS, E.cM.symm]) (by omega_arith)

/-- Polynomial `i` of `r` (`u16`s), as on entry. -/
theorem KT.rW {s : State} (h : KT L σ s) {i : Nat} (hi : i < 2 * L.k + 1) :
    PolyIsW 16 s.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * i))
      (polyAtW 16 σ.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * i))) := by
  obtain hs : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * i), 512⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine polyIsW16_frame h.fr (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.rS.sub_left hs, E.cR.symm.sub_left hs]
  · have := E.redR i hi
    rwa [show 32 * 16 * i = 512 * i by omega_arith] at this

/-- Polynomial `e` of `a` (`u16`s), as on entry. -/
theorem KT.aW {s : State} (h : KT L σ s) {e : Nat} (he : e < L.k * L.k) :
    PolyIsW 16 s.mem (σ.gpr .rsi + BitVec.ofNat 64 (512 * e))
      (polyAtW 16 σ.mem (σ.gpr .rsi + BitVec.ofNat 64 (512 * e))) := by
  obtain hs : Region.Sub ⟨σ.gpr .rsi + BitVec.ofNat 64 (512 * e), 512⟩ ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine polyIsW16_frame h.fr (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.aS.sub_left hs, E.cA.symm.sub_left hs]
  · have := E.redA e he
    rwa [show 32 * 16 * e = 512 * e by omega_arith] at this

/-! ## The prologue and the epilogue -/

omit E in
theorem proE_eq : proE = [.store (at_ .r9 19456) .rbx, .store (at_ .r9 19464) .rbp, .store (at_ .r9 19472) .r12,
    .store (at_ .r9 19480) .r13, .store (at_ .r9 19488) .r14, .store (at_ .r9 19496) .r15,
    .mov .rbx (.reg .r9), .mov .r15 (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8)] := rfl

omit E in
/-- The six stores of `proE`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ i < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 19456) (v 0)).writeW (a + BitVec.ofNat 64 19464) (v 1)).writeW
      (a + BitVec.ofNat 64 19472) (v 2)).writeW (a + BitVec.ofNat 64 19480) (v 3)).writeW
      (a + BitVec.ofNat 64 19488) (v 4)).writeW (a + BitVec.ofNat 64 19496) (v 5)).readW
      (a + BitVec.ofNat 64 (oKSE + 8 * i)) 64 = v i := by
  intro i hi
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega_arith) only [oKSE, Nat.reduceMul, Nat.reduceAdd, readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_ok : WP isa (.block proE) σ (KT L σ) := by
  obtain hS : ⟨σ.gpr .r9, kScrE⟩ ∈ σ.wr := by rw [E.wr]; simp
  have nS := E.nS
  obtain c : ∀ o, o + 8 ≤ kScrE → (⟨σ.gpr .r9, kScrE⟩ : Region).Contains (σ.gpr .r9 + BitVec.ofNat 64 o) 8 :=
    fun o ho => Offset.contains_base _ ho (by omega_arith)
  obtain w : ∀ o, o + 8 ≤ kScrE → InRegions σ.wr (σ.gpr .r9 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  obtain w0 := w 19456 (by decide); have w1 := w 19464 (by decide); have w2 := w 19472 (by decide)
  obtain w3 := w 19480 (by decide); have w4 := w 19488 (by decide); have w5 := w 19496 (by decide)
  rw [proE_eq]
  refine WP.mono (WP.keep [.rbx, .r15, .rbp, .r12, .r13, .r14] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 19456) (σ.gpr .rbx)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 19464) (σ.gpr .rbp)).writeW (σ.gpr .r9 + BitVec.ofNat 64 19472) (σ.gpr .r12)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 19480) (σ.gpr .r13)).writeW (σ.gpr .r9 + BitVec.ofNat 64 19488) (σ.gpr .r14)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 19496) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r9 ∧ s.gpr .r15 = σ.gpr .rdi ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧
    s.gpr .r13 = σ.gpr .rcx ∧ s.gpr .r14 = σ.gpr .r8)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, h15, hbp, h12, h13, h14⟩, k⟩ => ?_
  obtain hf : Frame [⟨σ.gpr .r9, kScrE⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 19456 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 19464 (by decide))).writeW (List.mem_singleton_self _) _
      (c 19472 (by decide))).writeW (List.mem_singleton_self _) _ (c 19480 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 19488 (by decide))).writeW (List.mem_singleton_self _) _ (c 19496 (by decide)))
  refine ⟨k.2.1, k.2.2, k.gpr (by decide), hbx, hbp, h12, h13, h14, h15, fun i hi => ?_, ?_,
    hf.mono (by simp)⟩
  · rw [hm]
    exact stores_read σ.mem (σ.gpr .r9) (fun i => σ.gpr (kRegs.getD i .rbx)) i hi
  · exact hf.readW (Region.contains_self _ _) (by simpa using E.xS) (by decide)

omit E in
theorem epiE_eq : epiE = [.mov .r15 (.mem (at_ .rbx 19496)), .mov .r14 (.mem (at_ .rbx 19488)),
    .mov .r13 (.mem (at_ .rbx 19480)), .mov .r12 (.mem (at_ .rbx 19472)),
    .mov .rbp (.mem (at_ .rbx 19464)), .mov .rbx (.mem (at_ .rbx 19456))] := rfl

theorem epi_ok {s : State} (h : KT L σ s) :
    WP isa (.block epiE) s fun s' => gprPreserved σ s' ∧ s'.mem = s.mem := by
  have nS := E.nS
  obtain hS : ⟨σ.gpr .r9, kScrE⟩ ∈ s.wr := by rw [h.wr, E.wr]; simp
  obtain i : ∀ j < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (oKSE + 8 * j)) 8 := fun j hj =>
    ⟨_, List.mem_append_right _ hS, by
      rw [h.rbx]; exact Offset.contains_base _ (by simp only [oKSE, kScrE]; omega_arith) (by simp only [oKSE]; omega_arith)⟩
  obtain e : ∀ j < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (oKSE + 8 * j)) 64 = σ.gpr (kRegs.getD j .rbx) :=
    fun j hj => by rw [h.rbx]; exact h.saved j hj
  obtain e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide); have e3 := e 3 (by decide)
  obtain e4 := e 4 (by decide); have e5 := e 5 (by decide)
  obtain i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide); have i3 := i 3 (by decide)
  obtain i4 := i 4 (by decide); have i5 := i 5 (by decide)
  simp only [oKSE, kRegs, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceMul, Nat.reduceAdd]
    at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [epiE_eq]
  refine WP.mono (WP.keep [.r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .r15 = σ.gpr .r15 ∧ s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧
    s'.gpr .rbp = σ.gpr .rbp ∧ s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem)
    (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨⟨fun r hr => ?_, ?_⟩, hm⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## Regions -/

section
variable {s : State} (h : KT L σ s)
include h

theorem inS {o n : Nat} (ho : o + n ≤ kScrE) : InRegions s.wr (σ.gpr .r9 + BitVec.ofNat 64 o) n :=
  ⟨_, by rw [h.wr, E.wr]; simp, Offset.contains_base _ ho (by have := E.nS; simp only [kScrE] at *; omega_arith)⟩

theorem inS' {o n : Nat} (ho : o + n ≤ kScrE) : InRegions (s.rd ++ s.wr) (σ.gpr .r9 + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := inS E h ho
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inCt {o n : Nat} (ho : o + n ≤ L.ctLen) (hn : 0 < n) : InRegions s.wr (σ.gpr .rdi + BitVec.ofNat 64 o) n :=
  ⟨_, by rw [h.wr, E.wr]; simp, Offset.contains_base _ ho (by have := E.nC; omega_arith)⟩

theorem inCt' {o n : Nat} (ho : o + n ≤ L.ctLen) (hn : 0 < n) : InRegions (s.rd ++ s.wr) (σ.gpr .rdi + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := inCt E h ho hn
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inR {o n : Nat} (ho : o + n ≤ 512 * (2 * L.k + 1)) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rcx + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_right _ (by rw [h.wr, E.wr]; simp), Offset.contains_base _ ho (by have := E.nR; omega_arith)⟩

theorem inT {o n : Nat} (ho : o + n ≤ 384 * L.k) : InRegions (s.rd ++ s.wr) (σ.gpr .rdx + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_left _ (by rw [h.rd, E.rd]; simp), Offset.contains_base _ ho (by have := E.nT; omega_arith)⟩

theorem inM {o n : Nat} (ho : o + n ≤ 32) : InRegions (s.rd ++ s.wr) (σ.gpr .r8 + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_left _ (by rw [h.rd, E.rd]; simp), Offset.contains_base _ ho (by have := E.nM; omega_arith)⟩

theorem inA {o n : Nat} (ho : o + n ≤ 512 * (L.k * L.k)) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rsi + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_left _ (by rw [h.rd, E.rd]; simp), Offset.contains_base _ ho (by have := E.nA; omega_arith)⟩

omit E in
theorem retR_eq : retR s = retR σ := by simp only [retR, h.rsp]

omit E in
theorem pa_q (i : Nat) : pa s (qP i) = σ.gpr .r9 + BitVec.ofNat 64 (oQ i) := by simp only [pa, h.rbx]

end

omit E in
/-- A polynomial of the working space below `oTop`. -/
theorem qSub {i : Nat} (hi : i < 14) :
    Region.Sub (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .r9, oTop⟩ :=
  Offset.sub_base _ (by simp only [oQ, oTop]; omega_arith)

omit E in
theorem qScr {i : Nat} (hi : i < 14) :
    Region.Sub (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .r9, kScrE⟩ :=
  fun x hx => sub_top x (qSub hi x hx)

theorem qDisj {i j : Nat} (hi : i < 14) (hj : j < 14) (hij : i ≠ j) :
    (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))).Disjoint (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ j))) :=
  Offset.disjoint _ (by simp only [oQ]; omega_arith) (by have := E.nS; simp only [oQ, kScrE] at *; omega_arith)
    (by have := E.nS; simp only [oQ, kScrE] at *; omega_arith)

/-! ## `t̂` and `y` -/

/-- The bytes of `t̂`. -/
abbrev tB (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) (384 * L.k)

/-- `y[j]`, `e₁[i]` (`j = k + i`) and `e₂` (`j = 2k`), as on entry. -/
abbrev rW (σ : State) (j : Nat) : Poly := polyAtW 16 σ.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * j))

/-- The first `nt` of `t̂` are done. -/
structure ER (L : Kem) (σ : State) (nt : Nat) (s : State) : Prop where
  kt : KT L σ s
  t : ∀ i < nt, PolyIs s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (L.k + i))) (ekT (tB L σ) i)

/-- What the proofs need of the parameter set, decided for each. -/
structure KeWf (L : Kem) : Prop where
  k34 : L.k = 3 ∨ L.k = 4
  du : 0 < L.du ∧ L.du ≤ 11
  dv : 0 < L.dv ∧ L.dv ≤ 11
  ct : L.ctLen < 2 ^ 16

theorem ER.keep {nt : Nat} {s s' : State} (h : ER L σ nt s) {i : Nat} (hi : i < 14) (hk : L.k ≤ 4)
    (hP : IPost s s' [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))]) (ht : ∀ j < nt, L.k + j ≠ i) (hnt : nt ≤ 4) :
    KT L σ s' ∧ ∀ j < nt, PolyIs s'.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (L.k + j))) (ekT (tB L σ) j) := by
  refine ⟨h.kt.step E hP (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub hi)),
    fun j hj => polyIs_frame hP.frame ?_ (h.t j hj)⟩
  intro r hr; rw [List.mem_singleton] at hr; subst hr
  exact qDisj E (by omega_arith) hi (ht j hj)

omit E in
theorem na_rbx (o : Nat) : NA ((.rbx, o) : Ptr) := by simp [NA, argRegs]

theorem t_ok {A : Prims} (hA : PrimsOk A) (W : KeWf L) (hn : A.dec12.noCalls = true) {i : Nat} (hi : i < L.k)
    {s : State} (h : ER L σ i s) : WP isa (tHatE L A i) s (ER L σ (i + 1)) := by
  have hkt := h.kt
  obtain hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega_arith
  obtain bnd : 384 * i + 384 ≤ 384 * L.k := by omega_arith
  obtain e1 : pa s ((.r12, 384 * i) : Ptr) = σ.gpr .rdx + BitVec.ofNat 64 (384 * i) := by simp only [pa, hkt.r12]
  obtain e2 := pa_q hkt (L.k + i)
  obtain H : TwoHi (.r12, 384 * i) (qP (L.k + i)) 384 1024 s :=
    { off := ⟨by omega_arith, by simp only [oQ]; omega_arith⟩
      d := by rw [e1, e2]; exact (E.tS.sub_left (Offset.sub_base _ bnd)).sub_right (qScr (by omega_arith))
      rP := by rw [retR_eq hkt, e1]; exact E.xT.sub_right (Offset.sub_base _ bnd)
      rQ := by rw [retR_eq hkt, e2]; exact E.xS.sub_right (qScr (by omega_arith))
      c := by
        rw [e1, e2]
        exact covers_append (covers_one (inT E hkt bnd)) (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_arith)))
      w := by rw [e2]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega_arith)) }
  refine WP.mono (dec12In_ok hA.dec12.ok hn (na_rbx _) H) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  obtain ⟨kt', ht⟩ := h.keep E (i := L.k + i) (by omega_arith) hk4 hP (fun j hj => by omega_arith) (by omega_arith)
  refine ⟨kt', fun j hj => ?_⟩
  rcases (by omega_arith : j < i ∨ j = i) with hj' | rfl
  · exact ht j hj'
  · rw [e1, ← bytesAt_slice _ _ bnd, hkt.bT E] at hq
    exact hq

/-! ## The products -/

/-- `ŷ`, from `y` on entry. -/
abbrev yHat (L : Kem) (σ : State) : List Poly := (vecAtW 16 σ.mem (σ.gpr .rcx) L.k).map ntt

/-- `NTT⁻¹(Â^⊺ ∘ ŷ)` and `NTT⁻¹(t̂^⊺ ∘ ŷ)`, from the inputs on entry. -/
abbrev prods (L : Kem) (σ : State) : List Poly :=
  ((mulMatTVec L.k (matAtW 16 σ.mem (σ.gpr .rsi) L.k) (yHat L σ)).map nttInv) ++
    [nttInv (dot (decodeVec L.k (tB L σ)) (yHat L σ))]

/-- After the products: the first `nu` of `u` are in `ct`, and the products from `nu` in place. -/
structure EU (L : Kem) (σ : State) (nu : Nat) (s : State) : Prop where
  kt : KT L σ s
  w : ∀ i < L.k + 1, nu ≤ i →
    PolyIs s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k + i))) ((prods L σ).getD i zero)
  u : ∀ i < nu, bytesAt s.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
    compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i)))

omit E in
theorem q_add (b i : Nat) :
    σ.gpr .r9 + BitVec.ofNat 64 (oQ b) + BitVec.ofNat 64 (1024 * i) = σ.gpr .r9 + BitVec.ofNat 64 (oQ (b + i)) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  simp only [oQ]; omega_arith

omit E in
theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem KT.mat {s : State} (h : KT L σ s) :
    matAtW 16 s.mem (σ.gpr .rsi) L.k = matAtW 16 σ.mem (σ.gpr .rsi) L.k := by
  simp only [matAtW, vecAtW]
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  obtain hi := List.mem_range.mp hi
  obtain hj := List.mem_range.mp hj
  obtain he : L.k * i + j < L.k * L.k :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)
  rw [off_add, show 32 * 16 * (L.k * i) + 32 * 16 * j = 512 * (L.k * i + j) by omega_arith]
  exact (h.aW E he).2

theorem mul_ok (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) {s : State} (h : ER L σ L.k s) :
    WP isa (prodE L mul) s (EU L σ 0) := by
  have hkt := h.kt
  obtain hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega_arith
  obtain hkk : 0 < 512 * (L.k * L.k) := by rcases W.k34 with e | e <;> rw [e] <;> decide
  obtain eU := pa_q hkt (2 * L.k)
  obtain eT := pa_q hkt L.k
  obtain eY : pa s ((.r13, 0) : Ptr) = σ.gpr .rcx := by simp only [pa, hkt.r13, add_ofNat_zero]
  obtain sY : Region.Sub ⟨σ.gpr .rcx, 512 * L.k⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩ := Region.sub_prefix (by omega_arith)
  obtain eA : pa s ((.rbp, 0) : Ptr) = σ.gpr .rsi := by simp only [pa, hkt.rbp, add_ofNat_zero]
  obtain eZ : pa s ((.rbx, 0) : Ptr) = σ.gpr .r9 := by simp only [pa, hkt.rbx, add_ofNat_zero]
  have nS := E.nS
  obtain od : ∀ {a n b m : Nat}, a + n ≤ b ∨ b + m ≤ a → a + n ≤ kScrE → b + m ≤ kScrE →
      Region.Disjoint ⟨σ.gpr .r9 + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .r9 + BitVec.ofNat 64 b, m⟩ :=
    fun h1 h2 h3 => Offset.disjoint _ h1 (by simp only [kScrE] at h2; omega_arith) (by simp only [kScrE] at h3; omega_arith)
  obtain od0 : ∀ {a n : Nat}, 4096 ≤ a → a + n ≤ kScrE →
      Region.Disjoint ⟨σ.gpr .r9 + BitVec.ofNat 64 a, n⟩ (cR (σ.gpr .r9)) := fun {a n} h1 h2 => by
    have := od (a := a) (n := n) (b := 0) (m := 4096) (.inr h1) h2 (by decide)
    rwa [add_ofNat_zero] at this
  obtain sV : ∀ {a n : Nat}, a + n ≤ oTop → Region.Sub ⟨σ.gpr .r9 + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .r9, oTop⟩ :=
    fun ha => Offset.sub_base _ ha
  obtain sC : Region.Sub (cR (σ.gpr .r9)) ⟨σ.gpr .r9, oTop⟩ := Region.sub_prefix (by decide)
  obtain sS : ∀ {r : Region}, Region.Sub r ⟨σ.gpr .r9, oTop⟩ → Region.Sub r ⟨σ.gpr .r9, kScrE⟩ :=
    fun hr x hx => sub_top x (hr x hx)
  obtain bU : oQ (2 * L.k) + 1024 * (L.k + 1) ≤ oTop := by simp only [oQ, oTop]; omega_using [hk4]
  obtain bT : oQ L.k + 1024 * L.k ≤ oTop := by simp only [oQ, oTop]; omega_using [hk4]
  obtain cY : Covers [⟨σ.gpr .rcx, 512 * L.k⟩] (s.rd ++ s.wr) := by
    have := covers_one (inR E hkt (o := 0) (n := 512 * L.k) (by omega_arith))
    rwa [add_ofNat_zero] at this
  obtain cA : Covers [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩] (s.rd ++ s.wr) := by
    have := covers_one (inA E hkt (o := 0) (n := 512 * (L.k * L.k)) (by omega_arith) hkk)
    rwa [add_ofNat_zero] at this
  obtain cZ : ∀ {X : List Region}, (∀ {o n : Nat}, o + n ≤ kScrE → InRegions X (σ.gpr .r9 + BitVec.ofNat 64 o) n) →
      Covers [cR (σ.gpr .r9)] X := fun hX => by
    have := covers_one (hX (o := 0) (n := 4096) (by decide))
    rwa [add_ofNat_zero] at this
  refine WP.mono (glueIn_ok hv hn (emGlue_ok (qP (2 * L.k)) (.rbp, 0) (qP L.k) (.r13, 0) (.rbx, 0)
      ⟨by simp only [oQ]; omega_using [hk4], by decide, by simp only [oQ]; omega_using [hk4], by decide, by decide⟩
      (by simp [NA, argRegs]) (na_rbx _) (by simp [NA, argRegs]) (na_rbx _) s)
    (rd := [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩, vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ L.k)) L.k,
      ⟨σ.gpr .rcx, 512 * L.k⟩])
    (wr := [vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k))) (L.k + 1), cR (σ.gpr .r9)])
    (fun s1 hV hm k1 => ?_) ?_ ?_) fun s' ⟨hP, s1, hV, hm, k1, hq⟩ => ?_
  · simp only [encMulK16, encMulKG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2, hm, eU, eT, eY, eA, eZ]
    obtain rS := fun {R : Region} (hR : Region.Sub R ⟨σ.gpr .r9, kScrE⟩) =>
      retR_keep k1 (by rw [retR_eq hkt]; exact E.xS.sub_right hR) [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩,
        vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ L.k)) L.k, ⟨σ.gpr .rcx, 512 * L.k⟩]
        [vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k))) (L.k + 1), cR (σ.gpr .r9)]
    refine ⟨trivial, trivial, E.aS.symm.sub_left (sS (sV bU)),
      od (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      (E.rS.symm.sub_left (sS (sV bU))).sub_right sY,
      od0 (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]), E.aS.sub_right (sS sC),
      od0 (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      (E.rS.sub_left sY).sub_right (sS sC),
      rS (sS (sV bU)), retR_keep k1 (by rw [retR_eq hkt]; exact E.xA) _ _, rS (sS (sV bT)),
      retR_keep k1 (by rw [retR_eq hkt]; exact E.xR.sub_right sY) _ _,
      rS (sS sC), fun e he => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [show 32 * 16 * e = 512 * e by omega_arith]; exact (hkt.aW E he).1
    · rw [q_add]; exact (h.t i hi).1
    · rw [show 32 * 16 * i = 512 * i by omega_arith]; exact (hkt.rW E (by omega_arith)).1
  · exact covers_append (covers_cons cA (covers_cons (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_using [hk4])))
      (covers_cons cY covers_nil)))
      (covers_cons (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_using [hk4]))) (covers_cons (cZ (inS' E hkt))
        covers_nil))
  · exact covers_cons (covers_one (inS E hkt (by simp only [oQ, kScrE]; omega_using [hk4]))) (covers_cons (cZ (inS E hkt))
      covers_nil)
  simp only [encMulK16, encMulKG, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2.1, hm, eU, eT, eY, eA] at hq
  obtain hy : (vecAtW 16 s.mem (σ.gpr .rcx) L.k).map ntt = yHat L σ := by
    simp only [yHat, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    rw [show 32 * 16 * j = 512 * j by omega_arith, (hkt.rW E (by have := List.mem_range.mp hj; omega_arith)).2]
  obtain ht : vecAt s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ L.k)) L.k = decodeVec L.k (tB L σ) := by
    rw [← List.take_of_length_le (l := tB L σ) (i := 384 * L.k) (by rw [bytesAt_length]), KPke.decodeVec_take]
    simp only [vecAt]
    exact List.map_congr_left fun j hj => by rw [q_add]; exact (h.t j (List.mem_range.mp hj)).2
  rw [hy, ht, hkt.mat E] at hq
  refine ⟨hkt.step E hP fun r hr => ?_, fun i hi _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [.inl (sV bU), .inl sC]
  · rw [← q_add]; exact hq.2 i hi

/-! ## `u` and `v` -/

/-- The compressions `vg_mlkem*_kpke_encrypt` runs in its MXCSR region,
verified for widths `wu` and `wv` that include `d_u` and `d_v`. -/
structure EncCE (L : Kem) (wu wv : List Nat) : Prop where
  u : CEImpl "" L.ceU wu
  v : CEImpl "" L.ceV wv
  du : L.du ∈ wu
  dv : L.dv ∈ wv

/-- The registers the code in the MXCSR region writes. -/
abbrev postRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10]


omit E in
omit E in
theorem pa_r15 {s : State} (h : KT L σ s) (o : Nat) : pa s (.r15, o) = σ.gpr .rdi + BitVec.ofNat 64 o := by
  simp only [pa, h.r15]

theorem u_ok {wu wv : List Nat} (K : EncCE L wu wv) (W : KeWf L)
    (hnC : L.ceU.noCalls = true) {i : Nat} (hi : i < L.k) {s : State}
    (h : EU L σ i s) : WP isa (uE L i) s (EU L σ (i + 1)) := by
  have hkt := h.kt
  obtain hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega_arith
  have hct := W.ct
  have hdu := W.du
  obtain bnd := Decaps.uSlice_le L hi
  obtain bR : 512 * (L.k + i) + 512 ≤ 512 * (2 * L.k + 1) := by omega_arith
  -- `u[i]`
  obtain e1 : pa s ((.r13, 512 * (L.k + i)) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * (L.k + i)) := by
    simp only [pa, hkt.r13]
  obtain eF := pa_q hkt (2 * L.k + i)
  obtain hw0 := h.w i (by omega_arith) (Nat.le_refl _)
  obtain hR := hkt.rW E (i := L.k + i) (by omega_arith)
  obtain HA : Add16Hi (qP (2 * L.k + i)) (.r13, 512 * (L.k + i)) s :=
    { off := ⟨by simp only [oQ]; omega_arith, by omega_arith⟩
      redF := by rw [eF]; exact hw0.1
      redG := by rw [e1]; exact hR.1
      d := by rw [eF, e1]; exact (E.rS.symm.sub_left (qScr (by omega_arith))).sub_right (Offset.sub_base _ bR)
      rF := by rw [retR_eq hkt, eF]; exact E.xS.sub_right (qScr (by omega_arith))
      rG := by rw [retR_eq hkt, e1]; exact E.xR.sub_right (Offset.sub_base _ bR)
      c := by
        rw [eF, e1]
        exact covers_append (covers_one (inR E hkt bR)) (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_arith)))
      w := by rw [eF]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega_arith)) }
  refine WP.seq (WP.mono (add16In_ok (by simp) HA) fun s2 ⟨hP2, hq2⟩ => ?_)
  rw [eF, e1, hw0.2, hR.2] at hq2
  rw [eF] at hP2
  obtain kt2 := hkt.step E hP2 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega_arith))
  -- to `ct`
  obtain eQ := pa_q kt2 (2 * L.k + i)
  obtain eO := pa_r15 kt2 (32 * L.du * i)
  obtain HC : CEHi wu (qP (2 * L.k + i)) (.r15, 32 * L.du * i) L.du s2 :=
    { off := ⟨by simp only [oQ]; omega_arith, by omega_arith⟩
      dw := K.du
      red := by rw [eQ]; exact hq2.1
      dj := by rw [eQ, eO]; exact (E.cS.symm.sub_left (qScr (by omega_arith))).sub_right (Offset.sub_base _ bnd)
      rF := by rw [retR_eq kt2, eQ]; exact E.xS.sub_right (qScr (by omega_arith))
      rO := by rw [retR_eq kt2, eO]; exact E.xC.sub_right (Offset.sub_base _ bnd)
      c := by
        rw [eQ, eO]
        exact covers_append (covers_one (inS' E kt2 (by simp only [oQ, kScrE]; omega_arith)))
          (covers_one (inCt' E kt2 bnd (by omega_arith)))
      w := by rw [eO]; exact covers_one (inCt E kt2 bnd (by omega_arith)) }
  refine WP.mono (ceIn_ok K.u hnC (by simp [NA, argRegs]) HC) fun s3 ⟨hP3, hq3⟩ => ?_
  rw [eO] at hP3 hq3
  rw [eQ, hq2.2] at hq3
  obtain kt3 := kt2.step E hP3 fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inr (Offset.sub_base _ bnd)
  obtain dC : ∀ {a : Nat}, a < 14 → ∀ r ∈ [(⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i), 32 * L.du⟩ : Region)],
      (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))).Disjoint r := fun ha r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (E.cS.symm.sub_left (qScr ha)).sub_right (Offset.sub_base _ bnd)
  refine ⟨kt3, fun i' hi' hn => ?_, fun i' hi' => ?_⟩
  · refine polyIs_frame hP3.frame (dC (by omega_arith)) (polyIs_frame hP2.frame ?_ (h.w i' hi' (by omega_arith)))
    intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact qDisj E (by omega_arith) (by omega_arith) (by omega_arith)
  · rcases (by omega_arith : i' < i ∨ i' = i) with hi'' | rfl
    · have bnd' := Decaps.uSlice_le L (i := i') (by omega_arith)
      obtain dj : Region.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i'), 32 * L.du⟩
          ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i), 32 * L.du⟩ :=
        Offset.disjoint _ (.inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi'')) (by omega_arith) (by omega_arith)
      obtain dq : ∀ {a : Nat}, a < 14 → ∀ r ∈ [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))],
          Region.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i'), 32 * L.du⟩ r := fun ha r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (E.cS.sub_left (Offset.sub_base _ bnd')).sub_right (qScr ha)
      rw [bytesAt_frame hP3.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dj) (by omega_arith),
        bytesAt_frame hP2.frame (dq (by omega_arith)) (by omega_arith)]
      exact h.u i' hi''
    · exact hq3

omit E in
/-- `k` consecutive pieces of `c` bytes. -/
theorem bytesAt_cat (m : Mem) (p : Addr) (c : Nat) (f : Nat → List Byte) :
    ∀ k, (∀ i < k, bytesAt m (p + BitVec.ofNat 64 (c * i)) c = f i) → bytesAt m p (c * k) = (List.range k).flatMap f
  | 0, _ => rfl
  | k + 1, h => by
    rw [Nat.mul_succ, bytesAt_add, bytesAt_cat m p c f k fun i hi => h i (by omega_arith), h k (by omega_arith),
      List.range_succ, List.flatMap_append, List.flatMap_singleton]

omit E in
theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

omit E in
theorem list_eq_map_getD {X : List Poly} {k : Nat} (h : X.length = k) :
    X = (List.range k).map fun i => X.getD i zero := by
  subst h
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

omit E in
/-- The ciphertext, from its pieces. -/
theorem ct_eq {m : Mem}
    (hu : ∀ i < L.k, bytesAt m (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))))
    (hv : bytesAt m (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * L.k)) (32 * L.dv) =
      compressEncode L.dv (add (add ((prods L σ).getD L.k zero) (rW σ (2 * L.k)))
        (decodeDecompress 1 (bytesAt σ.mem (σ.gpr .r8) 32)))) :
    bytesAt m (σ.gpr .rdi) L.ctLen = encCt L σ.mem (σ.gpr .rsi) (σ.gpr .rdx) (σ.gpr .rcx) (σ.gpr .r8) := by
  obtain hX : ((mulMatTVec L.k (matAtW 16 σ.mem (σ.gpr .rsi) L.k) (yHat L σ)).map nttInv).length = L.k := by
    simp [mulMatTVec]
  obtain hP : ∀ i < L.k, (prods L σ).getD i zero =
      ((mulMatTVec L.k (matAtW 16 σ.mem (σ.gpr .rsi) L.k) (yHat L σ)).map nttInv).getD i zero := fun i hi => by
    simp only [prods, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hX]; exact hi)]
  obtain hPk : (prods L σ).getD L.k zero = nttInv (dot (decodeVec L.k (tB L σ)) (yHat L σ)) := by
    rw [prods, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hX]), hX, Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  rw [show L.ctLen = 32 * L.du * L.k + 32 * L.dv by
      simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, Nat.mul_assoc],
    bytesAt_add, hv, hPk, bytesAt_cat m _ (32 * L.du) _ L.k hu]
  simp only [encCt]
  rw [list_eq_map_getD hX, vecAtW, KPke.addVec_map, List.flatMap_map]
  refine congr (congrArg HAppend.hAppend (flatMap_congr fun i hi => ?_)) ?_
  · rw [hP i (List.mem_range.mp hi), rW, off_add, show 512 * L.k + 32 * 16 * i = 512 * (L.k + i) by omega_arith]
  · rw [rW, show 512 * (2 * L.k) = 1024 * L.k by omega_arith]

theorem v_ok {A : Prims} (hA : PrimsOk A) {wu wv : List Nat} (K : EncCE L wu wv) (W : KeWf L)
    (hnA : A.add.noCalls = true) (hnC : L.ceV.noCalls = true) (hnD : A.codecs.dd.noCalls = true)
    {s : State} (h : EU L σ L.k s) :
    WP isa (vE L A) s fun s' => KT L σ s' ∧
      bytesAt s'.mem (σ.gpr .rdi) L.ctLen = encCt L σ.mem (σ.gpr .rsi) (σ.gpr .rdx) (σ.gpr .rcx) (σ.gpr .r8) := by
  have hkt := h.kt
  obtain hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega_arith
  have hct := W.ct
  have hdv := W.dv
  have hdu := W.du
  obtain bnd : 32 * L.du * L.k + 32 * L.dv ≤ L.ctLen := by
    simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, ← Nat.mul_assoc]
  obtain bR : 512 * (2 * L.k) + 512 ≤ 512 * (2 * L.k + 1) := by omega_arith
  obtain e3 : 2 * L.k + L.k = 3 * L.k := by omega_arith
  -- `NTT⁻¹(t̂^⊺ ∘ ŷ) + e₂`
  obtain e1 : pa s ((.r13, 512 * (2 * L.k)) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * (2 * L.k)) := by
    simp only [pa, hkt.r13]
  obtain eF := pa_q hkt (3 * L.k)
  obtain hw0 := h.w L.k (by omega_arith) (Nat.le_refl _)
  rw [e3] at hw0
  obtain hR := hkt.rW E (i := 2 * L.k) (by omega_arith)
  obtain HA2 : Add16Hi (qP (3 * L.k)) (.r13, 512 * (2 * L.k)) s :=
    { off := ⟨by simp only [oQ]; omega_arith, by omega_arith⟩
      redF := by rw [eF]; exact hw0.1
      redG := by rw [e1]; exact hR.1
      d := by rw [eF, e1]; exact (E.rS.symm.sub_left (qScr (by omega_arith))).sub_right (Offset.sub_base _ bR)
      rF := by rw [retR_eq hkt, eF]; exact E.xS.sub_right (qScr (by omega_arith))
      rG := by rw [retR_eq hkt, e1]; exact E.xR.sub_right (Offset.sub_base _ bR)
      c := by
        rw [eF, e1]
        exact covers_append (covers_one (inR E hkt bR)) (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_arith)))
      w := by rw [eF]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega_arith)) }
  obtain dQ : ∀ {a b : Nat}, a < 14 → b < 14 → a ≠ b →
      ∀ r ∈ [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ b))], (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))).Disjoint r :=
    fun ha hb hne r hr => by rw [List.mem_singleton] at hr; subst hr; exact qDisj E ha hb hne
  obtain dC : ∀ {a : Nat}, a < 14 → ∀ i < L.k, ∀ r ∈ [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))],
      Region.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i), 32 * L.du⟩ r := fun ha i hi r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (E.cS.sub_left (Offset.sub_base _ (Decaps.uSlice_le L hi))).sub_right (qScr ha)
  refine WP.seq (WP.mono (add16In_ok (by simp) HA2) fun s2 ⟨hP2, hq2⟩ => ?_)
  rw [eF, e1, hw0.2, hR.2] at hq2
  rw [eF] at hP2
  obtain kt2 := hkt.step E hP2 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega_arith))
  obtain hu2 : ∀ i < L.k, bytesAt s2.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))) := fun i hi => by
    rw [bytesAt_frame hP2.frame (dC (by omega_arith) i hi) (by omega_arith)]; exact h.u i hi
  obtain HA : ∀ {s : State}, KT L σ s → Reduced s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (3 * L.k))) →
      Reduced s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (3 * L.k + 1))) → AccHi (qP (3 * L.k)) (eP L) s :=
    fun {s} kt rf rg =>
    { off := ⟨by simp only [oQ]; omega_arith, by simp only [oQ]; omega_arith⟩
      redF := by rw [pa_q kt]; exact rf
      redG := by rw [pa_q kt]; exact rg
      d := by rw [pa_q kt, pa_q kt]; exact qDisj E (by omega_arith) (by omega_arith) (by omega_arith)
      rF := by rw [retR_eq kt, pa_q kt]; exact E.xS.sub_right (qScr (by omega_arith))
      rG := by rw [retR_eq kt, pa_q kt]; exact E.xS.sub_right (qScr (by omega_arith))
      c := by
        rw [pa_q kt, pa_q kt]
        exact covers_append (covers_one (inS' E kt (by simp only [oQ, kScrE]; omega_arith)))
          (covers_one (inS' E kt (by simp only [oQ, kScrE]; omega_arith)))
      w := by rw [pa_q kt]; exact covers_one (inS E kt (by simp only [oQ, kScrE]; omega_arith)) }
  -- `μ`
  obtain eB : pa s2 ((.r14, 0) : Ptr) = σ.gpr .r8 + BitVec.ofNat 64 0 := by simp only [pa, kt2.r14]
  obtain eE2 := pa_q kt2 (3 * L.k + 1)
  obtain bM : 0 + 32 * 1 ≤ 32 := by decide
  obtain HD : DDHi compressWidths (.r14, 0) (eP L) 1 s2 :=
    { off := ⟨by decide, by simp only [oQ]; omega_arith⟩
      dw := by decide
      dj := by rw [eB, eE2]; exact (E.mS.sub_left (Offset.sub_base _ bM)).sub_right (qScr (by omega_arith))
      rB := by rw [retR_eq kt2, eB]; exact E.xM.sub_right (Offset.sub_base _ bM)
      rF := by rw [retR_eq kt2, eE2]; exact E.xS.sub_right (qScr (by omega_arith))
      c := by
        rw [eB, eE2]
        exact covers_append (covers_one (inM E kt2 bM)) (covers_one (inS' E kt2 (by simp only [oQ, kScrE]; omega_arith)))
      w := by rw [eE2]; exact covers_one (inS E kt2 (by simp only [oQ, kScrE]; omega_arith)) }
  refine WP.seq (WP.mono (ddIn_ok (Codecs.ddI A.codecs) hnD (na_rbx _) HD) fun s3 ⟨hP3, hq3⟩ => ?_)
  rw [eE2] at hP3 hq3
  rw [eB, add_ofNat_zero, show 32 * 1 = 32 from rfl, kt2.bM E] at hq3
  obtain kt3 := kt2.step E hP3 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega_arith))
  obtain hv3 := polyIs_frame hP3.frame (dQ (by omega_arith) (by omega_arith) (by omega_arith)) hq2
  obtain hu3 : ∀ i < L.k, bytesAt s3.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))) := fun i hi => by
    rw [bytesAt_frame hP3.frame (dC (by omega_arith) i hi) (by omega_arith)]; exact hu2 i hi
  -- `v`
  obtain eF3 := pa_q kt3 (3 * L.k)
  obtain eG3 := pa_q kt3 (3 * L.k + 1)
  refine WP.seq (WP.mono (accIn_ok hA.add.ok hnA (g := eP L) (by simp) (HA kt3 hv3.1 hq3.1)) fun s4 ⟨hP4, hq4⟩ => ?_)
  rw [eF3, eG3, hv3.2, hq3.2] at hq4
  rw [eF3] at hP4
  obtain kt4 := kt3.step E hP4 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega_arith))
  obtain hu4 : ∀ i < L.k, bytesAt s4.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))) := fun i hi => by
    rw [bytesAt_frame hP4.frame (dC (by omega_arith) i hi) (by omega_arith)]; exact hu3 i hi
  -- to `ct`
  obtain eQ := pa_q kt4 (3 * L.k)
  obtain eO := pa_r15 kt4 (32 * L.du * L.k)
  obtain HC : CEHi wv (qP (3 * L.k)) (.r15, 32 * L.du * L.k) L.dv s4 :=
    { off := ⟨by simp only [oQ]; omega_arith, by omega_arith⟩
      dw := K.dv
      red := by rw [eQ]; exact hq4.1
      dj := by rw [eQ, eO]; exact (E.cS.symm.sub_left (qScr (by omega_arith))).sub_right (Offset.sub_base _ bnd)
      rF := by rw [retR_eq kt4, eQ]; exact E.xS.sub_right (qScr (by omega_arith))
      rO := by rw [retR_eq kt4, eO]; exact E.xC.sub_right (Offset.sub_base _ bnd)
      c := by
        rw [eQ, eO]
        exact covers_append (covers_one (inS' E kt4 (by simp only [oQ, kScrE]; omega_arith)))
          (covers_one (inCt' E kt4 bnd (by omega_arith)))
      w := by rw [eO]; exact covers_one (inCt E kt4 bnd (by omega_arith)) }
  refine WP.mono (ceIn_ok K.v hnC (by simp [NA, argRegs]) HC) fun s5 ⟨hP5, hq5⟩ => ?_
  rw [eO] at hP5 hq5
  rw [eQ, hq4.2] at hq5
  refine ⟨kt4.step E hP5 fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inr (Offset.sub_base _ bnd), ct_eq (fun i hi => ?_) hq5⟩
  rw [bytesAt_frame hP5.frame (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi))
      (by have := Decaps.uSlice_le L hi; omega_arith) (by omega_arith)) (by omega_arith)]
  exact hu4 i hi

end

/-! ## The function -/

/-- The prologue, `t̂`, `y` and the products. -/
theorem pre_wp {L : Kem} {A : Prims} (hA : PrimsOk A) (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hn12 : A.dec12.noCalls = true) {σ : State} (hp : (kpkeEncK L).pre σ) :
    WP isa (kpkeEncPre L A mul) σ (EU L σ 0) := by
  obtain E := ep hp
  refine WP.seq (WP.mono (pro_ok E) fun s₁ h₁ => ?_)
  obtain d₀ : ER L σ 0 s₁ := ⟨h₁, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (seqR_ok (I := fun i s => ER L σ i s) L.k 0
    (fun i _ hi s h => t_ok E hA W hn12 (by omega_arith) h) s₁ d₀) fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  exact mul_ok E W hv hn h₂

/-- `u`, `v` and the epilogue. -/
theorem post_wp {L : Kem} {A : Prims} (hA : PrimsOk A) {wu wv : List Nat} (K : EncCE L wu wv)
    (W : KeWf L) (hnA : A.add.noCalls = true) (hnU : L.ceU.noCalls = true) (hnV : L.ceV.noCalls = true)
    (hnD : A.codecs.dd.noCalls = true)
    {σ : State} (hp : (kpkeEncK L).pre σ) {s : State} (h : EU L σ 0 s) :
    WP isa (kpkeEncPost L A) s fun s' => gprPreserved σ s' ∧ (kpkeEncK L).post σ s' := by
  obtain E := ep hp
  have hkt := h.kt
  obtain hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega_arith
  obtain wM : ∀ r ∈ [mxR (σ.gpr .r9)], WOk L σ r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inl (Offset.sub_base _ (by decide))
  obtain dM : ∀ r ∈ [mxR (σ.gpr .r9)], Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact E.cS.sub_right (Offset.sub_base _ (by decide))
  unfold kpkeEncPost
  refine WP.seq (WP.mono (noMx_ok (sP := σ.gpr .r9)
    (Q := fun s' => KT L σ s' ∧
      bytesAt s'.mem (σ.gpr .rdi) L.ctLen = encCt L σ.mem (σ.gpr .rsi) (σ.gpr .rdx) (σ.gpr .rcx) (σ.gpr .r8))
    (fun s₁ k₁ f₁ => ?_)) fun s₃ ⟨s₂, ⟨kt₂, hm₂⟩, f₃, k₃⟩ => ?_)
  · have h₁ : EU L σ 0 s₁ :=
      ⟨hkt.stepF E k₁.2.1 k₁.2.2 (k₁.gpr (by decide)) (fun r hr => k₁.gpr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) f₁ wM,
        fun i hi hn => polyIs_frame f₁ (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inr (by simp only [oQ]; omega_arith)) (by simp only [oQ]; omega_arith)
            (by decide)) (h.w i hi hn),
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    refine WP.seq (WP.mono (seqR_ok (I := fun i s => EU L σ i s) L.k 0
      (fun i _ hi s h => u_ok E K W hnU (by omega_arith) h) s₁ h₁) fun s₅ h₅ => ?_)
    rw [Nat.zero_add] at h₅
    exact v_ok E hA K W hnA hnV hnD h₅
  · have kt₃ : KT L σ s₃ := kt₂.stepF E k₃.2.1 k₃.2.2 (k₃.gpr (by simp)) (fun r _ => k₃.gpr (by simp)) f₃ wM
    exact WP.mono (epi_ok E kt₃) fun s₇ ⟨hg, hm⟩ => ⟨hg, by
      show bytesAt _ _ _ = _
      rw [hm, bytesAt_frame f₃ dM (by have := E.nC; omega_arith)]; exact hm₂⟩

theorem kpkeEnc_wp {L : Kem} {A : Prims} (hA : PrimsOk A) {wu wv : List Nat} (K : EncCE L wu wv)
    (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hn12 : A.dec12.noCalls = true) (hnA : A.add.noCalls = true)
    (hnU : L.ceU.noCalls = true) (hnV : L.ceV.noCalls = true) (hnD : A.codecs.dd.noCalls = true)
    {σ : State} (hp : (kpkeEncK L).pre σ) :
    WP isa (kpkeEnc L A mul) σ fun s' => gprPreserved σ s' ∧ (kpkeEncK L).post σ s' :=
  WP.seq (WP.mono (pre_wp hA W hv hn hn12 hp) fun _ h => post_wp hA K W hnA hnU hnV hnD hp h)

theorem kpkeEnc_correct {L : Kem} {A : Prims} (hA : PrimsOk A) {wu wv : List Nat} (K : EncCE L wu wv)
    (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hn12 : A.dec12.noCalls = true) (hnA : A.add.noCalls = true)
    (hnU : L.ceU.noCalls = true) (hnV : L.ceV.noCalls = true) (hnD : A.codecs.dd.noCalls = true)
    (hctl : ctlOk (kpkeEnc L A mul) = true) (σ : State) (hp : (kpkeEncK L).pre σ) :
    ∃ t s', Exec isa (kpkeEnc L A mul) σ t s' ∧ abiPreserved σ s' ∧ (kpkeEncK L).post σ s' := by
  obtain ⟨t, s', he, hg, hq⟩ := kpkeEnc_wp hA K W hv hn hn12 hnA hnU hnV hnD hp
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hq⟩

end KpkeEnc

end VG.Proof.MlKem.X86_64
