module
public import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Rows
public import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Gb
public import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Mem
public import VerifiedGarbage.Proof.Argon2.X86_64.Initialize

import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Cols
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Ends
import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Rows
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Argon2.X86_64.Finish
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on x86-64 with AVX-512: the first and last XOR

`initChunk k` writes 64 bytes of X XOR Y to R, and `finishChunk n k` writes
words `8n…8n+7` of rows `2k` and `2k + 1` of the output: `cv` XOR R. Each
is proven for any prefix of its chunks (`init_prefix`, `finish_prefix`).
-/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Proof.Argon2.X86_64 (off Scratch ea_at Inputs blockAt_get xorBlock_get input_unchanged
  scratch_unchanged)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl qword_pxor ifp ifn)
open VG.Proof.Poly1305.X86_64.Avx512 (qz qz_zbin qz_vshufi32x4)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

theorem cv_idx (m : Mem) (p : Addr) {a b : Nat} (h : a = b) (ha : a < 128) (hb : b < 128) :
    (cv m p)[a]'ha = (cv m p)[b]'hb := by
  subst h; rfl

/-! ## R -/

theorem initChunk_ok {k : Nat} (hk : k < 16) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block (initChunk k)) s fun t => ∃ v : BitVec 512,
      (∀ q < 8, v.extractLsb' (64 * q) 64 =
        s.mem.readW (off x (64 * k + 8 * q)) 64 ^^^ s.mem.readW (off y (64 * k + 8 * q)) 64) ∧
      t.mem = s.mem.writeW (off p (64 * k)) v ∧ VKeep s t := by
  have lx : InRegions (s.rd ++ s.wr) (off x (64 * k)) 64 :=
    ⟨_, hin.xread, Offset.contains_base x (by omega_arith) (by omega_arith)⟩
  have ly : InRegions (s.rd ++ s.wr) (off y (64 * k)) 64 :=
    ⟨_, hin.yread, Offset.contains_base y (by omega_arith) (by omega_arith)⟩
  have w := hs.write (d := 64 * k) (n := 64) (by omega_arith)
  apply WP.of_runBlock
  simp only [initChunk, z, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512,
    State.store512_eq, ea_at, State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem,
    ZOp.exec_gpr, ZOp.exec_mem, ZOp.exec_wr, hs.reg, hin.xreg, hin.yreg, lx, ly, w, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, ((((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans
    (zop_vkeep _ _)).trans (setMem_vkeep _ _))⟩
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by decide)
  simp (disch := omega_arith) only [zmm_qz _ _ hq, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor,
    qz_lane, qz_load, ↓reduceIte, reduceCtorEq, Offset.add_add]

/-- The chunks `k < n` of R hold `r`. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val / 8 < n → m.readW (off p (8 * i.val)) 64 = r[i]

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat} (hn : n < 16)
    (h : Initialized m p r n) {v : BitVec 512} (hv : ∀ q < 8, ∀ hi : 8 * n + q < 128,
      v.extractLsb' (64 * q) 64 = r[8 * n + q]'hi) :
    Initialized (m.writeW (off p (64 * n)) v) p r (n + 1) := by
  intro i hi
  have hi' := i.isLt
  rw [read_write512 _ p (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
  by_cases e : i.val / 8 = n
  · have q := hv (i.val % 8) (Nat.mod_lt _ (by decide)) (by omega_arith)
    simp only [show 8 * n + i.val % 8 = i.val by omega_arith] at q
    rw [ifp (by omega_arith), show (8 * i.val - 64 * n) / 8 = i.val % 8 by omega_arith, q]
    rfl
  · rw [ifn (by omega_arith)]
    exact h i (by omega_arith)

/-- Initialize the first `n` chunks of R, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 16) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initChunk)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ VKeep s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, VKeep.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (initChunk_ok (by omega_arith) (hs.of_vkeep hk) (hin.of_vkeep hk)).mono ?_
    rintro u ⟨v, hv, hmem, hk'⟩
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hmem]
      refine initialized_step (by omega_arith) ht fun q hq hi => ?_
      rw [hv q hq, show 64 * n + 8 * q = 8 * (8 * n + q) by omega_arith,
        input_unchanged hf hin.xsep ⟨8 * n + q, hi⟩, input_unchanged hf hin.ysep ⟨8 * n + q, hi⟩]
      simp only [xorBlock, Vector.getElem_zipWith, blockAt, Vector.getElem_ofFn]
      rfl
    · rw [hmem]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base p (by omega_arith) (by omega_arith))

/-- R, initialized. -/
theorem initialized_all {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r 16) :
    blockAt m p = r := by
  apply Vector.ext; intro i hi
  have := h ⟨i, hi⟩ (by simp only; omega_arith)
  rw [← blockAt_get m p ⟨i, hi⟩] at this
  exact this

/-! ## The output -/

/-- The words of `cv` that `vshufi32x4` with `0x88` and `0xdd` join. -/
theorem finQ : ∀ n < 2, ∀ k < 4, ∀ q < 8,
    cvIdx (2 * n + q / 4) k (2 * sel4 (0x88 : BitVec 8).toNat (q / 2) + q % 2) = 32 * k + 8 * n + q ∧
    cvIdx (2 * n + q / 4) k (2 * sel4 (0xdd : BitVec 8).toNat (q / 2) + q % 2) =
      32 * k + 16 + 8 * n + q := by
  decide

/-- Quadword `q` of `vshufi32x4 d, a, b, sel`, from the halves of `a` and `b`. -/
theorem qz_shuf (s : State) (d a b : XReg) (n : BitVec 8) {q : Nat} (hq : q < 8) :
    qz ((ZOp.vshufi32x4 d a b n).exec s) d q =
      (if q < 4 then qz s a else qz s b) (2 * sel4 n.toNat (q / 2) + q % 2) := by
  rw [qz_vshufi32x4 _ _ _ _ _ _ hq, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  by_cases h : q < 4
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false h)]

def joinOps : List ZOp :=
  [.vshufi32x4 .xmm2 .xmm0 .xmm1 0x88, .vshufi32x4 .xmm3 .xmm0 .xmm1 0xdd,
    .zbin .vpxord .xmm2 .xmm2 .xmm4, .zbin .vpxord .xmm3 .xmm3 .xmm5]

theorem join_qz2 (s : State) {q : Nat} (hq : q < 8) :
    qz (zrun joinOps s) .xmm2 q =
      (if q / 2 < 2 then qz s .xmm0 else qz s .xmm1) (2 * sel4 (0x88 : BitVec 8).toNat (q / 2) + q % 2) ^^^
        qz s .xmm4 q := by
  simp only [joinOps, zrun, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor, qz_lane, reduceCtorEq,
    ↓reduceIte, qz_vshufi32x4 _ _ _ _ _ _ hq]

theorem join_qz3 (s : State) {q : Nat} (hq : q < 8) :
    qz (zrun joinOps s) .xmm3 q =
      (if q / 2 < 2 then qz s .xmm0 else qz s .xmm1) (2 * sel4 (0xdd : BitVec 8).toNat (q / 2) + q % 2) ^^^
        qz s .xmm5 q := by
  have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0xdd : BitVec 8).toNat (q / 2)
  simp only [joinOps, zrun, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor, qz_lane, reduceCtorEq,
    ↓reduceIte, qz_vshufi32x4 _ _ _ _ _ _ hq]
  split <;> simp (disch := omega_arith) only [qz_vshufi32x4, reduceCtorEq, ↓reduceIte]

def finLoads (n k : Nat) : List Instr :=
  [.vmovdqu32Load .xmm0 (at_ .rcx (colOff (2 * n) k)),
    .vmovdqu32Load .xmm1 (at_ .rcx (colOff (2 * n + 1) k)),
    .vmovdqu32Load .xmm4 (at_ .rcx (256 * k + 64 * n)),
    .vmovdqu32Load .xmm5 (at_ .rcx (256 * k + 128 + 64 * n))]

def finStores (n k : Nat) : List Instr :=
  [.vmovdqu32Store (at_ .rdx (256 * k + 64 * n)) .xmm2,
    .vmovdqu32Store (at_ .rdx (256 * k + 128 + 64 * n)) .xmm3]

theorem finishChunk_eq (n k : Nat) :
    finishChunk n k = finLoads n k ++ joinOps.map .zop ++ finStores n k := rfl

theorem finLoads_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (finLoads n k)) s fun t =>
      (∀ e (he : e < 8), qz t .xmm0 e = (cv s.mem p)[cvIdx (2 * n) k e]'(by simp only [cvIdx]; omega_arith)) ∧
      (∀ e (he : e < 8), qz t .xmm1 e = (cv s.mem p)[cvIdx (2 * n + 1) k e]'(by simp only [cvIdx]; omega_arith)) ∧
      (∀ q < 8, qz t .xmm4 q = s.mem.readW (off p (8 * (32 * k + 8 * n + q))) 64) ∧
      (∀ q < 8, qz t .xmm5 q = s.mem.readW (off p (8 * (32 * k + 16 + 8 * n + q))) 64) ∧
      t.mem = s.mem ∧ VKeep s t := by
  have r0 := colOff_read hs (c := 2 * n) (k := k) (by omega_arith) hk
  have r1 := colOff_read hs (c := 2 * n + 1) (k := k) (by omega_arith) hk
  have r4 := hs.read (d := 256 * k + 64 * n) (n := 64) (by omega_arith)
  have r5 := hs.read (d := 256 * k + 128 + 64 * n) (n := 64) (by omega_arith)
  apply WP.of_runBlock
  simp only [finLoads, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg, r0, r1, r4, r5, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun e he => ?_, fun e he => ?_, fun q hq => ?_, fun q hq => ?_, trivial,
    (((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans (setZ_vkeep _ _ _ _ _ _)).trans
      (setZ_vkeep _ _ _ _ _ _)⟩
  · simp only [qz_load _ _ _ _ _ he, reduceCtorEq, ↓reduceIte]
    exact cv_chunk _ _ (by omega_arith) hk he
  · simp only [qz_load _ _ _ _ _ he, reduceCtorEq, ↓reduceIte]
    exact cv_chunk _ _ (by omega_arith) hk he
  · simp only [qz_load _ _ _ _ _ hq, reduceCtorEq, ↓reduceIte, Offset.add_add]
    exact congrArg (Mem.readW _ · 64) (congrArg (off p) (by omega_arith))
  · simp only [qz_load _ _ _ _ _ hq, ↓reduceIte, Offset.add_add]
    exact congrArg (Mem.readW _ · 64) (congrArg (off p) (by omega_arith))

theorem finStores_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {out : Addr}
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (finStores n k)) s fun t =>
      t.mem = (s.mem.writeW (off out (256 * k + 64 * n)) (s.zmm .xmm2)).writeW
        (off out (256 * k + 128 + 64 * n)) (s.zmm .xmm3) ∧ VKeep s t := by
  have w1 : InRegions s.wr (off out (256 * k + 64 * n)) 64 :=
    ⟨_, hw, Offset.contains_base out (by omega_arith) (by omega_arith)⟩
  have w2 : InRegions s.wr (off out (256 * k + 128 + 64 * n)) 64 :=
    ⟨_, hw, Offset.contains_base out (by omega_arith) (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [finStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, State.setMem_zmm, ho, w1, w2, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, (setMem_vkeep _ _).trans (setMem_vkeep _ _)⟩

theorem finishChunk_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {p out : Addr}
    (hs : Scratch s p) (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (finishChunk n k)) s fun t => ∃ v w : BitVec 512,
      (∀ q (hq : q < 8), v.extractLsb' (64 * q) 64 = (cv s.mem p)[32 * k + 8 * n + q]'(by omega_arith) ^^^
        s.mem.readW (off p (8 * (32 * k + 8 * n + q))) 64) ∧
      (∀ q (hq : q < 8), w.extractLsb' (64 * q) 64 = (cv s.mem p)[32 * k + 16 + 8 * n + q]'(by omega_arith) ^^^
        s.mem.readW (off p (8 * (32 * k + 16 + 8 * n + q))) 64) ∧
      t.mem = (s.mem.writeW (off out (256 * k + 64 * n)) v).writeW (off out (256 * k + 128 + 64 * n)) w ∧
      VKeep s t := by
  rw [finishChunk_eq, WP.block_append_iff, WP.block_append_iff]
  refine (finLoads_ok hn hk hs).mono ?_
  rintro t1 ⟨h0, h1, h4, h5, hm1, hk1⟩
  refine WP.of_runBlock ⟨_, runBlock_zops _ _, ?_⟩
  have hk2 := hk1.trans (zrun_vkeep joinOps t1)
  refine (finStores_ok (out := out) hn hk (hk2.gpr ▸ ho) (hk2.wr ▸ hw)).mono ?_
  rintro t ⟨hm, hk3⟩
  refine ⟨_, _, fun q hq => ?_, fun q hq => ?_, by rw [hm, zrun_mem, hm1], hk2.trans hk3⟩
  · have fq := (finQ n hn k hk q hq).1
    have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0x88 : BitVec 8).toNat (q / 2)
    rw [zmm_qz _ _ hq, join_qz2 _ hq, h4 q hq]
    by_cases h2 : q / 2 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), h0 _ (by omega_arith)]
      rw [show q / 4 = 0 by omega_arith, Nat.add_zero] at fq
      rw [cv_idx _ _ fq]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), h1 _ (by omega_arith)]
      rw [show q / 4 = 1 by omega_arith] at fq
      rw [cv_idx _ _ fq]
  · have fq := (finQ n hn k hk q hq).2
    have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0xdd : BitVec 8).toNat (q / 2)
    rw [zmm_qz _ _ hq, join_qz3 _ hq, h5 q hq]
    by_cases h2 : q / 2 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), h0 _ (by omega_arith)]
      rw [show q / 4 = 0 by omega_arith, Nat.add_zero] at fq
      rw [cv_idx _ _ fq]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), h1 _ (by omega_arith)]
      rw [show q / 4 = 1 by omega_arith] at fq
      rw [cv_idx _ _ fq]

end VG.Proof.Argon2.X86_64.Avx512
