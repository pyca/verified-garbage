module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Crypt
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Two
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 and Poly1305 together (x86-64): the prologue with the last bytes' block

`Stitch.prologueX`: for the lengths `xTest` picks (at least 513 bytes, 1 to
64 past a multiple of 512, `XLen`), `twoKs` computes the one-time key's block
and the block of the last bytes in the two lanes of `Avx2Tail`'s code for one
set (`Avx2Tail.twoC_ok`), from the state at `ctx + 608` (counter 0) with the
lane increments `0` and `1 + 8 ⌊len / 512⌋`, into `ctx[672, 800)`; otherwise
the prologue calls `vg_chacha20_xor` as `prologue` does. Either way it ends as
`prologue` does (`PostP`), and if 1 to 64 bytes are left after the whole
chunks, their keystream is at `ctx + 736` (`TailKs`).

`twoKs` is proven with its permissions narrowed to the state copy and the 320
bytes from `ctx + 672` (`twoKsN_ok`), which `RegionModel.wp_narrow` moves to
`open`'s: they are `stR (stA c')` and `bufR (bfA c')` for `c' = ctx + 544`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR storeAll pairs_ok pairsCode constPairs constPairs_le
  consts_eq consts_mem storeAll_frame)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (IncsC cOf twoC_ok)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState serialize)

variable {e : Bool}

/-! ## The test -/

/-- The lengths whose last bytes' block the prologue computes. -/
abbrev XLen (L : Nat) : Prop := 513 ≤ L ∧ (L - 1) % 512 < 64

theorem sub1and511 (x : BitVec 64) (h : 1 ≤ x.toNat) :
    ((x - BitVec.ofNat 64 1) &&& BitVec.ofNat 64 511).toNat = (x.toNat - 1) % 512 := by
  have hx := x.isLt
  have hs : (x - BitVec.ofNat 64 1).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 1).toNat = 1 from rfl,
      show 2 ^ 64 - 1 + x.toNat = (x.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_and, hs, show (BitVec.ofNat 64 511).toNat = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `xTest`, from `s`: `CF` set for the lengths (`r13`) `XLen` holds of, and
only `rax`, `r10` and the flags written. -/
theorem xTest_ok (s : State) :
    WP isa (.block xTest) s fun t =>
      isa.eval .b t = some (decide (XLen (s.gpr .r13).toNat)) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x1 : BitVec.signExtend 64 (1#32) = 1#64 := by decide
  have x511 : BitVec.signExtend 64 (511#32) = 511#64 := by decide
  have x513 : BitVec.signExtend 64 (513#32) = 513#64 := by decide
  have x64 : BitVec.signExtend 64 (64#32) = 64#64 := by decide
  have e64 : (64#64).toNat = 64 := rfl
  have e513 : (513#64).toNat = 513 := rfl
  rw [show xTest = [.mov .rax (.reg .r13), .alu .sub .rax (.imm (BitVec.ofNat 32 1)),
    .alu .and .rax (.imm (BitVec.ofNat 32 511)), .mov32 .r10 (.imm (BitVec.ofNat 32 64)),
    .alu .cmp .r13 (.imm (BitVec.ofNat 32 513)), .cmov .b .rax (.reg .r10), .alu .cmp .rax (.imm (BitVec.ofNat 32 64))]
    from rfl]
  by_cases h : (s.gpr .r13).toNat < 513
  · have hc : ¬ XLen (s.gpr .r13).toNat := fun ⟨h1, _⟩ => by omega
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, readSrc, x1, x511, x513, x64,
      Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval, h, hc,
      readSrc32, State.setReg32, decide_true, decide_false, Option.some.injEq, exists_eq_left', ↓reduceIte,
      reduceCtorEq, e64, e513]
    exact ⟨by decide, fun r h1 h2 => by simp only [h1, h2, ite_false], rfl, rfl, rfl, rfl⟩
  · have hm := sub1and511 (s.gpr .r13) (by omega)
    have hc : XLen (s.gpr .r13).toNat ↔ ((s.gpr .r13).toNat - 1) % 512 < 64 := ⟨fun h => h.2, fun h' => ⟨by omega, h'⟩⟩
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, readSrc, x1, x511, x513, x64,
      Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval, h, hc,
      readSrc32, State.setReg32, decide_false, Bool.false_eq_true, Option.some.injEq, exists_eq_left',
      ↓reduceIte, reduceCtorEq, e64, e513, hm]
    exact ⟨trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], rfl, rfl, rfl, rfl⟩

/-! ## The lane increments -/

/-- The quadwords `storeQ 224 [0, 0, 0, 0]` stores. -/
def tzPairs : List (Nat × BitVec 64) := [(224, 0), (232, 0), (240, 0), (248, 0)]

theorem tz_eq : Impl.ChaCha20.X86_64.Avx2Tail.storeQ 224 [0, 0, 0, 0] = pairsCode tzPairs := rfl

theorem tzPairs_le : ∀ p ∈ tzPairs, p.1 + 8 ≤ 320 := by decide

/-- The counter of the block of the last bytes, as `twoConsts` computes it from
the length `x`. -/
abbrev xCtr (x : BitVec 64) : BitVec 32 := (((x >>> 9) <<< 3) + 1).setWidth 32

theorem xCtr_eq (x : BitVec 64) : xCtr x = BitVec.ofNat 32 (1 + 8 * (x.toNat / 512)) := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [xCtr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (2 : Nat) ^ 9 = 512 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (show x.toNat / 512 * 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x.toNat / 512 * 8 + 1 < 2 ^ 64 by omega)]
  omega

/-- Read back a stored quadword. -/
local macro "zread" : tactic => `(tactic|
  simp (disch := decide) only [storeAll, tzPairs, List.foldl_cons, List.foldl_nil, Nat.reduceAdd,
    VG.Proof.ChaCha20.X86_64.Avx2.readW64_off, Mem.readW_writeW_self64])

theorem incsC_mem (m : Mem) (buf : Addr) (v : BitVec 32) :
    IncsC ((storeAll buf tzPairs m).writeW (buf + BitVec.ofNat 64 240) v) buf v.toNat := by
  intro p hp
  by_cases h4 : p = 4
  · subst h4
    rw [ite_eq_left rfl, show 4 * (56 + 4) = 240 from rfl, Mem.readW_writeW_self32, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [ite_eq_right h4, Mem.readW_writeW_sep (Offset.sep buf (d := 4 * (56 + p)) (n := 4) (e := 240) (k := 4)
      (by omega) (by lit_omega) (by lit_omega)) (by decide)]
    have E := VG.X86_64.readW_extract (storeAll buf tzPairs m)
      (buf + BitVec.ofNat 64 (8 * ((56 + p) / 2))) (w := 64) (k := 4 * ((56 + p) % 2)) (n := 4) (by omega)
    rw [VG.Proof.ChaCha20.X86_64.Avx2.add_ofNat, show 8 * ((56 + p) / 2) + 4 * ((56 + p) % 2) = 4 * (56 + p) by omega] at E
    rw [← E]
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 6 ∨ p = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]; zread; decide)

/-! ## The two blocks, on narrowed permissions -/

/-- Stores at offsets below `d` keep what is from `buf + d` on. -/
theorem storeAll_frameLo {buf : Addr} {d : Nat} (hd : d ≤ 320) (ps : List (Nat × BitVec 64))
    (hps : ∀ p ∈ ps, p.1 + 8 ≤ d) (m : Mem) : Frame [⟨buf, d⟩] m (storeAll buf ps m) := by
  induction ps generalizing m with
  | nil => exact Frame.refl _ _
  | cons p ps ih =>
    rw [storeAll, List.foldl_cons, ← storeAll]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base buf (hps p (List.mem_cons_self ..)) (by have := hps p (List.mem_cons_self ..); omega))).trans
      (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _)

theorem constPairs_lo : ∀ p ∈ constPairs, p.1 + 8 ≤ 224 := by decide

/-- The counter of the block of the last bytes, stored as a doubleword. -/
theorem cStore_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block [.mov .rax (.reg .r13), .shift .shr .rax 9, .shift .shl .rax 3, .alu .add .rax (.imm 1),
      .store32 (at_ .rcx 240) .rax]) s fun t =>
      t.mem = s.mem.writeW (buf + BitVec.ofNat 64 240) (xCtr (s.gpr .r13)) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have o : InRegions s.wr (buf + BitVec.ofNat 64 240) 4 := ⟨_, hb, Offset.contains_base _ (by decide) (by decide)⟩
  have se : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, execAlu, readSrc, arithFlags,
    VG.Proof.ChaCha20.X86_64.Avx2.ea_at, State.store32, State.setReg, State.setFlags, hrcx, se, o,
    reduceCtorEq, ite_true, ite_false, Nat.reduceLeDiff, and_self, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h => by simp [h], trivial⟩

theorem twoConsts_eq : ptr .rcx .r15 672 ++ twoConsts ++ ([.mov .r9 (.reg .rcx)] : List Instr) =
    ptr .rcx .r15 672 ++ (pairsCode tzPairs ++ (([.mov .rax (.reg .r13), .shift .shr .rax 9, .shift .shl .rax 3,
      .alu .add .rax (.imm 1), .store32 (at_ .rcx 240) .rax] : List Instr) ++
      (pairsCode constPairs ++ ([.mov .r9 (.reg .rcx)] : List Instr)))) := by
  simp only [twoConsts, tz_eq, VG.Proof.ChaCha20.X86_64.Avx2.consts_eq, List.append_assoc]

theorem movR9_ok (s : State) :
    WP isa (.block [.mov .r9 (.reg .rcx)]) s fun t =>
      t.gpr .r9 = s.gpr .rcx ∧ (∀ r, r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, gpr_setReg, mem_setReg, rd_setReg,
    wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun r h => by simp [h], trivial, trivial, trivial⟩

/-- The memory after `twoKs`'s constants, at `buf`. -/
abbrev twoMem (buf : Addr) (x : BitVec 64) (m : Mem) : Mem :=
  storeAll buf constPairs ((storeAll buf tzPairs m).writeW (buf + BitVec.ofNat 64 240) (xCtr x))

/-- `twoKs`'s constants: the lane increments and the masks at `buf`
(`r15 + 672`), in `r9` and `rcx`. -/
theorem twoPre_ok {buf : Addr} {s : State} (hbuf : off (s.gpr .r15) 672 = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block (ptr .rcx .r15 672 ++ twoConsts ++ ([.mov .r9 (.reg .rcx)] : List Instr))) s fun t =>
      t.mem = twoMem buf (s.gpr .r13) s.mem ∧ t.gpr .r9 = buf ∧ t.gpr .rcx = buf ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [twoConsts_eq]
  refine WP.block_append (WP.mono (ptr_ok .rcx .r15 (k := 672) (by lit_omega) s)
    fun s₁ ⟨rcx₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  rw [hbuf] at rcx₁
  refine WP.block_append (WP.mono (pairs_ok tzPairs tzPairs_le rcx₁ (by rw [wr₁]; exact hb))
    fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (cStore_ok (buf := buf) (s := s₂) (by rw [g₂ _ (by decide), rcx₁]) (by rw [wr₂, wr₁]; exact hb))
    fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_)
  refine WP.block_append (WP.mono (pairs_ok (buf := buf) constPairs constPairs_le (s := s₃)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), rcx₁]) (by rw [wr₃, wr₂, wr₁]; exact hb))
    fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.mono (movR9_ok s₄) fun s₅ ⟨r9₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  have hc : s₄.gpr .rcx = buf := by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), rcx₁]
  have h13 : s₂.gpr .r13 = s.gpr .r13 := by rw [g₂ _ (by decide), g₁ _ (by decide)]
  refine ⟨by rw [m₅, m₄, m₃, m₂, h13, m₁], by rw [r9₅, hc], by rw [g₅ _ (by decide), hc],
    fun r h₁ h₂ h₃ => by rw [g₅ r h₃, g₄ r h₁, g₃ r h₁, g₂ r h₁, g₁ r h₂],
    by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩

theorem twoMem_consts (buf : Addr) (x : BitVec 64) (m : Mem) : Consts (twoMem buf x m) buf := consts_mem _ _

theorem twoMem_incs (buf : Addr) (x : BitVec 64) (m : Mem) : IncsC (twoMem buf x m) buf (xCtr x).toNat :=
  VG.Proof.ChaCha20.X86_64.Avx2Tail.incsC_frame (incsC_mem m buf (xCtr x))
    (storeAll_frameLo (d := 224) (by decide) constPairs constPairs_lo _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base buf (Nat.le_refl _) (by decide))
theorem endB_ok (s : State) :
    WP isa (.block (([.vop .vzeroupper] : List Instr) ++ ptr .rsi .r15 128)) s fun t =>
      t.gpr .rsi = off (s.gpr .r15) 128 ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr :=
  WP.block_append (WP.mono (VG.Proof.ChaCha20.X86_64.Avx2.vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (ptr_ok .rsi .r15 (k := 128) (by lit_omega) s₁) fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ =>
      ⟨by rw [e₂, g₁], fun r h => by rw [g₂ r h, g₁], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩)

/-- `twoKs`, with its permissions: the state copy at `stA c'` and `bfA c'`
for `c' = c + 544` (`c` in `r15`), whose first 128 bytes it leaves the
keystream of the blocks at counters `0` and `xCtr len` in. -/
theorem twoKsN_ok (vl : Bool) {c : Addr} {s : State} (hr15 : s.gpr .r15 = c)
    (hrdi : s.gpr .rdi = stA (c + BitVec.ofNat 64 544))
    (hwr : s.wr = [stR (stA (c + BitVec.ofNat 64 544)), bufR (bfA (c + BitVec.ofNat 64 544))]) :
    WP isa (twoKs vl) s fun t =>
      (∀ k < 128, t.mem (bfA (c + BitVec.ofNat 64 544) + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt s.mem (stA (c + BitVec.ofNat 64 544)))
          (cOf (xCtr (s.gpr .r13)).toNat (k / 64))))).getD (k % 64) 0) ∧
      t.gpr .rsi = off c 128 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb : off c 672 = bfA (c + BitVec.ofNat 64 544) := by
    rw [off_eq]; simp only [bfA, Offset.add_add]
  unfold twoKs
  refine WP.seq (WP.mono (twoPre_ok (buf := bfA (c + BitVec.ofNat 64 544)) (by rw [hr15, hb]) (by rw [hwr]; simp))
    fun s₁ ⟨m₁, r9₁, rcx₁, g₁, rd₁, wr₁⟩ => ?_)
  have hc : VG.Proof.ChaCha20.X86_64.Avx512Tail.Ctx 0 s₁ := ctx0 (c := c + BitVec.ofNat 64 544)
    (by rw [g₁ _ (by decide) (by decide) (by decide), hrdi]) r9₁ (by rw [wr₁, hwr]; simp) (by rw [wr₁, hwr]; simp)
  refine WP.seq (WP.mono (twoC_ok (c := (xCtr (s.gpr .r13)).toNat) vl hc (by rw [m₁, r9₁]; exact twoMem_consts _ _ _)
    (by rw [m₁, r9₁]; exact twoMem_incs _ _ _)) fun s₂ ⟨ks₂, _, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (endB_ok s₂) fun s₃ ⟨rsi₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have F₁ : Frame [bufR (bfA (c + BitVec.ofNat 64 544))] s.mem s₁.mem := by
    rw [m₁]
    exact ((storeAll_frame (List.mem_singleton_self _) tzPairs tzPairs_le _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).trans
      (storeAll_frame (List.mem_singleton_self _) constPairs constPairs_le _)
  have rdi₁ : s₁.gpr .rdi = stA (c + BitVec.ofNat 64 544) := by
    rw [g₁ .rdi (by decide) (by decide) (by decide), hrdi]
  have S₁ : VG.Proof.ChaCha20.X86_64.Avx512Tail.S0 s₁ = stateAt s.mem (stA (c + BitVec.ofNat 64 544)) := by
    show stateAt s₁.mem (s₁.gpr .rdi) = _
    rw [rdi₁]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_bf
  refine ⟨fun k hk => ?_, by rw [rsi₃, g₂, g₁ _ (by decide) (by decide) (by decide), hr15],
    fun r h₁ h₂ h₃ h₄ => by rw [g₃ r h₄, g₂, g₁ r h₁ h₂ h₃], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  rw [m₃, ← r9₁, ks₂ k hk, S₁]

/-- If 1 to 64 bytes are left after the whole chunks, their keystream at
`ctx + 736`, as `prologueX` leaves it. -/
def TailKs (s₀ : State) (m : Mem) : Prop :=
  512 ≤ L s₀ → 1 ≤ L s₀ % 512 → L s₀ % 512 ≤ 64 → ∀ k < L s₀ % 512,
    m (off (cx s₀) (736 + k)) = (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (512 * (L s₀ / 512) + k) 0

theorem TailKs.of_xlen {s₀ : State} {m : Mem} (h : ¬ XLen (L s₀)) : TailKs s₀ m :=
  fun h₁ h₂ h₃ => absurd ⟨by omega, by omega⟩ h

theorem TailKs.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : TailKs s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ 736 64).Disjoint r) : TailKs s₀ m' := fun h₁ h₂ h₃ k hk => by
  rw [← h h₁ h₂ h₃ k hk]
  exact hf _ fun r hr hc => hd r hr _ (contains_sub s₀ (k := 736) (n := 64) (by omega) (by omega) (by lit_omega)) hc

theorem ctr_toNat (S : CState) {v : BitVec 32} {n : Nat} (h : v = BitVec.ofNat 32 n) : ctr S v.toNat = ctr S n := by
  simp only [ctr, BitVec.ofNat_toNat, BitVec.setWidth_eq, h]

/-- The passes for which `twoKs` computes all the call would: none (`open`'s),
and 512. -/
abbrev XPass (pass : Nat) : Prop := pass = 0 ∨ pass = 512

theorem XPass.ok {pass : Nat} (h : XPass pass) : PassOk 448 pass := by
  rcases h with rfl | rfl
  · exact .inl rfl
  · exact .inr (.inr ⟨rfl, rfl⟩)

/-- With `twoKs`, the call would have computed only the one-time key's block. -/
theorem mOf_xlen {pass L : Nat} (h : XPass pass) (hx : XLen L) : mOf 448 pass L = 0 := by
  rcases h with rfl | rfl <;> simp only [mOf, splitOf] <;> rw [ite_eq_right (by omega)] <;> simp <;> omega

/-- `twoKs`, from where the prologue would call `vg_chacha20_xor`: as after
that call (`AfterF`), and the keystream of the last bytes at `ctx + 736`. -/
theorem twoKs_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀)
    {s : State} (h : FArgs v.callee.fold pass s₀ s) (hx : XLen (L s₀)) :
    WP isa (twoKs v.callee.vl) s fun s' => AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem := by
  have hf := (avx2_of v hv).1
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm0 : mOf v.callee.fold pass (L s₀) = 0 := by rw [hf]; exact mOf_xlen hpass hx
  have eA : ∀ k, bfA (cx s₀ + BitVec.ofNat 64 544) + BitVec.ofNat 64 k = off (cx s₀) (672 + k) := by
    intro k; rw [off_eq]; simp only [bfA, Offset.add_add]
  have eS : stA (cx s₀ + BitVec.ofNat 64 544) = off (cx s₀) 608 := by
    rw [off_eq]; simp only [stA, Offset.add_add]
  have eB : bfA (cx s₀ + BitVec.ofNat 64 544) = off (cx s₀) 672 := by
    rw [off_eq]; simp only [bfA, Offset.add_add]
  let w : List Region := [stR (stA (cx s₀ + BitVec.ofNat 64 544)), bufR (bfA (cx s₀ + BitVec.ofNat 64 544))]
  have hw : Covers w s.wr := covers_sub hp h.wr w (by
    intro r hr
    simp only [w, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨608, by rw [eS], by show 608 + 64 ≤ 1696; omega⟩
    · exact ⟨672, by rw [eB], by show 672 + 320 ≤ 1696; omega⟩)
  have hn : (twoKs v.callee.vl).noCalls = true := by cases v.callee.vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := w)
    (twoKsN_ok v.callee.vl (s := s.withRegions [] w) (c := cx s₀) h.r15 (by rw [State.withRegions_gpr, h.rdi, eS]) rfl)
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ rd' wr' f' hP => ?_
  obtain ⟨ks₀, rsi₀, g₀, -, -⟩ := hP
  have ks' : ∀ k < 128, s'.mem (bfA (cx s₀ + BitVec.ofNat 64 544) + BitVec.ofNat 64 k) =
      (serialize (Spec.ChaCha20.block (ctr (stateAt (s.withRegions [] w).mem (stA (cx s₀ + BitVec.ofNat 64 544)))
        (cOf (xCtr ((s.withRegions [] w).gpr .r13)).toNat (k / 64))))).getD (k % 64) 0 := ks₀
  have rsi' : s'.gpr .rsi = off (cx s₀) 128 := rsi₀
  have f'' : Frame w s.mem s'.mem := f'
  have rd'' : s'.rd = s.rd := rd'
  have wr'' : s'.wr = s.wr := wr'
  have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → s'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    have := (g₀ r h₁ h₂ h₃ h₄ : s'.gpr r = (s.withRegions [] w).gpr r)
    rwa [State.withRegions_gpr] at this
  have dw : ∀ {k n : Nat}, k + n ≤ 608 ∨ 992 ≤ k → k + n ≤ 1696 → ∀ r ∈ w, (sub s₀ k n).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [w, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [eS]; exact sub_disj s₀ (b := 608) (m := 64) (by omega) (by omega) (by lit_omega)
    · rw [eB]; exact sub_disj s₀ (b := 672) (m := 320) (by omega) (by omega) (by lit_omega)
  have S₀ : stateAt (s.withRegions [] w).mem (stA (cx s₀ + BitVec.ofNat 64 544)) = initState (K s₀) 0 (N s₀) := by
    rw [State.withRegions_mem, eS, h.st']
  have r13 : (s.withRegions [] w).gpr .r13 = s₀.gpr .r9 := by rw [State.withRegions_gpr, h.r13]
  refine ⟨⟨rsi',
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), h.r14],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), h.r13],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), h.r12],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), h.rbx],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), h.rbp],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), h.rsp],
    by rw [rd'', h.rd], by rw [wr'', h.wr], h.saved.frame f'' (dw (by omega) (by lit_omega)),
    h.fine.trans (f''.sub fun r hr => ?_),
    by rw [stateAt_frame f'' (dw (k := 64) (n := 64) (by omega) (by lit_omega)), h.st], fun k hk => ?_⟩,
    fun h₁ h₂ h₃ k hk => ?_⟩
  · simp only [w, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, by rw [eS]; exact sub_sub s₀ (by omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, by rw [eB]; exact sub_sub s₀ (by omega) (by lit_omega) (by lit_omega)⟩
  · rw [hm0] at hk ⊢
    have := ks' k (by omega)
    rw [S₀, show k / 64 = 0 by omega, show k % 64 = k by omega] at this
    rw [← eA, this, VG.Proof.ChaCha20.keystream_getD _ hk, show k / 64 = 0 by omega, show k % 64 = k by omega]
    simp only [cOf, ite_true, VG.Proof.ChaCha20.ctr_zero]
  · have := ks' (64 + k) (by omega)
    rw [S₀, show (64 + k) / 64 = 1 by omega, show (64 + k) % 64 = k by omega, r13] at this
    rw [show 736 + k = 672 + (64 + k) by omega, ← eA, this,
      VG.Proof.ChaCha20.keystream_getD _ (by omega : 512 * (L s₀ / 512) + k < L s₀),
      show (512 * (L s₀ / 512) + k) / 64 = 8 * (L s₀ / 512) by omega,
      show (512 * (L s₀ / 512) + k) % 64 = k by omega, ← initState_ctr]
    simp only [cOf, show (1 : Nat) ≠ 0 by decide, ite_false]
    rw [ctr_toNat _ (xCtr_eq _)]

/-- `prologueX`'s choice and the keystream: `twoKs` or the call of `vg_chacha20_xor`. -/
theorem prologueXM_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀) {s : State} (h : FArgs v.callee.fold pass s₀ s) :
    WP isa (.seq (.block xTest) (.ite .b (twoKs v.callee.vl) (.call v.callee.name v.callee.code))) s fun s' =>
      AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem := by
  refine WP.seq (WP.mono (xTest_ok s) fun s₁ ⟨cf₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have h₁ : FArgs v.callee.fold pass s₀ s₁ :=
    ⟨by rw [g₁ _ (by decide) (by decide), h.rdi], by rw [g₁ _ (by decide) (by decide), h.rsi],
      by rw [g₁ _ (by decide) (by decide), h.rdx], by rw [g₁ _ (by decide) (by decide), h.rcx],
      by rw [g₁ _ (by decide) (by decide), h.r15], by rw [g₁ _ (by decide) (by decide), h.r14],
      by rw [g₁ _ (by decide) (by decide), h.r13], by rw [g₁ _ (by decide) (by decide), h.r12],
      by rw [g₁ _ (by decide) (by decide), h.rbx], by rw [g₁ _ (by decide) (by decide), h.rbp],
      by rw [g₁ _ (by decide) (by decide), h.rsp], by rw [rd₁, h.rd], by rw [wr₁, h.wr],
      by rw [m₁]; exact h.saved, by rw [m₁]; exact h.fine, by rw [m₁]; exact h.st, by rw [m₁]; exact h.st',
      fun k hk => by rw [m₁]; exact h.zero k hk⟩
  have e13 : (s.gpr .r13).toNat = L s₀ := by rw [h.r13]
  rw [e13] at cf₁
  refine WP.ite (decide (XLen (L s₀))) cf₁ (fun hx => ?_) (fun hx => ?_)
  · exact twoKs_ok v hv hpass hp h₁ (of_decide_eq_true hx)
  · exact WP.mono (foldCall_ok v hp h₁) fun s' a => ⟨a, TailKs.of_xlen (of_decide_eq_false hx)⟩

/-- The prologue with the last bytes' block: as `prologue`, and their keystream
at `ctx + 736`. -/
theorem prologueX_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀) :
    WP isa (prologueX { v.callee with pass := pass }) (entryS s₀) fun s =>
      PostP v.callee.fold pass s₀ s ∧ TailKs s₀ s.mem := by
  have hP : PassOk v.callee.fold pass := by rw [(avx2_of v hv).1]; exact hpass.ok
  refine WP.seq (WP.mono (prologueA_ok v.fold_le hP (wide_of v) hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (prologueXM_ok v hv hpass hp h₁) fun s₂ ⟨a₂, t₂⟩ => ?_)
  refine WP.mono (prologueBF_ok v.fold_le hp a₂) fun s₃ ⟨p₃, f₃⟩ => ⟨p₃, t₂.frame f₃ fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj s₀ (by omega) (by lit_omega) (by lit_omega)
  · exact (hp.stk_sub (by lit_omega)).symm

theorem prologueX_mx (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass) :
    (prologueX { v.callee with pass := pass }).allInstrs (fun i => !loadsMxcsr i) = true := by
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  rcases hpass with rfl | rfl <;> rcases Bool.eq_false_or_eq_true v.callee.vl with hl | hl <;>
    (simp only [prologueX, Code.allInstrs, v.mxcsr, hf, hw, hl]; rfl)

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
