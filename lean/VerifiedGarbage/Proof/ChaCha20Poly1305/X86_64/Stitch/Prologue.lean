module

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Crypt
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Two
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Tail
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Bulk

/-!
# ChaCha20 and Poly1305 together (x86-64): the prologue with the last bytes' block

`Stitch.prologueX`: past `fold` (448) bytes, `twoKs` computes the one-time
key's block and the block of the last bytes in the two lanes of `Avx2Tail`'s
code for one set (`Avx2Tail.twoC_ok`), from the state at `ctx + 608` (counter
0) with the lane increments `0` and `1 + 8 ⌊len / 512⌋`, into
`ctx[672, 800)`, or, with 65 to 192 bytes after the whole chunks (`FLen`),
`fourKs` the key's block and their three; up to `fold` bytes the prologue
calls `vg_chacha20_xor` as `prologue` does. Either way it ends as `prologue`
does (`PostP`), and if 1 to 192 bytes are left after at least one whole chunk,
their keystream is at `ctx + 736` (`TailKs`).

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

/-- The lengths whose last bytes' blocks the prologue computes: 1 to 192
bytes past a multiple of 512, from 513 on. -/
abbrev XLen (L : Nat) : Prop := 513 ≤ L ∧ (L - 1) % 512 < 192

/-- Of those, the lengths with 1 to 64 such bytes, whose one block `twoKs`
computes (`fourKs` three otherwise). -/
abbrev XLen1 (L : Nat) : Prop := (L - 1) % 512 < 64

theorem sub1and511 (x : BitVec 64) (h : 1 ≤ x.toNat) :
    ((x - BitVec.ofNat 64 1) &&& BitVec.ofNat 64 511).toNat = (x.toNat - 1) % 512 := by
  have hx := x.isLt
  have hs : (x - BitVec.ofNat 64 1).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 1).toNat = 1 from rfl,
      show 2 ^ 64 - 1 + x.toNat = (x.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_and, hs, show (BitVec.ofNat 64 511).toNat = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- Past `fold` bytes, those with 65 to 192 bytes after the whole chunks,
whose three blocks `fourKs` computes (`twoKs` one otherwise). -/
abbrev FLen (L : Nat) : Prop := 64 ≤ (L - 1) % 512 ∧ (L - 1) % 512 < 192

theorem xlen_of_flen {L : Nat} (hl : 449 ≤ L) (h : FLen L) : XLen L := ⟨by omega, h.2⟩

/-- `xTest`, from `s`: `CF` set if the length (`r13`) is at most 448, `rax`
then `(len - 1) mod 512`, and only `rax` and the flags written. -/
theorem xTest_ok (s : State) :
    WP isa (.block xTest) s fun t =>
      isa.eval .b t = some (decide ((s.gpr .r13).toNat < 449)) ∧
      (1 ≤ (s.gpr .r13).toNat → (t.gpr .rax).toNat = ((s.gpr .r13).toNat - 1) % 512) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x1 : BitVec.signExtend 64 (1#32) = 1#64 := by decide
  have x511 : BitVec.signExtend 64 (511#32) = 511#64 := by decide
  have x449 : BitVec.signExtend 64 (449#32) = 449#64 := by decide
  have e449 : (449#64).toNat = 449 := rfl
  rw [show xTest = [.mov .rax (.reg .r13), .alu .sub .rax (.imm (BitVec.ofNat 32 1)),
    .alu .and .rax (.imm (BitVec.ofNat 32 511)), .alu .cmp .r13 (.imm (BitVec.ofNat 32 449))] from rfl]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, x1, x511, x449,
    Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval, e449,
    Option.some.injEq, exists_eq_left', ↓reduceIte, reduceCtorEq]
  exact ⟨trivial, fun h => sub1and511 (s.gpr .r13) h, fun r h1 => by simp only [h1, ite_false], rfl, rfl, rfl, rfl⟩

theorem sub64_lt128 (x : BitVec 64) :
    (x - BitVec.ofNat 64 64).toNat < 128 ↔ 64 ≤ x.toNat ∧ x.toNat < 192 := by
  have hx := x.isLt
  rw [BitVec.toNat_sub, show (BitVec.ofNat 64 64).toNat = 64 from rfl]
  omega

/-- `prologueX`'s second test (`fTest`): `CF` set if `rax` is from 64 to 191. -/
theorem fTest_ok (s : State) :
    WP isa (.block fTest) s fun t =>
      isa.eval .b t = some (decide (64 ≤ (s.gpr .rax).toNat ∧ (s.gpr .rax).toNat < 192)) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
  have x128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  have e128 : (BitVec.ofNat 64 128).toNat = 128 := rfl
  simp only [fTest, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval,
    Option.some.injEq, exists_eq_left', ↓reduceIte]
  exact ⟨by simp only [x64, x128, e128, sub64_lt128], fun r h1 => by simp only [h1, ite_false], rfl, rfl, rfl, rfl⟩

/-- `xTestV`, from `s`: `CF` set for the lengths (`r13`) `XLen` holds of,
`rax` then `(len - 1) mod 512`, and only `rax`, `r10` and the flags written. -/
theorem xTestV_ok (s : State) :
    WP isa (.block xTestV) s fun t =>
      isa.eval .b t = some (decide (XLen (s.gpr .r13).toNat)) ∧
      (513 ≤ (s.gpr .r13).toNat → (t.gpr .rax).toNat = ((s.gpr .r13).toNat - 1) % 512) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x1 : BitVec.signExtend 64 (1#32) = 1#64 := by decide
  have x511 : BitVec.signExtend 64 (511#32) = 511#64 := by decide
  have x513 : BitVec.signExtend 64 (513#32) = 513#64 := by decide
  have x192 : BitVec.signExtend 64 (192#32) = 192#64 := by decide
  have e192 : (192#64).toNat = 192 := rfl
  have e513 : (513#64).toNat = 513 := rfl
  rw [show xTestV = [.mov .rax (.reg .r13), .alu .sub .rax (.imm (BitVec.ofNat 32 1)),
    .alu .and .rax (.imm (BitVec.ofNat 32 511)), .mov32 .r10 (.imm (BitVec.ofNat 32 192)),
    .alu .cmp .r13 (.imm (BitVec.ofNat 32 513)), .cmov .b .rax (.reg .r10), .alu .cmp .rax (.imm (BitVec.ofNat 32 192))]
    from rfl]
  by_cases h : (s.gpr .r13).toNat < 513
  · have hc : ¬ XLen (s.gpr .r13).toNat := fun ⟨h1, _⟩ => by omega
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, readSrc, x1, x511, x513, x192,
      Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval, h, hc,
      readSrc32, State.setReg32, decide_true, decide_false, Option.some.injEq, exists_eq_left', ↓reduceIte,
      reduceCtorEq, e192, e513]
    exact ⟨by decide, fun h' => absurd h' (by omega), fun r h1 h2 => by simp only [h1, h2, ite_false], rfl, rfl, rfl,
      rfl⟩
  · have hm := sub1and511 (s.gpr .r13) (by omega)
    have hc : XLen (s.gpr .r13).toNat ↔ ((s.gpr .r13).toNat - 1) % 512 < 192 :=
      ⟨fun h => h.2, fun h' => ⟨by omega, h'⟩⟩
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, readSrc, x1, x511, x513, x192,
      Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval, h, hc,
      readSrc32, State.setReg32, decide_false, Bool.false_eq_true, Option.some.injEq, exists_eq_left',
      ↓reduceIte, reduceCtorEq, e192, e513, hm]
    exact ⟨trivial, fun _ => trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], rfl, rfl, rfl, rfl⟩

/-- `prologueX`'s second test: `CF` set if `rax` is below 64. -/
theorem cmpRax64_ok (s : State) :
    WP isa (.block [.alu .cmp .rax (.imm 64)]) s fun t =>
      isa.eval .b t = some (decide ((s.gpr .rax).toNat < 64)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
  have e64 : (BitVec.ofNat 64 64).toNat = 64 := rfl
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, x64,
    Option.bind_some, cf_arithFlags, eval, e64, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, rfl⟩

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
theorem twoKsBN_ok (vl : Bool) {c : Addr} {s : State} (hr15 : s.gpr .r15 = c)
    (hrdi : s.gpr .rdi = stA (c + BitVec.ofNat 64 544))
    (hwr : s.wr = [stR (stA (c + BitVec.ofNat 64 544)), bufR (bfA (c + BitVec.ofNat 64 544))]) :
    WP isa (twoKsB vl) s fun t =>
      (∀ k < 128, t.mem (bfA (c + BitVec.ofNat 64 544) + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt s.mem (stA (c + BitVec.ofNat 64 544)))
          (cOf (xCtr (s.gpr .r13)).toNat (k / 64))))).getD (k % 64) 0) ∧
      t.gpr .rsi = off c 128 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb : off c 672 = bfA (c + BitVec.ofNat 64 544) := by
    rw [off_eq]; simp only [bfA, Offset.add_add]
  unfold twoKsB
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

/-! ## The four blocks, on narrowed permissions -/

/-- The quadwords `fourConsts`'s two `storeQ`s store. -/
def tz4Pairs : List (Nat × BitVec 64) := tzPairs ++ [(256, 0), (264, 0), (272, 0), (280, 0)]

theorem tz4Pairs_le : ∀ p ∈ tz4Pairs, p.1 + 8 ≤ 320 := by decide

/-- The block counter of the last bytes, `1 + 8 ⌊len / 512⌋`, before its
truncation to a doubleword. -/
abbrev xCtrQ (x : BitVec 64) : BitVec 64 := ((x >>> 9) <<< 3) + 1

theorem xCtrQ_eq (x : BitVec 64) {k : Nat} (hk : k < 3) :
    (xCtrQ x + BitVec.ofNat 64 k).setWidth 32 = BitVec.ofNat 32 (1 + 8 * (x.toNat / 512) + k) := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [xCtrQ, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (2 : Nat) ^ 9 = 512 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (show x.toNat / 512 * 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x.toNat / 512 * 8 + 1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x.toNat / 512 * 8 + 1 + k < 2 ^ 64 by omega)]
  omega

/-- The counters of the blocks of the last bytes, stored as doublewords. -/
theorem cStore4_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block [.mov .rax (.reg .r13), .shift .shr .rax 9, .shift .shl .rax 3, .alu .add .rax (.imm 1),
      .store32 (at_ .rcx 240) .rax, .alu .add .rax (.imm 1), .store32 (at_ .rcx 256) .rax,
      .alu .add .rax (.imm 1), .store32 (at_ .rcx 272) .rax]) s fun t =>
      t.mem = ((s.mem.writeW (buf + BitVec.ofNat 64 240) (BitVec.setWidth 32 (xCtrQ (s.gpr .r13)))).writeW
        (buf + BitVec.ofNat 64 256) (BitVec.setWidth 32 (xCtrQ (s.gpr .r13) + 1))).writeW
        (buf + BitVec.ofNat 64 272) (BitVec.setWidth 32 (xCtrQ (s.gpr .r13) + 1 + 1)) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have o0 : InRegions s.wr (buf + BitVec.ofNat 64 240) 4 := ⟨_, hb, Offset.contains_base _ (by decide) (by decide)⟩
  have o1 : InRegions s.wr (buf + BitVec.ofNat 64 256) 4 := ⟨_, hb, Offset.contains_base _ (by decide) (by decide)⟩
  have o2 : InRegions s.wr (buf + BitVec.ofNat 64 272) 4 := ⟨_, hb, Offset.contains_base _ (by decide) (by decide)⟩
  have se : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, execAlu, readSrc, arithFlags,
    VG.Proof.ChaCha20.X86_64.Avx2.ea_at, State.store32, State.setReg, State.setFlags, hrcx, se, o0, o1, o2,
    reduceCtorEq, ite_true, ite_false, Nat.reduceLeDiff, and_self, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h => by simp [h], trivial⟩

theorem fourConsts_eq : ptr .rcx .r15 672 ++ fourConsts ++ ([.mov .r9 (.reg .rcx)] : List Instr) =
    ptr .rcx .r15 672 ++ (pairsCode tz4Pairs ++ (([.mov .rax (.reg .r13), .shift .shr .rax 9, .shift .shl .rax 3,
      .alu .add .rax (.imm 1), .store32 (at_ .rcx 240) .rax, .alu .add .rax (.imm 1), .store32 (at_ .rcx 256) .rax,
      .alu .add .rax (.imm 1), .store32 (at_ .rcx 272) .rax] : List Instr) ++
      (pairsCode constPairs ++ ([.mov .r9 (.reg .rcx)] : List Instr)))) := by
  simp only [fourConsts, tz_eq, VG.Proof.ChaCha20.X86_64.Avx2.consts_eq, List.append_assoc]; rfl

/-- The memory after `fourKs`'s constants, at `buf`. -/
abbrev fourMem (buf : Addr) (x : BitVec 64) (m : Mem) : Mem :=
  storeAll buf constPairs ((((storeAll buf tz4Pairs m).writeW (buf + BitVec.ofNat 64 240) (BitVec.setWidth 32 (xCtrQ x))).writeW
    (buf + BitVec.ofNat 64 256) (BitVec.setWidth 32 (xCtrQ x + 1))).writeW (buf + BitVec.ofNat 64 272) (BitVec.setWidth 32 (xCtrQ x + 1 + 1)))

theorem fourPre_ok {buf : Addr} {s : State} (hbuf : off (s.gpr .r15) 672 = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block (ptr .rcx .r15 672 ++ fourConsts ++ ([.mov .r9 (.reg .rcx)] : List Instr))) s fun t =>
      t.mem = fourMem buf (s.gpr .r13) s.mem ∧ t.gpr .r9 = buf ∧ t.gpr .rcx = buf ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [fourConsts_eq]
  refine WP.block_append (WP.mono (ptr_ok .rcx .r15 (k := 672) (by lit_omega) s)
    fun s₁ ⟨rcx₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  rw [hbuf] at rcx₁
  refine WP.block_append (WP.mono (pairs_ok tz4Pairs tz4Pairs_le rcx₁ (by rw [wr₁]; exact hb))
    fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (cStore4_ok (buf := buf) (s := s₂) (by rw [g₂ _ (by decide), rcx₁])
    (by rw [wr₂, wr₁]; exact hb)) fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_)
  refine WP.block_append (WP.mono (pairs_ok (buf := buf) constPairs constPairs_le (s := s₃)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), rcx₁]) (by rw [wr₃, wr₂, wr₁]; exact hb))
    fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.mono (movR9_ok s₄) fun s₅ ⟨r9₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  have hc : s₄.gpr .rcx = buf := by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), rcx₁]
  have h13 : s₂.gpr .r13 = s.gpr .r13 := by rw [g₂ _ (by decide), g₁ _ (by decide)]
  refine ⟨by rw [m₅, m₄, m₃, m₂, h13, m₁], by rw [r9₅, hc], by rw [g₅ _ (by decide), hc],
    fun r h₁ h₂ h₃ => by rw [g₅ r h₃, g₄ r h₁, g₃ r h₁, g₂ r h₁, g₁ r h₂],
    by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩

theorem fourMem_consts (buf : Addr) (x : BitVec 64) (m : Mem) : Consts (fourMem buf x m) buf := consts_mem _ _

/-- Read back a stored quadword of `tz4Pairs`. -/
local macro "zread4" : tactic => `(tactic|
  simp (disch := decide) only [storeAll, tz4Pairs, tzPairs, List.cons_append, List.nil_append, List.foldl_cons,
    List.foldl_nil, Nat.reduceAdd, VG.Proof.ChaCha20.X86_64.Avx2.readW64_off, Mem.readW_writeW_self64])

/-- The doublewords of the lane increments `fourConsts` zeroes. -/
theorem tz4_zero (m : Mem) (buf : Addr) {d : Nat} (h₁ : 224 ≤ d) (h₂ : d < 288) (h₄ : d % 4 = 0) :
    (storeAll buf tz4Pairs m).readW (buf + BitVec.ofNat 64 d) 32 = 0 := by
  have E := VG.X86_64.readW_extract (storeAll buf tz4Pairs m) (buf + BitVec.ofNat 64 (8 * (d / 8)))
    (w := 64) (k := d % 8) (n := 4) (by omega)
  rw [VG.Proof.ChaCha20.X86_64.Avx2.add_ofNat, show 8 * (d / 8) + d % 8 = d by omega] at E
  rw [← E]
  rcases (by omega : d = 224 ∨ d = 228 ∨ d = 232 ∨ d = 236 ∨ d = 240 ∨ d = 244 ∨ d = 248 ∨ d = 252 ∨
    d = 256 ∨ d = 260 ∨ d = 264 ∨ d = 268 ∨ d = 272 ∨ d = 276 ∨ d = 280 ∨ d = 284) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul]; zread4; decide)

theorem incsC4_pre (m : Mem) (buf : Addr) (x : BitVec 64) :
    VG.Proof.ChaCha20.X86_64.Avx2Tail.IncsC4 ((((storeAll buf tz4Pairs m).writeW (buf + BitVec.ofNat 64 240)
      (BitVec.setWidth 32 (xCtrQ x))).writeW (buf + BitVec.ofNat 64 256) (BitVec.setWidth 32 (xCtrQ x + 1))).writeW
      (buf + BitVec.ofNat 64 272) (BitVec.setWidth 32 (xCtrQ x + 1 + 1))) buf (1 + 8 * (x.toNat / 512)) := by
  have e0 : (xCtrQ x).setWidth 32 = BitVec.ofNat 32 (1 + 8 * (x.toNat / 512) + 0) := by
    have := xCtrQ_eq x (k := 0) (by decide)
    rwa [show xCtrQ x + BitVec.ofNat 64 0 = xCtrQ x from BitVec.add_zero _] at this
  have e1 : (xCtrQ x + 1).setWidth 32 = BitVec.ofNat 32 (1 + 8 * (x.toNat / 512) + 1) := xCtrQ_eq x (k := 1) (by decide)
  have e2 : (xCtrQ x + 1 + 1).setWidth 32 = BitVec.ofNat 32 (1 + 8 * (x.toNat / 512) + 2) := by
    have := xCtrQ_eq x (k := 2) (by decide)
    rwa [show BitVec.ofNat 64 2 = (1 : BitVec 64) + 1 from rfl, ← BitVec.add_assoc] at this
  -- The three counters, and the zeroed doublewords around them.
  have sep : ∀ {d e : Nat}, d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 320 → e + 4 ≤ 320 →
      Mem.Sep (buf + BitVec.ofNat 64 d) 4 (buf + BitVec.ofNat 64 e) 4 :=
    fun h a b => Offset.sep buf h (by lit_omega) (by lit_omega)
  intro k hk p hp
  rw [show 4 * (56 + 8 * k + p) = 224 + 4 * (8 * k + p) by omega]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, ite_true, ite_false,
    VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4, reduceCtorEq, Nat.add_zero]
  -- 240: the first counter, under two later writes.
  case inl.inr.inr.inr.inr.inl =>
    rw [Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32, e0]
    rfl
  -- 256 and 272: the second and third.
  case inr.inl =>
    rw [Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32, e1]
    rfl
  case inr.inr.inr.inr.inr.inl =>
    rw [Mem.readW_writeW_self32, e2]
    rfl
  all_goals
    rw [Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
      tz4_zero m buf (by decide) (by decide) (by decide)]
    try rfl

theorem fourMem_incs (buf : Addr) (x : BitVec 64) (m : Mem) :
    VG.Proof.ChaCha20.X86_64.Avx2Tail.IncsC4 (fourMem buf x m) buf (1 + 8 * (x.toNat / 512)) :=
  VG.Proof.ChaCha20.X86_64.Avx2Tail.incsC4_frame (incsC4_pre m buf x)
    (storeAll_frameLo (d := 224) (by decide) constPairs constPairs_lo _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base buf (Nat.le_refl _) (by decide))

/-- `fourKs`, with its permissions: as `twoKsN_ok`, with the first 256 bytes
of `bfA c'` the keystream of the blocks at counters `0` and `1 + 8 ⌊len / 512⌋`
to `3 + 8 ⌊len / 512⌋`. -/
theorem fourKsN_ok (vl : Bool) {c : Addr} {s : State} (hr15 : s.gpr .r15 = c)
    (hrdi : s.gpr .rdi = stA (c + BitVec.ofNat 64 544))
    (hwr : s.wr = [stR (stA (c + BitVec.ofNat 64 544)), bufR (bfA (c + BitVec.ofNat 64 544))]) :
    WP isa (fourKs vl) s fun t =>
      (∀ k < 256, t.mem (bfA (c + BitVec.ofNat 64 544) + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt s.mem (stA (c + BitVec.ofNat 64 544)))
          (VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4 (1 + 8 * ((s.gpr .r13).toNat / 512)) (k / 64))))).getD (k % 64) 0) ∧
      t.gpr .rsi = off c 128 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb : off c 672 = bfA (c + BitVec.ofNat 64 544) := by
    rw [off_eq]; simp only [bfA, Offset.add_add]
  unfold fourKs
  refine WP.seq (WP.mono (fourPre_ok (buf := bfA (c + BitVec.ofNat 64 544)) (by rw [hr15, hb]) (by rw [hwr]; simp))
    fun s₁ ⟨m₁, r9₁, rcx₁, g₁, rd₁, wr₁⟩ => ?_)
  have hc : VG.Proof.ChaCha20.X86_64.Avx512Tail.Ctx 0 s₁ := ctx0 (c := c + BitVec.ofNat 64 544)
    (by rw [g₁ _ (by decide) (by decide) (by decide), hrdi]) r9₁ (by rw [wr₁, hwr]; simp) (by rw [wr₁, hwr]; simp)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Avx2Tail.fourC_ok (c := 1 + 8 * ((s.gpr .r13).toNat / 512)) vl hc
    (by rw [m₁, r9₁]; exact fourMem_consts _ _ _)
    (by rw [m₁, r9₁]; exact fourMem_incs _ _ _)) fun s₂ ⟨ks₂, _, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (endB_ok s₂) fun s₃ ⟨rsi₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have F₁ : Frame [bufR (bfA (c + BitVec.ofNat 64 544))] s.mem s₁.mem := by
    rw [m₁]
    exact (((((storeAll_frame (List.mem_singleton_self _) tz4Pairs tz4Pairs_le _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide)))).trans
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

/-- If 1 to 192 bytes are left after the whole chunks, their keystream at
`ctx + 736`, as `prologueX` leaves it. -/
def TailKs (s₀ : State) (m : Mem) : Prop :=
  512 ≤ L s₀ → 1 ≤ L s₀ % 512 → L s₀ % 512 ≤ 192 → ∀ k < L s₀ % 512,
    m (off (cx s₀) (736 + k)) = (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD (512 * (L s₀ / 512) + k) 0

theorem TailKs.of_xlen {s₀ : State} {m : Mem} (h : ¬ XLen (L s₀)) : TailKs s₀ m :=
  fun h₁ h₂ h₃ => absurd ⟨by omega, by omega⟩ h

theorem TailKs.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : TailKs s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ 736 192).Disjoint r) : TailKs s₀ m' := fun h₁ h₂ h₃ k hk => by
  rw [← h h₁ h₂ h₃ k hk]
  exact hf _ fun r hr hc => hd r hr _ (contains_sub s₀ (k := 736) (n := 192) (by omega) (by omega) (by lit_omega)) hc

theorem ctr_toNat (S : CState) {v : BitVec 32} {n : Nat} (h : v = BitVec.ofNat 32 n) : ctr S v.toNat = ctr S n := by
  simp only [ctr, BitVec.ofNat_toNat, BitVec.setWidth_eq, h]

/-- The pass for which `twoKs` computes all the call would: none (`open`'s;
with a pass of 512 the prologue's keystream covers the first 448 bytes from
513 to 576, `PreLen`). -/
abbrev XPass (pass : Nat) : Prop := pass = 0

theorem XPass.ok {pass : Nat} (h : XPass pass) : PassOk 448 pass := .inl h

/-- Past `fold` bytes, the call would have computed only the one-time key's
block. -/
theorem mOf_gt {pass L : Nat} (h : XPass pass) (hl : 449 ≤ L) : mOf 448 pass L = 0 := by
  subst h; simp only [mOf, splitOf]; rw [ite_eq_right (by omega)]; simp

/-- With `twoKs` or `fourKs`, the call would have computed only the one-time
key's block. -/
theorem mOf_xlen {pass L : Nat} (h : XPass pass) (hx : XLen L) : mOf 448 pass L = 0 :=
  mOf_gt h (by omega)

/-- `twoKs`, from where the prologue would call `vg_chacha20_xor`, past
`fold` bytes but for 65 to 192 after the whole chunks: as after that call
(`AfterF`), and the keystream of 1 to 64 bytes left at `ctx + 736`. -/
theorem twoKsB_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀)
    {s : State} (h : FArgs v.callee.fold pass s₀ s) (hl : 449 ≤ L s₀) (hF : ¬ FLen (L s₀)) :
    WP isa (twoKsB v.callee.vl) s fun s' => AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem := by
  have hf := (avx2_of v hv).1
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm0 : mOf v.callee.fold pass (L s₀) = 0 := by rw [hf]; exact mOf_gt hpass hl
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
  have hn : (twoKsB v.callee.vl).noCalls = true := by cases v.callee.vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := w)
    (twoKsBN_ok v.callee.vl (s := s.withRegions [] w) (c := cx s₀) h.r15 (by rw [State.withRegions_gpr, h.rdi, eS]) rfl)
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
    by rw [stateAt_frame f'' (dw (k := 64) (n := 64) (by omega) (by lit_omega)), h.st], fun k hk => ?_,
    fun hps => absurd (hpass.symm.trans hps) (by decide)⟩,
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
  · have h1 : XLen1 (L s₀) := by
      rcases Nat.lt_or_ge ((L s₀ - 1) % 512) 64 with h' | h'
      · exact h'
      · exact absurd ⟨h', by omega_using [h₂, h₃, hl]⟩ hF
    have := ks' (64 + k) (by omega_using [hk, h1, h₂])
    rw [S₀, show (64 + k) / 64 = 1 by omega_using [hk, h1, h₂], show (64 + k) % 64 = k by omega_using [hk, h1, h₂],
      r13] at this
    rw [show 736 + k = 672 + (64 + k) by omega, ← eA, this,
      VG.Proof.ChaCha20.keystream_getD _ (by omega : 512 * (L s₀ / 512) + k < L s₀),
      show (512 * (L s₀ / 512) + k) / 64 = 8 * (L s₀ / 512) by omega,
      show (512 * (L s₀ / 512) + k) % 64 = k by omega, ← initState_ctr]
    simp only [cOf, show (1 : Nat) ≠ 0 by decide, ite_false]
    rw [ctr_toNat _ (xCtr_eq _)]


/-- Writes of `rax` alone keep what follows the call. -/
theorem AfterF.pad {fold pass : Nat} {s₀ s t : State} (h : AfterF fold pass s₀ s)
    (g : ∀ q, q ≠ .rax → t.gpr q = s.gpr q) (m : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    AfterF fold pass s₀ t :=
  ⟨by rw [g _ (by decide)]; exact h.rsi, by rw [g _ (by decide)]; exact h.r14,
    by rw [g _ (by decide)]; exact h.r13, by rw [g _ (by decide)]; exact h.r12,
    by rw [g _ (by decide)]; exact h.rbx, by rw [g _ (by decide)]; exact h.rbp,
    by rw [g _ (by decide)]; exact h.rsp, by rw [rd]; exact h.rd, by rw [wr]; exact h.wr,
    by rw [m]; exact h.saved, by rw [m]; exact h.fine, by rw [m]; exact h.st,
    fun k hk => by rw [m]; exact h.ks k hk, fun hps => by rw [m]; exact h.mslot hps⟩

/-- `twoKs`: `twoKsB` and its padding. -/
theorem twoKs_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀)
    {s : State} (h : FArgs v.callee.fold pass s₀ s) (hl : 449 ≤ L s₀) (hF : ¬ FLen (L s₀)) :
    WP isa (twoKs v.callee.vl) s fun s' => AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem :=
  WP.seq (WP.mono (twoKsB_ok v hv hpass hp h hl hF) fun t ⟨a, k⟩ =>
    WP.mono (padIns_ok .rax (by decide) t) fun u p => ⟨AfterF.pad a p.gpr p.mem p.rd p.wr, by rw [p.mem]; exact k⟩)

/-- `fourKs`, from where the prologue would call `vg_chacha20_xor`: as
`twoKs_ok`, for 1 to 192 bytes past the whole chunks (`prologueX` takes
it for 65 to 192). -/
theorem fourKs_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀)
    {s : State} (h : FArgs v.callee.fold pass s₀ s) (hx : XLen (L s₀)) :
    WP isa (fourKs v.callee.vl) s fun s' => AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem := by
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
  have hn : (fourKs v.callee.vl).noCalls = true := by cases v.callee.vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := w)
    (fourKsN_ok v.callee.vl (s := s.withRegions [] w) (c := cx s₀) h.r15 (by rw [State.withRegions_gpr, h.rdi, eS]) rfl)
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ rd' wr' f' hP => ?_
  obtain ⟨ks₀, rsi₀, g₀, -, -⟩ := hP
  have ks' : ∀ k < 256, s'.mem (bfA (cx s₀ + BitVec.ofNat 64 544) + BitVec.ofNat 64 k) =
      (serialize (Spec.ChaCha20.block (ctr (stateAt (s.withRegions [] w).mem (stA (cx s₀ + BitVec.ofNat 64 544)))
        (VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4 (1 + 8 * (((s.withRegions [] w).gpr .r13).toNat / 512))
          (k / 64))))).getD (k % 64) 0 := ks₀
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
    by rw [stateAt_frame f'' (dw (k := 64) (n := 64) (by omega) (by lit_omega)), h.st], fun k hk => ?_,
    fun hps => absurd (hpass.symm.trans hps) (by decide)⟩,
    fun h₁ h₂ h₃ k hk => ?_⟩
  · simp only [w, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, by rw [eS]; exact sub_sub s₀ (by omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, by rw [eB]; exact sub_sub s₀ (by omega) (by lit_omega) (by lit_omega)⟩
  · rw [hm0] at hk ⊢
    have := ks' k (by omega)
    rw [S₀, show k / 64 = 0 by omega, show k % 64 = k by omega] at this
    rw [← eA, this, VG.Proof.ChaCha20.keystream_getD _ hk, show k / 64 = 0 by omega, show k % 64 = k by omega]
    simp only [VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4, ite_true, VG.Proof.ChaCha20.ctr_zero]
  · have := ks' (64 + k) (by omega_using [hk, h₃])
    have hq : (1 + 8 * ((s₀.gpr .r9).toNat / 512)) + (1 + k / 64) - 1 = 1 + (8 * (L s₀ / 512) + k / 64) := by
      show _ = 1 + (8 * ((s₀.gpr .r9).toNat / 512) + k / 64); omega
    rw [S₀, show (64 + k) / 64 = 1 + k / 64 by omega_using [hk, h₃],
      show (64 + k) % 64 = k % 64 by omega_using [hk, h₃], r13, VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4,
      ite_eq_right (by omega : ¬ 1 + k / 64 = 0), hq] at this
    rw [show 736 + k = 672 + (64 + k) by omega, ← eA, this,
      VG.Proof.ChaCha20.keystream_getD _ (by omega : 512 * (L s₀ / 512) + k < L s₀),
      show (512 * (L s₀ / 512) + k) / 64 = 8 * (L s₀ / 512) + k / 64 by omega,
      show (512 * (L s₀ / 512) + k) % 64 = k % 64 by omega, ← initState_ctr]

/-- `prologueX`'s choice and the keystream: `twoKs`, `fourKs` or the call of
`vg_chacha20_xor`. -/
theorem prologueXMA_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀) {s : State} (h : FArgs v.callee.fold pass s₀ s) :
    WP isa (xselA v.callee) s fun s' => AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem := by
  unfold xselA
  refine WP.seq (WP.mono (xTest_ok s) fun s₁ ⟨cf₁, rax₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have h₁ : FArgs v.callee.fold pass s₀ s₁ :=
    ⟨by rw [g₁ _ (by decide), h.rdi], by rw [g₁ _ (by decide), h.rsi],
      by rw [g₁ _ (by decide), h.rdx], by rw [g₁ _ (by decide), h.rcx],
      by rw [g₁ _ (by decide), h.r15], by rw [g₁ _ (by decide), h.r14],
      by rw [g₁ _ (by decide), h.r13], by rw [g₁ _ (by decide), h.r12],
      by rw [g₁ _ (by decide), h.rbx], by rw [g₁ _ (by decide), h.rbp],
      by rw [g₁ _ (by decide), h.rsp], by rw [rd₁, h.rd], by rw [wr₁, h.wr],
      by rw [m₁]; exact h.saved, by rw [m₁]; exact h.fine, by rw [m₁]; exact h.st, by rw [m₁]; exact h.st',
      fun k hk => by rw [m₁]; exact h.zero k hk, fun hps => by rw [m₁]; exact h.mslot hps⟩
  have e13 : (s.gpr .r13).toNat = L s₀ := by rw [h.r13]
  rw [e13] at cf₁ rax₁
  refine WP.ite (decide (L s₀ < 449)) cf₁ (fun hx => ?_) (fun hx => ?_)
  · have hx' := of_decide_eq_true hx
    exact WP.mono (foldCall_ok v hp h₁) fun s' a => ⟨a, TailKs.of_xlen fun h' => by omega_using [hx', h'.1]⟩
  · have hl : 449 ≤ L s₀ := by have := of_decide_eq_false hx; omega_using [this]
    refine WP.seq (WP.mono (fTest_ok s₁) fun s₂ ⟨cf₂, g₂, m₂, rd₂, wr₂, _⟩ => ?_)
    have h₂ : FArgs v.callee.fold pass s₀ s₂ :=
      ⟨by rw [g₂ _ (by decide)]; exact h₁.rdi, by rw [g₂ _ (by decide)]; exact h₁.rsi,
        by rw [g₂ _ (by decide)]; exact h₁.rdx, by rw [g₂ _ (by decide)]; exact h₁.rcx,
        by rw [g₂ _ (by decide)]; exact h₁.r15, by rw [g₂ _ (by decide)]; exact h₁.r14,
        by rw [g₂ _ (by decide)]; exact h₁.r13, by rw [g₂ _ (by decide)]; exact h₁.r12,
        by rw [g₂ _ (by decide)]; exact h₁.rbx, by rw [g₂ _ (by decide)]; exact h₁.rbp,
        by rw [g₂ _ (by decide)]; exact h₁.rsp, by rw [rd₂]; exact h₁.rd,
        by rw [wr₂]; exact h₁.wr, by rw [m₂]; exact h₁.saved, by rw [m₂]; exact h₁.fine, by rw [m₂]; exact h₁.st,
        by rw [m₂]; exact h₁.st', fun k hk => by rw [m₂]; exact h₁.zero k hk,
        fun hps => by rw [m₂]; exact h₁.mslot hps⟩
    rw [rax₁ (by omega_using [hl])] at cf₂
    refine WP.ite (decide (FLen (L s₀))) cf₂ (fun hF => ?_) (fun hF => ?_)
    · exact fourKs_ok v hv hpass hp h₂ (xlen_of_flen hl (of_decide_eq_true hF))
    · exact twoKs_ok v hv hpass hp h₂ hl (of_decide_eq_false hF)

/-- `prologueX`'s choice and the keystream: `twoKs`, `fourKs` or the call of
`vg_chacha20_xor`. -/
theorem prologueXMV_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀) {s : State} (h : FArgs v.callee.fold pass s₀ s) :
    WP isa (xselV v.callee) s fun s' => AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem := by
  unfold xselV
  refine WP.seq (WP.mono (xTestV_ok s) fun s₁ ⟨cf₁, rax₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have h₁ : FArgs v.callee.fold pass s₀ s₁ :=
    ⟨by rw [g₁ _ (by decide) (by decide), h.rdi], by rw [g₁ _ (by decide) (by decide), h.rsi],
      by rw [g₁ _ (by decide) (by decide), h.rdx], by rw [g₁ _ (by decide) (by decide), h.rcx],
      by rw [g₁ _ (by decide) (by decide), h.r15], by rw [g₁ _ (by decide) (by decide), h.r14],
      by rw [g₁ _ (by decide) (by decide), h.r13], by rw [g₁ _ (by decide) (by decide), h.r12],
      by rw [g₁ _ (by decide) (by decide), h.rbx], by rw [g₁ _ (by decide) (by decide), h.rbp],
      by rw [g₁ _ (by decide) (by decide), h.rsp], by rw [rd₁, h.rd], by rw [wr₁, h.wr],
      by rw [m₁]; exact h.saved, by rw [m₁]; exact h.fine, by rw [m₁]; exact h.st, by rw [m₁]; exact h.st',
      fun k hk => by rw [m₁]; exact h.zero k hk, fun hps => by rw [m₁]; exact h.mslot hps⟩
  have e13 : (s.gpr .r13).toNat = L s₀ := by rw [h.r13]
  rw [e13] at cf₁ rax₁
  refine WP.ite (decide (XLen (L s₀))) cf₁ (fun hx => ?_) (fun hx => ?_)
  · have hx' := of_decide_eq_true hx
    refine WP.seq (WP.mono (cmpRax64_ok s₁) fun s₂ ⟨cf₂, g₂, m₂, rd₂, wr₂, _⟩ => ?_)
    have h₂ : FArgs v.callee.fold pass s₀ s₂ :=
      ⟨by rw [g₂]; exact h₁.rdi, by rw [g₂]; exact h₁.rsi, by rw [g₂]; exact h₁.rdx, by rw [g₂]; exact h₁.rcx,
        by rw [g₂]; exact h₁.r15, by rw [g₂]; exact h₁.r14, by rw [g₂]; exact h₁.r13, by rw [g₂]; exact h₁.r12,
        by rw [g₂]; exact h₁.rbx, by rw [g₂]; exact h₁.rbp, by rw [g₂]; exact h₁.rsp, by rw [rd₂]; exact h₁.rd,
        by rw [wr₂]; exact h₁.wr, by rw [m₂]; exact h₁.saved, by rw [m₂]; exact h₁.fine, by rw [m₂]; exact h₁.st,
        by rw [m₂]; exact h₁.st', fun k hk => by rw [m₂]; exact h₁.zero k hk,
        fun hps => by rw [m₂]; exact h₁.mslot hps⟩
    rw [rax₁ hx'.1] at cf₂
    refine WP.ite (decide (XLen1 (L s₀))) cf₂ (fun h1 => ?_) (fun _ => ?_)
    · have h1' : XLen1 (L s₀) := of_decide_eq_true h1
      exact twoKsB_ok v hv hpass hp h₂ (by omega_using [hx'.1]) fun hf => absurd hf.1 (Nat.not_le.mpr h1')
    · exact fourKs_ok v hv hpass hp h₂ hx'
  · exact WP.mono (foldCall_ok v hp h₁) fun s' a => ⟨a, TailKs.of_xlen (of_decide_eq_false hx)⟩

/-- The prologue with the last bytes' block: as `prologue`, and their keystream
at `ctx + 736`. -/
theorem prologueX_ok (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass)
    {s₀ : State} (hp : APre e s₀) :
    WP isa (prologueX { v.callee with pass := pass }) (entryS s₀) fun s =>
      PostP v.callee.fold pass s₀ s ∧ TailKs s₀ s.mem := by
  have hP : PassOk v.callee.fold pass := by rw [(avx2_of v hv).1]; exact hpass.ok
  refine WP.seq (WP.mono (prologueA_ok v.fold_le hP (wide_of v) hp) fun s₁ h₁ => ?_)
  have hx : WP isa (xsel { v.callee with pass := pass }) s₁ fun s' =>
      AfterF v.callee.fold pass s₀ s' ∧ TailKs s₀ s'.mem := by
    unfold xsel; split
    · exact prologueXMV_ok v hv hpass hp h₁
    · exact prologueXMA_ok v hv hpass hp h₁
  refine WP.seq (WP.mono hx fun s₂ ⟨a₂, t₂⟩ => ?_)
  refine WP.mono (prologueBF_ok v.fold_le hp a₂) fun s₃ ⟨p₃, f₃⟩ => ⟨p₃, t₂.frame f₃ fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj s₀ (by omega) (by lit_omega) (by lit_omega)
  · exact (hp.stk_sub (by lit_omega)).symm

theorem prologueX_mx (v : Proof.ChaCha20.X86_64.XorImpl) (hv : v.poly = .avx2) {pass : Nat} (hpass : XPass pass) :
    (prologueX { v.callee with pass := pass }).allInstrs (fun i => !loadsMxcsr i) = true := by
  obtain ⟨hf, -, hw⟩ := avx2_of v hv
  subst hpass
  rcases Bool.eq_false_or_eq_true v.callee.vl with hl | hl <;>
    (simp only [prologueX, xsel, xselV, xselA, hl, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, v.mxcsr, hf, hw]; rfl)

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
