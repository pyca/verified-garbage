module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Weave
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SHA-512 with AVX2 on x86-64, rolled: the compression function

`correct` proves `Impl.Sha512.X86_64.Avx2Rolled.compress` correct from `Pre`:
the precondition of the unrolled code (`Proof/Sha512/X86_64/Avx2/Compress.lean`),
with the table of round constants readable after the blocks, outside the
writable regions and the return address. The proof follows the unrolled
one: the loops of rounds run sixteen of them per iteration (`Rounds.lean`),
the first block's reading its words from the ring of the scratch space
(`RMem`), the second block's from the words kept for it (`HMem`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2 VG.Impl.Sha512.X86_64.Avx2Rolled
open VG.Proof.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha512.X86_64 (st bp nb scr stR blR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' sub_offset ofInt_natCast stateAt_get
  stateAt_eq readW_writeW_word writeState stateAt_writeState frame_writeState)

/-! ## The precondition -/

/-- The address of the table. -/
abbrev kb (s₀ : State) : Addr := s₀.syms kSym

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The precondition of the unrolled code, of `s₀` without the table. -/
theorem base : Avx2.PreN 1328 (s₀.withRegions [blR s₀] s₀.wr) :=
  ⟨rfl, h.wr, h.st_scr, h.blk_st, h.blk_scr, h.ret_st, h.ret_scr⟩

/-- The precondition of the unrolled code, which is the same. -/
theorem avx2 : Avx2.PreN 1328 s₀ := ⟨h.rd, h.wr, h.st_scr, h.blk_st, h.blk_scr, h.ret_st, h.ret_scr⟩

theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := h.base.nb_lt

theorem in_blk16 {i n : Nat} (hi : i < nb s₀) (hn : n < 8) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 := by
  obtain ⟨r, hr, hc⟩ := h.base.in_blk16 hi hn
  refine ⟨r, ?_, hc⟩
  simp only [State.withRegions_rd, State.withRegions_wr, List.mem_append, List.mem_singleton] at hr
  rcases hr with rfl | hr
  · simp [h.rd]
  · exact List.mem_append_right _ hr

end Pre

/-! ## The scratch space -/

/-- The part of the scratch space holding the words: the ring, and the
second block's schedule. -/
abbrev wR (scr : Addr) : Region := ⟨scr, 896⟩

theorem wR_sub (p : Addr) : Region.Sub (wR p) ⟨p, 1328⟩ := Region.sub_prefix (by omega_arith)

theorem frame_wide {scr : Addr} {m m' : Mem} (h : Frame [wR scr] m m') : Frame [wRegion scr] m m' :=
  h.sub fun r hr => ⟨wRegion scr, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩

theorem frame_scr {s₀ : State} {m m' : Mem} (h : Frame [wR (scr s₀)] m m') : Frame [stR s₀, scrR s₀] m m' :=
  h.sub fun r hr => ⟨scrR s₀, by simp, by rw [List.mem_singleton.mp hr]; exact wR_sub _⟩

/-- Where the ring keeps the words `2k` and `2k+1` of both blocks. -/
abbrev ringAddr (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofNat 64 (32 * (k % 8))

/-- Where the words `2k` and `2k+1` of the second block are kept. -/
abbrev hiAddr (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofNat 64 (256 + 16 * k)

/-- The ring holds the words `2k` and `2k+1`: of `M₁` in lane 0, of `M₀` in lane 1. -/
def RMem (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) : Prop :=
  m.readW (ringAddr scr k) 256 = pair M₀ k ++ pair M₁ k

/-- The words `2k` and `2k+1` of `M₁` are kept. -/
def HMem (m : Mem) (scr : Addr) (M₁ : Block) (k : Nat) : Prop :=
  m.readW (hiAddr scr k) 128 = pair M₁ k

theorem rmem_write {m : Mem} {scr : Addr} {M₀ M₁ : Block} {k e w : Nat} (v : BitVec w)
    (h : 32 * (k % 8) + 32 ≤ e ∨ e + w / 8 ≤ 32 * (k % 8)) (he : e + w / 8 ≤ 2 ^ 64) (hm : RMem m scr M₀ M₁ k) :
    RMem (m.writeW (scr + BitVec.ofNat 64 e) v) scr M₀ M₁ k :=
  (Mem.readW_writeW_sep (Offset.sep scr h (by omega_arith) he) (by decide)).trans hm

theorem hmem_write {m : Mem} {scr : Addr} {M₁ : Block} {k e w : Nat} (v : BitVec w)
    (h : 256 + 16 * k + 16 ≤ e ∨ e + w / 8 ≤ 256 + 16 * k) (hk : k < 40) (he : e + w / 8 ≤ 2 ^ 64)
    (hm : HMem m scr M₁ k) : HMem (m.writeW (scr + BitVec.ofNat 64 e) v) scr M₁ k :=
  (Mem.readW_writeW_sep (Offset.sep scr h (by omega_arith) he) (by decide)).trans hm

theorem rmem_self (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) {e : Nat} (he : e = 32 * (k % 8)) :
    RMem (m.writeW (scr + BitVec.ofNat 64 e) (pair M₀ k ++ pair M₁ k)) scr M₀ M₁ k := by
  subst he; exact Mem.readW_writeW_self m _ 32 _ (by decide)

theorem hmem_self (m : Mem) (scr : Addr) (M₁ : Block) (k : Nat) :
    HMem (m.writeW (hiAddr scr k) (pair M₁ k)) scr M₁ k :=
  Mem.readW_writeW_self m _ 16 _ (by decide)

theorem in_scrN {s : State} {scr : Addr} (hR : (⟨scr, 1328⟩ : Region) ∈ s.wr) {d n : Nat}
    (hd : d + n ≤ 1328) : InRegions s.wr (scr + BitVec.ofNat 64 d) n :=
  ⟨_, hR, Offset.contains_base scr hd (by omega_arith)⟩

/-- The first block's rounds read the words the ring holds. -/
theorem wr0_of_rmem {s : State} {scr : Addr} {M₀ M₁ : Block} {i t' : Nat} (ht : t' < 16)
    (hrcx : s.gpr .rcx = scr) (hR : (⟨scr, 1328⟩ : Region) ∈ s.wr)
    (h : RMem s.mem scr M₀ M₁ (8 * i + t' / 2)) : WR 0 s t' (W M₀ (16 * i + t')) := by
  obtain e : s.ea (wSlotR 0 t') =
      ringAddr scr (8 * i + t' / 2) + BitVec.ofNat 64 (16 * 1 + 8 * (t' % 2)) := by
    simp only [State.ea, wSlotR, at_, hrcx, ↓reduceIte, ofInt_natCast, ringAddr]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun x => scr + BitVec.ofNat 64 x) (by omega_arith)
  refine ⟨?_, ?_⟩
  · rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]
    obtain ⟨r, hr, hc⟩ := in_scrN hR (d := 32 * ((8 * i + t' / 2) % 8) + (16 * 1 + 8 * (t' % 2))) (n := 8)
      (by omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [e]
    refine (readW_extract _ _ (w := 256) (k := 16 * 1 + 8 * (t' % 2)) (n := 8) (by omega_arith)).symm.trans ?_
    rw [h, extract_lane1 _ _ (Nat.mod_lt _ (by omega_arith)), qword_pair _ _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg (W M₀) (by omega_arith)

/-- The second block's rounds read the words kept for them. -/
theorem wr1_of_hmem {s : State} {scr : Addr} {M : Block} {i t' : Nat} (ht : t' < 16) (hi' : i < 5)
    (hrcx : s.gpr .rcx = scr) (hrdx : s.gpr .rdx = idx i) (hR : (⟨scr, 1328⟩ : Region) ∈ s.wr)
    (h : HMem s.mem scr M (8 * i + t' / 2)) : WR 1 s t' (W M (16 * i + t')) := by
  obtain e : s.ea (wSlotR 1 t') = hiAddr scr (8 * i + t' / 2) + BitVec.ofNat 64 (8 * (t' % 2)) := by
    simp only [State.ea, wSlotR, hrcx, hrdx, ofInt_natCast, BitVec.mul_one, hiAddr,
      Impl.Sha512.X86_64.Avx2Rolled.hi, Nat.one_ne_zero, ↓reduceIte]
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (fun x => scr + BitVec.ofNat 64 x) (by omega_arith)
  refine ⟨?_, ?_⟩
  · rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]
    obtain ⟨r, hr, hc⟩ := in_scrN hR (d := 256 + 16 * (8 * i + t' / 2) + 8 * (t' % 2)) (n := 8) (by omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [e, ← qword_readW _ _ (Nat.mod_lt _ (by omega_arith)), h, qword_pair _ _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg (W M) (by omega_arith)

/-! ## The prologue -/

/-- The callee-saved registers are saved in the scratch space. -/
abbrev Saved (s₀ : State) (s : State) : Prop := Spill.Saved s.mem (scr s₀) s₀.gpr Impl.Sha512.X86_64.Avx2Rolled.saved

theorem saved_bound : ∀ p ∈ Impl.Sha512.X86_64.Avx2Rolled.saved, 1256 ≤ p.2 ∧ p.2 + 8 ≤ 1312 := by decide

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (scr s₀) s₀.gpr Impl.Sha512.X86_64.Avx2Rolled.saved

theorem save_eq : Impl.Sha512.X86_64.Avx2Rolled.save =
    Spill.saveCode .rcx Impl.Sha512.X86_64.Avx2Rolled.saved := rfl

set_option simprocs false in
theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (Impl.Sha512.X86_64.Avx2Rolled.save ++ const mBswap bswapMask ++
        ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀
      fun s₁ =>
      (∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.syms = s₀.syms ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) ∧ Masks s₁ := by
  rw [save_eq, List.append_assoc]
  refine Spill.save_then .rcx Impl.Sha512.X86_64.Avx2Rolled.saved (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [const, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, VOp.exec, State.setV, State.lane,
    State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial, ?_⟩
  simp (config := {decide := true}) only [Masks, mBswap, ite_true, ite_false, VBinOp.sse,
    movq_const, and_self]

/-! ## Keeping `rsi` and `rdx` in the scratch space -/

/-- Where `enter` keeps `rsi` and `rdx`. -/
abbrev spA (scr : Addr) : Addr := Spill.slot scr 1312
abbrev spB (scr : Addr) : Addr := Spill.slot scr 1320

theorem idx_zero : idx 0 = BitVec.signExtend 64 (0 : BitVec 32) := by decide

theorem enter_ok (s : State) (hA : InRegions s.wr (spA (s.gpr .rcx)) 8)
    (hB : InRegions s.wr (spB (s.gpr .rcx)) 8) :
    WP isa (.block enter) s fun s' =>
      s'.gpr .rsi = s.syms kSym ∧ s'.gpr .rdx = idx 0 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (spA (s.gpr .rcx)) (s.gpr .rsi)).writeW (spB (s.gpr .rcx)) (s.gpr .rdx) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [enter, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.store64,
    Spill.ea_slot, hA, hB, ite_true, State.setReg, Option.map_some, Option.some.injEq,
    exists_eq_left', ← idx_zero]
  exact ⟨by simp, by simp, fun r h1 h2 => by simp [h1, h2], by simp, trivial, trivial, trivial, trivial⟩

theorem leave_ok (s : State) (hA : InRegions (s.rd ++ s.wr) (spA (s.gpr .rcx)) 8)
    (hB : InRegions (s.rd ++ s.wr) (spB (s.gpr .rcx)) 8) :
    WP isa (.block leave) s fun s' =>
      s'.gpr .rsi = s.mem.readW (spA (s.gpr .rcx)) 64 ∧ s'.gpr .rdx = s.mem.readW (spB (s.gpr .rcx)) 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [leave, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.load64,
    Spill.ea_slot, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, reduceCtorEq, ↓reduceIte, hA, hB, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial, trivial, trivial⟩

theorem step_ok (stop : BitVec 32) (s : State) :
    WP isa (.block (step stop.toNat)) s fun s' =>
      eval .ne s' = some (!(s.gpr .rdx + 128 - BitVec.signExtend 64 (BitVec.ofNat 32 stop.toNat) == 0)) ∧
      s'.gpr .rdx = s.gpr .rdx + 128 ∧ (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [step, ↓reduceIte, Nat.reducePow, and_self, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, State.setReg, arithFlags, State.setFlags, e128,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, fun r h => by simp [h], trivial⟩

/-- The loops stop after iteration `j`: `128 (j + 1) = stop`. -/
theorem step_idx {j n : Nat} (hj : j < n) (hn : n ≤ 5) :
    (idx j + 128 - BitVec.signExtend 64 (BitVec.ofNat 32 (128 * n)) == 0) = (j + 1 == n) := by
  revert j; revert n; decide

theorem idx_succ (j : Nat) : idx j + 128 = idx (j + 1) := by
  simp only [idx]
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add]
  congr 1

/-! ## The schedule, across the iterations -/

/-- The registers the rounds of an iteration keep, but its index. -/
def pubR : List Reg := [.rdi, .rsi, .rcx, .rsp]

theorem pubR_sub {r : Reg} (h : r ∈ pubR) : r ∈ pubRegs := by
  simp only [pubR, pubRegs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp

/-- The scratch space after `n` steps of the schedule were stored, and the
registers after `n'` of them were computed (`n'` is `n`, or `n + 1` between
a step and its stores): the ring holds the words `2n … 2n+15` of both
blocks, and the second block's words up to `2n+15` are kept. -/
structure SchedR (M₀ M₁ : Block) (scr : Addr) (sB : State) (n n' : Nat) (s : State) : Prop where
  pub : ∀ r ∈ pubR, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  masks : Masks s
  frame : Frame [wR scr] sB.mem s.mem
  ring : ∀ k, n ≤ k → k < n + 8 → k < 40 → RMem s.mem scr M₀ M₁ k
  high : ∀ k < 40, k < n + 8 → HMem s.mem scr M₁ k
  msgs : ∀ k, n' ≤ k → k < n' + 8 → k < 40 → s.xmm (msg k) = pair M₁ k ∧ s.ymmHi (msg k) = pair M₀ k
  syms : s.syms = sB.syms

theorem SchedR.keeps {M₀ M₁ : Block} {scr : Addr} {sB : State} {n n' : Nat} {s s' : State}
    (h : SchedR M₀ M₁ scr sB n n' s) (hk : KeepsS s s') : SchedR M₀ M₁ scr sB n n' s' := by
  obtain ⟨⟨hm, hrd, hwr, hpub, hx, hy⟩, hsy⟩ := hk
  refine ⟨fun r hr => (hpub r (pubR_sub hr)).trans (h.pub r hr), hrd.trans h.rd, hwr.trans h.wr, ?_,
    hm ▸ h.frame, fun k h₁ h₂ h₃ => hm ▸ h.ring k h₁ h₂ h₃, fun k hk hk' => hm ▸ h.high k hk hk',
    fun k h₁ h₂ h₃ => hx ▸ hy ▸ h.msgs k h₁ h₂ h₃,
    hsy.trans h.syms⟩
  rw [Masks, hx, hy]; exact h.masks

theorem msg_mod8 (j n : Nat) : msg (8 * j + n) = msg n := by
  simp only [msg]; rw [show (8 * j + n) % 8 = n % 8 by omega_arith]

/-- The schedule step `n + 8` of iteration `j`: words `2N+16, 2N+17`, `N = 8 j + n`. -/
theorem schedR_step {M₀ M₁ : Block} {scr : Addr} {sB : State} {j n : Nat} (hn : n < 8) (hN : 8 * j + n < 32)
    {s : State} (h : SchedR M₀ M₁ scr sB (8 * j + n) (8 * j + n) s) :
    WP isa (.block (scheduleR (n + 8))) s fun s' =>
      SchedR M₀ M₁ scr sB (8 * j + n) (8 * j + n + 1) s' ∧ s'.gpr = s.gpr := by
  obtain m : ∀ q < 8, s.xmm (msg (n + 8 + q)) = pair M₁ (8 * j + n + q) ∧
      s.ymmHi (msg (n + 8 + q)) = pair M₀ (8 * j + n + q) := fun q hq => by
    rw [show n + 8 + q = 8 * j + n + q + 8 - 8 * j by omega_arith, ← msg_mod8 j, show 8 * j + (8 * j + n + q + 8 - 8 * j)
      = 8 * j + n + q + 8 by omega_arith, msg_add8]
    exact h.msgs (8 * j + n + q) (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ⟨ma, ma'⟩ := m 0 (by omega_arith)
  obtain ⟨mb, mb'⟩ := m 1 (by omega_arith)
  obtain ⟨mc, mc'⟩ := m 4 (by omega_arith)
  obtain ⟨md, md'⟩ := m 5 (by omega_arith)
  obtain ⟨me, me'⟩ := m 7 (by omega_arith)
  simp only [Nat.add_zero] at ma ma'
  refine VG.X86_64.WP.mono_syms (scheduleR_ok (n + 8) s _ _ _ _ _ _ _ _ _ _ ma mb mc md me ma' mb' mc' md' me')
    fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ hsy => ⟨?_, hg⟩
  rw [xupd_pair] at ex ey
  obtain hmsg : msg (n + 8) = msg (8 * j + n + 8) := by
    rw [show 8 * j + n + 8 = 8 * j + (n + 8) by omega_arith, msg_mod8]
  rw [hmsg] at ex ey hx
  refine ⟨fun r hr => by rw [hg]; exact h.pub r hr, hrd.trans h.rd, hwr.trans h.wr, ?_, hm ▸ h.frame,
    fun k h₁ h₂ h₃ => hm ▸ h.ring k h₁ h₂ h₃, fun k hk hk' => hm ▸ h.high k hk hk', ?_,
    hsy.trans h.syms⟩
  · have o := hx mBswap (sched_other (8 * j + n + 8) mBswap (.inl rfl)).1
      (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.1
      (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.2.1 (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.2.2.1
      (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.2.2.2
    have masks := h.masks
    rw [Masks, o.1, o.2]
    exact masks
  · intro k h₁ h₂ h₃
    by_cases hkn : k = 8 * j + n + 8
    · subst hkn; exact ⟨ex, ey⟩
    · have o := msg_ne (8 * j + n + 8) (k + 8) (by omega_arith) (by omega_arith)
      rw [msg_add8] at o
      rw [(hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).1, (hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).2]
      exact h.msgs k (by omega_arith) (by omega_arith) h₃

/-- The stores of a schedule step, in iteration `j`. -/
theorem storeR_ok (n j : Nat) (s : State) {scr : Addr} (hrcx : s.gpr .rcx = scr) (hrdx : s.gpr .rdx = idx j)
    (hr : InRegions s.wr (scr + BitVec.ofNat 64 (32 * n)) 32)
    (hh : InRegions s.wr (scr + BitVec.ofNat 64 (256 + 16 * (8 * j + n + 8))) 16) :
    WP isa (.block (storeR n)) s fun s' =>
      s'.mem = (s.mem.writeW (scr + BitVec.ofNat 64 (32 * n)) (s.ymmHi (msg (n + 8)) ++ s.xmm (msg (n + 8)))).writeW
        (scr + BitVec.ofNat 64 (256 + 16 * (8 * j + n + 8))) (s.xmm (msg (n + 8))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  obtain e₂ : scr + BitVec.ofNat 64 (128 * j) + BitVec.ofNat 64 (256 + 128 + 16 * n) =
      scr + BitVec.ofNat 64 (256 + 16 * (8 * j + n + 8)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun x => scr + BitVec.ofNat 64 x) (by omega_arith)
  apply WP.of_runBlock
  simp only [storeR, ringSlot, hiSlot, at_, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    State.store256, State.store128, State.ymm, State.ea, hrcx, hrdx, ofInt_natCast, BitVec.mul_one,
    Impl.Sha512.X86_64.Avx2Rolled.hi, e₂, hr, hh, ↓reduceIte, Option.some.injEq,
    exists_eq_left', and_self]

/-- The stores of the schedule step `n + 8` of iteration `j`. -/
theorem storeR_step {M₀ M₁ : Block} {scr : Addr} {sB : State} (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) {j n : Nat} (hn : n < 8) (hN : 8 * j + n < 32) {s : State}
    (hI : s.gpr .rdx = idx j) (h : SchedR M₀ M₁ scr sB (8 * j + n) (8 * j + n + 1) s) :
    WP isa (.block (storeR n)) s fun s' =>
      SchedR M₀ M₁ scr sB (8 * j + n + 1) (8 * j + n + 1) s' ∧ s'.gpr = s.gpr := by
  obtain hrcx' : s.gpr .rcx = scr := (h.pub .rcx (by decide)).trans hrcx
  obtain ⟨ex, ey⟩ : s.xmm (msg (n + 8)) = pair M₁ (8 * j + n + 8) ∧
      s.ymmHi (msg (n + 8)) = pair M₀ (8 * j + n + 8) := by
    rw [show msg (n + 8) = msg (8 * j + n + 8) by
      rw [show 8 * j + n + 8 = 8 * j + (n + 8) by omega_arith, msg_mod8]]
    exact h.msgs _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine VG.X86_64.WP.mono_syms (storeR_ok n j s hrcx' hI (by rw [h.wr]; exact in_scrN hR (by omega_arith))
    (by rw [h.wr]; exact in_scrN hR (by omega_arith)))
    fun s' ⟨hm, hg, hrd, hwr, hx, hy⟩ hsy => ⟨?_, hg⟩
  rw [ex, ey] at hm
  refine ⟨fun r hr => by rw [hg]; exact h.pub r hr, hrd.trans h.rd, hwr.trans h.wr,
    by rw [Masks, hx, hy]; exact h.masks, ?_, ?_, ?_, fun k h₁ h₂ h₃ => hx ▸ hy ▸ h.msgs k h₁ h₂ h₃,
    hsy.trans h.syms⟩
  · rw [hm]
    exact (h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base scr (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base scr (by omega_arith) (by omega_arith))
  · intro k h₁ h₂ h₃
    rw [hm]
    by_cases hk : k = 8 * j + n + 8
    · subst hk
      exact rmem_write _ (by omega_arith) (by omega_arith) (rmem_self _ _ _ _ _ (by omega_arith))
    · exact rmem_write _ (by omega_arith) (by omega_arith) (rmem_write _ (by omega_arith) (by omega_arith)
        (h.ring k (by omega_arith) (by omega_arith) h₃))
  · intro k hk hk'
    rw [hm]
    by_cases hkn : k = 8 * j + n + 8
    · subst hkn; exact hmem_self _ _ _ _
    · exact hmem_write _ (by omega_arith) hk (by omega_arith) (hmem_write _ (by omega_arith) hk (by omega_arith)
        (h.high k hk (by omega_arith)))

/-! ## The rounds of the first block -/

/-- The table can be read in `s`: its statics are those of `sB`. -/
theorem kok_of {kb : Addr} {sB s : State} (hk : ∀ t < 80, KOk kb sB t) (hs : s.syms = sB.syms) :
    ∀ t < 80, KOk kb s t := fun t ht => (hk t ht).of_syms hs

/-- After `n` groups of iteration `j`. -/
def GInvR (H : HashValue) (M₀ M₁ : Block) (scr : Addr) (sB : State) (j n : Nat) (s : State) : Prop :=
  Vars (2 * n) s (Spec.Sha512.rounds H M₀ (16 * j + 2 * n)) ∧
    SchedR M₀ M₁ scr sB (8 * j + n) (8 * j + n) s ∧ s.gpr .rdx = idx j

theorem groupsR_ok (H : HashValue) (M₀ M₁ : Block) (scr kb : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) (hkb : sB.gpr .rsi = kb) (hk : ∀ t < 80, KOk kb sB t)
    {j : Nat} (hj : j < 4) {s₀ : State} (h₀ : GInvR H M₀ M₁ scr sB j 0 s₀) :
    ∀ n ≤ 8, WP isa (groupsR n) s₀ (GInvR H M₀ M₁ scr sB j n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h₀
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s ⟨hv, hs, hI⟩ => ?_)
    rw [groupR, WP.block_append_iff]
    refine VG.Interleave.WP.weave (group_indeps (by omega_arith)) trivial ?_
    refine WP.mono (schedR_step (by omega_arith) (by omega_arith) hs) fun s₁ ⟨hs₁, hg₁⟩ => ?_
    obtain hv₁ : Vars (2 * n) s₁ (Spec.Sha512.rounds H M₀ (16 * j + 2 * n)) := by
      simp only [Vars, hg₁]; exact hv
    obtain hI₁ : Idx kb j s₁ := ⟨by rw [hg₁]; exact hI, by rw [hs₁.pub .rsi (by decide)]; exact hkb⟩
    obtain hrcx₁ : s₁.gpr .rcx = scr := (hs₁.pub .rcx (by decide)).trans hrcx
    obtain hR₁ : (⟨scr, 1328⟩ : Region) ∈ s₁.wr := hs₁.wr ▸ hR
    obtain hk₁ := kok_of hk hs₁.syms
    obtain hw : ∀ q < 2, WR 0 s₁ (2 * n + q) (W M₀ (16 * j + (2 * n + q))) := fun q hq =>
      wr0_of_rmem (by omega_arith) hrcx₁ hR₁ (by
        rw [show 8 * j + (2 * n + q) / 2 = 8 * j + n by omega_arith]
        exact hs₁.ring _ (Nat.le_refl _) (by omega_arith) (by omega_arith))
    rw [WP.block_append_iff]
    refine WP.mono (roundR_step 0 j (2 * n) H M₀ s₁ hI₁ hv₁ (hk₁ _ (by omega_arith))
      (hw 0 (by omega_arith))) fun s₂ ⟨hv₂, hk₂⟩ => ?_
    obtain hv₂' : Vars (2 * n + 1) s₂ (Spec.Sha512.rounds H M₀ (16 * j + (2 * n + 1))) := by
      rw [show 16 * j + (2 * n + 1) = 16 * j + 2 * n + 1 by omega_arith]; exact hv₂
    obtain hw₂ : WR 0 s₂ (2 * n + 1) (W M₀ (16 * j + (2 * n + 1))) := (hw 1 (by omega_arith)).keeps hk₂.1
    refine WP.mono (roundR_step 0 j (2 * n + 1) H M₀ s₂ (hI₁.keeps hk₂) hv₂'
      ((hk₁ _ (by omega_arith)).keeps hk₂) hw₂) fun s₃ ⟨hv₃, hk₃⟩ => ?_
    obtain hI₃ : s₃.gpr .rdx = idx j := by
      rw [hk₃.1.2.2.2.1 .rdx (by decide), hk₂.1.2.2.2.1 .rdx (by decide)]; exact hI₁.rdx
    refine WP.mono (storeR_step hrcx hR (by omega_arith) (by omega_arith) hI₃ ((hs₁.keeps hk₂).keeps hk₃))
      fun s₄ ⟨hs₄, hg₄⟩ => ⟨?_, hs₄, by rw [hg₄]; exact hI₃⟩
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega_arith]
    simp only [Vars, hg₄]
    exact hv₃

/-- What `step` leaves of `SchedR`: everything but `rdx` and the flags. -/
theorem SchedR.of_eq {M₀ M₁ : Block} {scr : Addr} {sB : State} {n n' : Nat} {s s' : State}
    (h : SchedR M₀ M₁ scr sB n n' s) (hg : ∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hsy : s'.syms = s.syms) :
    SchedR M₀ M₁ scr sB n n' s' := by
  refine ⟨fun r hr => (hg r ?_).trans (h.pub r hr), hrd.trans h.rd, hwr.trans h.wr, ?_,
    hm ▸ h.frame, fun k h₁ h₂ h₃ => hm ▸ h.ring k h₁ h₂ h₃, fun k hk hk' => hm ▸ h.high k hk hk',
    fun k h₁ h₂ h₃ => hx ▸ hy ▸ h.msgs k h₁ h₂ h₃,
    hsy.trans h.syms⟩
  · simp only [pubR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [Masks, hx, hy]; exact h.masks

theorem vars16 {s : State} {v : HashValue} : Vars 16 s v ↔ Vars 0 s v := vars_add16 1 0 s v

theorem step512 : step 512 = step (512 : BitVec 32).toNat := rfl
theorem step640 : step 640 = step (640 : BitVec 32).toNat := rfl

theorem bound_idx : ∀ j < 4, idx j &&& BitVec.signExtend 64 (384 : BitVec 32) = idx j := by decide

/-- The mask of the index changes nothing. -/
theorem bound_ok (s : State) {j : Nat} (hj : j < 4) (hI : s.gpr .rdx = idx j) :
    WP isa (.block bound) s fun s' =>
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [bound, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, State.setReg,
    arithFlags, State.setFlags, hI, bound_idx j hj, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨fun r => by by_cases h : r = .rdx <;> simp [h, hI], trivial, trivial, trivial, trivial, trivial⟩

/-- The first block's loop: rounds 0–63, and the schedule of both blocks. -/
theorem loop1_ok (H : HashValue) (M₀ M₁ : Block) (scr kb : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) (hkb : sB.gpr .rsi = kb) (hk : ∀ t < 80, KOk kb sB t)
    (h₀ : GInvR H M₀ M₁ scr sB 0 0 sB) :
    WP isa (.loop (.seq (.block bound) (.seq (groupsR 8) (.block (step 512)))) .ne) sB (GInvR H M₀ M₁ scr sB 4 0) := by
  let Inv : Nat → State → Prop := fun m s => ∃ j, m = 4 - j ∧ j < 4 ∧ GInvR H M₀ M₁ scr sB j 0 s
  obtain hstep : ∀ m s, Inv m s → WP isa (.seq (.block bound) (.seq (groupsR 8) (.block (step 512)))) s (fun s' =>
      (eval .ne s' = some false ∧ GInvR H M₀ M₁ scr sB 4 0 s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s' ⟨j, rfl, hj, hG'⟩
    refine WP.seq (VG.X86_64.WP.mono_syms (bound_ok s' hj hG'.2.2) fun s ⟨hgb, hmb, hrdb, hwrb, hxb, hyb⟩ hsyb => ?_)
    obtain hG : GInvR H M₀ M₁ scr sB j 0 s :=
      ⟨by simp only [Vars, hgb]; exact hG'.1, hG'.2.1.of_eq (fun r _ => hgb r) hmb hrdb hwrb hxb hyb hsyb,
        (hgb .rdx).trans hG'.2.2⟩
    refine WP.seq (WP.mono (groupsR_ok H M₀ M₁ scr kb sB hrcx hR hkb hk hj hG 8 (Nat.le_refl _))
      fun s₁ ⟨hv₁, hs₁, hI₁⟩ => ?_)
    rw [step512]
    refine VG.X86_64.WP.mono_syms (step_ok 512 s₁) fun s₂ ⟨he, hrdx, hg, hm, hrd, hwr, hx, hy⟩ hsy => ?_
    obtain hG₂ : GInvR H M₀ M₁ scr sB (j + 1) 0 s₂ := by
      refine ⟨?_, ?_, by rw [hrdx, hI₁, idx_succ]⟩
      · rw [show 16 * (j + 1) + 2 * 0 = 16 * j + 2 * 8 by omega_arith]
        simp only [Vars] at hv₁ ⊢
        obtain hv₁' := vars16.mp hv₁
        simp only [Vars] at hv₁'
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₁'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hg _ (by decide)]; assumption
      · rw [show 8 * (j + 1) + 0 = 8 * j + 8 by omega_arith]
        exact hs₁.of_eq hg hm hrd hwr hx hy hsy
    rw [hI₁, show (512 : BitVec 32).toNat = 128 * 4 from rfl, step_idx hj (by decide)] at he
    by_cases hlast : j + 1 = 4
    · left
      obtain hb : (j + 1 == 4) = true := beq_iff_eq.mpr hlast
      refine ⟨by rw [he, hb]; rfl, ?_⟩
      rw [← hlast]; exact hG₂
    · right
      obtain hb : (j + 1 == 4) = false := beq_eq_false_iff_ne.mpr hlast
      refine ⟨by rw [he, hb]; rfl, 4 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hG₂⟩
  exact WP.loop (M := isa) Inv hstep 4 sB ⟨0, rfl, by decide, h₀⟩

theorem vars8_of16 {s : State} {v : HashValue} (h : Vars 16 s v) : Vars8 s v :=
  Vars.vars8 (by exact h)

/-- Rounds 64–79 of the first block. -/
theorem tail_ok (H : HashValue) (M₀ M₁ : Block) (scr kb : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) (hkb : sB.gpr .rsi = kb) (hk : ∀ t < 80, KOk kb sB t)
    {s : State} (h : GInvR H M₀ M₁ scr sB 4 0 s) :
    WP isa (rounds16 0) s fun s' =>
      Vars8 s' (Spec.Sha512.rounds H M₀ 80) ∧ SchedR M₀ M₁ scr sB 32 32 s' ∧ s'.gpr .rdx = idx 4 := by
  obtain ⟨hv, hs, hI⟩ := h
  obtain hrcx' : s.gpr .rcx = scr := (hs.pub .rcx (by decide)).trans hrcx
  obtain hR' : (⟨scr, 1328⟩ : Region) ∈ s.wr := hs.wr ▸ hR
  obtain hk' := kok_of hk hs.syms
  refine WP.mono (roundsR_ok 0 4 H M₀ (P := fun _ => True) (p := .block [])
    (WP.block_nil ⟨trivial, hv, Keeps.refl s⟩) ⟨hI, by rw [hs.pub .rsi (by decide)]; exact hkb⟩
    (fun t ht => hk' _ (by omega_arith))
    (fun t ht => wr0_of_rmem ht hrcx' hR' (hs.ring _ (by omega_arith) (by omega_arith) (by omega_arith))) 16
      (Nat.le_refl _))
    fun s' ⟨_, hv', hk₁⟩ => ⟨vars8_of16 hv', hs.keeps hk₁, (hk₁.1.2.2.2.1 .rdx (by decide)).trans hI⟩

/-- What the second block's loop keeps of the state `sC` it starts from. -/
structure Same (sC s : State) : Prop where
  mem : s.mem = sC.mem
  rd : s.rd = sC.rd
  wr : s.wr = sC.wr
  pub : ∀ r ∈ pubR, s.gpr r = sC.gpr r
  xmm : s.xmm = sC.xmm
  ymmHi : s.ymmHi = sC.ymmHi
  syms : s.syms = sC.syms

theorem KOk.of_same {kb : Addr} {sC s : State} {t : Nat} (h : KOk kb sC t) (hs : Same sC s) : KOk kb s t :=
  h.of_syms hs.syms

theorem Same.keeps {sC s s' : State} (h : Same sC s) (hk : KeepsS s s') : Same sC s' :=
  ⟨hk.1.1.trans h.mem, hk.1.2.1.trans h.rd, hk.1.2.2.1.trans h.wr,
    fun r hr => (hk.1.2.2.2.1 r (pubR_sub hr)).trans (h.pub r hr), hk.1.2.2.2.2.1.trans h.xmm,
    hk.1.2.2.2.2.2.trans h.ymmHi, hk.2.trans h.syms⟩

/-- The second block's loop: its 80 rounds. -/
theorem loop2_ok (H : HashValue) (M : Block) (scr kb : Addr) (sC : State) (hrcx : sC.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sC.wr) (hkb : sC.gpr .rsi = kb)
    (hk : ∀ t < 80, KOk kb sC t) (hw : ∀ k < 40, HMem sC.mem scr M k) (hv : Vars 0 sC H)
    (hI : sC.gpr .rdx = idx 0) :
    WP isa (.loop (.seq (rounds16 1) (.block (step 640))) .ne) sC fun s =>
      Vars8 s (Spec.Sha512.rounds H M 80) ∧ Same sC s := by
  let Inv : Nat → State → Prop := fun m s => ∃ j, m = 5 - j ∧ j < 5 ∧
    Vars 0 s (Spec.Sha512.rounds H M (16 * j)) ∧ s.gpr .rdx = idx j ∧ Same sC s
  obtain hstep : ∀ m s, Inv m s → WP isa (.seq (rounds16 1) (.block (step 640))) s (fun s' =>
      (eval .ne s' = some false ∧ Vars8 s' (Spec.Sha512.rounds H M 80) ∧ Same sC s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨j, rfl, hj, hv₀, hI₀, hS⟩
    refine WP.seq (WP.mono (roundsR_ok 1 j H M (P := fun _ => True) (p := .block [])
      (WP.block_nil ⟨trivial, hv₀, Keeps.refl s⟩) ⟨hI₀, by rw [hS.pub .rsi (by decide)]; exact hkb⟩
      (fun t ht => KOk.of_same (hk (16 * j + t) (by omega_arith)) hS)
      (fun t ht => wr1_of_hmem (scr := scr) ht hj ((hS.pub .rcx (by decide)).trans hrcx) hI₀ (by rw [hS.wr]; exact hR)
        (by rw [hS.mem]; exact hw _ (by omega_arith))) 16 (Nat.le_refl _))
      fun s₁ ⟨_, hv₁, hk₁⟩ => ?_)
    rw [step640]
    refine VG.X86_64.WP.mono_syms (step_ok 640 s₁) fun s₂ ⟨he, hrdx, hg, hm, hrd, hwr, hx, hy⟩ hsy => ?_
    obtain hI₁ : s₁.gpr .rdx = idx j := (hk₁.1.2.2.2.1 .rdx (by decide)).trans hI₀
    obtain hS₂ : Same sC s₂ := by
      obtain hS₁ := hS.keeps hk₁
      refine ⟨hm.trans hS₁.mem, hrd.trans hS₁.rd, hwr.trans hS₁.wr, fun r hr => (hg r ?_).trans (hS₁.pub r hr),
        hx.trans hS₁.xmm, hy.trans hS₁.ymmHi, hsy.trans hS₁.syms⟩
      simp only [pubR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    obtain hv₂ : Vars 16 s₂ (Spec.Sha512.rounds H M (16 * j + 16)) := by
      simp only [Vars] at hv₁ ⊢
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₁
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hg _ (by decide)]; assumption
    rw [hI₁, show (640 : BitVec 32).toNat = 128 * 5 from rfl, step_idx hj (by decide)] at he
    by_cases hlast : j + 1 = 5
    · left
      obtain hb : (j + 1 == 5) = true := beq_iff_eq.mpr hlast
      refine ⟨by rw [he, hb]; rfl, ?_, hS₂⟩
      rw [show 80 = 16 * j + 16 by omega_arith]; exact vars8_of16 hv₂
    · right
      obtain hb : (j + 1 == 5) = false := beq_eq_false_iff_ne.mpr hlast
      refine ⟨by rw [he, hb]; rfl, 5 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, ?_,
        by rw [hrdx, hI₁, idx_succ], hS₂⟩
      rw [show 16 * (j + 1) = 16 * j + 16 by omega_arith]; exact vars16.mp hv₂
  exact WP.loop (M := isa) Inv hstep 5 sC ⟨0, rfl, by decide, hv, hI,
    ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩⟩

/-! ## Loading the blocks -/

/-- `loadR`: the block at `p₁` in lane 0 and the block at `p₀` in lane 1. -/
theorem loadR_ok {i : Nat} (s : State) {p₀ p₁ scr : Addr} {M₀ M₁ : Block}
    (hrsi : s.gpr .rsi = p₀) (hr15 : s.gpr .r15 = p₁) (hrcx : s.gpr .rcx = scr)
    (hin₀ : InRegions (s.rd ++ s.wr) (p₀ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (p₁ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hr : InRegions s.wr (scr + BitVec.ofInt 64 ((32 * i : Nat) : Int)) 32)
    (hh : InRegions s.wr (scr + BitVec.ofInt 64 ((256 + 16 * i : Nat) : Int)) 16)
    (hm : s.xmm mBswap = bswapMask) (hm' : s.ymmHi mBswap = bswapMask)
    (q₀ : XBinOp.eval .pshufb (s.mem.readW (p₀ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 128) bswapMask =
      pair M₀ i)
    (q₁ : XBinOp.eval .pshufb (s.mem.readW (p₁ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 128) bswapMask =
      pair M₁ i) :
    WP isa (.block (loadR i)) s fun s' =>
      s'.xmm (msg i) = pair M₁ i ∧ s'.ymmHi (msg i) = pair M₀ i ∧
      (∀ r, r ≠ msg i → r ≠ tmp → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = (s.mem.writeW (scr + BitVec.ofInt 64 ((32 * i : Nat) : Int)) (pair M₀ i ++ pair M₁ i)).writeW
        (scr + BitVec.ofInt 64 ((256 + 16 * i : Nat) : Int)) (pair M₁ i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup i
  have hd' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [loadR, vb, ringSlot, Impl.Sha512.X86_64.Avx2Rolled.hi]
  generalize msg i = x at *
  generalize msg (i + 1) = x₁ at *
  generalize msg (i + 4) = x₄ at *
  generalize msg (i + 5) = x₅ at *
  generalize msg (i + 7) = x₇ at *
  simp only [T, t0, t1, t2, t3, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd' hm hm' ⊢
  obtain b1 : (1 : BitVec 8).getLsbD 0 = true := by decide
  simp only [reduceCtorEq, ↓reduceIte, b1, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, State.setV, State.lane, State.ymm, State.store256, State.store128, State.load128, ea_at, hrsi, hr15,
    hrcx, hin₀, hin₁, hr, hh, hd, hd', hm, hm', VBinOp.sse, q₀, q₁, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial, trivial⟩

/-- After loading words `0 … 2n-1` of both blocks, from the state `sL`. -/
structure LdInvR (M₀ M₁ : Block) (scr : Addr) (sL : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = sL.gpr
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  masks : Masks s
  frame : Frame [wR scr] sL.mem s.mem
  ring : ∀ k < n, RMem s.mem scr M₀ M₁ k
  high : ∀ k < n, HMem s.mem scr M₁ k
  msgs : ∀ k < n, s.xmm (msg k) = pair M₁ k ∧ s.ymmHi (msg k) = pair M₀ k

theorem load_stepR {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sL : State}
    (hrsi : sL.gpr .rsi = p₀) (hr15 : sL.gpr .r15 = p₁) (hrcx : sL.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sL.wr)
    (hin : ∀ n : Nat, n < 8 → InRegions (sL.rd ++ sL.wr) (p₀ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (sL.rd ++ sL.wr) (p₁ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ m, Frame [wR scr] sL.mem m →
      (∀ t : Nat, t < 16 → bswap64 (m.readW (p₀ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₀ t) ∧
      (∀ t : Nat, t < 16 → bswap64 (m.readW (p₁ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₁ t))
    {n : Nat} (hn : n < 8) {s : State} (h : LdInvR M₀ M₁ scr sL n s) :
    WP isa (.block (loadR n)) s (LdInvR M₀ M₁ scr sL (n + 1)) := by
  obtain ⟨k1, k2⟩ := h.masks
  refine WP.mono (loadR_ok (p₀ := p₀) (p₁ := p₁) (scr := scr) (M₀ := M₀) (M₁ := M₁) s
    (by rw [h.gpr]; exact hrsi) (by rw [h.gpr]; exact hr15) (by rw [h.gpr]; exact hrcx)
    (by rw [h.rd, h.wr]; exact (hin n hn).1) (by rw [h.rd, h.wr]; exact (hin n hn).2)
    (by rw [h.wr, ofInt_natCast]; exact in_scrN hR (by omega_arith))
    (by rw [h.wr, ofInt_natCast]; exact in_scrN hR (by omega_arith)) k1 k2
    (load_pair M₀ s.mem p₀ hn (hblk _ h.frame).1) (load_pair M₁ s.mem p₁ hn (hblk _ h.frame).2))
    fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ => ?_
  rw [ofInt_natCast, ofInt_natCast] at hm
  refine ⟨hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩
  · have o := hx mBswap (sched_other n mBswap (.inl rfl)).1 (by decide)
    rw [Masks, o.1, o.2]
    exact ⟨k1, k2⟩
  · rw [hm]
    exact (h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base scr (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base scr (by omega_arith) (by omega_arith))
  · intro k hk
    rw [hm]
    by_cases hkn : k = n
    · subst hkn
      exact rmem_write _ (by omega_arith) (by omega_arith) (rmem_self _ _ _ _ _ (by omega_arith))
    · exact rmem_write _ (by omega_arith) (by omega_arith) (rmem_write _ (by omega_arith) (by omega_arith)
        (h.ring k (by omega_arith)))
  · intro k hk
    rw [hm]
    by_cases hkn : k = n
    · subst hkn; exact hmem_self _ _ _ _
    · exact hmem_write _ (by omega_arith) (by omega_arith) (by omega_arith) (hmem_write _ (by omega_arith)
        (by omega_arith) (by omega_arith) (h.high k (by omega_arith)))
  · intro k hk
    by_cases hkn : k = n
    · subst hkn; exact ⟨ex, ey⟩
    · have o₁ := (msg_ne k n (by omega_arith) (by omega_arith)).1
      have o₂ := (sched_other k tmp (.inr rfl)).1
      rw [(hx _ (Ne.symm o₁) (Ne.symm o₂)).1, (hx _ (Ne.symm o₁) (Ne.symm o₂)).2]
      exact h.msgs k (by omega_arith)

/-! ## The hash value -/

theorem loadState_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block loadState) s fun s₁ => Vars8 s₁ (stateAt s.mem (st s₀)) ∧ Keeps s s₁ :=
  Avx2.loadState_ok hp.avx2 hrdi hrd hwr

theorem addState_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars8 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 = H[k]) :
    WP isa (.block addState) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      Vars8 s' (Vector.zipWith (· + ·) V H) ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi :=
  Avx2.addState_ok hp.avx2 V H hv hrdi hrd hwr hH

/-! ## The loop invariant -/

/-- The slots that keep `rdi` and `rdx`. -/
abbrev spR (p : Addr) : Region := ⟨spA p, 16⟩

theorem sp_sub (p : Addr) : Region.Sub (spR p) ⟨p, 1328⟩ := Offset.sub_base _ (by omega_arith)

theorem w_sp (p : Addr) : Region.Disjoint (wRegion p) (spR p) := Offset.base_disjoint _ (by omega_arith) (by omega_arith)

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : Saved s₀ s
  masks : Masks s
  syms : s.syms = s₀.syms

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-- After the first block of an iteration. -/
structure Mid (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ (i + 1) s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  vars : Vars8 s (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1))
  high : ∀ k < 40, HMem s.mem (scr s₀) (blk s₀ (nxt s₀ i)) k
  e : eval .e s = some (nb s₀ - i == 1)

theorem saved_frame {s₀ : State} (hp : Pre s₀) {s s' : State} (h : Saved s₀ s)
    (hf : Frame [wR (scr s₀)] s.mem s'.mem ∨ Frame [stR s₀] s.mem s'.mem ∨ Frame [spR (scr s₀)] s.mem s'.mem) :
    Saved s₀ s' := by
  rcases hf with hf | hf | hf <;> refine Spill.Saved.frame h hf fun p hp' r hr => ?_ <;>
    rw [List.mem_singleton.mp hr] <;> have := saved_bound p hp'
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega_arith))
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The table, in any state naming the statics `s₀` names. -/
theorem kok_of_syms {s₀ s : State} (hs : s.syms = s₀.syms) : ∀ t < 80, KOk (kb s₀) s t :=
  fun t ht => ⟨by rw [hs], ht⟩

theorem spill_read (p : Addr) (m : Mem) (a b : BitVec 64) :
    ((m.writeW (spA p) a).writeW (spB p) b).readW (spA p) 64 = a ∧
      ((m.writeW (spA p) a).writeW (spB p) b).readW (spB p) 64 = b :=
  ⟨(Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)).trans
    (Mem.readW_writeW_self m _ 8 a (by decide)), Mem.readW_writeW_self _ _ 8 b (by decide)⟩

theorem spA_in (p : Addr) : (spR p).Contains (spA p) 8 :=
  Offset.contains (e := 1312) (d := 1312) (n := 8) (k := 16) p (by omega_arith) (by omega_arith) (by omega_arith)

theorem spB_in (p : Addr) : (spR p).Contains (spB p) 8 :=
  Offset.contains (e := 1312) (d := 1320) (n := 8) (k := 16) p (by omega_arith) (by omega_arith) (by omega_arith)

theorem spill_frame (p : Addr) (m : Mem) (a b : BitVec 64) :
    Frame [spR p] m ((m.writeW (spA p) a).writeW (spB p) b) := by
  refine ((Frame.refl _ m).writeW (List.mem_singleton_self _) a ?_).writeW (List.mem_singleton_self _) b ?_
  · exact spA_in p
  · exact spB_in p

/-- What is read in the scratch space below the slots of `rsi` and `rdx`
is kept by writes of the hash value and of those slots. -/
theorem scr_read {s₀ : State} (hp : Pre s₀) {m m' : Mem} {d w : Nat} (hd : d + w / 8 ≤ 1312)
    (hf : Frame [stR s₀] m m' ∨ Frame [spR (scr s₀)] m m') :
    m'.readW (scr s₀ + BitVec.ofNat 64 d) w = m.readW (scr s₀ + BitVec.ofNat 64 d) w := by
  obtain hs : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 d, w / 8⟩ (scrR s₀) := Offset.sub_base _ (by omega_arith)
  rcases hf with hf | hf
  · exact hf.readW (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]; exact Region.Disjoint.sub_left hp.st_scr.symm hs) (by omega_arith)
  · refine hf.readW (Region.contains_self _ _) ?_ (by omega_arith)
    simp only [List.mem_singleton, forall_eq]
    exact Offset.disjoint _ (.inl hd) (by omega_arith) (by omega_arith)

theorem rmem_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} {M₀ M₁ : Block} {k : Nat}
    (h : RMem m (scr s₀) M₀ M₁ k) (hf : Frame [stR s₀] m m' ∨ Frame [spR (scr s₀)] m m') :
    RMem m' (scr s₀) M₀ M₁ k :=
  (scr_read hp (by omega_arith) hf).trans h

theorem hmem_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} {M₁ : Block} {k : Nat} (hk : k < 40)
    (h : HMem m (scr s₀) M₁ k) (hf : Frame [stR s₀] m m' ∨ Frame [spR (scr s₀)] m m') :
    HMem m' (scr s₀) M₁ k :=
  (scr_read hp (by omega_arith) hf).trans h

theorem state_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem}
    (hf : Frame [wRegion (scr s₀)] m m' ∨ Frame [spR (scr s₀)] m m') :
    stateAt m' (st s₀) = stateAt m (st s₀) := by
  rcases hf with hf | hf
  · exact state_frame_w hp.base hf
  · apply stateAt_eq
    intro k hk
    rw [hf.readW (contains_offset' (off := 8 * k) (len := 64) (by omega_arith) (by omega_arith))
      (by simpa using Region.Disjoint.sub_right hp.st_scr (sp_sub _)) (by decide), ← stateAt_get _ _ hk]

theorem spill_keep {s₀ : State} {m m' : Mem} (hf : Frame [wRegion (scr s₀)] m m') :
    m'.readW (spA (scr s₀)) 64 = m.readW (spA (scr s₀)) 64 ∧ m'.readW (spB (scr s₀)) 64 = m.readW (spB (scr s₀)) 64 :=
  ⟨hf.readW (spA_in _) (by simpa using (w_sp _).symm) (by decide),
    hf.readW (spB_in _) (by simpa using (w_sp _).symm) (by decide)⟩

theorem sp_in {s₀ : State} (hp : Pre s₀) {s : State} (hrcx : s.gpr .rcx = scr s₀) (hwr : s.wr = s₀.wr) :
    InRegions s.wr (spA (s.gpr .rcx)) 8 ∧ InRegions s.wr (spB (s.gpr .rcx)) 8 := by
  rw [hrcx, hwr]
  exact ⟨⟨scrR s₀, by simp [hp.wr], Offset.contains_base (d := 1312) (n := 8) (k := 1328) _ (by omega_arith) (by omega_arith)⟩,
    ⟨scrR s₀, by simp [hp.wr], Offset.contains_base (d := 1320) (n := 8) (k := 1328) _ (by omega_arith) (by omega_arith)⟩⟩

theorem sp_in' {s₀ : State} (hp : Pre s₀) {s : State} (hrcx : s.gpr .rcx = scr s₀) (hwr : s.wr = s₀.wr) :
    InRegions (s.rd ++ s.wr) (spA (s.gpr .rcx)) 8 ∧ InRegions (s.rd ++ s.wr) (spB (s.gpr .rcx)) 8 := by
  obtain ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩⟩ := sp_in hp hrcx hwr
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r', List.mem_append_right _ hr', hc'⟩⟩

/-- What holds after the first block's rounds, once `rsi` and `rdx` are back. -/
structure AtLeave (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  rcx : s.gpr .rcx = scr s₀
  rsi : s.gpr .rsi = blkAddr s₀ i
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  vars : Vars8 s (Spec.Sha512.rounds (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) (blk s₀ i) 80)
  saved : Saved s₀ s
  masks : Masks s
  high : ∀ k < 40, HMem s.mem (scr s₀) (blk s₀ (nxt s₀ i)) k
  syms : s.syms = s₀.syms

/-- The first block of an iteration, up to getting back `rsi` and `rdx`. -/
theorem prefix_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.first s (AtLeave s₀ i) := by
  have := hp.nb_lt
  obtain hscr : (⟨scr s₀, 1328⟩ : Region) ∈ s₀.wr := by simp [hp.wr]
  obtain hj : nxt s₀ i < nb s₀ := by simp only [nxt]; split <;> omega_arith
  obtain hb : (s.gpr .rdx - 1 == 0) = (nb s₀ - i == 1) := by rw [hL.rdx]; exact sub_one_eq hp.base hi
  refine WP.seq (VG.X86_64.WP.mono_syms (setup_ok s) fun s₁ ⟨he₁, h15₁, hg₁, hk₁⟩ hsy₁ => ?_)
  refine WP.seq (VG.X86_64.WP.mono_syms (Q := fun (s₂ : State) => s₂.gpr .r15 = blkAddr s₀ (nxt s₀ i) ∧
    (∀ r, r ≠ .r15 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂) ?_ fun s₂ ⟨h15₂, hg₂, hk₂⟩ hsy₂ => ?_)
  · refine WP.ite _ he₁ (fun h => ?_) (fun h => ?_)
    · rw [hb, beq_iff_eq] at h
      refine WP.block_nil ⟨?_, hg₁, hk₁⟩
      simp only [nxt, h, ↓reduceIte, h15₁, hL.rsi]
    · refine WP.mono (next_ok s₁) fun s₂ ⟨e15, eg, ek⟩ =>
        ⟨?_, fun r hr => (eg r hr).trans (hg₁ r hr), hk₁.trans ek⟩
      rw [hb, beq_eq_false_iff_ne] at h
      rw [e15, h15₁, hL.rsi]
      simp only [nxt, h, ↓reduceIte, blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add,
      show 128 * (i + 1) = 128 * i + 128 by omega_arith]
  obtain ⟨hm₂, hrd₂, hwr₂, -, hx₂, hy₂⟩ := hk₂
  obtain pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => hg₂ r (pub_ne15 hr)
  obtain hrsi₂ : s₂.gpr .rsi = blkAddr s₀ i := (pub₂ .rsi (by decide)).trans hL.rsi
  obtain hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hL.rcx
  obtain hrdi₂ : s₂.gpr .rdi = st s₀ := (pub₂ .rdi (by decide)).trans hL.rdi
  obtain hR₂ : (⟨scr s₀, 1328⟩ : Region) ∈ s₂.wr := by rw [hwr₂, hL.wr]; exact hscr
  obtain hf₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem := hm₂ ▸ hL.frame
  obtain hin : ∀ n : Nat, n < 8 →
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ (nxt s₀ i) + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 :=
    fun n hn => by rw [hrd₂, hwr₂, hL.rd, hL.wr]; exact ⟨hp.in_blk16 hi hn, hp.in_blk16 hj hn⟩
  obtain hblk := fun m (hm : Frame [wR (scr s₀)] s₂.mem m) =>
    And.intro (blk_read hp.base hi hf₂ (frame_wide hm)) (blk_read hp.base hj hf₂ (frame_wide hm))
  obtain step := fun {n : Nat} (hn : n < 8) {x : State}
      (h : LdInvR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ n x) =>
    load_stepR hrsi₂ h15₂ hrcx₂ hR₂ hin hblk hn h
  obtain hk2 : Masks s₂ := by rw [Masks, hx₂, hy₂]; exact hL.masks
  obtain h₀ : LdInvR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ 0 s₂ :=
    ⟨rfl, rfl, rfl, hk2, Frame.refl _ _, fun _ h => absurd h (by omega_arith),
      fun _ h => absurd h (by omega_arith), fun _ h => absurd h (by omega_arith)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine VG.X86_64.WP.mono_syms (Q := fun s₅ => ∃ s₃, LdInvR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ 8 s₃ ∧
    Vars 0 s₅ (stateAt s₃.mem (st s₀)) ∧ Keeps s₃ s₅) ?_ fun s₅ ⟨s₃, ld, hv₅, hk₃₅⟩ hsy₅ => ?_
  · rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
      WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
      WP.block_append_iff]
    refine WP.mono (step (by omega_arith) h₀) fun x₁ h₁ => ?_
    refine WP.mono (step (by omega_arith) h₁) fun x₂ h₂ => ?_
    refine WP.mono (step (by omega_arith) h₂) fun x₃ h₃ => ?_
    refine WP.mono (step (by omega_arith) h₃) fun x₄ h₄ => ?_
    refine WP.mono (step (by omega_arith) h₄) fun x₅ h₅ => ?_
    refine WP.mono (step (by omega_arith) h₅) fun x₆ h₆ => ?_
    refine WP.mono (step (by omega_arith) h₆) fun x₇ h₇ => ?_
    refine WP.mono (step (by omega_arith) h₇) fun s₃ ld => ?_
    refine WP.mono (loadState_ok hp (by rw [ld.gpr]; exact hrdi₂) (by rw [ld.rd, hrd₂, hL.rd])
      (by rw [ld.wr, hwr₂, hL.wr])) fun s₄ ⟨hv₄, hk₄⟩ => ?_
    exact WP.mono (initCarry_ok hv₄) fun s₅ ⟨hv₅, hk₅⟩ => ⟨s₃, ld, hv₅, hk₄.trans hk₅⟩
  obtain ⟨hm₅, hrd₅, hwr₅, pub₅, hx₅, hy₅⟩ := hk₃₅
  obtain hrcx₅ : s₅.gpr .rcx = scr s₀ := by rw [pub₅ .rcx (by decide), ld.gpr]; exact hrcx₂
  obtain hwr₅' : s₅.wr = s₀.wr := by rw [hwr₅, ld.wr, hwr₂, hL.wr]
  obtain hrd₅' : s₅.rd = s₀.rd := by rw [hrd₅, ld.rd, hrd₂, hL.rd]
  obtain hsy : s₅.syms = s₀.syms := by rw [hsy₅, hsy₂, hsy₁]; exact hL.syms
  obtain ⟨spa, spb⟩ := sp_in hp hrcx₅ hwr₅'
  refine VG.X86_64.WP.mono_syms (enter_ok s₅ spa spb) fun sB ⟨hrdiB, hrdxB, hgB, hmB, hrdB, hwrB, hxB, hyB⟩ hsyB => ?_
  rw [hsy] at hrdiB
  obtain hspB : Frame [spR (scr s₀)] s₅.mem sB.mem := by rw [hmB, hrcx₅]; exact spill_frame _ _ _ _
  obtain hrcxB : sB.gpr .rcx = scr s₀ := by rw [hgB _ (by decide) (by decide)]; exact hrcx₅
  obtain hRB : (⟨scr s₀, 1328⟩ : Region) ∈ sB.wr := by rw [hwrB, hwr₅']; exact hscr
  obtain hsub' : ∀ r ∈ [spR (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact sp_sub _⟩
  obtain hfB : Frame [stR s₀, scrR s₀] s₀.mem sB.mem :=
    hf₂.trans ((frame_scr ld.frame).trans (hm₅ ▸ hspB.sub hsub'))
  obtain hkB := kok_of_syms (s₀ := s₀) (s := sB) (by rw [hsyB, hsy])
  obtain hvB : Vars 0 sB (Spec.Sha512.rounds (stateAt s₃.mem (st s₀)) (blk s₀ i) (16 * 0 + 2 * 0)) := by
    simp only [Vars] at hv₅ ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₅
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hgB _ (by decide) (by decide)]; assumption
  obtain hSB : SchedR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) sB (8 * 0 + 0) (8 * 0 + 0) sB :=
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Masks, hxB, hyB, hx₅, hy₅]; exact ld.masks, Frame.refl _ _,
      fun k _ hk _ => rmem_frame hp (by rw [hm₅]; exact ld.ring k (by omega_arith)) (.inr hspB),
      fun k hk hk' => hmem_frame hp hk (by rw [hm₅]; exact ld.high k (by omega_arith)) (.inr hspB),
      fun k _ hk _ => by rw [hxB, hyB, hx₅, hy₅]; exact ld.msgs k (by omega_arith), rfl⟩
  refine WP.seq (VG.X86_64.WP.mono_syms (loop1_ok _ _ _ (scr s₀) (kb s₀) sB hrcxB hRB hrdiB hkB
    ⟨hvB, hSB, hrdxB⟩) fun s₆ h₆ hsy₆ => ?_)
  refine WP.seq (VG.X86_64.WP.mono_syms (tail_ok _ _ _ (scr s₀) (kb s₀) sB hrcxB hRB hrdiB hkB h₆)
    fun s₇ ⟨hv₇, hS₇, hrdx₇⟩ hsy₇ => ?_)
  obtain hrcx₇ : s₇.gpr .rcx = scr s₀ := (hS₇.pub .rcx (by decide)).trans hrcxB
  obtain hwr₇ : s₇.wr = s₀.wr := by rw [hS₇.wr, hwrB, hwr₅']
  obtain hrd₇ : s₇.rd = s₀.rd := by rw [hS₇.rd, hrdB, hrd₅']
  obtain ⟨spa', spb'⟩ := sp_in' hp hrcx₇ hwr₇
  refine VG.X86_64.WP.mono_syms (leave_ok s₇ spa' spb')
    fun s₈ ⟨hrdi₈, hrdx₈, hg₈, hm₈, hrd₈, hwr₈, hx₈, hy₈⟩ hsy₈ => ?_
  obtain sk := spill_keep (s₀ := s₀) (frame_wide hS₇.frame)
  obtain sr := spill_read (scr s₀) s₅.mem (s₅.gpr .rsi) (s₅.gpr .rdx)
  rw [← hrcx₅, ← hmB] at sr
  rw [hrcx₇, sk.1, ← hrcx₅, sr.1, pub₅ .rsi (by decide), ld.gpr, hrsi₂] at hrdi₈
  rw [hrcx₇, sk.2, ← hrcx₅, sr.2, pub₅ .rdx (by decide), ld.gpr, pub₂ .rdx (by decide)] at hrdx₈
  obtain hHi : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i := by
    rw [state_frame hp (.inl (frame_wide ld.frame)), hm₂]; exact hL.state
  obtain hst₈ : stateAt s₈.mem (st s₀) = stateAt s₃.mem (st s₀) := by
    rw [hm₈, state_frame hp (.inl (frame_wide hS₇.frame)), state_frame hp (.inr hspB), hm₅]
  obtain g₇ : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsp → s₈.gpr r = s.gpr r := fun r hr => by
    obtain h1 : r ∈ pubR := by rcases hr with rfl | rfl | rfl <;> decide
    obtain h2 : r ∈ pubRegs := pubR_sub h1
    obtain h3 : r ≠ .rsi := by rcases hr with rfl | rfl | rfl <;> decide
    obtain h4 : r ≠ .rdx := by rcases hr with rfl | rfl | rfl <;> decide
    rw [hg₈ r h3 h4, hS₇.pub r h1, hgB r h3 h4, pub₅ r h2, ld.gpr, pub₂ r h2]
  obtain a₂ : Saved s₀ s₂ := saved_frame hp hL.saved (.inl (hm₂ ▸ Frame.refl _ _))
  obtain a₃ : Saved s₀ s₃ := saved_frame hp a₂ (.inl ld.frame)
  obtain a₅ : Saved s₀ s₅ := saved_frame hp a₃ (.inl (hm₅ ▸ Frame.refl _ _))
  obtain aB : Saved s₀ sB := saved_frame hp a₅ (.inr (.inr hspB))
  obtain a₇ : Saved s₀ s₇ := saved_frame hp aB (.inl hS₇.frame)
  refine ⟨by rw [g₇ .rdi (by simp)]; exact hL.rdi, hrdx₈.trans hL.rdx, by rw [g₇ .rcx (by simp)]; exact hL.rcx,
    hrdi₈, by rw [g₇ .rsp (by simp)]; exact hL.rsp,
    by rw [hrd₈]; exact hrd₇, by rw [hwr₈]; exact hwr₇, ?_, hst₈.trans hHi, ?_,
    saved_frame hp a₇ (.inl (hm₈ ▸ Frame.refl _ _)), ?_, ?_, ?_⟩
  · rw [hm₈]; exact hfB.trans (frame_scr hS₇.frame)
  · rw [← hHi]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv₇
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hg₈ _ (by decide) (by decide)]; assumption
  · rw [Masks, hx₈, hy₈]; exact hS₇.masks
  · intro k hk; rw [hm₈]; exact hS₇.high k hk (by omega_arith)
  · rw [hsy₈, hsy₇, hsy₆, hsyB]; exact hsy

/-- The first block's hash value. -/
theorem first_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hA : AtLeave s₀ i s)
    {G : Prog isa} {Q : State → Prop} (hG : ∀ s', Mid s₀ i s' → WP isa G s' Q) :
    WP isa (.seq (.block (addState ++ ([.alu .cmp .rdx (.imm 1)] : List Instr))) G) s Q := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 =
        (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)[k] :=
    fun k hk => by rw [← stateAt_get _ _ hk, hA.state]
  refine VG.X86_64.WP.mono_syms (addState_ok hp _ _ hA.vars hA.rdi hA.rd hA.wr hH)
    fun s₉ ⟨hm₉, hv₉, pub₉, hrd₉, hwr₉, hx₉, hy₉⟩ hsy₉ => ?_
  refine VG.X86_64.WP.mono_syms (WP.mono (cmp_ok s₉) fun s₁₀ h => h) fun s₁₀ ⟨he₁₀, hg₁₀, hk₁₀⟩ hsy₁₀ => hG s₁₀ ?_
  obtain ⟨hm₁₀, hrd₁₀, hwr₁₀, -, hx₁₀, hy₁₀⟩ := hk₁₀
  obtain hc : Vector.zipWith (· + ·) (Spec.Sha512.rounds (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) (blk s₀ i) 80)
      (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ]; rfl
  obtain hfw : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]; exact frame_writeState (Frame.refl _ _) _
  obtain hsub' : ∀ r ∈ [stR s₀], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
  obtain g : ∀ r ∈ pubRegs, s₁₀.gpr r = s.gpr r := fun r hr => by rw [hg₁₀, pub₉ r hr]
  refine ⟨⟨by rw [g .rdi (by decide)]; exact hA.rdi, by rw [g .rcx (by decide)]; exact hA.rcx,
    by rw [g .rsp (by decide)]; exact hA.rsp, by rw [hrd₁₀, hrd₉]; exact hA.rd,
    by rw [hwr₁₀, hwr₉]; exact hA.wr, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [g .rsi (by decide)]; exact hA.rsi, by rw [g .rdx (by decide)]; exact hA.rdx, ?_, ?_, ?_⟩
  · rw [hm₁₀]; exact hA.frame.trans (hfw.sub hsub')
  · rw [hm₁₀, hm₉, stateAt_writeState]; exact hc
  · exact saved_frame hp (saved_frame hp hA.saved (.inr (.inl hfw))) (.inl (hm₁₀ ▸ Frame.refl _ _))
  · rw [Masks, hx₁₀, hy₁₀, hx₉, hy₉]; exact hA.masks
  · rw [hsy₁₀, hsy₉]; exact hA.syms
  · simp only [Vars8, hg₁₀]; rw [← hc]; exact hv₉
  · intro k hk
    rw [hm₁₀]
    exact hmem_frame hp hk (hA.high k hk) (.inl hfw)
  · rw [he₁₀, pub₉ .rdx (by decide), hA.rdx]; exact congrArg some (sub_one_eq hp.base hi)

/-! ## The end of an iteration -/

theorem adv_common {s₀ : State} (hp : Pre s₀) {k : Nat} {s : State} (hc : Common s₀ k s) (a b : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm a), .alu .sub .rdx (.imm b)]) s fun s' =>
      Common s₀ k s' ∧ eval .ne s' = some (!(s.gpr .rdx - b.signExtend 64 == 0)) ∧
      s'.gpr .rsi = s.gpr .rsi + a.signExtend 64 ∧ s'.gpr .rdx = s.gpr .rdx - b.signExtend 64 := by
  refine VG.X86_64.WP.mono_syms (adv_ok s a b) fun s' ⟨he, hrsi, hrdx, hg, hm, hrd, hwr, hx, hy⟩ hsy =>
    ⟨?_, he, hrsi, hrdx⟩
  refine ⟨by rw [hg _ (by decide) (by decide)]; exact hc.rdi, by rw [hg _ (by decide) (by decide)]; exact hc.rcx,
    by rw [hg _ (by decide) (by decide)]; exact hc.rsp, hrd.trans hc.rd, hwr.trans hc.wr, hm ▸ hc.frame,
    hm ▸ hc.state, saved_frame hp hc.saved (.inl (hm ▸ Frame.refl _ _)), ?_,
    hsy.trans hc.syms⟩
  rw [Masks, hx, hy]; exact hc.masks

/-- The loop exits after the last block, or goes on with block `k`. -/
theorem exit_or_next {s₀ : State} (hp : Pre s₀) {k : Nat} (hk' : k ≤ nb s₀) {s : State}
    (hc : Common s₀ k s) (hrsi : s.gpr .rsi = blkAddr s₀ k) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - k))
    (he : eval .ne s = some (!(BitVec.ofNat 64 (nb s₀ - k) == 0))) :
    (k = nb s₀ ∧ eval .ne s = some false ∧ Common s₀ (nb s₀) s) ∨
      (k < nb s₀ ∧ eval .ne s = some true ∧ LInv s₀ k s) := by
  by_cases hlast : k = nb s₀
  · left
    subst hlast
    refine ⟨rfl, by rw [he]; simp, hc⟩
  · right
    have := hp.nb_lt
    obtain h0 : BitVec.ofNat 64 (nb s₀ - k) ≠ 0 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at h'
      simp at h'
      omega_arith
    refine ⟨by omega_arith, by rw [he]; simpa using h0, { hc with rsi := hrsi, rdx := hrdx }⟩

/-- The block the next iteration starts at. -/
abbrev nxtI (s₀ : State) (i : Nat) : Nat := if nb s₀ - i = 1 then i + 1 else i + 2

/-- After an iteration from block `i`: the loop exits, or goes on with block `nxtI s₀ i`. -/
def BodyPost (s₀ : State) (i : Nat) (s : State) : Prop :=
  (nxtI s₀ i = nb s₀ ∧ eval .ne s = some false ∧ Common s₀ (nb s₀) s) ∨
    (nxtI s₀ i < nb s₀ ∧ eval .ne s = some true ∧ LInv s₀ (nxtI s₀ i) s)

theorem rest_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hA : AtLeave s₀ i s) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.rest s (BodyPost s₀ i) := by
  have := hp.nb_lt
  obtain hn := (s₀.gpr .rdx).isLt
  refine first_ok hp hi hA fun s₁ hM => WP.ite _ hM.e (fun h => ?_) (fun h => ?_)
  · rw [beq_iff_eq] at h
    refine WP.mono (adv_common hp hM.toCommon 128 1) fun s₂ ⟨hc, he, hrsi, hrdx⟩ => ?_
    obtain hrdx' : s₁.gpr .rdx - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
      rw [hM.rdx, e1, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    obtain hk : nxtI s₀ i = i + 1 := by simp only [nxtI, h, ↓reduceIte]
    unfold BodyPost; rw [hk]
    refine exit_or_next hp (by omega_arith) hc ?_ hrdx he
    rw [hrsi, hM.rsi, e128]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add,
      show 128 * (i + 1) = 128 * i + 128 by omega_arith]
  · rw [beq_eq_false_iff_ne] at h
    obtain hnx : nxt s₀ i = i + 1 := by simp only [nxt, h, ↓reduceIte]
    have hw := hM.high
    rw [hnx] at hw
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine VG.X86_64.WP.mono_syms (initCarry_ok hM.vars) fun s₂ ⟨hv₂, hk₂⟩ hsy₂ => ?_
    obtain ⟨hm₂, hrd₂, hwr₂, pub₂, hx₂, hy₂⟩ := hk₂
    obtain hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hM.rcx
    obtain hwr₂' : s₂.wr = s₀.wr := hwr₂.trans hM.wr
    obtain hrd₂' : s₂.rd = s₀.rd := hrd₂.trans hM.rd
    obtain ⟨spa, spb⟩ := sp_in hp hrcx₂ hwr₂'
    refine VG.X86_64.WP.mono_syms (enter_ok s₂ spa spb)
      fun sC ⟨hrdiC, hrdxC, hgC, hmC, hrdC, hwrC, hxC, hyC⟩ hsyC => ?_
    rw [hsy₂, hM.syms] at hrdiC
    obtain hspC : Frame [spR (scr s₀)] s₂.mem sC.mem := by rw [hmC, hrcx₂]; exact spill_frame _ _ _ _
    obtain hrcxC : sC.gpr .rcx = scr s₀ := by rw [hgC _ (by decide) (by decide)]; exact hrcx₂
    obtain hRC : (⟨scr s₀, 1328⟩ : Region) ∈ sC.wr := by rw [hwrC, hwr₂', hp.wr]; simp
    obtain hsub' : ∀ r ∈ [spR (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
      fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact sp_sub _⟩
    obtain hfC : Frame [stR s₀, scrR s₀] s₀.mem sC.mem := hM.frame.trans (hm₂ ▸ hspC.sub hsub')
    obtain hkC := kok_of_syms (s₀ := s₀) (s := sC) (by rw [hsyC, hsy₂, hM.syms])
    obtain hwC : ∀ k < 40, HMem sC.mem (scr s₀) (blk s₀ (i + 1)) k := fun k hk =>
      hmem_frame hp hk (by rw [hm₂]; exact hw k hk) (.inr hspC)
    obtain hvC : Vars 0 sC (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) := by
      simp only [Vars] at hv₂ ⊢
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₂
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hgC _ (by decide) (by decide)]; assumption
    refine WP.seq (VG.X86_64.WP.mono_syms (loop2_ok _ (blk s₀ (i + 1)) (scr s₀) (kb s₀) sC hrcxC hRC hrdiC hkC hwC hvC hrdxC)
      fun s₃ ⟨hv₃, hS₃⟩ hsy₃ => ?_)
    rw [WP.block_append_iff, WP.block_append_iff]
    obtain hrcx₃ : s₃.gpr .rcx = scr s₀ := (hS₃.pub .rcx (by decide)).trans hrcxC
    obtain hwr₃ : s₃.wr = s₀.wr := by rw [hS₃.wr, hwrC, hwr₂']
    obtain hrd₃ : s₃.rd = s₀.rd := by rw [hS₃.rd, hrdC, hrd₂']
    obtain ⟨spa', spb'⟩ := sp_in' hp hrcx₃ hwr₃
    refine VG.X86_64.WP.mono_syms (leave_ok s₃ spa' spb')
      fun s₄ ⟨hrdi₄, hrdx₄, hg₄, hm₄, hrd₄, hwr₄, hx₄, hy₄⟩ hsy₄ => ?_
    obtain sr := spill_read (scr s₀) s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)
    rw [← hrcx₂, ← hmC] at sr
    rw [hrcx₃, hS₃.mem, ← hrcx₂, sr.1, pub₂ .rsi (by decide)] at hrdi₄
    rw [hrcx₃, hS₃.mem, ← hrcx₂, sr.2, pub₂ .rdx (by decide)] at hrdx₄
    obtain hH : ∀ k : Nat, (hk : k < 8) → s₄.mem.readW (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 =
        (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1))[k] :=
      fun k hk => by
        rw [← hM.state, stateAt_get _ _ hk, hm₄, hS₃.mem, ← hm₂]
        exact hspC.readW (r := stR s₀) (contains_offset' (off := 8 * k) (len := 64) (by omega_arith) (by omega_arith))
          (by simpa using Region.Disjoint.sub_right hp.st_scr (sp_sub _)) (by decide)
    obtain hv₄ : Vars8 s₄ (Spec.Sha512.rounds (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) (blk s₀ (i + 1)) 80) := by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv₃
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hg₄ _ (by decide) (by decide)]; assumption
    refine VG.X86_64.WP.mono_syms (addState_ok hp _ _ hv₄ (by
      rw [hg₄ .rdi (by decide) (by decide), hS₃.pub .rdi (by decide), hgC .rdi (by decide) (by decide),
        pub₂ .rdi (by decide)]; exact hM.rdi) (by rw [hrd₄, hrd₃])
      (by rw [hwr₄, hwr₃]) hH) fun s₅ ⟨hm₅, _, pub₅, hrd₅, hwr₅, hx₅, hy₅⟩ hsy₅ => ?_
    obtain hfw : Frame [stR s₀] s₄.mem s₅.mem := by
      rw [hm₅]; exact frame_writeState (Frame.refl _ _) _
    obtain hrsi₅ : s₅.gpr .rsi = s₁.gpr .rsi := by rw [pub₅ .rsi (by decide), hrdi₄]
    obtain g₅ : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsp → s₅.gpr r = s₁.gpr r := fun r hr => by
      obtain h1 : r ∈ pubR := by rcases hr with rfl | rfl | rfl <;> decide
      obtain h2 : r ∈ pubRegs := pubR_sub h1
      obtain h3 : r ≠ .rsi := by rcases hr with rfl | rfl | rfl <;> decide
      obtain h4 : r ≠ .rdx := by rcases hr with rfl | rfl | rfl <;> decide
      rw [pub₅ r h2, hg₄ r h3 h4, hS₃.pub r h1, hgC r h3 h4, pub₂ r h2]
    obtain hc₄ : Common s₀ (i + 2) s₅ := by
      obtain hsub'' : ∀ r ∈ [stR s₀], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
        fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
      refine ⟨by rw [g₅ .rdi (by simp)]; exact hM.rdi,
        by rw [g₅ .rcx (by simp)]; exact hM.rcx, by rw [g₅ .rsp (by simp)]; exact hM.rsp,
        by rw [hrd₅, hrd₄]; exact hrd₃, by rw [hwr₅, hwr₄]; exact hwr₃, ?_, ?_, ?_, ?_, ?_⟩
      · exact hfC.trans (hS₃.mem ▸ hm₄ ▸ hfw.sub hsub'')
      · rw [hm₅, stateAt_writeState, show i + 2 = i + 1 + 1 by omega_arith, compressBlocks_succ _ _ _ (i + 1)]; rfl
      · have a₂ : Saved s₀ s₂ := saved_frame hp hM.saved (.inl (hm₂ ▸ Frame.refl _ _))
        obtain aC : Saved s₀ sC := saved_frame hp a₂ (.inr (.inr hspC))
        obtain a₃ : Saved s₀ s₃ := saved_frame hp aC (.inl (hS₃.mem ▸ Frame.refl _ _))
        exact saved_frame hp a₃ (.inr (.inl (hm₄ ▸ hfw)))
      · rw [Masks, hx₅, hy₅, hx₄, hy₄, hS₃.xmm, hS₃.ymmHi, hxC, hyC, hx₂, hy₂]; exact hM.masks
      · rw [hsy₅, hsy₄, hsy₃, hsyC, hsy₂]; exact hM.syms
    refine WP.mono (adv_common hp hc₄ 256 2) fun s₆ ⟨hc, he, hrsi, hrdx⟩ => ?_
    obtain hrdx' : s₅.gpr .rdx - BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 2)) := by
      rw [pub₅ .rdx (by decide), hrdx₄, hM.rdx, e2,
        show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    obtain hk : nxtI s₀ i = i + 2 := by simp only [nxtI, h, ↓reduceIte]
    unfold BodyPost; rw [hk]
    refine exit_or_next hp (by omega_arith) hc ?_ hrdx he
    rw [hrsi, hrsi₅, hM.rsi, e256]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, ← BitVec.ofNat_add,
      show 128 * (i + 2) = 128 * i + 256 by omega_arith]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.body s (BodyPost s₀ i) :=
  WP.seq (WP.mono (prefix_ok hp hi hL) fun _ hA => rest_ok hp hi hA)

/-! ## The prologue and the epilogue -/

theorem restore_eq : Impl.Sha512.X86_64.Avx2Rolled.restore = Spill.restoreCode .rcx Impl.Sha512.X86_64.Avx2Rolled.saved ++
    ([.vop .vzeroupper] : List Instr) := rfl

theorem saveMem_saved {s₀ : State} : Spill.Saved (saveMem s₀) (scr s₀) s₀.gpr Impl.Sha512.X86_64.Avx2Rolled.saved :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_bound p hp; omega_arith) (by decide)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) (hsy : s₁.syms = s₀.syms)
    (hk : Masks s₁) : Common s₀ 0 s₁ := by
  refine ⟨hg _ (by decide), hg _ (by decide), hg _ (by decide), hrd, hwr, ?_, ?_,
    by rw [Saved, hm]; exact saveMem_saved, hk, hsy⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 8 * k) (len := 64) (by omega_arith) (by omega_arith))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get _ _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block Impl.Sha512.X86_64.Avx2Rolled.restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  obtain hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  rw [restore_eq]
  refine Spill.restore_then .rcx Impl.Sha512.X86_64.Avx2Rolled.saved s₀.gpr (by decide) (fun p hp' => ?_)
    (by rw [hc.rcx]; exact hc.saved) ?_
  · have := saved_bound p hp'
    rw [hc.rcx, hc.rd, hc.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hm := (Spill.restoreState_mem s₀.gpr s Impl.Sha512.X86_64.Avx2Rolled.saved).1
  obtain hg := Spill.restoreState_gpr s₀.gpr s Impl.Sha512.X86_64.Avx2Rolled.saved
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq,
    exists_eq_left', isa]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [hg]
      simp [Impl.Sha512.X86_64.Avx2Rolled.saved, hc.rsp]
  · rw [hm]; exact hret
  · show stateAt _ _ = _; rw [hm]; exact hc.state

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  refine WP.seq (VG.X86_64.WP.mono_syms (prologue_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, _, hzf, hk⟩ hsy => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  obtain hc₀ := common_zero hp hg hrd hwr hm hsy hk
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    obtain hstep : ∀ m s, Inv m s → WP isa Impl.Sha512.X86_64.Avx2Rolled.body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨_, he, hc⟩ | ⟨hi', he, hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - nxtI s₀ i, by simp only [nxtI]; split <;> omega_arith, nxtI s₀ i, rfl, hi', hL'⟩
    obtain hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg _ (by decide)]; simp [blkAddr]
        rdx := by rw [hg _ (by decide)]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

end VG.Proof.Sha512.X86_64.Avx2.Rolled
