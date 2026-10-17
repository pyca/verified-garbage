module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Rounds
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Weave
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SHA-512 with AVX2 on x86-64, rolled: the compression function

`correct` proves `Impl.Sha512.X86_64.Avx2Rolled.compress` correct from `Pre`:
the precondition of the unrolled code (`Proof/Sha512/X86_64/Avx2/Compress.lean`),
with the table of round constants readable after the blocks, outside the
writable regions and the return address. The proof follows the unrolled
one: the loops of rounds run sixteen of them per iteration (`Rounds.lean`).
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
theorem base : Avx2.Pre (s₀.withRegions [blR s₀] s₀.wr) :=
  ⟨rfl, h.wr, h.st_scr, h.blk_st, h.blk_scr, h.ret_st, h.ret_scr⟩

/-- The precondition of the unrolled code, which is the same. -/
theorem avx2 : Avx2.Pre s₀ := ⟨h.rd, h.wr, h.st_scr, h.blk_st, h.blk_scr, h.ret_st, h.ret_scr⟩

theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := h.base.nb_lt

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem in_blk16 {i n : Nat} (hi : i < nb s₀) (hn : n < 8) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 := by
  obtain ⟨r, hr, hc⟩ := h.base.in_blk16 hi hn
  refine ⟨r, ?_, hc⟩
  simp only [State.withRegions_rd, State.withRegions_wr, List.mem_append, List.mem_singleton] at hr
  rcases hr with rfl | hr
  · simp [h.rd]
  · exact List.mem_append_right _ hr

end Pre

/-! ## The prologue -/

/-- The callee-saved registers are saved: `rbx, rbp, r12, r13` in the scratch
space, `r14` and `r15` in the low quadwords of `xmm14` and `xmm15`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  mem : Spill.Saved s.mem (scr s₀) s₀.gpr Impl.Sha512.X86_64.Avx2Rolled.saved
  x14 : (s.xmm .xmm14).extractLsb' 0 64 = s₀.gpr .r14
  x15 : (s.xmm .xmm15).extractLsb' 0 64 = s₀.gpr .r15

theorem saved_bound : ∀ p ∈ Impl.Sha512.X86_64.Avx2Rolled.saved, 1280 ≤ p.2 ∧ p.2 + 8 ≤ 1312 := by decide

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (scr s₀) s₀.gpr Impl.Sha512.X86_64.Avx2Rolled.saved

theorem save_eq : Impl.Sha512.X86_64.Avx2Rolled.save = Spill.saveCode .rcx Impl.Sha512.X86_64.Avx2Rolled.saved ++
    ([.vop (.vmovq .xmm14 .r14), .vop (.vmovq .xmm15 .r15)] : List Instr) := rfl

set_option simprocs false in
theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (Impl.Sha512.X86_64.Avx2Rolled.save ++ const mBswap bswapMask ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀
      fun s₁ =>
      (∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.syms = s₀.syms ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) ∧ Masks s₁ ∧
      (s₁.xmm .xmm14).extractLsb' 0 64 = s₀.gpr .r14 ∧ (s₁.xmm .xmm15).extractLsb' 0 64 = s₀.gpr .r15 := by
  simp only [save_eq, List.append_assoc]
  refine Spill.save_then .rcx Impl.Sha512.X86_64.Avx2Rolled.saved (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [const, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, VOp.exec, State.setV, State.lane,
    State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [Masks, mBswap, ite_true, ite_false, VBinOp.sse,
      movq_const, and_self]
  · exact BitVec.extractLsb'_append_eq_right
  · exact BitVec.extractLsb'_append_eq_right

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

/-- `Sched`, but for the index. -/
structure SchedR (M₀ M₁ : Block) (scr : Addr) (sB : State) (n : Nat) (s : State) : Prop where
  pub : ∀ r ∈ pubR, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  masks : Masks s
  frame : Frame [wRegion scr] sB.mem s.mem
  wmem : ∀ k < 40, k < n + 8 → WMem s.mem scr M₀ M₁ k
  msgs : ∀ k, n ≤ k → k < n + 8 → k < 40 → s.xmm (msg k) = pair M₀ k ∧ s.ymmHi (msg k) = pair M₁ k
  x14 : s.xmm .xmm14 = sB.xmm .xmm14
  x15 : s.xmm .xmm15 = sB.xmm .xmm15
  syms : s.syms = sB.syms

theorem SchedR.keeps {M₀ M₁ : Block} {scr : Addr} {sB : State} {n : Nat} {s s' : State}
    (h : SchedR M₀ M₁ scr sB n s) (hk : KeepsS s s') : SchedR M₀ M₁ scr sB n s' := by
  obtain ⟨⟨hm, hrd, hwr, hpub, hx, hy⟩, hsy⟩ := hk
  refine ⟨fun r hr => (hpub r (pubR_sub hr)).trans (h.pub r hr), hrd.trans h.rd, hwr.trans h.wr, ?_,
    hm ▸ h.frame, fun k hk hk' => hm ▸ h.wmem k hk hk', fun k h₁ h₂ h₃ => hx ▸ hy ▸ h.msgs k h₁ h₂ h₃,
    by rw [hx]; exact h.x14, by rw [hx]; exact h.x15, hsy.trans h.syms⟩
  rw [Masks, hx, hy]; exact h.masks

theorem msg_mod8 (j n : Nat) : msg (8 * j + n) = msg n := by
  simp only [msg]; rw [show (8 * j + n) % 8 = n % 8 by omega]

theorem x1415_ne (r : XReg) (h : r = .xmm14 ∨ r = .xmm15) (n : Nat) :
    r ≠ msg n ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ t3 ∧ r ≠ tmp ∧ r ≠ mBswap := by
  have key : ∀ c < 8, ∀ r ∈ [XReg.xmm14, .xmm15],
      r ≠ msg c ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ t3 ∧ r ≠ tmp ∧ r ≠ mBswap := by decide
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

/-- The schedule step `n + 8` of iteration `j`: words `2N+16, 2N+17`, `N = 8 j + n`. -/
theorem schedR_step {M₀ M₁ : Block} {scr : Addr} {sB : State} (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) {j n : Nat} (hn : n < 8) (hN : 8 * j + n < 32) {s : State}
    (hI : s.gpr .rdx = idx j) (h : SchedR M₀ M₁ scr sB (8 * j + n) s) :
    WP isa (.block (scheduleR (n + 8))) s fun s' =>
      SchedR M₀ M₁ scr sB (8 * j + n + 1) s' ∧ s'.gpr = s.gpr := by
  have hrcx' : s.gpr .rcx = scr := (h.pub .rcx (by decide)).trans hrcx
  have m : ∀ q < 8, s.xmm (msg (n + 8 + q)) = pair M₀ (8 * j + n + q) ∧
      s.ymmHi (msg (n + 8 + q)) = pair M₁ (8 * j + n + q) := fun q hq => by
    rw [show n + 8 + q = 8 * j + n + q + 8 - 8 * j by omega, ← msg_mod8 j, show 8 * j + (8 * j + n + q + 8 - 8 * j)
      = 8 * j + n + q + 8 by omega, msg_add8]
    exact h.msgs (8 * j + n + q) (by omega) (by omega) (by omega)
  obtain ⟨ma, ma'⟩ := m 0 (by omega)
  obtain ⟨mb, mb'⟩ := m 1 (by omega)
  obtain ⟨mc, mc'⟩ := m 4 (by omega)
  obtain ⟨md, md'⟩ := m 5 (by omega)
  obtain ⟨me, me'⟩ := m 7 (by omega)
  simp only [Nat.add_zero] at ma ma'
  have ea := sSlot_ea s hI (n + 8)
  rw [hrcx', show 8 * j + (n + 8) = 8 * j + n + 8 by omega] at ea
  refine VG.X86_64.WP.mono_syms (scheduleR_ok (n + 8) s _ _ _ _ _ _ _ _ _ _ ma mb mc md me ma' mb' mc' md' me'
    (by rw [ea, h.wr]; exact in_scr hR (by omega)))
    fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ hsy => ⟨?_, hg⟩
  rw [xupd_pair] at ex ey
  rw [xupd_pair, xupd_pair, ea] at hm
  have hmsg : msg (n + 8) = msg (8 * j + n + 8) := by
    rw [show 8 * j + n + 8 = 8 * j + (n + 8) by omega, msg_mod8]
  rw [hmsg] at ex ey hx
  have o14 := x1415_ne .xmm14 (.inl rfl) (8 * j + n + 8)
  have o15 := x1415_ne .xmm15 (.inr rfl) (8 * j + n + 8)
  refine ⟨fun r hr => by rw [hg]; exact h.pub r hr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_,
    by rw [(hx _ o14.1 o14.2.1 o14.2.2.1 o14.2.2.2.1 o14.2.2.2.2.1).1]; exact h.x14,
    by rw [(hx _ o15.1 o15.2.1 o15.2.2.1 o15.2.2.2.1 o15.2.2.2.2.1).1]; exact h.x15, hsy.trans h.syms⟩
  · have o := hx mBswap (sched_other (8 * j + n + 8) mBswap (.inl rfl)).1
      (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.1
      (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.2.1 (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.2.2.1
      (sched_other (8 * j + n + 8) mBswap (.inl rfl)).2.2.2.2
    have masks := h.masks
    rw [Masks, o.1, o.2]
    exact masks
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (wAddr_contains scr (by omega))
  · intro k hk hk'
    rw [hm]
    by_cases hkn : k = 8 * j + n + 8
    · subst hkn; exact wmem_self _ _ _ _ _
    · exact wmem_write hk (by omega) hkn _ (h.wmem k hk (by omega))
  · intro k h₁ h₂ h₃
    by_cases hkn : k = 8 * j + n + 8
    · subst hkn; exact ⟨ex, ey⟩
    · have o := msg_ne (8 * j + n + 8) (k + 8) (by omega) (by omega)
      rw [msg_add8] at o
      rw [(hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).1, (hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).2]
      exact h.msgs k (by omega) (by omega) h₃

/-! ## The rounds of the first block -/

/-- The table can be read in `s`: its statics are those of `sB`. -/
theorem kok_of {kb : Addr} {sB s : State} (hk : ∀ t < 80, KOk kb sB t) (hs : s.syms = sB.syms) :
    ∀ t < 80, KOk kb s t := fun t ht => (hk t ht).of_syms hs

/-- After `n` groups of iteration `j`. -/
def GInvR (H : HashValue) (M₀ M₁ : Block) (scr : Addr) (sB : State) (j n : Nat) (s : State) : Prop :=
  Vars (2 * n) s (Spec.Sha512.rounds H M₀ (16 * j + 2 * n)) ∧ SchedR M₀ M₁ scr sB (8 * j + n) s ∧
    s.gpr .rdx = idx j

theorem groupsR_ok (H : HashValue) (M₀ M₁ : Block) (scr kb : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) (hkb : sB.gpr .rsi = kb) (hk : ∀ t < 80, KOk kb sB t)
    {j : Nat} (hj : j < 4) {s₀ : State} (h₀ : GInvR H M₀ M₁ scr sB j 0 s₀) :
    ∀ n ≤ 8, WP isa (groupsR n) s₀ (GInvR H M₀ M₁ scr sB j n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h₀
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s ⟨hv, hs, hI⟩ => ?_)
    refine VG.Interleave.WP.weave (group_indeps (by omega)) trivial ?_
    refine WP.mono (schedR_step hrcx hR (by omega) (by omega) hI hs) fun s₁ ⟨hs₁, hg₁⟩ => ?_
    have hv₁ : Vars (2 * n) s₁ (Spec.Sha512.rounds H M₀ (16 * j + 2 * n)) := by
      simp only [Vars, hg₁]; exact hv
    have hI₁ : Idx kb j s₁ := ⟨by rw [hg₁]; exact hI, by rw [hs₁.pub .rsi (by decide)]; exact hkb⟩
    have hrcx₁ : s₁.gpr .rcx = scr := (hs₁.pub .rcx (by decide)).trans hrcx
    have hR₁ : (⟨scr, 1328⟩ : Region) ∈ s₁.wr := hs₁.wr ▸ hR
    have hk₁ := kok_of hk hs₁.syms
    have hw : ∀ q < 2, WOk 0 M₀ s₁ (16 * j + 2 * n + q) := fun q hq =>
      (wok_of_wmem (by omega) hrcx₁ hR₁ (by
        rw [show (16 * j + 2 * n + q) / 2 = 8 * j + n by omega]
        exact hs₁.wmem _ (by omega) (by omega))).1
    rw [WP.block_append_iff]
    refine WP.mono (roundR_step 0 j (2 * n) H M₀ s₁ hI₁ hv₁ (hk₁ _ (by omega))
      (by simpa using hw 0 (by omega))) fun s₂ ⟨hv₂, hk₂⟩ => ?_
    have hv₂' : Vars (2 * n + 1) s₂ (Spec.Sha512.rounds H M₀ (16 * j + (2 * n + 1))) := by
      rw [show 16 * j + (2 * n + 1) = 16 * j + 2 * n + 1 by omega]; exact hv₂
    have hw₂ : WOk 0 M₀ s₂ (16 * j + (2 * n + 1)) := by
      rw [show 16 * j + (2 * n + 1) = 16 * j + 2 * n + 1 by omega]; exact (hw 1 (by omega)).keeps hk₂.1
    refine WP.mono (roundR_step 0 j (2 * n + 1) H M₀ s₂ (hI₁.keeps hk₂) hv₂'
      ((hk₁ _ (by omega)).keeps hk₂) hw₂) fun s₃ ⟨hv₃, hk₃⟩ => ?_
    refine ⟨?_, (hs₁.keeps hk₂).keeps hk₃, ?_⟩
    · rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      exact hv₃
    · rw [hk₃.1.2.2.2.1 .rdx (by decide), hk₂.1.2.2.2.1 .rdx (by decide)]; exact hI₁.rdx

/-- What `step` leaves of `SchedR`: everything but `rdx` and the flags. -/
theorem SchedR.of_eq {M₀ M₁ : Block} {scr : Addr} {sB : State} {n : Nat} {s s' : State}
    (h : SchedR M₀ M₁ scr sB n s) (hg : ∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hsy : s'.syms = s.syms) :
    SchedR M₀ M₁ scr sB n s' := by
  refine ⟨fun r hr => (hg r ?_).trans (h.pub r hr), hrd.trans h.rd, hwr.trans h.wr, ?_,
    hm ▸ h.frame, fun k hk hk' => hm ▸ h.wmem k hk hk', fun k h₁ h₂ h₃ => hx ▸ hy ▸ h.msgs k h₁ h₂ h₃,
    by rw [hx]; exact h.x14, by rw [hx]; exact h.x15, hsy.trans h.syms⟩
  · simp only [pubR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [Masks, hx, hy]; exact h.masks

theorem vars16 {s : State} {v : HashValue} : Vars 16 s v ↔ Vars 0 s v := vars_add16 1 0 s v

theorem step512 : step 512 = step (512 : BitVec 32).toNat := rfl
theorem step640 : step 640 = step (640 : BitVec 32).toNat := rfl

/-- The first block's loop: rounds 0–63, and the schedule of both blocks. -/
theorem loop1_ok (H : HashValue) (M₀ M₁ : Block) (scr kb : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) (hkb : sB.gpr .rsi = kb) (hk : ∀ t < 80, KOk kb sB t)
    (h₀ : GInvR H M₀ M₁ scr sB 0 0 sB) :
    WP isa (.loop (.seq (groupsR 8) (.block (step 512))) .ne) sB (GInvR H M₀ M₁ scr sB 4 0) := by
  let Inv : Nat → State → Prop := fun m s => ∃ j, m = 4 - j ∧ j < 4 ∧ GInvR H M₀ M₁ scr sB j 0 s
  have hstep : ∀ m s, Inv m s → WP isa (.seq (groupsR 8) (.block (step 512))) s (fun s' =>
      (eval .ne s' = some false ∧ GInvR H M₀ M₁ scr sB 4 0 s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨j, rfl, hj, hG⟩
    refine WP.seq (WP.mono (groupsR_ok H M₀ M₁ scr kb sB hrcx hR hkb hk hj hG 8 (Nat.le_refl _))
      fun s₁ ⟨hv₁, hs₁, hI₁⟩ => ?_)
    rw [step512]
    refine VG.X86_64.WP.mono_syms (step_ok 512 s₁) fun s₂ ⟨he, hrdx, hg, hm, hrd, hwr, hx, hy⟩ hsy => ?_
    have hG₂ : GInvR H M₀ M₁ scr sB (j + 1) 0 s₂ := by
      refine ⟨?_, ?_, by rw [hrdx, hI₁, idx_succ]⟩
      · rw [show 16 * (j + 1) + 2 * 0 = 16 * j + 2 * 8 by omega]
        simp only [Vars] at hv₁ ⊢
        have hv₁' := vars16.mp hv₁
        simp only [Vars] at hv₁'
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₁'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hg _ (by decide)]; assumption
      · rw [show 8 * (j + 1) + 0 = 8 * j + 8 by omega]
        exact hs₁.of_eq hg hm hrd hwr hx hy hsy
    rw [hI₁, show (512 : BitVec 32).toNat = 128 * 4 from rfl, step_idx hj (by decide)] at he
    by_cases hlast : j + 1 = 4
    · left
      have hb : (j + 1 == 4) = true := beq_iff_eq.mpr hlast
      refine ⟨by rw [he, hb]; rfl, ?_⟩
      rw [← hlast]; exact hG₂
    · right
      have hb : (j + 1 == 4) = false := beq_eq_false_iff_ne.mpr hlast
      refine ⟨by rw [he, hb]; rfl, 4 - (j + 1), by omega, j + 1, rfl, by omega, hG₂⟩
  exact WP.loop (M := isa) Inv hstep 4 sB ⟨0, rfl, by decide, h₀⟩

theorem vars8_of16 {s : State} {v : HashValue} (h : Vars 16 s v) : Vars8 s v :=
  Vars.vars8 (by exact h)

/-- Rounds 64–79 of the first block. -/
theorem tail_ok (H : HashValue) (M₀ M₁ : Block) (scr kb : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sB.wr) (hkb : sB.gpr .rsi = kb) (hk : ∀ t < 80, KOk kb sB t)
    {s : State} (h : GInvR H M₀ M₁ scr sB 4 0 s) :
    WP isa (rounds16 0) s fun s' =>
      Vars8 s' (Spec.Sha512.rounds H M₀ 80) ∧ SchedR M₀ M₁ scr sB 32 s' ∧ s'.gpr .rdx = idx 4 := by
  obtain ⟨hv, hs, hI⟩ := h
  have hrcx' : s.gpr .rcx = scr := (hs.pub .rcx (by decide)).trans hrcx
  have hR' : (⟨scr, 1328⟩ : Region) ∈ s.wr := hs.wr ▸ hR
  have hk' := kok_of hk hs.syms
  refine WP.mono (roundsR_ok 0 4 H M₀ (P := fun _ => True) (p := .block [])
    (WP.block_nil ⟨trivial, hv, Keeps.refl s⟩) ⟨hI, by rw [hs.pub .rsi (by decide)]; exact hkb⟩
    (fun t ht => hk' _ (by omega))
    (fun t ht => (wok_of_wmem (by omega) hrcx' hR' (hs.wmem _ (by omega) (by omega))).1) 16 (Nat.le_refl _))
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

theorem WOk.of_same {j : Nat} {M : Block} {sC s : State} {t : Nat} (h : WOk j M sC t) (hs : Same sC s) :
    WOk j M s t := by
  have e : s.ea (wSlot j t) = sC.ea (wSlot j t) := by
    simp only [State.ea, wSlot, at_, hs.pub .rcx (by decide)]
  rw [WOk, e, hs.mem, hs.rd, hs.wr]; exact h

theorem KOk.of_same {kb : Addr} {sC s : State} {t : Nat} (h : KOk kb sC t) (hs : Same sC s) : KOk kb s t :=
  h.of_syms hs.syms

theorem Same.keeps {sC s s' : State} (h : Same sC s) (hk : KeepsS s s') : Same sC s' :=
  ⟨hk.1.1.trans h.mem, hk.1.2.1.trans h.rd, hk.1.2.2.1.trans h.wr,
    fun r hr => (hk.1.2.2.2.1 r (pubR_sub hr)).trans (h.pub r hr), hk.1.2.2.2.2.1.trans h.xmm,
    hk.1.2.2.2.2.2.trans h.ymmHi, hk.2.trans h.syms⟩

/-- The second block's loop: its 80 rounds. -/
theorem loop2_ok (H : HashValue) (M : Block) (kb : Addr) (sC : State) (hkb : sC.gpr .rsi = kb)
    (hk : ∀ t < 80, KOk kb sC t) (hw : ∀ t < 80, WOk 1 M sC t) (hv : Vars 0 sC H) (hI : sC.gpr .rdx = idx 0) :
    WP isa (.loop (.seq (rounds16 1) (.block (step 640))) .ne) sC fun s =>
      Vars8 s (Spec.Sha512.rounds H M 80) ∧ Same sC s := by
  let Inv : Nat → State → Prop := fun m s => ∃ j, m = 5 - j ∧ j < 5 ∧
    Vars 0 s (Spec.Sha512.rounds H M (16 * j)) ∧ s.gpr .rdx = idx j ∧ Same sC s
  have hstep : ∀ m s, Inv m s → WP isa (.seq (rounds16 1) (.block (step 640))) s (fun s' =>
      (eval .ne s' = some false ∧ Vars8 s' (Spec.Sha512.rounds H M 80) ∧ Same sC s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨j, rfl, hj, hv₀, hI₀, hS⟩
    refine WP.seq (WP.mono (roundsR_ok 1 j H M (P := fun _ => True) (p := .block [])
      (WP.block_nil ⟨trivial, hv₀, Keeps.refl s⟩) ⟨hI₀, by rw [hS.pub .rsi (by decide)]; exact hkb⟩
      (fun t ht => KOk.of_same (hk (16 * j + t) (by omega)) hS)
      (fun t ht => WOk.of_same (hw (16 * j + t) (by omega)) hS) 16 (Nat.le_refl _))
      fun s₁ ⟨_, hv₁, hk₁⟩ => ?_)
    rw [step640]
    refine VG.X86_64.WP.mono_syms (step_ok 640 s₁) fun s₂ ⟨he, hrdx, hg, hm, hrd, hwr, hx, hy⟩ hsy => ?_
    have hI₁ : s₁.gpr .rdx = idx j := (hk₁.1.2.2.2.1 .rdx (by decide)).trans hI₀
    have hS₂ : Same sC s₂ := by
      have hS₁ := hS.keeps hk₁
      refine ⟨hm.trans hS₁.mem, hrd.trans hS₁.rd, hwr.trans hS₁.wr, fun r hr => (hg r ?_).trans (hS₁.pub r hr),
        hx.trans hS₁.xmm, hy.trans hS₁.ymmHi, hsy.trans hS₁.syms⟩
      simp only [pubR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have hv₂ : Vars 16 s₂ (Spec.Sha512.rounds H M (16 * j + 16)) := by
      simp only [Vars] at hv₁ ⊢
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₁
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hg _ (by decide)]; assumption
    rw [hI₁, show (640 : BitVec 32).toNat = 128 * 5 from rfl, step_idx hj (by decide)] at he
    by_cases hlast : j + 1 = 5
    · left
      have hb : (j + 1 == 5) = true := beq_iff_eq.mpr hlast
      refine ⟨by rw [he, hb]; rfl, ?_, hS₂⟩
      rw [show 80 = 16 * j + 16 by omega]; exact vars8_of16 hv₂
    · right
      have hb : (j + 1 == 5) = false := beq_eq_false_iff_ne.mpr hlast
      refine ⟨by rw [he, hb]; rfl, 5 - (j + 1), by omega, j + 1, rfl, by omega, ?_,
        by rw [hrdx, hI₁, idx_succ], hS₂⟩
      rw [show 16 * (j + 1) = 16 * j + 16 by omega]; exact vars16.mp hv₂
  exact WP.loop (M := isa) Inv hstep 5 sC ⟨0, rfl, by decide, hv, hI,
    ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩⟩

/-! ## Loading the blocks, keeping `xmm14` and `xmm15` -/

/-- `LdInv`, and `xmm14` and `xmm15` are kept. -/
structure LdInvR (M₀ M₁ : Block) (scr : Addr) (sL : State) (n : Nat) (s : State) : Prop
    extends LdInv M₀ M₁ scr sL n s where
  x14 : s.xmm .xmm14 = sL.xmm .xmm14
  x15 : s.xmm .xmm15 = sL.xmm .xmm15

theorem load_stepR {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sL : State}
    (hrsi : sL.gpr .rsi = p₀) (hr15 : sL.gpr .r15 = p₁) (hrcx : sL.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sL.wr)
    (hin : ∀ n : Nat, n < 8 → InRegions (sL.rd ++ sL.wr) (p₀ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (sL.rd ++ sL.wr) (p₁ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ m, Frame [wRegion scr] sL.mem m →
      (∀ t : Nat, t < 16 → bswap64 (m.readW (p₀ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₀ t) ∧
      (∀ t : Nat, t < 16 → bswap64 (m.readW (p₁ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₁ t))
    {n : Nat} (hn : n < 8) {s : State} (h : LdInvR M₀ M₁ scr sL n s) :
    WP isa (.block (load n)) s (LdInvR M₀ M₁ scr sL (n + 1)) := by
  obtain ⟨k1, k2⟩ := h.masks
  have hb := hblk _ h.frame
  have o14 := x1415_ne .xmm14 (.inl rfl) n
  have o15 := x1415_ne .xmm15 (.inr rfl) n
  refine WP.mono (WP.and (load_step hrsi hr15 hrcx hR hin hblk hn h.toLdInv) (WP.mono (load_ok (p₀ := p₀) (p₁ := p₁)
    (scr := scr) (M₀ := M₀) (M₁ := M₁) hn s
    (by rw [h.gpr]; exact hrsi) (by rw [h.gpr]; exact hr15)
    (by rw [h.gpr]; exact hrcx) (by rw [h.rd, h.wr]; exact (hin n hn).1) (by rw [h.rd, h.wr]; exact (hin n hn).2)
    (by rw [h.wr]; exact in_scr hR (by omega)) k1 k2 hb.1 hb.2) fun s' ⟨_, _, hx, _⟩ =>
    And.intro ((hx _ o14.1 o14.2.2.2.2.2.1).1.trans h.x14) ((hx _ o15.1 o15.2.2.2.2.2.1).1.trans h.x15)))
    fun s' h' => ⟨h'.1, h'.2.1, h'.2.2⟩

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

theorem sp_sub (p : Addr) : Region.Sub (spR p) ⟨p, 1328⟩ := Offset.sub_base _ (by omega)

theorem w_sp (p : Addr) : Region.Disjoint (wRegion p) (spR p) := Offset.base_disjoint _ (by omega) (by omega)

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
  wmem : ∀ k < 40, WMem s.mem (scr s₀) (blk s₀ i) (blk s₀ (nxt s₀ i)) k
  e : eval .e s = some (nb s₀ - i == 1)

theorem saved_frame {s₀ : State} (hp : Pre s₀) {s s' : State} (h : Saved s₀ s)
    (hf : Frame [wRegion (scr s₀)] s.mem s'.mem ∨ Frame [stR s₀] s.mem s'.mem ∨ Frame [spR (scr s₀)] s.mem s'.mem)
    (hx : s'.xmm .xmm14 = s.xmm .xmm14) (hy : s'.xmm .xmm15 = s.xmm .xmm15) : Saved s₀ s' := by
  refine ⟨?_, by rw [hx]; exact h.x14, by rw [hy]; exact h.x15⟩
  rcases hf with hf | hf | hf <;> refine Spill.Saved.frame h.mem hf fun p hp' r hr => ?_ <;>
    rw [List.mem_singleton.mp hr] <;> have := saved_bound p hp'
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega))
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The table, in any state naming the statics `s₀` names. -/
theorem kok_of_syms {s₀ s : State} (hs : s.syms = s₀.syms) : ∀ t < 80, KOk (kb s₀) s t :=
  fun t ht => ⟨by rw [hs], ht⟩

theorem spill_read (p : Addr) (m : Mem) (a b : BitVec 64) :
    ((m.writeW (spA p) a).writeW (spB p) b).readW (spA p) 64 = a ∧
      ((m.writeW (spA p) a).writeW (spB p) b).readW (spB p) 64 = b :=
  ⟨(Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)).trans
    (Mem.readW_writeW_self m _ 8 a (by decide)), Mem.readW_writeW_self _ _ 8 b (by decide)⟩

theorem spA_in (p : Addr) : (spR p).Contains (spA p) 8 :=
  Offset.contains (e := 1312) (d := 1312) (n := 8) (k := 16) p (by omega) (by omega) (by omega)

theorem spB_in (p : Addr) : (spR p).Contains (spB p) 8 :=
  Offset.contains (e := 1312) (d := 1320) (n := 8) (k := 16) p (by omega) (by omega) (by omega)

theorem spill_frame (p : Addr) (m : Mem) (a b : BitVec 64) :
    Frame [spR p] m ((m.writeW (spA p) a).writeW (spB p) b) := by
  refine ((Frame.refl _ m).writeW (List.mem_singleton_self _) a ?_).writeW (List.mem_singleton_self _) b ?_
  · exact spA_in p
  · exact spB_in p

theorem wmem_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} {M₀ M₁ : Block} {k : Nat} (hk : k < 40)
    (h : WMem m (scr s₀) M₀ M₁ k) (hf : Frame [stR s₀] m m' ∨ Frame [spR (scr s₀)] m m') :
    WMem m' (scr s₀) M₀ M₁ k := by
  simp only [WMem] at h ⊢
  rw [← h]
  have hs := slot_sub (scr s₀) (d := 32 * k) (n := 32) (by omega)
  rcases hf with hf | hf
  · exact hf.readW (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]; exact Region.Disjoint.sub_left hp.st_scr.symm hs) (by decide)
  · refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    show Region.Disjoint ⟨scr s₀ + BitVec.ofInt 64 ((32 * k : Nat) : Int), 32⟩ ⟨scr s₀ + BitVec.ofNat 64 1312, 16⟩
    rw [ofInt_natCast]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem state_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem}
    (hf : Frame [wRegion (scr s₀)] m m' ∨ Frame [spR (scr s₀)] m m') :
    stateAt m' (st s₀) = stateAt m (st s₀) := by
  rcases hf with hf | hf
  · exact state_frame_w hp.base hf
  · apply stateAt_eq
    intro k hk
    rw [hf.readW (contains_offset' (off := 8 * k) (len := 64) (by omega) (by omega))
      (by simpa using Region.Disjoint.sub_right hp.st_scr (sp_sub _)) (by decide), ← stateAt_get _ _ hk]

theorem spill_keep {s₀ : State} {m m' : Mem} (hf : Frame [wRegion (scr s₀)] m m') :
    m'.readW (spA (scr s₀)) 64 = m.readW (spA (scr s₀)) 64 ∧ m'.readW (spB (scr s₀)) 64 = m.readW (spB (scr s₀)) 64 :=
  ⟨hf.readW (spA_in _) (by simpa using (w_sp _).symm) (by decide),
    hf.readW (spB_in _) (by simpa using (w_sp _).symm) (by decide)⟩

theorem sp_in {s₀ : State} (hp : Pre s₀) {s : State} (hrcx : s.gpr .rcx = scr s₀) (hwr : s.wr = s₀.wr) :
    InRegions s.wr (spA (s.gpr .rcx)) 8 ∧ InRegions s.wr (spB (s.gpr .rcx)) 8 := by
  rw [hrcx, hwr]
  exact ⟨⟨scrR s₀, by simp [hp.wr], Offset.contains_base (d := 1312) (n := 8) (k := 1328) _ (by omega) (by omega)⟩,
    ⟨scrR s₀, by simp [hp.wr], Offset.contains_base (d := 1320) (n := 8) (k := 1328) _ (by omega) (by omega)⟩⟩

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
  wmem : ∀ k < 40, WMem s.mem (scr s₀) (blk s₀ i) (blk s₀ (nxt s₀ i)) k
  syms : s.syms = s₀.syms

/-- The first block of an iteration, up to getting back `rsi` and `rdx`. -/
theorem prefix_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.first s (AtLeave s₀ i) := by
  have := hp.nb_lt
  have hscr : (⟨scr s₀, 1328⟩ : Region) ∈ s₀.wr := by simp [hp.wr]
  have hj : nxt s₀ i < nb s₀ := by simp only [nxt]; split <;> omega
  have hb : (s.gpr .rdx - 1 == 0) = (nb s₀ - i == 1) := by rw [hL.rdx]; exact sub_one_eq hp.base hi
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
      show 128 * (i + 1) = 128 * i + 128 by omega]
  obtain ⟨hm₂, hrd₂, hwr₂, -, hx₂, hy₂⟩ := hk₂
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => hg₂ r (pub_ne15 hr)
  have hrsi₂ : s₂.gpr .rsi = blkAddr s₀ i := (pub₂ .rsi (by decide)).trans hL.rsi
  have hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hL.rcx
  have hrdi₂ : s₂.gpr .rdi = st s₀ := (pub₂ .rdi (by decide)).trans hL.rdi
  have hR₂ : (⟨scr s₀, 1328⟩ : Region) ∈ s₂.wr := by rw [hwr₂, hL.wr]; exact hscr
  have hf₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem := hm₂ ▸ hL.frame
  have hin : ∀ n : Nat, n < 8 →
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ (nxt s₀ i) + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 :=
    fun n hn => by rw [hrd₂, hwr₂, hL.rd, hL.wr]; exact ⟨hp.in_blk16 hi hn, hp.in_blk16 hj hn⟩
  have hblk := fun m (hm : Frame [wRegion (scr s₀)] s₂.mem m) =>
    And.intro (blk_read hp.base hi hf₂ hm) (blk_read hp.base hj hf₂ hm)
  have step := fun {n : Nat} (hn : n < 8) {x : State}
      (h : LdInvR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ n x) =>
    load_stepR hrsi₂ h15₂ hrcx₂ hR₂ hin hblk hn h
  have h₀ : LdInvR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ 0 s₂ :=
    ⟨⟨rfl, rfl, rfl, by rw [Masks, hx₂, hy₂]; exact hL.masks, Frame.refl _ _, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩, rfl, rfl⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine VG.X86_64.WP.mono_syms (Q := fun s₅ => ∃ s₃, LdInvR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ 8 s₃ ∧
    Vars 0 s₅ (stateAt s₃.mem (st s₀)) ∧ Keeps s₃ s₅) ?_ fun s₅ ⟨s₃, ld, hv₅, hk₃₅⟩ hsy₅ => ?_
  · rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
      WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
      WP.block_append_iff]
    refine WP.mono (step (by omega) h₀) fun x₁ h₁ => ?_
    refine WP.mono (step (by omega) h₁) fun x₂ h₂ => ?_
    refine WP.mono (step (by omega) h₂) fun x₃ h₃ => ?_
    refine WP.mono (step (by omega) h₃) fun x₄ h₄ => ?_
    refine WP.mono (step (by omega) h₄) fun x₅ h₅ => ?_
    refine WP.mono (step (by omega) h₅) fun x₆ h₆ => ?_
    refine WP.mono (step (by omega) h₆) fun x₇ h₇ => ?_
    refine WP.mono (step (by omega) h₇) fun s₃ ld => ?_
    refine WP.mono (loadState_ok hp (by rw [ld.gpr]; exact hrdi₂) (by rw [ld.rd, hrd₂, hL.rd])
      (by rw [ld.wr, hwr₂, hL.wr])) fun s₄ ⟨hv₄, hk₄⟩ => ?_
    exact WP.mono (initCarry_ok hv₄) fun s₅ ⟨hv₅, hk₅⟩ => ⟨s₃, ld, hv₅, hk₄.trans hk₅⟩
  obtain ⟨hm₅, hrd₅, hwr₅, pub₅, hx₅, hy₅⟩ := hk₃₅
  have hrcx₅ : s₅.gpr .rcx = scr s₀ := by rw [pub₅ .rcx (by decide), ld.gpr]; exact hrcx₂
  have hwr₅' : s₅.wr = s₀.wr := by rw [hwr₅, ld.wr, hwr₂, hL.wr]
  have hrd₅' : s₅.rd = s₀.rd := by rw [hrd₅, ld.rd, hrd₂, hL.rd]
  have hsy : s₅.syms = s₀.syms := by rw [hsy₅, hsy₂, hsy₁]; exact hL.syms
  obtain ⟨spa, spb⟩ := sp_in hp hrcx₅ hwr₅'
  refine VG.X86_64.WP.mono_syms (enter_ok s₅ spa spb) fun sB ⟨hrdiB, hrdxB, hgB, hmB, hrdB, hwrB, hxB, hyB⟩ hsyB => ?_
  rw [hsy] at hrdiB
  have hspB : Frame [spR (scr s₀)] s₅.mem sB.mem := by rw [hmB, hrcx₅]; exact spill_frame _ _ _ _
  have hrcxB : sB.gpr .rcx = scr s₀ := by rw [hgB _ (by decide) (by decide)]; exact hrcx₅
  have hRB : (⟨scr s₀, 1328⟩ : Region) ∈ sB.wr := by rw [hwrB, hwr₅']; exact hscr
  have hfB : Frame [stR s₀, scrR s₀] s₀.mem sB.mem := by
    have hsub : ∀ r ∈ [wRegion (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
      fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact wsub _⟩
    have hsub' : ∀ r ∈ [spR (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
      fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact sp_sub _⟩
    exact hf₂.trans ((ld.frame.sub hsub).trans (hm₅ ▸ hspB.sub hsub'))
  have hkB := kok_of_syms (s₀ := s₀) (s := sB) (by rw [hsyB, hsy])
  have hvB : Vars 0 sB (Spec.Sha512.rounds (stateAt s₃.mem (st s₀)) (blk s₀ i) (16 * 0 + 2 * 0)) := by
    simp only [Vars] at hv₅ ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₅
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hgB _ (by decide) (by decide)]; assumption
  have hSB : SchedR (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) sB (8 * 0 + 0) sB :=
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Masks, hxB, hyB, hx₅, hy₅]; exact ld.masks, Frame.refl _ _,
      fun k hk hk' => wmem_frame hp hk (by rw [hm₅]; exact ld.wmem k (by omega)) (.inr hspB),
      fun k _ hk _ => by rw [hxB, hyB, hx₅, hy₅]; exact ld.msgs k (by omega), rfl, rfl, rfl⟩
  refine WP.seq (VG.X86_64.WP.mono_syms (loop1_ok _ _ _ (scr s₀) (kb s₀) sB hrcxB hRB hrdiB hkB
    ⟨hvB, hSB, hrdxB⟩) fun s₆ h₆ hsy₆ => ?_)
  refine WP.seq (VG.X86_64.WP.mono_syms (tail_ok _ _ _ (scr s₀) (kb s₀) sB hrcxB hRB hrdiB hkB h₆)
    fun s₇ ⟨hv₇, hS₇, hrdx₇⟩ hsy₇ => ?_)
  have hrcx₇ : s₇.gpr .rcx = scr s₀ := (hS₇.pub .rcx (by decide)).trans hrcxB
  have hwr₇ : s₇.wr = s₀.wr := by rw [hS₇.wr, hwrB, hwr₅']
  have hrd₇ : s₇.rd = s₀.rd := by rw [hS₇.rd, hrdB, hrd₅']
  obtain ⟨spa', spb'⟩ := sp_in' hp hrcx₇ hwr₇
  refine VG.X86_64.WP.mono_syms (leave_ok s₇ spa' spb')
    fun s₈ ⟨hrdi₈, hrdx₈, hg₈, hm₈, hrd₈, hwr₈, hx₈, hy₈⟩ hsy₈ => ?_
  have sk := spill_keep (s₀ := s₀) hS₇.frame
  have sr := spill_read (scr s₀) s₅.mem (s₅.gpr .rsi) (s₅.gpr .rdx)
  rw [← hrcx₅, ← hmB] at sr
  rw [hrcx₇, sk.1, ← hrcx₅, sr.1, pub₅ .rsi (by decide), ld.gpr, hrsi₂] at hrdi₈
  rw [hrcx₇, sk.2, ← hrcx₅, sr.2, pub₅ .rdx (by decide), ld.gpr, pub₂ .rdx (by decide)] at hrdx₈
  have hHi : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i := by
    rw [state_frame hp (.inl ld.frame), hm₂]; exact hL.state
  have hst₈ : stateAt s₈.mem (st s₀) = stateAt s₃.mem (st s₀) := by
    rw [hm₈, state_frame hp (.inl hS₇.frame), state_frame hp (.inr hspB), hm₅]
  have g₇ : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsp → s₈.gpr r = s.gpr r := fun r hr => by
    have h1 : r ∈ pubR := by rcases hr with rfl | rfl | rfl <;> decide
    have h2 : r ∈ pubRegs := pubR_sub h1
    have h3 : r ≠ .rsi := by rcases hr with rfl | rfl | rfl <;> decide
    have h4 : r ≠ .rdx := by rcases hr with rfl | rfl | rfl <;> decide
    rw [hg₈ r h3 h4, hS₇.pub r h1, hgB r h3 h4, pub₅ r h2, ld.gpr, pub₂ r h2]
  have hsub : ∀ r ∈ [wRegion (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact wsub _⟩
  have a₂ : Saved s₀ s₂ := saved_frame hp hL.saved (.inl (hm₂ ▸ Frame.refl _ _)) (by rw [hx₂]) (by rw [hx₂])
  have a₃ : Saved s₀ s₃ := saved_frame hp a₂ (.inl ld.frame) ld.x14 ld.x15
  have a₅ : Saved s₀ s₅ := saved_frame hp a₃ (.inl (hm₅ ▸ Frame.refl _ _)) (by rw [hx₅]) (by rw [hx₅])
  have aB : Saved s₀ sB := saved_frame hp a₅ (.inr (.inr hspB)) (by rw [hxB]) (by rw [hxB])
  have a₇ : Saved s₀ s₇ := saved_frame hp aB (.inl hS₇.frame) hS₇.x14 hS₇.x15
  refine ⟨by rw [g₇ .rdi (by simp)]; exact hL.rdi, hrdx₈.trans hL.rdx, by rw [g₇ .rcx (by simp)]; exact hL.rcx,
    hrdi₈, by rw [g₇ .rsp (by simp)]; exact hL.rsp,
    by rw [hrd₈]; exact hrd₇, by rw [hwr₈]; exact hwr₇, ?_, hst₈.trans hHi, ?_,
    saved_frame hp a₇ (.inl (hm₈ ▸ Frame.refl _ _)) (by rw [hx₈]) (by rw [hx₈]), ?_, ?_, ?_⟩
  · rw [hm₈]; exact hfB.trans (hS₇.frame.sub hsub)
  · rw [← hHi]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv₇
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hg₈ _ (by decide) (by decide)]; assumption
  · rw [Masks, hx₈, hy₈]; exact hS₇.masks
  · intro k hk; rw [hm₈]; exact hS₇.wmem k hk (by omega)
  · rw [hsy₈, hsy₇, hsy₆, hsyB]; exact hsy

/-- The first block's hash value. -/
theorem first_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hA : AtLeave s₀ i s)
    {G : Prog isa} {Q : State → Prop} (hG : ∀ s', Mid s₀ i s' → WP isa G s' Q) :
    WP isa (.seq (.block (addState ++ ([.alu .cmp .rdx (.imm 1)] : List Instr))) G) s Q := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 =
        (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)[k] :=
    fun k hk => by rw [← stateAt_get _ _ hk, hA.state]
  refine VG.X86_64.WP.mono_syms (addState_ok hp _ _ hA.vars hA.rdi hA.rd hA.wr hH)
    fun s₉ ⟨hm₉, hv₉, pub₉, hrd₉, hwr₉, hx₉, hy₉⟩ hsy₉ => ?_
  refine VG.X86_64.WP.mono_syms (WP.mono (cmp_ok s₉) fun s₁₀ h => h) fun s₁₀ ⟨he₁₀, hg₁₀, hk₁₀⟩ hsy₁₀ => hG s₁₀ ?_
  obtain ⟨hm₁₀, hrd₁₀, hwr₁₀, -, hx₁₀, hy₁₀⟩ := hk₁₀
  have hc : Vector.zipWith (· + ·) (Spec.Sha512.rounds (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) (blk s₀ i) 80)
      (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ]; rfl
  have hfw : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]; exact frame_writeState (Frame.refl _ _) _
  have hsub' : ∀ r ∈ [stR s₀], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
  have g : ∀ r ∈ pubRegs, s₁₀.gpr r = s.gpr r := fun r hr => by rw [hg₁₀, pub₉ r hr]
  refine ⟨⟨by rw [g .rdi (by decide)]; exact hA.rdi, by rw [g .rcx (by decide)]; exact hA.rcx,
    by rw [g .rsp (by decide)]; exact hA.rsp, by rw [hrd₁₀, hrd₉]; exact hA.rd,
    by rw [hwr₁₀, hwr₉]; exact hA.wr, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [g .rsi (by decide)]; exact hA.rsi, by rw [g .rdx (by decide)]; exact hA.rdx, ?_, ?_, ?_⟩
  · rw [hm₁₀]; exact hA.frame.trans (hfw.sub hsub')
  · rw [hm₁₀, hm₉, stateAt_writeState]; exact hc
  · exact saved_frame hp (saved_frame hp hA.saved (.inr (.inl hfw)) (by rw [hx₉]) (by rw [hx₉]))
      (.inl (hm₁₀ ▸ Frame.refl _ _)) (by rw [hx₁₀]) (by rw [hx₁₀])
  · rw [Masks, hx₁₀, hy₁₀, hx₉, hy₉]; exact hA.masks
  · rw [hsy₁₀, hsy₉]; exact hA.syms
  · simp only [Vars8, hg₁₀]; rw [← hc]; exact hv₉
  · intro k hk
    rw [hm₁₀]
    exact wmem_frame hp hk (hA.wmem k hk) (.inl hfw)
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
    hm ▸ hc.state, saved_frame hp hc.saved (.inl (hm ▸ Frame.refl _ _)) (by rw [hx]) (by rw [hx]), ?_,
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
    have h0 : BitVec.ofNat 64 (nb s₀ - k) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      simp at h'
      omega
    refine ⟨by omega, by rw [he]; simpa using h0, { hc with rsi := hrsi, rdx := hrdx }⟩

/-- The block the next iteration starts at. -/
abbrev nxtI (s₀ : State) (i : Nat) : Nat := if nb s₀ - i = 1 then i + 1 else i + 2

/-- After an iteration from block `i`: the loop exits, or goes on with block `nxtI s₀ i`. -/
def BodyPost (s₀ : State) (i : Nat) (s : State) : Prop :=
  (nxtI s₀ i = nb s₀ ∧ eval .ne s = some false ∧ Common s₀ (nb s₀) s) ∨
    (nxtI s₀ i < nb s₀ ∧ eval .ne s = some true ∧ LInv s₀ (nxtI s₀ i) s)

theorem rest_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hA : AtLeave s₀ i s) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.rest s (BodyPost s₀ i) := by
  have := hp.nb_lt
  have hn := (s₀.gpr .rdx).isLt
  refine first_ok hp hi hA fun s₁ hM => WP.ite _ hM.e (fun h => ?_) (fun h => ?_)
  · rw [beq_iff_eq] at h
    refine WP.mono (adv_common hp hM.toCommon 128 1) fun s₂ ⟨hc, he, hrsi, hrdx⟩ => ?_
    have hrdx' : s₁.gpr .rdx - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
      rw [hM.rdx, e1, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    have hk : nxtI s₀ i = i + 1 := by simp only [nxtI, h, ↓reduceIte]
    unfold BodyPost; rw [hk]
    refine exit_or_next hp (by omega) hc ?_ hrdx he
    rw [hrsi, hM.rsi, e128]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add,
      show 128 * (i + 1) = 128 * i + 128 by omega]
  · rw [beq_eq_false_iff_ne] at h
    have hnx : nxt s₀ i = i + 1 := by simp only [nxt, h, ↓reduceIte]
    have hw := hM.wmem
    rw [hnx] at hw
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine VG.X86_64.WP.mono_syms (initCarry_ok hM.vars) fun s₂ ⟨hv₂, hk₂⟩ hsy₂ => ?_
    obtain ⟨hm₂, hrd₂, hwr₂, pub₂, hx₂, hy₂⟩ := hk₂
    have hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hM.rcx
    have hwr₂' : s₂.wr = s₀.wr := hwr₂.trans hM.wr
    have hrd₂' : s₂.rd = s₀.rd := hrd₂.trans hM.rd
    obtain ⟨spa, spb⟩ := sp_in hp hrcx₂ hwr₂'
    refine VG.X86_64.WP.mono_syms (enter_ok s₂ spa spb)
      fun sC ⟨hrdiC, hrdxC, hgC, hmC, hrdC, hwrC, hxC, hyC⟩ hsyC => ?_
    rw [hsy₂, hM.syms] at hrdiC
    have hspC : Frame [spR (scr s₀)] s₂.mem sC.mem := by rw [hmC, hrcx₂]; exact spill_frame _ _ _ _
    have hrcxC : sC.gpr .rcx = scr s₀ := by rw [hgC _ (by decide) (by decide)]; exact hrcx₂
    have hRC : (⟨scr s₀, 1328⟩ : Region) ∈ sC.wr := by rw [hwrC, hwr₂', hp.wr]; simp
    have hsub' : ∀ r ∈ [spR (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
      fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact sp_sub _⟩
    have hfC : Frame [stR s₀, scrR s₀] s₀.mem sC.mem := hM.frame.trans (hm₂ ▸ hspC.sub hsub')
    have hkC := kok_of_syms (s₀ := s₀) (s := sC) (by rw [hsyC, hsy₂, hM.syms])
    have hwC : ∀ t < 80, WOk 1 (blk s₀ (i + 1)) sC t := fun t ht =>
      (wok_of_wmem ht hrcxC hRC (wmem_frame hp (by omega) (by rw [hm₂]; exact hw (t / 2) (by omega))
        (.inr hspC))).2
    have hvC : Vars 0 sC (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) := by
      simp only [Vars] at hv₂ ⊢
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv₂
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hgC _ (by decide) (by decide)]; assumption
    refine WP.seq (VG.X86_64.WP.mono_syms (loop2_ok _ (blk s₀ (i + 1)) (kb s₀) sC hrdiC hkC hwC hvC hrdxC)
      fun s₃ ⟨hv₃, hS₃⟩ hsy₃ => ?_)
    rw [WP.block_append_iff, WP.block_append_iff]
    have hrcx₃ : s₃.gpr .rcx = scr s₀ := (hS₃.pub .rcx (by decide)).trans hrcxC
    have hwr₃ : s₃.wr = s₀.wr := by rw [hS₃.wr, hwrC, hwr₂']
    have hrd₃ : s₃.rd = s₀.rd := by rw [hS₃.rd, hrdC, hrd₂']
    obtain ⟨spa', spb'⟩ := sp_in' hp hrcx₃ hwr₃
    refine VG.X86_64.WP.mono_syms (leave_ok s₃ spa' spb')
      fun s₄ ⟨hrdi₄, hrdx₄, hg₄, hm₄, hrd₄, hwr₄, hx₄, hy₄⟩ hsy₄ => ?_
    have sr := spill_read (scr s₀) s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)
    rw [← hrcx₂, ← hmC] at sr
    rw [hrcx₃, hS₃.mem, ← hrcx₂, sr.1, pub₂ .rsi (by decide)] at hrdi₄
    rw [hrcx₃, hS₃.mem, ← hrcx₂, sr.2, pub₂ .rdx (by decide)] at hrdx₄
    have hH : ∀ k : Nat, (hk : k < 8) → s₄.mem.readW (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 =
        (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1))[k] :=
      fun k hk => by
        rw [← hM.state, stateAt_get _ _ hk, hm₄, hS₃.mem, ← hm₂]
        exact hspC.readW (r := stR s₀) (contains_offset' (off := 8 * k) (len := 64) (by omega) (by omega))
          (by simpa using Region.Disjoint.sub_right hp.st_scr (sp_sub _)) (by decide)
    have hv₄ : Vars8 s₄ (Spec.Sha512.rounds (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) (blk s₀ (i + 1)) 80) := by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv₃
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hg₄ _ (by decide) (by decide)]; assumption
    refine VG.X86_64.WP.mono_syms (addState_ok hp _ _ hv₄ (by
      rw [hg₄ .rdi (by decide) (by decide), hS₃.pub .rdi (by decide), hgC .rdi (by decide) (by decide),
        pub₂ .rdi (by decide)]; exact hM.rdi) (by rw [hrd₄, hrd₃])
      (by rw [hwr₄, hwr₃]) hH) fun s₅ ⟨hm₅, _, pub₅, hrd₅, hwr₅, hx₅, hy₅⟩ hsy₅ => ?_
    have hfw : Frame [stR s₀] s₄.mem s₅.mem := by
      rw [hm₅]; exact frame_writeState (Frame.refl _ _) _
    have hrsi₅ : s₅.gpr .rsi = s₁.gpr .rsi := by rw [pub₅ .rsi (by decide), hrdi₄]
    have g₅ : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsp → s₅.gpr r = s₁.gpr r := fun r hr => by
      have h1 : r ∈ pubR := by rcases hr with rfl | rfl | rfl <;> decide
      have h2 : r ∈ pubRegs := pubR_sub h1
      have h3 : r ≠ .rsi := by rcases hr with rfl | rfl | rfl <;> decide
      have h4 : r ≠ .rdx := by rcases hr with rfl | rfl | rfl <;> decide
      rw [pub₅ r h2, hg₄ r h3 h4, hS₃.pub r h1, hgC r h3 h4, pub₂ r h2]
    have hc₄ : Common s₀ (i + 2) s₅ := by
      have hsub'' : ∀ r ∈ [stR s₀], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
        fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
      refine ⟨by rw [g₅ .rdi (by simp)]; exact hM.rdi,
        by rw [g₅ .rcx (by simp)]; exact hM.rcx, by rw [g₅ .rsp (by simp)]; exact hM.rsp,
        by rw [hrd₅, hrd₄]; exact hrd₃, by rw [hwr₅, hwr₄]; exact hwr₃, ?_, ?_, ?_, ?_, ?_⟩
      · exact hfC.trans (hS₃.mem ▸ hm₄ ▸ hfw.sub hsub'')
      · rw [hm₅, stateAt_writeState, show i + 2 = i + 1 + 1 by omega, compressBlocks_succ _ _ _ (i + 1)]; rfl
      · have a₂ : Saved s₀ s₂ := saved_frame hp hM.saved (.inl (hm₂ ▸ Frame.refl _ _)) (by rw [hx₂]) (by rw [hx₂])
        have aC : Saved s₀ sC := saved_frame hp a₂ (.inr (.inr hspC)) (by rw [hxC]) (by rw [hxC])
        have a₃ : Saved s₀ s₃ := saved_frame hp aC (.inl (hS₃.mem ▸ Frame.refl _ _)) (by rw [hS₃.xmm])
          (by rw [hS₃.xmm])
        exact saved_frame hp a₃ (.inr (.inl (hm₄ ▸ hfw))) (by rw [hx₅, hx₄]) (by rw [hx₅, hx₄])
      · rw [Masks, hx₅, hy₅, hx₄, hy₄, hS₃.xmm, hS₃.ymmHi, hxC, hyC, hx₂, hy₂]; exact hM.masks
      · rw [hsy₅, hsy₄, hsy₃, hsyC, hsy₂]; exact hM.syms
    refine WP.mono (adv_common hp hc₄ 256 2) fun s₆ ⟨hc, he, hrsi, hrdx⟩ => ?_
    have hrdx' : s₅.gpr .rdx - BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 2)) := by
      rw [pub₅ .rdx (by decide), hrdx₄, hM.rdx, e2,
        show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    have hk : nxtI s₀ i = i + 2 := by simp only [nxtI, h, ↓reduceIte]
    unfold BodyPost; rw [hk]
    refine exit_or_next hp (by omega) hc ?_ hrdx he
    rw [hrsi, hrsi₅, hM.rsi, e256]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, ← BitVec.ofNat_add,
      show 128 * (i + 2) = 128 * i + 256 by omega]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.body s (BodyPost s₀ i) :=
  WP.seq (WP.mono (prefix_ok hp hi hL) fun _ hA => rest_ok hp hi hA)

/-! ## The prologue and the epilogue -/

theorem restore_eq : Impl.Sha512.X86_64.Avx2Rolled.restore = Spill.restoreCode .rcx Impl.Sha512.X86_64.Avx2Rolled.saved ++
    ([.vop .vzeroupper, .movqR .r14 .xmm14, .movqR .r15 .xmm15] : List Instr) := rfl

theorem restoreState_xmm (s : State) (g : Reg → BitVec 64) :
    ∀ l : List (Reg × Nat), (Spill.restoreState s g l).xmm = s.xmm := by
  intro l
  induction l generalizing s with
  | nil => rfl
  | cons p l ih => exact (ih _).trans rfl

theorem saveMem_saved {s₀ : State} : Spill.Saved (saveMem s₀) (scr s₀) s₀.gpr Impl.Sha512.X86_64.Avx2Rolled.saved :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_bound p hp; omega) (by decide)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) (hsy : s₁.syms = s₀.syms)
    (hk : Masks s₁) (h14 : (s₁.xmm .xmm14).extractLsb' 0 64 = s₀.gpr .r14)
    (h15 : (s₁.xmm .xmm15).extractLsb' 0 64 = s₀.gpr .r15) : Common s₀ 0 s₁ := by
  refine ⟨hg _ (by decide), hg _ (by decide), hg _ (by decide), hrd, hwr, ?_, ?_,
    ⟨by rw [hm]; exact saveMem_saved, h14, h15⟩, hk, hsy⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 8 * k) (len := 64) (by omega) (by omega))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get _ _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block Impl.Sha512.X86_64.Avx2Rolled.restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  rw [restore_eq]
  refine Spill.restore_then .rcx Impl.Sha512.X86_64.Avx2Rolled.saved s₀.gpr (by decide) (fun p hp' => ?_)
    (by rw [hc.rcx]; exact hc.saved.mem) ?_
  · have := saved_bound p hp'
    rw [hc.rcx, hc.rd, hc.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  have hm := (Spill.restoreState_mem s₀.gpr s Impl.Sha512.X86_64.Avx2Rolled.saved).1
  have hx := restoreState_xmm s s₀.gpr Impl.Sha512.X86_64.Avx2Rolled.saved
  have hg := Spill.restoreState_gpr s₀.gpr s Impl.Sha512.X86_64.Avx2Rolled.saved
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq,
    exists_eq_left', isa]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (simp only [State.setReg, reduceCtorEq, ↓reduceIte]; rw [hg]
         simp [Impl.Sha512.X86_64.Avx2Rolled.saved, hc.rsp])
      | skip
    · simp only [State.setReg, reduceCtorEq, ↓reduceIte, hx]; exact hc.saved.x14
    · simp only [State.setReg, ↓reduceIte, hx]; exact hc.saved.x15
  · simp only [State.setReg]; rw [hm]; exact hret
  · show stateAt _ _ = _; simp only [State.setReg]; rw [hm]; exact hc.state

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha512.X86_64.Avx2Rolled.compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressWideX86_64.post s₀ s' := by
  refine WP.seq (VG.X86_64.WP.mono_syms (prologue_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, _, hzf, hk, h14, h15⟩ hsy => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm hsy hk h14 h15
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa Impl.Sha512.X86_64.Avx2Rolled.body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨_, he, hc⟩ | ⟨hi', he, hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - nxtI s₀ i, by simp only [nxtI]; split <;> omega, nxtI s₀ i, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg _ (by decide)]; simp [blkAddr]
        rdx := by rw [hg _ (by decide)]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

end VG.Proof.Sha512.X86_64.Avx2.Rolled
