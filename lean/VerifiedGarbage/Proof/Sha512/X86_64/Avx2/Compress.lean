module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Schedule
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Rounds
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Schedule
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Rounds
meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SHA-512 with AVX2 on x86-64: the rounds of the first block

Group `n` computes the message words `2n+16` and `2n+17` of both blocks,
stores them, and runs rounds `2n` and `2n+1` of the first block, which read
their words from the scratch space. The words of both blocks are then all
stored, for the rounds of the second one.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W)
open VG.Proof.Sha512.X86_64 (ofInt_natCast contains_offset')

/-- Where `schedule` and `load` store the words `2k` and `2k+1` of both blocks. -/
abbrev wAddr (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofInt 64 ((32 * k : Nat) : Int)

/-- The words `2k` and `2k+1` of `M₀` and `M₁` are stored, in lanes 0 and 1. -/
def WMem (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) : Prop :=
  m.readW (wAddr scr k) 256 = pair M₁ k ++ pair M₀ k

/-- The part of the scratch space holding the words. -/
abbrev wRegion (scr : Addr) : Region := ⟨scr, 1280⟩

/-- The mask that `load` uses. -/
def Masks (s : State) : Prop := s.xmm mBswap = bswapMask ∧ s.ymmHi mBswap = bswapMask

theorem extract_lane0 (x₁ x₀ : BitVec 128) {q : Nat} (hq : q < 2) :
    (x₁ ++ x₀).extractLsb' (8 * (16 * 0 + 8 * q)) (8 * 8) = qword x₀ q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and,
    show 8 * (16 * 0 + 8 * q) + i < 128 by omega_arith, ite_true]
  exact congrArg _ (by omega_arith)

theorem extract_lane1 (x₁ x₀ : BitVec 128) {q : Nat} (hq : q < 2) :
    (x₁ ++ x₀).extractLsb' (8 * (16 * 1 + 8 * q)) (8 * 8) = qword x₁ q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and,
    show ¬ 8 * (16 * 1 + 8 * q) + i < 128 by omega_arith, ite_false]
  exact congrArg _ (by omega_arith)

theorem qword_pair (M : Block) (k : Nat) {q : Nat} (hq : q < 2) : qword (pair M k) q = W M (2 * k + q) := by
  rcases (by omega_arith : q = 0 ∨ q = 1) with rfl | rfl
  · exact qword_append_0 _ _
  · exact qword_append_1 _ _

theorem wSlot_ea (s : State) (j t : Nat) :
    s.ea (wSlot j t) = wAddr (s.gpr .rcx) (t / 2) + BitVec.ofNat 64 (16 * j + 8 * (t % 2)) := by
  simp only [State.ea, wSlot, at_, wAddr, ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]

theorem in_scr {s : State} {scr : Addr} (hR : (⟨scr, 1328⟩ : Region) ∈ s.wr) {d n : Nat}
    (hd : d + n ≤ 1328) : InRegions s.wr (scr + BitVec.ofInt 64 (d : Int)) n :=
  ⟨_, hR, contains_offset' hd (by omega_arith)⟩

/-- Rounds read the words `WMem` says are stored. -/
theorem wok_of_wmem {s : State} {scr : Addr} {M₀ M₁ : Block} {t : Nat} (ht : t < 80)
    (hrcx : s.gpr .rcx = scr) (hR : (⟨scr, 1328⟩ : Region) ∈ s.wr) (h : WMem s.mem scr M₀ M₁ (t / 2)) :
    WOk 0 M₀ s t ∧ WOk 1 M₁ s t := by
  have hin : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 8 := by
    intro j hj
    have e : s.ea (wSlot j t) = scr + BitVec.ofInt 64 ((32 * (t / 2) + 16 * j + 8 * (t % 2) : Nat) : Int) := by
      simp only [State.ea, wSlot, at_, hrcx]
    rw [e]
    obtain ⟨r, hr, hc⟩ := in_scr hR (d := 32 * (t / 2) + 16 * j + 8 * (t % 2)) (n := 8) (by omega_arith)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have rd : ∀ j < 2, s.mem.readW (s.ea (wSlot j t)) 64 =
      (pair M₁ (t / 2) ++ pair M₀ (t / 2)).extractLsb' (8 * (16 * j + 8 * (t % 2))) (8 * 8) := by
    intro j hj
    rw [wSlot_ea, hrcx, ← h, readW_extract _ _ (by omega_arith)]
  have et : 2 * (t / 2) + t % 2 = t := by omega_arith
  refine ⟨⟨hin 0 (by omega_arith), ?_⟩, ⟨hin 1 (by omega_arith), ?_⟩⟩
  · rw [rd 0 (by omega_arith), extract_lane0 _ _ (Nat.mod_lt _ (by omega_arith)), qword_pair _ _ (Nat.mod_lt _ (by omega_arith)),
      et]
  · rw [rd 1 (by omega_arith), extract_lane1 _ _ (Nat.mod_lt _ (by omega_arith)), qword_pair _ _ (Nat.mod_lt _ (by omega_arith)),
      et]

theorem wmem_write {m : Mem} {scr : Addr} {M₀ M₁ : Block} {k k' : Nat} (hk : k < 40) (hk' : k' < 40)
    (hne : k ≠ k') (v : BitVec 256) (h : WMem m scr M₀ M₁ k) :
    WMem (m.writeW (wAddr scr k') v) scr M₀ M₁ k := by
  simp only [WMem, wAddr, ofInt_natCast] at h ⊢
  exact (readW_writeW_off m scr v (d := 32 * k) (e := 32 * k') (n := 32) (by omega_arith) (by omega_arith)
    (by omega_arith)).trans h

theorem wmem_self (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) :
    WMem (m.writeW (wAddr scr k) (pair M₁ k ++ pair M₀ k)) scr M₀ M₁ k :=
  Mem.readW_writeW_self m _ 32 _ (by omega_arith)

theorem wAddr_contains (scr : Addr) {k : Nat} (hk : k < 40) : (wRegion scr).Contains (wAddr scr k) (256 / 8) :=
  contains_offset' (by omega_arith) (by omega_arith)

/-! ## The groups -/

/-- The registers `schedule` writes. -/
theorem sched_other (n : Nat) (r : XReg) (h : r = mBswap ∨ r = tmp) :
    r ≠ msg n ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ t3 := by
  have key : ∀ c < 8, ∀ r ∈ [mBswap, tmp],
      r ≠ msg c ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ t3 := by decide
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

theorem msg_ne (n k : Nat) (h₁ : n < k) (h₂ : k ≤ n + 7) : msg k ≠ msg n ∧ msg k ≠ t0 ∧ msg k ≠ t1 ∧
    msg k ≠ t2 ∧ msg k ≠ t3 := by
  have key : ∀ c < 8, ∀ d < 8, 0 < d →
      msg (c + d) ≠ msg c ∧ msg (c + d) ≠ t0 ∧ msg (c + d) ≠ t1 ∧ msg (c + d) ≠ t2 ∧ msg (c + d) ≠ t3 := by
    decide
  rw [show msg k = msg (n % 8 + (k - n)) by simp only [msg]; rw [show (n % 8 + (k - n)) % 8 = k % 8 by omega_arith],
    show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) _ (by omega_arith) (by omega_arith)

end VG.Proof.Sha512.X86_64.Avx2

/-!
# SHA-512 compression function on x86-64 with AVX2 and BMI

Facts about the state and the blocks of `Impl.Sha512.X86_64.Avx2.compress`'s
loop, reusing the scalar proof's block lemmas.
-/

namespace VG.Proof.Sha512.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha512.X86_64 (st bp nb scr stR blR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' sub_offset toNat_ofNat_lt ofInt_natCast stateAt_get
  stateAt_eq readW_writeW_word writeState stateAt_writeState frame_writeState)

/-! ## The precondition -/

abbrev scrR (s₀ : State) : Region := ⟨scr s₀, 1328⟩

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressWideX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_arith

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega_arith) (by omega_arith)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega_arith) (by omega_arith)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega_arith) (by omega_arith)

theorem in_blk16 {i n : Nat} (hi : i < nb s₀) (hn : n < 8) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 := by
  have := h.nb_lt
  refine ⟨blR s₀, by simp [h.rd], ?_⟩
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 16 * n) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega_arith) (by omega_arith)

end Pre

/-! ## Loading the blocks -/

theorem bswapMask_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a bswapMask = ofBytes fun j => byte a (8 * (j / 8) + 7 - j % 8) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem getLsbD_bswap64_block (x : BitVec 64) {j r : Nat} (hj : j < 8) (hr : r < 8) :
    (bswap64 x).getLsbD (8 * j + r) = x.getLsbD (8 * (7 - j) + r) := by
  simp only [bswap64, getLsbD_append_block _ _ _ hr]
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega_arith) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.add_comm]

/-- `vpshufb` with `bswapMask`: each quadword byte-reversed. -/
theorem pshufb_bswap64 (a : BitVec 128) :
    XBinOp.eval .pshufb a bswapMask = bswap64 (qword a 1) ++ bswap64 (qword a 0) := by
  rw [bswapMask_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega_arith, by omega_arith, by omega_arith⟩
  rw [getLsbD_ofBytes _ hk hr, BitVec.getLsbD_append]
  rcases (by omega_arith : k < 8 ∨ 8 ≤ k) with h | h
  · simp only [show 8 * k + r < 64 by omega_arith, ↓reduceIte]
    rw [getLsbD_bswap64_block _ h hr]
    simp only [byte, qword, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and,
      decide_eq_true (show 8 * (7 - k) + r < 64 by omega_arith)]
    exact congrArg _ (by omega_arith)
  · obtain ⟨j, rfl⟩ : ∃ j, k = 8 + j := ⟨k - 8, by omega_arith⟩
    simp only [show ¬ 8 * (8 + j) + r < 64 by omega_arith, ↓reduceIte]
    rw [show 8 * (8 + j) + r - 64 = 8 * j + r by omega_arith,
      getLsbD_bswap64_block _ (by omega_arith) hr]
    simp only [byte, qword, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and,
      decide_eq_true (show 8 * (7 - j) + r < 64 by omega_arith)]
    exact congrArg _ (by omega_arith)

theorem qword_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 2) :
    qword (m.readW a 128) j = m.readW (a + BitVec.ofNat 64 (8 * j)) 64 := by
  rw [qword, show 64 * j = 8 * (8 * j) by omega_arith]
  exact readW_extract m a (k := 8 * j) (n := 8) (by omega_arith)

theorem load_pair (M : Block) (m : Mem) (p : Addr) {n : Nat} (hn : n < 8)
    (hblk : ∀ t : Nat, t < 16 → bswap64 (m.readW (p + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M t) :
    XBinOp.eval .pshufb (m.readW (p + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) bswapMask = pair M n := by
  rw [pshufb_bswap64, pair]
  have e : ∀ j, j < 2 → bswap64 (qword (m.readW (p + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) j) =
      W M (2 * n + j) := by
    intro j hj
    rw [qword_readW _ _ hj, ← hblk (2 * n + j) (by omega_arith)]
    refine congrArg (fun a => bswap64 (m.readW a 64)) ?_
    simp only [ofInt_natCast]
    rw [show 8 * (2 * n + j) = 16 * n + 8 * j by omega_arith]
    exact Offset.add_ofNat_add_ofNat _ _ _
  rw [e 0 (by omega_arith), e 1 (by omega_arith)]
  rfl

theorem load_ok {i : Nat} (hi : i < 8) (s : State) {p₀ p₁ scr : Addr} {M₀ M₁ : Block}
    (hrsi : s.gpr .rsi = p₀) (hr15 : s.gpr .r15 = p₁) (hrcx : s.gpr .rcx = scr)
    (hin₀ : InRegions (s.rd ++ s.wr) (p₀ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (p₁ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hout : InRegions s.wr (wAddr scr i) 32)
    (hm : s.xmm mBswap = bswapMask) (hm' : s.ymmHi mBswap = bswapMask)
    (hb₀ : ∀ t : Nat, t < 16 → bswap64 (s.mem.readW (p₀ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₀ t)
    (hb₁ : ∀ t : Nat, t < 16 → bswap64 (s.mem.readW (p₁ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₁ t) :
    WP isa (.block (load i)) s fun s' =>
      s'.xmm (msg i) = pair M₀ i ∧ s'.ymmHi (msg i) = pair M₁ i ∧
      (∀ r, r ≠ msg i → r ≠ tmp → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem.writeW (wAddr scr i) (pair M₁ i ++ pair M₀ i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup i
  have hd' := VG.nodup_reverse hd
  have q₀ := load_pair M₀ s.mem p₀ hi hb₀
  have q₁ := load_pair M₁ s.mem p₁ hi hb₁
  apply WP.of_runBlock
  simp only [load, vb]
  generalize msg i = x at *
  generalize msg (i + 1) = x₁ at *
  generalize msg (i + 4) = x₄ at *
  generalize msg (i + 5) = x₅ at *
  generalize msg (i + 7) = x₇ at *
  simp only [T, t0, t1, t2, t3, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd' hm hm' ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, State.setV, State.lane, State.ymm, State.store256, State.load128, ea_at, hrsi, hr15, hrcx, hin₀,
    hin₁, hout, ite_true, ite_false, hd, hd', hm, hm', VBinOp.sse, q₀, q₁, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩

/-! ## The hash value -/

/-- The working variables `v` are in the registers of round 0. -/
def Vars8 (s : State) (v : HashValue) : Prop :=
  s.gpr .rax = v[0] ∧ s.gpr .rbx = v[1] ∧ s.gpr .rbp = v[2] ∧ s.gpr .r8 = v[3] ∧
  s.gpr .r9 = v[4] ∧ s.gpr .r10 = v[5] ∧ s.gpr .r11 = v[6] ∧ s.gpr .r12 = v[7]

theorem Vars.vars8 {s : State} {v : HashValue} (h : Vars 80 s v) : Vars8 s v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem loadState_eq : loadState = [
    .mov .rax (.mem (at_ .rdi (8 * 0))), .mov .rbx (.mem (at_ .rdi (8 * 1))),
    .mov .rbp (.mem (at_ .rdi (8 * 2))), .mov .r8 (.mem (at_ .rdi (8 * 3))),
    .mov .r9 (.mem (at_ .rdi (8 * 4))), .mov .r10 (.mem (at_ .rdi (8 * 5))),
    .mov .r11 (.mem (at_ .rdi (8 * 6))), .mov .r12 (.mem (at_ .rdi (8 * 7)))] := by
  decide

theorem addState_eq : addState = [
    .alu .add .rax (.mem (at_ .rdi (8 * 0))), .alu .add .rbx (.mem (at_ .rdi (8 * 1))),
    .alu .add .rbp (.mem (at_ .rdi (8 * 2))), .alu .add .r8 (.mem (at_ .rdi (8 * 3))),
    .alu .add .r9 (.mem (at_ .rdi (8 * 4))), .alu .add .r10 (.mem (at_ .rdi (8 * 5))),
    .alu .add .r11 (.mem (at_ .rdi (8 * 6))), .alu .add .r12 (.mem (at_ .rdi (8 * 7))),
    .store (at_ .rdi (8 * 0)) .rax, .store (at_ .rdi (8 * 1)) .rbx,
    .store (at_ .rdi (8 * 2)) .rbp, .store (at_ .rdi (8 * 3)) .r8,
    .store (at_ .rdi (8 * 4)) .r9, .store (at_ .rdi (8 * 5)) .r10,
    .store (at_ .rdi (8 * 6)) .r11, .store (at_ .rdi (8 * 7)) .r12] := by
  decide

theorem initCarry_eq : initCarry = [.mov .r13 (.reg .rbx), .alu .xor .r13 (.reg .rbp)] := rfl

set_option simprocs false in
theorem loadState_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block loadState) s fun s₁ => Vars8 s₁ (stateAt s.mem (st s₀)) ∧ Keeps s s₁ := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [loadState_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp (config := {decide := true}) only [Vars8, Keeps, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at,
    State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, hrdi, h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [pubRegs]

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .rax = v[0] ∧ s.gpr .rbx = v[1] ∧ s.gpr .rbp = v[2] ∧ s.gpr .r8 = v[3] ∧
    s.gpr .r9 = v[4] ∧ s.gpr .r10 = v[5] ∧ s.gpr .r11 = v[6] ∧ s.gpr .r12 = v[7] ∧
    s.gpr .r13 = v[1] ^^^ v[2] := Iff.rfl

theorem initCarry_ok {s : State} {v : HashValue} (hv : Vars8 s v) :
    WP isa (.block initCarry) s fun s₁ => Vars 0 s₁ v ∧ Keeps s s₁ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  rw [initCarry_eq]
  simp only [reduceCtorEq, ↓reduceIte, and_self, vars0, Keeps, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags,
    h0, h1, h2, h3, h4, h5, h6, h7, 
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, rfl⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

set_option simprocs false in
theorem addState_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars8 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 = H[k]) :
    WP isa (.block addState) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      Vars8 s' (Vector.zipWith (· + ·) V H) ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [addState_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, ea_at, State.load64, State.store64, State.setReg, arithFlags,
    State.setFlags, hrdi, i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, trivial⟩
  · simp only [writeState, Vector.getElem_zipWith]
  · simp (config := {decide := true}) only [Vars8, Vector.getElem_zipWith, ite_true, ite_false, and_self]
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- After loading words `0 … 2n-1` of both blocks, from the state `sL`. -/
structure LdInv (M₀ M₁ : Block) (scr : Addr) (sL : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = sL.gpr
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  masks : Masks s
  frame : Frame [wRegion scr] sL.mem s.mem
  wmem : ∀ k < n, WMem s.mem scr M₀ M₁ k
  msgs : ∀ k < n, s.xmm (msg k) = pair M₀ k ∧ s.ymmHi (msg k) = pair M₁ k

theorem load_step {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sL : State}
    (hrsi : sL.gpr .rsi = p₀) (hr15 : sL.gpr .r15 = p₁) (hrcx : sL.gpr .rcx = scr)
    (hR : (⟨scr, 1328⟩ : Region) ∈ sL.wr)
    (hin : ∀ n : Nat, n < 8 → InRegions (sL.rd ++ sL.wr) (p₀ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (sL.rd ++ sL.wr) (p₁ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ m, Frame [wRegion scr] sL.mem m →
      (∀ t : Nat, t < 16 → bswap64 (m.readW (p₀ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₀ t) ∧
      (∀ t : Nat, t < 16 → bswap64 (m.readW (p₁ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₁ t))
    {n : Nat} (hn : n < 8) {s : State} (h : LdInv M₀ M₁ scr sL n s) :
    WP isa (.block (load n)) s (LdInv M₀ M₁ scr sL (n + 1)) := by
  obtain ⟨k1, k2⟩ := h.masks
  have hb := hblk _ h.frame
  refine WP.mono (load_ok (p₀ := p₀) (p₁ := p₁) (scr := scr) (M₀ := M₀) (M₁ := M₁) hn s
    (by rw [h.gpr]; exact hrsi) (by rw [h.gpr]; exact hr15)
    (by rw [h.gpr]; exact hrcx) (by rw [h.rd, h.wr]; exact (hin n hn).1) (by rw [h.rd, h.wr]; exact (hin n hn).2)
    (by rw [h.wr]; exact in_scr hR (by omega_arith)) k1 k2 hb.1 hb.2)
    fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ => ⟨hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_⟩
  · have o := hx mBswap (sched_other n mBswap (.inl rfl)).1 (by decide)
    rw [Masks, o.1, o.2]
    exact ⟨k1, k2⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (wAddr_contains scr (by omega_arith))
  · intro k hk
    rw [hm]
    by_cases hkn : k = n
    · subst hkn; exact wmem_self _ _ _ _ _
    · exact wmem_write (by omega_arith) (by omega_arith) hkn _ (h.wmem k (by omega_arith))
  · intro k hk
    by_cases hkn : k = n
    · subst hkn; exact ⟨ex, ey⟩
    · have o₁ := (msg_ne k n (by omega_arith) (by omega_arith)).1
      have o₂ := (sched_other k tmp (.inr rfl)).1
      rw [(hx _ (Ne.symm o₁) (Ne.symm o₂)).1, (hx _ (Ne.symm o₁) (Ne.symm o₂)).2]
      exact h.msgs k (by omega_arith)

/-! ## Counting the blocks -/

theorem e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem e2 : BitVec.signExtend 64 (2 : BitVec 32) = 2 := by decide
theorem e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
theorem e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide

theorem pub_ne15 {r : Reg} (hr : r ∈ pubRegs) : r ≠ .r15 := by
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem setup_ok (s : State) :
    WP isa (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)]) s fun s' =>
      eval .e s' = some (s.gpr .rdx - 1 == 0) ∧ s'.gpr .r15 = s.gpr .rsi ∧
      (∀ r, r ≠ .r15 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [T, Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, e1, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, fun r hr => by simp [hr], trivial, trivial, trivial,
    fun r hr => by simp [pub_ne15 hr], trivial⟩

theorem next_ok (s : State) :
    WP isa (.block [.alu .add T (.imm 128)]) s fun s' =>
      s'.gpr .r15 = s.gpr .r15 + 128 ∧ (∀ r, r ≠ .r15 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reducePow, and_self, T, Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, e128, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, fun r hr => by simp [pub_ne15 hr], trivial⟩

theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1)]) s fun s' =>
      eval .e s' = some (s.gpr .rdx - 1 == 0) ∧ s'.gpr = s.gpr ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp only [and_self, implies_true, Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, arithFlags, State.setFlags, e1, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial⟩

theorem adv_ok (s : State) (a b : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm a), .alu .sub .rdx (.imm b)]) s fun s' =>
      eval .ne s' = some (!(s.gpr .rdx - b.signExtend 64 == 0)) ∧
      s'.gpr .rsi = s.gpr .rsi + a.signExtend 64 ∧ s'.gpr .rdx = s.gpr .rdx - b.signExtend 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩

/-! ## Regions -/

theorem wsub (p : Addr) : Region.Sub (wRegion p) ⟨p, 1328⟩ := Region.sub_prefix (by omega_arith)

theorem slot_sub (p : Addr) {d n : Nat} (hd : d + n ≤ 1328) :
    Region.Sub ⟨p + BitVec.ofInt 64 (d : Int), n⟩ ⟨p, 1328⟩ := by
  rw [ofInt_natCast]; exact sub_offset (by omega_arith) (by omega_arith)

theorem state_frame_w {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [wRegion (scr s₀)] m m') :
    stateAt m' (st s₀) = stateAt m (st s₀) := by
  apply stateAt_eq
  intro k hk
  rw [hf.readW (contains_offset' (off := 8 * k) (len := 64) (by omega_arith) (by omega_arith))
    (by simpa using Region.Disjoint.sub_right hp.st_scr (wsub _)) (by decide), ← stateAt_get _ _ hk]

/-! ## The loop invariant -/

/-- The block in lane 1: the next one if there is one, else block `i` again. -/
abbrev nxt (s₀ : State) (i : Nat) : Nat := if nb s₀ - i = 1 then i else i + 1

theorem sub_one_eq {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (BitVec.ofNat 64 (nb s₀ - i) - 1 == 0) = (nb s₀ - i == 1) := by
  have := hp.nb_lt
  have hn : nb s₀ - i < 2 ^ 64 := by omega_arith
  have h1 : 1 ≤ nb s₀ - i := by omega_arith
  generalize nb s₀ - i = n at *
  by_cases h : n = 1
  · subst h; decide
  · have h' : BitVec.ofNat 64 n - 1 ≠ 0 := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat h1]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      exact h (by have h2 : n - 1 = 0 := this; omega_arith)
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

theorem blk_read {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {m m' : Mem}
    (hf : Frame [stR s₀, scrR s₀] s₀.mem m) (hf' : Frame [wRegion (scr s₀)] m m') :
    ∀ t : Nat, t < 16 → bswap64 (m'.readW (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) =
      W (blk s₀ i) t := by
  intro t ht
  rw [hf'.readW (hp.blk_contains hi ht) (by simpa using Region.Disjoint.sub_right hp.blk_scr (wsub _)) (by decide),
    hf.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
  exact blk_word i t ht

/-! ## The whole function -/

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩]

end VG.Proof.Sha512.X86_64.Avx2
