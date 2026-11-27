module

public import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
public import VerifiedGarbage.Proof.Aes.Contract
public import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
public import VerifiedGarbage.Proof.Aes.X86_64.Sbox
public import VerifiedGarbage.Proof.Aes.KeyWords
public import VerifiedGarbage.Proof.Framework.X86_64.Linear
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
meta import VerifiedGarbage.Proof.Aes.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Linear
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The AES key expansion on x86-64

`expandKey_verified`: `Impl.Aes.X86_64.expandKey` computes the key schedule.
The words are those of `Proof/Aes/KeyWords.lean` (`W`); `subWord_ok` is the
bitsliced `SUBWORD`, `word_ok` one word of the schedule.
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64
open VG.Proof.Aes VG.Proof.Aes.KeyWords
open VG.Impl.Aes.KeyWords (rc)

/-! ## SUBWORD -/

def spreadG (j p : Nat) : List Nat := if p + j < 64 then [p + j] else []

theorem spread_check : check (lanes 64 6) sboxCfg (linExt 0) spread (linEnv [(.rax, 0)])
    (linPost 6 ((List.range 8).map fun j => (q j, spreadG j))) = true := by
  decide +kernel

def gatherG (p : Nat) : List Nat := if p < 32 then [64 * (p % 8) + (p - p % 8)] else []

def qIns : List (Reg × Nat) := (List.range 8).map fun j => (q j, j)

theorem gather_check : check (lanes 64 9) sboxCfg (linExt 0) gather (linEnv qIns)
    (linPost 9 [(.rax, gatherG)]) = true := by
  decide +kernel

theorem subWord_rest :
    [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all (fun r =>
      (spread.all fun i => i.dst != some r) && gather.all fun i => i.dst != some r) = true := by
  decide +kernel

theorem subWord_ok {s : State} (hok : Ok sboxCfg s) :
    WP isa (.block subWord) s fun s' =>
      s'.gpr .rax = (sub32 ((s.gpr .rax).setWidth 32)).setWidth 64 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∉ sboxWrites, s'.gpr r = s.gpr r) ∧ Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have rest : ∀ r ∉ sboxWrites, (spread.all fun i => i.dst != some r) = true ∧ (gather.all fun i => i.dst != some r) = true :=
    fun r hr => by
      have := List.all_eq_true.mp subWord_rest r (by revert hr; cases r <;> decide)
      simpa using this
  have hsb : sb ∉ sboxWrites := by decide
  obtain ⟨s1, e1, o1, rd1, wr1, k1, f1⟩ := linear_ok spread_check hok (fun _ => s.gpr .rax)
    (fun r i h => by simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (Nat.not_lt_zero _))
  have g1 : ∀ r ∉ sboxWrites, s1.gpr r = s.gpr r := fun r hr => k1 r (rest r hr).1
  have hok1 : Ok sboxCfg s1 := hok.congr (g1 _ hsb) (g1 _ hsb) rd1 wr1
  obtain ⟨s2, e2, o2, rd2, wr2, g2, f2⟩ := sbox_ok hok1
  have hok2 : Ok sboxCfg s2 := hok1.congr (g2 _ hsb) (g2 _ hsb) rd2 wr2
  obtain ⟨s3, e3, o3, rd3, wr3, k3, f3⟩ := linear_ok gather_check hok2 (fun j => s2.gpr (q j))
    (fun r i h => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at h
      obtain ⟨j, hj, rfl, rfl⟩ := h
      exact ⟨by omega, rfl⟩)
    (fun j hj => absurd hj (Nat.not_lt_zero _))
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s1, e1, WP.of_runBlock ⟨s2, e2, WP.of_runBlock ⟨s3, e3, ?_⟩⟩⟩))
  have s2s : slotRegion sboxCfg s1 = slotRegion sboxCfg s := congrArg (fun a => (⟨a, 384⟩ : Region)) (g1 _ hsb)
  have s3s : slotRegion sboxCfg s2 = slotRegion sboxCfg s := congrArg (fun a => (⟨a, 384⟩ : Region)) ((g2 _ hsb).trans (g1 _ hsb))
  rw [s2s] at f2
  rw [s3s] at f3
  refine ⟨?_, rd3.trans (rd2.trans rd1), wr3.trans (wr2.trans wr1), fun r hr => by rw [k3 r (rest r hr).2, g2 r hr, g1 r hr],
    f1.trans (f2.trans f3)⟩
  refine BitVec.eq_of_getLsbD_eq fun p hp => ?_
  rw [o3 _ _ (List.mem_singleton.mpr rfl) p hp, BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and, gatherG]
  by_cases h32 : p < 32
  · rw [ite_eq_left h32, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf]
    simp only [show (64 * (p % 8) + (p - p % 8)) / 64 = p % 8 by omega, show (64 * (p % 8) + (p - p % 8)) % 64 = p - p % 8 by omega]
    rw [o2 (p % 8) (by omega) _ (by omega)]
    have hb := congrArg (BitVec.getLsbD · (p % 8)) (sub32_byte ((s.gpr .rax).setWidth 32) (q := p / 8) (by omega))
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true (show p % 8 < 8 by omega), Bool.true_and,
      show 8 * (p / 8) + p % 8 = p by omega] at hb
    rw [hb, Vector.sbox_eq]
    refine congrArg (fun b => (Spec.Aes.sbox b).getLsbD (p % 8)) (byte_ext fun j hj => ?_)
    rw [getLsbD_bsByte _ _ hj, o1 (q j) (spreadG j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) _ (by omega), spreadG,
      ite_eq_left (by omega), xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
      BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and]
    simp only [show p - p % 8 + j < 64 by omega, Nat.mod_eq_of_lt, show 8 * (p / 8) + j = p - p % 8 + j by omega]
  · rw [ite_eq_right h32, BitVec.getLsbD_of_ge _ _ (by omega)]
    rfl

/-! ## ROTWORD and the round constants -/

/-- Round constant `k + 1`. -/
def rcVal (k : Nat) : BitVec 64 := (rc (k + 1)).setWidth 64

theorem rcVal_next : ∀ k < 10, rcVal k <<< 1 ^^^ ((0#64 - (rcVal k <<< 1) >>> 8) &&& 283#64) = rcVal (k + 1) := by
  decide +kernel

theorem width_8 (v : BitVec 8) : (v.setWidth 64).setWidth 32 = v.setWidth 32 :=
  BitVec.setWidth_setWidth_of_le v (by decide)

/-- What the code for a word's `temp` may write below its scratch. -/
abbrev tR (B : Addr) : List Region := [⟨B, 384⟩, ⟨B + BitVec.ofNat 64 432, 8⟩]

theorem rotTail_ok {s : State} {B : Addr} {k : Nat} (hk : k < 10) (h9 : s.gpr .r9 = B) (hB : ⟨B, 512⟩ ∈ s.wr)
    (hrc : s.mem.readW (B + BitVec.ofNat 64 432) 64 = rcVal k) :
    WP isa (.block rotTail) s fun s' =>
      (s'.gpr .rax).setWidth 32 = ((s.gpr .rax).setWidth 32).rotateRight 8 ^^^ (rc (k + 1)).setWidth 32 ∧
      s'.mem.readW (B + BitVec.ofNat 64 432) 64 = rcVal (k + 1) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∉ sboxWrites, s'.gpr r = s.gpr r) ∧ Frame (tR B) s.mem s'.mem := by
  have hw : InRegions s.wr (B + BitVec.ofNat 64 432) 8 := ⟨_, hB, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 432) 8 := ⟨_, List.mem_append_right _ hB, Offset.contains_base _ (by decide) (by decide)⟩
  have ea : ∀ s' : State, s'.ea (slotAt sb rcSlot) = s'.gpr .r9 + BitVec.ofNat 64 432 := fun _ => rfl
  have c1 : ((1 : Nat) ≤ 8 ∧ 8 ≤ 31) = True := by decide
  have c2 : ((1 : Nat) ≤ 1 ∧ 1 ≤ 63) = True := by decide
  have c3 : ((1 : Nat) ≤ 8 ∧ 8 ≤ 63) = True := by decide
  have e11b : BitVec.signExtend 64 (283 : BitVec 32) = 283#64 := by decide
  apply WP.of_runBlock
  simp only [c1, c2, c3, e11b, rotTail, movS, movR, xorR, shrI, st, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execShift32,
    execShift, execAlu, readSrc, readSrc32, State.load64, State.store64, State.setReg32, ea, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, wr_setReg, rd_setReg, mem_setReg, wr_arithFlags, rd_arithFlags, mem_arithFlags, wr_setFlags, rd_setFlags,
    mem_setFlags, reduceCtorEq, ite_false, ite_true, h9, hw, hr, hrc,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have ez : BitVec.setWidth 64 (0 : BitVec 32) = 0#64 := by decide
  rw [ez, rcVal_next k hk]
  refine ⟨?_, Mem.readW_writeW_self (n := 8) _ _ _ (by decide), trivial, trivial, fun r hr => ?_, ?_⟩
  · rw [BitVec.setWidth_xor, setWidth_setWidth_32, rcVal, width_8]
  · obtain ⟨a, c, d, e⟩ : r ≠ .rax ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert hr; cases r <;> decide
    simp only [a, c, d, e, ite_false]
  · exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)

/-! ## The loop's state -/

/-- The callee-saved registers are in their slots. -/
def Saved (s₀ : State) (B : Addr) (m : Mem) : Prop :=
  ∀ p ∈ savedRegs, m.readW (B + BitVec.ofNat 64 (8 * p.1)) 64 = s₀.gpr p.2

theorem savedRegs_slot : ∀ p ∈ savedRegs, 48 ≤ p.1 ∧ p.1 < 54 := by decide

theorem Saved.frame {s₀ : State} {B : Addr} {m m' : Mem} (h : Saved s₀ B m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨B + BitVec.ofNat 64 384, 48⟩ r) : Saved s₀ B m' := fun p hp => by
  obtain ⟨h1, h2⟩ := savedRegs_slot p hp
  rw [← h p hp]
  exact hf.readW (r := ⟨B + BitVec.ofNat 64 384, 48⟩) (Offset.contains _ (by omega) (by omega) (by decide)) hd (by decide)

theorem Good.frame {m m' : Mem} {p : Addr} {f : Nat → BitVec 32} {K : Nat} (h : Good m p f K) (hK : 4 * K ≤ 240)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 240⟩ r) : Good m' p f K := fun i hi => by
  rw [← h i hi]
  exact hf.readW (r := ⟨p, 240⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

/-- The buffers. -/
structure ES (s₀ : State) (B S kp : Addr) (nk : Nat) : Prop where
  nks : nk = 4 ∨ nk = 6 ∨ nk = 8
  inB : ⟨B, 512⟩ ∈ s₀.wr
  inS : ⟨S, 240⟩ ∈ s₀.wr
  inK : ⟨kp, 4 * nk⟩ ∈ s₀.rd
  dSB : Region.Disjoint ⟨S, 240⟩ ⟨B, 512⟩
  dKS : Region.Disjoint ⟨kp, 4 * nk⟩ ⟨S, 240⟩
  dKB : Region.Disjoint ⟨kp, 4 * nk⟩ ⟨B, 512⟩

/-- After word `i - 1`. -/
structure WI (s₀ : State) (B S kp : Addr) (nk i : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = S + BitVec.ofNat 64 (4 * i)
  rsi : s.gpr .rsi = BitVec.ofNat 64 (4 * nk)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * (i % nk))
  rdi : s.gpr .rdi = BitVec.ofNat 64 (4 * (4 * (nk + 7) - i))
  r9 : s.gpr .r9 = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rc : s.mem.readW (B + BitVec.ofNat 64 432) 64 = rcVal ((i - 1) / nk)
  saved : Saved s₀ B s.mem
  good : Good s.mem S (W s₀.mem kp nk) i
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-! ## One word -/

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; bv_omega
  · rintro rfl; exact BitVec.sub_self _

theorem ofNat_beq {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  rw [← sub_beq ha (by decide), BitVec.sub_zero]

theorem addr_m4 (S : Addr) {i : Nat} (hi : 1 ≤ i) :
    S + BitVec.ofNat 64 (4 * i) + BitVec.ofInt 64 (-4) = S + BitVec.ofNat 64 (4 * (i - 1)) := by
  rw [show 4 * i = 4 * (i - 1) + 4 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc _ _ (BitVec.ofInt 64 (-4)),
    show BitVec.ofNat 64 4 + BitVec.ofInt 64 (-4) = 0#64 by decide, BitVec.add_zero]

variable {s₀ : State} {B S kp : Addr} {nk : Nat}

theorem i_div {nk i : Nat} (h : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (hi' : i < 4 * (nk + 7)) (h0 : i % nk = 0) :
    i / nk = (i - 1) / nk + 1 ∧ (i - 1) / nk < 10 := by
  rcases h with rfl | rfl | rfl <;> omega

theorem i_div' {nk i : Nat} (h : nk = 4 ∨ nk = 6 ∨ nk = 8) (h0 : i % nk ≠ 0) : i / nk = (i - 1) / nk := by
  rcases h with rfl | rfl | rfl <;> omega

theorem i_mod {nk i : Nat} (h : nk = 4 ∨ nk = 6 ∨ nk = 8) :
    i % nk < nk ∧ (i % nk + 1 = nk → (i + 1) % nk = 0) ∧ (i % nk + 1 ≠ nk → (i + 1) % nk = i % nk + 1) := by
  rcases h with rfl | rfl | rfl <;> omega

/-- `temp` of word `i`. -/
structure TP (s₀ : State) (B : Addr) (kp : Addr) (nk i : Nat) (s s' : State) : Prop where
  rax : (s'.gpr .rax).setWidth 32 = temp32 nk i (W s₀.mem kp nk (i - 1))
  rc : s'.mem.readW (B + BitVec.ofNat 64 432) 64 = rcVal (i / nk)
  gpr : ∀ r ∉ sboxWrites, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (tR B) s.mem s'.mem

theorem temp_ok (hs : ES s₀ B S kp nk) {i : Nat} (hi : nk ≤ i) (hi' : i < 4 * (nk + 7)) {s : State}
    (h : WI s₀ B S kp nk i s) : WP isa temp s (TP s₀ B kp nk i s) := by
  have hnk := hs.nks
  have h60 : i < 60 := by omega
  have hmod := (i_mod (i := i) hnk).1
  have hld : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (4 * (i - 1))) 4 :=
    ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.inS), Offset.contains_base _ (by omega) (by omega)⟩
  have key : ∃ s1, runBlock isa [.mov32 .rax (.mem { base := .rdx, disp := -4 }), .alu .test .r8 (.reg .r8)] s = some s1 ∧
      (s1.gpr .rax).setWidth 32 = W s₀.mem kp nk (i - 1) ∧ s1.zf = some (decide (i % nk = 0)) ∧
      (∀ r, r ≠ .rax → s1.gpr r = s.gpr r) ∧ s1.mem = s.mem ∧ s1.rd = s.rd ∧ s1.wr = s.wr := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc32, readSrc, State.load32,
      State.setReg32, State.ea, h.rdx, addr_m4 S (show 1 ≤ i by omega), hld, ite_true, Option.map_some, Option.bind_some,
      gpr_setReg, gpr_arithFlags, zf_arithFlags, reduceCtorEq, ite_false, BitVec.and_self, h.r8, Option.some.injEq,
      exists_eq_left', setWidth_setWidth_32]
    refine ⟨h.good _ (by omega), ?_, fun r hr => by simp only [hr, ite_false], rfl, rfl, rfl⟩
    rw [ofNat_beq (by omega)]
    exact decide_eq_decide.mpr (by omega)
  obtain ⟨s1, e1, x1, z1, g1, m1, rd1, wr1⟩ := key
  have w9 : Reg.r9 ∉ sboxWrites := by decide
  have hB : ⟨B, 512⟩ ∈ s.wr := by rw [h.wr]; exact hs.inB
  have ok : ∀ s' : State, s'.gpr .r9 = B → s'.wr = s.wr → Ok sboxCfg s' := fun s' a c =>
    Ok.of_region (r := ⟨B, 512⟩) (by rw [c]; exact hB) a.symm (show 8 * 48 ≤ 512 by decide) (by decide) rfl
  have reg : ∀ s' : State, s'.gpr .r9 = B → slotRegion sboxCfg s' = ⟨B, 384⟩ := fun s' a =>
    congrArg (fun a => (⟨a, 384⟩ : Region)) a
  have r91 : s1.gpr .r9 = B := by rw [g1 _ (by decide), h.r9]
  have nax : ∀ r ∉ sboxWrites, r ≠ .rax ∧ r ≠ .r10 := fun r hr => by revert hr; cases r <;> decide
  have dd : ∀ r ∈ ([⟨B, 384⟩] : List Region), Region.Disjoint ⟨B + BitVec.ofNat 64 432, 8⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  refine WP.seq (WP.of_runBlock ⟨s1, e1, WP.ite (decide (i % nk = 0)) (by simp [X86_64.eval, z1]) (fun h0 => ?_) (fun h0 => ?_)⟩)
  · have h0 : i % nk = 0 := by simpa using h0
    obtain ⟨d1, d2⟩ := i_div hnk hi hi' h0
    refine WP.block_append (WP.mono (subWord_ok (ok s1 r91 wr1)) fun s2 ⟨x2, rd2, wr2, g2, f2⟩ => ?_)
    rw [reg s1 r91] at f2
    refine WP.mono (rotTail_ok (B := B) (k := (i - 1) / nk) d2 (by rw [g2 _ w9, r91]) (by rw [wr2, wr1]; exact hB) ?_)
      fun s3 ⟨x3, rc3, rd3, wr3, g3, f3⟩ => ⟨?_, by rw [d1]; exact rc3, fun r hr => by rw [g3 r hr, g2 r hr, g1 r (nax r hr).1],
        rd3.trans (rd2.trans rd1), wr3.trans (wr2.trans wr1), ?_⟩
    · rw [f2.readW (r := ⟨B + BitVec.ofNat 64 432, 8⟩) (Region.contains_self _ _) dd (by decide), m1, h.rc]
    · rw [x3, x2, setWidth_setWidth_32, x1, temp32, ite_eq_left h0, d1]
    · rw [← m1]
      exact (f2.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans f3
  · have h0 : i % nk ≠ 0 := by simpa using h0
    have dv := i_div' hnk h0
    have key2 : ∃ s2, runBlock isa [movR .r10 .rsi, .alu .add .r10 (.reg .r8), .alu .cmp .r10 (.imm 48)] s1 = some s2 ∧
        s2.zf = some (decide (nk > 6 ∧ i % nk = 4)) ∧ (∀ r, r ≠ .r10 → s2.gpr r = s1.gpr r) ∧ s2.mem = s1.mem ∧
        s2.rd = s1.rd ∧ s2.wr = s1.wr := by
      have e48 : BitVec.signExtend 64 (48 : BitVec 32) = BitVec.ofNat 64 48 := by decide
      simp only [movR, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.map_some,
        Option.bind_some, gpr_setReg, gpr_arithFlags, zf_arithFlags, reduceCtorEq, ite_false, ite_true, e48,
        g1 _ (show Reg.rsi ≠ .rax by decide), g1 _ (show Reg.r8 ≠ .rax by decide), h.rsi, h.r8, ← BitVec.ofNat_add,
        Option.some.injEq, exists_eq_left']
      refine ⟨?_, fun r hr => by simp only [hr, ite_false], rfl, rfl, rfl⟩
      rw [sub_beq (by omega) (by decide)]
      refine decide_eq_decide.mpr ?_
      rcases hnk with rfl | rfl | rfl <;> omega
    obtain ⟨s2, e2, z2, g2, m2, rd2, wr2⟩ := key2
    have r92 : s2.gpr .r9 = B := by rw [g2 _ (by decide), r91]
    have x2 : (s2.gpr .rax).setWidth 32 = W s₀.mem kp nk (i - 1) := by rw [g2 _ (by decide), x1]
    refine WP.seq (WP.of_runBlock ⟨s2, e2, WP.ite (decide (nk > 6 ∧ i % nk = 4)) (by simp [X86_64.eval, z2]) (fun h4 => ?_) (fun h4 => ?_)⟩)
    · have h4 := of_decide_eq_true h4
      refine WP.mono (subWord_ok (ok s2 r92 (wr2.trans wr1))) fun s3 ⟨x3, rd3, wr3, g3, f3⟩ => ?_
      rw [reg s2 r92] at f3
      refine ⟨?_, ?_, fun r hr => by rw [g3 r hr, g2 r (nax r hr).2, g1 r (nax r hr).1], rd3.trans (rd2.trans rd1),
        wr3.trans (wr2.trans wr1), ?_⟩
      · rw [x3, setWidth_setWidth_32, x2, temp32, ite_eq_right h0, ite_eq_left h4]
      · rw [f3.readW (r := ⟨B + BitVec.ofNat 64 432, 8⟩) (Region.contains_self _ _) dd (by decide), m2, m1, h.rc, dv]
      · rw [← m1, ← m2]
        exact f3.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self
    · have h4 := of_decide_eq_false h4
      refine WP.block_nil ⟨?_, by rw [m2, m1, h.rc, dv], fun r hr => by rw [g2 r (nax r hr).2, g1 r (nax r hr).1], rd2.trans rd1,
        wr2.trans wr1, by rw [m2, m1]; exact Frame.refl _ _⟩
      rw [x2, temp32, ite_eq_right h0, ite_eq_right h4]

theorem word_ok (hs : ES s₀ B S kp nk) {i : Nat} (hi : nk ≤ i) (hi' : i < 4 * (nk + 7)) {s : State}
    (h : WI s₀ B S kp nk i s) : WP isa word s fun s' => WI s₀ B S kp nk (i + 1) s' ∧
      X86_64.eval .ne s' = some (decide (4 * (nk + 7) - (i + 1) ≠ 0)) := by
  have hnk := hs.nks
  have h60 : i < 60 := by omega
  obtain ⟨hmod, hm0, hm1⟩ := i_mod (i := i) hnk
  refine WP.seq (WP.mono (temp_ok hs hi hi' h) fun s1 h1 => ?_)
  have dT : ∀ r ∈ tR B, Region.Sub r ⟨B, 512⟩ := fun r hr => by
    simp only [tR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by decide)
    · exact fun x hx => by simp only [Region.Contains] at hx ⊢; bv_omega
  have good1 : Good s1.mem S (W s₀.mem kp nk) i := Good.frame h.good (by omega) h1.frame fun r hr => hs.dSB.sub_right (dT r hr)
  have saved1 : Saved s₀ B s1.mem := h.saved.frame h1.frame fun r hr => by
    simp only [tR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint _ (by decide) (by decide)).symm
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have f1 : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s1.mem := h.frame.trans (h1.frame.sub fun r hr =>
    ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, dT r hr⟩)
  have wr1 : s1.wr = s₀.wr := h1.wr.trans h.wr
  have rd1 : s1.rd = s₀.rd := h1.rd.trans h.rd
  have rdx1 : s1.gpr .rdx = S + BitVec.ofNat 64 (4 * i) := by rw [h1.gpr _ (by decide), h.rdx]
  have rsi1 : s1.gpr .rsi = BitVec.ofNat 64 (4 * nk) := by rw [h1.gpr _ (by decide), h.rsi]
  have r81 : s1.gpr .r8 = BitVec.ofNat 64 (4 * (i % nk)) := by rw [h1.gpr _ (by decide), h.r8]
  have rdi1 : s1.gpr .rdi = BitVec.ofNat 64 (4 * (4 * (nk + 7) - i)) := by rw [h1.gpr _ (by decide), h.rdi]
  have hld : InRegions (s1.rd ++ s1.wr) (S + BitVec.ofNat 64 (4 * (i - nk)) + BitVec.ofNat 64 0) 4 := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    exact ⟨_, List.mem_append_right _ (by rw [wr1]; exact hs.inS), Offset.contains_base _ (by omega) (by omega)⟩
  have hst : InRegions s1.wr (S + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 0) 4 := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    exact ⟨_, by rw [wr1]; exact hs.inS, Offset.contains_base _ (by omega) (by omega)⟩
  have esub : S + BitVec.ofNat 64 (4 * i) - BitVec.ofNat 64 (4 * nk) = S + BitVec.ofNat 64 (4 * (i - nk)) := by
    rw [show 4 * i = 4 * (i - nk) + 4 * nk by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 := by decide
  have ea : ∀ (s' : State) (r : Reg), s'.ea (at_ r 0) = s'.gpr r + BitVec.ofNat 64 0 := fun _ _ => rfl
  have key : ∃ s2, runBlock isa [movR .r10 .rdx, .alu .sub .r10 (.reg .rsi), .alu32 .xor .rax (.mem (at_ .r10 0)),
      .store32 (at_ .rdx 0) .rax, .alu .add .rdx (.imm 4), .alu .add .r8 (.imm 4), .alu .cmp .r8 (.reg .rsi)] s1 = some s2 ∧
      s2.mem = s1.mem.writeW (S + BitVec.ofNat 64 (4 * i)) (W s₀.mem kp nk i) ∧
      s2.gpr .rdx = S + BitVec.ofNat 64 (4 * (i + 1)) ∧ s2.gpr .r8 = BitVec.ofNat 64 (4 * (i % nk) + 4) ∧
      s2.zf = some (decide (i % nk + 1 = nk)) ∧ (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rdx → r ≠ .r8 → s2.gpr r = s1.gpr r) ∧
      s2.rd = s1.rd ∧ s2.wr = s1.wr := by
    simp only [movR, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execAlu32, readSrc, readSrc32,
      State.load32, State.store32, State.setReg32, ea, gpr_setReg, gpr_arithFlags, rd_setReg, wr_setReg, mem_setReg,
      rd_arithFlags, wr_arithFlags, mem_arithFlags, zf_arithFlags, reduceCtorEq, ite_false, ite_true, rdx1, rsi1, r81, esub, e4,
      hld, hst, ← BitVec.ofNat_add, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', setWidth_setWidth_32]
    refine ⟨?_, ?_, trivial, ?_, fun r a c d e => by simp only [a, c, d, e, ite_false], trivial, trivial⟩
    · rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.add_zero, good1 _ (by omega), h1.rax,
        W_ge (by omega) hi, BitVec.xor_comm]
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
    · rw [sub_beq (by omega) (by omega)]
      exact decide_eq_decide.mpr (by omega)
  obtain ⟨s2, e2, m2, rdx2, r82, z2, g2, rd2, wr2⟩ := key
  have hw2 : Frame [⟨S, 240⟩] s1.mem s2.mem := by
    rw [m2]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  have dBS : ∀ {d len : Nat}, d + len ≤ 512 → ∀ r ∈ ([⟨S, 240⟩] : List Region), Region.Disjoint ⟨B + BitVec.ofNat 64 d, len⟩ r :=
    fun hd r hr => by
      rw [List.mem_singleton.mp hr]
      refine (hs.dSB.sub_right fun x hx => ?_).symm
      simp only [Region.Contains] at hx ⊢
      rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hx
      have := (x - B).isLt
      omega
  refine WP.seq (WP.of_runBlock ⟨s2, e2, ?_⟩)
  -- The index.
  refine WP.seq (WP.mono (Q := fun s3 : State => s3.gpr .r8 = BitVec.ofNat 64 (4 * ((i + 1) % nk)) ∧ (∀ r, r ≠ .r8 → s3.gpr r = s2.gpr r) ∧
    s3.mem = s2.mem ∧ s3.rd = s2.rd ∧ s3.wr = s2.wr) ?_ fun s3 ⟨r83, g3, m3, rd3, wr3⟩ => ?_)
  · refine WP.ite (decide (i % nk + 1 = nk)) (by simp [X86_64.eval, z2]) (fun hc => ?_) (fun hc => ?_)
    · rw [hm0 (of_decide_eq_true hc)]
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, readSrc32, State.setReg32, Option.map_some,
        Option.some.injEq, exists_eq_left', gpr_setReg, ite_true]
      exact ⟨rfl, fun r hr => by simp only [hr, ite_false], rfl, rfl, rfl⟩
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [r82, hm1 (of_decide_eq_false hc)]; rfl
  have g13 : ∀ r, r ∉ sboxWrites → r ≠ .rdx → r ≠ .r8 → s3.gpr r = s.gpr r := fun r hr a c => by
    obtain ⟨d, e⟩ : r ≠ .rax ∧ r ≠ .r10 := by revert hr; cases r <;> decide
    rw [g3 r c, g2 r d e a c, h1.gpr r hr]
  have ecnt : s3.gpr .rdi - BitVec.ofNat 64 4 = BitVec.ofNat 64 (4 * (4 * (nk + 7) - (i + 1))) := by
    rw [g13 _ (by decide) (by decide) (by decide), h.rdi, show 4 * (4 * (nk + 7) - i) = 4 * (4 * (nk + 7) - (i + 1)) + 4 by omega,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, e4, ecnt, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; rw [g3 _ (by decide), rdx2]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rw [g13 _ (by decide) (by decide) (by decide), h.rsi]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact r83
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rw [g13 _ (by decide) (by decide) (by decide), h.r9]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rw [g13 _ (by decide) (by decide) (by decide), h.rsp]
  · simp only [mem_setReg, mem_arithFlags]
    rw [m3, hw2.readW (r := ⟨B + BitVec.ofNat 64 432, 8⟩) (Region.contains_self _ _) (dBS (by decide)) (by decide), h1.rc]
    rfl
  · simp only [mem_setReg, mem_arithFlags]
    rw [m3]
    exact saved1.frame hw2 (dBS (by decide))
  · simp only [mem_setReg, mem_arithFlags]
    rw [m3, m2]
    exact good_store good1 rfl (by omega)
  · simp only [mem_setReg, mem_arithFlags]
    rw [m3]
    exact f1.trans (hw2.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  · exact rd3.trans (rd2.trans rd1)
  · exact wr3.trans (wr2.trans wr1)
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [ofNat_beq (by omega)]
    simp only [← decide_not]
    exact decide_eq_decide.mpr (by omega)

theorem words_ok (hs : ES s₀ B S kp nk) {s : State} (h : WI s₀ B S kp nk nk s) :
    WP isa (.loop word .ne) s (WI s₀ B S kp nk (4 * (nk + 7))) := by
  let I : Nat → State → Prop := fun c s => ∃ i, c = 4 * (nk + 7) - i ∧ nk ≤ i ∧ i < 4 * (nk + 7) ∧ WI s₀ B S kp nk i s
  refine WP.loop (M := isa) I ?_ _ s ⟨nk, rfl, Nat.le_refl _, by omega, h⟩
  rintro c s' ⟨i, rfl, hi, hi', hs'⟩
  refine WP.mono (word_ok hs hi hi' hs') fun s2 ⟨h2, hz⟩ => ?_
  by_cases hl : 4 * (nk + 7) - (i + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show i + 1 = 4 * (nk + 7) by omega] at h2
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, i + 1, rfl, by omega, by omega, h2⟩

/-! ## The key's words -/

/-- After `j` words of the key. -/
structure KI (s₀ : State) (B S kp : Addr) (nk j : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = S + BitVec.ofNat 64 (4 * j)
  rdi : s.gpr .rdi = kp + BitVec.ofNat 64 (4 * j)
  rsi : s.gpr .rsi = BitVec.ofNat 64 (4 * nk)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * (nk - j))
  r9 : s.gpr .r9 = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : Saved s₀ B s.mem
  good : Good s.mem S (W s₀.mem kp nk) j
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ES.saved_disj (hs : ES s₀ B S kp nk) :
    ∀ r ∈ ([⟨S, 240⟩] : List Region), Region.Disjoint ⟨B + BitVec.ofNat 64 384, 48⟩ r := fun r hr => by
  rw [List.mem_singleton.mp hr]
  refine (hs.dSB.sub_right fun x hx => ?_).symm
  simp only [Region.Contains] at hx ⊢
  bv_omega

theorem keyCopy_ok (hs : ES s₀ B S kp nk) {j : Nat} (hj : j < nk) {s : State} (h : KI s₀ B S kp nk j s) :
    WP isa (.block keyCopy) s fun s' => KI s₀ B S kp nk (j + 1) s' ∧
      X86_64.eval .ne s' = some (decide (nk - (j + 1) ≠ 0)) := by
  have hnk := hs.nks
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 := by decide
  have ea : ∀ (s' : State) (r : Reg), s'.ea (at_ r 0) = s'.gpr r := fun s' r => BitVec.add_zero _
  have hld : InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 (4 * j)) 4 :=
    ⟨_, List.mem_append_left _ (by rw [h.rd]; exact hs.inK), Offset.contains_base _ (by omega) (by omega)⟩
  have hst : InRegions s.wr (S + BitVec.ofNat 64 (4 * j)) 4 :=
    ⟨_, by rw [h.wr]; exact hs.inS, Offset.contains_base _ (by omega) (by omega)⟩
  have ecnt : s.gpr .r8 - BitVec.ofNat 64 4 = BitVec.ofNat 64 (4 * (nk - (j + 1))) := by
    rw [h.r8, show 4 * (nk - j) = 4 * (nk - (j + 1)) + 4 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hv : s.mem.readW (kp + BitVec.ofNat 64 (4 * j)) 32 = W s₀.mem kp nk j := by
    rw [W_lt hj]
    refine h.frame.readW (r := ⟨kp, 4 * nk⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.dKS
    · exact hs.dKB
  have hw : Frame [⟨S, 240⟩] s.mem (s.mem.writeW (S + BitVec.ofNat 64 (4 * j)) (W s₀.mem kp nk j)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  apply WP.of_runBlock
  simp only [keyCopy, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, readSrc32,
    State.load32, State.store32, State.setReg32, ea, gpr_setReg, gpr_arithFlags, wr_setReg, mem_setReg,
    reduceCtorEq, ite_false, ite_true, h.rdx, h.rdi,
    e4, hld, hst, hv, ecnt, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', setWidth_setWidth_32]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.saved.frame hw hs.saved_disj, good_store h.good rfl (by omega),
    h.frame.trans (hw.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self), h.rd, h.wr⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h.rsi
  · simp only [gpr_setReg, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h.r9
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h.rsp
  · show some (!(BitVec.ofNat 64 (4 * (nk - (j + 1))) == 0)) = _
    rw [ofNat_beq (by omega), ← decide_not]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem keyLoop_ok (hs : ES s₀ B S kp nk) {s : State} (h : KI s₀ B S kp nk 0 s) :
    WP isa (.loop (.block keyCopy) .ne) s (KI s₀ B S kp nk nk) := by
  have hnk := hs.nks
  let I : Nat → State → Prop := fun c s => ∃ j, c = nk - j ∧ j < nk ∧ KI s₀ B S kp nk j s
  refine WP.loop (M := isa) I ?_ _ s ⟨0, rfl, by omega, h⟩
  rintro c s' ⟨j, rfl, hj, hs'⟩
  refine WP.mono (keyCopy_ok hs hj hs') fun s2 ⟨h2, hz⟩ => ?_
  by_cases hl : nk - (j + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = nk by omega] at h2
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, j + 1, rfl, by omega, h2⟩

/-! ## The whole function -/

theorem save_ok {s : State} {r9 : Addr} (h9 : s.gpr .r9 = r9) (hB : ⟨r9, 512⟩ ∈ s.wr) :
    WP isa (.block saveRegs) s fun s' => (∀ p ∈ savedRegs, s'.mem.readW (r9 + BitVec.ofNat 64 (8 * p.1)) 64 = s.gpr p.2) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨r9, 512⟩] s.mem s'.mem := by
  have hin : ∀ k < 64, InRegions s.wr (r9 + BitVec.ofNat 64 (8 * k)) 8 := fun k hk =>
    ⟨_, hB, Offset.contains_base _ (by omega) (by omega)⟩
  have ea : ∀ (s' : State) (k : Nat), s'.ea (slotAt sb k) = s'.gpr .r9 + BitVec.ofNat 64 (8 * k) := fun s' k => by
    simp only [State.ea, slotAt, sb, BitVec.ofInt_natCast]
  have go : ∀ (l : List (Nat × Reg)) (s1 : State), (∀ p ∈ l, p.1 < 64) → l.Pairwise (fun a b => a.1 ≠ b.1) →
      s1.gpr = s.gpr → s1.rd = s.rd → s1.wr = s.wr →
      WP isa (.block (l.map fun p => st p.1 p.2)) s1 fun s' => (∀ p ∈ l, s'.mem.readW (r9 + BitVec.ofNat 64 (8 * p.1)) 64 = s.gpr p.2) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame (l.map fun p => ⟨r9 + BitVec.ofNat 64 (8 * p.1), 8⟩) s1.mem s'.mem := by
    intro l
    induction l with
    | nil => exact fun s1 _ _ a c d => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, a, c, d, Frame.refl _ _⟩
    | cons p l ih =>
      intro s1 hl hp a c d
      rw [List.pairwise_cons] at hp
      have hp64 := hl p List.mem_cons_self
      rw [List.map_cons, show st p.1 p.2 :: (l.map fun p => st p.1 p.2) = [st p.1 p.2] ++ (l.map fun p => st p.1 p.2) from rfl]
      refine WP.block_append ?_
      apply WP.of_runBlock
      simp only [st, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, State.store64, ea, a, d, h9, hin _ hp64, ite_true,
        Option.some.injEq, exists_eq_left']
      refine WP.mono (ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hp.2 rfl c rfl) fun s' ⟨h1, h2, h3, h4, h5⟩ => ⟨?_, h2, h3, h4, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · rw [h5.readW (r := ⟨r9 + BitVec.ofNat 64 (8 * q.1), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
          · exact Mem.readW_writeW_self (n := 8) _ _ _ (by decide)
          · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
            have := hp.1 o ho
            have := hl o (List.mem_cons_of_mem _ ho)
            exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact h1 q hq
      · refine ((Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)).trans
          (h5.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.mono (go savedRegs s (by decide) (by decide) rfl rfl rfl) fun s' ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5.sub fun r hr => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨p1, p2⟩ := savedRegs_slot p hp
  refine ⟨_, List.mem_singleton.mpr rfl, fun x hx => ?_⟩
  simp only [Region.Contains] at hx ⊢
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hx
  have := (x - r9).isLt
  omega

theorem restore_ok {s₀ s : State} (hB : ⟨B, 512⟩ ∈ s.wr) (h9 : s.gpr .r9 = B) (h : Saved s₀ B s.mem) :
    WP isa (.block restoreRegs) s fun s' => (∀ p ∈ savedRegs, s'.gpr p.2 = s₀.gpr p.2) ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.mem = s.mem := by
  have hin : ∀ k < 64, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * k)) 8 := fun k hk =>
    ⟨_, List.mem_append_right _ hB, Offset.contains_base _ (by omega) (by omega)⟩
  have ea : ∀ (s' : State) (k : Nat), s'.ea (slotAt sb k) = s'.gpr .r9 + BitVec.ofNat 64 (8 * k) := fun s' k => by
    simp only [State.ea, slotAt, sb, BitVec.ofInt_natCast]
  have v := fun p hp => h p hp
  simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := v
  apply WP.of_runBlock
  simp only [restoreRegs, savedRegs, List.map_cons, List.map_nil, movS, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec,
    readSrc, State.load64, ea, gpr_setReg, rd_setReg, wr_setReg, mem_setReg, reduceCtorEq, ite_false, h9, hin, v0, v1, v2, v3, v4, v5,
    ite_true, Nat.reduceLT, Option.map_some, Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_self]

theorem ek_correct {s₀ : State} (hp : Proof.Aes.expandKeyX86_64.pre s₀) :
    WP isa Impl.Aes.X86_64.expandKey s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Aes.expandKeyX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dRS, dRB, hL⟩ := hp
  obtain ⟨nk, hnk⟩ : ∃ nk, nk = (s₀.gpr .rsi).toNat / 4 := ⟨_, rfl⟩
  have hL4 : (s₀.gpr .rsi).toNat = 4 * nk := by omega
  obtain ⟨B, hB⟩ : ∃ B, B = s₀.gpr .rcx := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = s₀.gpr .rdx := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ kp, kp = s₀.gpr .rdi := ⟨_, rfl⟩
  rw [hL4, ← hkp] at dKS dKB hrd
  rw [← hS] at dKS dSB dRS hwr
  rw [← hB] at dKB dSB dRB hwr
  have hs : ES s₀ B S kp nk := ⟨by omega, by rw [hwr]; simp, by rw [hwr]; simp, by rw [hrd]; simp, dSB, dKS, dKB⟩
  have hnks := hs.nks
  have hsi : s₀.gpr .rsi = BitVec.ofNat 64 (4 * nk) := by rw [← hL4]; simp
  have inBwr : ∀ s : State, s.wr = s₀.wr → ⟨B, 512⟩ ∈ s.wr := fun s h => by rw [h]; exact hs.inB
  -- The prologue.
  refine WP.seq (WP.block_append (WP.block_append ?_))
  have key : ∃ s1, runBlock isa [movR .r9 .rcx] s₀ = some s1 ∧ s1.gpr .r9 = B ∧ (∀ r, r ≠ .r9 → s1.gpr r = s₀.gpr r) ∧
      s1.mem = s₀.mem ∧ s1.rd = s₀.rd ∧ s1.wr = s₀.wr := by
    simp only [movR, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, readSrc, Option.map_some, Option.some.injEq,
      exists_eq_left', gpr_setReg, ite_true, hB]
    exact ⟨trivial, fun r hr => by simp only [hr, ite_false], rfl, rfl, rfl⟩
  obtain ⟨s1, e1, r91, g1, m1, rd1, wr1⟩ := key
  refine WP.of_runBlock ⟨s1, e1, WP.mono (save_ok r91 (inBwr s1 wr1)) fun s2 ⟨sv2, g2, rd2, wr2, f2⟩ => ?_⟩
  have hsv : Saved s₀ B s2.mem := fun p hp => by
    rw [sv2 p hp, g1 _ (by revert p; decide)]
  rw [m1] at f2
  have key3 : ∃ s3, runBlock isa [movR .r8 .rsi] s2 = some s3 ∧ s3.gpr .r8 = BitVec.ofNat 64 (4 * nk) ∧
      (∀ r, r ≠ .r8 → s3.gpr r = s2.gpr r) ∧ s3.mem = s2.mem ∧ s3.rd = s2.rd ∧ s3.wr = s2.wr := by
    simp only [movR, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, readSrc, Option.map_some, Option.some.injEq,
      exists_eq_left', gpr_setReg, ite_true]
    exact ⟨by rw [g2, g1 _ (by decide), hsi], fun r hr => by simp only [hr, ite_false], rfl, rfl, rfl⟩
  obtain ⟨s3, e3, r83, g3, m3, rd3, wr3⟩ := key3
  refine WP.of_runBlock ⟨s3, e3, ?_⟩
  have g13 : ∀ r, r ≠ .r8 → r ≠ .r9 → s3.gpr r = s₀.gpr r := fun r a c => by rw [g3 r a, g2, g1 r c]
  have hK0 : KI s₀ B S kp nk 0 s3 := by
    refine ⟨?_, ?_, ?_, r83, ?_, g13 _ (by decide) (by decide), by rw [m3]; exact hsv, fun i hi => absurd hi (Nat.not_lt_zero _), ?_,
      rd3.trans (rd2.trans rd1), wr3.trans (wr2.trans wr1)⟩
    · rw [g13 _ (by decide) (by decide), hS]; simp
    · rw [g13 _ (by decide) (by decide), hkp]; simp
    · rw [g13 _ (by decide) (by decide), hsi]
    · rw [g3 _ (by decide), g2, r91]
    · rw [m3]; exact f2.mono fun r hr => List.mem_cons_of_mem _ hr
  refine WP.seq (WP.mono (keyLoop_ok hs hK0) fun s4 h4 => ?_)
  have hwB : InRegions s4.wr (B + BitVec.ofNat 64 432) 8 :=
    ⟨_, inBwr s4 h4.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have ea : ∀ s' : State, s'.ea (slotAt sb rcSlot) = s'.gpr .r9 + BitVec.ofNat 64 432 := fun _ => rfl
  have e112 : BitVec.signExtend 64 (112 : BitVec 32) = BitVec.ofNat 64 112 := by decide
  have e1 : BitVec.setWidth 64 (1 : BitVec 32) = rcVal 0 := by decide
  have hwf : Frame [⟨B + BitVec.ofNat 64 432, 8⟩] s4.mem (s4.mem.writeW (B + BitVec.ofNat 64 432) (rcVal 0)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have sub432 : Region.Sub ⟨B + BitVec.ofNat 64 432, 8⟩ ⟨B, 512⟩ := fun x hx => by
    simp only [Region.Contains] at hx ⊢; bv_omega
  have key5 : ∃ s5, runBlock isa [.mov32 .r10 (.imm 1), st rcSlot .r10, .mov32 .r8 (.imm 0), movR .rdi .rsi,
      .alu .add .rdi (.reg .rsi), .alu .add .rdi (.reg .rsi), .alu .add .rdi (.imm 112)] s4 = some s5 ∧
      WI s₀ B S kp nk nk s5 := by
    simp only [movR, st, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, readSrc32,
      State.store64, State.setReg32, ea, gpr_setReg, gpr_arithFlags, wr_setReg, mem_setReg,
      reduceCtorEq, ite_false, ite_true, h4.r9, h4.rsi, e112, e1, hwB, ← BitVec.ofNat_add, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h4.saved.frame hwf ?_, Good.frame h4.good (by omega) hwf ?_, ?_, h4.rd, h4.wr⟩
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h4.rdx
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h4.rsi
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, Nat.mod_self]; rfl
    · simp only [gpr_setReg, ite_true]
      exact congrArg _ (by omega)
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h4.r9
    · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h4.rsp
    · rw [Nat.div_eq_of_lt (by omega)]
      exact Mem.readW_writeW_self (n := 8) _ _ _ (by decide)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact dSB.sub_right sub432
    · exact h4.frame.trans (hwf.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        rw [List.mem_singleton.mp hr]; exact sub432⟩)
  obtain ⟨s5, e5, h5⟩ := key5
  refine WP.seq (WP.of_runBlock ⟨s5, e5, WP.seq (WP.mono (words_ok hs h5) fun s6 h6 => ?_)⟩)
  refine WP.mono (restore_ok (inBwr s6 h6.wr) h6.r9 h6.saved) fun s7 ⟨g7, sp7, m7⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    by_cases hsp : r = .rsp
    · rw [hsp, sp7, h6.rsp]
    · obtain ⟨p, hp, rfl⟩ : ∃ p ∈ savedRegs, p.2 = r := by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hsp | decide
      exact g7 p hp
  · rw [m7]
    refine h6.frame.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRB
  · show Spec.Aes.bytesAt s7.mem (s₀.gpr .rdx) (16 * (Spec.Aes.rounds ((s₀.gpr .rsi).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
    have hr : Spec.Aes.rounds nk = nk + 6 := rfl
    rw [m7, ← hnk, ← hS, ← hkp, hL4, expandKey_eq _ _ (by omega), hr, show 16 * (nk + 6 + 1) = 4 * (4 * (nk + 7)) by omega,
      bytesAt_eq _ _ (W s₀.mem kp nk) _ h6.good]

/-- A state satisfying the precondition. -/
def ekSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyX86_64.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := ek_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub
    Impl.Aes.X86_64.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_verified :
    Verified X86_64.target Impl.Aes.X86_64.expandKey (Proof.Aes.expandKeyScratchContract X86_64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Aes.expandKeyScratchContract, Proof.Aes.expandKeyScratchSig, Proof.Aes.expandKeyX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Aes.X86_64.ekSatState] using Proof.Aes.X86_64.ekSatState)

end VG.Proof.Aes.X86_64
