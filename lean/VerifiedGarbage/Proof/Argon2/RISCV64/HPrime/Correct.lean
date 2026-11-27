module

import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Proof.Argon2.HPrime
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! ### `Argon2.RISCV64.HPrime.Setup`, which this module and modules that import it used -/

section

/-! # H′ on RISC-V: saving the caller's registers and the length prefix

The return address is a register like the callee-saved ones, saved at 880
with them. -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_sw)

/-- The memory after the setup: the saved registers and the length prefix
at 832. -/
def setupMem (s : State) : Mem :=
  (Spill.saveMem s.mem (s.gpr .a4) s.gpr saved).writeW
    (s.gpr .a4 + BitVec.ofNat 64 832) ((s.gpr .a3).setWidth 32)

theorem saved_in : ∀ p ∈ saved, 832 ≤ p.2 ∧ p.2 + 8 ≤ 832 + 64 := by decide

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .a4 + BitVec.ofNat 64 832, 64⟩] s.mem (setupMem s) :=
  (Spill.saveMem_frame saved_in (by decide) _ _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by decide) (by decide) (by decide))

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (setupMem s) (s.gpr .a4 + BitVec.ofNat 64 832) 4 =
      Spec.Argon2.le32 (s.gpr .a3).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem saved_bounds : ∀ p ∈ saved, 840 ≤ p.2 ∧ p.2 + 8 ≤ 888 := by decide

theorem setupMem_saved (s : State) : Spill.Saved (s.gpr .a4) s.gpr saved (setupMem s) := by
  intro p hp
  have hd := saved_bounds p hp
  unfold setupMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)) (by decide)]
  exact Spill.saveMem_saved (by decide) _ _ _ p hp

structure Setup (s t : State) : Prop where
  workspace : t.gpr .s4 = s.gpr .a4
  input : t.gpr .s0 = s.gpr .a0
  length : t.gpr .s1 = s.gpr .a1
  output : t.gpr .s2 = s.gpr .a2
  remaining : t.gpr .s3 = s.gpr .a3
  other : ∀ r, r ≠ .s4 → r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  mem : t.mem = setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem setup_ok (s : State) (hw : (⟨s.gpr .a4, 16384⟩ : Region) ∈ s.wr)
    (hal : (s.gpr .a4).toNat % 8 = 0) :
    WP isa (.block setup) s (Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .a4 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega_using [h])⟩
  unfold setup
  rw [show saved.map (fun (r, d) => Instr.store .d r .a4 d) = Spill.saveCode .a4 saved from rfl]
  refine Spill.save_ok hal saved_fits (fun p hp => write _ _ (by have := saved_in p hp; omega_using [this])) ?_
  generalize hs₀ : ({ s with mem := Spill.saveMem s.mem (s.gpr .a4) s.gpr saved } : State) = s₀
  refine wp_mv fun d hd => wp_mv fun e he => wp_mv fun f hf => wp_mv fun g hg =>
    wp_mv fun h hh => ?_
  have g4 : s₀.gpr .a4 = s.gpr .a4 := by rw [← hs₀]
  refine wp_sw (a := s.gpr .a4 + BitVec.ofNat 64 832) (by decide)
    (by rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, g4])
    (by have h8 := Spill.al8 hal (d := 832) (by decide); omega_using [h8])
    (by rw [hh.wr, hg.wr, hf.wr, he.wr, hd.wr, ← hs₀]; exact write 832 4 (by decide))
    fun t ht => WP.block_nil ?_
  have o : ∀ r, r ≠ .s4 → r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 →
      t.gpr r = s.gpr r := fun r h4 h0 h1 h2 h3 => by
    rw [ht.gpr, hh.other _ h3, hg.other _ h2, hf.other _ h1, he.other _ h0, hd.other _ h4, ← hs₀]
  have ga : ∀ r, r ≠ .s4 → r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s₀.gpr r = s.gpr r :=
    fun _ _ _ _ _ _ => by rw [← hs₀]
  refine ⟨?_, ?_, ?_, ?_, ?_, o, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, g4]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide), he.gpr,
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.gpr, he.other _ (by decide),
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.gpr, hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [ht.gpr, hh.gpr, hg.other _ (by decide), hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · have a3 : h.gpr .a3 = s.gpr .a3 := by
      rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
        he.other _ (by decide), hd.other _ (by decide),
        ga _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [ht.mem, a3, hh.mem, hg.mem, hf.mem, he.mem, hd.mem, ← hs₀]
    rfl
  · rw [ht.rd, hh.rd, hg.rd, hf.rd, he.rd, hd.rd, ← hs₀]
  · rw [ht.wr, hh.wr, hg.wr, hf.wr, he.wr, hd.wr, ← hs₀]
  · rw [ht.sp, hh.sp, hg.sp, hf.sp, he.sp, hd.sp, ← hs₀]

/-- Restoring the return address and the caller's registers. -/
theorem restore_ok (original s : State) (base : s.gpr .s4 = original.gpr .a4)
    (hal : (original.gpr .a4).toNat % 8 = 0)
    (extra : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → s.gpr r = original.gpr r)
    (readable : (⟨original.gpr .a4, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : Spill.Saved (original.gpr .a4) original.gpr saved s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = original.gpr r) ∧ t.gpr .ra = original.gpr .ra ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .a4 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega_using [h])⟩
  rw [show restore = Spill.restoreCode .s4 saved from rfl]
  refine WP.mono (Spill.restore_wp (b := .s4) hal base saved_fits (by decide)
    (fun p (hp : p ∈ saved) => read _ (by have := saved_bounds p hp; omega_using [this])) values) fun t ht => ?_
  refine ⟨fun r hr => ht.gpr_of ?_, ht.gpr (.ra, 880) (by decide), ht.mem, ht.rd, ht.wr, ht.sp⟩
  by_cases hm : r ∈ saved.map Prod.fst
  · exact .inl hm
  · exact .inr (extra r hr hm)

end VG.Proof.Argon2.RISCV64.HPrime

end

end

/-! ### `Argon2.RISCV64.HPrime.Space`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.HPrime.Chain`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.HPrime.Compare`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.HPrime.Length`, which this module and modules that import it used -/

section

/-! # H′: selecting the first digest length -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_mv wp_subi wp_li Upd eval_nonzero)

/-- A bounded public output length can be compared using the high bit of
its subtraction, without adding flag-based branches to the ISA. -/
theorem below65 (x : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    (x - 65) >>> (63 : Nat) = if x.toNat < 65 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  by_cases h : x.toNat < 65
  · rw [ite_eq_left h, BitVec.toNat_sub_of_lt (by rw [BitVec.lt_def]; exact h)]
    simp only [show (65 : BitVec 64).toNat = 65 from rfl,
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.reducePow]
    omega
  · rw [ite_eq_right h, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_not_gt h)]
    simp only [show (65 : BitVec 64).toNat = 65 from rfl,
      show (0 : BitVec 64).toNat = 0 from rfl]
    omega

theorem Keeps.of_upd {s t : State} {d : Reg} {v : BitVec 64}
    (h : Upd s t d v) (hd : d ∉ preserved) : Keeps s t := by
  refine ⟨fun r hr => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · intro he; subst r; exact hd hr
  · rw [h.mem]; exact Frame.refl _ _

theorem chooseLength_ok (s : State) (hb : (s.gpr .s3).toNat < 2 ^ 32) :
    WP isa chooseLength s fun t =>
      t.gpr .a1 = BitVec.ofNat 64 (min (s.gpr .s3).toNat 64) ∧ Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mv fun a ha => wp_subi (by decide) fun b hb' =>
    wp_srl (by decide) fun u hu => WP.block_nil ?_)
  have ku : Keeps s u :=
    (Keeps.of_upd ha (by decide)).trans
      ((Keeps.of_upd hb' (by decide)).trans (Keeps.of_upd hu (by decide)))
  have n : u.gpr .a1 = s.gpr .s3 := by
    rw [hu.other _ (by decide), hb'.other _ (by decide), ha.gpr]
  have comparison : u.gpr .a7 = if (s.gpr .s3).toNat < 65 then 1 else 0 := by
    rw [hu.gpr, hb'.gpr, ha.gpr]
    exact below65 _ hb
  have flag : isa.eval (.nonzero .a7) u = some (decide ((s.gpr .s3).toNat < 65)) := by
    show VG.RISCV64.eval (.nonzero .a7) u = _
    by_cases hn : (s.gpr .s3).toNat < 65 <;>
      simp [eval_nonzero, comparison, hn]
  refine WP.ite (decide ((s.gpr .s3).toNat < 65)) flag ?_ ?_
  · intro h
    have hn : (s.gpr .s3).toNat ≤ 64 := by have := of_decide_eq_true h; omega_using [this]
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .s3).toNat := by have := of_decide_eq_false h; omega_using [this]
    refine wp_li (by decide) fun t ht => WP.block_nil ?_
    refine ⟨?_, ku.trans (Keeps.of_upd ht (by decide))⟩
    rw [Nat.min_eq_right hn]; exact ht.gpr

end VG.Proof.Argon2.RISCV64.HPrime

end

end

/-! # H′: a bounded public length comparison -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64
open VG.RISCV64.Wp (wp_subi)

structure Compared (s t : State) : Prop where
  value : t.gpr .a7 = if (s.gpr .s3).toNat < 65 then 1 else 0
  other : ∀ r, r ≠ .a7 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem compare_ok (s : State) (hb : (s.gpr .s3).toNat < 2 ^ 32) :
    WP isa (.block Impl.Argon2.RISCV64.HPrime.cmpLeft) s (Compared s) := by
  unfold Impl.Argon2.RISCV64.HPrime.cmpLeft
  refine wp_subi (by decide) fun a ha => wp_srl (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, fun r hr => (ht.other r hr).trans (ha.other r hr), ht.mem.trans ha.mem,
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  rw [ht.gpr, ha.gpr]
  exact below65 _ hb

theorem Compared.keeps {s t : State} (h : Compared s t) : Keeps s t := by
  refine ⟨fun r hr => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · exact fun h => by subst h; exact absurd hr (by decide)
  · rw [h.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.RISCV64.HPrime

end

end

/-! ### `Argon2.RISCV64.HPrime.Output`, which this module and modules that import it used -/

section

/-! # H′: emitting a digest or its 32-byte prefix -/

@[expose] public section

/-! # H′: copying digest bytes -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_lbu wp_sb wp_addi wp_subi eval_nonzero)

theorem copyByte_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a2) 1)
    (hw : InRegions s.wr (s.gpr .s2) 1) :
    WP isa (.block copyByte) s fun t =>
      t.mem = s.mem.writeW (s.gpr .s2) (s.mem (s.gpr .a2)) ∧
      t.gpr .a2 = s.gpr .a2 + 1 ∧ t.gpr .s2 = s.gpr .s2 + 1 ∧
      t.gpr .a6 = s.gpr .a6 - 1 ∧
      (∀ r, r ≠ .a6 → r ≠ .a3 → r ≠ .a2 → r ≠ .s2 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold copyByte
  refine wp_lbu (a := s.gpr .a2) (by decide) (BitVec.add_zero _) hr fun a ha => ?_
  refine wp_sb (a := s.gpr .s2) (by decide) (by rw [ha.other _ (by decide)]; exact BitVec.add_zero _)
    (by rw [ha.wr]; exact hw) fun c hc => ?_
  refine wp_addi (by decide) fun d hd => wp_addi (by decide) fun e he =>
    wp_subi (by decide) fun t ht => WP.block_nil ?_
  have o : ∀ r, r ≠ .a6 → r ≠ .a3 → r ≠ .a2 → r ≠ .s2 → t.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [ht.other _ h1, he.other _ h4, hd.other _ h3, hc.gpr, ha.other _ h2]
  refine ⟨?_, ?_, ?_, ?_, o, ?_, ?_, ?_⟩
  · rw [ht.mem, he.mem, hd.mem, hc.mem, ha.gpr, ha.mem]
    congr 1
    ext i hi
    simp
  · rw [ht.other _ (by decide), he.other _ (by decide), hd.gpr, hc.gpr, ha.other _ (by decide)]; rfl
  · rw [ht.other _ (by decide), he.gpr, hd.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl
  · rw [ht.gpr, he.other _ (by decide), hd.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl
  · rw [ht.rd, he.rd, hd.rd, hc.rd, ha.rd]
  · rw [ht.wr, he.wr, hd.wr, hc.wr, ha.wr]
  · rw [ht.sp, he.sp, hd.sp, hc.sp, ha.sp]

open VG.WriteBytes
open VG.Spec.Blake2 (bytesAt)

/-- The prefix already copied, with every other register preserved. -/
structure CopyI (s₀ : State) (src dst : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ k
  source : s.gpr .a2 = src + BitVec.ofNat 64 j
  destination : s.gpr .s2 = dst + BitVec.ofNat 64 j
  count : s.gpr .a6 = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .a6 → r ≠ .a3 → r ≠ .a2 → r ≠ .s2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem copyLoop_ok (s₀ : State) (src dst : Addr) (k : Nat)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 64)
    (hs : s₀.gpr .a2 = src) (hd : s₀.gpr .s2 = dst)
    (hn : s₀.gpr .a6 = BitVec.ofNat 64 k)
    (hr : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < k, InRegions s₀.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : Region.Disjoint ⟨src, k⟩ ⟨dst, k⟩) :
    WP isa (.loop (.block copyByte) (.nonzero .a6)) s₀ (CopyI s₀ src dst k k) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = k - j ∧ j < k ∧ CopyI s₀ src dst k j s)
    ?_ k s₀ ⟨0, by omega_using [], hk, by omega_using [], by simpa using hs, by simpa using hd,
      by simpa using hn, fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hlen : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  have htake : ((bytesAt s₀.mem src k).take j).length = j := by
    rw [List.length_take, hlen, Nat.min_eq_left (by omega_using [hj])]
  have hb : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    apply (writeBytes_frame s₀.mem dst _ (R := ⟨dst, k⟩)
      (by simpa only [BitVec.add_zero, htake] using
        (Offset.contains_base dst (k := k) (d := 0) (n := j) (by omega_using [hj]) (by decide)))).bytes
        (R := ⟨src, k⟩) _ (show k ≤ 2 ^ 64 by omega_using [hk']) hj
    simpa using hsep
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .a2) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .s2) 1 := by
    rw [h.wr, h.destination]; exact hw j hj
  refine (copyByte_ok s hr' hw').mono ?_
  rintro t ⟨hm, hs', hd', hn', ho, hrd, hwr, -⟩
  have hc : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hj] : 1 ≤ k - j)]
    congr 1
  have hi : CopyI s₀ src dst k (j + 1) t := by
    refine ⟨by omega_using [hj], ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, hrd.trans h.rd, hwr.trans h.wr, ?_⟩
    · rw [hs', h.source, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hd', h.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hn', h.count, hc]
    · exact (ho r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4)
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega_using [hj, hlen]
      rw [hm, h.source, h.destination, hb, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [htake]; omega_using [hk', hj]), htake]
      refine congrArg (fun b => (writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)).writeW
        (dst + BitVec.ofNat 64 j) b) ?_
      simp only [bytesAt, List.getElem_map, List.getElem_range]
  have hz' : (t.gpr .a6 == 0) = decide (k - (j + 1) = 0) := by
    rw [hi.count]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk'] : k - (j + 1) < 2 ^ 64),
        show (0 : BitVec 64).toNat = 0 from rfl] using ht
    · intro he; rw [he]; rfl
  by_cases he : j + 1 = k
  · refine .inl ⟨?_, he ▸ hi⟩
    simp only [VG.RISCV64.eval, bne, hz', show k - (j + 1) = 0 by omega_using [he], decide_true, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], hi⟩
    simp only [VG.RISCV64.eval, bne, hz', show k - (j + 1) ≠ 0 by omega_using [hj, he], decide_false, Bool.not_false]

end VG.Proof.Argon2.RISCV64.HPrime

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_mv wp_addi wp_li wp_subi)
open VG.Spec.Blake2 (bytesAt)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn, hi] : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

structure Copied (s : State) (k : Nat) (t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .a6 → r ≠ .a3 → r ≠ .a2 → r ≠ .s2 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .s2) (bytesAt s.mem (s.gpr .s4 + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .a6 = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4 + 768, k⟩ : Region).Disjoint ⟨s.gpr .s2, k⟩) :
    WP isa copy s (Copied s k) := by
  unfold copy
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  have src : u.gpr .a2 = s.gpr .s4 + 768 := by rw [hu.gpr]; rfl
  have other : ∀ r, r ≠ .a2 → u.gpr r = s.gpr r := fun r hr => hu.other r hr
  have mem : u.mem = s.mem := hu.mem
  have rd : u.rd = s.rd := hu.rd
  have wr : u.wr = s.wr := hu.wr
  have read : ∀ i < k, InRegions (u.rd ++ u.wr)
      (s.gpr .s4 + 768 + BitVec.ofNat 64 i) 1 := by
    intro i hi'
    rw [rd, wr, BitVec.add_assoc,
      show (768 : Addr) = BitVec.ofNat 64 768 from rfl, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ work,
      Offset.contains_base _ (by omega_using [hi, hi'] : 768 + i + 1 ≤ 16384) (by omega_using [hi, hi'])⟩
  have loop := copyLoop_ok u _ _ k lo (by omega_using [hi]) src (other .s2 (by decide))
    ((other .a6 (by decide)).trans count) read
    (by intro i hi'; rw [wr]; exact out i hi') sep
  obtain ⟨tr, t, he, ht⟩ := loop
  refine ⟨tr, t, he, ht.destination,
    fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
    ht.rd.trans rd, ht.wr.trans wr, (VG.RISCV64.Exec.sp he).trans hu.sp, ?_⟩
  rw [ht.mem, mem, List.take_of_length_le]
  simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : Copied s k t) :
    Frame [⟨s.gpr .s2, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .s2) (d := 0) (n := k) (k := k) (by omega_using []) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + 32
  remaining : t.gpr .s3 = s.gpr .s3 - 32
  other : ∀ r, r ≠ .a6 → r ≠ .a3 → r ≠ .a2 → r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .s2) (bytesAt s.mem (s.gpr .s4 + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4 + 768, 32⟩ : Region).Disjoint ⟨s.gpr .s2, 32⟩) :
    WP isa emitPrefix s (Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have base : a.gpr .s4 = s.gpr .s4 := ha.other _ (by decide)
  have dst : a.gpr .s2 = s.gpr .s2 := ha.other _ (by decide)
  have workA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .s2 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .s4 + 768, 32⟩ : Region).Disjoint ⟨a.gpr .s2, 32⟩ := by
    rw [base, dst]; exact sep
  refine WP.seq ((copy_ok a 32 (by decide) (by decide) ha.gpr workA outA sepA).mono ?_)
  intro u hu
  refine wp_subi (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ht.rd.trans (hu.rd.trans ha.rd),
    ht.wr.trans (hu.wr.trans ha.wr), ht.sp.trans (hu.sp.trans ha.sp), ?_⟩
  · rw [ht.other _ (by decide), hu.output, dst]; rfl
  · rw [ht.gpr, hu.other _ (by decide) (by decide) (by decide) (by decide), ha.other _ (by decide)]
    rfl
  · exact (ht.other r h5).trans ((hu.other r h1 h2 h3 h4).trans (ha.other r h1))
  · rw [ht.mem, hu.mem, ha.mem, base, dst]

theorem Emitted.frame {s t : State} (h : Emitted s t) :
    Frame [⟨s.gpr .s2, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .s2) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : Emitted s t)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32⟩) :
    bytesAt t.mem (s.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .s4 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))

end VG.Proof.Argon2.RISCV64.HPrime

end

end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.Next`. -/

@[expose] public section

section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.RISCV64.Wp (wp_li)

theorem next_ok (s : State)
    (hlen : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 64)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    WP isa (next) s fun t =>
      (bytesAt t.mem (s.gpr .s4 + 768) 64).take (s.gpr .a1).toNat =
        Spec.Argon2.H (s.gpr .a1).toNat (bytesAt s.mem (s.gpr .s4 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
    rw [ka.s4]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .s4 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .a1).toNat 0) a.mem (a.gpr .s4) [] := by
    rw [ka.s4]; exact reprA
  have wrA' : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [ka.s4, ka.wr]; exact hwr
  refine WP.seq ((absorbFixed_ok a _ 768 64 (by decide) (by decide) (by decide) (by decide) reprA' wrA').mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .a1).toNat 0) u.mem (u.gpr .s4)
      (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    rw [ku.s4]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_li (by decide) fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · exact hw.other r (preserved_ne hr)
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .a1).toNat 0) w.mem (w.gpr .s4)
      (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    rw [hw.mem, kw.s4]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .s4 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .a1 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .s4 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .s4 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .s4, 16384⟩ : Region) ∈ w.wr := by rw [ksw.s4, ksw.wr]; exact hwr
  refine (finalize_ok w _ _ reprW count bound wrW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .a1).toNat) out
  rw [ksw.s4] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_li)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + 32
  remaining : t.gpr .s3 = s.gpr .s3 - 32
  regs : ∀ r ∈ preserved, r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .s4, 832⟩, ⟨s.gpr .s2, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .s4 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .s4 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .s2) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .s4 + 768) 64)).take 32
  comparison : t.gpr .a7 = if (s.gpr .s3 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (s : State)
    (remainingBound : 32 ≤ (s.gpr .s3).toNat ∧ (s.gpr .s3).toNat < 2 ^ 32)
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32⟩) :
    WP isa (.seq (.block [.li .a1 64]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      s (ChainStep s) := by
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [ka.s4, ka.wr]; exact work
  have lengthA : (a.gpr .a1).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok a (by rw [lengthA]; decide) workA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .s2 = s.gpr .s2 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .s4 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    simpa only [lengthA, ka.s4, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [ksu.s4, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .s2 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .s4 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .s2, 32⟩ := by
    rw [ksu.s4, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .s3).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .s2, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), compared.sp.trans (hw.sp.trans ksu.sp), ?_, ?_, ?_, ?_⟩
  · rw [gt _ (by decide), hw.output, dstU]
  · rw [gt _ (by decide), hw.remaining, ksu.regs _ (by decide)]
  · rw [gt r (preserved_ne hr)]
    exact (hw.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr) h14 h15).trans
      (ksu.regs r hr)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ hr, fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .s4 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.s4, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide)]

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)
open VG.RISCV64.Wp (eval_zero)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .s3 = s.gpr .s3 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ preserved, r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .s4, 832⟩, ⟨s.gpr .s2, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .s4 + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .s2) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .s4 (by decide) (by decide) (by decide)
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_arith
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .s4, 832⟩,
      ⟨s.gpr .s2 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .s4, 832⟩,
        ⟨s.gpr .s2 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .s4, 832⟩, ⟨s.gpr .s2, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h1 h2 => (tail.regs r hr h1 h2).trans (step.regs r hr h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, tail.sp.trans step.sp, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega_arith) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_arith) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .s2) 32 = bytesAt u.mem (s.gpr .s2) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .s2, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (show 832 ≤ 16384 by decide))).symm.sub_left
          (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega_arith)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rw [Proof.Argon2.chainPrefixes]

theorem chain_ok (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 32)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, 32 * n⟩) :
    WP isa (chain) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega_arith
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_arith)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok s
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) work out32 sep32
    have base := step.regs .s4 (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
    have compareU : u.gpr .a7 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .a7) u = some false := by
        show VG.RISCV64.eval (.zero .a7) u = _
        simp [eval_zero, compareU, show lastLen < 65 by omega_arith]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_arith) sep⟩
    | succ n =>
      have workU : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .s2 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_arith)
      have suffix : Region.Sub ⟨u.gpr .s2, 32 * (n + 1)⟩ ⟨s.gpr .s2, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_arith : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .s4, 16384⟩ : Region).Disjoint ⟨u.gpr .s2, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_arith) (by omega_arith) countU workU outU sepU
      have flag : isa.eval (.zero .a7) u = some true := by
        show VG.RISCV64.eval (.zero .a7) u = _
        simp [eval_zero, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_arith]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_arith) sep⟩

end VG.Proof.Argon2.RISCV64.HPrime

end

end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.Written`. -/

@[expose] public section

section
/-! # H′: composing output fragments -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64
open VG.Spec.Blake2 (bytesAt)

/-- An output fragment, allowing hashing in the workspace between writes. -/
structure Written (s : State) (xs : List Byte) (t : State) : Prop where
  output : t.gpr .s2 = s.gpr .s2 + BitVec.ofNat 64 xs.length
  regs : ∀ r ∈ preserved, r ≠ .s2 → r ≠ .s3 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .s4, 832⟩, ⟨s.gpr .s2, xs.length⟩] s.mem t.mem
  bytes : bytesAt t.mem (s.gpr .s2) xs.length = xs

theorem Written.s4 {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .s4 = s.gpr .s4 := h.regs _ (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : Keeps s t) : Written s [] t := by
  refine ⟨?_, fun r hr _ _ => h.regs r hr, h.rd, h.wr, h.sp, ?_, rfl⟩
  · exact (h.regs .s2 (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : Written u xs t)
    (k : Keeps s u) : Written s xs t := by
  have dst := k.regs .s2 (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h1 h2 => (h.regs r hr h1 h2).trans (k.regs r hr),
    h.rd.trans k.rd, h.wr.trans k.wr, h.sp.trans k.sp, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .s4, 832⟩,
        ⟨s.gpr .s2, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.s4] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : Copied s k t) (hk : k < 2 ^ 64) :
    Written s (bytesAt s.mem (s.gpr .s4 + 768) k) t := by
  have len : (bytesAt s.mem (s.gpr .s4 + 768) k).length = k := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 _ => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · exact h.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr) h14
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ hr, fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : Emitted s t) :
    Written s (bytesAt s.mem (s.gpr .s4 + 768) 32) t := by
  have len : (bytesAt s.mem (s.gpr .s4 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 h15 => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · exact h.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr) h14 h15
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ hr, fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : ChainResult s n t) :
    Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, h.sp, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : Written s xs u)
    (last : Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, xs.length + ys.length⟩) :
    Written s (xs ++ ys) t := by
  have tf : Frame [⟨s.gpr .s4, 832⟩,
      ⟨s.gpr .s2 + BitVec.ofNat 64 xs.length, ys.length⟩] u.mem t.mem := by
    rw [← first.s4, ← first.output]; exact last.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ xs.length + ys.length)
      (h : Frame [⟨s.gpr .s4, 832⟩,
        ⟨s.gpr .s2 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .s4, 832⟩,
        ⟨s.gpr .s2, (xs ++ ys).length⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        Offset.sub_base _ (by simpa only [List.length_append] using hk)⟩
  refine ⟨?_, fun r hr h1 h2 => (last.regs r hr h1 h2).trans (first.regs r hr h1 h2),
    last.rd.trans first.rd, last.wr.trans first.wr, last.sp.trans first.sp, ?_, ?_⟩
  · rw [last.output, first.output, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  · exact (extend 0 xs.length (by omega_using []) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega_using []) tf)
  · have before : bytesAt t.mem (s.gpr .s2) xs.length = bytesAt u.mem (s.gpr .s2) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .s2, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega_using [bound]) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (show 832 ≤ 16384 by decide))).symm.sub_left
          (Region.sub_prefix (show xs.length ≤ xs.length + ys.length by omega_using []))
      · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [bound])
    rw [List.length_append, Proof.Blake2.bytesAt_add, before, first.bytes, ← first.output, last.bytes]

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_mv)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 32
  work : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .s2 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .s4, 16384⟩ : Region).Disjoint ⟨s.gpr .s2, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .s2, k⟩ ⟨s.gpr .s2, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega_using [size, this], ?_, ?_, ?_⟩
  · rw [written.wr, written.s4]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega_using [size, hi])
  · rw [written.s4]; exact h.sep.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega_using [hk, this], h.work, fun i hi => h.out i (by omega_using [hk, hi]),
    h.sep.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega_using [size, this])
    (h.sep.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .s3 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .s4 + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mv fun a ha => WP.block_nil ?_)
  have base := ha.other .s4 (by decide)
  have dst := ha.other .s2 (by decide)
  have workA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .s2 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .s4 + 768, n⟩ : Region).Disjoint ⟨a.gpr .s2, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega_using [hi] : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht (by have := space.bound; omega_using [hi])
  refine ⟨?_, fun r hr h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, result.sp.trans ha.sp, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · exact (result.regs r hr h1 h2).trans (ha.other r (preserved_ne hr))
  · simpa only [base, dst, ha.mem] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.RISCV64.HPrime

end

end

/-! ### `Argon2.RISCV64.HPrime.Contract`, which this module and modules that import it used -/

section

/-!
# H′ on RISC-V: its contract

`vg_argon2_hprime` is an internal function, which only the derivation
calls, with its rounded scratch: the contract its proof is of, and the
derivation's proof composes, states that `scratch` is 8-byte aligned. H′ uses
no stack.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64

def inputR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .a4, 16384⟩

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .a1).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat < 2 ^ 32 ∧
    (s.gpr .a4).toNat % 8 = 0 ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat =
    Spec.Argon2.hPrime (s.gpr .a3).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s t := s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧
    s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧ s.gpr .a4 = t.gpr .a4 ∧ s.sp = t.sp

end VG.Proof.Argon2.RISCV64.HPrime

end

end

@[expose] public section

/-! Merged from `Proof.Argon2.RISCV64.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.RISCV64.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.RISCV64.Wp (wp_mv wp_addi)

theorem finishInput_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .s4) d)
    (length : d.length = 4 + (s.gpr .s1).toNat) (bound : (s.gpr .s1).toNat < 2 ^ 32)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    WP isa (finishInput) s fun t =>
      bytesAt t.mem (s.gpr .s4 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  obtain ku : Keeps s u := Keeps.of_upd hu (by decide)
  obtain repr' : Repr b h0 u.mem (u.gpr .s4) d := by rw [hu.mem, ku.s4]; exact repr
  obtain count : u.gpr .a1 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  obtain len : d.length < 2 ^ 64 := by rw [length]; omega_arith
  obtain wr : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [ku.s4, ku.wr]; exact hwr
  refine (finalize_ok u h0 d repr' count len wr).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', finalize_frame _ frame⟩⟩
  simpa only [ku.s4] using out

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (s : State)
    (hlen : 1 ≤ (s.gpr .s3).toNat ∧ (s.gpr .s3).toNat < 2 ^ 32)
    (len : (s.gpr .s1).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .s4 + 832) 4 = Spec.Argon2.le32 (s.gpr .s3).toNat)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .s0, (s.gpr .s1).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .s0, (s.gpr .s1).toNat⟩ : Region).Disjoint ⟨s.gpr .s4, 16384⟩) :
    WP isa (first) s fun t =>
      (bytesAt t.mem (s.gpr .s4 + 768) 64).take (min (s.gpr .s3).toNat 64) =
        Spec.Argon2.H (min (s.gpr .s3).toNat 64)
          (Spec.Argon2.le32 (s.gpr .s3).toNat ++ bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  obtain na : (a.gpr .a1).toNat = min (s.gpr .s3).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain wrA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by rw [ka.s4, ka.wr]; exact hwr
  obtain lenA : 1 ≤ (a.gpr .a1).toNat ∧ (a.gpr .a1).toNat ≤ 64 := by rw [na]; omega_arith
  refine WP.seq ((init_ok a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  obtain ku : Keeps a u := ⟨regsU, rdU, wrU, spU, init_frame _ frameU⟩
  obtain ksu := ka.trans ku
  obtain reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .s3).toNat 64) 0) u.mem (u.gpr .s4) [] := by
    rw [ku.s4]; simpa only [na] using reprU
  obtain wrU' : (⟨u.gpr .s4, 16384⟩ : Region) ∈ u.wr := by rw [ksu.s4, ksu.wr]; exact hwr
  obtain headU : bytesAt u.mem (u.gpr .s4 + 832) 4 = Spec.Argon2.le32 (s.gpr .s3).toNat := by
    rw [ksu.s4, ksu.prefix]; exact headBytes
  refine WP.seq ((absorbFixed_ok u _ 832 4 (by decide) (by decide) (by decide) (by decide) reprU' wrU').mono ?_)
  rintro w ⟨reprW, kw⟩
  obtain ksw := ksu.trans kw
  obtain r12 : w.gpr .s0 = s.gpr .s0 := ksw.regs _ (by decide)
  obtain r13 : w.gpr .s1 = s.gpr .s1 := ksw.regs _ (by decide)
  obtain headLen : (Spec.Argon2.le32 (s.gpr .s3).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  obtain reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .s3).toNat 64) 0) w.mem (w.gpr .s4)
      (Spec.Argon2.le32 (s.gpr .s3).toNat) := by
    rw [kw.s4]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  obtain wrW : (⟨w.gpr .s4, 16384⟩ : Region) ∈ w.wr := by rw [ksw.s4, ksw.wr]; exact hwr
  obtain dataW : Covers [⟨w.gpr .s0, (w.gpr .s1).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  obtain dwW : (⟨w.gpr .s0, (w.gpr .s1).toNat⟩ : Region).Disjoint ⟨w.gpr .s4, 16384⟩ := by
    rw [r12, r13, ksw.s4]; exact dataWork
  obtain inputW : bytesAt w.mem (w.gpr .s0) (w.gpr .s1).toNat =
      bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .s1).toNat ≤ 2 ^ 64 by omega_arith)
      (dataWork.sub_right (Region.sub_prefix (show 832 ≤ 16384 by decide)))
  refine WP.seq ((absorbInput_ok w _ _ headLen reprW' (by rw [r13]; exact len)
    wrW dataW dwW).mono ?_)
  rintro x ⟨reprX, kx⟩
  obtain ksx := ksw.trans kx
  obtain reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .s3).toNat 64) 0) x.mem (x.gpr .s4)
      (Spec.Argon2.le32 (s.gpr .s3).toNat ++ bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat) := by
    rw [kx.s4]; simpa only [inputW] using reprX
  obtain r13X : x.gpr .s1 = s.gpr .s1 := ksx.regs _ (by decide)
  obtain length : (Spec.Argon2.le32 (s.gpr .s3).toNat ++ bytesAt s.mem (s.gpr .s0) (s.gpr .s1).toNat).length =
      4 + (x.gpr .s1).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  obtain wrX : (⟨x.gpr .s4, 16384⟩ : Region) ∈ x.wr := by rw [ksx.s4, ksx.wr]; exact hwr
  refine (finishInput_ok x _ _ reprX' length (by rw [r13X]; exact len) wrX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  obtain result := congrArg (List.take (min (s.gpr .s3).toNat 64)) out
  rw [ksx.s4] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! Merged from `Proof.Argon2.RISCV64.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.RISCV64.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (wp_mv)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen))
    (comparison : s.gpr .a7 = if 32 * n + lastLen < 65 then 1 else 0) :
    WP isa (.ite (.nonzero .a7) (.block []) (chain)) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by by_cases h : 32 * n + lastLen < 65 <;>
    simp [VG.RISCV64.eval, comparison, h]) ?_ ?_
  · intro h
    obtain hn : n = 0 := by have := of_decide_eq_true h; omega_arith
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    obtain hn : 1 ≤ n := by have := of_decide_eq_false h; omega_arith
    obtain p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega_arith)
    exact chain_ok n lastLen s hn last space.bound count p.work p.out p.sep

theorem extendDigest_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .s4 + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .s4 + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64)) ∧
      t.gpr .s3 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  obtain short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega_arith)
  obtain sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  obtain wa := Written.of_emitted ha
  obtain lenA : (bytesAt s.mem (s.gpr .s4 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  obtain spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega_arith)
  obtain countA : a.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
  obtain digestA : bytesAt a.mem (a.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
    rw [wa.s4]; exact ha.digest short.sep
  refine WP.seq ((compare_ok a (by rw [countA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]; exact spaceA.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .s3 = BitVec.ofNat 64 (32 * n + lastLen) :=
    (compared.other _ (by decide)).trans countA
  obtain compareU : u.gpr .a7 = if 32 * n + lastLen < 65 then 1 else 0 := by
    rw [compared.value, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]
  refine WP.seq ((maybeChain_ok n lastLen u (spaceA.keeps ku) last countU compareU).mono ?_)
  intro w hw
  obtain ww := (Written.of_chain hw).before_keeps ku
  obtain digestU : bytesAt u.mem (u.gpr .s4 + 768) 64 = bytesAt s.mem (s.gpr .s4 + 768) 64 := by
    rw [compared.mem, ku.s4]; exact digestA
  obtain ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)) w := by
    simpa only [digestU] using ww
  obtain wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega_arith)
  obtain produced : ((bytesAt s.mem (s.gpr .s4 + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega_arith
  obtain spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  obtain countW : w.gpr .s3 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega_arith : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  obtain digestW : bytesAt w.mem (w.gpr .s4 + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64) := by
    rw [hw.regs .s4 (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mv fun x hx => WP.block_nil ?_)
  obtain kx : Keeps w x := Keeps.of_upd hx (by decide)
  obtain spaceX := spaceW.keeps kx
  obtain lenX : (x.gpr .a1).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceW.bound; omega_arith)]
  refine (next_ok x (by rw [lenX]; omega_arith) spaceX.work).mono ?_
  rintro t ⟨dt, kt⟩
  obtain wwt := Written.of_keeps (kx.trans kt)
  obtain written := space.join wsw wwt (by rw [produced, List.length_nil]; omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.s4, hx.mem, digestW, wsw.s4] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .s3 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .s4 + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  obtain len : ((bytesAt s.mem (s.gpr .s4 + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .s4 + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega_arith
  obtain spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega_arith) last.2 remaining).mono ?_
  intro t copied
  obtain out : bytesAt u.mem (u.gpr .s4 + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .s4 + 768) 64)) := by
    rw [written.s4, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  obtain all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .s3 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .s4 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((compare_ok s (by rw [count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .s3 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  obtain compareU : u.gpr .a7 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [VG.RISCV64.eval, compareU, h]) ?_ ?_
  · intro h
    obtain short : n ≤ 64 := by have := of_decide_eq_true h; omega_arith
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain value : bytesAt u.mem (u.gpr .s4 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.s4, ← bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    obtain long : 64 < n := by have := of_decide_eq_false h; omega_arith
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    obtain bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega_arith)
    change r = q + 1 at hq
    obtain size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    obtain spaceU : Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    obtain countLong : u.gpr .s3 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain digestU : bytesAt u.mem (u.gpr .s4 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.s4]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega_arith), bytesAt_take _ _ 64 64 (by decide)] using digest
    obtain value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .s4 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega_arith)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.RISCV64.HPrime
end

/-! # H′: functional correctness of the complete RISC-V program -/

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (s : State) (pre : localContract.pre s) :
    WP isa code s fun t => localContract.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra ∧
      Frame [outputR s, workR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hal, dw, ow⟩ := pre
  obtain work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work hal).mono ?_)
  intro a ha
  obtain workA : (⟨a.gpr .s4, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  obtain dataA : Covers [⟨a.gpr .s0, (a.gpr .s1).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  obtain dwA : (⟨a.gpr .s0, (a.gpr .s1).toNat⟩ : Region).Disjoint ⟨a.gpr .s4, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  obtain inputA : bytesAt a.mem (a.gpr .s0) (a.gpr .s1).toNat =
      bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .a1).toNat ≤ 2 ^ 64 by omega_arith) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  obtain headA : bytesAt a.mem (a.gpr .s4 + 832) 4 = Spec.Argon2.le32 (a.gpr .s3).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  obtain spaceA : Space a (s.gpr .a3).toNat := by
    refine ⟨hi, workA, ?_, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
  refine WP.seq ((first_ok a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA workA dataA dwA).mono ?_)
  rintro b ⟨digestB, kb⟩
  obtain spaceB := spaceA.keeps kb
  obtain countB : b.gpr .s3 = BitVec.ofNat 64 (s.gpr .a3).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain digestB' : (bytesAt b.mem (b.gpr .s4 + 768) 64).take (min (s.gpr .a3).toNat 64) =
      Spec.Argon2.H (min (s.gpr .a3).toNat 64)
        (Spec.Argon2.le32 (s.gpr .a3).toNat ++ bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    rw [kb.s4]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok b (s.gpr .a3).toNat
    (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  obtain baseB : b.gpr .s4 = s.gpr .a4 := kb.s4.trans ha.workspace
  obtain dstB : b.gpr .s2 = s.gpr .a2 := (kb.regs _ (by decide)).trans ha.output
  obtain wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  obtain frame : Frame [⟨s.gpr .a4, 832⟩, outputR s] a.mem x.mem := by
    obtain fb : Frame [⟨s.gpr .a4, 832⟩, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, dstB, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have keep (d : Nat) (dlo : 832 ≤ d) (dhi : d + 8 ≤ 16384) :
      x.mem.readW (s.gpr .a4 + BitVec.ofNat 64 d) 64 = a.mem.readW (s.gpr .a4 + BitVec.ofNat 64 d) 64 := by
    apply frame.readW (r := ⟨s.gpr .a4 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (Offset.base_disjoint _ dlo (by omega_arith)).symm
    · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
  obtain values : Spill.Saved (s.gpr .a4) s.gpr saved x.mem := by
    intro p hp
    obtain bounds := saved_bounds p hp
    rw [keep p.2 (by omega_arith) (by omega_arith), ha.mem]; exact setupMem_saved s p hp
  obtain baseX := (hx.regs .s4 (by decide) (by decide) (by decide)).trans baseB
  obtain readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX hal (fun r hr hm => ?_) readable values).mono ?_
  · have h : r ≠ .s4 ∧ r ≠ .s0 ∧ r ≠ .s1 ∧ r ≠ .s2 ∧ r ≠ .s3 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun e => hm (by subst e; decide)
    rw [hx.regs r hr h.2.2.2.1 h.2.2.2.2, kb.regs r hr]
    exact ha.other r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  rintro t ⟨regs, ra, mem, _, _, _⟩
  refine ⟨?_, regs, ra, ?_⟩
  · change bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    obtain setupFrame : Frame [outputR s, workR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 64 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_correct (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, lr, _⟩ := code_wp s pre
  exact ⟨tr, t, run, ⟨regs, VG.RISCV64.Exec.sp run, lr⟩, post⟩

end VG.Proof.Argon2.RISCV64.HPrime
