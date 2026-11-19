module

import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Absorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Frame
public import VerifiedGarbage.Proof.Argon2.HPrime
public import VerifiedGarbage.Impl.Argon2.PPC64LE.HPrime
public import VerifiedGarbage.Impl.MdStream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `Argon2.PPC64LE.HPrime.Setup`, which this module and modules that import it used -/

section

/-! # H′ on PPC64LE: saving the caller, the return address and the length prefix -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (Upd wp_mov wp_std wp_stw wp_ld)

/-- The memory after the setup: the saved registers, the return address at
880 and the length prefix at 832. -/
def setupMem (s : State) : Mem :=
  ((Spill.saveMem s.mem (s.gpr .r7) s.gpr saved).writeW (s.gpr .r7 + BitVec.ofNat 64 880) s.lr).writeW
    (s.gpr .r7 + BitVec.ofNat 64 832) ((s.gpr .r6).setWidth 32)

theorem saved_in : ∀ p ∈ saved, 832 ≤ p.2 ∧ p.2 + 8 ≤ 832 + 64 := by decide

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .r7 + BitVec.ofNat 64 832, 64⟩] s.mem (setupMem s) :=
  ((Spill.saveMem_frame saved_in (by decide) _ _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by decide) (by decide) (by decide))

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (setupMem s) (s.gpr .r7 + BitVec.ofNat 64 832) 4 =
      Spec.Argon2.le32 (s.gpr .r6).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem saved_bounds : ∀ p ∈ saved, 840 ≤ p.2 ∧ p.2 + 8 ≤ 880 := by decide

theorem setupMem_saved (s : State) (r : Reg) (d : Nat) (hr : (r, d) ∈ saved) :
    (setupMem s).readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  have hd := saved_bounds (r, d) hr
  have h880 : d + 8 ≤ 880 := hd.2
  unfold setupMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inr (by omega)) (by omega_using [h880]) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep _ (Or.inl h880) (by omega_using [h880]) (by decide)) (by decide)]
  exact Spill.saveMem_saved (by decide) _ _ _ (r, d) hr

theorem setupMem_lr (s : State) :
    (setupMem s).readW (s.gpr .r7 + BitVec.ofNat 64 880) 64 = s.lr := by
  unfold setupMem
  rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inr (by decide)) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64]

structure Setup (s t : State) : Prop where
  workspace : t.gpr .r31 = s.gpr .r7
  input : t.gpr .r27 = s.gpr .r3
  length : t.gpr .r28 = s.gpr .r4
  output : t.gpr .r29 = s.gpr .r5
  remaining : t.gpr .r30 = s.gpr .r6
  other : ∀ r, r ≠ .r0 → r ≠ .r31 → r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  mem : t.mem = setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem setup_ok (s : State) (hw : (⟨s.gpr .r7, 16384⟩ : Region) ∈ s.wr) :
    WP isa (.block setup) s (Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega_using [h])⟩
  unfold setup
  rw [show saved.map (fun (r, d) => Instr.store .d r .r7 d) = Spill.saveCode .r7 saved from rfl]
  refine Spill.save_ok (by decide) (by decide) (fun p hp => write _ _ (by have := saved_in p hp; omega_using [this])) ?_
  refine MdStream.PPC64LE.WP.cons exec_mflr ?_
  have u₀ := Upd.write { s with mem := Spill.saveMem s.mem (s.gpr .r7) s.gpr saved } .r0 s.lr
  generalize { s with mem := Spill.saveMem s.mem (s.gpr .r7) s.gpr saved }.write .r0 s.lr = a at u₀
  refine wp_std (a := s.gpr .r7 + BitVec.ofNat 64 880) (by decide) (by rw [u₀.other _ (by decide)])
    (by rw [u₀.wr]; exact write 880 8 (by decide)) fun c hc => ?_
  refine wp_mov fun d hd => wp_mov fun e he => wp_mov fun f hf => wp_mov fun g hg =>
    wp_mov fun h hh => ?_
  refine wp_stw (a := s.gpr .r7 + BitVec.ofNat 64 832) (by decide)
    (by rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, hc.gpr, u₀.other _ (by decide)])
    (by rw [hh.wr, hg.wr, hf.wr, he.wr, hd.wr, hc.wr, u₀.wr]; exact write 832 4 (by decide))
    fun t ht => WP.block_nil ?_
  have o : ∀ r, r ≠ .r0 → r ≠ .r31 → r ≠ .r27 → r ≠ .r28 → r ≠ .r29 → r ≠ .r30 →
      t.gpr r = s.gpr r := fun r h0 h31 h27 h28 h29 h30 => by
    rw [ht.gpr, hh.other _ h30, hg.other _ h29, hf.other _ h28, he.other _ h27, hd.other _ h31,
      hc.gpr, u₀.other _ h0]
  refine ⟨?_, ?_, ?_, ?_, ?_, o, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.gpr, hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide), he.gpr,
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.other _ (by decide), hf.gpr, he.other _ (by decide),
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.other _ (by decide), hg.gpr, hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · rw [ht.gpr, hh.gpr, hg.other _ (by decide), hf.other _ (by decide), he.other _ (by decide),
      hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
  · have r6 : h.gpr .r6 = s.gpr .r6 := by
      rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
        he.other _ (by decide), hd.other _ (by decide), hc.gpr, u₀.other _ (by decide)]
    rw [ht.mem, r6, hh.mem, hg.mem, hf.mem, he.mem, hd.mem, hc.mem, u₀.mem, u₀.gpr]
    rfl
  · rw [ht.rd, hh.rd, hg.rd, hf.rd, he.rd, hd.rd, hc.rd, u₀.rd]
  · rw [ht.wr, hh.wr, hg.wr, hf.wr, he.wr, hd.wr, hc.wr, u₀.wr]
  · rw [ht.sp, hh.sp, hg.sp, hf.sp, he.sp, hd.sp, hc.sp, u₀.sp]

/-- Restoring the return address and the caller's registers. -/
theorem restore_ok (original s : State) (base : s.gpr .r31 = original.gpr .r7)
    (extra : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → s.gpr r = original.gpr r)
    (readable : (⟨original.gpr .r7, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .r7 + BitVec.ofNat 64 d) 64 = original.gpr r)
    (lrSlot : s.mem.readW (original.gpr .r7 + BitVec.ofNat 64 880) 64 = original.lr) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = original.gpr r) ∧ t.lr = original.lr ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .r7 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega_using [h])⟩
  rw [show restore = ([.load .d .r0 .r31 880, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r31 saved
    from rfl, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ld (a := original.gpr .r7 + BitVec.ofNat 64 880) (by decide) (by rw [base])
    (read 880 (by decide)) fun a ha => ?_
  refine MdStream.PPC64LE.WP.cons exec_mtlr ?_
  refine WP.mono (Spill.restore_wp (b := .r31) (B := original.gpr .r7) (g := original.gpr) (by decide)
    (by simp [ha.other _ (by decide : Reg.r31 ≠ .r0), base]) (by decide) (by decide)
    (fun p hp => by
      simp only [ha.rd, ha.wr]
      exact read _ (by have := saved_bounds p hp; omega_using [this]))
    (fun p hp => by simp only [ha.mem]; exact values p.1 p.2 hp)) fun t ht => ?_
  refine ⟨fun r hr => ht.gpr_of ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm : r ∈ saved.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      have h0 : r ≠ .r0 := fun h => by subst h; exact absurd hr (by decide)
      show a.gpr r = _
      rw [ha.other r h0, extra r hr hm]
  · rw [ht.lr]; show a.gpr .r0 = _; rw [ha.gpr, lrSlot]
  · rw [ht.mem]; exact ha.mem
  · rw [ht.rd]; exact ha.rd
  · rw [ht.wr]; exact ha.wr
  · rw [ht.sp]; exact ha.sp

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! ### `Argon2.PPC64LE.HPrime.Space`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.HPrime.Chain`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.HPrime.Compare`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.HPrime.Length`, which this module and modules that import it used -/

section

/-! # H′: selecting the first digest length -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_mov wp_subi wp_lsr wp_li Upd eval_nonzero)

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

theorem chooseLength_ok (s : State) (hb : (s.gpr .r30).toNat < 2 ^ 32) :
    WP isa chooseLength s fun t =>
      t.gpr .r4 = BitVec.ofNat 64 (min (s.gpr .r30).toNat 64) ∧ Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mov fun a ha => wp_subi (by decide) fun b hb' =>
    wp_lsr (by decide) fun u hu => WP.block_nil ?_)
  have ku : Keeps s u :=
    (Keeps.of_upd ha (by decide)).trans
      ((Keeps.of_upd hb' (by decide)).trans (Keeps.of_upd hu (by decide)))
  have n : u.gpr .r4 = s.gpr .r30 := by
    rw [hu.other _ (by decide), hb'.other _ (by decide), ha.gpr]
  have comparison : u.gpr .r10 = if (s.gpr .r30).toNat < 65 then 1 else 0 := by
    rw [hu.gpr, hb'.gpr, ha.gpr]
    exact below65 _ hb
  have flag : isa.eval (.nonzero .d .r10) u = some (decide ((s.gpr .r30).toNat < 65)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) u = _
    by_cases hn : (s.gpr .r30).toNat < 65 <;>
      simp [eval_nonzero, comparison, hn]
  refine WP.ite (decide ((s.gpr .r30).toNat < 65)) flag ?_ ?_
  · intro h
    have hn : (s.gpr .r30).toNat ≤ 64 := by have := of_decide_eq_true h; omega_using [this]
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .r30).toNat := by have := of_decide_eq_false h; omega_using [this]
    refine wp_li (by decide) fun t ht => WP.block_nil ?_
    refine ⟨?_, ku.trans (Keeps.of_upd ht (by decide))⟩
    rw [Nat.min_eq_right hn]; exact ht.gpr

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! # H′: a bounded public length comparison -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (wp_subi wp_lsr)

structure Compared (s t : State) : Prop where
  value : t.gpr .r10 = if (s.gpr .r30).toNat < 65 then 1 else 0
  other : ∀ r, r ≠ .r10 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem compare_ok (s : State) (hb : (s.gpr .r30).toNat < 2 ^ 32) :
    WP isa (.block Impl.Argon2.PPC64LE.HPrime.cmpLeft) s (Compared s) := by
  unfold Impl.Argon2.PPC64LE.HPrime.cmpLeft
  refine wp_subi (by decide) fun a ha => wp_lsr (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, fun r hr => (ht.other r hr).trans (ha.other r hr), ht.mem.trans ha.mem,
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  rw [ht.gpr, ha.gpr]
  exact below65 _ hb

theorem Compared.keeps {s t : State} (h : Compared s t) : Keeps s t := by
  refine ⟨fun r hr => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · exact fun h => by subst h; exact absurd hr (by decide)
  · rw [h.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! ### `Argon2.PPC64LE.HPrime.Output`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.HPrime.Copy`, which only this module used -/

section

/-! # H′: copying digest bytes -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_lbz wp_stb wp_addi wp_subi eval_nonzero)

theorem copyByte_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r5) 1)
    (hw : InRegions s.wr (s.gpr .r29) 1) :
    WP isa (.block copyByte) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r29) (s.mem (s.gpr .r5)) ∧
      t.gpr .r5 = s.gpr .r5 + 1 ∧ t.gpr .r29 = s.gpr .r29 + 1 ∧
      t.gpr .r9 = s.gpr .r9 - 1 ∧
      (∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold copyByte
  refine wp_lbz (a := s.gpr .r5) (by decide) (BitVec.add_zero _) hr fun a ha => ?_
  refine wp_stb (a := s.gpr .r29) (by decide) (by rw [ha.other _ (by decide)]; exact BitVec.add_zero _)
    (by rw [ha.wr]; exact hw) fun c hc => ?_
  refine wp_addi (by decide) fun d hd => wp_addi (by decide) fun e he =>
    wp_subi (by decide) fun t ht => WP.block_nil ?_
  have o : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
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
  source : s.gpr .r5 = src + BitVec.ofNat 64 j
  destination : s.gpr .r29 = dst + BitVec.ofNat 64 j
  count : s.gpr .r9 = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem copyLoop_ok (s₀ : State) (src dst : Addr) (k : Nat)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 64)
    (hs : s₀.gpr .r5 = src) (hd : s₀.gpr .r29 = dst)
    (hn : s₀.gpr .r9 = BitVec.ofNat 64 k)
    (hr : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < k, InRegions s₀.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : Region.Disjoint ⟨src, k⟩ ⟨dst, k⟩) :
    WP isa (.loop (.block copyByte) (.nonzero .d .r9)) s₀ (CopyI s₀ src dst k k) := by
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
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .r5) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .r29) 1 := by
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
  have hz' : (t.gpr .r9 == 0) = decide (k - (j + 1) = 0) := by
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
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) = 0 by omega_using [he], decide_true, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) ≠ 0 by omega_using [hj, he], decide_false, Bool.not_false]

end VG.Proof.Argon2.PPC64LE.HPrime

end

end


/-! # H′: emitting a digest or its 32-byte prefix -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_mov wp_addi wp_li wp_subi)
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
  output : t.gpr .r29 = s.gpr .r29 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .r29) (bytesAt s.mem (s.gpr .r31 + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .r9 = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31 + 768, k⟩ : Region).Disjoint ⟨s.gpr .r29, k⟩) :
    WP isa copy s (Copied s k) := by
  unfold copy
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  have src : u.gpr .r5 = s.gpr .r31 + 768 := by rw [hu.gpr]; rfl
  have other : ∀ r, r ≠ .r5 → u.gpr r = s.gpr r := fun r hr => hu.other r hr
  have mem : u.mem = s.mem := hu.mem
  have rd : u.rd = s.rd := hu.rd
  have wr : u.wr = s.wr := hu.wr
  have read : ∀ i < k, InRegions (u.rd ++ u.wr)
      (s.gpr .r31 + 768 + BitVec.ofNat 64 i) 1 := by
    intro i hi'
    rw [rd, wr, BitVec.add_assoc,
      show (768 : Addr) = BitVec.ofNat 64 768 from rfl, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ work,
      Offset.contains_base _ (by omega_using [hi, hi'] : 768 + i + 1 ≤ 16384) (by omega_using [hi, hi'])⟩
  have loop := copyLoop_ok u _ _ k lo (by omega_using [hi]) src (other .r29 (by decide))
    ((other .r9 (by decide)).trans count) read
    (by intro i hi'; rw [wr]; exact out i hi') sep
  obtain ⟨tr, t, he, ht⟩ := loop
  refine ⟨tr, t, he, ht.destination,
    fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
    ht.rd.trans rd, ht.wr.trans wr, (VG.PPC64LE.Exec.sp he).trans hu.sp, ?_⟩
  rw [ht.mem, mem, List.take_of_length_le]
  simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : Copied s k t) :
    Frame [⟨s.gpr .r29, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r29) (d := 0) (n := k) (k := k) (by omega_using []) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .r29 = s.gpr .r29 + 32
  remaining : t.gpr .r30 = s.gpr .r30 - 32
  other : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r5 → r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .r29) (bytesAt s.mem (s.gpr .r31 + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31 + 768, 32⟩ : Region).Disjoint ⟨s.gpr .r29, 32⟩) :
    WP isa emitPrefix s (Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have base : a.gpr .r31 = s.gpr .r31 := ha.other _ (by decide)
  have dst : a.gpr .r29 = s.gpr .r29 := ha.other _ (by decide)
  have workA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .r29 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .r31 + 768, 32⟩ : Region).Disjoint ⟨a.gpr .r29, 32⟩ := by
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
    Frame [⟨s.gpr .r29, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r29) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : Emitted s t)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32⟩) :
    bytesAt t.mem (s.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .r31 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.Next`. -/

@[expose] public section

section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.PPC64LE (wp_li)

theorem next_ok (s : State)
    (hlen : 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 64)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa (next) s fun t =>
      (bytesAt t.mem (s.gpr .r31 + 768) 64).take (s.gpr .r4).toNat =
        Spec.Argon2.H (s.gpr .r4).toNat (bytesAt s.mem (s.gpr .r31 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
    rw [ka.r31]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .r31 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .r4).toNat 0) a.mem (a.gpr .r31) [] := by
    rw [ka.r31]; exact reprA
  have wrA' : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [ka.r31, ka.wr]; exact hwr
  have swA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ka.r31, ka.sp]; exact stackWork
  refine WP.seq ((absorbFixed_ok a _ 768 64 (by decide) (by rw [ka.sp]; exact hsp) (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .r4).toNat 0) u.mem (u.gpr .r31)
      (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    rw [ku.r31]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_li (by decide) fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · exact hw.other r (preserved_ne hr)
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .r4).toNat 0) w.mem (w.gpr .r31)
      (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    rw [hw.mem, kw.r31]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .r31 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .r4 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .r31 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .r31 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .r31, 16384⟩ : Region) ∈ w.wr := by rw [ksw.r31, ksw.wr]; exact hwr
  have swW : (below w.sp 48).Disjoint ⟨w.gpr .r31, 16384⟩ := by
    rw [ksw.r31, ksw.sp]; exact stackWork
  refine (finalize_ok w _ _ reprW count bound (by rw [ksw.sp]; exact hsp) wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .r4).toNat) out
  rw [ksw.r31] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_li)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .r29 = s.gpr .r29 + 32
  remaining : t.gpr .r30 = s.gpr .r30 - 32
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48, ⟨s.gpr .r29, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .r31 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .r31 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r29) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .r31 + 768) 64)).take 32
  comparison : t.gpr .r10 = if (s.gpr .r30 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (s : State)
    (hsp : 48 ≤ s.sp.toNat)
    (remainingBound : 32 ≤ (s.gpr .r30).toNat ∧ (s.gpr .r30).toNat < 2 ^ 32)
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa (.seq (.block [.li .r4 64]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      s (ChainStep s) := by
  refine WP.seq (wp_li (by decide) fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [ka.r31, ka.wr]; exact work
  have stackA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ka.r31, ka.sp]; exact stackWork
  have lengthA : (a.gpr .r4).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok a (by rw [lengthA]; decide) (by rw [ka.sp]; exact hsp) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .r29 = s.gpr .r29 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .r31 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    simpa only [lengthA, ka.r31, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [ksu.r31, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .r29 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .r31 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .r29, 32⟩ := by
    rw [ksu.r31, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .r30).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .r29, 32⟩] u.mem w.mem := by
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
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .r31 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.r31, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide)]

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)
open VG.Proof.MdStream.PPC64LE (eval_zero)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .r29 = s.gpr .r29 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .r30 = s.gpr .r30 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48, ⟨s.gpr .r29, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .r31 + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r29) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32 * (n + 1)⟩)
    (stackOut : (below s.sp 48).Disjoint ⟨s.gpr .r29, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .r31 (by decide) (by decide) (by decide)
  have sp := step.sp
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_arith
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
      ⟨s.gpr .r29 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
        ⟨s.gpr .r29 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .r31, 832⟩, below s.sp 48, ⟨s.gpr .r29, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h1 h2 => (tail.regs r hr h1 h2).trans (step.regs r hr h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, tail.sp.trans step.sp, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega_arith) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_arith) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .r29) 32 = bytesAt u.mem (s.gpr .r29) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r29, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega_arith))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega_arith))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega_arith)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rw [Proof.Argon2.chainPrefixes]

theorem chain_ok (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 32)
    (hsp : 48 ≤ s.sp.toNat)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, 32 * n⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackOut : (below s.sp 48).Disjoint ⟨s.gpr .r29, 32 * n⟩) :
    WP isa (chain) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega_arith
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_arith)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok s hsp
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) work out32 sep32 stackWork
    have base := step.regs .r31 (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
    have compareU : u.gpr .r10 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .d .r10) u = some false := by
        show VG.PPC64LE.eval (.zero .d .r10) u = _
        simp [eval_zero, compareU, show lastLen < 65 by omega_arith]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_arith) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .r29 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_arith)
      have suffix : Region.Sub ⟨u.gpr .r29, 32 * (n + 1)⟩ ⟨s.gpr .r29, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_arith : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .r31, 16384⟩ : Region).Disjoint ⟨u.gpr .r29, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below u.sp 48).Disjoint ⟨u.gpr .r29, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_arith) (by omega_arith) (by rw [sp]; exact hsp) countU workU outU sepU swU soU
      have flag : isa.eval (.zero .d .r10) u = some true := by
        show VG.PPC64LE.eval (.zero .d .r10) u = _
        simp [eval_zero, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_arith]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_arith) sep stackOut⟩

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.Written`. -/

@[expose] public section

section
/-! # H′: composing output fragments -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE
open VG.Spec.Blake2 (bytesAt)

/-- An output fragment, allowing hashing in the workspace between writes. -/
structure Written (s : State) (xs : List Byte) (t : State) : Prop where
  output : t.gpr .r29 = s.gpr .r29 + BitVec.ofNat 64 xs.length
  regs : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48, ⟨s.gpr .r29, xs.length⟩] s.mem t.mem
  bytes : bytesAt t.mem (s.gpr .r29) xs.length = xs

theorem Written.r31 {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .r31 = s.gpr .r31 := h.regs _ (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : Keeps s t) : Written s [] t := by
  refine ⟨?_, fun r hr _ _ => h.regs r hr, h.rd, h.wr, h.sp, ?_, rfl⟩
  · exact (h.regs .r29 (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : Written u xs t)
    (k : Keeps s u) : Written s xs t := by
  have dst := k.regs .r29 (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h1 h2 => (h.regs r hr h1 h2).trans (k.regs r hr),
    h.rd.trans k.rd, h.wr.trans k.wr, h.sp.trans k.sp, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
        ⟨s.gpr .r29, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.r31, k.sp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : Copied s k t) (hk : k < 2 ^ 64) :
    Written s (bytesAt s.mem (s.gpr .r31 + 768) k) t := by
  have len : (bytesAt s.mem (s.gpr .r31 + 768) k).length = k := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 _ => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · exact h.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr) h14
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : Emitted s t) :
    Written s (bytesAt s.mem (s.gpr .r31 + 768) 32) t := by
  have len : (bytesAt s.mem (s.gpr .r31 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 h15 => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · exact h.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr) h14 h15
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : ChainResult s n t) :
    Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, h.sp, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : Written s xs u)
    (last : Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, xs.length + ys.length⟩)
    (stack : (below s.sp 48).Disjoint ⟨s.gpr .r29, xs.length + ys.length⟩) :
    Written s (xs ++ ys) t := by
  have tf : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
      ⟨s.gpr .r29 + BitVec.ofNat 64 xs.length, ys.length⟩] u.mem t.mem := by
    rw [← first.r31, ← first.sp, ← first.output]; exact last.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ xs.length + ys.length)
      (h : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
        ⟨s.gpr .r29 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .r31, 832⟩, below s.sp 48,
        ⟨s.gpr .r29, (xs ++ ys).length⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ (by simpa only [List.length_append] using hk)⟩
  refine ⟨?_, fun r hr h1 h2 => (last.regs r hr h1 h2).trans (first.regs r hr h1 h2),
    last.rd.trans first.rd, last.wr.trans first.wr, last.sp.trans first.sp, ?_, ?_⟩
  · rw [last.output, first.output, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  · exact (extend 0 xs.length (by omega_using []) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega_using []) tf)
  · have before : bytesAt t.mem (s.gpr .r29) xs.length = bytesAt u.mem (s.gpr .r29) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r29, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega_using [bound]) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [bound])
    rw [List.length_append, Proof.Blake2.bytesAt_add, before, first.bytes, ← first.output, last.bytes]

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_mov)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 32
  spBound : 48 ≤ s.sp.toNat
  work : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .r29 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .r31, 16384⟩ : Region).Disjoint ⟨s.gpr .r29, n⟩
  stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩
  stackOut : (below s.sp 48).Disjoint ⟨s.gpr .r29, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .r29, k⟩ ⟨s.gpr .r29, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega_using [size, this], by rw [written.sp]; exact h.spBound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.r31]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega_using [size, hi])
  · rw [written.r31]; exact h.sep.sub_right suffix
  · rw [written.r31, written.sp]; exact h.stackWork
  · rw [written.sp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega_using [hk, this], h.spBound, h.work, fun i hi => h.out i (by omega_using [hk, hi]),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega_using [size, this])
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .r30 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .r31 + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha => WP.block_nil ?_)
  have base := ha.other .r31 (by decide)
  have dst := ha.other .r29 (by decide)
  have workA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .r29 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .r31 + 768, n⟩ : Region).Disjoint ⟨a.gpr .r29, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega_using [hi] : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht (by have := space.bound; omega_using [hi])
  refine ⟨?_, fun r hr h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, result.sp.trans ha.sp, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · exact (result.regs r hr h1 h2).trans (ha.other r (preserved_ne hr))
  · simpa only [base, dst, ha.mem, ha.sp] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! ### `Argon2.PPC64LE.HPrime.Contract`, which this module and modules that import it used -/

section

/-! # H′ on PPC64LE: a local contract -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE

def inputR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .r7, 16384⟩
/-- The frames of the streaming functions H′ calls. -/
def stackR (s : State) : Region := below s.sp 48

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .r4).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat < 2 ^ 32 ∧
    48 ≤ s.sp.toNat ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s) ∧
    (stackR s).Disjoint (inputR s) ∧ (stackR s).Disjoint (outputR s) ∧ (stackR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat =
    Spec.Argon2.hPrime (s.gpr .r6).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s t := s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧
    s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧ s.gpr .r7 = t.gpr .r7 ∧ s.sp = t.sp

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

@[expose] public section

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.PPC64LE.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.PPC64LE (wp_mov wp_addi)

theorem finishInput_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .r31) d)
    (length : d.length = 4 + (s.gpr .r28).toNat) (bound : (s.gpr .r28).toNat < 2 ^ 32)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa (finishInput) s fun t =>
      bytesAt t.mem (s.gpr .r31 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_addi (by decide) fun u hu => WP.block_nil ?_)
  obtain ku : Keeps s u := Keeps.of_upd hu (by decide)
  obtain repr' : Repr b h0 u.mem (u.gpr .r31) d := by rw [hu.mem, ku.r31]; exact repr
  obtain count : u.gpr .r4 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  obtain len : d.length < 2 ^ 64 := by rw [length]; omega_arith
  obtain wr : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [ku.r31, ku.wr]; exact hwr
  obtain sw : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
    rw [ku.r31, ku.sp]; exact stackWork
  refine (finalize_ok u h0 d repr' count len (by rw [ku.sp]; exact hsp) wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', finalize_frame _ _ frame⟩⟩
  simpa only [ku.r31] using out

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (s : State)
    (hlen : 1 ≤ (s.gpr .r30).toNat ∧ (s.gpr .r30).toNat < 2 ^ 32)
    (len : (s.gpr .r28).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .r31 + 832) 4 = Spec.Argon2.le32 (s.gpr .r30).toNat)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r27, (s.gpr .r28).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r27, (s.gpr .r28).toNat⟩ : Region).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackData : (below s.sp 48).Disjoint ⟨s.gpr .r27, (s.gpr .r28).toNat⟩) :
    WP isa (first) s fun t =>
      (bytesAt t.mem (s.gpr .r31 + 768) 64).take (min (s.gpr .r30).toNat 64) =
        Spec.Argon2.H (min (s.gpr .r30).toNat 64)
          (Spec.Argon2.le32 (s.gpr .r30).toNat ++ bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  obtain na : (a.gpr .r4).toNat = min (s.gpr .r30).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain wrA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by rw [ka.r31, ka.wr]; exact hwr
  obtain swA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ka.r31, ka.sp]; exact stackWork
  obtain lenA : 1 ≤ (a.gpr .r4).toNat ∧ (a.gpr .r4).toNat ≤ 64 := by rw [na]; omega_arith
  refine WP.seq ((init_ok a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  obtain ku : Keeps a u := ⟨regsU, rdU, wrU, spU, init_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .r30).toNat 64) 0) u.mem (u.gpr .r31) [] := by
    rw [ku.r31]; simpa only [na] using reprU
  obtain wrU' : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [ksu.r31, ksu.wr]; exact hwr
  obtain swU : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
    rw [ksu.r31, ksu.sp]; exact stackWork
  obtain headU : bytesAt u.mem (u.gpr .r31 + 832) 4 = Spec.Argon2.le32 (s.gpr .r30).toNat := by
    rw [ksu.r31, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok u _ 832 4 (by decide) (by rw [ksu.sp]; exact hsp) (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  obtain ksw := ksu.trans kw
  obtain r12 : w.gpr .r27 = s.gpr .r27 := ksw.regs _ (by decide)
  obtain r13 : w.gpr .r28 = s.gpr .r28 := ksw.regs _ (by decide)
  obtain headLen : (Spec.Argon2.le32 (s.gpr .r30).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  obtain reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .r30).toNat 64) 0) w.mem (w.gpr .r31)
      (Spec.Argon2.le32 (s.gpr .r30).toNat) := by
    rw [kw.r31]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  obtain wrW : (⟨w.gpr .r31, 16384⟩ : Region) ∈ w.wr := by rw [ksw.r31, ksw.wr]; exact hwr
  obtain dataW : Covers [⟨w.gpr .r27, (w.gpr .r28).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  obtain dwW : (⟨w.gpr .r27, (w.gpr .r28).toNat⟩ : Region).Disjoint ⟨w.gpr .r31, 16384⟩ := by
    rw [r12, r13, ksw.r31]; exact dataWork
  obtain swW : (below w.sp 48).Disjoint ⟨w.gpr .r31, 16384⟩ := by
    rw [ksw.sp, ksw.r31]; exact stackWork
  obtain sdW : (below w.sp 48).Disjoint ⟨w.gpr .r27, (w.gpr .r28).toNat⟩ := by
    rw [ksw.sp, r12, r13]; exact stackData
  obtain inputW : bytesAt w.mem (w.gpr .r27) (w.gpr .r28).toNat =
      bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .r28).toNat ≤ 2 ^ 64 by omega_arith)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok w _ _ headLen reprW' (by rw [r13]; exact len)
    (by rw [ksw.sp]; exact hsp) wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  obtain ksx := ksw.trans kx
  obtain reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .r30).toNat 64) 0) x.mem (x.gpr .r31)
      (Spec.Argon2.le32 (s.gpr .r30).toNat ++ bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat) := by
    rw [kx.r31]; simpa only [inputW] using reprX
  obtain r13X : x.gpr .r28 = s.gpr .r28 := ksx.regs _ (by decide)
  obtain length : (Spec.Argon2.le32 (s.gpr .r30).toNat ++ bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat).length =
      4 + (x.gpr .r28).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  obtain wrX : (⟨x.gpr .r31, 16384⟩ : Region) ∈ x.wr := by rw [ksx.r31, ksx.wr]; exact hwr
  obtain swX : (below x.sp 48).Disjoint ⟨x.gpr .r31, 16384⟩ := by
    rw [ksx.sp, ksx.r31]; exact stackWork
  refine (finishInput_ok x _ _ reprX' length (by rw [r13X]; exact len) (by rw [ksx.sp]; exact hsp) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  obtain result := congrArg (List.take (min (s.gpr .r30).toNat 64)) out
  rw [ksx.r31] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! Merged from `Proof.Argon2.PPC64LE.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.PPC64LE.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (wp_mov)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen))
    (comparison : s.gpr .r10 = if 32 * n + lastLen < 65 then 1 else 0) :
    WP isa (.ite (.nonzero .d .r10) (.block []) (chain)) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by by_cases h : 32 * n + lastLen < 65 <;>
    simp [eval, State.read, comparison, h]) ?_ ?_
  · intro h
    obtain hn : n = 0 := by have := of_decide_eq_true h; omega_arith
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    obtain hn : 1 ≤ n := by have := of_decide_eq_false h; omega_arith
    obtain p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega_arith)
    exact chain_ok n lastLen s hn last space.bound space.spBound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .r31 + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .r31 + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64)) ∧
      t.gpr .r30 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  obtain short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega_arith)
  obtain sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  obtain wa := Written.of_emitted ha
  obtain lenA : (bytesAt s.mem (s.gpr .r31 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  obtain spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega_arith)
  obtain countA : a.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
  obtain digestA : bytesAt a.mem (a.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
    rw [wa.r31]; exact ha.digest short.sep
  refine WP.seq ((compare_ok a (by rw [countA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]; exact spaceA.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .r30 = BitVec.ofNat 64 (32 * n + lastLen) :=
    (compared.other _ (by decide)).trans countA
  obtain compareU : u.gpr .r10 = if 32 * n + lastLen < 65 then 1 else 0 := by
    rw [compared.value, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]
  refine WP.seq ((maybeChain_ok n lastLen u (spaceA.keeps ku) last countU compareU).mono ?_)
  intro w hw
  obtain ww := (Written.of_chain hw).before_keeps ku
  obtain digestU : bytesAt u.mem (u.gpr .r31 + 768) 64 = bytesAt s.mem (s.gpr .r31 + 768) 64 := by
    rw [compared.mem, ku.r31]; exact digestA
  obtain ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)) w := by
    simpa only [digestU] using ww
  obtain wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega_arith)
  obtain produced : ((bytesAt s.mem (s.gpr .r31 + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega_arith
  obtain spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  obtain countW : w.gpr .r30 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega_arith : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  obtain digestW : bytesAt w.mem (w.gpr .r31 + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64) := by
    rw [hw.regs .r31 (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx => WP.block_nil ?_)
  obtain kx : Keeps w x := Keeps.of_upd hx (by decide)
  obtain spaceX := spaceW.keeps kx
  obtain lenX : (x.gpr .r4).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceW.bound; omega_arith)]
  refine (next_ok x (by rw [lenX]; omega_arith) spaceX.spBound spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  obtain wwt := Written.of_keeps (kx.trans kt)
  obtain written := space.join wsw wwt (by rw [produced, List.length_nil]; omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.r31, hx.mem, digestW, wsw.r31] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r30 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .r31 + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  obtain len : ((bytesAt s.mem (s.gpr .r31 + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .r31 + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega_arith
  obtain spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega_arith) last.2 remaining).mono ?_
  intro t copied
  obtain out : bytesAt u.mem (u.gpr .r31 + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .r31 + 768) 64)) := by
    rw [written.r31, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  obtain all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .r30 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .r31 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((compare_ok s (by rw [count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .r30 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  obtain compareU : u.gpr .r10 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [eval, State.read, compareU, h]) ?_ ?_
  · intro h
    obtain short : n ≤ 64 := by have := of_decide_eq_true h; omega_arith
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain value : bytesAt u.mem (u.gpr .r31 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.r31, ← bytesAt_take _ _ n 64 short]
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
    obtain countLong : u.gpr .r30 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain digestU : bytesAt u.mem (u.gpr .r31 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.r31]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega_arith), bytesAt_take _ _ 64 64 (by decide)] using digest
    obtain value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .r31 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega_arith)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.PPC64LE.HPrime
end

/-! # H′: functional correctness of the complete ARM64 program -/

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (s : State) (pre : localContract.pre s) :
    WP isa code s fun t => localContract.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.lr = s.lr ∧
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := pre
  obtain work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  have sp := ha.sp
  obtain workA : (⟨a.gpr .r31, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  obtain dataA : Covers [⟨a.gpr .r27, (a.gpr .r28).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  obtain dwA : (⟨a.gpr .r27, (a.gpr .r28).toNat⟩ : Region).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  obtain swA : (below a.sp 48).Disjoint ⟨a.gpr .r31, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  obtain sdA : (below a.sp 48).Disjoint ⟨a.gpr .r27, (a.gpr .r28).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  obtain inputA : bytesAt a.mem (a.gpr .r27) (a.gpr .r28).toNat =
      bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .r4).toNat ≤ 2 ^ 64 by omega_arith) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  obtain headA : bytesAt a.mem (a.gpr .r31 + 832) 4 = Spec.Argon2.le32 (a.gpr .r30).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  obtain spaceA : Space a (s.gpr .r6).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA (by rw [sp]; exact hsp) workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  obtain spaceB := spaceA.keeps kb
  obtain countB : b.gpr .r30 = BitVec.ofNat 64 (s.gpr .r6).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain digestB' : (bytesAt b.mem (b.gpr .r31 + 768) 64).take (min (s.gpr .r6).toNat 64) =
      Spec.Argon2.H (min (s.gpr .r6).toNat 64)
        (Spec.Argon2.le32 (s.gpr .r6).toNat ++ bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) := by
    rw [kb.r31]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok b (s.gpr .r6).toNat
    (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  obtain baseB : b.gpr .r31 = s.gpr .r7 := kb.r31.trans ha.workspace
  obtain spB : b.sp = s.sp := kb.sp.trans sp
  obtain dstB : b.gpr .r29 = s.gpr .r5 := (kb.regs _ (by decide)).trans ha.output
  obtain wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  obtain frame : Frame [⟨s.gpr .r7, 832⟩, stackR s, outputR s] a.mem x.mem := by
    obtain fb : Frame [⟨s.gpr .r7, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have keep (d : Nat) (dlo : 832 ≤ d) (dhi : d + 8 ≤ 16384) :
      x.mem.readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 = a.mem.readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 := by
    apply frame.readW (r := ⟨s.gpr .r7 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact (Offset.base_disjoint _ dlo (by omega_arith)).symm
    · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
    · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
  obtain values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .r7 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    obtain bounds := saved_bounds (r, d) hr
    rw [keep d (by omega_arith) (by omega_arith), ha.mem]; exact setupMem_saved s r d hr
  obtain lrSlot : x.mem.readW (s.gpr .r7 + BitVec.ofNat 64 880) 64 = s.lr := by
    rw [keep 880 (by decide) (by decide), ha.mem]; exact setupMem_lr s
  obtain baseX := (hx.regs .r31 (by decide) (by decide) (by decide)).trans baseB
  obtain readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX (fun r hr hm => ?_) readable values lrSlot).mono ?_
  · have h : r ≠ .r0 ∧ r ≠ .r31 ∧ r ≠ .r27 ∧ r ≠ .r28 ∧ r ≠ .r29 ∧ r ≠ .r30 := by
      refine ⟨preserved_ne hr, ?_, ?_, ?_, ?_, ?_⟩ <;> exact fun e => hm (by subst e; decide)
    rw [hx.regs r hr h.2.2.2.2.1 h.2.2.2.2.2, kb.regs r hr]
    exact ha.other r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  rintro t ⟨regs, lr, mem, _, _, _⟩
  refine ⟨?_, regs, lr, ?_⟩
  · change bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    obtain setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
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
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_correct (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, lr, _⟩ := code_wp s pre
  exact ⟨tr, t, run, ⟨regs, VG.PPC64LE.Exec.sp run, lr⟩, post⟩

end VG.Proof.Argon2.PPC64LE.HPrime
