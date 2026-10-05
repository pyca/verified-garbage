import VerifiedGarbage.Impl.Ed25519.X86_64.CombTable
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.Framework.RelCT
import Mathlib.Tactic.Module
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.WindowTables`. -/
section
/-!
# Verification's tables: `[1]A … [15]A` and cached `-[1]B … -[15]B`

The table of multiples of `A` is built by repeated addition of `A`, each entry
representing its multiple (`Rep`); the table of negated multiples of `B` is
stored from constants.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)
open VG.Impl.Ed25519 (negBaseCached)

variable {fld : Arith} [EdArith fld]

theorem tableStart_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base) (o : Nat) :
    WP isa (.block (tableStart o)) s fun t => t.gpr .rax = off base o ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [tableStart, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hp, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.add_comm _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-! ## Cached `-[i]B` -/

theorem bTablePrefix_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hp : s.gpr .rax = off base 2048) (n : Nat) (hn : n ≤ 15) :
    WP isa (.block ((List.range n).flatMap fun i => cachedPointStore (negBaseCached i) (128 * i))) s
      fun t => (∀ i < n, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i) ∧
        TableKeep base 2048 (128 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (cachedPointStore_ok (hk.scratch hs) ((hk.gpr _ (by decide)).trans hp)
      (negBaseCached n) (128 * n) (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun i hi => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : i < n
    · rw [(TableFrame.table ku.mem).point (by omega) (Or.inl (by omega)) (by omega), hv i h]
    · obtain rfl : i = n := by omega
      exact hu

/-- What the table of `B`'s multiples leaves. -/
structure BTableStored (base : Addr) (s t : State) : Prop where
  table : ∀ i < 15, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i
  gpr : ∀ r, r ∉ [Reg.rax, .r8, .r9, .r10, .r11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 2048 1920 s.mem t.mem

theorem bTable_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block bTable) s (BTableStored base s) := by
  rw [bTable, WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 2048) fun a ⟨ap, ka⟩ => ?_
  refine WP.mono (bTablePrefix_ok (hs.of_keeps ka (by decide)) ap 15 (by decide)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨tv, fun r hr => ?_, kt.rd.trans ka.2.2.1, kt.wr.trans ka.2.2.2, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), ka.1 r (by simp [hr.1])]
  · rw [← ka.2.1]; exact kt.mem

/-! ## `[i]A` -/

theorem rbxNext_ok (s : State) (n : Nat) (hn : n < 15) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 15)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (n + 1) ∧ t.zf = some (decide (n + 1 = 15)) ∧ Keeps [.rbx] s t := by
  have ha : BitVec.ofNat 64 n + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (n + 1) - (15 : BitVec 32).signExtend 64 == 0) = decide (n + 1 = 15) := by
    rw [show (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 15 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem rbxSet_ok (s : State) (n : Nat) (hn : n < 2 ^ 31) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- The table of `A`'s multiples, with `n` entries and `[n]A` in slots 0–3. -/
structure ATableInv (s₀ : State) (base : Addr) (A : EPoint dZ) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 15
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 n
  d : env s.mem base 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem base) 0 1 2 3) (n • A)
  table : ∀ j < n, Rep (tablePoint s.mem base (5376 + 128 * j)) ((j + 1) • A)
  a : tablePoint s.mem base 7424 = tablePoint s₀.mem base 7424
  keep : PowersKeep base 5376 1920 s₀ s

theorem aTableBody_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {n : Nat} (hn : n < 15)
    (hA : Rep (tablePoint s₀.mem base 7424) A) (h : ATableInv s₀ base A n s) :
    WP isa (.block (aTableBody fld)) s fun t => t.zf = some (decide (n + 1 = 15)) ∧
      ATableInv s₀ base A (n + 1) t := by
  rw [aTableBody, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (tableStart_ok h.scratch.rdi 7424) fun a ⟨ap, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (h.scratch.of_keep kae) ap (by decide) (by decide))
    fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  have b16 : env b.mem base 16 = env s.mem base 16 := by
    change Proof.X25519.X86_64.F b.mem base (offset 16) = Proof.X25519.X86_64.F s.mem base (offset 16)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega)), ka.2.1]
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  have kab := kae.trans kbe
  rw [WP.block_append_iff]
  refine WP.mono (pointAddWide_ok (h.scratch.of_keep kab) (b16.trans h.d)) fun c ⟨kc, cp, ch⟩ => ?_
  have crep : Rep (point (env c.mem base) 0 1 2 3) ((n + 1) • A) := by
    rw [cp, bp, pb, ka.2.1, h.a, succ_nsmul]
    exact pointAdd_rep h.value hA
  have kabc := kab.trans kc
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (h.scratch.of_keep kabc).rdi 5376 n (by omega)
    ((kabc.gpr _ (by decide)).trans h.counter)) fun d ⟨dp, kd⟩ => ?_
  have kde : Keep base c d := Keep.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok (h.scratch.of_keep (kabc.trans kde)) dp (by omega) (by omega))
    fun e ⟨ep, ke⟩ => ?_
  refine WP.mono (rbxNext_ok e n hn ((ke.gpr _ (by decide)).trans ((kde.gpr _ (by decide)).trans
    ((kabc.gpr _ (by decide)).trans h.counter)))) fun t ⟨tc, tz, kt⟩ => ?_
  have kall : PowersKeep base 5376 1920 s t :=
    ((PowersKeep.of_keep (kabc.trans kde)).trans ⟨fun r _ _ hr => ke.gpr r (fun hm => hr (by
      revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> decide)), ke.rd, ke.wr,
      (TableFrame.table ke.mem).mono (by omega) (by omega)⟩).trans
      (PowersKeep.of_keeps kt (by decide))
  have te : env t.mem base = env e.mem base := by rw [kt.2.1]
  have ee : env e.mem base = env d.mem base := table_env ke.mem (by omega)
  refine ⟨tz, by omega, by omega, kall.scratch h.scratch, tc, ?_, ?_, ?_, ?_, h.keep.trans kall⟩
  · rw [te, ee, kd.2.1]; exact (ch 16 (by decide)).trans (b16.trans h.d)
  · rw [te, ee, kd.2.1]; exact crep
  · intro j hj
    rw [kt.2.1]
    by_cases hjn : j < n
    · rw [(TableFrame.table ke.mem).point (by omega) (Or.inl (by omega)) (by omega), kd.2.1,
        workspace_tablePoint kc.mem (by omega) (by omega), workspace_tablePoint kab.mem (by omega) (by omega)]
      exact h.table j hjn
    · obtain rfl : j = n := by omega
      rw [ep, kd.2.1]; exact crep
  · rw [kt.2.1, (TableFrame.table ke.mem).point (by omega) (Or.inr (by omega)) (by omega), kd.2.1,
      workspace_tablePoint kc.mem (by omega) (by omega), workspace_tablePoint kab.mem (by omega) (by omega)]
    exact h.a

theorem aTableInit_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (.block aTableInit) s (ATableInv s base A 1) := by
  rw [aTableInit, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 7424) fun a ⟨ap, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTable_ok (hs.of_keep kae) ap (by decide) (by decide)) fun b ⟨pb, kb⟩ => ?_
  have kab := kae.trans (Keep.of_table kb)
  rw [WP.block_append_iff]
  refine WP.mono (rbxSet_ok b 0 (by decide)) fun c ⟨cc, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok ((hs.of_keep kab).of_keeps kc (by decide)).rdi 5376 0 (by decide) cc)
    fun d ⟨dp, kd⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok (((hs.of_keep kab).of_keeps kc (by decide)).of_keeps kd (by decide))
    dp (by decide) (by decide)) fun e ⟨ep, ke⟩ => ?_
  refine WP.mono (rbxSet_ok e 1 (by decide)) fun t ⟨tc, kt⟩ => ?_
  have hcd : d.mem = b.mem := kd.2.1.trans kc.2.1
  have hbs : env b.mem base 16 = env s.mem base 16 := by
    rw [tableLoad_high kb 16 (by decide), ka.2.1]
  have bA : Rep (point (env b.mem base) 0 1 2 3) A := by rw [pb, ka.2.1]; exact hA
  have kall : PowersKeep base 5376 1920 s t := by
    refine ((((PowersKeep.of_keep kab).trans (PowersKeep.of_keeps kc (by decide))).trans
      (PowersKeep.of_keeps kd (by decide))).trans ⟨fun r _ _ hr => ke.gpr r (fun hm => hr (by
        revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl | rfl | rfl | rfl) <;> decide)), ke.rd, ke.wr,
        (TableFrame.table ke.mem).mono (by omega) (by omega)⟩).trans (PowersKeep.of_keeps kt (by decide))
  have ee : env e.mem base = env d.mem base := table_env ke.mem (by omega)
  refine ⟨by decide, by decide, kall.scratch hs, tc, ?_, ?_, ?_, ?_, kall⟩
  · rw [kt.2.1, ee, hcd, hbs, hd]
  · rw [kt.2.1, ee, hcd, one_nsmul]; exact bA
  · intro j hj
    obtain rfl : j = 0 := by omega
    rw [kt.2.1, ep, hcd, zero_add, one_nsmul]; exact bA
  · rw [kt.2.1, (TableFrame.table ke.mem).point (by omega) (Or.inr (by omega)) (by omega), hcd,
      workspace_tablePoint (Keep.of_table kb).mem (by omega) (by omega), ka.2.1]

theorem aTable_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (aTable fld) s (ATableInv s base A 15) := by
  rw [aTable]
  refine WP.seq (WP.mono (aTableInit_ok hs hd hA) fun a ha => ?_)
  apply WP.loop (fun n t => ATableInv s base A (15 - n) t ∧ 0 < n) (n := 14)
  · intro n t ⟨h, hn⟩
    have hp := h.positive
    refine WP.mono (aTableBody_ok (n := 15 - n) (by omega) hA h) fun u ⟨uz, hu⟩ => ?_
    by_cases he : 15 - n + 1 = 15
    · exact Or.inl ⟨by simp only [eval, uz, he, decide_true, Option.map_some, Bool.not_true],
        by rw [← he]; exact hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false he, Option.map_some, Bool.not_false],
        n - 1, by omega, by rw [show 15 - (n - 1) = 15 - n + 1 by omega]; exact hu,
        by have := hu.bound; omega⟩
  · exact ⟨ha, by decide⟩

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyFrame`. -/
section
/-! Verification preserves input buffers and its saved pointers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside)

theorem tableFrame_work {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : o ≤ 64) (hn : 768 ≤ o + n) : Outside base o n m m' :=
  fun p hp => h p (by omega) hp

theorem outside_bytes {base p : Addr} {o n len : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192)
    (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt m' p len = Spec.Ed25519.bytesAt m p len := by
  apply List.map_congr_left
  intro i hi
  apply h
  change ofs base (off p i) < o ∨ o + n ≤ ofs base (off p i)
  have := hf i (List.mem_range.mp hi)
  omega

theorem PowersKeep.header {base : Addr} {o n d : Nat} {s t : State}
    (h : PowersKeep base o n s t) (hd : 7936 ≤ d) (hb : d + 8 ≤ 8192) (hn : o + n ≤ 7936) :
    t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (by omega) (Or.inr (by omega)) (by omega)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyInputs`. -/
section
/-! Reload verification pointers and check the complete unsigned scalar S. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Proof.X25519.X86_64 (off Keeps ea_at ea_sc val4)

theorem loadPointer_ok {s : State} {base : Addr} (hs : Scratch s base) (r : Reg) (d : Nat)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_sc, hs.rdi, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hk)

theorem add32_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add r (.imm 32)]) s fun t => t.gpr r = off (s.gpr r) 32 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨rfl, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem loadScalarWords_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadScalarWords) s fun t =>
      scalarValue t = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [loadScalarWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hp, hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left', scalarValue]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact (decodeLE_inputWords s.mem p).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem verifyScalar_ok {s : State} {base sig : Addr} (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8) :
    WP isa (.block verifyScalar) s fun t => Keep base s t ∧ t.mem = s.mem ∧
      t.cf = some (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) < Spec.Ed25519.L)) := by
  change WP isa (.block (([.mov .rdx (.mem (sc 7944))] : List Instr) ++
    ([.alu .add .rdx (.imm 32)] : List Instr) ++ loadScalarWords ++ scalarSubtract)) s _
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_
  rw [hp] at ap
  rw [WP.block_append_iff]
  refine WP.mono (add32_ok a .rdx) fun b ⟨bp, kb⟩ => ?_
  rw [ap] at bp
  rw [WP.block_append_iff]
  refine WP.mono (loadScalarWords_ok b (off sig 32) bp (by
    intro d hd; rw [kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]; exact hr d hd)) fun c ⟨cv, kc⟩ => ?_
  refine WP.mono (scalarSubtract_ok c) fun t ⟨tc, _, _, kt⟩ => ?_
  refine ⟨(((Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kb (by decide))).trans
    (Keep.of_keeps kc (by decide))).trans (Keep.of_keeps kt (by decide)),
    kt.2.1.trans (kc.2.1.trans (kb.2.1.trans ka.2.1)), ?_⟩
  rw [tc, cv, kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
end

/-!
# Verification's windows: doublings, digits and table additions

The accumulator in slots 0–3 always represents a point of the group (`Rep`):
four doublings multiply it by 16, and a nonzero digit `v` adds entry `v - 1`
of a table, which represents `[v]X`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

/-- What a window may change: the field workspace and the doublings' (below
byte 1888), and the registers it computes with. -/
structure WinKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 1824 s.mem t.mem

theorem WinKeep.refl (base : Addr) (s : State) : WinKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem WinKeep.trans {base : Addr} {s t u : State} (h : WinKeep base s t) (k : WinKeep base t u) :
    WinKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem WinKeep.scratch {base : Addr} {s t : State} (h : WinKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : WinKeep base s t :=
  ⟨fun r hr _ _ => h.gpr r hr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem WinKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : WinKeep base s t := by
  refine ⟨fun r hr hb hs => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, by rw [h.2.1]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact hb h
  · exact hs h
  · exact hr h

theorem WinKeep.of_double {base : Addr} {s t : State} (h : DoubleKeep base s t) : WinKeep base s t :=
  ⟨fun r hr _ hs => h.gpr r hs hr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem WinKeep.of_rbx {base : Addr} {s t : State} (h : RbxKeep base s t) : WinKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem WinKeep.counter {base : Addr} {s t : State} (h : WinKeep base s t) :
    t.mem.readW (off base 56) 64 = s.mem.readW (off base 56) 64 :=
  h.mem.word (Or.inl (by decide)) (by decide)

/-! ## Four doublings -/

theorem dblOps_eval (e : Env) :
    point (evalOps (dblOps true) e) 0 1 2 3 = dblPoint (point e 0 1 2 3) ∧
    evalOps (dblOps false) e 0 = (dblPoint (point e 0 1 2 3)).X ∧
    evalOps (dblOps false) e 1 = (dblPoint (point e 0 1 2 3)).Y ∧
    evalOps (dblOps false) e 2 = (dblPoint (point e 0 1 2 3)).Z :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dbl_ok {s : State} {base : Addr} (hs : Scratch s base) (t : Bool) {a : EPoint dZ}
    (ha : RepP (point (env s.mem base) 0 1 2 3) a) :
    WP isa (.block (fieldCode fld (dblOps t))) s fun u => Keep base s u ∧
      RepP (point (env u.mem base) 0 1 2 3) (a + a) ∧
      (t = true → Rep (point (env u.mem base) 0 1 2 3) (a + a)) ∧
      ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i := by
  refine WP.mono (fieldCodeWide_ok hs _) fun u ⟨ku, vu⟩ => ?_
  have hr := dblPoint_rep ha
  refine ⟨ku, ?_, fun ht => ?_, fun i hi => by
    rw [vu]; exact point_ops_high _ (by cases t <;> decide) _ i hi⟩
  · rw [vu]
    cases t
    · obtain ⟨_, ex, ey, ez⟩ := dblOps_eval (env s.mem base)
      refine ⟨?_, ?_, ?_⟩
      · show toZ (evalOps _ _ 2) ≠ 0
        rw [ez]; exact hr.z
      · show toZ (evalOps _ _ 0) = _ * toZ (evalOps _ _ 2)
        rw [ex, ez]; exact hr.x
      · show toZ (evalOps _ _ 1) = _ * toZ (evalOps _ _ 2)
        rw [ey, ez]; exact hr.y
    · rw [(dblOps_eval _).1]; exact hr.proj
  · subst ht
    rw [vu, (dblOps_eval _).1]; exact hr

theorem double4_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scratch s base)
    (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (double4 fld) s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [double4]
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rsi (.imm 3)]) s
      (fun t => t.gpr .rsi = 3 ∧ Keeps [.rsi] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨c1, k1⟩ => ?_)
  have hs₁ : Scratch s₁ base := hs.of_keeps k1 (by decide)
  have k1d : DoubleKeep base s s₁ := ⟨fun r hr _ => k1.1 r (by simpa using hr), k1.2.2.1, k1.2.2.2,
    by rw [k1.2.1]; exact Outside.refl _ _ _ _⟩
  have keepD {x y : State} (k : Keep base x y) : DoubleKeep base x y :=
    ⟨fun r _ hc => k.gpr r hc, k.rd, k.wr, k.mem⟩
  refine WP.seq ?_
  apply WP.loop (fun (n : Nat) (t : State) => 0 < n ∧ n ≤ 3 ∧ Scratch t base ∧
    t.gpr .rsi = BitVec.ofNat 64 n ∧ RepP (point (env t.mem base) 0 1 2 3) ((2 ^ (3 - n) : Nat) • a) ∧
    (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t) (n := 3)
  · intro n t ⟨hn0, hn3, ht, tc, tv, th, tk⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [WP.block_append_iff]
    refine WP.mono (dbl_ok ht false tv) fun u ⟨ku, uv, _, uh⟩ => ?_
    refine WP.mono (doubleDec_ok u k (by omega) ((ku.gpr _ (by decide)).trans tc))
      fun w ⟨wc, wz, kw⟩ => ?_
    have wrep : RepP (point (env w.mem base) 0 1 2 3) ((2 ^ (3 - k) : Nat) • a) := by
      rw [kw.2.1, show 3 - k = (3 - (k + 1)) + 1 by omega, pow_succ, mul_nsmul, two_nsmul]
      exact uv
    have wh : ∀ i : Slot, 16 ≤ i.val → env w.mem base i = env s.mem base i :=
      fun i h => by rw [kw.2.1, uh i h, th i h]
    have wk : DoubleKeep base s w := tk.trans ((keepD ku).trans
      ⟨fun r hr _ => kw.1 r (by simpa using hr), kw.2.2.1, kw.2.2.2,
        by rw [kw.2.1]; exact Outside.refl _ _ _ _⟩)
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, wz, decide_true, Option.map_some, Bool.not_true], ?_⟩
      refine WP.mono (dbl_ok (wk.scratch hs) true wrep) fun v ⟨kv, _, vr, vh⟩ => ?_
      refine ⟨?_, fun i h => (vh i h).trans (wh i h), wk.trans (keepD kv)⟩
      rw [show (16 : Nat) = 2 ^ (3 - 0) * 2 by rfl, mul_nsmul, two_nsmul]
      exact vr rfl
    · exact Or.inr ⟨by simp only [eval, wz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, by omega, by omega, wk.scratch hs, wc, wrep, wh, wk⟩
  · refine ⟨by decide, by decide, hs₁, c1, ?_, fun i _ => by rw [k1.2.1], k1d⟩
    rw [show (2 ^ (3 - 3) : Nat) = 1 from rfl, one_nsmul, k1.2.1]; exact ha.proj

/-! ## Digits -/

theorem addImm_ok (s : State) (r : Reg) (n : Nat) (hn : n < 2 ^ 31) :
    WP isa (.block [.alu .add r (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr r = off (s.gpr r) n ∧ Keeps [r] s t := by
  have he : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]; omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, he,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem digitByte_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitByte ptr add)) s fun t =>
      t.gpr .rbx = (s.mem (off (off P add) i)).setWidth 64 ∧ Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitByte, show ([.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr)),
      .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (Impl.X25519.X86_64.sc 56)),
      .movzx8 .rbx { base := .rsi, index := some .rax }] : List Instr) =
    [.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr))] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 add))] ++
      ([.mov .rax (.mem (Impl.X25519.X86_64.sc 56))] ++
        [.movzx8 .rbx { base := .rsi, index := some .rax }])) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rsi ptr hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addImm_ok a .rsi add hadd) fun b ⟨bp, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .rax 56
    (by decide)) fun c ⟨cp, kc⟩ => ?_
  have hm : c.mem = s.mem := kc.2.1.trans (kb.2.1.trans ka.2.1)
  have hrd : c.rd ++ c.wr = s.rd ++ s.wr := by
    rw [kc.2.2.1, kc.2.2.2, kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]
  have crsi : c.gpr .rsi = off P add := by rw [kc.1 _ (by decide), bp, ap, hp]
  have crax : c.gpr .rax = BitVec.ofNat 64 i := by rw [cp, kb.2.1, ka.2.1, hc]
  have hea : c.ea { base := .rsi, index := some .rax } = off (off P add) i := by
    simp only [State.ea, crsi, crax]
    rw [BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hea, State.load8, hrd, hr, hm,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, hm, kc.2.2.1.trans (kb.2.2.1.trans ka.2.2.1),
    kc.2.2.2.trans (kb.2.2.2.trans ka.2.2.2)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, kc.1 r (by simp [hr.2.1]), kb.1 r (by simp [hr.1]),
    ka.1 r (by simp [hr.1])]

private theorem high_nibble : ∀ b : BitVec 8,
    b.setWidth 64 >>> 4 = BitVec.ofNat 64 (b.toNat / 16) := by decide

private theorem low_nibble : ∀ b : BitVec 8,
    b.setWidth 64 &&& (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (b.toNat % 16) := by decide

private theorem nibble_zero : ∀ n < 16, (BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem digitHigh_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitHigh ptr add)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat / 16) ∧
      t.zf = some (decide ((s.mem (off (off P add) i)).toNat / 16 = 0)) ∧
      Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitHigh, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  have hlt : (s.mem (off (off P add) i)).toNat / 16 < 16 := by
    have := (s.mem (off (off P add) i)).isLt; omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, av,
    show 1 ≤ 4 ∧ 4 ≤ 63 by decide, and_self, ite_true, high_nibble, BitVec.and_self, nibble_zero _ hlt,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.2.2, ite_false]
  exact ka.1 r (by simp [hr.1, hr.2.1, hr.2.2])

theorem digitLow_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitLow ptr add)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat % 16) ∧
      t.zf = some (decide ((s.mem (off (off P add) i)).toNat % 16 = 0)) ∧
      Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitLow, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  have hlt : (s.mem (off (off P add) i)).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, av, low_nibble,
    nibble_zero _ hlt, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.2.2, ite_false]
  exact ka.1 r (by simp [hr.1, hr.2.1, hr.2.2])

/-! ## Adding a table entry -/

theorem tableEntryAdd_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base) {o j : Nat}
    (hlo : 768 ≤ o) (hhi : o + 128 * j + 128 ≤ 8192) (hj : j < 64)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (o + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (tableAddr o ++ pointFromTableQ ++ add)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.rdi o j hj hc) fun a ⟨pa, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) pa (by omega) (by omega)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  have b_high : ∀ i : Slot, 8 ≤ i.val → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega)), ka.2.1]
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  have bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.2.1, hq]
  refine WP.mono (hadd b base q (hs.of_keep (kae.trans kbe)) (by rw [b_high 16 (by decide)]; exact hd) bq)
    fun t ⟨kt, tp, th⟩ => ?_
  exact ⟨(kae.trans kbe).trans kt, by rw [tp, bp], by rw [th 16 (by decide), b_high 16 (by decide)]⟩

/-- Entries `j < 15` of the table at byte `o` are `f` of representatives of `[j + 1]X`. -/
def TableOf (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (m : Mem) (base : Addr) (o : Nat)
    (X : EPoint dZ) : Prop :=
  ∀ j < 15, ∃ q, tablePoint m base (o + 128 * j) = f q ∧ Rep q ((j + 1) • X)

theorem addDigit_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hlo : 768 ≤ o) (hhi : o + 1920 ≤ 8192) {X a : EPoint dZ} (htab : TableOf f s.mem base o X)
    (v : Nat) (hv : v < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 v) (hz : s.zf = some (decide (v = 0)))
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (addDigit o add) s fun t => Rep (point (env t.mem base) 0 1 2 3) (a + v • X) ∧
      env t.mem base 16 = env s.mem base 16 ∧ WinKeep base s t := by
  rw [addDigit]
  refine WP.ite (!decide (v = 0)) (by simp only [eval, hz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
    refine WP.mono (accumulateDec_ok s n hc) fun b ⟨bc, kb⟩ => ?_
    obtain ⟨q, hq, hr⟩ := htab n (by omega)
    rw [← List.append_assoc]
    refine WP.mono (tableEntryAdd_ok hadd (hs.of_keeps kb (by decide)) hlo (by omega) (by omega) bc q
      (by rw [kb.2.1]; exact hq) (by rw [kb.2.1]; exact hd)) fun t ⟨kt, tp, td⟩ => ?_
    refine ⟨?_, by rw [td, kb.2.1], (WinKeep.of_keeps kb (by decide)).trans (WinKeep.of_keep kt)⟩
    rw [tp, kb.2.1]
    exact pointAdd_rep ha hr
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    refine WP.block_nil ⟨by rw [zero_smul, add_zero]; exact ha, rfl, WinKeep.refl _ _⟩

/-! ## Windows -/

/-- What verification's windows keep: the tables, the inputs and where they are. -/
structure WinCtx (base kp sp : Addr) (A : EPoint dZ) (s : State) : Prop where
  scratch : Scratch s base
  kHeader : s.mem.readW (off base 7952) 64 = kp
  sHeader : s.mem.readW (off base 7944) 64 = sp
  kRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off kp i) 1
  sRead : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sp 32) i) 1
  kFar : ∀ i < 64, 8192 ≤ ofs base (off kp i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)
  aTab : TableOf id s.mem base 5376 A
  bTab : TableOf cache s.mem base 2048 (-baseAff)

/-- Four doublings of the point in slots 0–3, as a window runs them:
`double4` with the field arithmetic, or `Ifma.double4`. -/
class EdDouble (dbl : Prog isa) : Prop where
  ok : ∀ {s : State} {base : Addr} {a : EPoint dZ}, Scratch s base →
    Rep (point (env s.mem base) 0 1 2 3) a → WP isa dbl s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ WinKeep base s t
  ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) dbl (fun _ _ => True)

variable {dbl : Prog isa} [EdDouble dbl]

theorem win_tablePoint {base : Addr} {m m' : Mem} (h : Outside base 56 1832 m m') {d : Nat}
    (hd : 1888 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega)),
    Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega))]

theorem TableOf.of_win {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {base : Addr} {m m' : Mem}
    {o : Nat} {X : EPoint dZ} (h : TableOf f m base o X) (k : Outside base 56 1832 m m')
    (ho : 1888 ≤ o) (hb : o + 1920 ≤ 8192) : TableOf f m' base o X := by
  intro j hj
  obtain ⟨q, hq, hr⟩ := h j hj
  exact ⟨q, by rw [win_tablePoint k (by omega) (by omega)]; exact hq, hr⟩

theorem Outside.widen {base : Addr} {m m' : Mem} (h : Outside base 64 1824 m m') :
    Outside base 56 1832 m m' := h.mono (by decide) (by decide)

theorem WinKeep.header {base : Addr} {s t : State} (h : WinKeep base s t) {d : Nat} (hd : 1888 ≤ d)
    (hb : d + 8 ≤ 8192) : t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (Or.inr (by omega)) (by omega)

theorem WinCtx.of_keep {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.header (by decide) (by decide)).trans h.kHeader,
    (k.header (by decide) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win (Outside.widen k.mem) (by decide) (by decide), h.bTab.of_win (Outside.widen k.mem) (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem WinCtx.byteK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 64) : t.mem (off kp i) = s.mem (off kp i) :=
  k.mem _ (by have := h.kFar i hi; omega)

theorem WinCtx.byteS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 32) :
    t.mem (off (off sp 32) i) = s.mem (off (off sp 32) i) :=
  k.mem _ (by have := h.sFar i hi; omega)

theorem off_zero (p : Addr) : off p 0 = p := by
  simp only [off, BitVec.add_zero]

/-- A digit's code, with its value `v`, from any state the window has reached. -/
def DigitSpec (base : Addr) (s : State) (digit : List Instr) (v : Nat) : Prop :=
  ∀ t, WinKeep base s t → WP isa (.block digit) t fun u =>
    u.gpr .rbx = BitVec.ofNat 64 v ∧ u.zf = some (decide (v = 0)) ∧ Keeps [.rsi, .rax, .rbx] t u

theorem windowA_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a)
    {digit : List Instr} {v : Nat} (hv : v < 16) (hdig : DigitSpec base s digit v) :
    WP isa (windowA fld dbl digit) s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + v • A) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowA]
  refine WP.seq (WP.mono (EdDouble.ok h.scratch ha) fun b ⟨br, bh, kb⟩ => ?_)
  refine WP.seq (WP.mono (hdig b kb) fun c ⟨cv, cz, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a) pointAdd_spec (kbc.scratch h.scratch) (by decide) (by decide)
    (h.aTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) v hv cv cz
    (by rw [kc.2.1, bh 16 (by decide)]; exact hd) (by rw [kc.2.1]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.2.1, bh 16 (by decide)]; exact hd, kbc.trans kt⟩

theorem windowAB_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a)
    {digitA digitB : List Instr} {vA vB : Nat} (hvA : vA < 16) (hvB : vB < 16)
    (hdA : DigitSpec base s digitA vA) (hdB : DigitSpec base s digitB vB) :
    WP isa (windowAB fld dbl digitA digitB) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + vA • A + vB • (-baseAff)) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowAB]
  refine WP.seq (WP.mono (windowA_ok h hd ha hvA hdA) fun b ⟨br, bd, kb⟩ => ?_)
  refine WP.seq (WP.mono (hdB b kb) fun c ⟨cv, cz, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a + vA • A) pointAddCached_spec (kbc.scratch h.scratch)
    (by decide) (by decide) (h.bTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) vB hvB cv cz
    (by rw [kc.2.1]; exact bd) (by rw [kc.2.1]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.2.1]; exact bd, kbc.trans kt⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.CombConstants`. -/
section
/-!
# The comb's tables represent `[k 256^j]B`, and `combG` represents `[G]B`

Each entry is turned back into affine `(x, y)` (`uncache`, which the kernel
checks inverts the caching) and `checkTables` walks the tables once: within
table `j`, each entry is the previous one plus the first, with the
specification's addition, compared projectively; the first entry of table `j +
1` is `[256]` of table `j`'s, with the specification's `pointMul`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- `1/2`. -/
def half : Fe := ⟨(Spec.X25519.P + 1) / 2, by decide⟩

/-- The affine `(x, y)` of a cached entry `[y - x, y + x, 2dxy]` with `Z = 1`. -/
def uncache (e : Fe × Fe × Fe) : Fe × Fe := ((e.2.1 - e.1) * half, (e.2.1 + e.1) * half)

/-- The entries `p`, `p + b`, `p + 2b`, …, each compared with `p`'s representative. -/
private def checkRow (b p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkRow b (pointAdd (affPt q) b) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (affPt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, hz⟩, hrest⟩ := hc
    have hq : Rep (affPt q) a := by
      refine h.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_
        (by show toZ (q.1 * q.2) * toZ 1 = toZ q.1 * toZ q.2; rw [toZ_mul, toZ_one, mul_one])
      · show toZ q.1 * toZ p.Z = toZ p.X * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hx]
      · show toZ q.2 * toZ p.Z = toZ p.Y * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hy]
    cases i with
    | zero => simpa using hq
    | succ i =>
      have := ih _ _ (pointAdd_rep hq hb) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ]
      convert this using 1
      rw [succ_nsmul]; abel

/-- Each table checked from the representative `b` of its first entry. -/
private def checkTables (b : Point) : List (List (Fe × Fe)) → Bool
  | [] => true
  | row :: rows => checkRow b b row && checkTables (pointMul 256 b) rows

private theorem checkTables_ok (b : Point) (c : EPoint dZ) (hb : Rep b c)
    (rows : List (List (Fe × Fe))) (hc : checkTables b rows = true) (j : Nat) (hj : j < rows.length)
    (k : Nat) (hk : k < (rows.getD j []).length) :
    Rep (affPt ((rows.getD j []).getD k (0, 1))) ((k + 1) • ((256 ^ j) • c)) := by
  induction rows generalizing b c j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons row rows ih =>
    simp only [checkTables, Bool.and_eq_true] at hc
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at hk ⊢
      have := checkRow_ok b b c c hb hb row hc.1 k hk
      rw [pow_zero, one_nsmul, succ_nsmul]
      exact this
    | succ j =>
      rw [List.getD_cons_succ] at hk ⊢
      have := ih (pointMul 256 b) ((256 : Nat) • c) (pointMul_rep 256 hb) hc.2 j
        (by simp only [List.length_cons] at hj; omega) hk
      rw [smul_smul, smul_smul] at this
      rw [smul_smul, pow_succ, ← Nat.mul_assoc]
      exact this

private theorem tables_check :
    checkTables basePoint (combTable.map (·.map uncache)) = true := by decide +kernel

/-- The caching of `affPt (uncache e)`. -/
private def recache (e : Fe × Fe × Fe) : Fe × Fe × Fe :=
  ((uncache e).2 - (uncache e).1, (uncache e).2 + (uncache e).1,
    (uncache e).1 * (uncache e).2 * 2 * d)

private theorem tables_cached :
    combTable.all (fun row => row.all fun e => decide (recache e = e)) = true := by decide +kernel

private theorem tables_length :
    combTable.length = 32 ∧ combTable.all (fun row => row.length == 8) = true := by decide +kernel

private theorem getD_map' {α β : Type} (l : List α) (f : α → β) (n : Nat) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

private theorem uncache_default : uncache (1, 1, 0) = (0, 1) := by decide

theorem combCached_ok (j k : Nat) (hj : j < 32) (hk : k < 9) :
    ∃ q, combCached j k = cache q ∧ Rep q ((k * 256 ^ j) • baseAff) := by
  cases k with
  | zero =>
    refine ⟨identity, ?_, ?_⟩
    · simp only [combCached, ↓reduceIte]; decide +kernel
    · rw [Nat.zero_mul, zero_smul]; exact identity_rep
  | succ k =>
    have hrow : (combTable.getD j []) ∈ combTable := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tables_length.1]; exact hj)]
      exact List.getElem_mem _
    have hlen : (combTable.getD j []).length = 8 :=
      beq_iff_eq.mp (List.all_eq_true.mp tables_length.2 _ hrow)
    have hmem : (combTable.getD j []).getD k (1, 1, 0) ∈ combTable.getD j [] := by
      have hk' : k < (combTable.getD j []).length := by rw [hlen]; omega
      rw [List.getD_eq_getElem?_getD (l := combTable.getD j []), List.getElem?_eq_getElem hk']
      exact List.getElem_mem _
    have hre := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp tables_cached _ hrow) _ hmem)
    refine ⟨affPt (uncache ((combTable.getD j []).getD k (1, 1, 0))), ?_, ?_⟩
    · simp only [combCached, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      generalize (combTable.getD j []).getD k (1, 1, 0) = e at hre
      obtain ⟨a, b, c⟩ := e
      simp only [recache, Prod.mk.injEq] at hre
      simp only [cache, affPt, Point.mk.injEq]
      exact ⟨hre.1.symm, hre.2.1.symm, hre.2.2.symm, rfl⟩
    · have hgj : (combTable.map (·.map uncache)).getD j [] = (combTable.getD j []).map uncache := by
        rw [show ([] : List (Fe × Fe)) = ([] : List (Fe × Fe × Fe)).map uncache from rfl, getD_map']
      have hr := checkTables_ok basePoint baseAff basePoint_rep _ tables_check j
        (by rw [List.length_map, tables_length.1]; exact hj) k
        (by rw [hgj, List.length_map, hlen]; omega)
      rw [hgj, ← uncache_default, getD_map', smul_smul] at hr
      exact hr

/-- The constant the comb's digits are offset by: `8 Σ_{j < 32} 256^j`. -/
def combGVal : Nat := 8 * ((256 ^ 32 - 1) / 255)

private def combGCheck (p : Point) : Bool := combG.X * p.Z == p.X && combG.Y * p.Z == p.Y && p.Z != 0

private theorem combG_check : combGCheck (pointMul combGVal basePoint) = true := by decide +kernel

theorem combG_ok : Rep combG (combGVal • baseAff) := by
  have hp := pointMul_rep combGVal basePoint_rep
  have hc := combG_check
  simp only [combGCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  refine hp.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_ ?_
  · show toZ combG.X * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ combG.Y * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]
  · show toZ (combGAff.1 * combGAff.2) * toZ 1 = toZ combGAff.1 * toZ combGAff.2
    rw [toZ_mul, toZ_one, mul_one]

theorem combGCached_eq : combGCached = cache combG := by decide +kernel

end VG.Proof.Ed25519.X86_64
end

/-!
# The comb's constant-time selection

`combMask k` stores all ones exactly when the digit in `rax` is `k`, and zero
otherwise; `selectField` then ORs every candidate's words, each ANDed with its
mask, so only the digit's candidate survives.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The mask of candidate `k`, for the digit `d`. -/
def maskVal (d k : Nat) : BitVec 64 := if d = k then BitVec.allOnes 64 else 0

private theorem mask_fact : ∀ d < 16, ∀ k < 16,
    ((BitVec.ofNat 64 d ^^^ (BitVec.ofNat 32 k).signExtend 64) - (1 : BitVec 32).signExtend 64) -
      ((BitVec.ofNat 64 d ^^^ (BitVec.ofNat 32 k).signExtend 64) - (1 : BitVec 32).signExtend 64) -
      (BitVec.ofBool (decide ((BitVec.ofNat 64 d ^^^ (BitVec.ofNat 32 k).signExtend 64).toNat <
        ((1 : BitVec 32).signExtend 64).toNat))).setWidth 64 = maskVal d k := by
  decide +kernel

theorem combMask_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 d) (k : Nat) (hk : k < 16) :
    WP isa (.block (combMask k)) s fun t =>
      t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base (combMasks + 8 * k) 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base (combMasks + 8 * k)) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by simp only [combMasks]; omega) (by simp only [combMasks]; omega)⟩
  apply WP.of_runBlock
  simp only [combMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hax, hw, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, trivial, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact mask_fact d hd k hk
  · simp only [hr, ite_false]
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by simp only [combMasks]; omega)

theorem combMaskPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 d) (n : Nat) (hn : n ≤ 16) :
    WP isa (.block ((List.range n).flatMap combMask)) s fun t =>
      (∀ k < n, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base combMasks 128 s.mem t.mem := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl,
      Outside.refl _ _ _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, tg, tr, tw, tm⟩ => ?_
    have ht : Scratch t base := ⟨(tg _ (by decide)).trans hs.rdi, tw ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (combMask_ok ht hd ((tg _ (by decide)).trans hax) n (by omega))
      fun u ⟨uv, ug, ur, uw, um⟩ => ?_
    refine ⟨fun k hk => ?_, fun r hr => (ug r hr).trans (tg r hr), ur.trans tr, uw.trans tw,
      tm.trans (um.mono (by simp only [combMasks]; omega) (by simp only [combMasks]; omega))⟩
    by_cases h : k < n
    · exact (um.word (d := combMasks + 8 * k) (Or.inl (by omega))
        (by simp only [combMasks]; omega)).trans (tv k h)
    · obtain rfl : k = n := by omega
      exact uv

theorem combMaskAll_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 d) :
    WP isa (.block combMaskAll) s fun t =>
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base combMasks 128 s.mem t.mem :=
  combMaskPrefix_ok hs hd hax 9 (by decide)

/-! ## Selection -/

theorem selectCand_ok {s : State} {base : Addr} (hs : Scratch s base) (v : Spec.X25519.Fe) (k : Nat)
    (hk : k < 16) {m : BitVec 64} (hm : s.mem.readW (off base (combMasks + 8 * k)) 64 = m) :
    WP isa (.block ((List.range 4).flatMap fun w => selectWord v k w)) s fun t =>
      t.gpr .r8 = s.gpr .r8 ||| (feWord v 0 &&& m) ∧ t.gpr .r9 = s.gpr .r9 ||| (feWord v 1 &&& m) ∧
      t.gpr .r10 = s.gpr .r10 ||| (feWord v 2 &&& m) ∧
      t.gpr .r11 = s.gpr .r11 ||| (feWord v 3 &&& m) ∧ Keeps [.rcx, .r8, .r9, .r10, .r11] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (combMasks + 8 * k)) 8 :=
    ⟨_, List.mem_append_right _ hs.wr,
      Offset.contains_base _ (by simp only [combMasks]; omega) (by simp only [combMasks]; omega)⟩
  rw [show ((List.range 4).flatMap fun w => selectWord v k w) =
    [.movImm64 .rcx (feWord v 0), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r8 (.reg .rcx),
      .movImm64 .rcx (feWord v 1), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r9 (.reg .rcx),
      .movImm64 .rcx (feWord v 2), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r10 (.reg .rcx),
      .movImm64 .rcx (feWord v 3), .alu .and .rcx (.mem (Impl.X25519.X86_64.sc (combMasks + 8 * k))),
      .alu .or .r11 (.reg .rcx)] from rfl]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, hs.rdi, hr, hm, ite_true, ite_false, reduceCtorEq, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
      RegUpd.wr_setReg, RegUpd.wr_arithFlags, and_self]

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp
private theorem zero_or' (x : BitVec 64) : 0 ||| x = x := by ext i; simp
private theorem zero_or_and_ones (x : BitVec 64) : 0 ||| (x &&& BitVec.allOnes 64) = x := by
  rw [BitVec.and_allOnes, zero_or']
private theorem or_zero' (x : BitVec 64) : x = x ||| 0 := by ext i; simp

theorem sel_step (d n : Nat) (x y : BitVec 64) (hy : d = n → y = x) :
    (if d < n then x else 0) ||| (y &&& maskVal d n) = if d < n + 1 then x else 0 := by
  by_cases h : d < n
  · have hne : d ≠ n := by omega
    simp only [maskVal, h, hne, ↓reduceIte, show d < n + 1 by omega]
    exact or_and_zero x y
  · by_cases he : d = n
    · subst he
      simp only [maskVal, h, ↓reduceIte, Nat.lt_add_one, hy rfl]
      exact zero_or_and_ones x
    · simp only [maskVal, h, he, ↓reduceIte, show ¬ d < n + 1 by omega]
      exact or_and_zero 0 y

/-- The candidates `k < n`, from cleared registers. -/
theorem selectCands_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat}
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k)
    (vs : List Spec.X25519.Fe) (n : Nat) (hn : n ≤ 9) :
    WP isa (.block ((List.range n).flatMap fun k => (List.range 4).flatMap fun w =>
      selectWord (vs.getD k 0) k w)) s fun t =>
      t.gpr .r8 = s.gpr .r8 ||| (if d < n then feWord (vs.getD d 0) 0 else 0) ∧
      t.gpr .r9 = s.gpr .r9 ||| (if d < n then feWord (vs.getD d 0) 1 else 0) ∧
      t.gpr .r10 = s.gpr .r10 ||| (if d < n then feWord (vs.getD d 0) 2 else 0) ∧
      t.gpr .r11 = s.gpr .r11 ||| (if d < n then feWord (vs.getD d 0) 3 else 0) ∧
      Keeps [.rcx, .r8, .r9, .r10, .r11] s t := by
  induction n with
  | zero =>
    refine WP.block_nil ⟨?_, ?_, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl⟩ <;>
      simp only [Nat.not_lt_zero, ↓reduceIte] <;> exact or_zero' _
  | succ n ih =>
    rw [List.range_succ (n := n), List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t8, t9, t10, t11, kt⟩ => ?_
    have ht : Scratch t base := ⟨(kt.1 _ (by decide)).trans hs.rdi, kt.2.2.2 ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (selectCand_ok (m := maskVal d n) ht (vs.getD n 0) n (by omega)
      (by rw [kt.2.1]; exact hm n (by omega))) fun u ⟨u8, u9, u10, u11, ku⟩ => ?_
    have hy : ∀ w, d = n → feWord (vs.getD n 0) w = feWord (vs.getD d 0) w := fun _ h => by rw [h]
    refine ⟨?_, ?_, ?_, ?_, ⟨fun r hr => (ku.1 r hr).trans (kt.1 r hr), ku.2.1.trans kt.2.1,
      ku.2.2.1.trans kt.2.2.1, ku.2.2.2.trans kt.2.2.2⟩⟩
    · rw [u8, t8, BitVec.or_assoc, sel_step d n _ _ (hy 0)]
    · rw [u9, t9, BitVec.or_assoc, sel_step d n _ _ (hy 1)]
    · rw [u10, t10, BitVec.or_assoc, sel_step d n _ _ (hy 2)]
    · rw [u11, t11, BitVec.or_assoc, sel_step d n _ _ (hy 3)]

/-- `store4`, in the larger scratch. -/
theorem store4W_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat} (ho : o + 32 ≤ 8192) :
    WP isa (.block (Impl.X25519.X86_64.store4 o)) s fun t =>
      t.mem = Proof.X25519.X86_64.st4 s.mem base o (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, Offset.contains_base base hd (by omega)⟩
  apply WP.of_runBlock
  simp only [Impl.X25519.X86_64.store4, Impl.X25519.X86_64.stores, runBlock_cons, runStep_some,
    runBlock_nil, exec, Proof.X25519.X86_64.ea_sc, hs.rdi, State.store64, w o (by omega),
    w (o + 8) (by omega), w (o + 16) (by omega), w (o + 24) (by omega), ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ => trivial, trivial, trivial⟩

theorem feWord_val (v : Spec.X25519.Fe) :
    Proof.X25519.X86_64.val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem selectField_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k)
    (vs : List Spec.X25519.Fe) {o : Nat} (ho : o + 32 ≤ 8192) :
    WP isa (.block (selectField vs o)) s fun t =>
      Proof.X25519.X86_64.F t.mem base o = vs.getD d 0 ∧
      (∀ r, r ∉ [Reg.rcx, .r8, .r9, .r10, .r11] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base o 32 s.mem t.mem := by
  rw [selectField, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Proof.X25519.X86_64.zero4_ok s) fun a ⟨a8, a9, a10, a11, ka⟩ => ?_
  have ha : Scratch a base := ⟨(ka.1 _ (by decide)).trans hs.rdi, ka.2.2.2 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok (d := d) ha (by rw [ka.2.1]; exact hm) vs 9 (Nat.le_refl _))
    fun b ⟨b8, b9, b10, b11, kb⟩ => ?_
  have hb : Scratch b base := ⟨(kb.1 _ (by decide)).trans ha.rdi, kb.2.2.2 ▸ ha.wr, hs.nowrap⟩
  refine WP.mono (store4W_ok hb ho) fun t ⟨tm, tg, tr, tw⟩ => ?_
  refine ⟨?_, fun r hr => ?_, tr.trans (kb.2.2.1.trans ka.2.2.1), tw.trans (kb.2.2.2.trans ka.2.2.2),
    ?_⟩
  · rw [tm, Proof.X25519.X86_64.F, Proof.X25519.X86_64.fe_st4 _ _ (by omega), b8, b9, b10, b11, a8, a9,
      a10, a11]
    simp only [hd, ↓reduceIte, zero_or']
    rw [feWord_val, Proof.X25519.toFe_self]
  · rw [tg, kb.1 r hr, ka.1 r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h <;> simp [h]))]
  · rw [tm, kb.2.1, ka.2.1]
    exact Proof.X25519.X86_64.st4_outside _ _ (by omega) _ _ _ _

private theorem entries_getD (j d : Nat) (hd : d < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD d 0 = f (combCached j d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd, Option.map_some,
    Option.getD_some]

/-- A field selected to slot `i` (4 to 7), keeping the masks and the slots below. -/
private theorem selectSlot_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k)
    (vs : List Spec.X25519.Fe) (i : Slot) (hi : 4 ≤ i.val) (hi' : i.val < 8) :
    WP isa (.block (selectField vs (offset i))) s fun t =>
      env t.mem base i = vs.getD d 0 ∧
      (∀ i' : Slot, i' ≠ i → env t.mem base i' = env s.mem base i') ∧ Keep base s t ∧
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) := by
  refine WP.mono (selectField_ok hs hd hm vs (by simp only [offset]; omega))
    fun t ⟨tv, tg, tr, tw, tm⟩ => ⟨tv, fun i' hi' => ?_, ⟨fun r hr => tg r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> decide)), tr, tw,
      tm.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      fun k hk => (tm.word (d := combMasks + 8 * k) (Or.inr (by simp only [offset, combMasks]; omega))
        (by simp only [combMasks]; omega)).trans (hm k hk)⟩
  have hne : i'.val ≠ i.val := fun h => hi' (Fin.ext h)
  exact Outside_F tm (by simp only [offset]; omega) (by simp only [offset]; omega)

theorem combSelect_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) (j : Nat) :
    WP isa (.block (combSelect j)) s fun t =>
      point (env t.mem base) 4 5 6 7 = combCached j d ∧ Keep base s t ∧
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok hs hd hm _ 4 (by decide) (by decide)) fun a ⟨av, ao, ka, am⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok (hs.of_keep ka) hd am _ 5 (by decide) (by decide))
    fun b ⟨bv, bo, kb, bm⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectSlot_ok ((hs.of_keep ka).of_keep kb) hd bm _ 6 (by decide) (by decide))
    fun c ⟨cv, co, kc, cm⟩ => ?_
  refine WP.mono (selectSlot_ok (((hs.of_keep ka).of_keep kb).of_keep kc) hd cm _ 7 (by decide)
    (by decide)) fun t ⟨tv, tO, kt, tm⟩ => ⟨?_, ((ka.trans kb).trans kc).trans kt, tm, fun i hi => ?_⟩
  · rw [entries_getD j d hd] at av bv cv tv
    simp only [point, tv, tO 6 (by decide), cv, tO 5 (by decide), co 5 (by decide), bv,
      tO 4 (by decide), co 4 (by decide), bo 4 (by decide), av]
  · have ne : ∀ (k : Nat) (h2 : k < 8), 4 ≤ k → i ≠ (⟨k, by omega⟩ : Slot) := fun k _ h1 h => by
      have := congrArg Fin.val h; simp only at this; omega
    rw [tO i (ne 7 (by decide) (by decide)), co i (ne 6 (by decide) (by decide)),
      bo i (ne 5 (by decide) (by decide)), ao i (ne 4 (by decide) (by decide))]

theorem rdxCmp_ok (s : State) (j k : Nat) (hj : j < 32) (hk : k < 32)
    (hc : s.gpr .rdx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (j = k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 32, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hk
  have hz : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hc, he, hz, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

theorem combSelectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 32) {s : State} {j : Nat}
    (hj : j ∈ ks) (hj32 : j < 32) (hc : s.gpr .rdx = BitVec.ofNat 64 j) {Q : State → Prop}
    (hq : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block (combSelect j)) s' Q) :
    WP isa (combSelectFrom ks) s Q := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    rw [combSelectFrom]
    refine WP.seq (WP.mono (rdxCmp_ok s j k hj32 (hks k (by simp)) hc)
      fun t ⟨tz, tg, tm, tr, tw⟩ => ?_)
    refine WP.ite (decide (j = k)) (by simp only [eval, tz]) (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      exact hq t tg tm tr tw
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      exact ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) hj' (by rw [tg]; exact hc)
        (fun s' g m r w => hq s' (g.trans tg) (m.trans tm) (r.trans tr) (w.trans tw))

theorem combSelectAll_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d < 9)
    (hm : ∀ k < 9, s.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) {j : Nat}
    (hj : j < 32) (hc : s.gpr .rdx = BitVec.ofNat 64 j) :
    WP isa (combSelectFrom (List.range 32)) s fun t =>
      point (env t.mem base) 4 5 6 7 = combCached j d ∧ Keep base s t ∧
      (∀ k < 9, t.mem.readW (off base (combMasks + 8 * k)) 64 = maskVal d k) ∧
      (∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  refine combSelectFrom_ok _ (fun k hk => List.mem_range.mp hk) (List.mem_range.mpr hj) hj hc ?_
  intro t tg tm tr tw
  have ht : Scratch t base := ⟨by rw [tg]; exact hs.rdi, tw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (combSelect_ok ht hd (by rw [tm]; exact hm) j) fun u ⟨uv, ku, um, ue⟩ =>
    ⟨uv, ?_, um, fun i hi => by rw [ue i hi, tm]⟩
  exact ⟨fun r hr => (ku.gpr r hr).trans (by rw [tg]), ku.rd.trans tr, ku.wr.trans tw,
    by rw [← tm]; exact ku.mem⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.CombDigit`. -/
section
/-!
# The comb's digits

Step `c` reads digit `2c + 1` (`c < 32`) or `2(c - 32)` of the scalar from its
bits, expanded one per byte at byte 768 of the scratch (`combIdx`), by
Horner's rule.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The digit step `c` reads. -/
def combIdx (c : Nat) : Nat := if c < 32 then 2 * c + 1 else 2 * (c - 32)

theorem combIdx_lt {c : Nat} (hc : c < 64) : combIdx c < 64 := by
  unfold combIdx; split <;> omega

theorem combIndex_ok (s : State) {c : Nat} (hc : c < 64) (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa combIndex s fun t => t.gpr .rcx = BitVec.ofNat 64 (4 * combIdx c) ∧ Keeps [.rcx] s t := by
  rw [combIndex]
  have h8 : BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c) +
      (BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c)) =
      BitVec.ofNat 64 (8 * c) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hcf : decide ((BitVec.ofNat 64 c).toNat < ((32 : BitVec 32).signExtend 64).toNat) =
      decide (c < 32) := by
    rw [show (32 : BitVec 32).signExtend 64 = BitVec.ofNat 64 32 from rfl, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    congr 1; apply propext; omega
  refine WP.seq (WP.mono (show WP isa (.block [.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx),
      .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .cmp .rbx (.imm 32)]) s
      (fun t => t.gpr .rcx = BitVec.ofNat 64 (8 * c) ∧ t.cf = some (decide (c < 32)) ∧
        Keeps [.rcx] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, hb, h8, hcf, ite_true,
      ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun a ⟨ac, af, ka⟩ => ?_)
  refine WP.ite (decide (c < 32)) (by simp only [eval, af]) (fun h => ?_) (fun h => ?_)
  · have hc32 : c < 32 := of_decide_eq_true h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ac, ite_true, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [combIdx, hc32, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (4 : BitVec 32).signExtend 64 = BitVec.ofNat 64 4 from rfl]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]; exact ka.1 r (by simpa using hr)
  · have hc32 : ¬ c < 32 := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ac, ite_true, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [combIdx, hc32, ↓reduceIte, BitVec.toNat_sub, BitVec.toNat_ofNat,
        show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]; exact ka.1 r (by simpa using hr)

theorem digit_bits (S i : Nat) :
    (S / 16 ^ i) % 16 = ((((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
      (S / 2 ^ (4 * i + 1)) % 2) * 2 + (S / 2 ^ (4 * i)) % 2) := by
  have h16 : 16 ^ i = 2 ^ (4 * i) := by rw [pow_mul]; norm_num
  have e : ∀ t, S / 2 ^ (4 * i + t) = S / 16 ^ i / 2 ^ t := fun t => by
    rw [h16, Nat.div_div_eq_div_mul, ← pow_add]
  rw [e 3, e 2, e 1, ← Nat.add_zero (4 * i), e 0]
  simp only [pow_zero, Nat.div_one, Nat.reducePow]
  omega

theorem combBit_ea {s : State} {base : Addr} (hs : Scratch s base) {i : Nat}
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (4 * i)) (t : Nat) :
    s.ea { base := .rdi, index := some .rcx, disp := 768 + (t : Int) } =
      off base (768 + (4 * i + t)) := by
  simp only [State.ea, hs.rdi, hrcx, BitVec.mul_one]
  rw [show (768 : Int) + (t : Int) = ((768 + t : Nat) : Int) by omega, BitVec.ofInt_natCast,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (off base) (by omega)

theorem loadBit_ok {s : State} {base : Addr} (hs : Scratch s base) {S i : Nat} (hi : i < 64)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (4 * i))
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (dst : Reg) (t : Nat) (ht : t < 4) :
    WP isa (.block [combBit dst t]) s fun u =>
      u.gpr dst = BitVec.ofNat 64 ((S / 2 ^ (4 * i + t)) % 2) ∧ Keeps [dst] s u := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + t))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have bit : (s.mem (off base (768 + (4 * i + t)))).setWidth 64 =
      BitVec.ofNat 64 ((S / 2 ^ (4 * i + t)) % 2) := by
    rw [hb _ (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [combBit, runBlock_cons, runStep_some, runBlock_nil, exec, State.load8,
    combBit_ea hs hrcx, hr, bit, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem addRax_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add .rax (.reg r)]) s fun u =>
      u.gpr .rax = s.gpr .rax + s.gpr r ∧ Keeps [.rax] s u := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

theorem combDigit_ok {s : State} {base : Addr} (hs : Scratch s base) {S i : Nat} (hi : i < 64)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (4 * i))
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combDigit) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((S / 16 ^ i) % 16) ∧ Keeps [.rax, .rdx] s t := by
  rw [show combDigit = [combBit .rax 3] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 2] ++
      ([.alu .add .rax (.reg .rdx)] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 1] ++
      ([.alu .add .rax (.reg .rdx)] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 0] ++
      [.alu .add .rax (.reg .rdx)])))))))) from rfl]
  have keep : ∀ {x y : State} {rs : List Reg}, Keeps rs x y → (∀ r ∈ rs, r = .rax ∨ r = .rdx) →
      Keeps [.rax, .rdx] x y := fun k h => ⟨fun r hr => k.1 r (fun hm => by
        rcases h r hm with rfl | rfl <;> simp at hr), k.2⟩
  have tr : ∀ {x y z : State}, Keeps [.rax, .rdx] x y → Keeps [.rax, .rdx] y z →
      Keeps [.rax, .rdx] x z := fun a b => ⟨fun r hr => (b.1 r hr).trans (a.1 r hr),
        b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.trans a.2.2.2⟩
  have st : ∀ {x : State}, Keeps [.rax, .rdx] s x → Scratch x base ∧
      x.gpr .rcx = BitVec.ofNat 64 (4 * i) ∧
      ∀ q < 256, x.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun k =>
    ⟨⟨(k.1 _ (by decide)).trans hs.rdi, k.2.2.2 ▸ hs.wr, hs.nowrap⟩,
      (k.1 _ (by decide)).trans hrcx, fun q hq => by rw [k.2.1]; exact hb q hq⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hs hi hrcx hb .rax 3 (by decide)) fun a ⟨a3, ka⟩ => ?_
  have ka' := keep ka (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok a .rax) fun b ⟨bv, kb⟩ => ?_
  have kb' := tr ka' (keep kb (by simp))
  obtain ⟨hsb, hcb, hbb⟩ := st kb'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsb hi hcb hbb .rdx 2 (by decide)) fun c ⟨c2, kc⟩ => ?_
  have kc' := tr kb' (keep kc (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok c .rdx) fun d ⟨dv, kd⟩ => ?_
  have kd' := tr kc' (keep kd (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok d .rax) fun e ⟨ev, ke⟩ => ?_
  have ke' := tr kd' (keep ke (by simp))
  obtain ⟨hse, hce, hbe⟩ := st ke'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hse hi hce hbe .rdx 1 (by decide)) fun f ⟨f1, kf⟩ => ?_
  have kf' := tr ke' (keep kf (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok f .rdx) fun g ⟨gv, kg⟩ => ?_
  have kg' := tr kf' (keep kg (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok g .rax) fun h ⟨hv, kh⟩ => ?_
  have kh' := tr kg' (keep kh (by simp))
  obtain ⟨hsh, hch, hbh⟩ := st kh'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsh hi hch hbh .rdx 0 (by decide)) fun u ⟨u0, ku⟩ => ?_
  have ku' := tr kh' (keep ku (by simp))
  refine WP.mono (addRax_ok u .rdx) fun t ⟨tv, kt⟩ => ⟨?_, tr ku' (keep kt (by simp))⟩
  rw [tv, u0, ku.1 _ (by decide), hv, gv, f1, kf.1 _ (by decide), ev, dv, c2, kc.1 _ (by decide), bv,
    a3, digit_bits S i, Nat.add_zero]
  have l0 := Nat.mod_lt (S / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have l1 := Nat.mod_lt (S / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have l2 := Nat.mod_lt (S / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have l3 := Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  generalize S / 2 ^ (4 * i) % 2 = b0 at *
  generalize S / 2 ^ (4 * i + 1) % 2 = b1 at *
  generalize S / 2 ^ (4 * i + 2) % 2 = b2 at *
  generalize S / 2 ^ (4 * i + 3) % 2 = b3 at *
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.CombSign`. -/
section
/-!
# The comb's signed digits

`combSign` turns the nibble `n` into the digit `n - 8`'s magnitude, in `rax`,
and the mask of its sign, at byte `combSignMask`; `combNeg` negates the
selected cached point in slots 4–7 under that mask.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The magnitude of the digit `n - 8`. -/
def mag (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

/-- The mask of the digit `n - 8`'s sign: all ones if it is negative. -/
def signMask (n : Nat) : BitVec 64 := if n < 8 then BitVec.allOnes 64 else 0

private theorem sign_fact : ∀ n < 16,
    ((BitVec.ofNat 64 n - (8 : BitVec 32).signExtend 64 ^^^
        0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
          ((8 : BitVec 32).signExtend 64).toNat))).setWidth 64) -
      (0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
        ((8 : BitVec 32).signExtend 64).toNat))).setWidth 64) = BitVec.ofNat 64 (mag n)) ∧
    0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
      ((8 : BitVec 32).signExtend 64).toNat))).setWidth 64 = signMask n := by
  decide +kernel

theorem combSign_ok {s : State} {base : Addr} (hs : Scratch s base) {n : Nat} (hn : n < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 n) :
    WP isa (.block combSign) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (mag n) ∧ t.mem.readW (off base combSignMask) 64 = signMask n ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base combSignMask 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base combSignMask) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)⟩
  apply WP.of_runBlock
  simp only [combSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hax, hw, ite_true, ite_false, reduceCtorEq,
    BitVec.sub_self, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, ?_, fun r h1 h2 => ?_, rfl, trivial, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact (sign_fact n hn).2
  · simp only [h1, h2, ite_false]
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by simp only [combSignMask]; omega)

/-! ## The negation -/

/-- The cached point `c` negated: `[Y + X, Y - X, -2dT, 2Z]` for `[Y - X, Y + X, 2dT, 2Z]`. -/
def negCached (c : Spec.Ed25519.Point) : Spec.Ed25519.Point := ⟨c.Y, c.X, 0 - c.Z, c.T⟩

theorem negCached_cache (q : Spec.Ed25519.Point) : negCached (cache q) = cache (negPoint q) := by
  simp only [negCached, cache, negPoint, Spec.Ed25519.Point.mk.injEq]
  refine ⟨toZ_inj.1 ?_, toZ_inj.1 ?_, toZ_inj.1 ?_, trivial⟩ <;>
    simp only [toZ_add, toZ_sub, toZ_mul, toZ_zero] <;> ring

variable {fld : Arith} [EdArith fld]

theorem loadSignMask_ok {s : State} {base : Addr} (hs : Scratch s base) {m : BitVec 64}
    (hm : s.mem.readW (off base combSignMask) 64 = m) :
    WP isa (.block [.mov .rcx (.mem (Impl.X25519.X86_64.sc combSignMask))]) s fun t =>
      t.gpr .rcx = m ∧ Keeps [.rcx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base combSignMask) 8 :=
    ⟨_, List.mem_append_right _ hs.wr,
      Offset.contains_base _ (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, hs.rdi, hr, hm, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem signMask_eq (n : Nat) : signMask n = Proof.X25519.X86_64.mask (decide (n < 8)) := by
  by_cases h : n < 8 <;> simp [signMask, Proof.X25519.X86_64.mask, h]

theorem combNeg_ok {s : State} {base : Addr} (hs : Scratch s base) {n : Nat}
    (hm : s.mem.readW (off base combSignMask) 64 = signMask n) :
    WP isa (.block (combNeg fld)) s fun t =>
      point (env t.mem base) 4 5 6 7 = (if n < 8 then negCached (point (env s.mem base) 4 5 6 7)
        else point (env s.mem base) 4 5 6 7) ∧ Keep base s t ∧
      (∀ i : Slot, (i.val < 4 ∨ 10 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs _) fun a ⟨ka, va⟩ => ?_
  have hsa := hs.of_keep ka
  rw [WP.block_append_iff]
  refine WP.mono (loadSignMask_ok hsa (m := signMask n) (by
    rw [← hm]; exact ka.mem.word (Or.inr (by simp only [combSignMask]; omega))
      (by simp only [combSignMask]; omega))) fun b ⟨bc, kb⟩ => ?_
  have hsb := hsa.of_keeps kb (by decide)
  refine WP.mono (swapFieldsWide_ok hsb [(4, 5), (6, 8)]
    (fun ab h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    (sw := decide (n < 8))
    (by rw [bc, signMask_eq])) fun t ⟨kt, _, vt⟩ => ?_
  have kbk : Keep base a b := ⟨fun r hr => kb.1 r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; decide)),
    kb.2.2.1, kb.2.2.2, by rw [kb.2.1]; exact Outside.refl _ _ _ _⟩
  have ev : env t.mem base = swapEnvs [(4, 5), (6, 8)] (decide (n < 8))
      (evalOps [.const 9 0, .sub 8 9 6] (env s.mem base)) := by rw [vt, kb.2.1, va]
  refine ⟨?_, (ka.trans kbk).trans kt, fun i hi => ?_⟩
  · rw [ev]
    by_cases h : n < 8
    · simp [h, swapEnvs, swapEnv, evalOps, evalOp, point, negCached]
    · simp [h, swapEnvs, swapEnv, evalOps, evalOp, point]
  · rw [ev]
    have h4 : i ≠ 4 := fun h => by subst h; simp at hi
    have h5 : i ≠ 5 := fun h => by subst h; simp at hi
    have h6 : i ≠ 6 := fun h => by subst h; simp at hi
    have h8 : i ≠ 8 := fun h => by subst h; simp at hi
    have h9 : i ≠ 9 := fun h => by subst h; simp at hi
    simp [swapEnvs, swapEnv, evalOps, evalOp, h4, h5, h6, h8, h9]

end VG.Proof.Ed25519.X86_64
end

/-!
# The comb's loop

After step `c`, the accumulator represents `[v]B` for the partial sum `v =
combVal S c`: `G` and the odd digits `d_{2j+1} 256^j` for `j < c` while `c ≤
32`, then sixteen times all of those, `G` again, and the even digits `d_{2j}
256^j` for `j < c - 32`, with the digits `d_i = n_i - 8`. At `c = 64` that is
the scalar (`comb_sum`), since `G = 8 Σ_{j < 32} 256^j`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

/-- Digit `i` of `S` in radix 16. -/
def nib (S i : Nat) : Nat := (S / 16 ^ i) % 16

/-- `Σ_{j < c} n_{2j+1} 256^j`. -/
def oddSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddSum S c + nib S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} n_{2j} 256^j`. -/
def evenSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenSum S c + nib S (2 * c) * 256 ^ c

theorem comb_partial (S : Nat) : ∀ n, 16 * oddSum S n + evenSum S n = S % 256 ^ n
  | 0 => by simp [oddSum, evenSum, Nat.mod_one]
  | n + 1 => by
    have ih := comb_partial S n
    have h16 : 256 ^ n = 16 ^ (2 * n) := by rw [pow_mul]; norm_num
    have hd : S / 16 ^ (2 * n + 1) = S / 16 ^ (2 * n) / 16 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hm : S % 256 ^ (n + 1) = S % 256 ^ n + 256 ^ n * (S / 256 ^ n % 256) := by
      rw [pow_succ, Nat.mod_mul]
    simp only [oddSum, evenSum, nib]
    rw [hm, ← ih, hd, h16]
    generalize S / 16 ^ (2 * n) = x
    generalize 16 ^ (2 * n) = y
    have : x % 256 = x % 16 + 16 * (x / 16 % 16) := by omega
    rw [this]; ring

/-- `Σ_{j < c} 256^j`. -/
def geom : Nat → Nat
  | 0 => 0
  | c + 1 => geom c + 256 ^ c

theorem combGVal_eq : combGVal = 8 * geom 32 := by decide

/-- The comb's digit `i`: `n_i - 8`, from `-8` to `7`. -/
def sdig (S i : Nat) : ℤ := (nib S i : ℤ) - 8

/-- `Σ_{j < c} d_{2j+1} 256^j`. -/
def oddSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => oddSumZ S c + sdig S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} d_{2j} 256^j`. -/
def evenSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => evenSumZ S c + sdig S (2 * c) * 256 ^ c

theorem oddSumZ_eq (S : Nat) : ∀ c, oddSumZ S c = oddSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [oddSumZ, oddSum, geom, oddSumZ_eq S c, sdig]
    push_cast; ring

theorem evenSumZ_eq (S : Nat) : ∀ c, evenSumZ S c = evenSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [evenSumZ, evenSum, geom, evenSumZ_eq S c, sdig]
    push_cast; ring

/-- The accumulator's multiple of `B` after `c` steps. -/
def combVal (S c : Nat) : ℤ :=
  if c ≤ 32 then combGVal + oddSumZ S c else 16 * (combGVal + oddSumZ S 32) + combGVal + evenSumZ S (c - 32)

theorem comb_sum {S : Nat} (hS : S < 2 ^ (16 * 16)) : combVal S 64 = S := by
  simp only [combVal, show ¬ 64 ≤ 32 by decide, ↓reduceIte, show 64 - 32 = 32 from rfl, oddSumZ_eq,
    evenSumZ_eq, combGVal_eq]
  have h := comb_partial S 32
  rw [Nat.mod_eq_of_lt (by simpa using hS)] at h
  have h' : (16 * oddSum S 32 + evenSum S 32 : ℤ) = S := by exact_mod_cast h
  push_cast
  linear_combination h'

theorem combIdx_nib (S c : Nat) (hc : c < 64) :
    sdig S (combIdx c) * 256 ^ (c % 32) + (if c = 32 then 16 * combVal S c + combGVal else combVal S c) =
      combVal S (c + 1) := by
  unfold combIdx combVal
  by_cases h : c < 32
  · simp only [h, ↓reduceIte, show c ≠ 32 by omega, show c ≤ 32 by omega, show c + 1 ≤ 32 by omega,
      oddSumZ, Nat.mod_eq_of_lt h]
    ring
  · have hs : c + 1 - 32 = (c - 32) + 1 := by omega
    by_cases h32 : c = 32
    · subst h32
      simp only [show ¬ 32 < 32 by decide, ↓reduceIte, le_refl, show ¬ 33 ≤ 32 by decide,
        show 33 - 32 = 0 + 1 from rfl, evenSumZ]
      ring
    · simp only [h, h32, ↓reduceIte, show ¬ c ≤ 32 by omega, show ¬ c + 1 ≤ 32 by omega, hs, evenSumZ,
        show c % 32 = c - 32 by omega]
      ring

/-! ## Counters -/

theorem rbxCmp_ok (s : State) (c k : Nat) (hc : c < 64) (hk : k < 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (c = k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 64, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hk
  have hz : (BitVec.ofNat 64 c - BitVec.ofNat 64 k == 0) = decide (c = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hc, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hb, he, hz, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

private theorem mod32_fact : ∀ c < 64,
    BitVec.ofNat 64 c &&& (31 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (c % 32) := by decide

theorem rdxMod_ok (s : State) (c : Nat) (hc : c < 64) (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa (.block [.mov .rdx (.reg .rbx), .alu .and .rdx (.imm 31)]) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (c % 32) ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hb, mod32_fact c hc, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem rbxNext64_ok (s : State) (n : Nat) (hn : n < 64) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 64)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (n + 1) ∧ t.zf = some (decide (n + 1 = 64)) ∧
      Keeps [.rbx] s t := by
  have ha : BitVec.ofNat 64 n + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (n + 1) - (64 : BitVec 32).signExtend 64 == 0) =
      decide (n + 1 = 64) := by
    rw [show (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-! ## A step -/

/-- The loop's invariant, after `c` steps. -/
structure CombInv (s₀ : State) (base : Addr) (S c : Nat) (s : State) : Prop where
  bound : c ≤ 64
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 c
  d : env s.mem base 16 = Spec.Ed25519.d
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  value : Rep (point (env s.mem base) 0 1 2 3) (combVal S c • baseAff)
  keep : PowersKeep base 56 7368 s₀ s

theorem bits_far {base : Addr} {q : Nat} (hq : q < 256) :
    ofs base (off base (768 + q)) = 768 + q := Proof.X25519.X86_64.ofs_off' base (by omega)

theorem combAddG_ok {s : State} {base : Addr} (hs : Scratch s base) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (combAddG fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) combG ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [combAddG, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs _) fun a ⟨ka, va⟩ => ?_
  have hsa := hs.of_keep ka
  have ha16 : ∀ i : Slot, 16 ≤ i.val → env a.mem base i = env s.mem base i := fun i hi => by
    rw [va]; exact point_ops_high _ (by decide) _ i hi
  have hp : point (env a.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by rw [va]; rfl
  refine WP.mono (pointAddCached_spec (fld := fld) a base combG hsa (by rw [ha16 16 (by decide)]; exact hd)
    (by rw [va, ← combGCached_eq]; rfl)) fun t ⟨kt, tp, th⟩ =>
    ⟨ka.trans kt, by rw [tp, hp], fun i hi => (th i hi).trans (ha16 i hi)⟩

theorem zsmul_16 (v : ℤ) (g : Nat) (P : EPoint dZ) :
    (16 : Nat) • (v • P) + g • P = (16 * v + g) • P := by
  rw [add_smul, mul_smul, ← natCast_zsmul, ← natCast_zsmul]; rfl

theorem combStep_ok {s₀ s : State} {base : Addr} {S c : Nat} (h : CombInv s₀ base S c s)
    (hc : c < 64) :
    WP isa (combStep fld) s fun t => t.zf = some (decide (c + 1 = 64)) ∧
      CombInv s₀ base S (c + 1) t := by
  rw [combStep]
  refine WP.seq (WP.mono (rbxCmp_ok s c 32 hc (by decide) h.counter) fun a ⟨az, ag, am, ar, aw⟩ => ?_)
  have hsa : Scratch a base := ⟨by rw [ag]; exact h.scratch.rdi, aw ▸ h.scratch.wr, h.scratch.nowrap⟩
  have kas : PowersKeep base 56 7368 s a := ⟨fun r _ _ _ => by rw [ag], ar, aw, by rw [am]; exact TableFrame.refl _ _ _ _⟩
  -- The doublings and `[G]B`, before the even digits.
  have hite : WP isa (.ite .e (.seq (double4 fld) (.block (combAddG fld))) (.block [])) a fun b =>
      Scratch b base ∧ b.gpr .rbx = BitVec.ofNat 64 c ∧ env b.mem base 16 = Spec.Ed25519.d ∧
      (∀ q < 256, b.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) ∧
      Rep (point (env b.mem base) 0 1 2 3)
        ((if c = 32 then 16 * combVal S c + combGVal else combVal S c) • baseAff) ∧
      PowersKeep base 56 7368 a b := by
    refine WP.ite (decide (c = 32)) (by simp only [eval, az]) (fun hy => ?_) (fun hn => ?_)
    · have h32 : c = 32 := of_decide_eq_true hy
      refine WP.seq (WP.mono (double4_ok (fld := fld) (a := combVal S c • baseAff) hsa (by rw [am]; exact h.value))
        fun b ⟨br, bh, bk⟩ => ?_)
      have hsb := bk.scratch hsa
      have bd : env b.mem base 16 = Spec.Ed25519.d := by rw [bh 16 (by decide), am]; exact h.d
      refine WP.mono (combAddG_ok (fld := fld) hsb bd) fun e ⟨ke, ep, eh⟩ => ?_
      refine ⟨hsb.of_keep ke, (ke.gpr _ (by decide)).trans ((bk.gpr _ (by decide) (by decide)).trans
          (by rw [ag]; exact h.counter)),
        by rw [eh 16 (by decide)]; exact bd,
        fun q hq => by
          rw [ke.mem _ (by rw [bits_far hq]; omega), bk.mem _ (by rw [bits_far hq]; omega), am]
          exact h.bits q hq, ?_,
        (⟨fun r _ hs hc' => bk.gpr r hs hc', bk.rd, bk.wr, TableFrame.workspace bk.mem⟩ :
          PowersKeep base 56 7368 a b).trans (PowersKeep.of_keep ke)⟩
      simp only [h32, ↓reduceIte]
      rw [ep, ← zsmul_16]
      subst h32
      exact pointAdd_rep br combG_ok
    · have h32 : c ≠ 32 := of_decide_eq_false hn
      refine WP.block_nil ⟨hsa, by rw [ag]; exact h.counter, by rw [am]; exact h.d,
        fun q hq => by rw [am]; exact h.bits q hq, by simp only [h32, ↓reduceIte]; rw [am]; exact h.value,
        PowersKeep.refl _ _ _ _⟩
  refine WP.seq (WP.mono hite fun b ⟨hsb, bc, bd, bbits, bv, kb⟩ => ?_)
  -- The digit's bit index.
  refine WP.seq (WP.mono (combIndex_ok b hc bc) fun e ⟨ec, ke⟩ => ?_)
  have hse : Scratch e base := hsb.of_keeps ke (by decide)
  -- The digit, its sign and magnitude, its masks and the table.
  have hn : nib S (combIdx c) < 16 := Nat.mod_lt _ (by decide)
  have hmag : mag (nib S (combIdx c)) < 9 := by unfold mag; split <;> omega
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combDigit_ok (S := S) hse (combIdx_lt hc) ec (by rw [ke.2.1]; exact bbits))
    fun f ⟨fax, kf⟩ => ?_
  have hsf : Scratch f base := hse.of_keeps kf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (combSign_ok (n := nib S (combIdx c)) hsf hn fax) fun f' ⟨f'ax, f'm, f'g, f'r, f'w, f'mem⟩ => ?_
  have hsf' : Scratch f' base := ⟨(f'g _ (by decide) (by decide)).trans hsf.rdi, f'w ▸ hsf.wr, hsf.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (combMaskAll_ok (d := mag (nib S (combIdx c))) hsf' (by omega) f'ax)
    fun g ⟨gm, gg, gr, gw, gmem⟩ => ?_
  have hsg : Scratch g base := ⟨(gg _ (by decide)).trans hsf'.rdi, gw ▸ hsf'.wr, hsf'.nowrap⟩
  have gc : g.gpr .rbx = BitVec.ofNat 64 c := by
    rw [gg _ (by decide), f'g _ (by decide) (by decide), kf.1 _ (by decide), ke.1 _ (by decide)]; exact bc
  have gsm : g.mem.readW (off base combSignMask) 64 = signMask (nib S (combIdx c)) :=
    (gmem.word (d := combSignMask) (Or.inr (by simp only [combMasks, combSignMask]; omega))
      (by simp only [combSignMask]; omega)).trans f'm
  refine WP.mono (rdxMod_ok g c hc gc) fun i ⟨irdx, ki⟩ => ?_
  have hsi : Scratch i base := hsg.of_keeps ki (by decide)
  -- The entry.
  refine WP.seq (WP.mono (combSelectAll_ok (d := mag (nib S (combIdx c))) hsi hmag
    (by rw [ki.2.1]; exact gm) (Nat.mod_lt _ (by decide)) irdx) fun u ⟨uq, ku, _, ue⟩ => ?_)
  have hsu : Scratch u base := hsi.of_keep ku
  have usm : u.mem.readW (off base combSignMask) 64 = signMask (nib S (combIdx c)) :=
    (ku.mem.word (d := combSignMask) (Or.inr (by simp only [combSignMask]; omega))
      (by simp only [combSignMask]; omega)).trans (by rw [ki.2.1]; exact gsm)
  -- Negated for a negative digit.
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok (fld := fld) hsu usm) fun u' ⟨u'q, ku', ue'⟩ => ?_
  have hsu' : Scratch u' base := hsu.of_keep ku'
  have eu : ∀ x : Slot, (x.val < 4 ∨ 16 ≤ x.val) → env u'.mem base x = env b.mem base x := fun x hx => by
    rw [ue' x (by omega), ue x (by omega), ki.2.1, table_env gmem (by simp only [combMasks]; omega),
      table_env f'mem (by simp only [combSignMask]; omega), kf.2.1, ke.2.1]
  have ud : env u'.mem base 16 = Spec.Ed25519.d := (eu 16 (by decide)).trans bd
  have up : point (env u'.mem base) 0 1 2 3 = point (env b.mem base) 0 1 2 3 := by
    simp only [point, eu 0 (by decide), eu 1 (by decide), eu 2 (by decide), eu 3 (by decide)]
  obtain ⟨q₀, hq₀, hrq₀⟩ := combCached_ok (c % 32) (mag (nib S (combIdx c))) (Nat.mod_lt _ (by decide)) hmag
  let q := if nib S (combIdx c) < 8 then negPoint q₀ else q₀
  have hq : point (env u'.mem base) 4 5 6 7 = cache q := by
    rw [u'q, uq, hq₀]
    by_cases hlt : nib S (combIdx c) < 8
    · simp only [hlt, ↓reduceIte, q, negCached_cache]
    · simp only [hlt, ↓reduceIte, q]
  have hrq : Rep q ((sdig S (combIdx c) * 256 ^ (c % 32)) • baseAff) := by
    by_cases hlt : nib S (combIdx c) < 8
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 256 ^ (c % 32) = -(((mag (nib S (combIdx c)) * 256 ^ (c % 32) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : nib S (combIdx c) ≤ 8)]; ring
      rw [e, neg_smul, natCast_zsmul]
      exact hrq₀.neg
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 256 ^ (c % 32) = (((mag (nib S (combIdx c)) * 256 ^ (c % 32) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 8 ≤ nib S (combIdx c))]; ring
      rw [e, natCast_zsmul]
      exact hrq₀
  -- The addition and the counter.
  rw [WP.block_append_iff]
  refine WP.mono (pointAddCached_spec (fld := fld) u' base q hsu' ud hq) fun v ⟨kv, vp, vh⟩ => ?_
  have vc : v.gpr .rbx = BitVec.ofNat 64 c := by
    rw [kv.gpr _ (by decide), ku'.gpr _ (by decide), ku.gpr _ (by decide), ki.1 _ (by decide), gc]
  refine WP.mono (rbxNext64_ok v c hc vc) fun t ⟨tc, tz, kt⟩ => ⟨tz, ?_⟩
  have kbu : PowersKeep base 56 7368 b u' :=
    (((((PowersKeep.of_keeps ke (by decide)).trans (PowersKeep.of_keeps kf (by decide))).trans
      ⟨fun r _ _ hcl => f'g r (by rintro rfl; exact hcl (by decide)) (by rintro rfl; exact hcl (by decide)),
        f'r, f'w, TableFrame.table (f'mem.mono (by simp only [combSignMask]; omega)
          (by simp only [combSignMask]; omega))⟩).trans
      ⟨fun r _ _ hcl => gg r (by rintro rfl; exact hcl (by decide)), gr, gw,
        TableFrame.table (gmem.mono (by simp only [combMasks]; omega) (by simp only [combMasks]; omega))⟩).trans
      (PowersKeep.of_keeps ki (by decide))).trans ((PowersKeep.of_keep ku).trans (PowersKeep.of_keep ku'))
  refine ⟨by omega, hsu'.of_keep kv |>.of_keeps kt (by decide), tc, ?_, fun x hx => ?_, ?_,
    ((((h.keep.trans kas).trans kb).trans kbu).trans (PowersKeep.of_keep kv)).trans
      (PowersKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1, vh 16 (by decide), ud]
  · rw [kt.2.1, kv.mem _ (by rw [bits_far hx]; omega), ku'.mem _ (by rw [bits_far hx]; omega),
      ku.mem _ (by rw [bits_far hx]; omega), ki.2.1,
      gmem _ (by rw [bits_far hx]; simp only [combMasks]; omega),
      f'mem _ (by rw [bits_far hx]; simp only [combSignMask]; omega), kf.2.1, ke.2.1]
    exact bbits x hx
  · rw [kt.2.1, vp, up, ← combIdx_nib S c hc, add_smul, add_comm]
    exact pointAdd_rep bv hrq

/-! ## The loop -/

theorem combMultiply_ok {s : State} {base : Addr} (hs : Scratch s base) {S : Nat}
    (hS : S < 2 ^ (16 * 16)) (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (combMultiply fld) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
  rw [combMultiply]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs (constPointOps combG))
    fun a ⟨ka, va⟩ => ?_
  refine WP.mono (rbxSet_ok a 0 (by decide)) fun b ⟨bc, kb⟩ => ?_
  have init : CombInv s base S 0 b := by
    refine ⟨by decide, (hs.of_keep ka).of_keeps kb (by decide), bc, ?_, fun q hq => ?_, ?_,
      (PowersKeep.of_keep ka).trans (PowersKeep.of_keeps kb (by decide))⟩
    · rw [kb.2.1, va, point_ops_high _ (by decide) _ 16 (by decide), hd]
    · rw [kb.2.1, ka.mem _ (by rw [bits_far hq]; omega)]; exact hb q hq
    · rw [kb.2.1, va, constPoint_eval, show combVal S 0 = (combGVal : ℤ) by simp [combVal, oddSumZ],
        natCast_zsmul]
      exact combG_ok
  apply WP.loop (fun n t => CombInv s base S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok (fld := fld) ht (by omega)) fun u ⟨uz, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      refine Or.inl ⟨by simp only [eval, uz, show 64 - (0 + 1) + 1 = 64 from rfl, decide_true,
        Option.map_some, Bool.not_true], ?_, hu.keep⟩
      have hv := hu.value
      rw [show 64 - (0 + 1) + 1 = 64 from rfl, comb_sum hS, natCast_zsmul] at hv
      exact hv
    · refine Or.inr ⟨by simp only [eval, uz, show ¬ (64 - (k + 1) + 1 = 64) by omega, decide_false,
        Option.map_some, Bool.not_false], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨init, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch`. -/
section

/-! Scratch counters are public by correctness, including after table stores. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem both_wp {P F : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True))
    (hw : ∀ s, P s → WP isa c s F) :
    RelCT isa (fun x y => P x ∧ P y) c (fun x y => F x ∧ F y) :=
  (h.wp (fun x y hp => ⟨hw x hp.1, hw y hp.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

def BatchCTPre (base : Addr) (j : Nat) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1) ∧
    env s.mem base 16 = Spec.Ed25519.d

def BatchCTReady (base : Addr) (j : Nat) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
    env s.mem base 16 = Spec.Ed25519.d ∧ s.gpr .rbx = BitVec.ofNat 64 j

def BatchCTOffset (base : Addr) (j : Nat) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j

theorem begin_ct (base : Addr) (j : Nat) :
    RelCT isa (fun x y => BatchCTPre base j x ∧ BatchCTPre base j y)
      (.block batchBegin) (fun x y => BatchCTReady base j x ∧ BatchCTReady base j y) := by
  apply both_wp
  · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  · intro s ⟨hs, hc, hd⟩
    refine WP.mono (batchBegin_ok hs j hc) fun t ⟨tc, tv, tg, tr, tw, tm⟩ => ?_
    refine ⟨⟨(tg _ (by decide)).trans hs.rdi, ?_, hs.nowrap⟩, tv, ?_, tc⟩
    · rw [tw]; exact hs.wr
    · rw [header_env tm]; exact hd

private theorem prepare_ct (base : Addr) (j : Nat) (hj : j < 32) :
    RelCT isa (fun x y => BatchCTReady base j x ∧ BatchCTReady base j y)
      (prepareBatch fld) (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y) := by
  apply both_wp
  · apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  · intro s ⟨hs, hc, hd, hr⟩
    refine WP.mono (prepareBatch_ok hs j hj hr hd) fun t ⟨kt, _, _, _⟩ => ?_
    exact ⟨kt.scratch hs, ((tableFrame_outside kt.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans hc⟩

theorem offset_ct (base : Addr) (j : Nat) (hj : j < 32) :
    RelCT isa (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y)
      (.block batchBitOffset) (fun x y =>
        (x.gpr .rdi = base ∧ x.gpr .rsi = BitVec.ofNat 64 (16 * j)) ∧
        (y.gpr .rdi = base ∧ y.gpr .rsi = BitVec.ofNat 64 (16 * j))) := by
  apply both_wp
  · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  · intro s ⟨hs, hc⟩
    refine WP.mono (batchBitOffset_ok hs j hj hc) fun t ⟨tr, kt⟩ => ?_
    exact ⟨(kt.1 _ (by decide)).trans hs.rdi, tr⟩

theorem pointMulBatch_ct (base : Addr) (j : Nat) (hj : j < 32) :
    RelCT isa (fun x y => BatchCTPre base j x ∧ BatchCTPre base j y)
      (pointMulBatch fld) (fun _ _ => True) := by
  rw [pointMulBatch]
  refine VG.RelCT.seq (begin_ct base j) (VG.RelCT.seq (prepare_ct base j hj)
    (VG.RelCT.seq (offset_ct base j hj) (VG.RelCT.seq (R := fun (x y : State) => ∀ r ∈ ([.rdi] : List Reg), x.gpr r = y.gpr r) ?_ ?_)))
  · apply taintRegsFld (τ := Taint.ofRegs [.rdi, .rsi]) _ [.rdi] (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs h

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.PointMulCT`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.PointMulCTLoop`. -/
section
/-! Both executions descend through the same public checkpoint count. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem pointMulLoop_ct (s₁ s₂ : State) (base : Addr) (count scalar₁ scalar₂ : Nat)
    (p₁ p₂ : Spec.Ed25519.Point) (hn : count ≤ 32) (n : Nat) :
    RelCT isa (fun x y => PointMulInv s₁ base count scalar₁ p₁ n x ∧
      PointMulInv s₂ base count scalar₂ p₂ n y) (.loop (pointMulBatch fld) .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (fun n x y => PointMulInv s₁ base count scalar₁ p₁ n x ∧
    PointMulInv s₂ base count scalar₂ p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply VG.RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < count
    · have hct := (pointMulBatch_ct (fld := fld) base j (by omega)).mono
        (fun x y (h : PointMulInv s₁ base count scalar₁ p₁ (j + 1) x ∧
            PointMulInv s₂ base count scalar₂ p₂ (j + 1) y) =>
          ⟨⟨h.1.scratch, h.1.counter, h.1.d⟩, ⟨h.2.scratch, h.2.counter, h.2.d⟩⟩)
        (fun _ _ h => h)
      have hw := withRuns hct (fun x y h =>
        ⟨pointMulBatch_ok h.1.scratch j count scalar₁ p₁ hj hn h.1.counter h.1.d h.1.value h.1.bits h.1.table,
         pointMulBatch_ok h.2.scratch j count scalar₂ p₂ hj hn h.2.counter h.2.d h.2.value h.2.bits h.2.table⟩)
      refine hw.mono (fun _ _ h => h) ?_
      intro x y ⟨_, a, b, hi, hx, hy⟩
      have ex : eval .ne x = some (!(decide (j = 0))) := by
        simp only [eval, hx.2.1, Option.map_some]
      have ey : eval .ne y = some (!(decide (j = 0))) := by
        simp only [eval, hy.2.1, Option.map_some]
      refine ⟨ex.trans ey.symm, fun _ => trivial, ?_⟩
      intro he
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp only [ex, decide_true, Bool.not_true] at he
        cases he
      refine ⟨j, by omega, ?_, ?_⟩
      · exact ⟨by omega, by omega, hx.2.2.2.2.2.2.scratch hi.1.scratch, hx.1,
          hx.2.2.2.1, hx.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1,
          hi.1.keep.trans hx.2.2.2.2.2.2⟩
      · exact ⟨by omega, by omega, hy.2.2.2.2.2.2.scratch hi.2.scratch, hy.1,
          hy.2.2.2.1, hy.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
          hi.2.keep.trans hy.2.2.2.2.2.2⟩
    · apply VG.RelCT.of_false
      intro x y h
      have := h.1.bound
      omega

end VG.Proof.Ed25519.X86_64
end

/-! Complete secret scalar multiplication has a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

def MulCTPreN (count : Nat) (base : Addr) (scalar : Nat) (s : State) : Prop :=
  Scratch s base ∧ scalar < 2 ^ (16 * count) ∧ env s.mem base 16 = Spec.Ed25519.d ∧
    ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)

abbrev MulCTPre := MulCTPreN 16

theorem pointMultiply_ct_of_init (count : Nat) (base : Addr) (scalar₁ scalar₂ : Nat)
    (hn0 : 0 < count) (hn : count ≤ 32)
    (initCT : RelCT isa (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiplyInit fld count) (fun _ _ => True)) :
    RelCT isa (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiply fld count) (fun _ _ => True) := by
  have hi := withRuns initCT (fun x y h =>
    ⟨pointMultiplyInit_ok h.1.1 count scalar₁ hn0 hn h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     pointMultiplyInit_ok h.2.1 count scalar₂ hn0 hn h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [pointMultiply]
  refine VG.RelCT.seq hi ?_
  intro x y tx ty x' y' ⟨_, a, b, _, hx, hy⟩ ex ey
  exact pointMulLoop_ct a b base count scalar₁ scalar₂ _ _ hn count _ _ _ _ _ _ ⟨hx, hy⟩ ex ey

theorem pointMultiply16_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiply fld 16) (fun _ _ => True) := by
  have initCT : RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiplyInit fld 16) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  exact pointMultiply_ct_of_init 16 base scalar₁ scalar₂ (by decide) (by decide) initCT

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.ScalarBaseCTEngine`. -/
section
/-! Expand secret scalar bits, multiply, and encode with a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]

def BaseEnginePre (base k : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    ∀ q < 32, 8192 ≤ ofs base (off k q)

end VG.Proof.Ed25519.X86_64
end

/-! Public argument pointers survive the secret point arithmetic. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

private def BaseStart (base k out : Addr) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .rdi = out ∧ s.gpr .rsi = k ∧ s.gpr .rdx = base

private def BasePrepared (base k out : Addr) (s : State) : Prop :=
  BaseEnginePre base k s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out : Addr} {s : State} (hs : BaseStart base k out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out) := by
  obtain ⟨⟨hr, hw, hd, _, _, hn⟩, ho, hk, hb⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, _⟩ => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, _⟩ => ?_
  rw [ga, hb] at pb ob
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScratch hd hq (by decide)

private theorem start_ct (base k out : Addr) :
    RelCT isa (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y) := by
  have hc : RelCT isa (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi, .rdx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {engine : Prog isa} (engine_ok : BaseEngineCorrect engine) {base k out : Addr} {s : State} (hs : BasePrepared base k out s) :
    WP isa engine s (BaseReady base out) := by
  refine WP.mono (engine_ok hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct {engine : Prog isa} (engine_ok : BaseEngineCorrect engine)
    (engine_ct : ∀ base k, RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      engine (fun _ _ => True)) (base k out : Addr) :
    RelCT isa (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k).mono
    (fun _ _ (h : BasePrepared base k out _ ∧ BasePrepared base k out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready engine_ok h.1, engine_ready engine_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .rdx = base ∧ t.gpr .rdi = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine VG.RelCT.seq hc' ?_
  apply taintFld (Taint.ofRegs [.rdx, .rdi]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct_of_engine (engine : Prog isa) (engine_ok : BaseEngineCorrect engine)
    (engineCT : ∀ base k, RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      engine (fun _ _ => True)) :
    ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub (scalarBaseWith engine) := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  intro x y tx ty x' y' ⟨hx, hy, _, ho, hk, hb⟩ ex ey
  have hc := VG.RelCT.seq (start_ct (x.gpr .rdx) (x.gpr .rsi) (x.gpr .rdi))
    (VG.RelCT.seq (engine_ct engine_ok engineCT (x.gpr .rdx) (x.gpr .rsi) (x.gpr .rdi))
      (finish_ct (x.gpr .rdx) (x.gpr .rdi)))
  exact hc _ _ _ _ _ _ ⟨⟨hx, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm⟩⟩ ex ey

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.ScalarBasePrecomputedEngine`. -/
section
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs val4)

variable {fld : Arith} [EdArith fld]

/-- The encoding's value depends only on the point represented. -/
theorem encodedValue_rep {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    encodedValue p = (a.y : Spec.X25519.Fe).val + ((a.x : Spec.X25519.Fe).val % 2) * 2 ^ 255 := by
  have hx : p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.x : Spec.X25519.Fe) := by
    show toZ (p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.x
    rw [toZ_mul, toZ_pow, h.x, mul_pow_inv h.z]
  have hy : p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2) = (a.y : Spec.X25519.Fe) := by
    show toZ (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)) = a.y
    rw [toZ_mul, toZ_pow, h.y, mul_pow_inv h.z]
  simp only [encodedValue, hx, hy]
  rfl

theorem scalarBasePrecomputedEngine_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBasePrecomputedEngine fld) s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBasePrecomputedEngine]
  refine WP.seq (WP.mono (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, _, bd, bbits, hscalar⟩ => ?_)
  refine WP.seq (WP.mono (combMultiply_ok (fld := fld) (kab.scratch hs) hscalar bd bbits)
    fun c ⟨cp, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scratch (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc).trans (PowersKeep.of_rbx kt), ?_⟩
  change val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv, VG.Proof.Ed25519.X86_64.encodedValue_rep cp, VG.Proof.Ed25519.X86_64.encodedValue_rep (pointMul_rep _ basePoint_rep)]

end VG.Proof.Ed25519.X86_64
end

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem scalarBasePrecomputedEngine_ct (base k : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      (scalarBasePrecomputedEngine fld) (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      (scalarBasePrepare fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hp := withRuns hc (fun x y h =>
    ⟨scalarBasePrepare_ok h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     scalarBasePrepare_ok h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [scalarBasePrecomputedEngine]
  refine VG.RelCT.seq hp ?_
  intro x y tx ty x' y' ⟨_, a, b, hab, hx, hy⟩ ex ey
  have hct : RelCT isa (fun u v =>
      (Scratch u base ∧ env u.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, u.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k 32) < 2 ^ (16 * 16)) ∧
      (Scratch v base ∧ env v.mem base 16 = Spec.Ed25519.d ∧
        (∀ q < 256, v.mem (off base (768 + q)) =
          BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) / 2 ^ q) % 2)) ∧
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k 32) < 2 ^ (16 * 16)))
      (combMultiply fld) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi) (by fld_taint_decide)
  have hm' := withRuns hct (fun u v h =>
    ⟨combMultiply_ok (fld := fld) h.1.1 h.1.2.2.2 h.1.2.1 h.1.2.2.1,
     combMultiply_ok (fld := fld) h.2.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1⟩)
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base)
      (pointEncode fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro u v h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.trans h.2.symm)
  have hm'' := hm'.mono (fun _ _ h => h) (fun u v ⟨_, c, d, hcd, hu, hv⟩ =>
      And.intro (hu.2.scratch hcd.1.1).rdi (hv.2.scratch hcd.2.1).rdi)
  exact (VG.RelCT.seq hm'' he) _ _ _ _ _ _
    ⟨⟨hx.1.scratch hab.1.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩,
     ⟨hy.1.scratch hab.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2⟩⟩ ex ey

theorem scalarBase_precomputed_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub
    (scalarBase_precomputed fld) :=
  scalarBase_ct_of_engine (scalarBasePrecomputedEngine fld) VG.Proof.Ed25519.X86_64.scalarBasePrecomputedEngine_ok
    VG.Proof.Ed25519.X86_64.scalarBasePrecomputedEngine_ct

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.ScalarBaseVerified`. -/
section
/-! A state satisfying the precondition of `vg_ed25519_scalar_base`'s contract,
the witness that it is satisfiable (`ScalarBasePrecomputedVerified.lean`). -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def baseSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

end VG.Proof.Ed25519.X86_64
end

/-! The precomputed variant satisfies the same reviewed ABI contract. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem scalarBase_precomputed_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa (scalarBase_precomputed fld) s t s' ∧
      abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine (scalarBasePrecomputedEngine fld)
    VG.Proof.Ed25519.X86_64.scalarBasePrecomputedEngine_ok hs
  exact ⟨t, s', he, abiPreserved_of_exec (by fld_lit_decide) he h.1, h.2⟩

theorem scalarBase_precomputed_verified : Verified X86_64.target (scalarBase_precomputed fld)
    (Spec.Ed25519.scalarBaseContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Ed25519.X86_64.scalarBase_precomputed_ok VG.Proof.Ed25519.X86_64.scalarBase_precomputed_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, scalarBaseLocal]
      [baseSatState] using VG.Proof.Ed25519.X86_64.baseSatState)

end VG.Proof.Ed25519.X86_64

end

end
