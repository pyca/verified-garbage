module

public import VerifiedGarbage.Proof.Rc4.AArch64.KsaGroup
import VerifiedGarbage.Proof.Rc4.AArch64.Consts
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Rc4.AArch64.ApplyFinish
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Rc4.AArch64.Taint
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Rc4.AArch64.Lit
public import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Rc4.AArch64.Init`, which only this module used -/

section

/-! ### `Rc4.AArch64.KsaSetup`, which only this module used -/

section

/-!
# The key schedule's setup

`ksaSetup_ok`: the setup saves the callee-saved vector registers it uses,
leaves the constants, the identity table in `v16`–`v31` (lane numbers, and
their XORs with 64, 128 and 192), `j = 0`, `S[0] = 0`, the key pointer and
length, sixteen groups to go and the base `0`: the first group's `KsaInv`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ident_xor : ∀ q < 4, laneNums q ^^^ bc 64#8 = laneNums (q + 4) ∧
    laneNums q ^^^ bc 128#8 = laneNums (q + 8) ∧ laneNums (q + 4) ^^^ bc 128#8 = laneNums (q + 12) := by
  decide +kernel

/-- The identity table's code, written out. -/
def identCode : List Instr :=
  [.vop (.mov .v16 .v8), .vop (.mov .v17 .v9), .vop (.mov .v18 .v10), .vop (.mov .v19 .v11),
   eorV .v20 .v8 .v12, eorV .v21 .v9 .v12, eorV .v22 .v10 .v12, eorV .v23 .v11 .v12,
   eorV .v24 .v8 .v13, eorV .v25 .v9 .v13, eorV .v26 .v10 .v13, eorV .v27 .v11 .v13,
   eorV .v28 .v20 .v13, eorV .v29 .v21 .v13, eorV .v30 .v22 .v13, eorV .v31 .v23 .v13]

theorem identCode_eq :
    (List.range 4).map (fun r => .vop (.mov (treg r) (lanes r))) ++
    (List.range 4).map (fun r => eorV (treg (4 + r)) (lanes r) c64) ++
    (List.range 4).map (fun r => eorV (treg (8 + r)) (lanes r) c128) ++
    (List.range 4).map (fun r => eorV (treg (12 + r)) (treg (4 + r)) c128) = identCode := by
  decide

theorem ident_ok {s : State} (hk : Consts s) :
    WP isa (.block identCode) s fun t =>
      (∀ q < 16, t.v (treg q) = laneNums q) ∧ (∀ v, NotTable v → t.v v = s.v v) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain l0 : s.v .v8 = laneNums 0 := hk.lns 0 (by decide)
  obtain l1 : s.v .v9 = laneNums 1 := hk.lns 1 (by decide)
  obtain l2 : s.v .v10 = laneNums 2 := hk.lns 2 (by decide)
  obtain l3 : s.v .v11 = laneNums 3 := hk.lns 3 (by decide)
  have k64 : s.v .v12 = bc 64 := hk.c64
  have k128 : s.v .v13 = bc 128 := hk.c128
  obtain x0 := ident_xor 0 (by decide)
  obtain x1 := ident_xor 1 (by decide)
  obtain x2 := ident_xor 2 (by decide)
  obtain x3 := ident_xor 3 (by decide)
  simp only [Nat.reduceAdd] at x0 x1 x2 x3
  unfold identCode eorV
  rrun [l0, l1, l2, l3, k64, k128, x0.1, x0.2.1, x0.2.2, x1.1, x1.2.1, x1.2.2, x2.1, x2.2.1,
    x2.2.2, x3.1, x3.2.1, x3.2.2]
  refine ⟨fun q hq => ?_, fun v hv => ?_, ?_⟩
  · rcases (by omega_using [hq] : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨
      q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [treg]
  · have ne (a : Nat) (ha : a < 16) : v ≠ treg a := (hv a ha).symm
    obtain n0 : v ≠ .v16 := ne 0 (by decide)
    obtain n1 : v ≠ .v17 := ne 1 (by decide)
    obtain n2 : v ≠ .v18 := ne 2 (by decide)
    obtain n3 : v ≠ .v19 := ne 3 (by decide)
    obtain n4 : v ≠ .v20 := ne 4 (by decide)
    obtain n5 : v ≠ .v21 := ne 5 (by decide)
    obtain n6 : v ≠ .v22 := ne 6 (by decide)
    obtain n7 : v ≠ .v23 := ne 7 (by decide)
    obtain n8 : v ≠ .v24 := ne 8 (by decide)
    obtain n9 : v ≠ .v25 := ne 9 (by decide)
    obtain n10 : v ≠ .v26 := ne 10 (by decide)
    obtain n11 : v ≠ .v27 := ne 11 (by decide)
    obtain n12 : v ≠ .v28 := ne 12 (by decide)
    obtain n13 : v ≠ .v29 := ne 13 (by decide)
    obtain n14 : v ≠ .v30 := ne 14 (by decide)
    obtain n15 : v ≠ .v31 := ne 15 (by decide)
    simp [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15]
  · simp [State.setV]

theorem saveK_ok (s : State) :
    WP isa (.block (save false)) s fun t =>
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ≠ .x10 → g ≠ .x11 → g ≠ .x14 → g ≠ .x15 → g ≠ .x16 → g ≠ .x17 → t.gpr g = s.gpr g) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold save saved
  rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil]
  refine ⟨fun p hp => ?_, fun g a b c d e f => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [a, b, c, d, e, f]
  · simp [State.write]

/-- The registers the key schedule's setup writes. -/
def ksaRegs : List Reg := [.x4, .x5, .x6, .x7, .x8, .x10, .x11, .x14, .x15, .x16, .x17]

/-- The key schedule's globals for the call from `s`, entering the loop in `t`. -/
def kglob (s t : State) : KGlob := ⟨s.gpr .x0, (s.gpr .x1).toNat, s.mem, t⟩

/-- An entry of `Vector.ofFn f`, for any length: with the length a numeral,
the kernel builds the vector to compare the forms of the goal. -/
theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) {k : Nat} (hk : k < n) (d : α) :
    (Vector.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Vector.getD, hk]

theorem ident_get {k : Nat} (hk : k < 256) :
    (Vector.ofFn fun i : Fin 256 => BitVec.ofNat 8 i.val).getD (BitVec.ofNat 8 (0 + k)).toNat 0 =
      BitVec.ofNat 8 k := by
  rw [Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, getD_ofFn _ hk]

theorem scheduleSetup_eq : scheduleSetup = save false ++ (constants ++ (identCode ++
    ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0, .addImm .x .x5 .x1 0,
      .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr))) := by
  rw [← identCode_eq]; simp only [scheduleSetup, List.append_assoc]

theorem tailK_ok (c : State) :
    WP isa (.block ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0,
      .addImm .x .x5 .x1 0, .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr)) c fun t =>
      t.v (dq 0) = 0 ∧ t.v si = 0 ∧ (∀ v, v ≠ .v0 → v ≠ .v4 → t.v v = c.v v) ∧
      t.gpr .x7 = c.gpr .x0 ∧ t.gpr .x5 = c.gpr .x1 ∧ t.gpr .x4 = 16#64 ∧ t.gpr .x8 = 0#64 ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → t.gpr r = c.gpr r) ∧
      t.mem = c.mem ∧ t.rd = c.rd ∧ t.wr = c.wr ∧ t.sp = c.sp := by
  have d0 : dq 0 = .v0 := rfl
  have s4 : si = .v4 := rfl
  rrun [d0, s4]
  refine ⟨fun v a b => by simp [a, b], fun r a b c d => by simp [a, b, c, d], ?_⟩
  simp [State.write, State.setV]

theorem ksaSetup_ok {s : State} (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa (.block scheduleSetup) s fun t =>
      (kglob s t).Ok ∧ KsaInv (kglob s t) 0 0 t ∧
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ r, r ∉ ksaRegs → t.gpr r = s.gpr r) ∧ t.v .v14 = s.v .v14 ∧ t.v .v15 = s.v .v15 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [scheduleSetup_eq, WP.block_append_iff]
  refine WP.mono (saveK_ok s) fun a ⟨asv, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok a) fun b ⟨bc', bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ident_ok bc') fun c ⟨ct, cv, cg, cm, crd, cwr, csp⟩ => ?_
  refine WP.mono (tailK_ok c) fun t ⟨tj, tsi, tv, t7, t5, t4, t8, tg, tm, trd, twr, tsp⟩ => ?_
  have hL1 := hL.1
  obtain gk : ∀ r, r ∉ ksaRegs → t.gpr r = s.gpr r := fun r hr => by
    obtain n : ∀ g ∈ ksaRegs, r ≠ g := fun g hg e => hr (e ▸ hg)
    rw [tg r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)), cg,
      bg r (n _ (by decide)) (n _ (by decide)),
      ag r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide))
        (n _ (by decide))]
  obtain t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide)
  obtain t1 : t.gpr .x1 = s.gpr .x1 := gk _ (by decide)
  obtain tvt : ∀ q < 16, t.v (treg q) = laneNums q := fun q hq => by
    rw [tv _ ((show NotTable .v0 by decide) q hq) ((show NotTable .v4 by decide) q hq), ct q hq]
  obtain tcon : Consts t := bc'.congr fun r hr => by
    rw [tv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      cv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  obtain tb : ∀ k < 256, tbyte t.v k = BitVec.ofNat 8 k := fun k hk => by
    rw [tbyte, tvt _ (by omega_using [hk]), laneNums, vbyte_ofVBytes _ (by omega_using [])]
    congr 1; omega_using []
  obtain keep : ∀ v, v ≠ .v0 → v ≠ .v4 → NotTable v → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 →
      v ≠ .v11 → v ≠ .v12 → v ≠ .v13 → t.v v = s.v v := fun v h0 h4 ht h7 h8 h9 h10 h11 h12 h13 => by
    rw [tv v h0 h4, cv v ht, bv v h7 h8 h9 h10 h11 h12 h13, av]
  obtain hok : (kglob s t).Ok := by
    refine ⟨hL.1, hL.2, t0, ?_, ?_⟩
    · show t.gpr .x1 = _
      rw [t1]; simp [kglob]
    · show InRegions (t.rd ++ t.wr) _ _
      rw [trd, twr, crd, cwr, brd, bwr, ard, awr]; exact hk
  refine ⟨hok, ?_, fun p hp => ?_, gk, keep _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), by rw [tm, cm, bm, am], by rw [trd, crd, brd, ard],
    by rw [twr, cwr, bwr, awr], by rw [tsp, csp, bsp, asp]⟩
  · exact {
      consts := tcon
      table := fun k hk => by rw [tb k hk]; exact (ident_get hk).symm
      j := by rw [tj, Nat.add_zero, schedule_zero]; decide
      si := by rw [tsi, tb 0 (by decide)]; rfl
      x7 := by rw [t7, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; simp [kglob]
      x5 := by
        rw [t5, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        simp [kglob]
      x8 := by rw [t8]
      x4 := by rw [t4]
      gpr := fun _ _ _ _ _ _ => rfl
      vkept := fun _ _ => rfl
      mem := by rw [tm, cm, bm, am]; rfl
      rd := rfl
      wr := rfl
      sp := rfl }
  · have ⟨h6, h7⟩ : p.2 ≠ .x6 ∧ p.2 ≠ .x7 := by revert p; decide
    have ⟨h4, h5, h8⟩ : p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x8 := by revert p; decide
    rw [tg _ h4 h5 h7 h8, cg, bg _ h6 h7, asv p hp]

end VG.Proof.Rc4.AArch64

end

end


/-!
# The key schedule

`init_ok`: `vg_rc4_init` checks the key length, and for a valid one leaves
the key schedule with both indices zero at `ctx`, preserving the low halves
of `v8`–`v15`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ctxRegs_ok (a : State) :
    WP isa (.block [.addImm .x .x0 .x2 0, .movz .x .x9 255 0]) a fun b =>
      b.gpr .x0 = a.gpr .x2 ∧ b.gpr .x9 = 255#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x9 → b.gpr r = a.gpr r) ∧
      b.v = a.v ∧ b.mem = a.mem ∧ b.rd = a.rd ∧ b.wr = a.wr ∧ b.sp = a.sp := by
  rrun
  refine ⟨fun r h0 h9 => by simp [h0, h9], ?_⟩
  simp [State.write]

theorem zeros_ok {b : State} (hp : InRegions b.wr (b.gpr .x0) 258) :
    WP isa (.block [.movz .w .x6 0 0, .strb .x6 .x0 256, .strb .x6 .x0 257, .movz .w .x0 0 0]) b
      fun c => c.mem = (b.mem.write (b.gpr .x0 + 256#64) 1 0).write (b.gpr .x0 + 257#64) 1 0 ∧
        c.gpr .x0 = 0#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x6 → c.gpr r = b.gpr r) ∧ c.v = b.v ∧
        c.rd = b.rd ∧ c.wr = b.wr ∧ c.sp = b.sp := by
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  obtain hz : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 0#16))) =
    0#8 := by decide
  rrun [State.store, h256, h257]
  refine ⟨by rw [hz], fun r a b => by simp [a, b], by simp [State.write]⟩

theorem ksaFinish_ok {g : KGlob} {u : State} (h : KsaInv g 256 0 u)
    (hp : InRegions u.wr (u.gpr .x2) 258) :
    WP isa (.block scheduleFinish) u fun t =>
      t.gpr .x0 = 0#64 ∧
      contextAt t.mem (u.gpr .x2) = { table := (schedulePrefix g.key 256).1, i := 0, j := 0 } ∧
      (∀ p ∈ saved false, (t.v p.1).extractLsb' 0 64 = u.gpr p.2) ∧
      (∀ v, (∀ p ∈ saved false, p.1 ≠ v) → t.v v = u.v v) ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp := by
  unfold scheduleFinish
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ctxRegs_ok u) fun a ⟨a0, a9, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff, storeTable_eq]
  obtain a8 : a.gpr .x8 = BitVec.ofNat 64 256 := by rw [ag _ (by decide) (by decide)]; exact h.x8
  obtain hpa : InRegions a.wr (a.gpr .x0) 258 := by rw [awr, a0]; exact hp
  obtain hpa' : InRegions a.wr (a.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hpa
  refine WP.mono (storeN_ok (by decide) a8 a9 hpa' (Nat.le_refl 16))
    fun b ⟨brow, _, bv, bg, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  obtain b0 : b.gpr .x0 = a.gpr .x0 := bg _ (by decide) (by decide)
  refine WP.mono (zeros_ok (by rw [bwr, b0]; exact hpa)) fun c ⟨cm, c0, cg, cv, crd, cwr, csp⟩ => ?_
  refine WP.mono (restore_ok false c) fun t ⟨tsv, tv, tg, tm, trd, twr, tsp⟩ => ?_
  obtain hT : TableIn a 256 (schedulePrefix g.key 256).1 := fun k hk => by
    rw [show tbyte a.v = tbyte u.v by rw [av]]; exact h.table k hk
  refine ⟨?_, ?_, fun p hp => ?_, fun v hv => ?_, ?_, ?_, ?_⟩
  · rw [tg, c0]
  · rw [tm, cm, b0, a0, context_finish, ← a0, stored_table (by decide) hT brow]
  · have ⟨n0, n6, n7, n9⟩ : p.2 ≠ .x0 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧ p.2 ≠ .x9 := by revert p; decide
    rw [tsv p hp, cg _ n0 n6, bg _ n6 n7, ag _ n0 n9]
  · rw [tv v hv, cv, bv, av]
  · rw [trd, crd, brd, ard]
  · rw [twr, cwr, bwr, awr]
  · rw [tsp, csp, bsp, asp]

theorem savedK_v : ∀ r ∈ preservedV, r = .v14 ∨ r = .v15 ∨ ∃ p ∈ saved false, p.1 = r := by decide

theorem savedK_kept : ∀ p ∈ saved false, p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧
    p.2 ≠ .x8 := by decide

theorem initValid_ok (s : State) (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa initValid s fun t => t.gpr .x0 = 0#64 ∧
      contextAt t.mem (s.gpr .x2) =
        { table := keySchedule (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat), i := 0, j := 0 } ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  unfold initValid
  refine WP.seq (WP.mono (ksaSetup_ok hL hk)
    fun t ⟨hok, hi, tsv, tg, t14, t15, _, _, twr, _⟩ => ?_)
  refine WP.seq (WP.mono (ksaLoop_ok hok 16 ⟨0, rfl, rfl, by decide, hi⟩) fun u hu => ?_)
  obtain u2 : u.gpr .x2 = s.gpr .x2 := by
    rw [hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact tg _ (by decide)
  obtain hpu : InRegions u.wr (u.gpr .x2) 258 := by
    rw [hu.wr, u2]; show InRegions t.wr _ _; rw [twr]; exact hp
  refine WP.mono (ksaFinish_ok hu hpu) fun w ⟨w0, wc, wsv, wv, _, _, _⟩ => ?_
  refine ⟨w0, ?_, fun r hr => ?_⟩
  · rw [← u2, wc, keySchedule_eq]; rfl
  · have hn : ∀ p ∈ saved false, p.1 ≠ .v14 ∧ p.1 ≠ .v15 := by decide
    rcases savedK_v r hr with rfl | rfl | ⟨p, hp, rfl⟩
    · rw [wv _ fun p hp => (hn p hp).1, hu.vkept _ (by decide)]; exact congrArg _ t14
    · rw [wv _ fun p hp => (hn p hp).2, hu.vkept _ (by decide)]; exact congrArg _ t15
    · obtain ⟨a4, a5, a6, a7, a8⟩ := savedK_kept p hp
      rw [wsv p hp, hu.gpr _ a4 a5 a6 a7 a8]
      exact tsv p hp

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = 0#64 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa VG.Impl.Rc4.AArch64.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
      | .ok ctx => t.gpr .x0 = 0#64 ∧ contextAt t.mem (s.gpr .x2) = ctx
      | .error .invalidKeyLength => t.gpr .x0 = 1#64) ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain hcheck : WP isa (.block [.subImm .x .x4 .x1 1, .lsr .x .x4 .x4 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x4 = (s.gpr .x1 - 1#64) >>> 8 := by rrun
  unfold VG.Impl.Rc4.AArch64.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, htv, ht0, ht1, ht2, ht4⟩ := ht
  let good := 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256
  obtain hcond : isa.eval (.nonzero .x .x4) t = some (decide (¬ good)) := by
    simp only [eval, State.read, BitVec.setWidth_eq, ht4, BitVec.ofNat_eq_ofNat, bne]
    apply congrArg some
    by_cases hg : good
    · have hz := (valid_length (s.gpr .x1)).mpr hg
      rw [hz, beq_self_eq_true]
      simp only [hg, not_true_eq_false, decide_false, Bool.not_true]
    · have hn : (s.gpr .x1 - 1#64) >>> 8 ≠ 0#64 := fun hz => hg ((valid_length _).mp hz)
      rw [beq_eq_false_iff_ne.mpr hn]
      simp only [hg, not_false_eq_true, decide_true, Bool.not_false]
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun
    exact fun r _ => by rw [htv]
  · have hg : good := by
      obtain hnn := of_decide_eq_false hy
      exact Classical.not_not.mp hnn
    change 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    obtain hpt : InRegions t.wr (t.gpr .x2) 258 := by rw [htw, ht2]; exact hp
    obtain hkt : InRegions (t.rd ++ t.wr) (t.gpr .x0) (t.gpr .x1).toNat := by
      rw [htr, htw, ht0, ht1]; exact hk
    obtain hlt : 0 < (t.gpr .x1).toNat ∧ (t.gpr .x1).toNat ≤ 256 := by rw [ht1]; omega_using [hg]
    refine WP.mono (initValid_ok t hlt hpt hkt) fun u ⟨u0, uc, uv⟩ => ?_
    refine ⟨⟨u0, ?_⟩, fun r hr => by rw [uv r hr, htv]⟩
    rw [← ht2, uc, htm, ht0, ht1]

end VG.Proof.Rc4.AArch64

end

end


@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem init_verified : Verified AArch64.target VG.Impl.Rc4.AArch64.init
    (Spec.Rc4.initContract AArch64.abi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    sig_pre [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs] at hs
    obtain ⟨hrd, hwr, _⟩ := hs
    obtain hp : InRegions s.wr (s.gpr .x2) 258 := by
      refine ⟨⟨s.gpr .x2, 258⟩, ?_, ?_⟩
      · rw [hwr]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    obtain hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat := by
      refine ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ?_, ?_⟩
      · rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _)
      · simp [Region.Contains]
    obtain hw := WP.gprs (rs := preserved) (init_ok s hp hk) (by lit_decide) (by rfl)
    obtain ⟨tr, t, he, ⟨hpost, hv⟩, hregs⟩ := hw
    refine ⟨tr, t, he, ⟨hregs, Exec.sp he, hv⟩, ?_⟩
    sig_post [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs]
    cases hc : Spec.Rc4.init (Spec.Rc4.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
    | ok ctx =>
      rw [hc] at hpost
      dsimp only at hpost ⊢
      exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
    | error err =>
      cases err
      rw [hc] at hpost
      dsimp only at hpost ⊢
      rw [hpost]
      rfl
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hpub he₁ he₂
    sig_pub [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs] at hpub
    obtain ⟨hsp, h0, h1, h2⟩ := hpub
    obtain hagree : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption
    exact init_ct s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hagree he₁ he₂
  · sig_implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs]
      [initSat] using initSat

end VG.Proof.Rc4.AArch64
