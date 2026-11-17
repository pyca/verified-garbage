module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillDep
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillPtr
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
import VerifiedGarbage.Proof.Argon2.RISCV64.Copy
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCall
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillInput
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body

/-! ### `Argon2.RISCV64.Derive.FillWrite`, which this module and modules that import it used -/

section

/-!
# Argon2 on RISC-V: writing the new block

`writeWords_ok`: the doublewords of a block (at `a1`: G's output, or a
lane's last block) to the current block (at `a3`), XORed into the old ones
after the first pass.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)

open VG.Impl.Argon2.RISCV64.Derive (writeWord)

/-- Doublewords of the memory matrix. -/
abbrev md (s₀ : State) (m : Mem) (o : Nat) : BitVec 64 := m.readW (memP s₀ + BitVec.ofNat 64 o) 64

theorem cell_get {s₀ : State} (m : Mem) (C : Nat) {j : Nat} (hj : j < 128) :
    (blockAt m (matrixCell (memP s₀) C))[j] = md s₀ m (C * 1024 + 8 * j) := by
  rw [blockAt_get _ _ hj, matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A doubleword of the matrix after a store to another, or the same. -/
theorem md_store (m : Mem) {a b : Nat} (ha : a + 8 ≤ blocksN s₀ * 1024) (hb : b + 8 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 8 ≤ b ∨ b + 8 ≤ a) (v : BitVec 64) :
    md s₀ (m.writeW (memP s₀ + BitVec.ofNat 64 a) v) b = if a = b then v else md s₀ m b := by
  have := hp.mem_fits
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self64 _ _ _
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [h, e]) (by omega_using [hb, this]) (by omega_using [ha, this])) (by decide)

/-- The doublewords of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : Addr} (h4 : s.gpr .a1 = P) (hPa : P.toNat % 8 = 0)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, P = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P, 1024⟩ ⟨matrixCell (memP s₀) cur, 1024⟩)
    (h6 : s.gpr .a3 = memP s₀ + BitVec.ofNat 64 (cur * 1024)) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .a0 → r ≠ .a2 → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 128, md s₀ t.mem (cur * 1024 + 8 * i) = if i < n then
        (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * i)
          else s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64)
        else md s₀ s.mem (cur * 1024 + 8 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega_using [])]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    obtain hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [hc]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo h4 hPa hPw hPC h6 n (by omega_using [hn])).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memP s₀) cur = memP s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    obtain b1 : cur * 1024 + 8 * n + 8 ≤ blocksN s₀ * 1024 := by omega_using [hc, hn]
    -- The source doubleword is kept: only the current block has been written.
    obtain sw_t : t.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 = s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 := by
      refine ft.readW (r := ⟨P + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    obtain ea : t.gpr .a1 + BitVec.ofNat 64 (8 * n) = P + BitVec.ofNat 64 (8 * n) := by
      rw [gt _ (by decide) (by decide), h4]
    obtain eb : t.gpr .a3 + BitVec.ofNat 64 (8 * n) = memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n) := by
      rw [gt _ (by decide) (by decide), h6, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    obtain inS : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 (8 * n)) 8 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      obtain RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 64 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 64; decide⟩
        · exact ⟨mem_mem hp, Nat.le_trans (Nat.le_add_left _ _) hm⟩
      rw [bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [hn, lR]) (by have := RW.2; omega_using [hn, lR, this])⟩
    obtain inMc : (memR s₀).Contains (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 :=
      Offset.contains_base _ b1 (by omega_using [hc, hn, hm])
    obtain inC : (⟨matrixCell (memP s₀) cur, 1024⟩ : Region).Contains
        (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 := by
      obtain bl := blocks_lt' hp
      rw [cell]
      exact Offset.contains (e := cur * 1024) (k := 1024) (d := cur * 1024 + 8 * n) (n := 8) _
        (Nat.le_add_right _ _) (by omega_using [hn]) (by omega_using [hc, bl])
    obtain inM : ∀ u : State, Inv s₀ u → InRegions u.wr (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 :=
      fun u iu => ⟨memR s₀, by rw [iu.wr]; exact mem_mem hp, inMc⟩
    obtain o8 : 8 * n < 2048 := by omega_using [hn]
    obtain aP : (P + BitVec.ofNat 64 (8 * n)).toNat % 8 = 0 := Spill.al8 hPa (by omega_using [])
    obtain aC : (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)).toNat % 8 = 0 :=
      Spill.al8 hp.mem_al (by omega_using [])
    -- The doubleword.
    obtain fin : ∀ (v : BitVec 64) (u : State), u.mem = t.mem.writeW (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) v →
        u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r, r ≠ .a0 → r ≠ .a2 → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * n)
          else s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64) →
        Inv s₀ u ∧ (∀ r, r ≠ .a0 → r ≠ .a2 → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 128, md s₀ u.mem (cur * 1024 + 8 * i) = if i < n + 1 then
          (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * i)
            else s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64)
          else md s₀ s.mem (cur * 1024 + 8 * i) := fun v u hmu hrd hwr hsp gu ev => by
      obtain fu : Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hmu]; exact ft.writeW (List.mem_singleton_self _) v inC
      obtain iu : Inv s₀ u := it.step hsp (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (fun r hr => by
          rw [gu r (by revert hr; revert r; decide) (by revert hr; revert r; decide),
            gt r (by revert hr; revert r; decide) (by revert hr; revert r; decide)])
        hrd hwr (by rw [hmu]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hmu, md_store hp _ b1 (by omega_using [hc, hi]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 8 * n = cur * 1024 + 8 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [e, c])]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ld o8 ea aP inS fun u₁ v₁ => ?_
      refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₁.other .a3 (by decide)]; exact eb) aC (by rw [v₁.wr]; exact inM _ it)
        fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem, v₁.gpr]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (by rw [mu.sp, v₁.sp]) (fun r a b => by rw [mu.gpr, v₁.other r a, gt r a b]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [← sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ld o8 ea aP inS fun u₁ v₁ => ?_
      refine wp_ld (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₁.other .a3 (by decide)]; exact eb) aC
        (by rw [v₁.rd, v₁.wr]; exact ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩)
        fun u₂ v₂ => wp_xor fun u₃ v₃ => ?_
      refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₃.other .a3 (by decide), v₂.other .a3 (by decide), v₁.other .a3 (by decide)]; exact eb) aC
        (by rw [v₃.wr, v₂.wr, v₁.wr]; exact inM _ it) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₃.mem, v₂.mem, v₁.mem, v₃.gpr]) (by rw [mu.rd, v₃.rd, v₂.rd, v₁.rd])
        (by rw [mu.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [mu.sp, v₃.sp, v₂.sp, v₁.sp])
        (fun r a b => by rw [mu.gpr, v₃.other r a, v₂.other r b, v₁.other r a, gt r a b]) ?_
      simp only [ite_true]
      rw [v₂.other .a0 (by decide), v₁.gpr, v₂.gpr, v₁.mem]
      change t.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 ^^^ md s₀ t.mem (cur * 1024 + 8 * n) = _
      rw [sw_t, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Impl.Argon2.RISCV64.Derive (passOff counterOff tmpOff curOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : Outside s₀ ⟨gwP s₀, 4096⟩ :=
  outside_scr hp (o := 4096) (n := 4096) (.inr ⟨by decide, by decide⟩)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 64 (R * 1024)) :
    WP isa Impl.Argon2.RISCV64.Derive.fillCompress s fun t => FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d) ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 0) =
        compress (blockAt s.mem (matrixCell (memP s₀) (lane * (prm s₀).laneLen +
          (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memP s₀) R)) := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega_arith))
  unfold Impl.Argon2.RISCV64.Derive.fillCompress Impl.Argon2.RISCV64.HPrime.mov
    Impl.Argon2.RISCV64.Derive.gScratch
  simp only [List.cons_append, List.nil_append]
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_only k₁
  refine WP.seq (wp_ldloc h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => wp_addi (by decide) fun s₃ u₃ =>
    wp_addi (imm := 1024) (by decide) fun s₄ u₄ => wp_addi (imm := 1024) (by decide) fun s₅ u₅ =>
      WP.block_nil ?_)
  have k₄ := (((Only.of_upd u₂).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have h₄ := h₁.of_only k₄
  have m₄ : s₅.mem = s.mem := by rw [k₄.mem, k₁.mem]
  have ax : s₅.gpr .a0 = memP s₀ + BitVec.ofNat 64 (P * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₅.gpr .a1 = memP s₀ + BitVec.ofNat 64 (R * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  have cx : s₅.gpr .a2 = scrP s₀ + BitVec.ofNat 64 0 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h₁.inv.s4]
  have dx : s₅.gpr .a3 = gwP s₀ := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h₁.inv.s0, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  refine ccall_ok hp h₄.inv dx (o := 0) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨scrP s₀ + BitVec.ofNat 64 0, 1024⟩, ⟨gwP s₀, 4096⟩], Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outside_scr hp (.inl (by decide))
    · exact outside_work hp
  refine ⟨h₄.frame hp it f ho, fun d h₁ => ?_, ?_⟩
  · rw [lw_keep hp f (fun r hr => ⟨scrR s₀, by simp, ?_⟩) h₁, lw_mem m₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_sub (by decide)
    · exact scr_sub (o := 4096) (n := 4096) (by decide)
  · rw [post, ax, sx, m₄]; rfl

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 64 (C * 1024)) :
    WP isa Impl.Argon2.RISCV64.Derive.fillWrite s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memP s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memP s₀) C) = if pass = 0 then blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0)
        else xorBlock (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0)) (blockAt s.mem (matrixCell (memP s₀) C)) := by
  unfold Impl.Argon2.RISCV64.Derive.fillWrite Impl.Argon2.RISCV64.HPrime.mov
  refine WP.seq (wp_addi (by decide) fun s₁ u₁ => ?_)
  have h₁ := h.of_only (Only.of_upd u₁)
  refine wp_ldloc h₁.inv (d := curOff) (by decide) fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂)
  refine wp_ldloc h₂.inv (d := passOff) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have h₃ := h₂.of_only (Only.of_upd u₃)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have si : s₃.gpr .a1 = scrP s₀ + BitVec.ofNat 64 0 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.inv.s4]
  have di : s₃.gpr .a3 = memP s₀ + BitVec.ofNat 64 (C * 1024) := by
    rw [u₃.other _ (by decide), u₂.gpr, lw_mem u₁.mem, hcur]
  have Pw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, scrP s₀ + BitVec.ofNat 64 0 = R.base + BitVec.ofNat 64 off ∧
      off + 1024 ≤ R.len := ⟨scrR s₀, by simp, 0, rfl, show 0 + 1024 ≤ 16384 by decide⟩
  have PC : Region.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 0, 1024⟩ ⟨matrixCell (memP s₀) C, 1024⟩ :=
    (hp.mem_scr.symm.sub_left (scr_sub (by decide))).sub_right (Proof.Argon2.matrixCell_sub _ _ _ hC)
  have done : ∀ (xo : Bool) (t : State), (∀ i < 128, md s₀ t.mem (C * 1024 + 8 * i) = if i < 128 then
        (if xo then s₃.mem.readW (scrP s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i)) 64 ^^^
            md s₀ s₃.mem (C * 1024 + 8 * i)
          else s₃.mem.readW (scrP s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i)) 64)
        else md s₀ s₃.mem (C * 1024 + 8 * i)) →
      blockAt t.mem (matrixCell (memP s₀) C) = if xo then
        xorBlock (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0)) (blockAt s.mem (matrixCell (memP s₀) C))
        else blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0) :=
    fun xo t wt => by
      apply Vector.ext
      intro j hj
      rw [cell_get _ _ hj, wt j hj, ite_eq_left hj, m₃]
      cases xo
      · simp only [Bool.false_eq_true, ite_false]; rw [blockAt_get _ _ hj]
      · simp only [ite_true]
        rw [xorBlock, Vector.getElem_zipWith, blockAt_get _ _ hj, cell_get _ _ hj]
  refine WP.ite (decide (pass = 0)) (zero_eval (by omega_arith) (by rw [u₃.gpr, h₂.pos.pass]))
    (fun hb => ?_) fun hb => ?_
  · refine ((writeWords_ok hp h₃.inv hC false si (by rw [BitVec.add_zero]; exact h₃.inv.sal) Pw PC di 128 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₃]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((writeWords_ok hp h₃.inv hC true si (by rw [BitVec.add_zero]; exact h₃.inv.sal) Pw PC di 128 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₃]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.RISCV64.Derive.fillBlock s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.RISCV64.Derive.fillBlock
  refine WP.seq ((randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((reference_ok hp ⟨h₁, w₁.1, w₁.2⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have cur' : lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) < blocksN s₀ := by
    rw [hb]; exact curLt
  have kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memP s₀) j) = blockAt t₃.mem (matrixCell (memP s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) cur' ne
  have lt : ∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ t₃ d := fun d h₁ =>
    lw_keep hp ft (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨memR s₀, by simp, Proof.Argon2.matrixCell_sub _ _ _ cur'⟩) h₁
  refine ⟨it, Prm.of_lw h₃.pr fun d h₁ h₂ => lt d (by omega_arith),
    h₃.pos.of_lw fun d h₁ h₂ => lt d (by omega_arith), ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [blockAt_keep ft (fun r hr => ?_), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact ((cell_disj hp cur' (scrR s₀) (by simp)).symm.sub_left (scr_sub (by decide)))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end

end VG.Proof.Argon2.RISCV64.Derive
