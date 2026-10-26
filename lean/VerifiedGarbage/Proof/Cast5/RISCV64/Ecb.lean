module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Cast5.ModeMem
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# CAST5 on RISC-V: ECB

`ecb_wp`: every block becomes its encryption or decryption, one at a time
(`loop_run`); our caller's `s0`–`s10` are saved in the working space,
rounded up to a multiple of 8 (`prologue_ok`), and restored. The loop
writes only the blocks. As on PPC64LE (`Proof/Cast5/PPC64LE/Ecb.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)]
  exact h i hi

theorem s1234_len : 8 * Impl.Cast5.s1234.length = 4096 := by rw [Impl.Cast5.s1234, table_length]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this; exact this)
    simp only [bne, decide_eq_false h, Bool.not_false, Bool.not_eq_true']
    exact beq_eq_false_iff_ne.mpr this

/-! ## The loop -/

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The registers the loop writes. -/
def loopWrites : List Reg := roundRegs ++ [dat, cnt]

/-- The loop's fixed facts, about the state `s₀` before it: the schedule at
`S`, the `n` blocks at `D`, and the table at `T`, readable and apart from
the blocks. -/
structure LoopEnv (S D T : Addr) (n N : Nat) (s₀ : State) : Prop where
  r3 : s₀.gpr sch = S
  r4 : s₀.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  tbl : s₀.gpr tbl = T
  key : (⟨S, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  kfit : S.toNat + 128 ≤ 2 ^ 64
  data : (⟨D, 8 * N⟩ : Region) ∈ s₀.wr
  keyData : (⟨S, 128⟩ : Region).Disjoint ⟨D, 8 * N⟩
  fit : D.toNat + 8 * N ≤ 2 ^ 64
  trd : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr
  held : Held s₀.mem T Impl.Cast5.s1234
  tblData : (⟨T, 4096⟩ : Region).Disjoint ⟨D, 8 * N⟩

/-- After `k` blocks. -/
structure EInv (S D : Addr) (n N : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ N
  ptr : u.gpr dat = wAt D k
  cnt : u.gpr cnt = BitVec.ofNat 64 (N - k)
  keep : Keep loopWrites s₀ u
  done : ∀ b < k, Spec.Cast5.blockAt u.mem (wAt D b) =
    cipher up (Spec.Cast5.scheduleAt s₀.mem S) n (Spec.Cast5.blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < N → Spec.Cast5.blockAt u.mem (wAt D b) = Spec.Cast5.blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * N⟩] s₀.mem u.mem

theorem ecb_step {S D T : Addr} {n N : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D T n N s₀) {k : Nat}
    (hk : k < N) {u : State} (I : EInv S D n N up s₀ k u) :
    WP isa (.seq (crypt up dat) (.block [.addi dat dat 8, .addi cnt cnt (-1)])) u
      (fun u' => EInv S D n N up s₀ (k + 1) u' ∧ u'.gpr cnt = BitVec.ofNat 64 (N - (k + 1))) := by
  have fit := L.fit
  have g (q : Reg) (hq : q ∉ loopWrites := by decide) : u.gpr q = s₀.gpr q := I.keep.gpr hq
  have dTD : ∀ r ∈ [(⟨D, 8 * N⟩ : Region)], Region.Disjoint ⟨T, 8 * Impl.Cast5.s1234.length⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [s1234_len]; exact L.tblData
  have hK : Spec.Cast5.scheduleAt u.mem S = Spec.Cast5.scheduleAt s₀.mem S :=
    Proof.Cast5.scheduleAt_frame I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have bp : BPre u dat (wAt D k) S n :=
    { ptr := I.ptr
      prOk := by decide
      sched := by rw [g sch]; exact L.r3
      rounds := by rw [g rnd]; exact L.r4
      nv := L.nv
      trd := by rw [g tbl, L.tbl, I.keep.2.1, I.keep.2.2]; exact L.trd
      held := by
        rw [g tbl, L.tbl]
        exact held_frame I.frame dTD (by rw [s1234_len]; decide) L.held
      inP := ⟨_, by rw [I.keep.2.2]; exact L.data, Offset.contains_base D (by omega_arith) (by omega_arith)⟩
      inK := by rw [I.keep.2.1, I.keep.2.2]; exact L.key
      kfit := L.kfit }
  refine WP.seq (WP.mono (crypt_ok bp up) fun u₁ B => ?_)
  refine wp_addi (imm := 8) (by decide) fun u₂ h₂ => wp_subi (imm := 1) (by decide) fun u₃ h₃ => WP.block_nil ?_
  have m₃ : u₃.mem = u₁.mem := by rw [h₃.mem, h₂.mem]
  have c₃ : u₃.gpr cnt = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [h₃.gpr, h₂.other _ (by decide), B.keep.gpr (by decide), I.cnt]
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  have other : ∀ b, b < N → b ≠ k →
      Spec.Cast5.blockAt u₃.mem (wAt D b) = Spec.Cast5.blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame B.frame fun r hr => ?_]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)
  have hk3 : Keep loopWrites s₀ u₃ := ⟨fun r hr => by
      have h1 : r ≠ dat := fun e => hr (by rw [e]; decide)
      have h2 : r ≠ cnt := fun e => hr (by rw [e]; decide)
      rw [h₃.other r h2, h₂.other r h1, B.keep.gpr (fun e => hr (List.mem_append_left _ e)), I.keep.gpr hr],
    by rw [h₃.rd, h₂.rd, B.keep.2.1, I.keep.2.1], by rw [h₃.wr, h₂.wr, B.keep.2.2, I.keep.2.2]⟩
  refine ⟨⟨by omega_arith, ?_, c₃, hk3, fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃⟩
  · rw [h₃.other _ (by decide), h₂.gpr, B.keep.gpr (by decide), I.ptr, Offset.add_add]
    congr 2
  · by_cases hbk : b = k
    · subst hbk
      rw [m₃, B.blk, hK, I.rest b (by omega_arith) hk]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · rw [m₃]
    refine I.frame.trans (B.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base D (by omega_arith)⟩

theorem loop_run {S D T : Addr} {n N : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D T n N s₀) (hn : 0 < N)
    {u : State} (I : EInv S D n N up s₀ 0 u) :
    WP isa (.loop (.seq (crypt up dat) (.block [.addi dat dat 8, .addi cnt cnt (-1)])) (.nonzero cnt)) u
      (EInv S D n N up s₀ N) := by
  refine WP.loop (M := isa) (Q := EInv S D n N up s₀ N)
    (fun m v => ∃ k, k < N ∧ m = N - k ∧ EInv S D n N up s₀ k v) ?_ N u ⟨0, hn, rfl, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (ecb_step L hk J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : N < 2 ^ 64 := by have := L.fit; omega_arith
  rw [eval_nonzero, hz, ofNat_bne_zero (by omega_arith)]
  by_cases e : k + 1 = N
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, N - (k + 1), by omega_arith, k + 1, by omega_arith, rfl, J'⟩

/-! ## Saving and restoring -/

/-- The working space at `P` rounded up to a multiple of 8. -/
abbrev wbase (P : Addr) : Addr := P + BitVec.ofNat 64 (Align.pad P)

theorem prologue_eq (b : Reg) (sym : String) :
    prologue b sym = .addi b b 7 :: .logicImm .and b b (-8) ::
      (Spill.saveCode b savedSlots ++ ([.lla tbl sym] : List Instr)) := rfl

theorem epilogue_eq (b : Reg) : epilogue b = Spill.restoreCode b savedSlots := rfl

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem savedSlots_ok : ∀ p ∈ savedSlots, p.2 % 8 = 0 ∧ p.2 < 2048 := savedSlots_fits.1
theorem savedSlots_fst : ∀ p ∈ savedSlots, p.1 ∈ saved := by decide
theorem savedSlots_lt : ∀ p ∈ savedSlots, 64 ≤ p.2 ∧ p.2 + 8 ≤ 64 + 88 := by decide

/-- An access of `w` bytes at offset `d` of the rounded working space lies
within the working space at `P` (256 bytes). -/
theorem wbase_in {rs : List Region} {P : Addr} (hP : (⟨P, 256⟩ : Region) ∈ rs)
    {d w : Nat} (hd : d + w ≤ 249) : InRegions rs (wbase P + BitVec.ofNat 64 d) w :=
  ⟨_, hP, by
    have := Align.pad_lt P
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The rounded working space's bytes `[d, d + n)` are within the working space. -/
theorem wbase_sub (P : Addr) {d n : Nat} (hd : d + n ≤ 249) :
    Region.Sub ⟨wbase P + BitVec.ofNat 64 d, n⟩ ⟨P, 256⟩ := by
  rw [Offset.add_add]
  exact Offset.sub_base _ (by have := Align.pad_lt P; omega_arith)

theorem wbase_sub0 (P : Addr) {n : Nat} (hn : n ≤ 249) : Region.Sub ⟨wbase P, n⟩ ⟨P, 256⟩ := by
  have h := wbase_sub P (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at h

theorem wbase_toNat {P : Addr} (h : P.toNat + 256 ≤ 2 ^ 64) : (wbase P).toNat = P.toNat + Align.pad P := by
  have := Align.pad_lt P
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Align.pad P) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

/-- The prologue: the working space at `b` rounded up, the slots there hold
the callee-saved registers, and the table's address is in `tbl`. -/
theorem prologue_ok (s : State) (b : Reg) (hb : b ∉ saved ∧ b ≠ tbl) (sym : String) {P : Addr}
    (hB : s.gpr b = P) (hP : (⟨P, 256⟩ : Region) ∈ s.wr)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Spill.Saved (wbase P) s.gpr savedSlots u.mem →
      Frame [⟨wbase P + BitVec.ofNat 64 64, 88⟩] s.mem u.mem →
      Keep [b, tbl] s u → u.gpr b = wbase P → u.gpr tbl = s.syms sym → u.syms = s.syms →
      WP isa (.block is) u Q) :
    WP isa (.block (prologue b sym ++ is)) s Q := by
  rw [prologue_eq, List.cons_append, List.cons_append, List.append_assoc]
  refine WP.cons (exec_addi (by decide)) (WP.cons (exec_logicImm (by decide)) ?_)
  generalize hs₂ : State.write _ b _ = s₂
  have h₂ : s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.syms = s.syms := by
    subst hs₂; exact ⟨rfl, rfl, rfl, rfl⟩
  have e₂ : s₂.gpr b = wbase P := by
    subst hs₂
    simp only [RegUpd.gpr_write_self, hB]
    exact Align.align_eq P
  have g₂ : ∀ r, r ≠ b → s₂.gpr r = s.gpr r := fun r hr => by
    subst hs₂; simp only [RegUpd.gpr_write_of_ne _ _ hr]
  refine Spill.save_ok (s := s₂) (by rw [e₂]; exact Align.align_al P) savedSlots_ok
    (fun p hp => by
      rw [e₂, h₂.2.2.1]
      exact wbase_in hP (by have := savedSlots_lt p hp; omega_arith)) ?_
  rw [List.cons_append, List.nil_append]
  refine WP.cons exec_lla ?_
  have sv : Spill.Saved (wbase P) s.gpr savedSlots
      (Spill.saveMem s₂.mem (s₂.gpr b) s₂.gpr savedSlots) := by
    have h := Spill.saveMem_saved savedSlots_fits s₂.mem (s₂.gpr b) s₂.gpr
    rw [e₂] at h
    intro p hp
    rw [e₂, h p hp, g₂ p.1 (fun e => hb.1 (by
      rw [← e]; exact savedSlots_fst p hp))]
  have fr : Frame [⟨wbase P + BitVec.ofNat 64 64, 88⟩] s.mem
      (Spill.saveMem s₂.mem (s₂.gpr b) s₂.gpr savedSlots) := by
    rw [e₂, h₂.1]
    exact Spill.saveMem_frame savedSlots_lt (by decide) _ _ _
  refine k _ sv fr ⟨fun r hr => ?_, h₂.2.1, h₂.2.2.1⟩
    (by simp only [State.write]; rw [ite_eq_right hb.2]; exact e₂)
    (by simp [State.write, h₂.2.2.2]) h₂.2.2.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [State.write, hr.2, ite_false]
  exact g₂ r hr.1

/-- The epilogue: the callee-saved registers restored from the slots. -/
theorem epilogue_ok (u : State) (b : Reg) (hb : Spill.Restorable b savedSlots) {P : Addr} (hB : u.gpr b = wbase P)
    (hP : (⟨P, 256⟩ : Region) ∈ u.wr) {g : Reg → BitVec 64} (hsv : Spill.Saved (wbase P) g savedSlots u.mem) :
    WP isa (.block (epilogue b)) u (Spill.Restored g savedSlots u) := by
  rw [epilogue_eq, ← List.append_nil (Spill.restoreCode b savedSlots)]
  refine Spill.restore_ok (Align.align_al P) hB savedSlots_ok hb (fun p hp => ?_) hsv
    fun s' R => WP.block_nil R
  have ⟨r, hr, hc⟩ := wbase_in (rs := u.wr) hP (d := p.2) (w := 8) (by have := savedSlots_lt p hp; omega_arith)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A restored register holds what it held before the prologue. -/
theorem restored_saved {g : Reg → BitVec 64} {u s' : State} (R : Spill.Restored g savedSlots u s') {r : Reg}
    (hr : r ∈ saved) : s'.gpr r = g r :=
  R.gpr_of (.inl (by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide))

/-! ## The function -/

/-- What ECB may assume: the schedule and the table readable, the `n`
blocks and the working space writable, all apart, none wrapping around, and
12 or 16 rounds. -/
structure EcbPre (s : State) : Prop where
  key : (⟨s.gpr .a0, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : (s.gpr .a0).toNat + 128 ≤ 2 ^ 64
  data : (⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩ : Region) ∈ s.wr
  fit : (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64
  scr : (⟨s.gpr .a4, 256⟩ : Region) ∈ s.wr
  keyData : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
  keyScr : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a4, 256⟩
  dataScr : (⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, 256⟩
  nv : (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 16
  trd : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.syms Impl.Cast5.s1234Sym) Impl.Cast5.s1234
  tblData : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
  tblScr : (⟨s.syms Impl.Cast5.s1234Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .a4, 256⟩

/-- What ECB guarantees. -/
structure EcbPost (up : Bool) (s s' : State) : Prop where
  done : ∀ b < (s.gpr .a3).toNat, Spec.Cast5.blockAt s'.mem (wAt (s.gpr .a2) b) =
    cipher up (Spec.Cast5.scheduleAt s.mem (s.gpr .a0)) (s.gpr .a1).toNat
      (Spec.Cast5.blockAt s.mem (wAt (s.gpr .a2) b))
  saved : ∀ r ∈ saved, s'.gpr r = s.gpr r

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Cast5.RISCV64.ecb up) s (EcbPost up s) := by
  have fit := h.fit
  have sub88 : Region.Sub ⟨wbase (s.gpr .a4) + BitVec.ofNat 64 64, 88⟩ ⟨s.gpr .a4, 256⟩ := wbase_sub _ (by decide)
  unfold Impl.Cast5.RISCV64.ecb
  apply WP.seq
  rw [← List.append_nil (prologue wkE _)]
  refine prologue_ok s wkE (by decide) _ rfl h.scr fun s₀ sv₀ fr₀ k₀ w₀ t₀ sy₀ => WP.block_nil ?_
  have g₀ (q : Reg) (hq : q ∉ [wkE, tbl] := by decide) : s₀.gpr q = s.gpr q := k₀.gpr hq
  have dS : ∀ r ∈ [(⟨wbase (s.gpr .a4) + BitVec.ofNat 64 64, 88⟩ : Region)],
      Region.Disjoint ⟨s.gpr .a0, 128⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.keyScr.sub_right sub88
  have dB (b : Nat) (hb : b < (s.gpr .a3).toNat) :
      ∀ r ∈ [(⟨wbase (s.gpr .a4) + BitVec.ofNat 64 64, 88⟩ : Region)], Region.Disjoint ⟨wAt (s.gpr .a2) b, 8⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (h.dataScr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right sub88
  have L : LoopEnv (s.gpr .a0) (s.gpr .a2) (s.syms Impl.Cast5.s1234Sym) (s.gpr .a1).toNat (s.gpr .a3).toNat s₀ :=
    { r3 := g₀ _
      r4 := by rw [g₀ rnd]; simp
      nv := h.nv
      tbl := t₀
      key := by rw [k₀.2.1, k₀.2.2]; exact h.key
      kfit := h.kfit
      data := by rw [k₀.2.2]; exact h.data
      keyData := h.keyData
      fit := fit
      trd := by rw [k₀.2.1, k₀.2.2]; exact h.trd
      held := held_frame fr₀ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [s1234_len]; exact h.tblScr.sub_right sub88)
        (by rw [s1234_len]; decide) h.held
      tblData := h.tblData }
  have I0 : EInv (s.gpr .a0) (s.gpr .a2) (s.gpr .a1).toNat (s.gpr .a3).toNat up s₀ 0 s₀ :=
    ⟨by omega_arith, by rw [g₀ dat]; simp [wAt], by rw [g₀ cnt]; simp, Keep.refl _ _,
      fun b hb => absurd hb (by omega_arith), fun _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (Q := EInv (s.gpr .a0) (s.gpr .a2) (s.gpr .a1).toNat (s.gpr .a3).toNat up s₀
    (s.gpr .a3).toNat) ?_ fun u U => ?_
  · refine WP.ite (s.gpr .a3 == 0) (by rw [eval_zero, g₀ cnt]) (fun hz => ?_) (fun hz => ?_)
    · have hn : (s.gpr .a3).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
      exact WP.block_nil (hn ▸ I0)
    · have hn : 0 < (s.gpr .a3).toNat := by
        have : s.gpr .a3 ≠ 0 := by simpa using hz
        have : (s.gpr .a3).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
        omega_arith
      exact loop_run L hn I0
  · have r7 : u.gpr wkE = wbase (s.gpr .a4) := by rw [U.keep.gpr (by decide), w₀]
    have hsv : Spill.Saved (wbase (s.gpr .a4)) s.gpr savedSlots u.mem :=
      sv₀.frame U.frame fun p hp r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact h.dataScr.symm.sub_left (wbase_sub _ (by have := savedSlots_lt p hp; omega_arith))
    refine WP.mono (epilogue_ok u wkE (by decide) r7 (by rw [U.keep.2.2, k₀.2.2]; exact h.scr) hsv)
      fun s' R => ⟨fun b hb => ?_, fun r hr => restored_saved R hr⟩
    rw [R.mem, U.done b hb, Proof.Cast5.scheduleAt_frame fr₀ dS, blockAt_frame fr₀ (dB b hb)]

end VG.Proof.Cast5.RISCV64
