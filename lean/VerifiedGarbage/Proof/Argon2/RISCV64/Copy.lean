module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Rounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Wp

/-! # Argon2 compression on RISC-V: the initial and final XORs -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64 VG.Spec.Argon2
open VG.RISCV64.Wp (Upd)

theorem blockAt_get (m : Mem) (p : Addr) (i : Fin 128) :
    (blockAt m p)[i] = m.readW (off p (8 * i.val)) 64 := by
  simp only [blockAt, Fin.getElem_fin, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

theorem xorBlock_get (a b : Block) (i : Fin 128) :
    (xorBlock a b)[i] = a[i] ^^^ b[i] := by
  simp only [xorBlock, Fin.getElem_fin, Vector.getElem_zipWith]

/-- The copying blocks change only `t0`, `t1` and memory. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .t0 → r ≠ .t1 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem CopyKeeps.refl (s : State) : CopyKeeps s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (h' : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r h0 h22 => (h'.1 r h0 h22).trans (h.1 r h0 h22), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem Scratch.of_copy {s t : State} {p : Addr} (hs : Scratch s p) (h : CopyKeeps s t) :
    Scratch t p := ⟨(h.1 .a3 (by decide) (by decide)).trans hs.reg, h.2.2.1 ▸ hs.wr, hs.al⟩

theorem off8 (i : Nat) (hi : i < 128) : 8 * i < 2048 := by omega_arith

theorem al_reg {s : State} {r : Reg} {x : Addr} (h : s.gpr r = x) (hx : x.toNat % 8 = 0) (d : Nat)
    (hd : d % 8 = 0) : (s.gpr r + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [h]; exact Spill.al8 hx hd

theorem initWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 128)
    (hx : InRegions (s.rd ++ s.wr) (off (s.gpr .a0) (8 * i)) 8)
    (hy : InRegions (s.rd ++ s.wr) (off (s.gpr .a1) (8 * i)) 8)
    (ax : (s.gpr .a0).toNat % 8 = 0) (ay : (s.gpr .a1).toNat % 8 = 0) :
    let a := s.mem.readW (off (s.gpr .a0) (8 * i)) 64 ^^^ s.mem.readW (off (s.gpr .a1) (8 * i)) 64
    WP isa (.block (initWord i)) s fun t =>
      t.mem = (s.mem.writeW (off p (8 * i)) a).writeW (off p (1024 + 8 * i)) a ∧
      CopyKeeps s t := by
  dsimp only
  have w1 := hs.write (d := 8 * i) (n := 8) (by omega_arith)
  have w2 := hs.write (d := 1024 + 8 * i) (n := 8) (by omega_arith)
  rw [← hs.reg] at w1 w2
  unfold initWord
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (off8 i hi) (al_reg rfl ax _ (by omega_arith)) hx, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (off8 i hi)
    (al_reg (by simp [State.write]) ay _ (by omega_arith)) (by simpa [State.write] using hy), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_logic (op := .xor), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (off8 i hi)
    (al_reg (by simp [State.write]; exact hs.reg) hs.al _ (by omega_arith)) (by simpa [State.write] using w1), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (word_offset i hi)
    (al_reg (by simp [State.write]; exact hs.reg) hs.al _ (by omega_arith)) (by simpa [State.write] using w2), ?_⟩
  refine WP.block_nil ⟨?_, fun r h0 h22 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, hs.reg]
  · simp [State.write, h0, h22]

theorem finishWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 128)
    (hout : InRegions s.wr (off (s.gpr .a2) (8 * i)) 8) (ao : (s.gpr .a2).toNat % 8 = 0) :
    WP isa (.block (finishWord i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .a2) (8 * i))
          (word s.mem p i ^^^ s.mem.readW (off p (8 * i)) 64) ∧
      CopyKeeps s t := by
  have r1 := hs.read (d := 8 * i) (n := 8) (by omega_arith)
  have r2 := hs.read (d := 1024 + 8 * i) (n := 8) (by omega_arith)
  rw [← hs.reg] at r1 r2
  unfold finishWord
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (word_offset i hi)
    (al_reg hs.reg hs.al _ (by omega_arith)) r2, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (off8 i hi)
    (al_reg (by simp [State.write]; exact hs.reg) hs.al _ (by omega_arith)) (by simpa [State.write] using r1), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_logic (op := .xor), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (off8 i hi)
    (al_reg (by simp [State.write]) ao _ (by omega_arith)) (by simpa [State.write] using hout), ?_⟩
  refine WP.block_nil ⟨?_, fun r h0 h22 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, hs.reg]
  · simp [State.write, h0, h22]

structure Inputs (s : State) (x y p : Addr) : Prop where
  xreg : s.gpr .a0 = x
  yreg : s.gpr .a1 = y
  xread : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr
  yread : (⟨y, 1024⟩ : Region) ∈ s.rd ++ s.wr
  xsep : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  ysep : (⟨y, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  xal : x.toNat % 8 = 0
  yal : y.toNat % 8 = 0

theorem Inputs.of_copy {s t : State} {x y p : Addr} (h : Inputs s x y p) (hk : CopyKeeps s t) :
    Inputs t x y p := ⟨(hk.1 .a0 (by decide) (by decide)).trans h.xreg,
      (hk.1 .a1 (by decide) (by decide)).trans h.yreg, by simpa only [hk.2.1, hk.2.2.1] using h.xread,
      by simpa only [hk.2.1, hk.2.2.1] using h.yread, h.xsep, h.ysep, h.xal, h.yal⟩

theorem input_unchanged {m m' : Mem} {x p : Addr} {n : Nat} (hf : Frame [⟨p, n⟩] m m')
    (hd : (⟨x, 1024⟩ : Region).Disjoint ⟨p, n⟩) (i : Fin 128) :
    m'.readW (off x (8 * i.val)) 64 = m.readW (off x (8 * i.val)) 64 :=
  hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega_arith) (by omega_arith))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- A prefix of the two scratch copies is initialized. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n →
    m.readW (off p (8 * i.val)) 64 = r[i] ∧ word m p i.val = r[i]

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Initialized m p r n) :
    Initialized ((m.writeW (off p (8 * n)) r[n]).writeW (off p (1024 + 8 * n)) r[n]) p r (n + 1) := by
  intro i hi
  obtain ⟨k, hk⟩ := i
  simp only at hi
  simp only [word]
  rcases (by omega_arith : k = n ∨ k < n) with rfl | he
  · refine ⟨?_, Mem.readW_writeW_self64 _ _ _⟩
    rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
    rfl
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h ⟨k, hk⟩ he

/-- Initialize a prefix of the words, framing the first half of scratch. -/
theorem init_prefix (n : Nat) (hn : n ≤ 128) (s : State) {x y p : Addr}
    (hs : Scratch s p) (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initWord)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 2048⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega_arith
    have htIn := hin.of_copy hk
    have lx : InRegions (t.rd ++ t.wr) (off (t.gpr .a0) (8 * n)) 8 := by
      rw [htIn.xreg]
      exact ⟨_, htIn.xread, Offset.contains_base x (by omega_arith) (by omega_arith)⟩
    have ly : InRegions (t.rd ++ t.wr) (off (t.gpr .a1) (8 * n)) 8 := by
      rw [htIn.yreg]
      exact ⟨_, htIn.yread, Offset.contains_base y (by omega_arith) (by omega_arith)⟩
    refine (initWord_ok t (hs.of_copy hk) n hn' lx ly (by rw [htIn.xreg]; exact hin.xal)
      (by rw [htIn.yreg]; exact hin.yal)).mono ?_
    rintro u ⟨hm, hk'⟩
    have hv : t.mem.readW (off x (8 * n)) 64 ^^^ t.mem.readW (off y (8 * n)) 64 =
        (xorBlock (blockAt s.mem x) (blockAt s.mem y))[n] := by
      rw [show (xorBlock (blockAt s.mem x) (blockAt s.mem y))[n] =
          (xorBlock (blockAt s.mem x) (blockAt s.mem y))[(⟨n, hn'⟩ : Fin 128)] from rfl,
        xorBlock_get, blockAt_get, blockAt_get,
        input_unchanged hf (hin.xsep.sub_right (Region.sub_prefix (by omega_arith))) ⟨n, hn'⟩,
        input_unchanged hf (hin.ysep.sub_right (Region.sub_prefix (by omega_arith))) ⟨n, hn'⟩]
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hm, htIn.xreg, htIn.yreg, hv]
      exact initialized_step hn' ht
    · rw [hm]
      exact (hf.writeW (r := ⟨p, 2048⟩) (by simp) _
        (Offset.contains_base p (by omega_arith) (by omega_arith))).writeW (r := ⟨p, 2048⟩) (by simp) _
        (Offset.contains_base p (by omega_arith) (by omega_arith))

/-- The initialized copies both contain X XOR Y. -/
theorem initialized_blocks {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r 128) :
    blockAt m p = r ∧ working m p = r := by
  constructor
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).1
    rw [← blockAt_get m p ⟨i, hi⟩] at he
    exact he
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).2
    rw [← working_get m p ⟨i, hi⟩] at he
    exact he

/-- A prefix of the output block has been written. -/
def Written (m : Mem) (out : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n → m.readW (off out (8 * i.val)) 64 = r[i]

theorem written_step {m : Mem} {out : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Written m out r n) :
    Written (m.writeW (off out (8 * n)) r[n]) out r (n + 1) := by
  intro i hi
  by_cases he : i.val = n
  · subst n
    exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep out (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h i (by omega_arith)

theorem scratch_unchanged {m m' : Mem} {out p : Addr} (hf : Frame [⟨out, 1024⟩] m m')
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) {d : Nat} (hd' : d + 8 ≤ 4096) :
    m'.readW (off p d) 64 = m.readW (off p d) 64 :=
  hf.readW (r := ⟨p, 4096⟩) (Offset.contains_base p hd' (by omega_arith))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- Finish a prefix of the words. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 128) (s : State) {p out : Addr}
    (hs : Scratch s p) (ho : s.gpr .a2 = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) (hal : out.toNat % 8 = 0) :
    WP isa (.block ((List.range n).flatMap finishWord)) s fun t =>
      Written t.mem out (xorBlock (working s.mem p) (blockAt s.mem p)) n ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega_arith
    have ho' : t.gpr .a2 = out := (hk.1 .a2 (by decide) (by decide)).trans ho
    have hout : InRegions t.wr (off (t.gpr .a2) (8 * n)) 8 := by
      rw [ho', hk.2.2.1]
      exact ⟨_, hw, Offset.contains_base out (by omega_arith) (by omega_arith)⟩
    refine (finishWord_ok t (hs.of_copy hk) n hn' hout (by rw [ho']; exact hal)).mono ?_
    rintro u ⟨hm, hk'⟩
    have hv : word t.mem p n ^^^ t.mem.readW (off p (8 * n)) 64 =
        (xorBlock (working s.mem p) (blockAt s.mem p))[n] := by
      rw [show (xorBlock (working s.mem p) (blockAt s.mem p))[n] =
          (xorBlock (working s.mem p) (blockAt s.mem p))[(⟨n, hn'⟩ : Fin 128)] from rfl,
        xorBlock_get, working_get, blockAt_get]
      simp only [word, scratch_unchanged hf hd (d := 1024 + 8 * n) (by omega_arith),
        scratch_unchanged hf hd (d := 8 * n) (by omega_arith)]
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hm, ho', hv]
      exact written_step hn' ht
    · rw [hm, ho']
      exact hf.writeW (r := ⟨out, 1024⟩) (by simp) _ (Offset.contains_base out (by omega_arith) (by omega_arith))

theorem written_block {m : Mem} {out : Addr} {r : Block} (h : Written m out r 128) :
    blockAt m out = r := by
  apply Vector.ext
  intro i hi
  have he := h ⟨i, hi⟩ hi
  rw [← blockAt_get m out ⟨i, hi⟩] at he
  exact he

end VG.Proof.Argon2.RISCV64
