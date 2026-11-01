module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.AArch64.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-! Merged from `Proof.Argon2.AArch64.Copy`. -/

@[expose] public section

section
/-! # Initial XOR and final XOR, one word at a time -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

theorem exec_ldrq_dwords {s : State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (ofVDwords
      (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)
      (s.mem.readW (s.gpr n + BitVec.ofNat 64 (off + 8)) 64))) := by
  simp only [exec, addr, show off < 4096 * 16 by omega_arith, ho, and_self, ite_true, Option.bind_some,
    State.load, h, Option.map_some, read16_dwords, Offset.add_add]

theorem exec_strq_write {s : State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show off < 4096 * 16 by omega_arith, ho, and_self, ite_true, Option.bind_some,
    State.store, h]

theorem ofVDwords_xor (a b c d : BitVec 64) :
    ofVDwords a b ^^^ ofVDwords c d = ofVDwords (a ^^^ c) (b ^^^ d) := by
  rw [ofVDwords, ofVDwords, ofVDwords, BitVec.xor_append]

theorem exec_eor_v {s : State} {d n m : VReg} :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

theorem initPair_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 64)
    (hx : InRegions (s.rd ++ s.wr) (off (s.gpr .x0) (16 * i)) 16)
    (hy : InRegions (s.rd ++ s.wr) (off (s.gpr .x1) (16 * i)) 16) :
    let a := s.mem.readW (off (s.gpr .x0) (16 * i)) 64 ^^^
      s.mem.readW (off (s.gpr .x1) (16 * i)) 64
    let b := s.mem.readW (off (s.gpr .x0) (16 * i + 8)) 64 ^^^
      s.mem.readW (off (s.gpr .x1) (16 * i + 8)) 64
    WP isa (.block (initPair i)) s fun t =>
      t.mem = (((s.mem.writeW (off p (16 * i)) a).writeW (off p (16 * i + 8)) b).writeW
        (off p (1024 + 16 * i)) a).writeW (off p (1024 + 16 * i + 8)) b ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  have w1 := hs.write (d := 16 * i) (n := 16) (by omega_arith)
  have w2 := hs.write (d := 1024 + 16 * i) (n := 16) (by omega_arith)
  have e1 : (16 * i) % 16 = 0 ∧ 16 * i < 65536 := by omega_arith
  have e2 : (1024 + 16 * i) % 16 = 0 ∧ 1024 + 16 * i < 65536 := by omega_arith
  simp only [off] at hx hy w1 w2
  rw [initPair]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e1 hx, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e1 hy, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_eor_v, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq_write e1 (by rw [← hs.reg] at w1; exact w1), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq_write e2 (by rw [← hs.reg] at w2; exact w2), ?_⟩
  refine WP.block_nil ⟨?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_setV_self,
    RegUpd.v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), hs.reg,
    ofVDwords_xor, write16_dwords, Offset.add_add, off]

theorem finishPair_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 64)
    (hout : InRegions s.wr (off (s.gpr .x2) (16 * i)) 16) :
    WP isa (.block (finishPair i)) s fun t =>
      t.mem = (s.mem.writeW (off (s.gpr .x2) (16 * i))
          (word s.mem p (2 * i) ^^^ s.mem.readW (off p (16 * i)) 64)).writeW
        (off (s.gpr .x2) (16 * i + 8))
          (word s.mem p (2 * i + 1) ^^^ s.mem.readW (off p (16 * i + 8)) 64) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r1 := hs.read (d := 16 * i) (n := 16) (by omega_arith)
  have r2 := hs.read (d := 1024 + 16 * i) (n := 16) (by omega_arith)
  have e1 : (16 * i) % 16 = 0 ∧ 16 * i < 65536 := by omega_arith
  have e2 : (1024 + 16 * i) % 16 = 0 ∧ 1024 + 16 * i < 65536 := by omega_arith
  simp only [off] at r1 r2 hout
  rw [finishPair]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e2 (by rw [← hs.reg] at r2; exact r2), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e1 (by rw [← hs.reg] at r1; exact r1), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_eor_v, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq_write e1 hout, ?_⟩
  refine WP.block_nil ⟨?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_setV_self,
    RegUpd.v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), hs.reg,
    ofVDwords_xor, write16_dwords, Offset.add_add, off, word,
    show 1024 + 8 * (2 * i) = 1024 + 16 * i by omega_arith,
    show 1024 + 8 * (2 * i + 1) = 1024 + 16 * i + 8 by omega_arith]

end VG.Proof.Argon2.AArch64
end

/-! # Copy X XOR Y into both scratch blocks -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

theorem blockAt_get (m : Mem) (p : Addr) (i : Fin 128) :
    (blockAt m p)[i] = m.readW (off p (8 * i.val)) 64 := by
  simp only [blockAt, Fin.getElem_fin, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

/-- Copying loops change only x8, x9, and memory. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.refl (s : State) : CopyKeeps s s := ⟨fun _ _ _ => rfl, rfl, rfl⟩

theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (h' : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r hr hr9 => (h'.1 r hr hr9).trans (h.1 r hr hr9), h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_copy {s t : State} {p : Addr} (hs : Scratch s p) (h : CopyKeeps s t) :
    Scratch t p := ⟨(h.1 .x3 (by decide) (by decide)).trans hs.reg, h.2.2 ▸ hs.wr⟩

structure Inputs (s : State) (x y p : Addr) : Prop where
  xreg : s.gpr .x0 = x
  yreg : s.gpr .x1 = y
  xread : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr
  yread : (⟨y, 1024⟩ : Region) ∈ s.rd ++ s.wr
  xsep : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  ysep : (⟨y, 1024⟩ : Region).Disjoint ⟨p, 4096⟩

theorem Inputs.of_copy {s t : State} {x y p : Addr} (h : Inputs s x y p) (hk : CopyKeeps s t) :
    Inputs t x y p := ⟨(hk.1 .x0 (by decide) (by decide)).trans h.xreg,
      (hk.1 .x1 (by decide) (by decide)).trans h.yreg, by simpa only [hk.2.1, hk.2.2] using h.xread,
      by simpa only [hk.2.1, hk.2.2] using h.yread, h.xsep, h.ysep⟩

theorem input_read {s : State} {x : Addr} (h : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (i : Fin 128) : InRegions (s.rd ++ s.wr) (off x (8 * i.val)) 8 :=
  ⟨_, h, Offset.contains_base x (by omega_arith) (by omega_arith)⟩

theorem input_unchanged {m m' : Mem} {x p : Addr} (hf : Frame [⟨p, 4096⟩] m m')
    (hd : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩) (i : Fin 128) :
    m'.readW (off x (8 * i.val)) 64 = m.readW (off x (8 * i.val)) 64 :=
  hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega_arith) (by omega_arith))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- A prefix of the two scratch copies is initialized. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n →
    m.readW (off p (8 * i.val)) 64 = r[i] ∧ word m p i.val = r[i]

theorem init_store_frame (m : Mem) (p : Addr) (n : Nat) (hn : n < 64) (a b : Word) :
    Frame [⟨p, 4096⟩] m
      ((((m.writeW (off p (16 * n)) a).writeW (off p (16 * n + 8)) b).writeW
        (off p (1024 + 16 * n)) a).writeW (off p (1024 + 16 * n + 8)) b) :=
  ((((Frame.refl [⟨p, 4096⟩] m).writeW (r := ⟨p, 4096⟩) (by simp) a
    (Offset.contains_base p (by omega_arith) (by omega_arith))).writeW (r := ⟨p, 4096⟩) (by simp) b
    (Offset.contains_base p (by omega_arith) (by omega_arith))).writeW (r := ⟨p, 4096⟩) (by simp) a
    (Offset.contains_base p (by omega_arith) (by omega_arith))).writeW (r := ⟨p, 4096⟩) (by simp) b
    (Offset.contains_base p (by omega_arith) (by omega_arith))

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat}
    (hn : n < 64) (h : Initialized m p r (2 * n)) :
    Initialized ((((m.writeW (off p (16 * n)) r[2 * n]).writeW (off p (16 * n + 8)) r[2 * n + 1]).writeW
      (off p (1024 + 16 * n)) r[2 * n]).writeW (off p (1024 + 16 * n + 8)) r[2 * n + 1])
      p r (2 * n + 2) := by
  intro i hi
  have rd (d : Nat) (hd : d + 8 ≤ 2048)
      (h1 : d + 8 ≤ 16 * n ∨ 16 * n + 8 ≤ d) (h2 : d + 8 ≤ 16 * n + 8 ∨ 16 * n + 16 ≤ d)
      (h3 : d + 8 ≤ 1024 + 16 * n ∨ 1024 + 16 * n + 8 ≤ d)
      (h4 : d + 8 ≤ 1024 + 16 * n + 8 ∨ 1024 + 16 * n + 16 ≤ d) :
      ((((m.writeW (off p (16 * n)) r[2 * n]).writeW (off p (16 * n + 8)) r[2 * n + 1]).writeW
        (off p (1024 + 16 * n)) r[2 * n]).writeW (off p (1024 + 16 * n + 8)) r[2 * n + 1]).readW
        (off p d) 64 = m.readW (off p d) 64 := by
    rw [Mem.readW_writeW_sep (Offset.sep p h4 (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p h3 (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p h2 (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p h1 (by omega_arith) (by omega_arith)) (by decide)]
  have top (d : Nat) {m' : Mem} {a : Addr} {w : Word}
      (hs : Mem.Sep (off p d) 8 a 8) : (m'.writeW a w).readW (off p d) 64 = m'.readW (off p d) 64 :=
    Mem.readW_writeW_sep hs (by decide)
  simp only [word]
  obtain ⟨k, hk⟩ := i
  simp only at hi
  rcases (by omega_arith : k = 2 * n ∨ k = 2 * n + 1 ∨ k < 2 * n) with he | he | he
  · subst he
    simp only [show 8 * (2 * n) = 16 * n by omega_arith]
    refine ⟨?_, ?_⟩
    · rw [top _ (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)),
        top _ (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)),
        top _ (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)),
        Mem.readW_writeW_self64]
      rfl
    · rw [top _ (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)),
        Mem.readW_writeW_self64]
      rfl
  · subst he
    simp only [show 8 * (2 * n + 1) = 16 * n + 8 by omega_arith,
      show 1024 + (16 * n + 8) = 1024 + 16 * n + 8 by omega_arith]
    refine ⟨?_, ?_⟩
    · rw [top _ (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)),
        top _ (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)),
        Mem.readW_writeW_self64]
      rfl
    · rw [Mem.readW_writeW_self64]
      rfl
  · rw [rd (8 * k) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      rd (1024 + 8 * k) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
    exact h ⟨k, hk⟩ he

theorem xorBlock_get (a b : Block) (i : Fin 128) :
    (xorBlock a b)[i] = a[i] ^^^ b[i] := by
  simp only [xorBlock, Fin.getElem_fin, Vector.getElem_zipWith]

/-- Initialize an arbitrary prefix of pairs, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 64) (s : State) {x y p : Addr}
    (hs : Scratch s p) (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap Impl.Argon2.AArch64.initPair)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) (2 * n) ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 64 := by omega_arith
    have htIn := hin.of_copy hk
    have lx : InRegions (t.rd ++ t.wr) (off (t.gpr .x0) (16 * n)) 16 := by
      rw [htIn.xreg]
      exact ⟨_, htIn.xread, Offset.contains_base x (by omega_arith) (by omega_arith)⟩
    have ly : InRegions (t.rd ++ t.wr) (off (t.gpr .x1) (16 * n)) 16 := by
      rw [htIn.yreg]
      exact ⟨_, htIn.yread, Offset.contains_base y (by omega_arith) (by omega_arith)⟩
    refine (initPair_ok t (hs.of_copy hk) n hn' lx ly).mono ?_
    rintro u ⟨hm, hreg, hr, hw⟩
    have hv (k : Nat) (hk : k < 128) (d : Nat) (hd : d = 8 * k) :
        t.mem.readW (off x d) 64 ^^^ t.mem.readW (off y d) 64 =
          (xorBlock (blockAt s.mem x) (blockAt s.mem y))[k] := by
      subst hd
      rw [show (xorBlock (blockAt s.mem x) (blockAt s.mem y))[k] =
          (xorBlock (blockAt s.mem x) (blockAt s.mem y))[(⟨k, hk⟩ : Fin 128)] from rfl,
        xorBlock_get, blockAt_get, blockAt_get,
        input_unchanged hf hin.xsep ⟨k, hk⟩, input_unchanged hf hin.ysep ⟨k, hk⟩]
    refine ⟨?_, ?_, hk.trans ⟨fun r _ _ => congrFun hreg r, hr, hw⟩⟩
    · rw [hm, htIn.xreg, htIn.yreg, hv (2 * n) (by omega_arith) (16 * n) (by omega_arith),
        hv (2 * n + 1) (by omega_arith) (16 * n + 8) (by omega_arith),
        show 2 * (n + 1) = 2 * n + 2 by omega_arith]
      exact initialized_step hn' ht
    · rw [hm]
      exact hf.trans (init_store_frame t.mem p n hn' _ _)

/-- The initialized copies both contain X XOR Y. -/
theorem initialized_blocks {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r (2 * 64)) :
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

end VG.Proof.Argon2.AArch64
