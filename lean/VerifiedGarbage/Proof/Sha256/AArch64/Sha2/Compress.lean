module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Spec
meta import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Spec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Lit
meta import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Lit
public import VerifiedGarbage.Proof.Sha256.AArch64.Compress
meta import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.MdStream.AArch64
meta import VerifiedGarbage.Impl.MdStream.AArch64
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! Correctness of SHA-256 compression with the AArch64 SHA-2 instructions. -/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Sha2

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Sha2
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks)

def kQuad (n : Nat) : BitVec 128 := ofVWords (K (4 * n)) (K (4 * n + 1)) (K (4 * n + 2)) (K (4 * n + 3))

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .v0, .v1, .v2, .v3, .v16, .v17].Nodup := by
  have key : ∀ c < 4,
      [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .v0, .v1, .v2, .v3, .v16, .v17].Nodup := by decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem exec_vop (s : State) (op : VOp) :
    exec (.vop op) s = (VOp.eval s op).map (fun p => s.setV p.1 p.2) := rfl

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.load,
    h, Option.bind_some, Option.map_some]

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.store,
    h, Option.bind_some]

theorem setLane_three_hi (a b c d : BitVec 32) :
    setLane (setLane (setLane (ofVWords a a a a) 32 1 b) 32 2 c) 32 3 d = ofVWords a b c d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [setLane, ofVWords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.reduceMul]
  by_cases h0 : j < 32
  · simp (disch := omega) [h0, decide_eq_true]
  by_cases h1 : j < 64
  · simp (disch := omega) [h0, h1, decide_eq_true, show j - 32 < 32 by omega]
  by_cases h2 : j < 96
  · simp (disch := omega) [h0, h1, h2, decide_eq_true,
      show ¬ j - 32 < 32 by omega, show j - 32 - 32 = j - 64 by omega, show j - 64 < 32 by omega]
  · simp (disch := omega) [h0, h1, h2, decide_eq_true, decide_eq_false,
      show ¬ j - 32 < 32 by omega, show ¬ j - 32 - 32 < 32 by omega,
      show j - 32 - 32 - 32 = j - 96 by omega]

theorem kreg_inj : ∀ i < 16, ∀ j < 16, kreg i = kreg j → i = j := by decide

/-- The registers that are never a constant register. -/
theorem kreg_ne : ∀ i < 16, ∀ r ∈ [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7], kreg i ≠ r := by decide

theorem writeW64 (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = m.write a 8 v := by
  simp only [Mem.writeW]
  rfl

theorem lo_append (a b : BitVec 32) : (b ++ a).extractLsb' 0 32 = a := by
  ext i hi
  rw [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [hi, BitVec.getLsbD_eq_getElem]

theorem hi_append (a b : BitVec 32) : (b ++ a).extractLsb' 32 32 = b := by
  ext i hi
  rw [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [hi, BitVec.getLsbD_eq_getElem]

/-- Group `k`'s constants, stored as `kWord k 0` and `kWord k 1` at `a` and
`a + 8`, read back as one vector. -/
theorem read_slot (m : Mem) (a : Addr) (k : Nat) :
    ((m.writeW a (kWord k 0)).writeW (a + BitVec.ofNat 64 8) (kWord k 1)).read a 16 = kQuad k := by
  rw [read16]
  have r0 : ((m.writeW a (kWord k 0)).writeW (a + BitVec.ofNat 64 8) (kWord k 1)).readW
      (a + BitVec.ofNat 64 (4 * 0)) 32 = K (4 * k) := by
    rw [Mem.readW_writeW_sep (Offset.sep a (by omega) (by omega) (by omega)) (by decide),
      show a + BitVec.ofNat 64 (4 * 0) = a by simp, ← readW64_lo, Mem.readW_writeW_self64, kWord,
      lo_append]
    rfl
  have r1 : ((m.writeW a (kWord k 0)).writeW (a + BitVec.ofNat 64 8) (kWord k 1)).readW
      (a + BitVec.ofNat 64 (4 * 1)) 32 = K (4 * k + 1) := by
    rw [Mem.readW_writeW_sep (Offset.sep a (by omega) (by omega) (by omega)) (by decide),
      ← readW64_hi, Mem.readW_writeW_self64, kWord, hi_append]
  have r2 : ((m.writeW a (kWord k 0)).writeW (a + BitVec.ofNat 64 8) (kWord k 1)).readW
      (a + BitVec.ofNat 64 (4 * 2)) 32 = K (4 * k + 2) := by
    rw [show a + BitVec.ofNat 64 (4 * 2) = a + BitVec.ofNat 64 8 from rfl, ← readW64_lo,
      Mem.readW_writeW_self64, kWord, lo_append]
  have r3 : ((m.writeW a (kWord k 0)).writeW (a + BitVec.ofNat 64 8) (kWord k 1)).readW
      (a + BitVec.ofNat 64 (4 * 3)) 32 = K (4 * k + 3) := by
    rw [show a + BitVec.ofNat 64 (4 * 3) = a + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 from
      (Offset.add_add _ _ _).symm, ← readW64_hi, Mem.readW_writeW_self64, kWord, hi_append]
  rw [r0, r1, r2, r3]
  rfl

/-- `movz_movk64'` with its shift amounts reduced, as `simp` leaves them. -/
theorem movz_movk64r (x : BitVec 64) :
    (((x.extractLsb' 0 16).setWidth 64 <<< 0 &&& ~~~((65535 : BitVec 64) <<< 16) |||
      (x.extractLsb' 16 16).setWidth 64 <<< 16) &&& ~~~((65535 : BitVec 64) <<< 32) |||
      (x.extractLsb' 32 16).setWidth 64 <<< 32) &&& ~~~((65535 : BitVec 64) <<< 48) |||
      (x.extractLsb' 48 16).setWidth 64 <<< 48 = x := movz_movk64' x

theorem build_ok (k : Nat) (s : State)
    (h1 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (slot k)) 8)
    (h2 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (slot k + 8)) 8) :
    WP isa (.block (build k)) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 (slot k)) (kWord k 0)).writeW
        (s.gpr .x3 + BitVec.ofNat 64 (slot k + 8)) (kWord k 1) ∧
      s'.v = s.v ∧ (∀ r, r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs : slot k % 8 = 0 ∧ slot k ≤ 504 := by simp only [slot]; omega
  have ha : s.gpr .x3 + BitVec.ofNat 64 (slot k) + 8 = s.gpr .x3 + BitVec.ofNat 64 (slot k + 8) :=
    Offset.add_add _ _ _
  apply WP.of_runBlock
  simp only [build, runBlock_cons, runStep_some, runBlock_nil, exec, reduceCtorEq, ↓reduceIte,
    Nat.reduceMul, Nat.reduceLT, ne_eq, not_false_eq_true, State.store, Option.bind_some, and_self, isa, State.read, Size.bits,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.v_write, BitVec.setWidth_eq, movz_movk64r,
    hs.1, hs.2, ha, h1, h2, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [writeW64, writeW64], trivial, fun r h4 h5 => ?_, trivial⟩
  simp only [RegUpd.gpr_write_of_ne, h4, h5, not_false_eq_true]

/-- The groups whose constants wait in their slots, at `p`: those from `n` to
`n + 1`. -/
def Slots (m : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ k, n ≤ k → k < n + 2 → k < 16 → m.read (p + BitVec.ofNat 64 (slot k)) 16 = kQuad k

/-- The first 64 bytes of scratch, the four slots. -/
abbrev slotsR (p : Addr) : Region := ⟨p, 112⟩

theorem slot_lt (k : Nat) : slot k + 16 ≤ 64 := by simp only [slot]; omega

/-- The two stores of group `k`'s constants. -/
abbrev buildMem (m : Mem) (p : Addr) (k : Nat) : Mem :=
  (m.writeW (p + BitVec.ofNat 64 (slot k)) (kWord k 0)).writeW (p + BitVec.ofNat 64 (slot k + 8)) (kWord k 1)

/-- Storing group `k`'s constants keeps a slot of another residue. -/
theorem buildMem_keep (m : Mem) (p : Addr) {j k : Nat} (hjk : j % 4 ≠ k % 4) :
    (buildMem m p k).read (p + BitVec.ofNat 64 (slot j)) 16 = m.read (p + BitVec.ofNat 64 (slot j)) 16 := by
  have e : ∀ (m' : Mem) (d : Nat) (v : BitVec 64), d + 8 ≤ 64 → (slot j + 16 ≤ d ∨ d + 8 ≤ slot j) →
      (m'.writeW (p + BitVec.ofNat 64 d) v).read (p + BitVec.ofNat 64 (slot j)) 16 =
        m'.read (p + BitVec.ofNat 64 (slot j)) 16 := fun m' d v hd hs => by
    have := slot_lt j
    rw [writeW64]
    exact Mem.read_write_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)
  have := slot_lt k
  have hne : slot j + 16 ≤ slot k ∨ slot k + 16 ≤ slot j := by simp only [slot]; omega
  rw [buildMem, e _ _ _ (by omega) (by omega), e _ _ _ (by omega) (by omega)]

/-- Storing group `k`'s constants puts them in its slot. -/
theorem buildMem_read (m : Mem) (p : Addr) (k : Nat) :
    (buildMem m p k).read (p + BitVec.ofNat 64 (slot k)) 16 = kQuad k := by
  rw [buildMem, show p + BitVec.ofNat 64 (slot k + 8) = p + BitVec.ofNat 64 (slot k) + BitVec.ofNat 64 8 from
    (Offset.add_add _ _ _).symm]
  exact read_slot _ _ _

/-- The two stores are within the slots. -/
theorem buildMem_frame (m : Mem) (p : Addr) (k : Nat) : Frame [slotsR p] m (buildMem m p k) := by
  have := slot_lt k
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by omega) (by omega))

theorem exec_ldrq' {s : State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.load,
    h, Option.bind_some, Option.map_some]

/-- Building group `n + 2` (if any) and loading group `n`, in the first block. -/
theorem kbuild_ok (n : Nat) (hn : n < 16) (s : State) (p : Addr) (hx3 : s.gpr .x3 = p)
    (hw : ∀ d, d + 8 ≤ 64 → InRegions s.wr (p + BitVec.ofNat 64 d) 8)
    (hr : ∀ k, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (slot k)) 16)
    (hs : Slots s.mem p n) :
    WP isa (.block (kbuild n)) s fun s' =>
      s'.v (kreg n) = kQuad n ∧
      (∀ r, r ≠ kreg n → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      Frame [slotsR p] s.mem s'.mem ∧ Slots s'.mem p (n + 1) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [kbuild, WP.block_append_iff]
  have hpart : WP isa (.block (if n + 2 < 16 then build (n + 2) else [])) s fun s₁ =>
      s₁.v = s.v ∧ (∀ r, r ≠ .x4 → r ≠ .x5 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      Frame [slotsR p] s.mem s₁.mem ∧ Slots s₁.mem p n ∧
      (n + 2 < 16 → s₁.mem.read (p + BitVec.ofNat 64 (slot (n + 2))) 16 = kQuad (n + 2)) := by
    by_cases h2 : n + 2 < 16
    · simp only [h2, ite_true]
      have := slot_lt (n + 2)
      refine (build_ok (n + 2) s (by rw [hx3]; exact hw _ (by omega))
        (by rw [hx3]; exact hw _ (by omega))).mono fun s₁ ⟨hm, hv, hg, hrd, hwr⟩ => ?_
      rw [hx3] at hm
      refine ⟨hv, hg, hrd, hwr, by rw [hm]; exact buildMem_frame _ _ _,
        fun j hj hj' hj16 => ?_, fun _ => by rw [hm]; exact buildMem_read _ _ _⟩
      rw [hm, buildMem_keep _ _ (by omega)]
      exact hs j hj hj' hj16
    · simp only [h2, ite_false]
      exact WP.block_nil (M := isa) ⟨rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, hs,
        fun h => absurd (by simp at h) h2⟩
  refine WP.mono hpart fun s₁ ⟨hv, hg, hrd, hwr, hf, hs₁, hk₂⟩ => ?_
  have ho : slot n % 16 = 0 ∧ slot n < 65536 := by simp only [slot]; omega
  have hx3' : s₁.gpr .x3 = p := by rw [hg .x3 (by decide) (by decide), hx3]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq' ho (by rw [hx3', hrd, hwr]; exact hr n),
    WP.block_nil (M := isa) ⟨?_, fun r hr' => ?_, fun r h4 h5 => ?_, hf, ?_, hrd, hwr⟩⟩
  · rw [RegUpd.v_setV_self, hx3']; exact hs₁ n (Nat.le_refl _) (by omega) hn
  · rw [RegUpd.v_setV_of_ne _ _ hr', hv]
  · rw [RegUpd.gpr_setV, hg r h4 h5]
  · intro k hk hk' hk16
    rw [RegUpd.mem_setV]
    by_cases e : k = n + 2
    · subst e; exact hk₂ hk16
    · exact hs₁ k (by omega) (by omega) hk16

theorem rounds4_ok (n : Nat) (s : State) (v : HashValue) (q : BitVec 128)
    (h0 : s.v .v0 = abcd v) (h1 : s.v .v1 = efgh v) (hq : s.v (msg n) = q)
    (hk : s.v (kreg n) = kQuad n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.v .v0 = sha256Hash (abcd v) (efgh v) (VArr.s4.map2 (fun _ x y => x + y) (kQuad n) q) true ∧
      s'.v .v1 = sha256Hash (abcd v) (efgh v) (VArr.s4.map2 (fun _ x y => x + y) (kQuad n) q) false ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [rounds4]
  generalize msg n = x at *
  generalize kreg n = y at *
  simp only [reduceCtorEq, ↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil,
    exec_vop, VOp.eval, isa, RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, Option.map_some,
    h0, h1, hq, hk, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h0 h1 h2 h3 => ?_, trivial⟩
  simp only [h0, h1, h2, h3, ite_false]

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a b c d : BitVec 128)
    (ha : s.v (msg n) = a) (hb : s.v (msg (n + 1)) = b) (hc : s.v (msg (n + 2)) = c)
    (hd' : s.v (msg (n + 3)) = d) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.v (msg n) = sha256Su1 (sha256Su0 a b) c d ∧
      (∀ r, r ≠ msg n → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd'' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, show ¬ n < 4 by omega, ite_false]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 2) = x₂ at *
  generalize msg (n + 3) = x₃ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd''
  simp only [↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval,
    isa, RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, hd'', ha, hb, hc, hd',
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial⟩

theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.v (msg n) = VRevOp.rev32b.eval (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16) ∧
      (∀ r, r ≠ msg n → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [schedule, hn, ite_true]
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval,
    isa, exec_ldrq, show 16 * n % 16 = 0 by omega, show 16 * n < 65536 by omega,
    and_self, hin, Option.map_some,
    RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial⟩

theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1

theorem msg_other (n : Nat) (r : VReg)
    (h : r = .v0 ∨ r = .v1 ∨ r = .v2 ∨ r = .v3) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [VReg.v0, .v1, .v2, .v3], msg c ≠ r := by decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

theorem msg_kreg (n : Nat) {j : Nat} (hj : j < 16) : msg n ≠ kreg j := by
  have key : ∀ c < 4, ∀ j < 16, msg c ≠ kreg j := by decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) j hj

structure RInv (c : Bool) (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  v0 : s.v .v0 = abcd (Spec.Sha256.rounds H M (4 * n))
  v1 : s.v .v1 = efgh (Spec.Sha256.rounds H M (4 * n))
  msgs : ∀ k < n, n ≤ k + 4 → s.v (msg k) = quad M k
  k : ∀ j < 16, (c = false ∨ j < n) → s.v (kreg j) = kQuad j
  gpr : ∀ r, r ≠ .x4 → r ≠ .x5 → s.gpr r = sB.gpr r
  frame : Frame [slotsR (sB.gpr .x3)] sB.mem s.mem
  same : c = false → s.mem = sB.mem
  slots : c = true → Slots s.mem (sB.gpr .x3) n
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_four (H : HashValue) (M : Block) (n : Nat) :
    Spec.Sha256.rounds H M (4 * (n + 1)) =
      roundKW (roundKW (roundKW (roundKW (Spec.Sha256.rounds H M (4 * n)) (K (4 * n)) (W M (4 * n)))
        (K (4 * n + 1)) (W M (4 * n + 1))) (K (4 * n + 2)) (W M (4 * n + 2)))
        (K (4 * n + 3)) (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rounds_succ, rounds_succ, rounds_succ, rounds_succ]
  rfl

theorem kq_quad (n : Nat) (M : Block) {j : Nat} (hj : j < 4) :
    vword (VArr.s4.map2 (fun _ x y => x + y) (kQuad n) (quad M n)) j =
      K (4 * n + j) + W M (4 * n + j) := by
  rw [vword_map2 _ _ _ hj]
  simp only [kQuad, quad, vword_ofVWords _ _ _ _ hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem rounds4_step (H : HashValue) (M : Block) (n : Nat) (s : State)
    (h0 : s.v .v0 = abcd (Spec.Sha256.rounds H M (4 * n)))
    (h1 : s.v .v1 = efgh (Spec.Sha256.rounds H M (4 * n))) (hq : s.v (msg n) = quad M n)
    (hk : s.v (kreg n) = kQuad n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.v .v0 = abcd (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      s'.v .v1 = efgh (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ h0 h1 hq hk) fun s' ⟨e0, e1, hv, hg, hm, hrd, hwr⟩ => ?_
  have h := hash_eq (Spec.Sha256.rounds H M (4 * n)) _
    (K (4 * n)) (W M (4 * n)) (K (4 * n + 1)) (W M (4 * n + 1))
    (K (4 * n + 2)) (W M (4 * n + 2)) (K (4 * n + 3)) (W M (4 * n + 3))
    (kq_quad n M (by decide)) (kq_quad n M (by decide)) (kq_quad n M (by decide)) (kq_quad n M (by decide))
  rw [h true] at e0
  rw [h false] at e1
  exact ⟨by rw [rounds_four]; exact e0, by rw [rounds_four]; exact e1, hv, hg, hm, hrd, hwr⟩

theorem load_quad (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t) :
    VRevOp.rev32b.eval (m.read (bp + BitVec.ofNat 64 (16 * n)) 16) = quad M n := by
  apply vec_ext
  intro j hj
  rw [vword_rev32b _ hj, vword_read16 _ _ hj,
    Offset.add_add_eq _ (show 16 * n + 4 * j = 4 * (4 * n + j) by omega), hblk _ (by omega)]
  simp only [quad, vword_ofVWords _ _ _ _ hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem rounds_ok (c : Bool) (H : HashValue) (M : Block) (bp : Addr) (sB : State)
    (hrsi : sB.gpr .x1 = bp)
    (hin : ∀ n : Nat, n < 4 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (16 * n)) 16)
    (R : Region) (hR : ∀ n : Nat, n < 4 → R.Contains (bp + BitVec.ofNat 64 (16 * n)) 16)
    (hRd : R.Disjoint (slotsR (sB.gpr .x3)))
    (hblk : ∀ t : Nat, t < 16 →
      rev32 (sB.mem.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (hw : ∀ d, d + 8 ≤ 64 → InRegions sB.wr (sB.gpr .x3 + BitVec.ofNat 64 d) 8)
    (hr : ∀ k, InRegions (sB.rd ++ sB.wr) (sB.gpr .x3 + BitVec.ofNat 64 (slot k)) 16)
    (h1 : sB.v .v0 = abcd H) (h2 : sB.v .v1 = efgh H)
    (hk : c = false → ∀ j < 16, sB.v (kreg j) = kQuad j) :
    ∀ n ≤ 16, WP isa (rounds c n) sB (RInv c H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    cases c with
    | false =>
      exact WP.block_nil (M := isa) ⟨h1, h2, fun _ h => absurd h (by omega),
        fun j hj _ => hk rfl j hj, fun _ _ _ => rfl, Frame.refl _ _, fun _ => rfl,
        fun h => absurd h (by decide), rfl, rfl⟩
    | true =>
      simp only [rounds, ite_true]
      rw [WP.block_append_iff]
      have := slot_lt 0
      have := slot_lt 1
      refine (build_ok 0 sB (hw _ (by omega)) (hw _ (by omega))).mono
        fun s₁ ⟨hm₁, hv₁, hg₁, hrd₁, hwr₁⟩ => ?_
      have hx3 : s₁.gpr .x3 = sB.gpr .x3 := hg₁ .x3 (by decide) (by decide)
      refine (build_ok 1 s₁ (by rw [hx3, hwr₁]; exact hw _ (by omega))
        (by rw [hx3, hwr₁]; exact hw _ (by omega))).mono fun s₂ ⟨hm₂, hv₂, hg₂, hrd₂, hwr₂⟩ => ?_
      rw [hx3] at hm₂
      refine ⟨by rw [hv₂, hv₁]; exact h1, by rw [hv₂, hv₁]; exact h2, fun _ h => absurd h (by omega),
        fun _ _ h => h.elim (fun h => absurd h (by decide)) (fun h => absurd h (by omega)),
        fun r h4 h5 => by rw [hg₂ r h4 h5, hg₁ r h4 h5],
        by rw [hm₂, hm₁]; exact (buildMem_frame _ _ 0).trans (buildMem_frame _ _ 1),
        fun h => absurd h (by decide), fun _ k hk hk' _ => ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
      rw [hm₂, hm₁]
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [buildMem_keep _ _ (by decide)]; exact buildMem_read _ _ _
      · exact buildMem_read _ _ _
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [group, WP.block_append_iff]
    have hs_rsi : s.gpr .x1 = bp := (hs.gpr .x1 (by decide) (by decide)).trans hrsi
    have hs_x3 : s.gpr .x3 = sB.gpr .x3 := hs.gpr .x3 (by decide) (by decide)
    -- The schedule replaces `msg n` with `quad M n`, preserving the other registers.
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.v (msg n) = quad M n ∧ (∀ r, r ≠ msg n → s₁.v r = s.v r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_rsi]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        rw [e, hs_rsi, hs.frame.read (hR n hlo) (by simpa using hRd) (by decide)]
        exact load_quad M sB.mem bp hlo hblk
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
        refine WP.mono (schedule_hi (i + 4) (by omega) s (quad M i) (quad M (i + 1)) (quad M (i + 2))
          (quad M (i + 3)) ?_ ?_ ?_ ?_) fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        · rw [msg_add4]; exact hs.msgs i (by omega) (by omega)
        · rw [show i + 4 + 1 = i + 1 + 4 by omega, msg_add4]; exact hs.msgs (i + 1) (by omega) (by omega)
        · rw [show i + 4 + 2 = i + 2 + 4 by omega, msg_add4]; exact hs.msgs (i + 2) (by omega) (by omega)
        · rw [show i + 4 + 3 = i + 3 + 4 by omega, msg_add4]; exact hs.msgs (i + 3) (by omega) (by omega)
        · rw [e]; exact schedule_eq M i
    refine WP.mono hsched fun s₁ ⟨hq, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    rw [WP.block_append_iff]
    have hn16 : n < 16 := by omega
    -- The constants: loaded by the first block (building those two groups ahead), kept by the others.
    have hmid : WP isa (.block (if c then kbuild n else [])) s₁ fun s₁' =>
        s₁'.v (kreg n) = kQuad n ∧ (∀ r, r ≠ kreg n → s₁'.v r = s₁.v r) ∧
        (∀ r, r ≠ .x4 → r ≠ .x5 → s₁'.gpr r = s₁.gpr r) ∧
        Frame [slotsR (sB.gpr .x3)] s₁.mem s₁'.mem ∧ (c = false → s₁'.mem = s₁.mem) ∧
        (c = true → Slots s₁'.mem (sB.gpr .x3) (n + 1)) ∧ s₁'.rd = s₁.rd ∧ s₁'.wr = s₁.wr := by
      cases c with
      | true =>
        simp only [ite_true]
        refine (kbuild_ok n hn16 s₁ (sB.gpr .x3) (by rw [hg₁, hs_x3])
          (fun d hd => by rw [hwr₁, hs.wr]; exact hw d hd)
          (fun k => by rw [hrd₁, hwr₁, hs.rd, hs.wr]; exact hr k)
          (by rw [hm₁]; exact hs.slots rfl)).mono
          fun s' ⟨e, hv, hg, hf, hsl, hrd, hwr⟩ => ⟨e, hv, hg, hf, fun h => absurd h (by decide),
            fun _ => hsl, hrd, hwr⟩
      | false =>
        refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, fun _ _ _ => rfl, Frame.refl _ _,
          fun _ => rfl, fun h => absurd h (by decide), rfl, rfl⟩
        rw [hx₁ _ (Ne.symm (msg_kreg n hn16))]
        exact hs.k n hn16 (.inl rfl)
    refine WP.mono hmid fun s₁' ⟨hk₁, hx₁', hg₁', hf₁', hsame₁', hsl₁', hrd₁', hwr₁'⟩ => ?_
    have o1 := msg_other n .v0 (by simp)
    have o2 := msg_other n .v1 (by simp)
    have kn := kreg_ne n hn16
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at kn
    refine WP.mono (rounds4_step H M n s₁'
      (by rw [hx₁' _ (Ne.symm kn.1), hx₁ _ (Ne.symm o1)]; exact hs.v0)
      (by rw [hx₁' _ (Ne.symm kn.2.1), hx₁ _ (Ne.symm o2)]; exact hs.v1)
      (by rw [hx₁' _ (msg_kreg n hn16)]; exact hq) hk₁)
      fun s₂ ⟨e1, e2, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e1, e2, fun k hk hk' => ?_, fun j hj hcj => ?_, fun r h4 h5 => ?_,
      by rw [hm₂]; exact hs.frame.trans (by rw [← hm₁]; exact hf₁'),
      fun hc => by rw [hm₂, hsame₁' hc, hm₁, hs.same hc], fun hc => by rw [hm₂]; exact hsl₁' hc,
      by rw [hrd₂, hrd₁', hrd₁, hs.rd], by rw [hwr₂, hwr₁', hwr₁, hs.wr]⟩
    · have n0 := msg_other k .v2 (by simp)
      have n1 := msg_other k .v0 (by simp)
      have n2 := msg_other k .v1 (by simp)
      have n11 := msg_other k .v3 (by simp)
      rw [hx₂ _ n1 n2 n0 n11, hx₁' _ (msg_kreg k hn16)]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (msg_ne n k (by omega) (by omega))]
        exact hs.msgs k (by omega) (by omega)
    · have kj := kreg_ne j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at kj
      rw [hx₂ _ kj.1 kj.2.1 kj.2.2.1 kj.2.2.2.1]
      by_cases hjn : j = n
      · subst hjn; exact hk₁
      · rw [hx₁' _ (fun h => hjn (kreg_inj j hj n hn16 h)), hx₁ _ (Ne.symm (msg_kreg n hj))]
        exact hs.k j hj (hcj.imp_right fun h => by omega)
    · rw [hg₂, hg₁' r h4 h5, hg₁, hs.gpr r h4 h5]

theorem read_abcd (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 0) 16 = abcd (stateAt m p) := by
  rw [read16]
  simp only [abcd, stateAt_get _ _ (by decide : 0 < 8), stateAt_get _ _ (by decide : 1 < 8),
    stateAt_get _ _ (by decide : 2 < 8), stateAt_get _ _ (by decide : 3 < 8),
    BitVec.add_zero]

theorem read_efgh (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 16) 16 = efgh (stateAt m p) := by
  rw [read16]
  simp only [efgh, stateAt_get _ _ (by decide : 4 < 8), stateAt_get _ _ (by decide : 5 < 8),
    stateAt_get _ _ (by decide : 6 < 8), stateAt_get _ _ (by decide : 7 < 8),
    Offset.add_add, Nat.reduceMul, Nat.reduceAdd]

theorem write_pair (m : Mem) (p : Addr) (v : HashValue) :
    (m.write (p + BitVec.ofNat 64 0) 16 (abcd v)).write (p + BitVec.ofNat 64 16) 16 (efgh v) =
      writeState m p v := by
  simp only [abcd, efgh, write16, writeState, Offset.add_add, Nat.reduceMul, Nat.reduceAdd,
    BitVec.add_zero]

theorem load_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 0) 16)
    (h16 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 16) 16) :
    WP isa (.block load) s fun s' =>
      s'.v .v0 = abcd (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v1 = efgh (stateAt s.mem (s.gpr .x0)) ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul,
    load, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.load, Option.bind_some, and_self, isa, Option.map_some,
    RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    h0, h16, read_abcd, read_efgh, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h0 h1 => by simp only [h0, h1, ite_false], trivial⟩

theorem store_ok (s : State) (v H : HashValue)
    (hv0 : s.v .v0 = abcd v) (hv1 : s.v .v1 = efgh v)
    (hH : stateAt s.mem (s.gpr .x0) = H)
    (h0 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 0) 16)
    (h16 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 16) 16) :
    WP isa (.block store) s fun s' =>
      s'.v .v0 = abcd (Vector.zipWith (· + ·) v H) ∧ s'.v .v1 = efgh (Vector.zipWith (· + ·) v H) ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) ∧
      s'.mem = writeState s.mem (s.gpr .x0) (Vector.zipWith (· + ·) v H) ∧
      s'.gpr .x1 = s.gpr .x1 + 64 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 0) 16 := by
    obtain ⟨r, hr, hc⟩ := h0; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hr16 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 16) 16 := by
    obtain ⟨r, hr, hc⟩ := h16; exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul,
    store, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.load, State.store, VOp.eval, Option.bind_some, and_self,
    isa, State.read, Size.bits, Option.map_some, RegUpd.gpr_setV, RegUpd.v_setV,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.gpr_write_self,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write,
    hr0, hr16, h0, h16, read_abcd, read_efgh, hH, hv0, hv1, add_abcd, add_efgh, write_pair,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h0 h1 h2 h3 => by simp only [h0, h1, h2, h3, ite_false], trivial,
    rfl, rfl, fun r h1 h2 => by simp only [RegUpd.gpr_write_of_ne, h1, h2, not_false_eq_true],
    trivial⟩

theorem Pre.in_blk16 {s₀ : State} (hp : AArch64.Pre s₀) {i n : Nat}
    (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * n)) 16 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 16 * n) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

/-- The loop invariant with the state the blocks carry in `v0` and `v1`. -/
structure VInv (s₀ : State) (i : Nat) (s : State) : Prop extends LInv s₀ i s where
  v0 : s.v .v0 = abcd (stateAt s.mem (st s₀))
  v1 : s.v .v1 = efgh (stateAt s.mem (st s₀))

/-- One block, building the constants (`c`) or finding them in their registers. -/
theorem block_ok (c : Bool) {s₀ : State} (hp : AArch64.Pre s₀) {i : Nat} (hi : i < nb s₀)
    {s : State} (hL : VInv s₀ i s) (hk : c = false → ∀ j < 16, s.v (kreg j) = kQuad j) :
    WP isa (oneBlock c) s fun s' => VInv s₀ (i + 1) s' ∧ ∀ j < 16, s'.v (kreg j) = kQuad j := by
  have hblk : ∀ t : Nat, t < 16 →
      rev32 (s.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
    intro t ht
    rw [hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hx3 : s.gpr .x3 = scr s₀ := hL.x3
  have hlt := hp.nb_lt
  refine WP.seq ((rounds_ok c _ (blk s₀ i) (blkAddr s₀ i) s hL.x1
    (fun n hn => by rw [hL.rd, hL.wr]; exact Pre.in_blk16 hp hi hn)
    (blR s₀) (fun n hn => by
      rw [show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
        bp s₀ + BitVec.ofNat 64 (64 * i + 16 * n) from Offset.add_add _ _ _]
      exact contains_offset (by omega) (by omega))
    (by rw [hx3]; exact hp.blk_scr)
    hblk
    (fun d hd => ⟨scrR s₀, by simp [hL.wr, hp.wr], by rw [hx3]; exact contains_offset (by omega) (by omega)⟩)
    (fun k => ⟨scrR s₀, by simp [hL.wr, hp.wr], by
      have := slot_lt k
      rw [hx3]; exact contains_offset (by omega) (by omega)⟩)
    hL.v0 hL.v1 hk 16 (Nat.le_refl _)).mono fun s₂ hR => ?_)
  have hg₂ : ∀ r, r ≠ .x4 → r ≠ .x5 → s₂.gpr r = s.gpr r := fun r h4 h5 => hR.gpr r h4 h5
  have hf₂ : Frame [scrR s₀] s.mem s₂.mem := by
    have := hR.frame; rw [hx3] at this; exact this
  have hout : ∀ d, d ≤ 16 → InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 d) 16 := by
    intro d hd
    refine ⟨stR s₀, by simp [hR.wr, hL.wr, hp.wr], ?_⟩
    rw [hg₂ .x0 (by decide) (by decide), hL.x0]; exact contains_offset (by omega) (by omega)
  have hst₂ : stateAt s₂.mem (st s₀) = stateAt s.mem (st s₀) :=
    VG.Proof.Sha256.Stream.stateAt_congr fun j hj =>
      hf₂.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hj
  refine (store_ok s₂ _ (stateAt s.mem (st s₀)) hR.v0 hR.v1
    (by rw [hg₂ .x0 (by decide) (by decide), hL.x0, hst₂])
    (hout 0 (by decide)) (hout 16 (by decide))).mono
    fun s₃ ⟨hv0₃, hv1₃, hv₃, hm₃, hx1₃, hx2₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hg₂ .x2 (by decide) (by decide), hL.x2]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hst : stateAt s₃.mem (st s₀) = Vector.zipWith (· + ·) (Spec.Sha256.rounds (stateAt s.mem (st s₀))
      (blk s₀ i) (4 * 16)) (stateAt s.mem (st s₀)) := by
    rw [hm₃, hg₂ .x0 (by decide) (by decide), hL.x0, stateAt_writeState]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans (Frame.trans (hf₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩) ?_)
    rw [hm₃, hg₂ .x0 (by decide) (by decide), hL.x0]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  refine ⟨VInv.mk (LInv.mk (Common.mk ?_ ?_ ?_ (by rw [hrd₃, hR.rd, hL.rd])
    (by rw [hwr₃, hR.wr, hL.wr]) hframe ?_) ?_ ?_) (by rw [hv0₃, hst]) (by rw [hv1₃, hst]),
    fun j hj => ?_⟩
  · rw [hg₃ .x0 (by decide) (by decide), hg₂ .x0 (by decide) (by decide), hL.x0]
  · rw [hg₃ .x3 (by decide) (by decide), hg₂ .x3 (by decide) (by decide), hL.x3]
  · intro r hr
    have key : ∀ r ∈ preserved, r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
    have hn := key r hr
    rw [hg₃ r hn.1 hn.2.1, hg₂ r hn.2.2.1 hn.2.2.2, hL.kept r hr]
  · rw [hst, compressBlocks_succ, ← hL.state]
    rfl
  · rw [hx1₃, hg₂ .x1 (by decide) (by decide), hL.x1]
    exact (Offset.add_add _ _ 64).trans
      (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
  · rw [hx2₃, hx2]
  · have kj := kreg_ne j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at kj
    rw [hv₃ _ kj.1 kj.2.1 kj.2.2.1 kj.2.2.2.1]
    exact hR.k j hj (.inr hj)

theorem eval_x2 {s₀ : State} {i : Nat} {s : State} (h : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i))
    (hn : nb s₀ < 2 ^ 64) :
    eval (.nonzero .x .x2) s = some (nb s₀ - i != 0) := by
  have e : (BitVec.ofNat 64 (nb s₀ - i) != 0) = (nb s₀ - i != 0) := by
    by_cases h0 : nb s₀ - i = 0
    · simp [h0]
    · have : BitVec.ofNat 64 (nb s₀ - i) ≠ 0 := by
        intro h'
        have h'' := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h''
        exact h0 h''
      rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, ne_eq]
      exact ⟨fun _ => h0, fun _ => this⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, h, e]

theorem correct {s₀ : State} (hp : AArch64.Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha256.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hlt := hp.nb_lt
    have hin : ∀ d, d ≤ 16 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 d) 16 := by
      intro d hd
      refine ⟨stR s₀, by simp [hp.wr], ?_⟩
      exact contains_offset (by omega) (by omega)
    refine WP.seq ((load_ok s₀ (hin 0 (by decide)) (hin 16 (by decide))).mono
      fun s₁ ⟨hv0, hv1, _, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
    have hL₀ : VInv s₀ 0 s₁ :=
      { x0 := (by rw [hg₁])
        x3 := (by rw [hg₁])
        kept := fun r _ => (by rw [hg₁])
        rd := hrd₁
        wr := hwr₁
        frame := (by rw [hm₁]; exact Frame.refl _ _)
        state := (by rw [hm₁]; rfl)
        x1 := (by rw [hg₁]; simp [blkAddr])
        x2 := (by rw [hg₁]; simp [nb])
        v0 := (by rw [hv0, hm₁])
        v1 := (by rw [hv1, hm₁]) }
    refine WP.seq ((block_ok true hp hpos hL₀ (fun h => absurd h (by decide))).mono
      fun s₂ ⟨hV, hk⟩ => ?_)
    refine WP.ite (s₂.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
    · have h1 : nb s₀ = 1 := by
        have := hV.x2
        simp only [beq_iff_eq] at h
        rw [h] at this
        have h' := congrArg BitVec.toNat this
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        simp at h'; omega
      exact WP.block_nil (M := isa) (h1 ▸ hV.toCommon)
    · have h1 : 1 < nb s₀ := by
        have := hV.x2
        simp only [beq_eq_false_iff_ne, ne_eq] at h
        rw [this] at h
        by_contra hc
        exact h (by rw [show nb s₀ - (0 + 1) = 0 by omega]; rfl)
      let Inv : Nat → State → Prop := fun m s =>
        ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ VInv s₀ i s ∧ ∀ j < 16, s.v (kreg j) = kQuad j
      have hstep : ∀ m s, Inv m s → WP isa (oneBlock false) s (fun s' =>
          (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
          (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hL, hk⟩
        refine WP.mono (block_ok false hp hi hL fun _ => hk) fun s' ⟨hV', hk'⟩ => ?_
        have hev := eval_x2 hV'.x2 (by omega)
        by_cases hlast : i + 1 = nb s₀
        · exact .inl ⟨by rw [hev, hlast]; simp, hlast ▸ hV'.toCommon⟩
        · exact .inr ⟨by rw [hev]; simp; omega, nb s₀ - (i + 1), by omega, i + 1, rfl, by omega, hV', hk'⟩
      exact WP.loop (M := isa) Inv hstep (nb s₀ - 1) s₂ ⟨0 + 1, rfl, by omega, hV, hk⟩


theorem compress_verified :
    Verified AArch64.target Impl.Sha256.AArch64.Sha2.compress Proof.Sha256.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact AArch64.compress_verified.2.2

end VG.Proof.Sha256.AArch64.Sha2
