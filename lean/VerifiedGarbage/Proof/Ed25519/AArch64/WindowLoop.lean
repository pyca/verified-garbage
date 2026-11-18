module

public import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
public import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
public import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverSign
public import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-! ### `Ed25519.AArch64.PointMulBatch`, which this module and modules that import it used -/

section

/-! Frames for the batches of the scalar multiplications. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem PowersKeep.of_keeps {base : Addr} {o n : Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : PowersKeep base o n s t := by
  refine ⟨fun r hb hs hr => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hb h
    · exact hs h
    · exact hr h
  · rw [h.mem]; exact TableFrame.refl _ _ _ _

theorem PowersKeep.of_keep {base : Addr} {o n : Nat} {s t : State} (h : Keep base s t) :
    PowersKeep base o n s t := ⟨fun r _ _ hr => h.gpr r hr, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

theorem PowersKeep.of_counter {base : Addr} {o n : Nat} {s t : State} (h : CounterKeep base s t) :
    PowersKeep base o n s t := ⟨fun r hb _ hr => h.gpr r hr hb, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

theorem header_env {base : Addr} {m m' : Mem} (h : Outside base 56 8 m m') : env m' base = env m base := by
  funext i
  exact Outside_F h (by simp only [offset]; omega_using []) (Or.inr (by simp only [offset]; omega_using []))

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.PointMulCounter`, which this module and modules that import it used -/

section

/-! The public batch counter survives field and table operations. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem batchBegin_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .x19 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 j := by
    rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
  change s.mem.read (off base 56) 8 = _ at hc
  apply WP.of_runBlock
  simp only [batchBegin, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    addr, Size.bytes, Size.bits, State.load, State.store,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    hs.x0, hr, hw, hc, he, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ?_, fun r hr => ?_, True.intro, True.intro, rfl, ?_⟩
  · rw [write64_eq_writeW]; exact Mem.readW_writeW_self64 _ _ _
  · simp only [hr, ite_false]
  · rw [write64_eq_writeW]; exact writeW_outside _ _ _ (by decide)

theorem batchTest_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchTest) s fun t => t.gpr .x19 = BitVec.ofNat 64 j ∧ Keeps [.x19] s t :=
  WP.mono (ld_ok hs (by decide) (by decide) .x19) fun _ ⟨hv, hk⟩ => ⟨hv.trans hc, hk⟩

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.PointEqual`, which the modules that import this one used -/

section

/-! ### `Ed25519.AArch64.Nibbles`, which the modules that import this one used -/

section

/-!
# Verification's nibbles, split with vector instructions

Each block of `nibbles` loads 16 bytes of a scalar, takes each byte's high nibble (`ushr`) and
low nibble (`and` with 15), and interleaves them (`zip1`, `zip2`) into 32 bytes of the
workspace, low nibble first: nibble `j` of the scalar lands at offset `j` of its buffer, which
is its base-16 digit `j` (`decodeLE_nibble`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519

/-- Nibble `e % 2` of the byte `b`: its high nibble if `e` is odd, its low nibble if even. -/
def nib (b : Byte) (e : Nat) : Nat := if e % 2 = 1 then b.toNat / 16 else b.toNat % 16

/-! ## Vector lanes -/

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]

theorem vbyte_map2_b16 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 16) : vbyte (VArr.b16.map2 f x y) e = f 8 (vbyte x e) (vbyte y e) := by
  rw [VArr.map2]; exact vbyte_ofVBytes _ he

theorem vbyte_read16 (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    vbyte (m.read a 16) e = m (a + BitVec.ofNat 64 e) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  rw [getLsbD_read m 16 a (8 * e + r) (by omega_arith), show (8 * e + r) / 8 = e by omega_arith,
    show (8 * e + r) % 8 = r by omega_arith]

theorem b16_lanes_getD (x : BitVec 128) {i : Nat} (hi : i < 16) :
    (VArr.b16.lanes x).getD i 0 = (vbyte x i).setWidth 128 := by
  simp [VArr.lanes, List.getD_eq_getElem?_getD, hi]

theorem b16_lanes_length (x : BitVec 128) : (VArr.b16.lanes x).length = 16 := by
  simp [VArr.lanes]

theorem setWidth_setWidth8 (x : BitVec 8) : (x.setWidth 128).setWidth 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem pairs_length {α : Type} (f g : Nat → α) :
    ∀ k, ((List.range k).flatMap fun p => [f p, g p]).length = 2 * k
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, pairs_length f g k]; simp; omega_arith

theorem getD_pairs {α : Type} (f g : Nat → α) (d : α) :
    ∀ (k e : Nat), e < 2 * k →
      ((List.range k).flatMap fun p => [f p, g p]).getD e d = if e % 2 = 0 then f (e / 2) else g (e / 2)
  | 0, _, h => absurd h (by omega_arith)
  | k + 1, e, h => by
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    have hl := pairs_length f g k
    by_cases he : e < 2 * k
    · rw [List.getElem?_append_left (by rw [hl]; exact he), ← List.getD_eq_getElem?_getD,
        getD_pairs f g d k e he]
    · rw [List.getElem?_append_right (by rw [hl]; omega_arith), hl]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rcases (by omega_arith : e = 2 * k ∨ e = 2 * k + 1) with rfl | rfl
      · simp
      · simp [show (2 * k + 1) % 2 = 1 by omega_arith, show (2 * k + 1) / 2 = k by omega_arith]

theorem vbyte_zip1 (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval .zip1 .b16 x y) e = if e % 2 = 0 then vbyte x (e / 2) else vbyte y (e / 2) := by
  simp only [VPermOp.eval, VArr.ofLanes]
  rw [vbyte_ofVBytes _ he, b16_lanes_length, show 16 / 2 = 8 from rfl,
    getD_pairs _ _ _ 8 e (by omega_arith)]
  split <;> rw [b16_lanes_getD _ (by omega_arith), setWidth_setWidth8]

theorem vbyte_zip2 (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VPermOp.eval .zip2 .b16 x y) e =
      if e % 2 = 0 then vbyte x (8 + e / 2) else vbyte y (8 + e / 2) := by
  simp only [VPermOp.eval, VArr.ofLanes]
  rw [vbyte_ofVBytes _ he, b16_lanes_length, show 16 / 2 = 8 from rfl,
    getD_pairs _ _ _ 8 e (by omega_arith)]
  split <;> rw [b16_lanes_getD _ (by omega_arith), setWidth_setWidth8]

/-! ## One block -/

/-- 15 in every byte. -/
def mask15 : BitVec 128 := ofVBytes fun _ => (((15 : BitVec 16).setWidth 64).setWidth 8)

private theorem nib_byte : ∀ b : BitVec 8,
    (b &&& ((15 : BitVec 16).setWidth 64).setWidth 8).toNat = b.toNat % 16 ∧
    (VShiftOp.ushr.eval 4 8 0 b).toNat = b.toNat / 16 := by decide

/-- The nibbles of `x`'s byte `e / 2`, interleaved, low nibble first. -/
theorem nib_lanes (x : BitVec 128) (v1 : BitVec 128) {e : Nat} (he : e < 32) :
    let lo := x &&& mask15
    let hi := VArr.b16.map2 (fun w x y => VShiftOp.ushr.eval 4 w x y) v1 x
    (vbyte (if e < 16 then VPermOp.eval .zip1 .b16 lo hi else VPermOp.eval .zip2 .b16 lo hi)
      (e % 16)).toNat = nib (vbyte x (e / 2)) e := by
  intro lo hi
  have hlo : ∀ i < 16, (vbyte lo i).toNat = (vbyte x i).toNat % 16 := fun i hi => by
    simp only [lo, vbyte_and, mask15, vbyte_ofVBytes _ hi]; exact (nib_byte _).1
  have hhi : ∀ i < 16, (vbyte hi i).toNat = (vbyte x i).toNat / 16 := fun i h => by
    simp only [hi, vbyte_map2_b16 _ _ _ h]; exact (nib_byte _).2
  unfold nib
  split
  · rw [vbyte_zip1 _ _ (by omega_arith), Nat.mod_eq_of_lt (by assumption : e < 16)]
    split
    · rw [hlo _ (by omega_arith), ite_eq_right (by omega_arith)]
    · rw [hhi _ (by omega_arith), ite_eq_left (by omega_arith)]
  · rw [vbyte_zip2 _ _ (by omega_arith)]
    rw [show 8 + e % 16 / 2 = e / 2 by omega_arith]
    split
    · rw [hlo _ (by omega_arith), ite_eq_right (by omega_arith)]
    · rw [hhi _ (by omega_arith), ite_eq_left (by omega_arith)]

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {o : Nat} (ho : o % 16 = 0 ∧ o < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 o) 16) :
    exec (.ldrq t n o) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 o) 16)) := by
  simp only [exec, addr, show o < 4096 * 16 from ho.2, ho.1, and_self, ite_true, Option.bind_some,
    State.load, h, Option.map_some]

theorem exec_strq {s : State} {t : VReg} {n : Reg} {o : Nat} (ho : o % 16 = 0 ∧ o < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 o) 16) :
    exec (.strq t n o) s = some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 o) 16 (s.v t) } := by
  simp only [exec, addr, show o < 4096 * 16 from ho.2, ho.1, and_self, ite_true, Option.bind_some,
    State.store, h]

theorem exec_ushr4 (s : State) (d n : VReg) :
    exec (.vop (.shift .ushr .b16 d n 4)) s =
      some (s.setV d (VArr.b16.map2 (fun w x y => VShiftOp.ushr.eval 4 w x y) (s.v d) (s.v n))) := rfl

theorem exec_andv (s : State) (d n m : VReg) :
    exec (.vop (.logic .and d n m)) s = some (s.setV d (s.v n &&& s.v m)) := rfl

theorem exec_perm (s : State) (op : VPermOp) (d n m : VReg) :
    exec (.vop (.perm op .b16 d n m)) s = some (s.setV d (VPermOp.eval op .b16 (s.v n) (s.v m))) := rfl

theorem write16_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 < 2 ^ 64) :
    Outside base d 16 m (m.write (off base d) 16 v) := by
  intro x hx
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega_arith)]
  simp only [ofs] at hx
  omega_arith

theorem write16_at (m : Mem) (base : Addr) {d i : Nat} (v : BitVec 128) (hi : i < 16) : m.write (off base d) 16 v (off base (d + i)) = vbyte v i := by
  have e : off base (d + i) - off base d = BitVec.ofNat 64 i := by
    rw [off, off, ← Offset.add_add, Offset.add_sub_cancel_left]
  simp only [Mem.write, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith), hi,
    ite_true, vbyte]

/-- One block: the bytes at `P + src` on, as nibbles at `dst` on. -/
theorem nibBlock_ok {s : State} {base P : Addr} (hs : Scr s base) (hp : s.gpr .x2 = P)
    (h7 : s.v .v7 = mask15) {src dst : Nat} (hsa : src % 16 = 0) (hsb : src < 65536)
    (hda : dst % 16 = 0) (hdb : dst + 32 ≤ 8192)
    (hr : InRegions (s.rd ++ s.wr) (off P src) 16) :
    WP isa (.block (nibBlock src dst)) s fun t =>
      (∀ e < 32, (t.mem (off base (dst + e))).toNat = nib (s.mem (off P (src + e / 2))) e) ∧
      Outside base dst 32 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.v .v7 = s.v .v7 := by
  have hn := hs.nowrap
  have hw0 : InRegions s.wr (base + BitVec.ofNat 64 dst) 16 := ⟨_, hs.wr, contains_sc (by omega_arith)⟩
  have hw1 : InRegions s.wr (base + BitVec.ofNat 64 (dst + 16)) 16 := ⟨_, hs.wr, contains_sc (by omega_arith)⟩
  apply WP.of_runBlock
  rw [nibBlock, runBlock_cons, exec_ldrq ⟨hsa, hsb⟩ (by rw [hp]; exact hr), runStep_some]
  rw [runBlock_cons, exec_ushr4, runStep_some, runBlock_cons, exec_andv, runStep_some,
    runBlock_cons, exec_perm, runStep_some, runBlock_cons, exec_perm, runStep_some, runBlock_cons]
  simp only [RegUpd.v_setV, reduceCtorEq, ite_true, ite_false]
  rw [exec_strq ⟨hda, by omega_arith⟩ (by simp only [RegUpd.gpr_setV, RegUpd.wr_setV, hs.x0]; exact hw0),
    runStep_some, runBlock_cons,
    exec_strq ⟨by omega_arith, by omega_arith⟩ (by simp only [RegUpd.gpr_setV, RegUpd.wr_setV, hs.x0]; exact hw1),
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_⟩
  simp only [RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    RegUpd.sp_setV, reduceCtorEq, ite_true, ite_false, hs.x0, hp, h7]
  refine ⟨fun e he => ?_, ?_, trivial, trivial, trivial, trivial, trivial⟩
  · have hl := nib_lanes (s.mem.read (off P src) 16) (s.v .v1) he
    simp only at hl
    rw [vbyte_read16 _ _ (by omega_arith), Offset.add_add] at hl
    by_cases h16 : e < 16
    · rw [write16_outside _ base _ (by omega_arith) _ (Or.inl (by rw [ofs_off' base (by omega_arith)]; omega_arith)),
        write16_at _ base _ h16]
      rw [ite_eq_left h16, Nat.mod_eq_of_lt h16] at hl
      exact hl
    · rw [show dst + e = dst + 16 + (e - 16) by omega_arith, write16_at _ base _ (by omega_arith)]
      rw [ite_eq_right h16, show e % 16 = e - 16 by omega_arith] at hl
      exact hl
  · intro x hx
    rw [write16_outside _ base _ (by omega_arith) _ (by omega_arith), write16_outside _ base _ (by omega_arith) _ (by omega_arith)]

theorem nib_congr (b : Byte) {e e' : Nat} (h : e % 2 = e' % 2) : nib b e = nib b e' := by
  simp only [nib, h]

/-! ## Blocks -/

/-- `n` blocks: the `16 n` bytes at `P + src` on, as nibbles at `dst` on. -/
theorem nibBlocks_ok {s : State} {base P : Addr} (hs : Scr s base) (hp : s.gpr .x2 = P)
    (h7 : s.v .v7 = mask15) {src dst : Nat} (n : Nat) (hsa : src % 16 = 0) (hsb : src + 16 * n ≤ 65536)
    (hda : dst % 16 = 0) (hdb : dst + 32 * n ≤ 8192)
    (hr : ∀ q < n, InRegions (s.rd ++ s.wr) (off P (src + 16 * q)) 16)
    (hf : ∀ i < 16 * n, ofs base (off P (src + i)) < dst ∨ dst + 32 * n ≤ ofs base (off P (src + i))) :
    WP isa (.block (nibBlocks src dst n)) s fun t =>
      (∀ e < 32 * n, (t.mem (off base (dst + e))).toNat = nib (s.mem (off P (src + e / 2))) e) ∧
      Outside base dst (32 * n) s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.v .v7 = s.v .v7 := by
  have hn := hs.nowrap
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun e he => by omega_arith, Outside.refl _ _ _ _, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [nibBlocks, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp h7 (by omega_arith) (by omega_arith) (fun q hq => hr q (by omega_arith))
      (fun i hi => by have := hf i (by omega_arith); omega_arith)) fun t ⟨tv, tm, tg, tr, tw, tsp, t7⟩ => ?_
    have ht : Scr t base := ⟨by rw [tg]; exact hs.x0, by rw [tw]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (nibBlock_ok (P := P) ht (by rw [tg]; exact hp) (by rw [t7]; exact h7) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by rw [tr, tw]; exact hr n (by omega_arith)))
      fun u ⟨uv, um, ug, ur, uw, usp, u7⟩ => ?_
    refine ⟨fun e he => ?_, fun x hx => ?_, ug.trans tg, ur.trans tr, uw.trans tw, usp.trans tsp,
      u7.trans t7⟩
    · by_cases h : e < 32 * n
      · rw [um _ (Or.inl (by rw [ofs_off' base (by omega_arith)]; omega_arith))]
        exact tv e h
      · obtain ⟨e', rfl⟩ : ∃ e', e = 32 * n + e' := ⟨e - 32 * n, by omega_arith⟩
        have hv := uv e' (by omega_arith)
        rw [show dst + 32 * n + e' = dst + (32 * n + e') by omega_arith,
          show src + 16 * n + e' / 2 = src + (32 * n + e') / 2 by omega_arith,
          tm _ (by have := hf ((32 * n + e') / 2) (by omega_arith); omega_arith)] at hv
        rw [hv]
        exact nib_congr _ (by omega_arith)
    · rw [um x (by omega_arith), tm x (by omega_arith)]

/-! ## The scalars -/

theorem exec_dupb (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .b16 d n)) s = some (s.setV d (ofVBytes fun _ => (s.gpr n).setWidth 8)) := rfl

/-- 15 in every byte of `v7`, through `x8`. -/
theorem nibMask_ok (s : State) :
    WP isa (.block [.movz .w .x8 15 0, .vop (.dup .b16 .v7 .x8)]) s fun t =>
      t.v .v7 = mask15 ∧ Keeps [.x8] s t := by
  rw [show ([.movz .w .x8 15 0, .vop (.dup .b16 .v7 .x8)] : List Instr) =
    [.movz .w .x8 15 0] ++ [.vop (.dup .b16 .v7 .x8)] from rfl, WP.block_append_iff]
  refine WP.mono (movzW_ok s .x8 15) fun a ⟨a8, ka⟩ => ?_
  apply WP.of_runBlock
  rw [runBlock_cons, exec_dupb, runStep_some, runBlock_nil]
  refine ⟨_, rfl, by rw [RegUpd.v_setV_self, a8]; rfl, ka.trans ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩

/-- A pointer from the workspace, keeping the vector registers. -/
theorem loadPointerV_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) (d : Nat)
    (ha : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [ld r d]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t ∧ t.v = s.v := by
  apply WP.of_runBlock
  rw [runBlock_cons, load_sc hs ha hd, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem nib_decode (m : Mem) (p : Addr) {n j : Nat} (hj : j < 2 * n) :
    nib (m (off p (j / 2))) j = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 16 ^ j % 16 := by
  rw [decodeLE_nibble, nibbleOf, input_byte m p n (j / 2) (by omega_arith), nib]

/-- `k`'s nibbles, from its pointer in `x2`. -/
theorem kNibblesAt_ok {s : State} {base kp : Addr} (hs : Scr s base) (hp : s.gpr .x2 = kp)
    (hkr : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off kp d) 16)
    (hkf : ∀ i < 64, 8192 ≤ ofs base (off kp i)) :
    WP isa (.block kNibblesAt) s fun t =>
      (∀ j < 128, (t.mem (off base (768 + j))).toNat =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 16 ^ j % 16) ∧
      Outside base 768 128 s.mem t.mem ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v .v7 = mask15 := by
  rw [kNibblesAt, WP.block_append_iff]
  refine WP.mono (nibMask_ok s) fun b ⟨b7, kb⟩ => ?_
  have hb : Scr b base := hs.of_keeps kb (by decide)
  refine WP.mono (nibBlocks_ok (P := kp) hb (by rw [kb.gpr _ (by decide), hp]) b7 4 (by decide)
    (by decide) (by decide) (by decide)
    (fun q hq => by rw [kb.rd, kb.wr, Nat.zero_add]; exact hkr (16 * q) (by omega_arith))
    (fun i hi => Or.inr (by rw [Nat.zero_add]; have := hkf i (by omega_arith); omega_arith)))
    fun c ⟨cv, cm, cg, cr, cw, csp, c7⟩ => ?_
  refine ⟨fun j hj => ?_, by rw [← kb.mem]; exact cm, fun r hr => ?_, by rw [cr, kb.rd],
    by rw [cw, kb.wr], by rw [csp, kb.sp], c7.trans b7⟩
  · have hv := cv j (by omega_arith)
    rw [Nat.zero_add, kb.mem] at hv
    rw [hv, nib_decode (n := 64) _ _ (by omega_arith)]
  · rw [cg, kb.gpr r (by simpa using hr)]

/-- `S`'s nibbles, from its pointer, less 32, in `x2`. -/
theorem sNibblesAt_ok {s : State} {base sp : Addr} (hs : Scr s base) (hp : s.gpr .x2 = sp)
    (h7 : s.v .v7 = mask15)
    (hsr : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sp 32) d) 16)
    (hsf : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)) :
    WP isa (.block (nibBlocks 32 896 2)) s fun t =>
      (∀ j < 64, (t.mem (off base (896 + j))).toNat =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 16 ^ j % 16) ∧
      Outside base 896 64 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have sp32 (d : Nat) : off (off sp 32) d = off sp (32 + d) := Offset.add_add ..
  refine WP.mono (nibBlocks_ok (P := sp) hs hp h7 2 (by decide) (by decide) (by decide) (by decide)
    (fun q hq => by rw [← sp32]; exact hsr (16 * q) (by omega_arith))
    (fun i hi => Or.inr (by rw [← sp32]; have := hsf i (by omega_arith); omega_arith)))
    fun u ⟨uv, um, ug, ur, uw, usp, _⟩ => ⟨fun j hj => ?_, um, ug, ur, uw, usp⟩
  rw [uv j (by omega_arith), ← sp32, nib_decode (n := 32) _ _ (by omega_arith)]

/-- The scalars' nibbles: `k`'s at byte 768 and `S`'s at byte 896. -/
theorem nibbles_ok {s : State} {base kp sp : Addr} (hs : Scr s base)
    (hk : s.mem.readW (off base 7952) 64 = kp) (hsg : s.mem.readW (off base 7944) 64 = sp)
    (hkr : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off kp d) 16)
    (hsr : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sp 32) d) 16)
    (hkf : ∀ i < 64, 8192 ≤ ofs base (off kp i))
    (hsf : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)) :
    WP isa (.block nibbles) s fun t =>
      (∀ j < 128, (t.mem (off base (768 + j))).toNat =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 16 ^ j % 16) ∧
      (∀ j < 64, (t.mem (off base (896 + j))).toNat =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 16 ^ j % 16) ∧
      Outside base 768 192 s.mem t.mem ∧ (∀ r, r ≠ .x2 → r ≠ .x8 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hn := hs.nowrap
  rw [nibbles, kNibbles, sNibbles, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x2 7952 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_
  have ha : Scr a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (kNibblesAt_ok ha (ap.trans hk) (fun d hd => by rw [ka.rd, ka.wr]; exact hkr d hd) hkf)
    fun c ⟨cv, cm, cg, cr, cw, csp, c7⟩ => ?_
  have hc : Scr c base := ⟨by rw [cg _ (by decide)]; exact ha.x0, by rw [cw]; exact ha.wr, ha.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadPointerV_ok hc .x2 7944 (by decide) (by decide)) fun d ⟨dp, kd, dv⟩ => ?_
  have hd : Scr d base := hc.of_keeps kd (by decide)
  have csg : c.mem.readW (off base 7944) 64 = sp :=
    (cm.word (d := 7944) (Or.inr (by decide)) (by decide)).trans (by rw [ka.mem]; exact hsg)
  have hsf' : ∀ i < 32, c.mem (off (off sp 32) i) = s.mem (off (off sp 32) i) := fun i hi => by
    rw [cm _ (Or.inr (by have := hsf i hi; omega_arith)), ka.mem]
  refine WP.mono (sNibblesAt_ok hd (dp.trans csg) (by rw [dv, c7])
    (fun d hd => by rw [kd.rd, kd.wr, cr, cw, ka.rd, ka.wr]; exact hsr d hd) hsf)
    fun u ⟨uv, um, ug, ur, uw, usp⟩ => ?_
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun x hx => ?_, fun r h2 h8 => ?_, ?_, ?_, ?_⟩
  · rw [um _ (Or.inl (by rw [ofs_off' base (by omega_arith)]; omega_arith)), kd.mem, cv j hj, ka.mem]
  · rw [uv j hj, kd.mem]
    congr 3
    exact List.map_congr_left fun i hi => hsf' i (List.mem_range.mp hi)
  · rw [um x (by omega_arith), kd.mem, cm x (by omega_arith), ka.mem]
  · rw [ug, kd.gpr r (by simpa using h2), cg r h8, ka.gpr r (by simpa using h2)]
  · rw [ur, kd.rd, cr, ka.rd]
  · rw [uw, kd.wr, cw, ka.wr]
  · rw [usp, kd.sp, csp, ka.sp]

end VG.Proof.Ed25519.AArch64

end

end

/-! Projective comparison implements the specification's pointEqual. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem equalOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa Impl.Ed25519.AArch64.pointEqual s fun t => Keep base s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual (point (env s.mem base) 0 1 2 3)
        (point (env s.mem base) 4 5 6 7)) := by
  rw [Impl.Ed25519.AArch64.pointEqual]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.scr hs) 8 9) fun b ⟨bz, kb, be⟩ => ?_
  have kab := ka.trans kb
  have bx : (b.gpr .x8 == 0) = decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2) := by
    rw [bz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  apply WP.ite _ (congrArg some bx)
  · intro htx
    have hx := of_decide_eq_true htx
    refine WP.seq (WP.mono (fieldEqual_ok (kab.scr hs) 10 11) fun c ⟨cz, kc, _⟩ => ?_)
    have cy : (c.gpr .x8 == 0) = decide (env s.mem base 1 * env s.mem base 6 = env s.mem base 5 * env s.mem base 2) := by
      rw [cz, be 10 (by decide), be 11 (by decide), va, (equalOps_eval _).2.2.1, (equalOps_eval _).2.2.2]
    apply WP.ite _ (congrArg some cy)
    · intro hty
      have hy := of_decide_eq_true hty
      refine WP.mono (returnFlag_ok c true) fun t ⟨tr, kt⟩ => ?_
      refine ⟨(kab.trans kc).trans (Keep.of_keeps kt (by decide)), ?_⟩
      simpa only [Spec.Ed25519.pointEqual, point, hx, hy, beq_self_eq_true, Bool.and_self] using tr
    · intro hfy
      have hy := of_decide_eq_false hfy
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
      refine ⟨(kab.trans kc).trans kt, ?_⟩
      simpa only [Spec.Ed25519.pointEqual, point, hx, beq_self_eq_true, beq_eq_false_iff_ne.mpr hy,
        Bool.and_false, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr
  · intro hfx
    have hx := of_decide_eq_false hfx
    refine WP.mono (recoverInvalid_ok b base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨kab.trans kt, ?_⟩
    simpa only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr hx, Bool.false_and, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr

end VG.Proof.Ed25519.AArch64

end

end

/-! Merged from `Proof.Ed25519.AArch64.WindowByte`. -/

@[expose] public section

section
/-!
# Verification's nibbles: one window per nibble of the scalars

Nibble `i` of `k` (and of `S`) is a digit, read from the nibbles' buffers; after it, the
accumulator represents `[k / 16^i]A - [S / 16^i]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- What a nibble of the scalars may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 56 712 s.mem t.mem

theorem ByteKeep.refl (base : Addr) (s : State) : ByteKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : ByteKeep base s t) (k : ByteKeep base t u) :
    ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.of_counter {base : Addr} {s t : State}
    (ag : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r) (ar : t.rd = s.rd) (aw : t.wr = s.wr) (asp : t.sp = s.sp)
    (am : Outside base 56 8 s.mem t.mem) : ByteKeep base s t :=
  ⟨fun r _ hb _ => ag r hb, ar, aw, asp, am.mono (by decide) (by decide)⟩

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : ByteKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinCtx.of_byte {base : Addr} {K S : Nat} {A : EPoint dZ} {s t : State}
    (h : WinCtx base K S A s) (k : ByteKeep base s t) : WinCtx base K S A t :=
  h.of_mem (k.scratch h.scratch) k.mem

/-! ## Digits from the nibbles -/

theorem digitK {base : Addr} {K S : Nat} {A : EPoint dZ} {s : State} (h : WinCtx base K S A s)
    {i : Nat} (hi : i < 128) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitAt 768) (K / 16 ^ i % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitAt_ok ht.scratch (by decide) (by omega_arith) (kt.counter.trans hc))
    fun u ⟨uv, ku⟩ => ?_
  rw [ht.kNib i hi] at uv
  exact ⟨uv, ku.mono (by decide)⟩

theorem digitS {base : Addr} {K S : Nat} {A : EPoint dZ} {s : State} (h : WinCtx base K S A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitAt 896) (S / 16 ^ i % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitAt_ok ht.scratch (by decide) (by omega_arith) (kt.counter.trans hc))
    fun u ⟨uv, ku⟩ => ?_
  rw [ht.sNib i hi] at uv
  exact ⟨uv, ku.mono (by decide)⟩

/-! ## A nibble -/

private theorem above_cmp : ∀ i < 129,
    (BitVec.ofNat 64 i - BitVec.ofNat 64 64 != 0) = decide (i ≠ 64) := by decide

theorem aboveLow_ok {s : State} {base : Addr} (hs : Scr s base) (i : Nat) (hi : i ≤ 128)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block aboveLow) s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 64)) ∧
      Keeps [.x19] s t := by
  rw [aboveLow, show ([ld .x19 56, .subImm .x .x19 .x19 64] : List Instr) =
    [ld .x19 56] ++ [.subImm .x .x19 .x19 64] from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x19 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (64 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write, ka.mem],
    by simp only [RegUpd.rd_write, ka.rd], by simp only [RegUpd.wr_write, ka.wr],
    by simp only [RegUpd.sp_write, ka.sp]⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, av, hc, above_cmp i (by omega_arith)]
  · have h : r ≠ .x19 := by simpa only [List.mem_singleton] using hr
    rw [RegUpd.gpr_write_of_ne _ _ _ h, ka.gpr r hr]

theorem nibStepA_ok {s : State} {base : Addr} {K S : Nat} {A : EPoint dZ} (h : WinCtx base K S A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi64 : 64 ≤ i) (hi : i < 128)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) (hS : S < 256 ^ 32)
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))) :
    WP isa nibStepA s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 64)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3) ((K / 16 ^ i) • A + (S / 16 ^ i) • (-baseAff)) ∧
      ByteKeep base s t := by
  rw [nibStepA]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
  have ae := header_env am
  have ha' := h.of_byte ka
  refine WP.seq (WP.mono (windowA_ok (a := (K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (Nat.mod_lt _ (by decide)) (digitK ha' hi av))
    fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.mono (aboveLow_ok hb'.scratch i (by omega_arith) (kb.counter.trans av)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact bd, ?_, (ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kb.counter.trans av
  · rw [kt.mem]
    convert br using 1
    rw [← nibble_step A (-baseAff) K S i, nibble_high_zero hS hi64, Nat.zero_mod, zero_smul, add_zero]

theorem nibStepAB_ok {s : State} {base : Addr} {K S : Nat} {A : EPoint dZ} (h : WinCtx base K S A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))) :
    WP isa nibStepAB s fun t => t.gpr .x19 = BitVec.ofNat 64 i ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3) ((K / 16 ^ i) • A + (S / 16 ^ i) • (-baseAff)) ∧
      ByteKeep base s t := by
  rw [nibStepAB]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
  have ae := header_env am
  have ha' := h.of_byte ka
  refine WP.seq (WP.mono (windowAB_ok (a := (K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (digitK ha' (by omega_arith) av) (digitS ha' hi av)) fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.mono (batchTest_ok hb'.scratch i (kb.counter.trans av)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact bd, ?_, (ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kb.counter.trans av
  · rw [kt.mem, ← nibble_step A (-baseAff) K S i]
    exact br

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's loops over the nibbles of the scalars

The leading zero nibbles of `k` above its low 64 are skipped, as the sum before
them is zero; nibbles 127 down to 64 are digits of `k` alone, nibbles 63 down to 0
of both scalars; after the loops the accumulator represents `[k]A - [S]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- The loops' invariant, with `c` nibbles left. -/
structure WinLoop (s₀ : State) (base : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base K S A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kLt : K < 256 ^ 64
  sLt : S < 256 ^ 32
  value : RepP (point (env s.mem base) 0 1 2 3) ((K / 16 ^ c) • A + (S / 16 ^ c) • (-baseAff))
  keep : ByteKeep base s₀ s

theorem WinLoop.of_keeps {s₀ s t : State} {base : Addr} {A : EPoint dZ} {K S c : Nat}
    {rs : List Reg} (h : WinLoop s₀ base A K S c s) (k : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : WinLoop s₀ base A K S c t := by
  have kb : ByteKeep base s t := ByteKeep.of_keeps k hrs
  exact ⟨h.ctx.of_byte kb, by rw [k.mem]; exact h.d, by rw [k.mem]; exact h.counter, h.kLt, h.sLt,
    by rw [k.mem]; exact h.value, h.keep.trans kb⟩

/-- A nibble of `k` alone, from `64 + j + 1` nibbles left to `64 + j`. -/
theorem stepA_ok {s₀ t : State} {base : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 64)
    (ht : WinLoop s₀ base A K S (64 + (j + 1)) t) :
    WP isa nibStepA t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base A K S (64 + j) u := by
  refine WP.mono (nibStepA_ok (i := 64 + j) ht.ctx ht.d (by omega_arith) (by omega_arith)
    (by rw [ht.counter]; rfl) ht.sLt ht.value) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  exact ⟨by rw [uz]; simp, ht.ctx.of_byte uk, ud, uc, ht.kLt, ht.sLt, uv, ht.keep.trans uk⟩

/-- A nibble of both scalars, from `j + 1` nibbles left to `j`. -/
theorem stepB_ok {s₀ t : State} {base : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 64)
    (ht : WinLoop s₀ base A K S (j + 1) t) :
    WP isa nibStepAB t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base A K S j u := by
  refine WP.mono (nibStepAB_ok (i := j) ht.ctx ht.d hj ht.counter ht.value)
    fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  exact ⟨by simp only [eval, read_x, uz, counter_nonzero (by omega_arith : j < 2 ^ 64)], ht.ctx.of_byte uk,
    ud, uc, ht.kLt, ht.sLt, uv, ht.keep.trans uk⟩

theorem loopA_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 64) (h : WinLoop s₀ base A K S (64 + n) s) :
    WP isa (.loop nibStepA (.nonzero .x .x19)) s (WinLoop s₀ base A K S 64) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base A K S (64 + n) t ∧ 0 < n ∧ n ≤ 64)
    (n := n)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega_arith : n ≠ 0)
    refine WP.mono (stepA_ok (by omega_arith) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega_arith, hu, by omega_arith, by omega_arith⟩
  · exact ⟨h, hn0, hn⟩

theorem windowsA_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc64 : 64 ≤ c) (hc128 : c ≤ 128) (h : WinLoop s₀ base A K S c s) :
    WP isa windowsA s (WinLoop s₀ base A K S 64) := by
  rw [windowsA]
  refine WP.seq (WP.mono (aboveLow_ok h.ctx.scratch c (by omega_arith) h.counter) fun a ⟨az, ka⟩ => ?_)
  have ha := h.of_keeps ka (by decide)
  refine WP.ite (decide (c ≠ 64)) az (fun hy => ?_) (fun hn => ?_)
  · obtain ⟨n, rfl⟩ : ∃ n, c = 64 + n := ⟨c - 64, by omega_arith⟩
    exact loopA_ok n (by have := of_decide_eq_true hy; omega_arith) (by omega_arith) ha
  · have : c = 64 := by simpa using hn
    subst this
    exact WP.block_nil ha

theorem loopB_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base A K S 64 s) :
    WP isa (.loop nibStepAB (.nonzero .x .x19)) s (WinLoop s₀ base A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base A K S n t ∧ 0 < n ∧ n ≤ 64)
    (n := 64)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega_arith : n ≠ 0)
    refine WP.mono (stepB_ok (by omega_arith) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega_arith, hu, by omega_arith, by omega_arith⟩
  · exact ⟨h, by decide, by decide⟩

/-! ## Skipping the leading zero nibbles of `k` -/

theorem subOne_ok (s : State) (r : Reg) (n : Nat) (hc : s.gpr r = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x r r 1]) s fun t => t.gpr r = BitVec.ofNat 64 n ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

private theorem byte_ext : ∀ b : BitVec 8, (b.setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  decide

theorem skipLoad_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat) (hj : j < 128)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block skipLoad) s fun t => t.gpr .x8 = BitVec.ofNat 64 j ∧
      t.gpr .x19 = BitVec.ofNat 64 (s.mem (off base (768 + j))).toNat ∧ Keeps [.x2, .x8, .x19] s t := by
  rw [skipLoad, show ([ld .x8 56, .subImm .x .x8 .x8 1, .add .x .x2 .x0 .x8, .ldrb .x19 .x2 768] :
      List Instr) = [ld .x8 56] ++ ([.subImm .x .x8 .x8 1] ++ [.add .x .x2 .x0 .x8, .ldrb .x19 .x2 768])
      from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun b ⟨bv, kb⟩ => ?_
  have hm : b.mem = s.mem := kb.mem.trans ka.mem
  have b0 : b.gpr .x0 = base := (kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hs.x0)
  have hea : base + BitVec.ofNat 64 j + BitVec.ofNat 64 768 = off base (768 + j) := by
    rw [Offset.add_add, Nat.add_comm]
  have hr : InRegions (b.rd ++ b.wr) (off base (768 + j)) 1 :=
    ⟨_, List.mem_append_right _ (by rw [kb.wr, ka.wr]; exact hs.wr), contains_sc (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    b0, bv, hea, hr, hm, read_byte, byte_ext,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, hm, by simp only [RegUpd.rd_write, kb.rd, ka.rd],
    by simp only [RegUpd.wr_write, kb.wr, ka.wr],
    by simp only [RegUpd.sp_write, kb.sp, ka.sp]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]
  rw [kb.gpr r (by simp [hr.2.1]), ka.gpr r (by simp [hr.2.1])]

theorem skipStore_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 (64 + n)) :
    WP isa (.block [st .x8 56, .subImm .x .x19 .x8 64]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (64 + n) ∧
      (∀ r, r ≠ .x19 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  have he : BitVec.ofNat 64 (64 + n) - BitVec.ofNat 64 64 = BitVec.ofNat 64 n := by
    rw [Nat.add_comm, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc hs (by decide) (by decide), runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (64 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, h8, he]
  refine ⟨trivial, ?_, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, ?_⟩
  · rw [RegUpd.mem_write, Mem.readW_writeW_self64]
  · rw [RegUpd.mem_write]; exact writeW_outside _ _ _ (by decide)

private theorem byte_nonzero : ∀ b : BitVec 8,
    (BitVec.ofNat 64 b.toNat != 0) = decide (b.toNat ≠ 0) := by decide

theorem movzZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => eval (.nonzero .x .x19) t = some false ∧
      Keeps [.x19] s t :=
  WP.mono (movzW_ok s .x19 0) fun t ⟨tv, kt⟩ => ⟨by simp only [eval, read_x, tv]; rfl, kt⟩

/-- Skipping: `c = 64 + n` nibbles are left, and the nibbles of `k` from `c` on are zero. -/
def SkipInv (s₀ : State) (base : Addr) (A : EPoint dZ) (K S : Nat) (n : Nat) (s : State) : Prop :=
  WinLoop s₀ base A K S (64 + n) s ∧ K / 16 ^ (64 + n) = 0 ∧ 0 < n ∧ n ≤ 64

/-- Whether the skipping goes on below `64 + j + 1` nibbles left: nibble `64 + j` of `k` is zero,
and more than 64 nibbles are left after it. -/
def skipOn (K j : Nat) : Bool := decide (K / 16 ^ (64 + j) % 16 = 0 ∧ j ≠ 0)

/-- Where the skipping stops below `64 + j + 1` nibbles left, if it does. -/
def skipEnd (K j : Nat) : Nat := if K / 16 ^ (64 + j) % 16 = 0 then 64 else 64 + (j + 1)

theorem skipBody_ok {s₀ t : State} {base : Addr} {A : EPoint dZ} {K S j : Nat}
    (h : SkipInv s₀ base A K S (j + 1) t) :
    WP isa skipBody t fun u => eval (.nonzero .x .x19) u = some (skipOn K j) ∧
      (skipOn K j = false → WinLoop s₀ base A K S (skipEnd K j) u) ∧
      (skipOn K j = true → SkipInv s₀ base A K S j u) := by
  obtain ⟨hl, hz, _, hn⟩ := h
  rw [skipBody]
  refine WP.seq (WP.mono (skipLoad_ok hl.ctx.scratch (64 + j) (by omega_arith)
    (by rw [hl.counter]; rfl)) fun a ⟨a8, av, ka⟩ => ?_)
  have ha := hl.of_keeps ka (by decide)
  have hb : (t.mem (off base (768 + (64 + j)))).toNat = K / 16 ^ (64 + j) % 16 :=
    hl.ctx.kNib _ (by omega_arith)
  refine WP.ite (decide ((t.mem (off base (768 + (64 + j)))).toNat ≠ 0))
    (by simp only [eval, read_x, av, byte_nonzero]) (fun hy => ?_) (fun hy => ?_)
  · have h0 : K / 16 ^ (64 + j) % 16 ≠ 0 := by rw [← hb]; simpa using hy
    have hoff : skipOn K j = false := by simp only [skipOn, h0, false_and, decide_false]
    refine WP.mono (movzZero_ok a) fun u ⟨uz, ku⟩ => ⟨by rw [uz, hoff], fun _ => ?_,
      fun ht => absurd ht (by rw [hoff]; decide)⟩
    have e : skipEnd K j = 64 + (j + 1) := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact ha.of_keeps ku (by decide)
  · have h0 : K / 16 ^ (64 + j) % 16 = 0 := by rw [← hb]; simpa using hy
    refine WP.mono (skipStore_ok ha.ctx.scratch j a8) fun u ⟨uv, uc, ug, ur, uw, usp, um⟩ => ?_
    have ku : ByteKeep base a u := ByteKeep.of_counter ug ur uw usp um
    have hK : K / 16 ^ (64 + j) = 0 := by
      have := nibble_split K (64 + j)
      rw [show 64 + j + 1 = 64 + (j + 1) by omega_arith, hz] at this
      omega_arith
    have hw : WinLoop s₀ base A K S (64 + j) u := by
      refine ⟨ha.ctx.of_byte ku, by rw [header_env um]; exact ha.d, uc, ha.kLt, ha.sLt, ?_,
        ha.keep.trans ku⟩
      have v := ha.value
      rw [hz, nibble_high_zero ha.sLt (by omega_arith)] at v
      rw [header_env um, hK, nibble_high_zero ha.sLt (by omega_arith)]
      exact v
    have he : skipOn K j = decide (j ≠ 0) := by simp only [skipOn, h0, true_and]
    have hj64 : j < 64 := by omega_arith
    refine ⟨by simp only [eval, read_x, uv]; rw [counter_nonzero (by omega_arith : j < 2 ^ 64), he], fun hf => ?_,
      fun ht => ⟨hw, hK, by rw [he] at ht; have := of_decide_eq_true ht; omega_arith, by omega_arith⟩⟩
    have hj : j = 0 := by rw [he] at hf; simpa using hf
    subst hj
    have e : skipEnd K 0 = 64 := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact hw

theorem skipEnd_range (K j : Nat) (hj : j < 64) : 64 ≤ skipEnd K j ∧ skipEnd K j ≤ 128 := by
  unfold skipEnd; split <;> omega_arith

theorem skipZero_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base A K S 128 s) :
    WP isa skipZero s fun t => ∃ c, 64 ≤ c ∧ c ≤ 128 ∧ WinLoop s₀ base A K S c t := by
  have hK : K / 16 ^ 128 = 0 := Nat.div_eq_of_lt (by rw [show (16 : Nat) ^ 128 = 256 ^ 64 from rfl]; exact h.kLt)
  rw [skipZero]
  apply WP.loop (SkipInv s₀ base A K S) (n := 64)
  · intro n t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.2.2.1; omega_arith : n ≠ 0)
    have hj : j < 64 := by have := ht.2.2.2; omega_arith
    refine WP.mono (skipBody_ok ht) fun u ⟨uz, uf, ut⟩ => ?_
    cases hs : skipOn K j
    · exact Or.inl ⟨uz.trans (by rw [hs]), skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2,
        uf hs⟩
    · exact Or.inr ⟨uz.trans (by rw [hs]), j, by omega_arith, ut hs⟩
  · exact ⟨h, hK, by decide, by decide⟩

end VG.Proof.Ed25519.AArch64
