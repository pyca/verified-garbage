module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Ed25519.WindowNibble
public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
