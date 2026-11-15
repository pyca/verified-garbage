module
-- separate module: its proofs (about 4 s) build in parallel with the batch's (`Verified`), which `ModeCore` also imports

public import VerifiedGarbage.Impl.Seed.AArch64.Serial
public import VerifiedGarbage.Proof.Seed.G
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Spec.Aes

/-!
# SEED's one-block core on AArch64 enciphers a block

`crypt_wp`: `Impl.Seed.AArch64.Serial.crypt` replaces the block at
`x5 + bufOff` with `Spec.Seed.encryptBlock` of it, under the schedule at
`x5 + keyOff`, and changes no other memory.

* `aff_ok`: `S1[x]` is `S0[x]` through the two tables of sixteen bytes
  (checked on the packed S-boxes, `Proof/Seed/SboxLit.lean`).
* `g_eq_mix`: RFC 4269 §2.2's `Z` is the masked, rotated `Y` of `mix`
  (`mixOf`), byte by byte (`byteOf_ror`, `maskBytes`).
* `g_run`: `g` computes `G`: the word's bytes select `S0` from the table
  registers (`Tbl.select_full_run`), `affine_run` makes those of `X1` and
  `X3` `S1`, and `mix_run` masks and rotates. `Consts` is what `setup`
  leaves (`setup_wp`) and every step keeps.
* `f_run`, `round2_run`, `rounds_run`: `F` into one half, two rounds, and
  the sixteen (`Proof.Seed.roundsN`), with the halves in `x0`–`x3`.
* `loads_run`, `stores_run`, `stored_bytes`: the block's words, big-endian.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64
open VG.Impl.Seed.AArch64.Serial
open VG.Spec.Seed (Word)
open VG.Proof.Seed (byteOf maskOf sOf sTable)

/-! ## `S1` over `S0` -/

/-- `S1[x]` from `S0[x]`, by the two tables. -/
def affOf (y : Byte) : Byte := loTable.getD (y.toNat % 16) 0 ^^^ hiTable.getD (y.toNat / 16) 0

theorem aff_nat : ∀ c < 256,
    affOf (BitVec.ofNat 8 (VG.Proof.Seed.sNat false c)) = BitVec.ofNat 8 (VG.Proof.Seed.sNat true c) := by
  lit_decide

theorem aff_ok (x : Byte) : affOf (Spec.Seed.s0.getD x.toNat 0) = Spec.Seed.s1.getD x.toNat 0 := by
  have h := aff_nat x.toNat x.isLt
  rw [← VG.Proof.Seed.sTable_getD, ← VG.Proof.Seed.sTable_getD] at h
  exact h

/-! ## The masks -/

/-- `mix`'s value. -/
def mixOf (y : Word) : Word :=
  ((y &&& mask0) ^^^ (y &&& mask1).rotateRight 8) ^^^
    ((y &&& mask0.rotateRight 8) ^^^ (y &&& mask1.rotateRight 8).rotateRight 8).rotateRight 16

theorem byteOf_xor (u v : Word) (j : Nat) : byteOf (u ^^^ v) j = byteOf u j ^^^ byteOf v j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [byteOf, hi]

theorem byteOf_and (u v : Word) (j : Nat) : byteOf (u &&& v) j = byteOf u j &&& byteOf v j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [byteOf, hi]

theorem byteOf_ror (u : Word) {j k : Nat} (hj : j < 4) (hk : k < 4) :
    byteOf (u.rotateRight (8 * k)) j = byteOf u ((j + k) % 4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [byteOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  have hk' : 8 * k % 32 = 8 * k := by omega_using [hk]
  rw [BitVec.getLsbD_rotateRight, hk']
  split
  · rename_i h
    congr 1
    omega_using [hj, hk, hi, h]
  · rename_i h
    simp only [show 8 * j + i < 32 by omega_using [hj, hi], decide_true, Bool.true_and]
    congr 1
    omega_using [hj, hk, hi, h]

theorem word_ext {u v : Word} (h : ∀ j < 4, byteOf u j = byteOf v j) : u = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun b : Byte => b.getLsbD (i % 8)) (h (i / 8) (by omega_using [hi]))
  simp only [VG.Proof.Seed.getLsbD_byteOf _ (show i % 8 < 8 by omega_using []),
    show 8 * (i / 8) + i % 8 = i by omega_using []] at this
  exact this

theorem byteOf_append (z3 z2 z1 z0 : Byte) :
    byteOf (z3 ++ z2 ++ z1 ++ z0) 0 = z0 ∧ byteOf (z3 ++ z2 ++ z1 ++ z0) 1 = z1 ∧
    byteOf (z3 ++ z2 ++ z1 ++ z0) 2 = z2 ∧ byteOf (z3 ++ z2 ++ z1 ++ z0) 3 = z3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [VG.Proof.Seed.getLsbD_byteOf _ hi]
    first
      | exact (VG.Proof.Seed.getLsbD_append4 z3 z2 z1 z0 hi).1
      | exact (VG.Proof.Seed.getLsbD_append4 z3 z2 z1 z0 hi).2.1
      | exact (VG.Proof.Seed.getLsbD_append4 z3 z2 z1 z0 hi).2.2.1
      | exact (VG.Proof.Seed.getLsbD_append4 z3 z2 z1 z0 hi).2.2.2

/-- `Y`: `S1[X3] ‖ S0[X2] ‖ S1[X1] ‖ S0[X0]`. -/
def yOf (x : Word) : Word :=
  Spec.Seed.s1.getD (byteOf x 3).toNat 0 ++ Spec.Seed.s0.getD (byteOf x 2).toNat 0 ++
    Spec.Seed.s1.getD (byteOf x 1).toNat 0 ++ Spec.Seed.s0.getD (byteOf x 0).toNat 0

theorem maskBytes :
    byteOf mask0 0 = Spec.Seed.m0 ∧ byteOf mask0 1 = Spec.Seed.m2 ∧ byteOf mask0 2 = Spec.Seed.m0 ∧
    byteOf mask0 3 = Spec.Seed.m2 ∧
    byteOf mask1 0 = Spec.Seed.m3 ∧ byteOf mask1 1 = Spec.Seed.m1 ∧ byteOf mask1 2 = Spec.Seed.m3 ∧
    byteOf mask1 3 = Spec.Seed.m1 := by decide

set_option linter.unusedSimpArgs false in
/-- RFC 4269 §2.2's `Z`, from `Y` by the masks. -/
theorem g_eq_mix (x : Word) : Spec.Seed.g x = mixOf (yOf x) := by
  obtain ⟨m00, m01, m02, m03, m10, m11, m12, m13⟩ := maskBytes
  have e0 : x.setWidth 8 = byteOf x 0 := by simp [byteOf]
  have e1 : (x >>> 8).setWidth 8 = byteOf x 1 := rfl
  have e2 : (x >>> 16).setWidth 8 = byteOf x 2 := rfl
  have e3 : (x >>> 24).setWidth 8 = byteOf x 3 := rfl
  have r8 : ∀ (u : Word) (j : Nat), j < 4 → byteOf (u.rotateRight 8) j = byteOf u ((j + 1) % 4) :=
    fun u j hj => byteOf_ror u (k := 1) hj (by decide)
  have r16 : ∀ (u : Word) (j : Nat), j < 4 → byteOf (u.rotateRight 16) j = byteOf u ((j + 2) % 4) :=
    fun u j hj => byteOf_ror u (k := 2) hj (by decide)
  apply word_ext
  intro j hj
  obtain ⟨y0, y1, y2, y3⟩ := byteOf_append (Spec.Seed.s1.getD (byteOf x 3).toNat 0)
    (Spec.Seed.s0.getD (byteOf x 2).toNat 0) (Spec.Seed.s1.getD (byteOf x 1).toNat 0)
    (Spec.Seed.s0.getD (byteOf x 0).toNat 0)
  simp only [Spec.Seed.g, e0, e1, e2, e3]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_using [hj]) with rfl | rfl | rfl | rfl
  · rw [(byteOf_append _ _ _ _).1]
    simp only [mixOf, byteOf_xor, byteOf_and, r8 _ _ (by decide : 0 < 4), r16 _ _ (by decide : 0 < 4),
      r8 _ _ (by decide : 2 < 4), r8 _ _ (by decide : 1 < 4), r8 _ _ (by decide : 3 < 4), yOf, y0, y1, y2,
      y3, m00, m01, m02, m03, m10, m11, m12, m13, Nat.reduceAdd, Nat.reduceMod]
    ac_rfl
  · rw [(byteOf_append _ _ _ _).2.1]
    simp only [mixOf, byteOf_xor, byteOf_and, r8 _ _ (by decide : 0 < 4), r16 _ _ (by decide : 1 < 4),
      r8 _ _ (by decide : 2 < 4), r8 _ _ (by decide : 1 < 4), r8 _ _ (by decide : 3 < 4), yOf, y0, y1, y2,
      y3, m00, m01, m02, m03, m10, m11, m12, m13, Nat.reduceAdd, Nat.reduceMod]
    ac_rfl
  · rw [(byteOf_append _ _ _ _).2.2.1]
    simp only [mixOf, byteOf_xor, byteOf_and, r8 _ _ (by decide : 0 < 4), r16 _ _ (by decide : 2 < 4),
      r8 _ _ (by decide : 2 < 4), r8 _ _ (by decide : 1 < 4), r8 _ _ (by decide : 3 < 4), yOf, y0, y1, y2,
      y3, m00, m01, m02, m03, m10, m11, m12, m13, Nat.reduceAdd, Nat.reduceMod]
    ac_rfl
  · rw [(byteOf_append _ _ _ _).2.2.2]
    simp only [mixOf, byteOf_xor, byteOf_and, r8 _ _ (by decide : 0 < 4), r16 _ _ (by decide : 3 < 4),
      r8 _ _ (by decide : 2 < 4), r8 _ _ (by decide : 1 < 4), r8 _ _ (by decide : 3 < 4), yOf, y0, y1, y2,
      y3, m00, m01, m02, m03, m10, m11, m12, m13, Nat.reduceAdd, Nat.reduceMod]
    ac_rfl

/-! ## The constants -/

/-- What `setup` leaves, and every `g` keeps. -/
structure Consts (s : State) : Prop where
  table : ∀ k < 256, tbyte s.v k = Spec.Seed.s0.getD k 0
  lo : ∀ e < 16, vbyte (s.v .v4) e = loTable.getD e 0
  hi : ∀ e < 16, vbyte (s.v .v5) e = hiTable.getD e 0
  q64 : s.v .v6 = bc 64
  q128 : s.v .v7 = bc 128
  x14 : s.gpr .x14 = 192
  x15 : s.gpr .x15 = 15
  x16 : s.gpr .x16 = oddMask.setWidth 64
  x17 : s.gpr .x17 = mask0.setWidth 64
  x4 : s.gpr .x4 = mask1.setWidth 64

/-- The registers `g` and `f` write, but the halves. -/
def scratch : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13]

theorem Consts.of_frame {s t : State} (hc : Consts s)
    (hv : ∀ v, v ∉ [.v0, .v1, .v2, .v3] → t.v v = s.v v)
    (hg : ∀ r, r ∉ [.x0, .x1, .x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13] → t.gpr r = s.gpr r) : Consts t where
  table k hk := by
    rw [tbyte_congr' (fun j hj => hv _ (by
      have hn := treg_ne j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩)) k hk]
    exact hc.table k hk
  lo e he := by rw [hv _ (by decide)]; exact hc.lo e he
  hi e he := by rw [hv _ (by decide)]; exact hc.hi e he
  q64 := (hv _ (by decide)).trans hc.q64
  q128 := (hv _ (by decide)).trans hc.q128
  x14 := (hg _ (by decide)).trans hc.x14
  x15 := (hg _ (by decide)).trans hc.x15
  x16 := (hg _ (by decide)).trans hc.x16
  x17 := (hg _ (by decide)).trans hc.x17
  x4 := (hg _ (by decide)).trans hc.x4

/-! ## Bytes of vectors -/

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [vbyte, hi]

theorem vbyte_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 16) : vbyte (VArr.b16.map2 f x y) e = f 8 (vbyte x e) (vbyte y e) := by
  simp only [VArr.map2]
  exact vbyte_ofVBytes _ he

/-- A word in every lane: byte `e` is its byte `e mod 4`. -/
theorem vbyte_dup (x : BitVec 32) {e : Nat} (he : e < 16) :
    vbyte (ofVWords x x x x) e = byteOf x (e % 4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.Seed.getLsbD_byteOf _ hi]
  simp only [vbyte, ofVWords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
    Bool.true_and]
  rcases (show e / 4 = 0 ∨ e / 4 = 1 ∨ e / 4 = 2 ∨ e / 4 = 3 by omega_using [he]) with h | h | h | h
  · rw [ite_eq_left (by omega_using [h, hi])]
    exact congrArg _ (by omega_using [h])
  · rw [ite_eq_right (by omega_using [h]), ite_eq_left (by omega_using [h, hi])]
    exact congrArg _ (by omega_using [h])
  · rw [ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]), ite_eq_left (by omega_using [h, hi])]
    exact congrArg _ (by omega_using [h])
  · rw [ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h])]
    exact congrArg _ (by omega_using [h])

/-- The low word of a vector, by its bytes. -/
theorem byteOf_low (v : BitVec 128) {j : Nat} (hj : j < 4) : byteOf (v.extractLsb' 0 32) j = vbyte v j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.Seed.getLsbD_byteOf _ hi]
  simp only [vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add,
    show 8 * j + i < 32 by omega_using [hj, hi]]

theorem oddMask_bytes : ∀ e < 16,
    vbyte (ofVWords oddMask oddMask oddMask oddMask) e = if e % 2 = 1 then 255 else 0 := by decide

theorem nibbles : ∀ y : Byte, (y &&& 15).toNat = y.toNat % 16 ∧ (y >>> 4).toNat = y.toNat / 16 := by decide

theorem byte_select (x y : Byte) : x ^^^ ((x ^^^ y) &&& 0) = x ∧ x ^^^ ((x ^^^ y) &&& 255) = y := by
  refine ⟨by simp, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h255 : (255 : Byte).getLsbD i = true :=
    (by decide : ∀ i < 8, (255 : Byte).getLsbD i = true) i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, h255, Bool.and_true]
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

/-! ## `g` -/

theorem indices_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa indices s = some t ∧
      (∀ e < 16, vbyte (t.v .v0) e = byteOf ((s.gpr .x10).setWidth 32) (e % 4)) ∧
      (∀ e < 16, vbyte (t.v .v1) e = vbyte (t.v .v0) e ^^^ 64) ∧
      (∀ e < 16, vbyte (t.v .v2) e = vbyte (t.v .v0) e ^^^ 128) ∧
      (∀ e < 16, vbyte (t.v .v3) e = vbyte (t.v .v0) e ^^^ 192) ∧
      VOnly [.v0, .v1, .v2, .v3] s t := by
  let x := (s.gpr .x10).setWidth 32
  let a := s.setV .v0 (ofVWords x x x x)
  let b := a.setV .v1 (a.v .v0 ^^^ a.v .v6)
  let c := b.setV .v2 (b.v .v0 ^^^ b.v .v7)
  let d := c.setV .v3 (bc ((c.gpr .x14).setWidth 8))
  let e := d.setV .v3 (d.v .v0 ^^^ d.v .v3)
  have h0 : e.v .v0 = ofVWords x x x x := by simp [e, d, c, b, a, State.setV]
  have h1 : e.v .v1 = ofVWords x x x x ^^^ bc 64 := by simp [e, d, c, b, a, State.setV, hc.q64]
  have h2 : e.v .v2 = ofVWords x x x x ^^^ bc 128 := by simp [e, d, c, b, a, State.setV, hc.q128]
  have h3 : e.v .v3 = ofVWords x x x x ^^^ bc 192 := by
    have h14 : c.gpr .x14 = 192 := hc.x14
    simp only [e, d, h14]
    simp [c, b, a, State.setV]
  refine ⟨e, ?_, fun k hk => by rw [h0, vbyte_dup _ hk], ?_, ?_, ?_, ?_⟩
  · simp only [indices, runBlock_cons]
    change (exec (.vop (.dup .s4 .v0 .x10)) s).bind _ = _
    rw [show exec (.vop (.dup .s4 .v0 .x10)) s = some a from rfl]
    simp only [Option.bind_some, exec_eorv, exec_dupb, runStep_some, runBlock_cons, runBlock_nil]
    rfl
  · intro k hk; rw [h1, h0, vbyte_xor, vbyte_bc _ hk]
  · intro k hk; rw [h2, h0, vbyte_xor, vbyte_bc _ hk]
  · intro k hk; rw [h3, h0, vbyte_xor, vbyte_bc _ hk]
  · exact (((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      ((VOnly.setV b (by simp) _).trans (VOnly.setV c (by simp) _))).trans (VOnly.setV d (by simp) _)

theorem affine_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa affine s = some t ∧
      (∀ k < 16, vbyte (t.v .v0) k =
        if k % 2 = 1 then affOf (vbyte (s.v .v0) k) else vbyte (s.v .v0) k) ∧
      VOnly [.v0, .v1, .v2] s t := by
  let a1 := s.setV .v1 (bc ((s.gpr .x15).setWidth 8))
  let a2 := a1.setV .v1 (a1.v .v0 &&& a1.v .v1)
  let a3 := a2.setV .v2 (VArr.b16.map2 (fun w x y => VShiftOp.ushr.eval 4 w x y) (a2.v .v2) (a2.v .v0))
  let a4 := a3.setV .v1 (ofVBytes fun i =>
    let idx := (vbyte (a3.v .v1) i).toNat
    if idx < 16 then vbyte (a3.v .v4) idx else 0)
  let a5 := a4.setV .v2 (ofVBytes fun i =>
    let idx := (vbyte (a4.v .v2) i).toNat
    if idx < 16 then vbyte (a4.v .v5) idx else 0)
  let a6 := a5.setV .v1 (a5.v .v1 ^^^ a5.v .v2)
  let m := (a6.gpr .x16).setWidth 32
  let a7 := a6.setV .v2 (ofVWords m m m m)
  let a8 := a7.setV .v0 (VSelOp.bit.eval (a7.v .v0) (a7.v .v1) (a7.v .v2))
  have hm : m = oddMask := by
    have h16 : a6.gpr .x16 = oddMask.setWidth 64 := hc.x16
    simp only [m, h16, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have h15 : (s.gpr .x15).setWidth 8 = 15 := by rw [hc.x15]; rfl
  refine ⟨a8, ?_, ?_, ?_⟩
  · simp only [affine, runBlock_cons]
    rw [exec_dupb]
    simp only [runStep_some, runBlock_cons]
    rw [show exec (.vop (.logic .and .v1 .v0 .v1)) a1 = some a2 from rfl]
    simp only [runStep_some, runBlock_cons]
    rw [show exec (.vop (.shift .ushr .b16 .v2 .v0 4)) a2 = some a3 from rfl]
    simp only [runStep_some, runBlock_cons]
    rw [show exec (.vop (.tbl .v1 .v4 .v1)) a3 = some a4 from rfl]
    simp only [runStep_some, runBlock_cons]
    rw [show exec (.vop (.tbl .v2 .v5 .v2)) a4 = some a5 from rfl]
    simp only [runStep_some, runBlock_cons, exec_eorv]
    rw [show exec (.vop (.dup .s4 .v2 .x16)) a6 = some a7 from rfl]
    simp only [runStep_some, runBlock_cons]
    rfl
  · intro k hk
    let y := vbyte (s.v .v0) k
    have i1 : vbyte (a3.v .v1) k = y &&& 15 := by
      simp only [a3, a2, a1, State.setV, ite_true, show (.v1 : VReg) ≠ .v2 by decide,
        show (.v0 : VReg) ≠ .v1 by decide, ite_false, vbyte_and, h15, vbyte_bc _ hk, y]
    have i2 : vbyte (a4.v .v2) k = y >>> 4 := by
      simp only [a4, a3, a2, a1, State.setV, ite_true, show (.v2 : VReg) ≠ .v1 by decide,
        show (.v0 : VReg) ≠ .v1 by decide, ite_false, vbyte_map2 _ _ _ hk, VShiftOp.eval, y]
    have t1 : vbyte (a8.v .v1) k = affOf y := by
      have e1 : a8.v .v1 = a4.v .v1 ^^^ a5.v .v2 := by
        simp [a8, a7, a6, a5, State.setV]
      have e2 : a4.v .v1 = ofVBytes fun i =>
          let idx := (vbyte (a3.v .v1) i).toNat
          if idx < 16 then vbyte (a3.v .v4) idx else 0 := by simp [a4, State.setV]
      have e3 : a5.v .v2 = ofVBytes fun i =>
          let idx := (vbyte (a4.v .v2) i).toNat
          if idx < 16 then vbyte (a4.v .v5) idx else 0 := by simp [a5, State.setV]
      have e4 : a3.v .v4 = s.v .v4 := by simp [a3, a2, a1, State.setV]
      have e5 : a4.v .v5 = s.v .v5 := by simp [a4, a3, a2, a1, State.setV]
      rw [e1, vbyte_xor, e2, e3, vbyte_ofVBytes _ hk, vbyte_ofVBytes _ hk]
      simp only [i1, i2, (nibbles y).1, (nibbles y).2, e4, e5]
      rw [ite_eq_left (Nat.mod_lt _ (by decide)), ite_eq_left (by omega_using [y.isLt]),
        hc.lo _ (Nat.mod_lt _ (by decide)), hc.hi _ (by omega_using [y.isLt])]
      rfl
    have t0 : a7.v .v0 = s.v .v0 := by simp [a7, a6, a5, a4, a3, a2, a1, State.setV]
    have t2 : a7.v .v2 = ofVWords oddMask oddMask oddMask oddMask := by
      simp only [a7, State.setV, ite_true, hm]
    have t1' : a7.v .v1 = a8.v .v1 := by simp [a8, State.setV]
    have e8 : a8.v .v0 = VSelOp.bit.eval (a7.v .v0) (a7.v .v1) (a7.v .v2) := by simp [a8, State.setV]
    rw [e8, t0, t2, t1']
    simp only [VSelOp.eval, vbyte_xor, vbyte_and, t1, oddMask_bytes k hk]
    split
    · exact (byte_select _ _).2
    · exact (byte_select _ _).1
  · exact ((((VOnly.setV s (by simp) _).trans (VOnly.setV a1 (by simp) _)).trans
      ((VOnly.setV a2 (by simp) _).trans (VOnly.setV a3 (by simp) _))).trans
      ((VOnly.setV a4 (by simp) _).trans (VOnly.setV a5 (by simp) _))).trans
      ((VOnly.setV a6 (by simp) _).trans (VOnly.setV a7 (by simp) _))

theorem mix_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa mix s = some t ∧
      t.gpr .x10 = (mixOf ((s.gpr .x10).setWidth 32)).setWidth 64 ∧
      (∀ r, r ∉ [.x10, .x11, .x12, .x13] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a1 := s.write .w .x11 (s.read .w .x10 &&& s.read .w .x17)
  let a2 := a1.write .w .x12 (a1.read .w .x10 &&& a1.read .w .x4)
  let a3 := a2.write .w .x11 (a2.read .w .x11 ^^^ (a2.read .w .x12).rotateRight 8)
  let a4 := a3.write .w .x12 (a3.read .w .x10 &&& (a3.read .w .x17).rotateRight 8)
  let a5 := a4.write .w .x13 (a4.read .w .x10 &&& (a4.read .w .x4).rotateRight 8)
  let a6 := a5.write .w .x12 (a5.read .w .x12 ^^^ (a5.read .w .x13).rotateRight 8)
  let a7 := a6.write .w .x10 (a6.read .w .x11 ^^^ (a6.read .w .x12).rotateRight 16)
  refine ⟨a7, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [mix, runBlock_cons, exec_logic, exec_logicRor (sz := .w) (sh := 8) (by decide),
      exec_logicRor (sz := .w) (sh := 16) (by decide), runStep_some, runBlock_nil]
    rfl
  · simp only [a7, a6, a5, a4, a3, a2, a1, gpr_write_self, State.read, Size.bits,
      gpr_write_of_ne _ _ _ (show ¬(Reg.x10 = .x11) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x10 = .x12) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x17 = .x11) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x17 = .x12) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x4 = .x11) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x4 = .x12) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x11 = .x12) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x11 = .x13) by decide),
      gpr_write_of_ne _ _ _ (show ¬(Reg.x12 = .x13) by decide),
      hc.x17, hc.x4,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [a7, a6, a5, a4, a3, a2, a1, gpr_write_of_ne _ _ _ hr.1, gpr_write_of_ne _ _ _ hr.2.1,
      gpr_write_of_ne _ _ _ hr.2.2.1, gpr_write_of_ne _ _ _ hr.2.2.2]

/-- `x10 := G(x10)`. -/
theorem g_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa g s = some t ∧
      t.gpr .x10 = (Spec.Seed.g ((s.gpr .x10).setWidth 32)).setWidth 64 ∧
      (∀ r, r ∉ [.x10, .x11, .x12, .x13] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ∉ [.v0, .v1, .v2, .v3] → t.v v = s.v v) := by
  let x := (s.gpr .x10).setWidth 32
  obtain ⟨a, ae, a0, a1, a2, a3, av⟩ := indices_run s hc
  have atab : ∀ k < 256, tbyte a.v k = Spec.Seed.s0.getD k 0 := fun k hk => by
    rw [tbyte_congr' (fun j hj => av.2 _ (by
      have hn := treg_ne j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩)) k hk]
    exact hc.table k hk
  obtain ⟨b, be, bo, bv⟩ := select_full_run (s := a) (fun e => byteOf x (e % 4)) a0
    (fun e he => by rw [a1 e he, a0 e he]) (fun e he => by rw [a2 e he, a0 e he])
    (fun e he => by rw [a3 e he, a0 e he])
  have sb : VOnly [.v0, .v1, .v2, .v3] s b := av.trans bv
  have bc' : Consts b := hc.of_frame sb.2 (fun r _ => by rw [sb.gpr])
  obtain ⟨c, ce, co, cv⟩ := affine_run b bc'
  have cv4 : VOnly [.v0, .v1, .v2, .v3] b c :=
    ⟨cv.1, fun v hv => cv.2 v (fun h => hv (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))))⟩
  have sc : VOnly [.v0, .v1, .v2, .v3] s c := sb.trans cv4
  let d := c.write .w .x10 ((c.v .v0).extractLsb' 0 32)
  have dc : Consts d := hc.of_frame (fun v hv => sc.2 v hv) (fun r hr => by
    rw [gpr_write_of_ne _ _ _ (fun h => hr (by simp [h])), sc.gpr])
  obtain ⟨e, ee, ev, eg, em, erd, ewr, esp, evec⟩ := mix_run d dc
  have word : (c.v .v0).extractLsb' 0 32 = yOf x := by
    apply word_ext
    intro j hj
    obtain ⟨y0, y1, y2, y3⟩ := byteOf_append (Spec.Seed.s1.getD (byteOf x 3).toNat 0)
      (Spec.Seed.s0.getD (byteOf x 2).toNat 0) (Spec.Seed.s1.getD (byteOf x 1).toNat 0)
      (Spec.Seed.s0.getD (byteOf x 0).toNat 0)
    rw [byteOf_low _ hj, co j (by omega_using [hj]), bo j (by omega_using [hj]), atab _ (byteOf x (j % 4)).isLt]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_using [hj]) with rfl | rfl | rfl | rfl
    · exact y0.symm
    · exact (aff_ok _).trans y1.symm
    · exact y2.symm
    · exact (aff_ok _).trans y3.symm
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g, List.append_assoc, List.append_assoc, List.append_assoc, VG.Interleave.runBlock_append, ae,
      Option.bind_some, VG.Interleave.runBlock_append, be, Option.bind_some,
      VG.Interleave.runBlock_append, ce, Option.bind_some, List.singleton_append, runBlock_cons]
    rw [show exec (.umov .w .x10 .v0 0) c = some d by simp [exec, Size.bits, d]]
    rw [runStep_some, ee]
  · rw [ev]
    simp only [d, gpr_write_self, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq, word, g_eq_mix]
    rfl
  · intro r hr
    rw [eg r hr, gpr_write_of_ne _ _ _ (fun h => hr (by simp [h])), sc.gpr]
  · rw [em]; exact sc.mem
  · rw [erd]; exact sc.rd
  · rw [ewr]; exact sc.wr
  · rw [esp]
    change c.sp = s.sp
    rw [sc.1]
  · intro v hv
    rw [evec]
    exact sc.2 v hv

/-! ## `F` -/

/-- The low word of a register. -/
abbrev wd (s : State) (r : Reg) : BitVec 32 := (s.gpr r).setWidth 32

theorem halves_ne : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], r ≠ .x5 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧
    r ∉ [Reg.x10, .x11, .x12, .x13] ∧ r ∉ scratch := by decide

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

/-- The round key XORed with the right half: `a` in `x8`, `a ⊕ b` in `x10`. -/
theorem fHead_run {s : State} {r0 r1 : Reg} {koff : Nat} (h0 : r0 ∈ [Reg.x0, .x1, .x2, .x3])
    (h1 : r1 ∈ [Reg.x0, .x1, .x2, .x3]) (ho : koff % 4 = 0 ∧ koff + 4 < 16384)
    (hr0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 koff) 4)
    (hr1 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 4) :
    ∃ t, runBlock isa [.ldr .w .x8 .x5 koff, .logic .eor .w .x8 .x8 r0, .ldr .w .x10 .x5 (koff + 4),
        .logic .eor .w .x10 .x10 r1, .logic .eor .w .x10 .x10 .x8] s = some t ∧
      wd t .x8 = wd s r0 ^^^ s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 koff) 32 ∧
      wd t .x10 = (wd s r0 ^^^ s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 koff) 32) ^^^
        (wd s r1 ^^^ s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 32) ∧
      (∀ r, r ≠ .x8 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  obtain ⟨-, n8, -, n10, -, -⟩ := halves_ne r0 h0
  obtain ⟨-, m8, -, m10, -, -⟩ := halves_ne r1 h1
  let a1 := s.write .w .x8 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 koff) 32)
  let a2 := a1.write .w .x8 (a1.read .w .x8 ^^^ a1.read .w r0)
  let a3 := a2.write .w .x10 (a2.mem.readW (a2.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 32)
  let a4 := a3.write .w .x10 (a3.read .w .x10 ^^^ a3.read .w r1)
  let a5 := a4.write .w .x10 (a4.read .w .x10 ^^^ a4.read .w .x8)
  have b5 : a2.gpr .x5 = s.gpr .x5 := by
    simp only [a2, a1, gpr_write_of_ne _ _ _ (show ¬(Reg.x5 = .x8) by decide)]
  have e8 : wd a5 .x8 = wd s r0 ^^^ s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 koff) 32 := by
    simp only [wd, a5, a4, a3, a2, a1, gpr_write_self, State.read, Size.bits, sw32,
      gpr_write_of_ne _ _ _ (show ¬(Reg.x8 = .x10) by decide), gpr_write_of_ne _ _ _ n8]
    exact BitVec.xor_comm _ _
  refine ⟨a5, ?_, e8, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_ldr_w ⟨ho.1, by omega_using [ho.2]⟩ hr0, runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_cons, exec_ldr_w ⟨by omega_using [ho.1], ho.2⟩ (by
        change InRegions (s.rd ++ s.wr) (a2.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 4
        rw [b5]; exact hr1), runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_nil]
  · have e10 : wd a5 .x10 = (wd a4 .x10) ^^^ wd a5 .x8 := by
      simp only [wd, a5, gpr_write_self, State.read, Size.bits, sw32,
        gpr_write_of_ne _ _ _ (show ¬(Reg.x8 = .x10) by decide)]
    have e4 : wd a4 .x10 = wd s r1 ^^^ s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 32 := by
      simp only [wd, a4, a3, gpr_write_self, State.read, Size.bits, sw32, b5, gpr_write_of_ne _ _ _ m10]
      simp only [a2, a1, gpr_write_of_ne _ _ _ m8, mem_write]
      exact BitVec.xor_comm _ _
    rw [e10, e4, e8]
    exact BitVec.xor_comm _ _
  · intro r h8 h10
    simp only [a5, a4, a3, a2, a1, gpr_write_of_ne _ _ _ h8, gpr_write_of_ne _ _ _ h10]

/-- `d := x10`, `x10 := x10 + o`. -/
theorem fStep_run (s : State) {d o : Reg} (hd : d ≠ .x10) (ho : o ≠ d) :
    ∃ t, runBlock isa [.addImm .x d .x10 0, .add .w .x10 .x10 o] s = some t ∧
      t.gpr d = s.gpr .x10 ∧ wd t .x10 = wd s .x10 + wd s o ∧
      (∀ r, r ≠ d → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a1 := s.write .x d (s.read .x .x10 + BitVec.ofNat _ 0)
  let a2 := a1.write .w .x10 (a1.read .w .x10 + a1.read .w o)
  refine ⟨a2, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_add, runStep_some,
      runBlock_nil]
  · simp only [a2, a1, gpr_write_of_ne _ _ _ hd, gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]
    exact BitVec.add_zero _
  · simp only [wd, a2, a1, gpr_write_self, State.read, Size.bits, sw32, gpr_write_of_ne _ _ _ (Ne.symm hd),
      gpr_write_of_ne _ _ _ ho]
  · intro r h1 h2
    simp only [a2, a1, gpr_write_of_ne _ _ _ h1, gpr_write_of_ne _ _ _ h2]

/-- `(l0, l1) := (l0, l1) ⊕ F(K, (r0, r1))`. -/
theorem f_run {s : State} {l0 l1 r0 r1 : Reg} {koff : Nat} (hc : Consts s)
    (hl0 : l0 ∈ [Reg.x0, .x1, .x2, .x3]) (hl1 : l1 ∈ [Reg.x0, .x1, .x2, .x3])
    (h0 : r0 ∈ [Reg.x0, .x1, .x2, .x3]) (h1 : r1 ∈ [Reg.x0, .x1, .x2, .x3]) (hne : l0 ≠ l1)
    (ho : koff % 4 = 0 ∧ koff + 4 < 16384)
    (hr0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 koff) 4)
    (hr1 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 4) :
    ∃ t, runBlock isa (f l0 l1 r0 r1 koff) s = some t ∧
      wd t l0 = wd s l0 ^^^ (Spec.Seed.f (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 koff) 32)
        (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 32) (wd s r0) (wd s r1)).1 ∧
      wd t l1 = wd s l1 ^^^ (Spec.Seed.f (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 koff) 32)
        (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 32) (wd s r0) (wd s r1)).2 ∧
      (∀ r, r ≠ l0 → r ≠ l1 → r ∉ scratch → t.gpr r = s.gpr r) ∧
      Consts t ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨-, p8, p9, p10, pg, -⟩ := halves_ne l0 hl0
  obtain ⟨-, q8, q9, q10, qg, -⟩ := halves_ne l1 hl1
  let k0 := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 koff) 32
  let k1 := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (koff + 4)) 32
  let a := wd s r0 ^^^ k0
  let b := wd s r1 ^^^ k1
  let c := Spec.Seed.g (a ^^^ b)
  let d := Spec.Seed.g (c + a)
  let e := Spec.Seed.g (d + c)
  -- the head
  obtain ⟨s1, x1, a8, a10, ag, am, ard, awr, asp, av⟩ := fHead_run (s := s) h0 h1 ho hr0 hr1
  have c1 : Consts s1 := hc.of_frame (fun v _ => by rw [av]) (fun r hr => ag r (fun h => hr (by simp [h]))
    (fun h => hr (by simp [h])))
  -- `c`
  obtain ⟨s2, x2, b10, bg, bm, brd, bwr, bsp, bv⟩ := g_run s1 c1
  have c2 : Consts s2 := c1.of_frame bv (fun r hr => bg r (fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h <;> simp [h])))
  have s2_8 : wd s2 .x8 = a := by rw [wd, bg _ (by decide)]; exact a8
  have s2_10 : wd s2 .x10 = c := by rw [wd, b10, sw32]; exact congrArg Spec.Seed.g a10
  obtain ⟨s3, x3, d9, d10, dg, dm, drd, dwr, dsp, dv⟩ := fStep_run s2 (d := .x9) (o := .x8) (by decide)
    (by decide)
  have c3 : Consts s3 := c2.of_frame (fun v _ => by rw [dv]) (fun r hr => dg r (fun h => hr (by simp [h]))
    (fun h => hr (by simp [h])))
  have s3_10 : wd s3 .x10 = c + a := by rw [d10, s2_10, s2_8]
  have s3_9 : wd s3 .x9 = c := by rw [wd, d9]; exact s2_10
  have s3_8 : wd s3 .x8 = a := by rw [wd, dg _ (by decide) (by decide)]; exact s2_8
  -- `d`
  obtain ⟨s4, x4, e10, eg, em, erd, ewr, esp, ev⟩ := g_run s3 c3
  have c4 : Consts s4 := c3.of_frame ev (fun r hr => eg r (fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h <;> simp [h])))
  have s4_10 : wd s4 .x10 = d := by rw [wd, e10, sw32]; exact congrArg Spec.Seed.g s3_10
  have s4_9 : wd s4 .x9 = c := by rw [wd, eg _ (by decide)]; exact s3_9
  obtain ⟨s5, x5, f8, f10, fg, fm, frd, fwr, fsp, fv⟩ := fStep_run s4 (d := .x8) (o := .x9) (by decide)
    (by decide)
  have c5 : Consts s5 := c4.of_frame (fun v _ => by rw [fv]) (fun r hr => fg r (fun h => hr (by simp [h]))
    (fun h => hr (by simp [h])))
  have s5_10 : wd s5 .x10 = d + c := by rw [f10, s4_10, s4_9]
  have s5_8 : wd s5 .x8 = d := by rw [wd, f8]; exact s4_10
  -- `e`
  obtain ⟨s6, x6, g10, gg, gm, grd, gwr, gsp, gv⟩ := g_run s5 c5
  have c6 : Consts s6 := c5.of_frame gv (fun r hr => gg r (fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h <;> simp [h])))
  have s6_10 : wd s6 .x10 = e := by rw [wd, g10, sw32]; exact congrArg Spec.Seed.g s5_10
  have s6_8 : wd s6 .x8 = d := by rw [wd, gg _ (by decide)]; exact s5_8
  -- the halves through all this
  have keep : ∀ r, r ∈ [Reg.x0, .x1, .x2, .x3] → s6.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, r8, r9, r10, rg, -⟩ := halves_ne r hr
    rw [gg r rg, fg r r8 r10, eg r rg, dg r r9 r10, bg r rg, ag r r8 r10]
  -- the tail
  let t1 := s6.write .w l1 (s6.read .w l1 ^^^ s6.read .w .x10)
  let t2 := t1.write .w .x10 (t1.read .w .x10 + t1.read .w .x8)
  let t3 := t2.write .w l0 (t2.read .w l0 ^^^ t2.read .w .x10)
  have fe : Spec.Seed.f k0 k1 (wd s r0) (wd s r1) = (e + d, e) := rfl
  refine ⟨t3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f]
    simp only [List.append_assoc]
    rw [VG.Interleave.runBlock_append, x1, Option.bind_some,
      VG.Interleave.runBlock_append, x2, Option.bind_some, VG.Interleave.runBlock_append, x3,
      Option.bind_some, VG.Interleave.runBlock_append, x4, Option.bind_some,
      VG.Interleave.runBlock_append, x5, Option.bind_some, VG.Interleave.runBlock_append, x6,
      Option.bind_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_add, runStep_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_nil]
  · rw [fe]
    simp only [wd, t3, t2, t1, gpr_write_self, State.read, Size.bits, sw32, gpr_write_of_ne _ _ _ p10,
      gpr_write_of_ne _ _ _ hne, gpr_write_of_ne _ _ _ (Ne.symm q10), gpr_write_of_ne _ _ _ (Ne.symm q8)]
    rw [show BitVec.setWidth 32 (s6.gpr l0) = wd s l0 by rw [keep l0 hl0],
      show BitVec.setWidth 32 (s6.gpr .x10) = e from s6_10,
      show BitVec.setWidth 32 (s6.gpr .x8) = d from s6_8]
  · rw [fe]
    simp only [wd, t3, t2, t1, gpr_write_self, State.read, Size.bits, sw32, gpr_write_of_ne _ _ _ q10,
      gpr_write_of_ne _ _ _ (Ne.symm hne)]
    rw [show BitVec.setWidth 32 (s6.gpr l1) = wd s l1 by rw [keep l1 hl1],
      show BitVec.setWidth 32 (s6.gpr .x10) = e from s6_10]
  · intro r hl hl' hs
    have r8 : r ≠ .x8 := fun h => hs (by simp [scratch, h])
    have r9 : r ≠ .x9 := fun h => hs (by simp [scratch, h])
    have r10 : r ≠ .x10 := fun h => hs (by simp [scratch, h])
    have rg : r ∉ [Reg.x10, .x11, .x12, .x13] := fun h => hs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> simp [scratch, h])
    simp only [t3, t2, t1, gpr_write_of_ne _ _ _ hl, gpr_write_of_ne _ _ _ hl', gpr_write_of_ne _ _ _ r10]
    rw [gg r rg, fg r r8 r10, eg r rg, dg r r9 r10, bg r rg, ag r r8 r10]
  · exact c6.of_frame (fun v _ => rfl) (fun r hr => by
      have rl0 : r ≠ l0 := fun h => hr (by
        subst h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl0 ⊢
        rcases hl0 with h | h | h | h <;> simp [h])
      have rl1 : r ≠ l1 := fun h => hr (by
        subst h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 ⊢
        rcases hl1 with h | h | h | h <;> simp [h])
      have r10 : r ≠ .x10 := fun h => hr (by simp [h])
      simp only [t3, t2, t1, gpr_write_of_ne _ _ _ rl0, gpr_write_of_ne _ _ _ rl1, gpr_write_of_ne _ _ _ r10])
  · exact gm.trans (fm.trans (em.trans (dm.trans (bm.trans am))))
  · exact grd.trans (frd.trans (erd.trans (drd.trans (brd.trans ard))))
  · exact gwr.trans (fwr.trans (ewr.trans (dwr.trans (bwr.trans awr))))
  · exact gsp.trans (fsp.trans (esp.trans (dsp.trans (bsp.trans asp))))

/-! ## The rounds -/

open VG.Proof.Seed (Quad roundsN roundsN_succ decodeQ encodeSwapped)

/-- The block's words. -/
def quadOf (s : State) : Quad := (wd s .x0, wd s .x1, wd s .x2, wd s .x3)

/-- Round `i + 1`'s key, at `x5 + keyOff`. -/
def rk (m : Mem) (p : Addr) (keyOff i : Nat) : Word × Word :=
  (m.readW (p + BitVec.ofNat 64 (keyOff + 8 * i)) 32, m.readW (p + BitVec.ofNat 64 (keyOff + 8 * i + 4)) 32)

/-- The registers the rounds write. -/
def written : List Reg := [.x0, .x1, .x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13]

theorem round2_run {s : State} {keyOff j : Nat} (hc : Consts s) (hj : j < 8)
    (hk : keyOff % 4 = 0 ∧ keyOff + 128 < 16384)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (keyOff + 4 * i)) 4) :
    ∃ t, runBlock isa (round2 keyOff j) s = some t ∧
      quadOf t = Spec.Seed.round (rk s.mem (s.gpr .x5) keyOff (2 * j + 1))
        (Spec.Seed.round (rk s.mem (s.gpr .x5) keyOff (2 * j)) (quadOf s)) ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      Consts t ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e1 : keyOff + 16 * j = keyOff + 8 * (2 * j) := by omega_using []
  have e2 : keyOff + 8 * (2 * j) + 8 = keyOff + 8 * (2 * j + 1) := by omega_using []
  have a0 : keyOff + 8 * (2 * j) = keyOff + 4 * (4 * j) := by omega_using []
  have a1 : keyOff + 8 * (2 * j) + 4 = keyOff + 4 * (4 * j + 1) := by omega_using []
  have a2 : keyOff + 8 * (2 * j + 1) = keyOff + 4 * (4 * j + 2) := by omega_using []
  have a3 : keyOff + 8 * (2 * j + 1) + 4 = keyOff + 4 * (4 * j + 3) := by omega_using []
  obtain ⟨u, ue, u0, u1, ug, uc, um, urd, uwr, usp⟩ := f_run (s := s) (l0 := .x0) (l1 := .x1) (r0 := .x2)
    (r1 := .x3) (koff := keyOff + 8 * (2 * j)) hc (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨by omega_using [hk.1], by omega_using [hk.2, hj]⟩ (by rw [a0]; exact hr _ (by omega_using [hj]))
    (by rw [a1]; exact hr _ (by omega_using [hj]))
  have u5 : u.gpr .x5 = s.gpr .x5 := ug _ (by decide) (by decide) (by decide)
  obtain ⟨t, te, t2, t3, tg, tc, tm, trd, twr, tsp⟩ := f_run (s := u) (l0 := .x2) (l1 := .x3) (r0 := .x0)
    (r1 := .x1) (koff := keyOff + 8 * (2 * j + 1)) uc (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨by omega_using [hk.1], by omega_using [hk.2, hj]⟩
    (by rw [urd, uwr, u5, a2]; exact hr _ (by omega_using [hj]))
    (by rw [urd, uwr, u5, a3]; exact hr _ (by omega_using [hj]))
  refine ⟨t, ?_, ?_, ?_, tc, tm.trans um, trd.trans urd, twr.trans uwr, tsp.trans usp⟩
  · rw [round2, e1, e2, VG.Interleave.runBlock_append, ue, Option.bind_some, te]
  · have k2 : wd u .x2 = wd s .x2 := by rw [wd, ug _ (by decide) (by decide) (by decide)]
    have k3 : wd u .x3 = wd s .x3 := by rw [wd, ug _ (by decide) (by decide) (by decide)]
    have k0 : wd t .x0 = wd u .x0 := by rw [wd, tg _ (by decide) (by decide) (by decide)]
    have k1 : wd t .x1 = wd u .x1 := by rw [wd, tg _ (by decide) (by decide) (by decide)]
    rw [um, u5, k2] at t2
    rw [um, u5, k3] at t3
    simp only [quadOf, rk, Spec.Seed.round]
    rw [k0, k1, t2, t3, u0, u1]
  · intro r hr'
    have h : r ∉ scratch := fun h => hr' (by
      simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h <;> simp [written, h])
    rw [tg r (fun h => hr' (by simp [written, h])) (fun h => hr' (by simp [written, h])) h,
      ug r (fun h => hr' (by simp [written, h])) (fun h => hr' (by simp [written, h])) h]

theorem rounds_run (s : State) (keyOff n : Nat) (hn : n ≤ 8) (hc : Consts s)
    (hk : keyOff % 4 = 0 ∧ keyOff + 128 < 16384)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (keyOff + 4 * i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap (round2 keyOff)) s = some t ∧
      quadOf t = roundsN (rk s.mem (s.gpr .x5) keyOff) (2 * n) (quadOf s) ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      Consts t ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact ⟨s, rfl, rfl, fun _ _ => rfl, hc, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aq, ag, ac, am, ard, awr, asp⟩ := ih (by omega_using [hn])
    have a5 : a.gpr .x5 = s.gpr .x5 := ag _ (by decide)
    obtain ⟨b, be, bq, bg, bc, bm, brd, bwr, bsp⟩ := round2_run (s := a) (keyOff := keyOff) (j := n) ac
      (by omega_using [hn]) hk (fun i hi => by rw [ard, awr, a5]; exact hr i hi)
    refine ⟨b, ?_, ?_, fun r hr' => (bg r hr').trans (ag r hr'), bc, bm.trans am, brd.trans ard,
      bwr.trans awr, bsp.trans asp⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · rw [bq, am, a5, aq, show 2 * (n + 1) = 2 * n + 1 + 1 by omega_using [], roundsN_succ, roundsN_succ]

/-! ## The constants set -/

theorem mid_run (s : State) :
    ∃ t, runBlock isa [.movz .w .x15 64 0, .vop (.dup .b16 .v6 .x15), .movz .w .x15 128 0,
        .vop (.dup .b16 .v7 .x15), .movz .w .x14 192 0, .movz .w .x15 15 0] s = some t ∧
      t.v .v6 = bc 64 ∧ t.v .v7 = bc 128 ∧ t.gpr .x14 = 192 ∧ t.gpr .x15 = 15 ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ≠ .v6 → v ≠ .v7 → t.v v = s.v v) := by
  let a1 := s.write .w .x15 64
  let a2 := a1.setV .v6 (bc 64)
  let a3 := a2.write .w .x15 128
  let a4 := a3.setV .v7 (bc 128)
  let a5 := a4.write .w .x14 192
  let a6 := a5.write .w .x15 15
  refine ⟨a6, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp [a6, a5, a4, a3, a2, State.setV, State.write]
  · simp [a6, a5, a4, State.setV, State.write]
  · simp [a6, a5, State.write]
    rfl
  · simp [a6, State.write]
    rfl
  · intro r h14 h15
    simp only [a6, a5, a4, a3, a2, a1, gpr_setV, gpr_write_of_ne _ _ _ h14, gpr_write_of_ne _ _ _ h15]
  · intro v h6 h7
    simp only [a6, a5, a4, a3, a2, a1, v_write, v_setV_of_ne _ _ h6, v_setV_of_ne _ _ h7]

/-- The registers `setup` writes. -/
def setupRegs : List Reg := [.x4, .x6, .x7, .x14, .x15, .x16, .x17]

theorem setup_wp (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧ (∀ r, r ∉ setupRegs → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadTable_ok s _) fun a ⟨atab, av, ag, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const128_ok a .v4 _) fun b ⟨b4, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const128_ok b .v5 _) fun c ⟨c5, cv, cg, cm, crd, cwr, csp⟩ => ?_
  obtain ⟨d, de, d6, d7, d14, d15, dg, dm, drd, dwr, dsp, dv⟩ := mid_run c
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨d, de, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok d .x16 _) fun e ⟨e16, eg, ee⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok e .x17 _) fun f ⟨f17, fg, fe⟩ => ?_
  refine WP.mono (const64_ok f .x4 _) fun t ⟨t4, tg, te⟩ => ?_
  have tv : t.v = d.v := by rw [te, fe, ee]
  have tmem : t.mem = d.mem := by rw [te, fe, ee]
  have trd : t.rd = d.rd := by rw [te, fe, ee]
  have twr : t.wr = d.wr := by rw [te, fe, ee]
  have tsp : t.sp = d.sp := by rw [te, fe, ee]
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, t4⟩, fun r hr => ?_,
    tmem.trans (dm.trans (cm.trans (bm.trans am))), trd.trans (drd.trans (crd.trans (brd.trans ard))),
    twr.trans (dwr.trans (cwr.trans (bwr.trans awr))), tsp.trans (dsp.trans (csp.trans (bsp.trans asp)))⟩
  · rw [tv, tbyte_congr' (fun j hj => by
      have hn := treg_ne8 j hj
      rw [dv _ hn.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2, cv _ hn.2.2.2.2.2.1, bv _ hn.2.2.2.2.1]) k hk]
    exact atab k hk
  · rw [tv, dv _ (by decide) (by decide), cv _ (by decide), b4]
    exact vbyte_ofVBytes _ hk
  · rw [tv, dv _ (by decide) (by decide), c5]
    exact vbyte_ofVBytes _ hk
  · rw [tv]; exact d6
  · rw [tv]; exact d7
  · rw [tg _ (by decide), fg _ (by decide), eg _ (by decide)]; exact d14
  · rw [tg _ (by decide), fg _ (by decide), eg _ (by decide)]; exact d15
  · rw [tg _ (by decide), fg _ (by decide)]; exact e16
  · rw [tg _ (by decide)]; exact f17
  · have n4 : r ≠ .x4 := fun h => hr (by simp [setupRegs, h])
    have n6 : r ≠ .x6 := fun h => hr (by simp [setupRegs, h])
    have n7 : r ≠ .x7 := fun h => hr (by simp [setupRegs, h])
    have n14 : r ≠ .x14 := fun h => hr (by simp [setupRegs, h])
    have n15 : r ≠ .x15 := fun h => hr (by simp [setupRegs, h])
    have n16 : r ≠ .x16 := fun h => hr (by simp [setupRegs, h])
    have n17 : r ≠ .x17 := fun h => hr (by simp [setupRegs, h])
    rw [tg _ n4, fg _ n17, eg _ n16, dg _ n14 n15, cg _ n6 n7, bg _ n6 n7, ag _ n6 n7]

/-! ## The block -/

theorem wordReg_ne : ∀ j < 4, wordReg j ≠ .x5 ∧ wordReg j ∈ [Reg.x0, .x1, .x2, .x3] := by decide

theorem wordReg_inj : ∀ a < 4, ∀ b < 4, wordReg a = wordReg b → a = b := by decide

theorem loadWord_run {s : State} {r : Reg} {off : Nat} (ho : off % 4 = 0 ∧ off < 16384)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 off) 4) :
    ∃ t, runBlock isa [.ldr .w r .x5 off, .rev32 r r] s = some t ∧
      wd t r = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 off) 32) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 off) 32)
  let b := a.write .w r (rev32 (a.read .w r))
  refine ⟨b, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_ldr_w ho hread, runStep_some, runBlock_cons, exec_rev32, runStep_some, runBlock_nil]
  · simp only [wd, b, a, gpr_write_self, State.read, Size.bits, sw32]
  · intro q hq
    simp only [b, a, gpr_write_of_ne _ _ _ hq]

theorem loads_run (s : State) (bufOff n : Nat) (hn : n ≤ 4) (hb : bufOff % 4 = 0 ∧ bufOff + 16 < 16384)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.ldr .w (wordReg i) .x5 (bufOff + 4 * i), .rev32 (wordReg i) (wordReg i)]) s = some t ∧
      (∀ j < n, wd t (wordReg j) = rev32 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * j)) 32)) ∧
      (∀ r, (∀ j < n, r ≠ wordReg j) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, am, ard, awr, asp, avec⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (fun j hj => (wordReg_ne j (by omega_using [hn, hj])).1.symm)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * n)) 4 := by
      rw [ard, awr, ab]
      exact hread n (by omega_using [hn])
    obtain ⟨b, be, bv, bg, bm, brd, bwr, bsp, bvec⟩ := loadWord_run (r := wordReg n)
      ⟨by omega_using [hb.1], by omega_using [hb.2, hn]⟩ ar
    refine ⟨b, ?_, ?_, ?_, bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp, bvec.trans avec⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · intro j hj
      by_cases h : j = n
      · subst j
        simpa only [am, ab] using bv
      · rw [wd, bg _ (fun e => h (wordReg_inj _ (by omega_using [hn, hj]) _ (by omega_using [hn]) e))]
        exact aw j (by omega_using [hj, h])
    · intro r hr
      exact (bg r (hr n (by omega_using []))).trans (ag r (fun j hj => hr j (by omega_using [hj])))

theorem storeWord_run {s : State} {r : Reg} {off : Nat} (hr : r ≠ .x5) (ho : off % 4 = 0 ∧ off < 16384)
    (hwrite : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 off) 4) :
    ∃ t, runBlock isa [.rev32 r r, .str .w r .x5 off] s = some t ∧
      t.mem = s.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 off) (rev32 (wd s r)) ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w r (rev32 ((s.gpr r).setWidth 32))
  let t : State := { a with mem := a.mem.writeW (a.gpr .x5 + BitVec.ofNat 64 off) ((a.gpr r).setWidth 32) }
  have base : a.gpr .x5 = s.gpr .x5 := gpr_write_of_ne _ _ _ hr.symm
  refine ⟨t, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_rev32, runStep_some, runBlock_cons]
    rw [exec_str_w ho (by
      change InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 off) 4
      rw [base]; exact hwrite), runStep_some, runBlock_nil]
    rfl
  · simp only [t, a, base, gpr_write_self, mem_write, sw32, wd]
  · intro q hq
    exact gpr_write_of_ne _ _ _ hq

theorem frame_write_word (m : Mem) (p : Addr) (v : BitVec 32) : Frame [⟨p, 4⟩] m (m.writeW p v) := by
  intro x hx
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right (fun h => hx _ List.mem_cons_self h)

/-- The register stored as word `i`: `R0, R1, L0, L1`. -/
abbrev outReg (i : Nat) : Reg := wordReg ((i + 2) % 4)

theorem stores_run (s : State) (bufOff n : Nat) (hn : n ≤ 4) (hb : bufOff % 4 = 0 ∧ bufOff + 16 < 16384)
    (hwrite : ∀ i < 4, InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.rev32 (outReg i) (outReg i), .str .w (outReg i) .x5 (bufOff + 4 * i)]) s = some t ∧
      (∀ j < n, t.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * j)) 32 = rev32 (wd s (outReg j))) ∧
      (∀ r, (∀ j < n, r ≠ outReg j) → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5 + BitVec.ofNat 64 bufOff, 16⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero =>
    exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, af, ard, awr, asp, avec⟩ := ih (by omega_using [hn])
    have on5 : outReg n ≠ .x5 := (wordReg_ne _ (Nat.mod_lt _ (by decide))).1
    have ab : a.gpr .x5 = s.gpr .x5 :=
      ag _ (fun j hj => (wordReg_ne _ (Nat.mod_lt _ (by decide))).1.symm)
    have av : a.gpr (outReg n) = s.gpr (outReg n) := ag _ (fun j hj he => by
      have := wordReg_inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) he
      omega_using [hn, hj, this])
    have ar : InRegions a.wr (a.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * n)) 4 := by
      rw [awr, ab]
      exact hwrite n (by omega_using [hn])
    obtain ⟨b, be, bm, bg, brd, bwr, bsp, bvec⟩ := storeWord_run on5
      ⟨by omega_using [hb.1], by omega_using [hb.2, hn]⟩ ar
    have bmem : b.mem = a.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * n)) (rev32 (wd s (outReg n))) := by
      simpa only [ab, av, wd] using bm
    have bf : Frame [⟨s.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * n), 4⟩] a.mem b.mem := by
      rw [bmem]
      exact frame_write_word _ _ _
    refine ⟨b, ?_, ?_, ?_, ?_, brd.trans ard, bwr.trans awr, bsp.trans asp, bvec.trans avec⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · intro j hj
      by_cases h : j = n
      · subst j
        rw [bmem, Mem.readW_writeW_self32]
      · rw [bf.readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr .x5) (by omega_using [h]) (by omega_using [hn, hj, hb.2])
            (by omega_using [hn, hb.2])) (by decide)]
        exact aw j (by omega_using [hj, h])
    · intro r hr
      exact (bg r (hr n (by omega_using []))).trans (ag r (fun j hj => hr j (by omega_using [hj])))
    · refine af.trans (bf.sub (fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst r
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [← VG.Offset.add_add (s.gpr .x5) bufOff (4 * n)]
      exact VG.Offset.sub_base _ (by omega_using [hn] : 4 * n + 4 ≤ 16)

/-- The block of the stored words `z 0 … z 3`, big-endian. -/
theorem stored_bytes {m : Mem} {p : Addr} {z : Nat → BitVec 32}
    (h : ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = rev32 (z i)) :
    Spec.Aes.bytesAt m p 16 =
      (Vector.ofFn fun i : Fin 16 => (z (i.val / 4) >>> (8 * (3 - i.val % 4))).setWidth 8).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i hi _
  have hi16 : i < 16 := by simpa [Spec.Aes.bytesAt] using hi
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, Vector.getElem_toList, Vector.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have b := Mem.readW_byte m (p + BitVec.ofNat 64 (4 * (i / 4))) (i := i % 4) (by omega_using [])
  rw [VG.Offset.add_add, show 4 * (i / 4) + i % 4 = i by omega_using [], h (i / 4) (by omega_using [hi16])] at b
  rw [b, BitVec.getLsbD_extractLsb']
  simp only [hj, decide_true, Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  change (byteRev32 (z (i / 4))).getLsbD (8 * (i % 4) + j) = _
  rw [byteRev32_getLsbD _ (by omega_using [hj])]
  congr 1; omega_using [hj]

/-! ## The block enciphered -/

/-- Every general-purpose register `crypt` writes. -/
def cryptRegs : List Reg := written ++ setupRegs

/-- `crypt`: the block at `x5 + bufOff` enciphered under the schedule at
`x5 + keyOff`. -/
theorem crypt_wp {s : State} {bufOff keyOff : Nat}
    (hb : bufOff % 4 = 0 ∧ bufOff + 16 < 16384) (hk : keyOff % 4 = 0 ∧ keyOff + 128 < 16384)
    (hrk : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (keyOff + 4 * i)) 4)
    (hwb : ∀ i < 4, InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 (bufOff + 4 * i)) 4) :
    WP isa (.block (crypt bufOff keyOff)) s fun t =>
      (∀ r, r ∉ cryptRegs → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5 + BitVec.ofNat 64 bufOff, 16⟩] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (s.gpr .x5 + BitVec.ofNat 64 bufOff) 16 =
        (Spec.Seed.encryptBlock (Spec.Seed.scheduleAt s.mem (s.gpr .x5 + BitVec.ofNat 64 keyOff))
          (Spec.Seed.blockAt s.mem (s.gpr .x5 + BitVec.ofNat 64 bufOff))).toList ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  change WP isa (.block (setup ++ loadBlock bufOff ++ (List.range 8).flatMap (round2 keyOff) ++
    storeBlock bufOff)) s _
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_wp s) fun a ⟨ac, ag, am, ard, awr, asp⟩ => ?_
  have a5 : a.gpr .x5 = s.gpr .x5 := ag _ (by decide)
  obtain ⟨b, be, bw, bg, bm, brd, bwr, bsp, bv⟩ := loads_run a bufOff 4 (Nat.le_refl _) hb (fun i hi => by
    rw [ard, awr, a5]
    obtain ⟨r, hr, hc⟩ := hwb i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩)
  have be' : runBlock isa (loadBlock bufOff) a = some b := be
  have bfr : ∀ r, r ∉ [Reg.x0, .x1, .x2, .x3] → b.gpr r = a.gpr r := fun r hr =>
    bg r (fun j hj h => hr (h ▸ (wordReg_ne j hj).2))
  have bc : Consts b := ac.of_frame (fun v _ => by rw [bv]) (fun r hr => bfr r (fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h <;> simp [h])))
  have b5 : b.gpr .x5 = s.gpr .x5 := (bfr _ (by decide)).trans a5
  obtain ⟨c, ce, cq, cg, cc, cm, crd, cwr, csp⟩ := rounds_run b keyOff 8 (Nat.le_refl _) bc hk
    (fun i hi => by rw [brd, bwr, ard, awr, b5]; exact hrk i hi)
  have c5 : c.gpr .x5 = s.gpr .x5 := (cg _ (by decide)).trans b5
  have cmem : c.mem = s.mem := cm.trans (bm.trans am)
  obtain ⟨d, de, dw, dg, df, drd, dwr, dsp, dv⟩ := stores_run c bufOff 4 (Nat.le_refl _) hb
    (fun i hi => by rw [cwr, bwr, awr, c5]; exact hwb i hi)
  have de' : runBlock isa (storeBlock bufOff) c = some d := de
  refine WP.of_runBlock ⟨d, ?_, ?_, ?_, ?_, drd.trans (crd.trans (brd.trans ard)),
    dwr.trans (cwr.trans (bwr.trans awr)), dsp.trans (csp.trans (bsp.trans asp))⟩
  · rw [VG.Interleave.runBlock_append, be', Option.bind_some, VG.Interleave.runBlock_append, ce,
      Option.bind_some, de']
  · intro r hr
    have hw : r ∉ written := fun h => hr (List.mem_append_left _ h)
    have hs : r ∉ setupRegs := fun h => hr (List.mem_append_right _ h)
    have hh : r ∉ [Reg.x0, .x1, .x2, .x3] := fun h => hw (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> simp [written, h])
    rw [dg r (fun j hj h => hh (h ▸ (wordReg_ne _ (Nat.mod_lt _ (by decide))).2)), cg r hw, bfr r hh, ag r hs]
  · rw [c5, cmem] at df
    exact df
  · let K := Spec.Seed.scheduleAt s.mem (s.gpr .x5 + BitVec.ofNat 64 keyOff)
    let q := quadOf c
    have hkeys : ∀ j < 16, rk b.mem (b.gpr .x5) keyOff j = Spec.Seed.roundKey K j := fun j hj => by
      rw [VG.Proof.Seed.roundKey_readW _ _ hj, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        VG.Offset.add_add, VG.Offset.add_add, rk, bm, am, b5]
    have hquad : quadOf b = decodeQ (Spec.Seed.blockAt s.mem (s.gpr .x5 + BitVec.ofNat 64 bufOff)) := by
      have q0 := bw 0 (by decide)
      have q1 := bw 1 (by decide)
      have q2 := bw 2 (by decide)
      have q3 := bw 3 (by decide)
      rw [am, a5] at q0 q1 q2 q3
      rw [VG.Proof.Seed.decodeQ_blockAt, VG.Offset.add_add, VG.Offset.add_add, VG.Offset.add_add,
        VG.Offset.add_add]
      exact Prod.ext q0 (Prod.ext q1 (Prod.ext q2 q3))
    have hq : q = roundsN (Spec.Seed.roundKey K) 16
        (decodeQ (Spec.Seed.blockAt s.mem (s.gpr .x5 + BitVec.ofNat 64 bufOff))) := by
      rw [← hquad, ← VG.Proof.Seed.roundsN_congr 16 _ hkeys]
      exact cq
    rw [stored_bytes (z := fun i => (#v[q.2.2.1, q.2.2.2, q.1, q.2.1] : Vector Word 4).getD i 0) (fun i hi => by
      rw [VG.Offset.add_add, ← c5, dw i hi]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl <;> rfl)]
    rw [Spec.Seed.encryptBlock, VG.Proof.Seed.crypt_eq, ← hq]
    rfl

end VG.Proof.Seed.AArch64.Serial
