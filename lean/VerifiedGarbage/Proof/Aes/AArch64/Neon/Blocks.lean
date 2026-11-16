module

public import VerifiedGarbage.Proof.Aes.AArch64.Neon.Crypt8
public import VerifiedGarbage.Proof.Aes.AArch64.Blocks
public import VerifiedGarbage.Proof.Aes.Vector
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Aes.AArch64.OneBlock
import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Crypt8
meta import VerifiedGarbage.Proof.Aes.AArch64.Blocks
meta import VerifiedGarbage.Proof.Aes.Vector
meta import VerifiedGarbage.Proof.Framework.AArch64.Tbl
meta import VerifiedGarbage.Proof.Aes.AArch64.OneBlock
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES on whole blocks, bitsliced in AdvSIMD registers, on AArch64

`blocks_correct`: `blocks crypt8` replaces each block of the data with
`f rounds w` of it, for a transformation of eight blocks that `CryptOk`
describes (`encrypt8` and `decrypt8`, `Crypt8.lean`).

* The key loop bitslices each round key: word `j` of round key `i`, at
  `scratch + 128 + 128 i + 16 j`, is `plane key j`, whose byte `e` is all
  ones when bit `j` of byte `e` of the key is set (`keyRel_plane`).
* A group loads its blocks into the registers `A k` (`loadFrom`), which
  name the states it transforms (`Vector.st`), so that the last group needs
  no padding, and stores the results from `B k` (`storeFrom`). The data's
  invariant is `EcbInv` (`Ecb.lean`): the first `k` blocks hold the
  transformation of the original ones.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.Neon

open VG VG.AArch64 VG.AArch64.RegUpd VG.Bitslice VG.Impl.Aes.AArch64.Neon VG.Proof.Aes
open VG.AArch64.StraightV (vAddr addr_slot read16_readW write16_writeW exec_vop_some slot_sep
  slot_contains)
open VG.AArch64.Tbl (bc vbyte_bc exec_dupb runBlock_cat_some)
open VG.Proof.Aes.Vector (KeyIs keyIs_readW st vbyte_readW)
open VG.Spec.Aes (roundKey bytesAt)

/-! ## The round keys -/

/-- Word `j` of a bitsliced round key: every bit of its byte `e` is bit `j`
of byte `e` of the key. -/
def plane (x : BitVec 128) (j : Nat) : BitVec 128 :=
  ofVBytes fun e => if (vbyte x e).getLsbD j then 0xFF else 0

theorem keyRel_plane {key : BitVec 128} {rk : List Byte} (hk : KeyIs key rk) :
    KeyRel (plane key) rk := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  rw [getLsbD_bsByte _ _ hj, plane, getLsbD_ofVBytes _ hi hb, ← hk i hi]
  cases (vbyte key i).getLsbD j
  · simp
  · rw [ite_eq_left rfl, show (0xFF : BitVec 8) = BitVec.allOnes 8 from rfl, BitVec.getLsbD_allOnes]
    simp [hb]

theorem range_flatMap_succ {α : Type} (f : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem B_inj : ∀ i < 8, ∀ j < 8, B i = B j → i = j := by decide

theorem B_ne : ∀ i < 8, B i ≠ .v0 ∧ B i ≠ .v1 := by decide

theorem maskVal : ∀ j < 8,
    (((BitVec.ofNat 16 (2 ^ j)).setWidth 32).setWidth 64).setWidth 8 = BitVec.ofNat 8 (2 ^ j) := by
  decide

/-- The masks: `2ʲ` in every byte of `B j`. -/
theorem keyMasks_ok (k : Nat) (hk : k ≤ 8) (s : State) :
    ∃ s', runBlock isa ((List.range k).flatMap keyMask) s = some s' ∧
      (∀ j < k, s'.v (B j) = bc (BitVec.ofNat 8 (2 ^ j))) ∧
      (∀ r, (∀ j < k, r ≠ B j) → s'.v r = s.v r) ∧ (∀ g, g ≠ .x6 → s'.gpr g = s.gpr g) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction k with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht, tm, to, tg, tmem, trd, twr, tsp⟩ := ih (by omega_using [hk])
    rw [range_flatMap_succ]
    let u := (t.write .w .x6 ((BitVec.ofNat 16 (2 ^ k)).setWidth 32))
    refine ⟨u.setV (B k) (bc ((u.gpr .x6).setWidth 8)), runBlock_cat_some ht (by
      rw [keyMask, runBlock_cons, exec_movz_w, runStep_some, runBlock_cons, exec_dupb, runStep_some,
        runBlock_nil]), fun j hj => ?_, fun r hr => ?_, fun g hg => ?_, tmem, trd, twr, tsp⟩
    · by_cases hjk : j = k
      · subst hjk
        rw [v_setV_self]
        simp only [u, State.write, ite_true]
        rw [maskVal j (by omega_using [hk])]
      · rw [v_setV_of_ne _ _ (fun h => hjk (B_inj j (by omega_using [hk, hj]) k (by omega_using [hk]) h))]
        exact tm j (by omega_using [hj, hjk])
    · rw [v_setV_of_ne _ _ (hr k (by omega_using []))]
      exact to r fun j hj => hr j (by omega_using [hj])
    · show (if g = Reg.x6 then _ else t.gpr g) = _
      rw [ite_eq_right hg, tg g hg]

theorem byte_bit : ∀ j < 8, ∀ x : BitVec 8,
    (x &&& BitVec.ofNat 8 (2 ^ j) = BitVec.ofNat 8 (2 ^ j)) = (x.getLsbD j = true) := by
  decide +kernel

/-- `cmeq` of the key masked by `2ʲ` with `2ʲ` is word `j` of the bitsliced key. -/
theorem cmeq_plane (x : BitVec 128) {j : Nat} (hj : j < 8) :
    VArr.b16.map2 (fun w a b => if a = b then BitVec.allOnes w else 0)
      (x &&& bc (BitVec.ofNat 8 (2 ^ j))) (bc (BitVec.ofNat 8 (2 ^ j))) = plane x j := by
  simp only [VArr.map2, plane]
  refine StraightQ.vbyte_ext fun e he => ?_
  rw [vbyte_ofVBytes _ he, vbyte_ofVBytes _ he, StraightQ.vbyte_and, vbyte_bc _ he]
  simp only [byte_bit j hj]
  rfl

/-- Word `j` of the round key in `v0`, stored at `[x7, #16j]`. -/
theorem keyWord_ok {s : State} {a : Addr} {j : Nat} (hj : j < 8) (ha : s.gpr .x7 = a)
    (hmask : s.v (B j) = bc (BitVec.ofNat 8 (2 ^ j))) (hin : InRegions s.wr (vAddr a j) 16) :
    ∃ s', runBlock isa (sliceWord j) s = some s' ∧
      s'.mem = s.mem.writeW (vAddr a j) (plane (s.v .v0) j) ∧
      (∀ r, r ≠ .v1 → s'.v r = s.v r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  let t := s.setV .v1 (s.v .v0 &&& s.v (B j))
  let u := t.setV .v1 (VArr.b16.map2 (fun w a b => if a = b then BitVec.allOnes w else 0)
    (t.v .v1) (t.v (B j)))
  have hu : u.v .v1 = plane (s.v .v0) j := by
    simp only [u, t]
    rw [v_setV_self, v_setV_self, v_setV_of_ne _ _ (B_ne j hj).2, hmask, cmeq_plane _ hj]
  have hst : exec (.strq .v1 .x7 (16 * j)) u =
      some { u with mem := u.mem.writeW (vAddr a j) (u.v .v1) } := by
    have hin' : InRegions u.wr (vAddr a j) 16 := hin
    have ha' : u.gpr .x7 = a := ha
    simp [exec, addr_slot (show 16 * j < 65536 by omega_using [hj]), State.store, hin',
      write16_writeW, ha']
  refine ⟨{ u with mem := u.mem.writeW (vAddr a j) (u.v .v1) }, ?_, ?_, fun r hr => ?_, rfl, rfl,
    rfl, rfl⟩
  · rw [sliceWord, vand, runBlock_cons, exec_vop_some rfl, runStep_some, runBlock_cons,
      exec_vop_some rfl, runStep_some, runBlock_cons, hst, runStep_some, runBlock_nil]
  · show u.mem.writeW _ _ = _
    rw [hu]; rfl
  · show u.v r = s.v r
    simp only [u, t]
    rw [v_setV_of_ne _ _ hr, v_setV_of_ne _ _ hr]

/-- The first `k` words of the round key in `v0`, stored at `x7`. -/
theorem keyWords_ok (k : Nat) (hk : k ≤ 8) {s : State} {a : Addr} (ha : s.gpr .x7 = a)
    (hmask : ∀ i < 8, s.v (B i) = bc (BitVec.ofNat 8 (2 ^ i)))
    (hin : ∀ i < 8, InRegions s.wr (vAddr a i) 16) :
    ∃ s', runBlock isa ((List.range k).flatMap sliceWord) s = some s' ∧
      (∀ i < k, s'.mem.readW (vAddr a i) 128 = plane (s.v .v0) i) ∧
      Frame [⟨a, 128⟩] s.mem s'.mem ∧ (∀ r, r ≠ .v1 → s'.v r = s.v r) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction k with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), Frame.refl _ _, fun _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht, tm, tf, tv, tg, trd, twr, tsp⟩ := ih (by omega_using [hk])
    have hk8 : k < 8 := by omega_using [hk]
    obtain ⟨u, hu, um, uv, ug, urd, uwr, usp⟩ := keyWord_ok (s := t) (a := a) hk8 (by rw [tg]; exact ha)
      (by rw [tv _ (B_ne k hk8).2]; exact hmask k hk8) (by rw [twr]; exact hin k hk8)
    rw [range_flatMap_succ]
    refine ⟨u, runBlock_cat_some ht hu, fun i hi => ?_, ?_, fun r hr => (uv r hr).trans (tv r hr),
      ug.trans tg, urd.trans trd, uwr.trans twr, usp.trans tsp⟩
    · rw [um, tv VReg.v0 (by decide)]
      by_cases hik : i = k
      · subst hik
        exact Mem.readW_writeW_self t.mem (vAddr a i) 16 (plane (s.v .v0) i) (by decide)
      · rw [Mem.readW_writeW_sep (slot_sep a (by omega_using [hi, hk]) (by omega_using [hk]) hik)
          (by decide)]
        exact tm i (by omega_using [hi, hik])
    · rw [um]
      exact tf.writeW (List.mem_singleton_self _) _ (slot_contains (n := 8) a hk8 (by decide))

/-- One round key bitsliced, and on to the next. -/
theorem keyBody_ok {s : State} {S b : Addr} {j : Nat} (hS : (⟨S, 240⟩ : Region) ∈ s.rd)
    (hb : ScrIn b s.wr) (h0 : s.gpr .x0 = S + BitVec.ofNat 64 (16 * j))
    (h7 : s.gpr .x7 = b + BitVec.ofNat 64 (128 + 128 * j)) (hj : j ≤ 14)
    (hmask : ∀ i < 8, s.v (B i) = bc (BitVec.ofNat 8 (2 ^ i))) :
    ∃ s', runBlock isa keyBody s = some s' ∧
      s'.gpr .x0 = S + BitVec.ofNat 64 (16 * (j + 1)) ∧
      s'.gpr .x7 = b + BitVec.ofNat 64 (128 + 128 * (j + 1)) ∧
      s'.gpr kp = s.gpr kp - BitVec.ofNat 64 1 ∧
      (∀ g, g ≠ .x0 → g ≠ .x7 → g ≠ kp → s'.gpr g = s.gpr g) ∧
      (∀ i < 8, s'.v (B i) = s.v (B i)) ∧
      (∀ i < 8, s'.mem.readW (vAddr (b + BitVec.ofNat 64 (128 + 128 * j)) i) 128 =
        plane (s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128) i) ∧
      Frame [⟨b + BitVec.ofNat 64 (128 + 128 * j), 128⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨L, hL, _, hb⟩ := hb
  -- The load.
  have hin0 : InRegions (s.rd ++ s.wr) (vAddr (s.gpr .x0) 0) 16 :=
    ⟨⟨S, 240⟩, List.mem_append_left _ hS, by
      rw [h0, key_addr]; exact Offset.contains_base S (by omega_using [hj]) (by omega_using [hj])⟩
  let t := s.setV .v0 (s.mem.readW (vAddr (s.gpr .x0) 0) 128)
  have ht : exec (.ldrq .v0 .x0 (16 * 0)) s = some t := by
    simp [exec, addr_slot (show 16 * 0 < 65536 by decide), State.load, hin0, read16_readW, t]
  have tv0 : t.v .v0 = s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 128 := by
    simp only [t]
    rw [v_setV_self, h0, key_addr, Nat.mul_zero, Nat.add_zero]
  -- The words.
  obtain ⟨u, hu, um, uf, uv, ug, urd, uwr, usp⟩ := keyWords_ok 8 (Nat.le_refl 8) (s := t)
    (a := b + BitVec.ofNat 64 (128 + 128 * j)) h7
    (fun i hi => by
      show (s.setV .v0 _).v (B i) = _
      rw [v_setV_of_ne _ _ (B_ne i hi).1]; exact hmask i hi)
    (fun i hi => ⟨⟨b, L⟩, hb, by
      rw [key_addr]
      exact Offset.contains_base b (by omega_using [hj, hi, hL]) (by omega_using [hj, hi])⟩)
  -- The steps.
  let w := ((u.write .x .x0 (u.read .x .x0 + BitVec.ofNat 64 16)).write .x .x7
    ((u.write .x .x0 (u.read .x .x0 + BitVec.ofNat 64 16)).read .x .x7 + BitVec.ofNat 64 128))
  have hw : runBlock isa ([.addImm .x .x0 .x0 16, .addImm .x .x7 .x7 128, .subImm .x kp kp 1] :
      List Instr) u = some (w.write .x kp (w.read .x kp - BitVec.ofNat 64 1)) := by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_nil]
  have ug' : ∀ g, u.gpr g = s.gpr g := fun g => by rw [ug]; rfl
  refine ⟨_, runBlock_cat_some (runBlock_cat_some (a := [.ldrq .v0 .x0 0]) (by
      rw [runBlock_cons, show (Instr.ldrq .v0 .x0 0) = .ldrq .v0 .x0 (16 * 0) from rfl, ht,
        runStep_some, runBlock_nil]) hu) hw, ?_, ?_, ?_, fun g g0 g7 gk => ?_, fun i hi => ?_,
    fun i hi => ?_, ?_, urd, uwr, usp⟩
  · simp only [w, State.write, State.read, BitVec.setWidth_eq, kp]
    simp only [show (Reg.x0 = Reg.x8) = False from by decide, show (Reg.x0 = Reg.x7) = False from by decide,
      ite_false, ite_true]
    rw [ug', h0, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * j + 16 = 16 * (j + 1) by omega_using []]
  · simp only [w, State.write, State.read, BitVec.setWidth_eq, kp]
    simp only [show (Reg.x7 = Reg.x8) = False from by decide, show (Reg.x7 = Reg.x0) = False from by decide,
      ite_false, ite_true]
    rw [ug', h7, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 128 + 128 * j + 128 = 128 + 128 * (j + 1) by omega_using []]
  · simp only [w, State.write, State.read, BitVec.setWidth_eq, kp]
    simp only [show (Reg.x8 = Reg.x7) = False from by decide, show (Reg.x8 = Reg.x0) = False from by decide,
      ite_false, ite_true]
    rw [ug']
  · simp only [w, State.write, g0, g7, gk, ite_false]
    exact ug' g
  · show u.v (B i) = s.v (B i)
    rw [uv _ (B_ne i hi).2]
    show (s.setV .v0 _).v (B i) = _
    rw [v_setV_of_ne _ _ (B_ne i hi).1]
  · show u.mem.readW _ 128 = _
    rw [um i hi, tv0]
  · exact uf

theorem eval_nz {s : State} {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    AArch64.eval (.nonzero .x r) s = some (!decide (k = 0)) := by
  simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, h, ofNat_ne_zero hk]

/-- Before round key `j` is bitsliced; the key loop starts in `s₂`. -/
structure KInv (s₂ : State) (S b : Addr) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hx0 : s.gpr .x0 = S + BitVec.ofNat 64 (16 * j)
  hx7 : s.gpr .x7 = b + BitVec.ofNat 64 (128 + 128 * j)
  hkp : s.gpr kp = BitVec.ofNat 64 (R + 1 - j)
  keep : ∀ g, g ≠ .x0 → g ≠ .x7 → g ≠ kp → s.gpr g = s₂.gpr g
  mask : ∀ i < 8, s.v (B i) = bc (BitVec.ofNat 8 (2 ^ i))
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  keys : ∀ i < j, KeyRel (fun k => s.mem.readW (vAddr (b + BitVec.ofNat 64 (128 + 128 * i)) k) 128)
    (roundKey w i)
  frame : Frame [⟨b, 2048⟩] s₂.mem s.mem

/-- The key loop: every round key bitsliced. -/
theorem keyLoop_ok {s₂ : State} {S b : Addr} {R : Nat} {w : List Byte}
    (hS : (⟨S, 240⟩ : Region) ∈ s₂.rd) (hb : ScrIn b s₂.wr)
    (hd : Region.Disjoint ⟨S, 240⟩ ⟨b, 2048⟩) (hR : R ≤ 14)
    (hw : w = bytesAt s₂.mem S (16 * (R + 1))) {s : State} (hi : KInv s₂ S b R w 0 s) :
    WP isa (.loop (.block keyBody) (.nonzero .x kp)) s (KInv s₂ S b R w (R + 1)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = R - j ∧ j ≤ R ∧ KInv s₂ S b R w j s)
    (fun n s hs => ?_) R s ⟨0, rfl, Nat.zero_le _, hi⟩
  obtain ⟨j, rfl, hj, hk⟩ := hs
  obtain ⟨s', hs', x0', x7', kp', keep', mask', keyj, fr', rd', wr', sp'⟩ :=
    keyBody_ok (S := S) (b := b) (j := j) (by rw [hk.rd]; exact hS) (by rw [hk.wr]; exact hb) hk.hx0
      hk.hx7 (by omega_using [hj, hR]) hk.mask
  refine WP.of_runBlock ⟨s', hs', ?_⟩
  have hkp : s'.gpr kp = BitVec.ofNat 64 (R - j) := by
    rw [kp', hk.hkp, Offset.ofNat_sub_ofNat (by omega_using [hj]),
      show R + 1 - j - 1 = R - j by omega_using [hj]]
  have inv' : KInv s₂ S b R w (j + 1) s' :=
    { hx0 := x0'
      hx7 := x7'
      hkp := by rw [hkp, show R + 1 - (j + 1) = R - j by omega_using []]
      keep := fun g g0 g7 gk => (keep' g g0 g7 gk).trans (hk.keep g g0 g7 gk)
      mask := fun i hi => (mask' i hi).trans (hk.mask i hi)
      rd := rd'.trans hk.rd
      wr := wr'.trans hk.wr
      sp := sp'.trans hk.sp
      keys := fun i hi => by
        by_cases hij : i = j
        · subst hij
          have hkey : KeyIs (s₂.mem.readW (S + BitVec.ofNat 64 (16 * i)) 128) (roundKey w i) := by
            rw [hw]; exact keyIs_readW _ _ (by omega_using [hj])
          have hrd : s.mem.readW (S + BitVec.ofNat 64 (16 * i)) 128 =
              s₂.mem.readW (S + BitVec.ofNat 64 (16 * i)) 128 :=
            hk.frame.readW (r := ⟨S, 240⟩)
              (Offset.contains_base S (by omega_using [hj, hR]) (by omega_using [hj, hR]))
              (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)
          exact keyRel_congr (keyRel_plane hkey) fun k hk8 => by rw [keyj k hk8, hrd]
        · have hlt : i < j := by omega_using [hi, hij]
          refine keyRel_congr (hk.keys i hlt) fun k hk8 => ?_
          have hc : (⟨b + BitVec.ofNat 64 (128 + 128 * i), 128⟩ : Region).Contains
              (vAddr (b + BitVec.ofNat 64 (128 + 128 * i)) k) (128 / 8) := by
            rw [key_addr]
            exact Offset.contains b (by omega_using []) (by omega_using [hk8]) (by omega_using [hlt, hj, hR])
          refine fr'.readW hc (fun r hr => ?_) (by decide)
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint b (Or.inl (by omega_using [hlt])) (by omega_using [hlt, hj, hR])
            (by omega_using [hj, hR])
      frame := hk.frame.trans (fr'.sub fun r hr => ⟨⟨b, 2048⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub_base b (by omega_using [hj, hR])⟩) }
  have hz := eval_nz hkp (by omega_using [hR])
  by_cases hlast : j = R
  · subst hlast
    exact .inl ⟨hz.trans (by simp), inv'⟩
  · exact .inr ⟨hz.trans (by simp [show R - j ≠ 0 by omega_using [hj, hlast]]), R - (j + 1),
      by omega_using [hj, hlast], j + 1, rfl, by omega_using [hj, hlast], inv'⟩

/-! ## Loading and storing the blocks of a group -/

theorem ldrq_ok {s : State} {t : VReg} {n : Reg} {k : Nat} (hk : 16 * k < 65536)
    (hin : InRegions (s.rd ++ s.wr) (vAddr (s.gpr n) k) 16) :
    exec (.ldrq t n (16 * k)) s = some (s.setV t (s.mem.readW (vAddr (s.gpr n) k) 128)) := by
  simp [exec, addr_slot hk, State.load, hin, read16_readW]

theorem strq_ok {s : State} {t : VReg} {n : Reg} {k : Nat} (hk : 16 * k < 65536)
    (hin : InRegions s.wr (vAddr (s.gpr n) k) 16) :
    exec (.strq t n (16 * k)) s =
      some { s with mem := s.mem.writeW (vAddr (s.gpr n) k) (s.v t) } := by
  simp [exec, addr_slot hk, State.store, hin, write16_writeW]

theorem A_inj : ∀ i < 8, ∀ j < 8, A i = A j → i = j := by decide

/-- The blocks `k`, … of a group loaded, while there are blocks left (`c`). -/
theorem loadFrom_wp (fuel : Nat) : ∀ (k : Nat), k + fuel = 7 → ∀ {s : State} {c : Nat}
    {P : State → Prop}, s.gpr .x4 = BitVec.ofNat 64 c → k < c → c < 2 ^ 64 →
    (∀ i < 8, i < c → InRegions (s.rd ++ s.wr) (vAddr (s.gpr .x3) i) 16) →
    (∀ s', (∀ i, k ≤ i → i < 8 → i < c → s'.v (A i) = s.mem.readW (vAddr (s.gpr .x3) i) 128) →
      (∀ r, (∀ i, k ≤ i → i < 8 → r ≠ A i) → s'.v r = s.v r) →
      (∀ g, g ≠ .x6 → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') →
    WP isa (loadFrom fuel k) s P := by
  induction fuel with
  | zero =>
    intro k hk s c P h4 hkc hc hin hP
    have hk7 : k = 7 := by omega_using [hk]
    subst hk7
    simp only [loadFrom]
    refine WP.of_runBlock ⟨s.setV (A 7) (s.mem.readW (vAddr (s.gpr .x3) 7) 128), by
      rw [runBlock_cons, ldrq_ok (by decide) (hin 7 (by decide) hkc), runStep_some, runBlock_nil],
      hP _ (fun i hi hi8 _ => ?_) (fun r hr => ?_) (fun _ _ => rfl) rfl rfl rfl rfl⟩
    · have : i = 7 := by omega_using [hi, hi8]
      subst this; exact v_setV_self _ _ _
    · exact v_setV_of_ne _ _ (hr 7 (Nat.le_refl _) (by decide))
  | succ fuel ih =>
    intro k hk s c P h4 hkc hc hin hP
    have hk8 : k < 8 := by omega_using [hk]
    simp only [loadFrom]
    let u := s.setV (A k) (s.mem.readW (vAddr (s.gpr .x3) k) 128)
    let t := u.write .x .x6 (u.read .x .x4 - BitVec.ofNat 64 (k + 1))
    have ht : runBlock isa [.ldrq (A k) .x3 (16 * k), .subImm .x .x6 .x4 (k + 1)] s = some t := by
      rw [runBlock_cons, ldrq_ok (by omega_using [hk8]) (hin k hk8 hkc), runStep_some, runBlock_cons,
        exec_subImm_x (by omega_using [hk8]), runStep_some, runBlock_nil]
    have tg : ∀ g, g ≠ .x6 → t.gpr g = s.gpr g := fun g hg => by
      show (if g = Reg.x6 then _ else s.gpr g) = _
      rw [ite_eq_right hg]
    have t6 : t.gpr .x6 = BitVec.ofNat 64 (c - (k + 1)) := by
      have e : t.gpr .x6 = s.gpr .x4 - BitVec.ofNat 64 (k + 1) := by
        simp [t, u, State.write, State.read, State.setV]
      rw [e, h4, Offset.ofNat_sub_ofNat (by omega_using [hkc])]
    refine WP.seq (WP.of_runBlock ⟨t, ht, ?_⟩)
    refine WP.ite _ (eval_nz t6 (by omega_using [hc])) (fun hb => ?_) (fun hb => ?_)
    · have hlt : k + 1 < c := by
        have : c - (k + 1) ≠ 0 := by simpa using hb
        omega_using [this]
      refine ih (k + 1) (by omega_using [hk]) (c := c) ((tg .x4 (by decide)).trans h4) hlt hc
        (fun i hi8 hic => by
          rw [tg .x3 (by decide)]; exact hin i hi8 hic)
        fun s' hv ho hg hm hrd hwr hsp => hP s' (fun i hki hi8 hic => ?_) (fun r hr => ?_)
          (fun g hg6 => (hg g hg6).trans (tg g hg6)) hm hrd hwr hsp
      · by_cases hik : i = k
        · subst hik
          rw [ho (A i) fun j hj hj8 => fun e => by
            have := A_inj i hi8 j hj8 e
            omega_using [hj, this]]
          exact v_setV_self _ _ _
        · rw [hv i (by omega_using [hki, hik]) hi8 hic, tg .x3 (by decide)]
          rfl
      · rw [ho r fun i hi hi8 => hr i (by omega_using [hi]) hi8]
        exact v_setV_of_ne _ _ (hr k (Nat.le_refl _) hk8)
    · have heq : c = k + 1 := by
        have : c - (k + 1) = 0 := by simpa using hb
        omega_using [this, hkc]
      refine WP.block_nil (hP t (fun i hki hi8 hic => ?_) (fun r hr => ?_) tg rfl rfl rfl rfl)
      · have : i = k := by omega_using [hki, hic, heq]
        subst this; exact v_setV_self _ _ _
      · exact v_setV_of_ne _ _ (hr k (Nat.le_refl _) hk8)

theorem writeQ_apply (m : Mem) (a x : Addr) (v : BitVec 128) :
    m.writeW a v x = if (x - a).toNat < 16 then vbyte v (x - a).toNat else m x := by
  show (if (x - a).toNat < 128 / 8 then
    (v.setWidth (8 * (128 / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x) = _
  rw [BitVec.setWidth_eq]
  rfl

/-- One more block stored. -/
theorem ecbInv_stepQ {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ t < 16, vbyte v t = (F k).getD t 0) :
    EcbInv m₀ (m.writeW (D + BitVec.ofNat 64 (16 * k)) v) D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m (m.writeW (D + BitVec.ofNat 64 (16 * k)) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [writeQ_apply, Offset.sub_toNat' D (by omega_using [hn, hk]) (by omega_using [hn, hi])]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, hv _ h2, ite_eq_left (show i < 16 * (k + 1) by omega_using [h2]),
          show i / 16 = k by omega_using [h1, h2], show i % 16 = i - 16 * k by omega_using [h1, h2]]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega_using [h2]),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_using [h2])]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_using [hn, hk]),
        h i hi, ite_eq_left (show i < 16 * k by omega_using [h1]),
        ite_eq_left (show i < 16 * (k + 1) by omega_using [h1])]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    rw [writeQ_apply, ite_eq_right]
    have : 16 * k < 2 ^ 64 := by omega_using [hk, hn]
    have : (BitVec.ofNat 64 (16 * k)).toNat = 16 * k := by simp; omega_using [this]
    bv_omega

theorem blk_addr (D : Addr) (g k : Nat) :
    vAddr (D + BitVec.ofNat 64 (16 * (8 * g))) k = D + BitVec.ofNat 64 (16 * (8 * g + k)) := by
  rw [key_addr, Nat.mul_add]

/-- The results `k`, … of group `g` stored, while there are blocks left. -/
theorem storeFrom_wp (fuel : Nat) : ∀ (k : Nat), k + fuel = 7 → ∀ {s : State} {m₀ : Mem} {D : Addr}
    {n g : Nat} {F : Nat → Spec.Aes.State} {P : State → Prop},
    s.gpr .x3 = D + BitVec.ofNat 64 (16 * (8 * g)) → s.gpr .x4 = BitVec.ofNat 64 (n - 8 * g) →
    8 * g + k < n → 16 * n < 2 ^ 64 → (⟨D, 16 * n⟩ : Region) ∈ s.wr →
    EcbInv m₀ s.mem D n (8 * g + k) F →
    (∀ i < 8, 8 * g + i < n → ∀ t < 16, vbyte (s.v (B i)) t = (F (8 * g + i)).getD t 0) →
    (∀ s', EcbInv m₀ s'.mem D n (min n (8 * g + 8)) F → Frame [⟨D, 16 * n⟩] s.mem s'.mem →
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) → s'.v = s.v → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') →
    WP isa (storeFrom fuel k) s P := by
  induction fuel with
  | zero =>
    intro k hk s m₀ D n g F P h3 h4 hkn hn hwr hinv hv hP
    have hk7 : k = 7 := by omega_using [hk]
    subst hk7
    simp only [storeFrom]
    have hin : InRegions s.wr (vAddr (s.gpr .x3) 7) 16 := ⟨⟨D, 16 * n⟩, hwr, by
      rw [h3, blk_addr]
      exact Offset.contains_base D (by omega_using [hkn]) (by omega_using [hkn, hn])⟩
    obtain ⟨hi', hf'⟩ := ecbInv_stepQ (v := s.v (B 7)) (by omega_using [hn]) hkn hinv
      (hv 7 (by decide) hkn)
    refine WP.of_runBlock ⟨{ s with mem := s.mem.writeW (vAddr (s.gpr .x3) 7) (s.v (B 7)) }, by
      rw [runBlock_cons, strq_ok (by decide) hin, runStep_some, runBlock_nil],
      hP _ ?_ ?_ (fun _ _ => rfl) rfl rfl rfl rfl⟩
    · show EcbInv m₀ (s.mem.writeW (vAddr (s.gpr .x3) 7) (s.v (B 7))) D n _ F
      rw [h3, blk_addr, show min n (8 * g + 8) = 8 * g + 7 + 1 by omega_using [hkn]]
      exact hi'
    · show Frame _ s.mem (s.mem.writeW (vAddr (s.gpr .x3) 7) (s.v (B 7)))
      rw [h3, blk_addr]; exact hf'
  | succ fuel ih =>
    intro k hk s m₀ D n g F P h3 h4 hkn hn hwr hinv hv hP
    have hk8 : k < 8 := by omega_using [hk]
    simp only [storeFrom]
    have hin : InRegions s.wr (vAddr (s.gpr .x3) k) 16 := ⟨⟨D, 16 * n⟩, hwr, by
      rw [h3, blk_addr]
      exact Offset.contains_base D (by omega_using [hkn]) (by omega_using [hkn, hn])⟩
    obtain ⟨hi', hf'⟩ := ecbInv_stepQ (v := s.v (B k)) (by omega_using [hn]) hkn hinv
      (hv k hk8 hkn)
    let u : State := { s with mem := s.mem.writeW (vAddr (s.gpr .x3) k) (s.v (B k)) }
    let t := u.write .x .x6 (u.read .x .x4 - BitVec.ofNat 64 (k + 1))
    have ht : runBlock isa [.strq (B k) .x3 (16 * k), .subImm .x .x6 .x4 (k + 1)] s = some t := by
      rw [runBlock_cons, strq_ok (by omega_using [hk8]) hin, runStep_some, runBlock_cons,
        exec_subImm_x (by omega_using [hk8]), runStep_some, runBlock_nil]
    have tg : ∀ r, r ≠ .x6 → t.gpr r = s.gpr r := fun r hr => by
      show (if r = Reg.x6 then _ else s.gpr r) = _
      rw [ite_eq_right hr]
    have t6 : t.gpr .x6 = BitVec.ofNat 64 (n - 8 * g - (k + 1)) := by
      have e : t.gpr .x6 = s.gpr .x4 - BitVec.ofNat 64 (k + 1) := by
        simp [t, u, State.write, State.read]
      rw [e, h4, Offset.ofNat_sub_ofNat (by omega_using [hkn])]
    have tm : EcbInv m₀ t.mem D n (8 * g + k + 1) F := by
      show EcbInv m₀ (s.mem.writeW (vAddr (s.gpr .x3) k) (s.v (B k))) D n _ F
      rw [h3, blk_addr]; exact hi'
    have tf : Frame [⟨D, 16 * n⟩] s.mem t.mem := by
      show Frame _ s.mem (s.mem.writeW (vAddr (s.gpr .x3) k) (s.v (B k)))
      rw [h3, blk_addr]; exact hf'
    refine WP.seq (WP.of_runBlock ⟨t, ht, ?_⟩)
    refine WP.ite _ (eval_nz t6 (by omega_using [hn])) (fun hb => ?_) (fun hb => ?_)
    · have hlt : 8 * g + (k + 1) < n := by
        have : n - 8 * g - (k + 1) ≠ 0 := by simpa using hb
        omega_using [this]
      exact ih (k + 1) (by omega_using [hk]) (m₀ := m₀) (D := D) (n := n) (g := g) (F := F)
        ((tg .x3 (by decide)).trans h3) ((tg .x4 (by decide)).trans h4) hlt hn hwr tm hv
        fun s' hi hf hg hv' hrd hwr' hsp => hP s' hi (tf.trans hf)
          (fun r hr => (hg r hr).trans (tg r hr)) hv' hrd hwr' hsp
    · have heq : n = 8 * g + k + 1 := by
        have : n - 8 * g - (k + 1) = 0 := by simpa using hb
        omega_using [this, hkn]
      refine WP.block_nil (hP t ?_ tf tg rfl rfl rfl rfl)
      rw [show min n (8 * g + 8) = 8 * g + k + 1 by omega_using [heq, hk8]]
      exact tm

theorem shr3_ne (x : Nat) (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x >>> 3 != 0) = decide (8 ≤ x) := by
  by_cases h : 8 ≤ x
  · have : BitVec.ofNat 64 x >>> 3 ≠ 0 := by
      intro h'; have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow] at this
      simp at this; omega_using [this, h]
    simpa [h] using this
  · have : BitVec.ofNat 64 x >>> 3 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]
      simp; omega_using [h]
    simp [this, h]

theorem exec_movz_x0 {s : State} {d : Reg} : exec (.movz .x d 0 0) s = some (s.write .x d 0) := by
  simp [reduceExec, Size.bits]

/-- On to the next group, if more than eight blocks were left (`c`). -/
theorem advance_wp {s : State} {c : Nat} (h4 : s.gpr .x4 = BitVec.ofNat 64 c) (hc : 0 < c)
    (hc64 : c < 2 ^ 64) {P : State → Prop}
    (h : ∀ s', (8 < c → s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 128 ∧
        s'.gpr .x4 = BitVec.ofNat 64 (c - 8)) →
      (¬ 8 < c → s'.gpr .x4 = BitVec.ofNat 64 0) →
      (∀ g, g ≠ .x6 → g ≠ .x3 → g ≠ .x4 → s'.gpr g = s.gpr g) → s'.v = s.v → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa advance s P := by
  unfold advance
  let u := s.write .x .x6 (s.read .x .x4 - BitVec.ofNat 64 1)
  let t := u.write .x .x6 (u.read .x .x6 >>> 3)
  have ht : runBlock isa [.subImm .x .x6 .x4 1, .lsr .x .x6 .x6 3] s = some t := by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil]
  have tg : ∀ r, r ≠ .x6 → t.gpr r = s.gpr r := fun r hr => by
    simp [t, u, State.write, hr]
  have t6 : t.gpr .x6 = BitVec.ofNat 64 (c - 1) >>> 3 := by
    have e : t.gpr .x6 = (s.gpr .x4 - BitVec.ofNat 64 1) >>> 3 := by
      simp [t, u, State.write, State.read]
    rw [e, h4, Offset.ofNat_sub_ofNat (by omega_using [hc])]
  have hev : AArch64.eval (.nonzero .x .x6) t = some (decide (8 ≤ c - 1)) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, t6,
      shr3_ne _ (show c - 1 < 2 ^ 64 by omega_using [hc64])]
  refine WP.seq (WP.of_runBlock ⟨t, ht, ?_⟩)
  refine WP.ite _ hev (fun hb => ?_) (fun hb => ?_)
  · have h8 : 8 < c := by
      have : 8 ≤ c - 1 := by simpa using hb
      omega_using [this]
    let w := t.write .x .x3 (t.read .x .x3 + BitVec.ofNat 64 128)
    refine WP.of_runBlock ⟨w.write .x .x4 (w.read .x .x4 - BitVec.ofNat 64 8), by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_subImm_x (by decide), runStep_some, runBlock_nil], h _ (fun _ => ⟨?_, ?_⟩)
      (fun hn => absurd h8 hn) (fun g g6 g3 g4 => ?_) rfl rfl rfl rfl rfl⟩
    · simp [w, State.write, State.read, tg .x3 (by decide)]
    · have e : (w.write .x .x4 (w.read .x .x4 - BitVec.ofNat 64 8)).gpr .x4 =
          s.gpr .x4 - BitVec.ofNat 64 8 := by
        simp [w, State.write, State.read, tg .x4 (by decide)]
      rw [e, h4, Offset.ofNat_sub_ofNat (by omega_using [h8])]
    · simp [w, State.write, g3, g4, tg g g6]
  · have h8 : ¬ 8 < c := by
      have : ¬ 8 ≤ c - 1 := by simpa using hb
      omega_using [this]
    refine WP.of_runBlock ⟨t.write .x .x4 0, by rw [runBlock_cons, exec_movz_x0, runStep_some,
      runBlock_nil], h _ (fun hn => absurd hn h8) (fun _ => ?_) (fun g g6 g3 g4 => ?_) rfl rfl rfl
      rfl rfl⟩
    · simp [State.write]
    · simp [State.write, g4, tg g g6]

/-! ## The groups -/

/-- What a transformation of eight blocks does: `f R w` to each, with the
round keys as `EncPre` has them. -/
def CryptOk (crypt8 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}, EncPre s₀ R w →
    InRel (QA s₀) S → WP isa crypt8 s₀ fun s => Ctx s₀ s ∧ InRel (QB s) (fun b => f R w (S b))

theorem encrypt8_cryptOk : CryptOk encrypt8 Spec.Aes.cipher := fun hp hin => encrypt8_ok hp hin
theorem decrypt8_cryptOk : CryptOk decrypt8 Spec.Aes.invCipher := fun hp hin => decrypt8_ok hp hin

/-- The words hold the states their bytes make. -/
theorem inRel_st (Q : Nat → BitVec 128) : InRel Q (fun b => st (Q b)) := by
  intro b _ i hi j hj
  rw [Vector.getD_st _ hi]
  simp [vbyte, hj]

theorem vbyte_of_inRel {Q : Nat → BitVec 128} {T : Nat → Spec.Aes.State} (h : InRel Q T) {c t : Nat}
    (hc : c < 8) (ht : t < 16) : vbyte (Q c) t = (T c).getD t 0 :=
  byte_ext fun j hj => by
    rw [← h c hc t ht j hj]
    simp [vbyte, hj]

theorem st_readW (m : Mem) (p : Addr) : st (m.readW p 128) = Spec.Aes.stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [st, Spec.Aes.stateAt, Vector.getElem_ofFn]
  exact vbyte_readW m p hi

theorem keysAt_frame {m m' : Mem} {b : Addr} {R : Nat} {w : List Byte} {rs : List Region}
    (hR : R ≤ 14) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 96, 1952⟩ r) (h : KeysAt m b R w) :
    KeysAt m' b R w := by
  intro j hj
  refine keyRel_congr (h j hj) fun k hk => ?_
  simp only [key_addr]
  exact hf.readW (r := ⟨b + BitVec.ofNat 64 96, 1952⟩)
    (Offset.contains _ (by omega_using []) (by omega_using [hR, hj, hk]) (by omega_using [])) hd
    (by decide)

/-- Before group `g`. -/
structure GInv (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (b D : Addr)
    (n R : Nat) (w : List Byte) (rd wr : List Region) (sp : Addr) (g : Nat) (s : State) : Prop where
  hg : 8 * g < n
  hx3 : s.gpr .x3 = D + BitVec.ofNat 64 (16 * (8 * g))
  hx4 : s.gpr .x4 = BitVec.ofNat 64 (n - 8 * g)
  hx5 : s.gpr sb = b
  hx1 : s.gpr .x1 = BitVec.ofNat 64 R
  hrd : s.rd = rd
  hwr : s.wr = wr
  hsp : s.sp = sp
  keys : KeysAt s.mem b R w
  data : EcbInv m₀ s.mem D n (8 * g) (ecbOut f m₀ D R w)

/-- After the last group. -/
structure GDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr)
    (n R : Nat) (w : List Byte) (rd wr : List Region) (sp : Addr) (s : State) : Prop where
  hrd : s.rd = rd
  hwr : s.wr = wr
  hsp : s.sp = sp
  data : EcbInv m₀ s.mem D n n (ecbOut f m₀ D R w)

section Groups

variable {crypt8 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {m₀ : Mem}
  {b D : Addr} {n R : Nat} {w : List Byte} {rd wr : List Region} {sp : Addr}

/-- One group: from before group `g`, to after the last group (`x4` zero) or
before group `g + 1`. -/
theorem group_ok (hcr : CryptOk crypt8 f) (hscr : (⟨b, 2048⟩ : Region) ∈ wr)
    (hdat : (⟨D, 16 * n⟩ : Region) ∈ wr) (n16 : 16 * n < 2 ^ 64)
    (hdis : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 2048⟩) (hR : R = 10 ∨ R = 12 ∨ R = 14) {g : Nat}
    {s : State} (hi : GInv f m₀ b D n R w rd wr sp g s) :
    WP isa (group crypt8) s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ GDone f m₀ D n R w rd wr sp s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ GInv f m₀ b D n R w rd wr sp (g + 1) s') := by
  have hR14 : R ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  have hg := hi.hg
  unfold group
  -- The loads.
  refine WP.seq (loadFrom_wp 7 0 rfl (c := n - 8 * g) hi.hx4 (by omega_using [hg])
    (by omega_using [n16]) (fun i hi8 hic => ⟨⟨D, 16 * n⟩, List.mem_append_right _ (hi.hwr ▸ hdat), by
      rw [hi.hx3, blk_addr]
      exact Offset.contains_base D (by omega_using [hic]) (by omega_using [hic, n16])⟩)
    fun s₁ hv₁ _ hg₁ hm₁ hrd₁ hwr₁ hsp₁ => ?_)
  -- The transformation.
  have hb₁ : s₁.gpr sb = b := (hg₁ sb (by decide)).trans hi.hx5
  have hp : EncPre s₁ R w :=
    ⟨by rw [hb₁, hwr₁, hi.hwr]; exact .of_mem hscr, hR, (hg₁ .x1 (by decide)).trans hi.hx1,
      by rw [hm₁, hb₁]; exact hi.keys⟩
  refine WP.seq (WP.mono (hcr hp (inRel_st (QA s₁))) fun s₂ h₂ => ?_)
  obtain ⟨hc₂, hin₂⟩ := h₂
  have keep₂ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → r ≠ cnt → s₂.gpr r = s.gpr r :=
    fun r h6 h7 hk hc => (hc₂.keep r h6 h7 hk hc).trans (hg₁ r h6)
  have hx3₂ : s₂.gpr .x3 = D + BitVec.ofNat 64 (16 * (8 * g)) :=
    (keep₂ .x3 (by decide) (by decide) (by decide) (by decide)).trans hi.hx3
  have hx4₂ : s₂.gpr .x4 = BitVec.ofNat 64 (n - 8 * g) :=
    (keep₂ .x4 (by decide) (by decide) (by decide) (by decide)).trans hi.hx4
  have fr₂ : Frame [⟨b, 96⟩] s.mem s₂.mem := by
    have := hc₂.frame
    rwa [hb₁, hm₁] at this
  have dis96 : ∀ r ∈ [(⟨b, 96⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hdis.sub_right (Region.sub_prefix (by omega_using []))
  have data₂ : EcbInv m₀ s₂.mem D n (8 * g) (ecbOut f m₀ D R w) :=
    ecbInv_frame fr₂ dis96 n16 hi.data
  have hv₂ : ∀ i < 8, 8 * g + i < n → ∀ t < 16,
      vbyte (s₂.v (B i)) t = (ecbOut f m₀ D R w (8 * g + i)).getD t 0 := by
    intro i hi8 hin t ht
    have hst : st (s₁.v (A i)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * (8 * g + i))) := by
      rw [hv₁ i (Nat.zero_le _) hi8 (by omega_using [hin]), hi.hx3, blk_addr, st_readW]
      exact ecbInv_orig hi.data (by omega_using []) hin
    rw [vbyte_of_inRel hin₂ hi8 ht]
    show (f R w (st (s₁.v (A i)))).getD t 0 = _
    rw [hst]; rfl
  -- The stores.
  refine WP.seq (storeFrom_wp 7 0 rfl hx3₂ hx4₂ (by omega_using [hg]) n16
    (by rw [hc₂.wr, hwr₁, hi.hwr]; exact hdat) data₂ hv₂
    fun s₃ hi₃ hf₃ hg₃ _ hrd₃ hwr₃ hsp₃ => ?_)
  -- On to the next group.
  refine advance_wp (c := n - 8 * g) ((hg₃ .x4 (by decide)).trans hx4₂) (by omega_using [hg])
    (by omega_using [n16]) fun s₄ hmore hlast hg₄ _ hm₄ hrd₄ hwr₄ hsp₄ => ?_
  have rd₄ : s₄.rd = rd := by rw [hrd₄, hrd₃, hc₂.rd, hrd₁, hi.hrd]
  have wr₄ : s₄.wr = wr := by rw [hwr₄, hwr₃, hc₂.wr, hwr₁, hi.hwr]
  have sp₄ : s₄.sp = sp := by rw [hsp₄, hsp₃, hc₂.sp, hsp₁, hi.hsp]
  by_cases h8 : 8 < n - 8 * g
  · obtain ⟨x3₄, x4₄⟩ := hmore h8
    have keep₄ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → r ≠ cnt → r ≠ .x3 → r ≠ .x4 →
        s₄.gpr r = s.gpr r := fun r h6 h7 hk hc h3 h4 =>
      (hg₄ r h6 h3 h4).trans ((hg₃ r h6).trans (keep₂ r h6 h7 hk hc))
    have keys₄ : KeysAt s₄.mem b R w := by
      rw [hm₄]
      refine keysAt_frame hR14 hf₃ (fun r hr => ?_) (keysAt_frame hR14 fr₂ (fun r hr => ?_) hi.keys)
      · simp only [List.mem_singleton] at hr; subst hr
        exact (hdis.sub_right (Offset.sub_base b (by omega_using []))).symm
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base b (by omega_using []) (by omega_using [])
    refine .inr ⟨(eval_nz x4₄ (by omega_using [n16])).trans (by
        simp [show n - 8 * g - 8 ≠ 0 by omega_using [h8]]),
      { hg := by omega_using [h8]
        hx3 := by
          rw [x3₄, hg₃ .x3 (by decide), hx3₂, BitVec.add_assoc, ← BitVec.ofNat_add,
            show 16 * (8 * g) + 128 = 16 * (8 * (g + 1)) by omega_using []]
        hx4 := by rw [x4₄, show n - 8 * g - 8 = n - 8 * (g + 1) by omega_using []]
        hx5 := (keep₄ sb (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans hi.hx5
        hx1 := (keep₄ .x1 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans hi.hx1
        hrd := rd₄
        hwr := wr₄
        hsp := sp₄
        keys := keys₄
        data := by
          rw [hm₄]
          have := hi₃
          rwa [show min n (8 * g + 8) = 8 * (g + 1) by omega_using [h8]] at this }⟩
  · have x4₄ := hlast h8
    refine .inl ⟨(eval_nz x4₄ (by decide)).trans (by simp), rd₄, wr₄, sp₄, ?_⟩
    rw [hm₄]
    have := hi₃
    rwa [show min n (8 * g + 8) = n by omega_using [h8, hg]] at this

/-- The loop over the groups. -/
theorem groups_ok (hcr : CryptOk crypt8 f) (hscr : (⟨b, 2048⟩ : Region) ∈ wr)
    (hdat : (⟨D, 16 * n⟩ : Region) ∈ wr) (n16 : 16 * n < 2 ^ 64)
    (hdis : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 2048⟩) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State}
    (hi : GInv f m₀ b D n R w rd wr sp 0 s) :
    WP isa (.loop (group crypt8) (.nonzero .x .x4)) s (GDone f m₀ D n R w rd wr sp) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 8 * g ∧ GInv f m₀ b D n R w rd wr sp g s)
    (fun k s hs => ?_) n s ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hi⟩ := hs
  refine WP.mono (group_ok hcr hscr hdat n16 hdis hR hi) fun s' h => ?_
  rcases h with ⟨hz, hd⟩ | ⟨hz, hi'⟩
  · exact .inl ⟨hz, hd⟩
  · exact .inr ⟨hz, n - 8 * (g + 1), by have := hi'.hg; omega_using [this], g + 1, rfl, hi'⟩

end Groups

/-! ## The functions -/

theorem correct_blocks {crypt8 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt8 f) {s₀ : State} (hp : (Proof.Aes.blocksAArch64 f).pre s₀) :
    WP isa (blocks crypt8) s₀ fun s' => (Proof.Aes.blocksAArch64 f).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, hwrap, hR⟩ := hp
  have hwD : (⟨s₀.gpr .x2, 16 * (s₀.gpr .x3).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .x4, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .x0, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  let n := (s₀.gpr .x3).toNat
  have n16 : 16 * n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDS (s₀.gpr .x4) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .x4 - s₀.gpr .x2).isLt
    omega_using [hc, this]
  have hR14 : (s₀.gpr .x1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  let b := s₀.gpr .x4
  let D := s₀.gpr .x2
  let S := s₀.gpr .x0
  let R := (s₀.gpr .x1).toNat
  let w := bytesAt s₀.mem S (16 * (R + 1))
  unfold blocks
  refine WP.seq ?_
  obtain ⟨s₁, h₁, x5₁, x4₁, x3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := blocksSetup_ok s₀
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  refine WP.ite (s₀.gpr .x3 == 0) (by simp [AArch64.eval, State.read, x4₁]) (fun h0 => ?_)
    (fun h0 => ?_)
  · have hn0 : (s₀.gpr .x3).toNat = 0 := by simp only [beq_iff_eq] at h0; simp [h0]
    refine WP.block_nil ?_
    show Spec.Aes.statesAt s₁.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = _
    rw [hn0]; rfl
  · have hn0 : n ≠ 0 := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h0
      intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
    -- The masks, and where the round keys go.
    refine WP.seq ?_
    simp only [keySetup]
    rw [WP.block_append_iff (M := isa)]
    obtain ⟨s₂, h₂, mask₂, -, g₂, m₂, rd₂, wr₂, sp₂⟩ := keyMasks_ok 8 (Nat.le_refl 8) s₁
    refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
    let s₃ := s₂.write .x .x7 (s₂.read .x sb + BitVec.ofNat 64 128)
    let s₄ := s₃.write .x kp (s₃.read .x .x1 + BitVec.ofNat 64 1)
    refine WP.of_runBlock ⟨s₄, by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
    have g₄ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → s₄.gpr r = s₁.gpr r := fun r h6 h7 hk => by
      simp [s₄, s₃, State.write, h7, hk, g₂ r h6]
    have x7₄ : s₄.gpr .x7 = b + BitVec.ofNat 64 128 := by
      have e : s₄.gpr .x7 = s₂.gpr sb + BitVec.ofNat 64 128 := by
        simp [s₄, s₃, State.write, State.read, kp]
      rw [e, g₂ sb (by decide)]; exact congrArg (· + _) x5₁
    have kp₄ : s₄.gpr kp = BitVec.ofNat 64 (R + 1) := by
      have e : s₄.gpr kp = s₂.gpr .x1 + BitVec.ofNat 64 1 := by
        simp [s₄, s₃, State.write, State.read, kp]
      rw [e, g₂ .x1 (by decide), o₁ .x1 (by decide) (by decide) (by decide), BitVec.ofNat_add,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hi₀ : KInv s₄ S b R w 0 s₄ :=
      { hx0 := by
          rw [g₄ .x0 (by decide) (by decide) (by decide), o₁ .x0 (by decide) (by decide) (by decide)]
          simp [S]
        hx7 := x7₄
        hkp := kp₄
        keep := fun _ _ _ _ => rfl
        mask := mask₂
        rd := rfl
        wr := rfl
        sp := rfl
        keys := fun i hi => absurd hi (by omega_using [])
        frame := Frame.refl _ _ }
    have m₄ : s₄.mem = s₀.mem := m₂.trans m₁
    have rd₄ : s₄.rd = s₀.rd := rd₂.trans rd₁
    have wr₄ : s₄.wr = s₀.wr := wr₂.trans wr₁
    have sp₄ : s₄.sp = s₀.sp := sp₂.trans sp₁
    refine WP.seq (WP.mono (keyLoop_ok (S := S) (b := b) (R := R) (w := w) (by rw [rd₄]; exact hrS)
      (by rw [wr₄]; exact .of_mem hwS) dSS hR14 (by rw [m₄]) hi₀) fun s₅ hk₅ => ?_)
    -- The groups.
    have g₅ : ∀ r, r ≠ .x0 → r ≠ .x6 → r ≠ .x7 → r ≠ kp → s₅.gpr r = s₁.gpr r :=
      fun r h0 h6 h7 hk => (hk₅.keep r h0 h7 hk).trans (g₄ r h6 h7 hk)
    have hi : GInv f s₀.mem b D n R w s₀.rd s₀.wr s₀.sp 0 s₅ :=
      { hg := by omega_using [hn0]
        hx3 := by rw [g₅ .x3 (by decide) (by decide) (by decide) (by decide), x3₁]; simp [D]
        hx4 := by
          rw [g₅ .x4 (by decide) (by decide) (by decide) (by decide), x4₁]
          simp [n]
        hx5 := (g₅ sb (by decide) (by decide) (by decide) (by decide)).trans x5₁
        hx1 := by
          rw [g₅ .x1 (by decide) (by decide) (by decide) (by decide),
            o₁ .x1 (by decide) (by decide) (by decide)]
          simp [R]
        hrd := hk₅.rd.trans rd₄
        hwr := hk₅.wr.trans wr₄
        hsp := hk₅.sp.trans sp₄
        keys := fun j hj => hk₅.keys j (by omega_using [hj])
        data := ecbInv_frame (m₄ ▸ hk₅.frame) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dDS) n16 fun i hi => by simp }
    refine WP.mono (groups_ok hcr hwS hwD n16 dDS hR hi) fun s₆ hd => ?_
    show Spec.Aes.statesAt s₆.mem D n = _
    rw [statesAt_of_ecbInv hd.data]
    simp only [Spec.Aes.statesAt, List.map_map]
    rfl

theorem blocks_correct {crypt8 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt8 f)
    (hregs : (blocks crypt8).allInstrs (fun i => preserved.all fun r => !clobbers i r) = true)
    (hnc : (blocks crypt8).noCalls = true)
    (hv : (blocks crypt8).allInstrs keepsV = true)
    (s : State) (hs : (Proof.Aes.blocksAArch64 f).pre s) :
    ∃ t s', Exec isa (blocks crypt8) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 f).post s s' := by
  obtain ⟨t, s', he, h₂, h₃⟩ := WP.gprs (rs := preserved) (correct_blocks hcr hs) hregs hnc
  exact ⟨t, s', he, ⟨h₃, Exec.sp he, Exec.preservedV he hv⟩, h₂⟩

/-- `encryptBlocks`: one block by the tables (`OneBlock.encryptOne_ok`), any
other number of blocks bitsliced. -/
theorem encryptBlocks_wp {s₀ : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s₀) :
    WP isa encryptBlocks s₀ fun s' => (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s₀ s' := by
  unfold encryptBlocks
  let s₁ := s₀.write .x .x6 (s₀.read .x .x3 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s₁ := hp
  refine WP.ite (s₀.gpr .x3 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x3 : s₀.gpr .x3 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x3) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h3 : (s₁.gpr .x3).toNat = 1 := by
      show (s₀.gpr .x3).toNat = 1
      rw [x3]; rfl
    exact WP.mono (OneBlock.encryptOne_ok hp₁ h3) fun s' h => h.2
  · exact correct_blocks encrypt8_cryptOk hp₁

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h₂, h₃⟩ :=
    WP.gprs (rs := preserved) (encryptBlocks_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

/-- `decryptBlocks`: one block by the tables (`OneBlock.decryptOne_ok`), any
other number of blocks bitsliced. -/
theorem decryptBlocks_wp {s₀ : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s₀) :
    WP isa decryptBlocks s₀ fun s' => (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s₀ s' := by
  unfold decryptBlocks
  let s₁ := s₀.write .x .x6 (s₀.read .x .x3 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s₁ := hp
  refine WP.ite (s₀.gpr .x3 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x3 : s₀.gpr .x3 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x3) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h3 : (s₁.gpr .x3).toNat = 1 := by
      show (s₀.gpr .x3).toNat = 1
      rw [x3]; rfl
    exact WP.mono (OneBlock.decryptOne_ok hp₁ h3) fun s' h => h.2
  · exact correct_blocks decrypt8_cryptOk hp₁

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h₂, h₃⟩ :=
    WP.gprs (rs := preserved) (decryptBlocks_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Aes.AArch64.Neon
