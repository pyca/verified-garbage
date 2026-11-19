module

import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Rc4
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Rc4.AArch64.ApplySetup`, which this module and modules that import it used -/

section

/-! ### `Rc4.AArch64.Lanes`, which this module and modules that import it used -/

section

/-! ### `Rc4.Iterate`, which this module and modules that import it used -/

section

/-!
# The stream, byte by byte

`stepN c n` is the context after `n` steps from `c`, and `ks c n` the `n`-th
keystream byte. `update` XORs the input with these bytes and ends in
`stepN` of its length (`update_bytes`).
-/

@[expose] public section

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- The context after `n` steps. -/
def stepN (c : Context) : Nat → Context
  | 0 => c
  | n + 1 => (step (stepN c n)).1

/-- Keystream byte `n`. -/
def ks (c : Context) (n : Nat) : Byte := (step (stepN c n)).2

theorem stepN_succ' (c : Context) (n : Nat) : stepN c (n + 1) = stepN (step c).1 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stepN] at ih ⊢; rw [ih]

theorem ks_succ (c : Context) (n : Nat) : ks c (n + 1) = ks (step c).1 n := by
  simp only [ks, stepN_succ']

theorem update_fst (c : Context) (bs : List Byte) : (update c bs).1 = stepN c bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp only [update, List.length_cons, stepN_succ', ih]

/-- Bytes that are the input XORed with the keystream are `update`'s output. -/
theorem update_bytes (c : Context) (m m' : Mem) (d : Addr) (n : Nat)
    (h : ∀ k < n, m' (d + BitVec.ofNat 64 k) = m (d + BitVec.ofNat 64 k) ^^^ ks c k) :
    bytesAt m' d n = (update c (bytesAt m d n)).2 := by
  induction n generalizing c d with
  | zero => rfl
  | succ n ih =>
    rw [bytes_cons, bytes_cons]
    simp only [update]
    have h0 := h 0 (by omega_using [])
    simp only [BitVec.add_zero] at h0
    rw [h0, ih (step c).1 (d + 1#64) fun k hk => by
      have := h (k + 1) (by omega_using [hk])
      rw [ks_succ] at this
      rw [show d + 1#64 + BitVec.ofNat 64 k = d + BitVec.ofNat 64 (k + 1) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using []]
      exact this]
    rfl

end VG.Proof.Rc4

end

end

/-!
# A group of sixteen bytes

In a group whose base is `B`, lane `n` is skipped while `x5` counts lanes to
skip (the first group starts at lane `sk = (i + 1) mod 16`), does nothing
once the data has ended, and otherwise produces the next byte of the stream
(`lane_ok`). `p` bytes of the `N` at `D` are done after lane `n`:
`p = min N (p₀ + (n - sk))` (`LaneInv`).
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The stream's fixed parameters: the context it starts from, the data and
its original bytes, and the state the loop starts in. -/
structure Glob where
  c₀ : Context
  D : Addr
  N : Nat
  M₀ : Mem
  s₀ : State

/-- `p` bytes of the data done. -/
structure DataAt (g : Glob) (p : Nat) (s : State) : Prop where
  le : p ≤ g.N
  x1 : s.gpr .x1 = g.D + BitVec.ofNat 64 p
  x2 : s.gpr .x2 = BitVec.ofNat 64 (g.N - p)
  bytes : ∀ k < g.N, s.mem (g.D + BitVec.ofNat 64 k) =
    if k < p then g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k else g.M₀ (g.D + BitVec.ofNat 64 k)
  frame : Frame [⟨g.D, g.N⟩] g.M₀ s.mem

/-- What the loop keeps: the registers it does not use, the regions and the
stack pointer. -/
structure Kept (g : Glob) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s.gpr r = g.s₀.gpr r
  rd : s.rd = g.s₀.rd
  wr : s.wr = g.s₀.wr
  sp : s.sp = g.s₀.sp

/-- The bytes done after lane `n` of the group with base `B` that starts
after `p₀` bytes, skipping its first `sk` lanes. -/
def doneAt (g : Glob) (p₀ sk n : Nat) : Nat := min g.N (p₀ + (n - sk))

structure LaneInv (g : Glob) (B p₀ sk n : Nat) (s : State) : Prop where
  prga : PrgaRegs s B (stepN g.c₀ (doneAt g p₀ sk n))
  data : DataAt g (doneAt g p₀ sk n) s
  x5 : s.gpr .x5 = BitVec.ofNat 64 (sk - n)
  x8 : s.gpr .x8 = BitVec.ofNat 64 B
  next : doneAt g p₀ sk n < g.N →
    (stepN g.c₀ (doneAt g p₀ sk n)).i + 1 = BitVec.ofNat 8 (B + max n sk) ∧
      s.v si = bc (tbyte s.v (max n sk))
  kept : Kept g s
  vkept : ∀ r, r ∉ stepRegs → r ≠ negBase → s.v r = g.s₀.v r

theorem eval_nonzero' (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 64 m ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this; simp at this; omega_using [h0, this]
    change (BitVec.ofNat 64 m != (0 : BitVec 64)) = (m != 0)
    simp only [bne, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]

theorem eval_zero' (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 64 m ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this; simp at this; omega_using [h0, this]
    change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]

theorem write_byte_apply (m : Mem) (p x : Addr) (v : BitVec 8) :
    m.write p 1 v x = if x = p then v else m x := VG.Proof.Rc4.write_byte m p x v

/-- The data region is writable, and fits in the address space. -/
structure DataOk (g : Glob) : Prop where
  wr : (⟨g.D, g.N⟩ : Region) ∈ g.s₀.wr
  fit : g.N < 2 ^ 64

theorem DataOk.byte {g : Glob} (h : DataOk g) {s : State} (hk : Kept g s) {p : Nat} (hp : p < g.N) :
    InRegions s.wr (g.D + BitVec.ofNat 64 p) 1 :=
  ⟨_, hk.wr ▸ h.wr, Offset.contains_base _ (by omega_using [hp]) (by have := h.fit; omega_using [hp, this])⟩

theorem lane_ok (g : Glob) (hg : DataOk g) {B p₀ sk n : Nat} (hsk : sk ≤ 15) (hn : n < 16) {s : State}
    (h : LaneInv g B p₀ sk n s) : WP isa (lane n) s (LaneInv g B p₀ sk (n + 1)) := by
  have hfit := hg.fit
  unfold lane
  apply WP.ite _ (eval_nonzero' s .x5 h.x5 (by omega_using [hsk]))
  · intro hz
    have hlt : n < sk := by simp at hz; omega_using [hz]
    let t := s.write .x .x5 (s.read .x .x5 - BitVec.ofNat _ 1)
    refine WP.of_runBlock ⟨t, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have hd : doneAt g p₀ sk (n + 1) = doneAt g p₀ sk n := by simp only [doneAt]; omega_using [hlt]
    have hm : max (n + 1) sk = max n sk := by omega_using [hlt]
    have g5 : ∀ r, r ≠ .x5 → t.gpr r = s.gpr r := fun r hr => by simp [t, State.write, hr]
    have x5 : t.gpr .x5 = BitVec.ofNat 64 (sk - (n + 1)) := by
      simp only [t, State.write, State.read, BitVec.setWidth_eq, ite_true, h.x5]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hlt])]
      congr 1
    exact {
      prga := by
        rw [hd]
        exact ⟨h.prga.table, h.prga.j, h.prga.nb,
          ⟨h.prga.consts.lns, h.prga.consts.c64, h.prga.consts.c128⟩⟩
      data := by
        rw [hd]
        exact ⟨h.data.le, by rw [g5 _ (by decide), h.data.x1], by rw [g5 _ (by decide), h.data.x2],
          h.data.bytes, h.data.frame⟩
      x5 := x5
      x8 := by rw [g5 _ (by decide), h.x8]
      next := by rw [hd, hm]; exact h.next
      kept := ⟨fun r a b c d e f => by rw [g5 r c, h.kept.gpr r a b c d e f], h.kept.rd, h.kept.wr,
        h.kept.sp⟩
      vkept := h.vkept }
  · intro hnz
    have hge : sk ≤ n := by simp at hnz; omega_using [hnz]
    let p := doneAt g p₀ sk n
    have hp := h.data.le
    apply WP.ite _ (eval_zero' s .x2 h.data.x2 (by omega_using [hfit]))
    · intro hz
      have hpN : p = g.N := by simp at hz; omega_using [hp, hz]
      apply WP.block_nil
      have hd : doneAt g p₀ sk (n + 1) = p := by simp only [doneAt, p] at hpN ⊢; omega_using [hpN]
      exact {
        prga := by rw [hd]; exact h.prga
        data := by rw [hd]; exact h.data
        x5 := by rw [h.x5]; congr 1; omega_using [hge]
        x8 := h.x8
        next := fun hlt => absurd hlt (by omega_using [hpN, hd])
        kept := h.kept
        vkept := h.vkept }
    · intro hnz2
      have hpN : p < g.N := by simp at hnz2; omega_using [hnz2]
      obtain ⟨hi, hsi⟩ := h.next hpN
      rw [show max n sk = n by omega_using [hge]] at hi hsi
      have hd : InRegions s.wr (s.gpr .x1) 1 := by rw [h.data.x1]; exact hg.byte h.kept hpN
      refine WP.mono (byte_ok hn h.prga hi hsi hd) fun t ⟨pr, tsi, m, x1, x2, gg, vv, rd, wr, sp⟩ => ?_
      have hd1 : doneAt g p₀ sk (n + 1) = p + 1 := by simp only [doneAt, p] at hpN ⊢; omega_using [hge, hpN]
      have bytes : ∀ k < g.N, t.mem (g.D + BitVec.ofNat 64 k) =
          if k < p + 1 then g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k
          else g.M₀ (g.D + BitVec.ofNat 64 k) := by
        intro k hk
        rw [m, h.data.x1, write_byte_apply]
        have hne : (g.D + BitVec.ofNat 64 k = g.D + BitVec.ofNat 64 p) ↔ k = p := by
          constructor
          · intro e; have := congrArg (fun x => (x - g.D).toNat) e
            simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at this
            rw [Nat.mod_eq_of_lt (by omega_using [hfit, hk]), Nat.mod_eq_of_lt (by omega_using [hfit, hp])] at this; exact this
          · intro e; rw [e]
        by_cases hkp : k = p
        · subst hkp
          rw [ite_eq_left rfl, h.data.bytes _ hk, ite_eq_right (by omega_using []), ite_eq_left (by omega_using [])]
          rfl
        · rw [ite_eq_right (fun e => hkp (hne.mp e)), h.data.bytes k hk]
          exact ite_iff ⟨fun h' => by omega_using [h'], fun h' => by omega_using [hkp, h']⟩ _ _
      have nexti : (stepN g.c₀ (p + 1)).i + 1 = BitVec.ofNat 8 (B + max (n + 1) sk) := by
        rw [show stepN g.c₀ (p + 1) = (step (stepN g.c₀ p)).1 from rfl, show max (n + 1) sk = n + 1 by omega_using [hge]]
        simp only [step]
        rw [hi]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 8).toNat = 1 from rfl]
        omega_using []
      exact {
        prga := by rw [hd1]; exact pr
        data := by
          rw [hd1]
          refine ⟨by omega_using [hpN], ?_, ?_, bytes, ?_⟩
          · rw [x1, h.data.x1, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
              BitVec.ofNat_add_ofNat]
          · rw [x2, h.data.x2, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
              BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hpN])]
            congr 1
          · rw [m, h.data.x1]
            exact h.data.frame.write List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hpN]) (by omega_using [hfit, hp]))
        x5 := by
          rw [gg _ (by decide) (by decide) (by decide) (by decide), h.x5]; congr 1; omega_using [hge]
        x8 := by rw [gg _ (by decide) (by decide) (by decide) (by decide), h.x8]
        next := by
          rw [hd1]
          exact fun _ => ⟨nexti, by rw [tsi, show max (n + 1) sk = n + 1 by omega_using [hge]]⟩
        kept := ⟨fun r a b c d e f => by rw [gg r a b d e, h.kept.gpr r a b c d e f],
          rd.trans h.kept.rd, wr.trans h.kept.wr, sp.trans h.kept.sp⟩
        vkept := fun r hr hn => by rw [vv r hr, h.vkept r hr hn] }

end VG.Proof.Rc4.AArch64

end

end

/-! ### `Rc4.AArch64.Consts`, which this module and modules that import it used -/

section

/-!
# The constants

`constants_ok`: the lane numbers 0–63 in `v8`–`v11`, and 64 and 128 in
every byte of `v12` and `v13`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem lanes0 (v : BitVec 128) :
    setLane (setLane v 64 0 0x0706050403020100#64) 64 1 0x0f0e0d0c0b0a0908#64 = laneNums 0 := by
  rw [setLane_two]
  decide

theorem lanes_next (q : Nat) :
    VArr.b16.map2 (fun _ x y => x + y) (laneNums q) (bc 16) = laneNums (q + 1) :=
  vbyte_ext fun e he => by
    rw [vbyte_map2 _ _ _ he, laneNums, laneNums, vbyte_ofVBytes _ he, vbyte_ofVBytes _ he,
      vbyte_bc _ he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
    omega_using []

theorem bc_lit (b : BitVec 8) : (ofVBytes fun _ => b) = bc b := rfl

theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t =>
      t.gpr r = v ∧ (∀ g, g ≠ r → t.gpr g = s.gpr g) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.of_runBlock ⟨_, rfl, ?_, fun g hg => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v
  · simp [State.write, hg]

theorem constants_ok (s : State) :
    WP isa (.block constants) s fun t =>
      Consts t ∧ (∀ v, v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 → v ≠ .v11 → v ≠ .v12 → v ≠ .v13 →
        t.v v = s.v v) ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold constants
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const64_ok s .x6 _) fun a ⟨a6, ag, av, am, ard, awr, asp⟩ => ?_
  refine WP.mono (const64_ok a .x7 _) fun b ⟨b7, bg, bv, bm, brd, bwr, bsp⟩ => ?_
  have b6 : b.gpr .x6 = 0x0706050403020100#64 := by rw [bg _ (by decide), a6]; rfl
  have b7' : b.gpr .x7 = 0x0f0e0d0c0b0a0908#64 := by rw [b7]; rfl
  have l0 : lanes 0 = .v8 := rfl
  have l1 : lanes 1 = .v9 := rfl
  have l2 : lanes 2 = .v10 := rfl
  have l3 : lanes 3 = .v11 := rfl
  have k64 : c64 = .v12 := rfl
  have k128 : c128 = .v13 := rfl
  rrun [l0, l1, l2, l3, k64, k128, b6, b7', bc_lit]
  have L0 := lanes0 (b.v .v8)
  have L1 : VArr.b16.map2 (fun _ x y => x + y) (laneNums 0) (bc 16#8) = laneNums 1 := lanes_next 0
  have L2 : VArr.b16.map2 (fun _ x y => x + y) (laneNums 1) (bc 16#8) = laneNums 2 := lanes_next 1
  have L3 : VArr.b16.map2 (fun _ x y => x + y) (laneNums 2) (bc 16#8) = laneNums 3 := lanes_next 2
  refine ⟨⟨fun q hq => ?_, ?_, ?_⟩, fun v h7 h8 h9 h10 h11 h12 h13 => ?_, fun g h6 h7 => ?_,
    ?_, ?_, ?_, ?_⟩
  · rcases (by omega_using [hq] : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
      simp [State.setV, State.write, l0, l1, l2, l3, L0, L1, L2, L3]
  · simp [State.setV, State.write, k64]
  · simp [State.setV, State.write, k128]
  · simp [h7, h8, h9, h10, h11, h12, h13, bv, av]
  · simp [h6, h7, bg, ag]
  · simp [bm, am]
  · simp [brd, ard]
  · simp [bwr, awr]
  · simp [State.setV, State.write, bsp, asp]

end VG.Proof.Rc4.AArch64

end

end

/-!
# The PRGA's setup

`applySetup_ok`: the setup saves the callee-saved vector registers it uses
in general-purpose registers, reads `i` and `j`, and computes the first
group's base `B = (i + 1) mod 256` rounded down to 16 and the lanes to skip
`sk = (i + 1) mod 16`; loads the table from `B`; and leaves the constants,
`j - B`, `-B` and `S[i + 1]` broadcast: the first group's `LaneInv`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The first group, from `i`. -/
def i1 (i : BitVec 8) : Nat := (i.toNat + 1) % 256
def sk0 (i : BitVec 8) : Nat := i1 i % 16
def base0 (i : BitVec 8) : Nat := i1 i - sk0 i

theorem incr_byte (I : BitVec 8) :
    (I.setWidth 64 + 1#64) &&& BitVec.setWidth 64 255#16 = BitVec.ofNat 64 (i1 I) := by
  rw [show BitVec.setWidth 64 255#16 = 255#64 from rfl, and255]
  congr 1
  simp only [i1, BitVec.toNat_add, BitVec.toNat_setWidth, show (1#64).toNat = 1 from rfl]
  have := I.isLt
  omega_using []

theorem low4 (n : Nat) (hn : n < 256) :
    BitVec.ofNat 64 n &&& BitVec.setWidth 64 15#16 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.setWidth 64 15#16).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem read_byte' (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p : BitVec 8) = m p
  exact BitVec.zero_width_append _ _

/-- The general-purpose registers the setup writes. -/
def setupRegs : List Reg :=
  [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The save and the scalar part of the setup. -/
theorem setupA_ok {s : State} (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258) :
    WP isa (.block (save true ++ ([.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0,
      .add .x .x4 .x12 .x2, .addImm .x .x6 .x12 1, .logic .and .x .x6 .x6 .x9, .movz .x .x7 15 0,
      .logic .and .x .x5 .x6 .x7, .sub .x .x8 .x6 .x5] : List Instr))) s fun t =>
      let c := contextAt s.mem (s.gpr .x0)
      t.gpr .x13 = c.j.setWidth 64 ∧ t.gpr .x9 = 255#64 ∧
      t.gpr .x4 = c.i.setWidth 64 + s.gpr .x2 ∧
      t.gpr .x5 = BitVec.ofNat 64 (sk0 c.i) ∧ t.gpr .x8 = BitVec.ofNat 64 (base0 c.i) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ p ∈ saved true, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ∉ setupRegs → t.gpr g = s.gpr g) := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hc (x : BitVec 8) : (x.setWidth 32).setWidth 64 = x.setWidth 64 :=
    BitVec.setWidth_setWidth (by decide)
  unfold save saved
  have hi1 : i1 (s.mem (s.gpr .x0 + 256#64)) < 256 := by simp only [i1]; omega_using []
  rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil, h256, h257, read_byte', hc,
    incr_byte, low4 _ hi1]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [])]; rfl
  · simp [State.write]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [negBase]
  · intro g hg
    simp only [setupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
    obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hg
    simp [h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

theorem low_sub (j : BitVec 8) (B : Nat) :
    (j.setWidth 64 - BitVec.ofNat 64 B).setWidth 8 = j - bB B := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := j.isLt
  omega_using []

theorem low_neg (B : Nat) : (255#64 - BitVec.ofNat 64 B + 1#64).setWidth 8 = 0 - bB B := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (255#64).toNat = 255 from rfl, show (1#64).toNat = 1 from rfl,
    show (0 : BitVec 8).toNat = 0 from rfl]
  omega_using []

theorem low_nat (n : Nat) : (BitVec.ofNat 64 n).setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using []

theorem tbl_bc (x : BitVec 128) {k : Nat} (hk : k < 16) :
    (ofVBytes fun i => if (vbyte (bc (BitVec.ofNat 8 k)) i).toNat < 16 then
      vbyte x (vbyte (bc (BitVec.ofNat 8 k)) i).toNat else 0#8) = bc (vbyte x k) :=
  vbyte_ext fun e he => by
    rw [vbyte_ofVBytes _ he, vbyte_bc _ he, vbyte_bc _ he, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hk]), ite_eq_left hk]

theorem setupD_ok {s : State} {j : BitVec 8} {B sk : Nat} (hsk : sk < 16)
    (h13 : s.gpr .x13 = j.setWidth 64) (h8 : s.gpr .x8 = BitVec.ofNat 64 B)
    (h9 : s.gpr .x9 = 255#64) (h5 : s.gpr .x5 = BitVec.ofNat 64 sk) :
    WP isa (.block [.sub .x .x6 .x13 .x8, .vop (.dup .b16 (dq 0) .x6), .sub .x .x6 .x9 .x8,
      .addImm .x .x6 .x6 1, .vop (.dup .b16 negBase .x6), .vop (.dup .b16 .v7 .x5),
      .vop (.tbl si (treg 0) .v7)]) s fun t =>
      t.v (dq 0) = bc (j - bB B) ∧ t.v negBase = bc (0 - bB B) ∧
      t.v si = bc (vbyte (s.v (treg 0)) sk) ∧
      (∀ v, v ≠ dq 0 → v ≠ negBase → v ≠ .v7 → v ≠ si → t.v v = s.v v) ∧
      (∀ g, g ≠ .x6 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have d0 : dq 0 = .v0 := rfl
  have nb : negBase = .v14 := rfl
  have t0 : treg 0 = .v16 := rfl
  have s4 : si = .v4 := rfl
  rrun [d0, nb, t0, s4, h13, h8, h9, h5, bc_lit, low_sub, low_neg, low_nat, tbl_bc _ hsk]
  refine ⟨fun v a b c d => ?_, fun g hg => ?_, ?_⟩
  · simp [a, b, c, d]
  · simp [hg]
  · simp [State.setV, State.write]

theorem i1_eq (i : BitVec 8) : BitVec.ofNat 8 (base0 i + sk0 i) = i + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [base0, sk0, i1, BitVec.toNat_ofNat, BitVec.toNat_add, show (1 : BitVec 8).toNat = 1 from rfl]
  omega_using []

theorem base0_mod (i : BitVec 8) : base0 i % 16 = 0 := by simp only [base0, sk0]; omega_using []

theorem sk0_lt (i : BitVec 8) : sk0 i < 16 := by simp only [sk0]; omega_using []

/-- The loop's globals for the call from `s`, entering the loop in `t`. -/
def glob (s t : State) : Glob :=
  ⟨contextAt s.mem (s.gpr .x0), s.gpr .x1, (s.gpr .x2).toNat, s.mem, t⟩

theorem saved_ne : ∀ p ∈ saved true, p.2 ≠ .x6 ∧ p.2 ≠ .x7 := by decide

theorem applySetup_ok {s : State} (hp : InRegions s.wr (s.gpr .x0) 258) :
    WP isa (.block (applyLoad ++ applySetup)) s fun t =>
      let c := contextAt s.mem (s.gpr .x0)
      LaneInv (glob s t) (base0 c.i) 0 (sk0 c.i) 0 t ∧
      t.gpr .x4 = c.i.setWidth 64 + s.gpr .x2 ∧ t.gpr .x9 = 255#64 ∧
      (∀ p ∈ saved true, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ∉ setupRegs → t.gpr g = s.gpr g) ∧ t.v .v15 = s.v .v15 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hpr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258 :=
    let ⟨r, h1, h2⟩ := hp; ⟨r, List.mem_append_right _ h1, h2⟩
  have h256 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hpr
  unfold applyLoad applySetup
  rw [WP.block_append_iff]
  refine WP.mono (setupA_ok hpr) fun a ⟨a13, a9, a4, a5, a8, av, am, ard, awr, asp, asv, ag⟩ => ?_
  rw [List.append_assoc, WP.block_append_iff, loadTable_eq]
  have hpa : InRegions (a.rd ++ a.wr) (a.gpr .x0) 256 := by
    rw [ard, awr, ag .x0 (by decide)]; exact h256
  refine WP.mono (loadN_ok (base0_mod _) a8 a9 hpa (Nat.le_refl 16))
    fun b ⟨brow, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok b) fun e ⟨ec, ev, eg, em, erd, ewr, esp⟩ => ?_
  have e13 : e.gpr .x13 = (contextAt s.mem (s.gpr .x0)).j.setWidth 64 := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a13]
  have e8 : e.gpr .x8 = BitVec.ofNat 64 (base0 (contextAt s.mem (s.gpr .x0)).i) := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a8]
  have e9 : e.gpr .x9 = 255#64 := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a9]
  have e5 : e.gpr .x5 = BitVec.ofNat 64 (sk0 (contextAt s.mem (s.gpr .x0)).i) := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a5]
  refine WP.mono (setupD_ok (sk0_lt _) e13 e8 e9 e5)
    fun t ⟨tj, tnb, tsi, tv, tg, tm, trd, twr, tsp⟩ => ?_
  have gk : ∀ g, g ∉ setupRegs → t.gpr g = s.gpr g := fun g hg => by
    have h6 : g ≠ .x6 := fun h => hg (h ▸ by decide)
    have h7 : g ≠ .x7 := fun h => hg (h ▸ by decide)
    rw [tg g h6, eg g h6 h7, bg g h6 h7, ag g hg]
  have hsk := sk0_lt (contextAt s.mem (s.gpr .x0)).i
  have hd : doneAt (glob s t) 0 (sk0 (contextAt s.mem (s.gpr .x0)).i) 0 = 0 := by
    simp only [doneAt]; omega_using []
  refine ⟨LaneInv.mk ?_ ?_ ?_ ?_ ?_ ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩ fun _ _ _ => rfl, ?_, ?_,
    fun p hp => ?_, gk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]
    refine ⟨rows_table (m := s.mem) (p := s.gpr .x0) (base0_mod _) fun r hr => ?_, tj, tnb,
      ec.congr fun r hr => tv r ?_ ?_ ?_ ?_⟩
    · have ht := treg_ne r hr
      rw [tv _ ht.1 (by revert r; decide) (by revert r; decide) (by revert r; decide),
        ev _ (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide) (by revert r; decide),
        brow r hr, am, ag .x0 (by decide)]
    all_goals rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hd]
    refine ⟨Nat.zero_le _, ?_, ?_, fun k _ => ?_, ?_⟩
    · rw [gk .x1 (by decide)]; simp [glob]
    · rw [gk .x2 (by decide)]; simp [glob]
    · simp only [Nat.not_lt_zero, ite_false, glob]; rw [tm, em, bm, am]
    · rw [tm, em, bm, am]; exact Frame.refl _ _
  · rw [tg _ (by decide), eg _ (by decide) (by decide), bg _ (by decide) (by decide), a5,
      Nat.sub_zero]
  · rw [tg _ (by decide), e8]
  · intro _
    refine ⟨?_, ?_⟩
    · rw [hd, Nat.zero_max]; exact (i1_eq _).symm
    · rw [Nat.zero_max, tsi, tbyte, Nat.div_eq_of_lt hsk,
        Nat.mod_eq_of_lt hsk, tv (treg 0) (by decide) (by decide) (by decide) (by decide)]
  · rw [tg _ (by decide), eg _ (by decide) (by decide), bg _ (by decide) (by decide), a4]
  · rw [tg _ (by decide), e9]
  · obtain ⟨h6, h7⟩ := saved_ne p hp
    rw [tg _ h6, eg _ h6 h7, bg _ h6 h7, asv p hp]
  · rw [tv _ (by decide) (by decide) (by decide) (by decide),
      ev _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      bv _ (by decide), av]
  · rw [tm, em, bm, am]
  · rw [trd, erd, brd, ard]
  · rw [twr, ewr, bwr, awr]
  · rw [tsp, esp, bsp, asp]

end VG.Proof.Rc4.AArch64

end

end

/-! ### `Rc4.AArch64.ApplyFinish`, which the modules that import this one used -/

section

/-!
# The PRGA's finish

`finish_ok`: the table is stored back from its registers at base `B`, then
`i` and `j = (j - B) + B`, and the callee-saved vector registers are
restored.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem far_row {y p : Addr} {o : Nat} (ho : o + 16 ≤ 256) (h : ¬ (y - p).toNat < 258) :
    ¬ (y - (p + BitVec.ofNat 64 o)).toNat < 16 := by
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho])]
  have := (y - p).isLt
  rw [show 2 ^ 64 - o + (y - p).toNat = ((y - p).toNat - o) + 2 ^ 64 by omega_using [ho, h], Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])]
  omega_using [ho, h]

theorem j_byte (K : BitVec 8) (B : Nat) :
    (((bc K).extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 B).setWidth 8 = K + bB B := by
  have hl := congrArg BitVec.toNat (low_byte K)
  have hx := ((bc K).extractLsb' 0 32).isLt
  simp only [BitVec.toNat_setWidth] at hl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hl]

theorem low_setLane (v : BitVec 128) (a : BitVec 64) : (setLane v 64 0 a).extractLsb' 0 64 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp (disch := omega) [hi, decide_eq_true]

theorem i_byte (x : BitVec 64) : (x.setWidth 32).setWidth 8 = x.setWidth 8 :=
  BitVec.setWidth_setWidth (by decide)

/-- `i` and `j = (j - B) + B`. -/
theorem indices_ok {a : State} {B : Nat} {J : BitVec 8} (h8 : a.gpr .x8 = BitVec.ofNat 64 B)
    (hp : InRegions a.wr (a.gpr .x0) 258) (hj : a.v (dq 0) = bc (J - bB B)) :
    WP isa (.block [.strb .x4 .x0 256, .umov .w .x6 (dq 0) 0, .add .x .x6 .x6 .x8,
      .strb .x6 .x0 257]) a fun b =>
      b.mem = (a.mem.write (a.gpr .x0 + 256#64) 1 ((a.gpr .x4).setWidth 8)).write
        (a.gpr .x0 + 257#64) 1 J ∧
      b.v = a.v ∧ (∀ g, g ≠ .x6 → b.gpr g = a.gpr g) ∧ b.rd = a.rd ∧ b.wr = a.wr ∧ b.sp = a.sp := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [State.store, h256, h257, hj, h8, i_byte, j_byte, BitVec.sub_add_cancel]
  refine ⟨fun g hg => ?_, ?_⟩
  · simp [hg]
  · simp [State.write]

theorem restore_ok (prga : Bool) (s : State) :
    WP isa (.block (restore prga)) s fun t =>
      (∀ p ∈ saved prga, (t.v p.1).extractLsb' 0 64 = s.gpr p.2) ∧
      (∀ v, (∀ p ∈ saved prga, p.1 ≠ v) → t.v v = s.v v) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  cases prga <;>
  · unfold restore saved
    rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    refine ⟨fun p hp => ?_, fun v hv => ?_, by simp [State.setV]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [negBase, low_setLane]
    · simp only [List.forall_mem_cons] at hv
      try simp only [negBase] at hv ⊢
      simp only [show ∀ a : VReg, (v = a) = (a = v) from fun a => propext eq_comm]
      simp [hv]

theorem finish_ok {u : State} {B : Nat} {T : Table} {I J : BitVec 8} (hB : B % 16 = 0)
    (h8 : u.gpr .x8 = BitVec.ofNat 64 B) (h9 : u.gpr .x9 = 255#64)
    (hp : InRegions u.wr (u.gpr .x0) 258) (hT : TableIn u B T)
    (hj : u.v (dq 0) = bc (J - bB B)) (h4 : (u.gpr .x4).setWidth 8 = I) :
    WP isa (.block applyFinish) u fun t =>
      contextAt t.mem (u.gpr .x0) = ⟨T, I, J⟩ ∧
      (∀ y, ¬ (y - u.gpr .x0).toNat < 258 → t.mem y = u.mem y) ∧
      (∀ p ∈ saved true, (t.v p.1).extractLsb' 0 64 = u.gpr p.2) ∧ t.v .v15 = u.v .v15 ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp := by
  have h256w : InRegions u.wr (u.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hp
  unfold applyFinish
  rw [List.append_assoc, WP.block_append_iff, storeTable_eq]
  refine WP.mono (storeN_ok hB h8 h9 h256w (Nat.le_refl 16))
    fun a ⟨arow, aout, av, ag, ard, awr, asp⟩ => ?_
  have a0 : a.gpr .x0 = u.gpr .x0 := ag _ (by decide) (by decide)
  have a4 : a.gpr .x4 = u.gpr .x4 := ag _ (by decide) (by decide)
  have a8 : a.gpr .x8 = u.gpr .x8 := ag _ (by decide) (by decide)
  rw [WP.block_append_iff]
  have hpa : InRegions a.wr (a.gpr .x0) 258 := by rw [awr, a0]; exact hp
  refine WP.mono (indices_ok (J := J) (a8.trans h8) hpa (by rw [av]; exact hj))
    fun b ⟨bm, bv, bg, brd, bwr, bsp⟩ => ?_
  refine WP.mono (restore_ok true b) fun t ⟨tsv, tv, _, tm, trd, twr, tsp⟩ => ?_
  refine ⟨?_, fun y hy => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_⟩
  · rw [tm, bm, a0, a4, h4, context_finish, stored_table hB hT arow]
  · have hne (d : Nat) (hd : d < 258) : y ≠ u.gpr .x0 + BitVec.ofNat 64 d := fun e => by
      rw [e, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hy; omega_using [hB, h8, h9, hj, h4, asp, a0, a4, a8, bsp, tsp, hy, hd, e]
    rw [tm, bm, a0, write_byte, ite_eq_right (hne 257 (by decide)), write_byte,
      ite_eq_right (hne 256 (by decide))]
    exact aout y fun r _ => far_row (rowOff_le r hB) hy
  · obtain ⟨h6, h7⟩ := saved_ne p hp
    rw [tsv p hp, bg _ h6, ag _ h6 h7]
  · rw [tv _ (by decide), bv, av]
  · rw [trd, brd, ard]
  · rw [twr, bwr, awr]
  · rw [tsp, bsp, asp]

end VG.Proof.Rc4.AArch64

end

end

/-! ### `Rc4.AArch64.Rotate`, which this module and modules that import it used -/

section

/-!
# The rotation after a group

`rotate_ok`: the table registers move down by one (byte `k` becomes the old
byte `k + 16`, around the table), `j` and `-B` move back by 16, and the base
in `x8` advances by 16.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

def movs (n : Nat) : List Instr := (List.range n).map fun r => .vop (.mov (treg r) (treg (r + 1)))

theorem movs_succ (n : Nat) :
    movs (n + 1) = movs n ++ ([.vop (.mov (treg n) (treg (n + 1)))] : List Instr) := by
  simp only [movs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem movs_run (s : State) {n : Nat} (hn : n ≤ 15) :
    ∃ t, runBlock isa (movs n) s = some t ∧ (∀ r < 16, t.v (treg r) =
      if r < n then s.v (treg (r + 1)) else s.v (treg r)) ∧ Only (treg 0 :: (List.range 15).map treg) s t := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun r _ => by simp, Only.refl _ _⟩
  | succ n ih =>
    obtain ⟨t, run, v, o⟩ := ih (by omega_using [hn])
    let t' := t.setV (treg n) (t.v (treg (n + 1)))
    refine ⟨t', ?_, fun r hr => ?_, o.trans (Only.setV _ (by
      simp only [List.mem_cons, List.mem_map, List.mem_range]
      exact .inr ⟨n, by omega_using [hn], rfl⟩) _)⟩
    · rw [movs_succ]
      exact runBlock_cat_some run (by rw [runBlock_cons]; exact rfl)
    · by_cases h : r = n
      · subst h
        simp only [t', v_setV_self, v (r + 1) (by omega_using [hn]), show ¬ r + 1 < r by omega_using [], ite_false,
          show r < r + 1 by omega_using [], ite_true]
      · rw [v_setV_of_ne _ _ (fun e => h (treg_inj _ hr _ (by omega_using [hn]) e)), v r hr]
        exact ite_iff ⟨fun h' => by omega_using [h'], fun h' => by omega_using [h, h']⟩ _ _

theorem lanes_diff : VArr.b16.map2 (fun _ x y => x - y) (laneNums 1) (laneNums 0) = bc 16 :=
  vbyte_ext fun e he => by
    rw [vbyte_map2 _ _ _ he, laneNums, laneNums, vbyte_ofVBytes _ he, vbyte_ofVBytes _ he,
      vbyte_bc _ he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
    omega_using []

theorem rotate_eq (prga : Bool) : rotate prga =
    ([.vop (.sub .b16 .v7 (lanes 1) (lanes 0)), .vop (.sub .b16 (dq 0) (dq 0) .v7)] : List Instr) ++
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) ++
        (([.vop (.mov .v7 (treg 0))] : List Instr) ++ (movs 15 ++
          ([.vop (.mov (treg 15) .v7), .addImm .x .x8 .x8 16] : List Instr)))) := by
  simp only [rotate, movs, List.append_assoc]

/-- The vector registers a rotation changes. -/
def rotRegs : List VReg := .v7 :: dq 0 :: negBase :: (List.range 16).map treg

theorem rotate_ok (prga : Bool) {s : State} (hk : Consts s) {J NB : BitVec 8}
    (hj : s.v (dq 0) = bc J) (hn : prga = true → s.v negBase = bc NB) :
    WP isa (.block (rotate prga)) s fun t =>
      (∀ k < 256, tbyte t.v k = tbyte s.v ((k + 16) % 256)) ∧ t.v (dq 0) = bc (J - 16) ∧
      t.v negBase = (if prga then bc (NB - 16) else s.v negBase) ∧
      t.gpr .x8 = s.gpr .x8 + 16 ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ rotRegs → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let s₁ := s.setV .v7 (VArr.b16.map2 (fun _ x y => x - y) (s.v (lanes 1)) (s.v (lanes 0)))
  have v₁ : s₁.v .v7 = bc 16 := by
    rw [v_setV_self, hk.lns 1 (by decide), hk.lns 0 (by decide), lanes_diff]
  let s₂ := s₁.setV (dq 0) (VArr.b16.map2 (fun _ x y => x - y) (s₁.v (dq 0)) (s₁.v .v7))
  have j₂ : s₂.v (dq 0) = bc (J - 16) := by
    rw [v_setV_self, v₁, v_setV_of_ne _ _ (by decide), hj, sub_bc]
  obtain ⟨s₃, run₃, n₃, o₃⟩ : ∃ s₃, runBlock isa
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) : List Instr) s₂ = some s₃ ∧
      s₃.v negBase = (if prga then bc (NB - 16) else s.v negBase) ∧ Only [negBase] s₂ s₃ := by
    cases prga
    · refine ⟨s₂, by simp only [Bool.false_eq_true, ite_false]; exact runBlock_nil, ?_, Only.refl _ _⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide)]
    · refine ⟨s₂.setV negBase (VArr.b16.map2 (fun _ x y => x - y) (s₂.v negBase) (s₂.v .v7)),
        by simp only [ite_true]; rw [runBlock_cons]; rfl, ?_, Only.setV _ (by simp) _⟩
      simp only [ite_true]
      rw [v_setV_self, v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), hn rfl,
        v_setV_of_ne _ _ (by decide), v₁, sub_bc]
  let s₄ := s₃.setV .v7 (s₃.v (treg 0))
  obtain ⟨s₅, run₅, v₅, o₅⟩ := movs_run s₄ (n := 15) (Nat.le_refl _)
  let s₆ := s₅.setV (treg 15) (s₅.v .v7)
  let s₇ := s₆.write .x .x8 (s₆.read .x .x8 + BitVec.ofNat _ 16)
  have run : runBlock isa (rotate prga) s = some s₇ := by
    rw [rotate_eq]
    refine runBlock_cat_some (s₁ := s₂) (by
      rw [runBlock_cons, show exec (.vop (.sub .b16 .v7 (lanes 1) (lanes 0))) s = some s₁ from rfl,
        runStep_some, runBlock_cons, show exec (.vop (.sub .b16 (dq 0) (dq 0) .v7)) s₁ = some s₂ from rfl,
        runStep_some, runBlock_nil]) ?_
    refine runBlock_cat_some run₃ ?_
    rw [List.singleton_append, runBlock_cons, show exec (.vop (.mov .v7 (treg 0))) s₃ = some s₄ from rfl,
      runStep_some]
    refine runBlock_cat_some run₅ ?_
    rw [runBlock_cons, show exec (.vop (.mov (treg 15) .v7)) s₅ = some s₆ from rfl, runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₇, run, ?_⟩
  have v₇ : s₇.v = s₆.v := rfl
  have movsRegs : ∀ r, r ∉ (treg 0 :: (List.range 15).map treg) → r ∉ (List.range 16).map treg →
      True := fun _ _ _ => trivial
  -- what the moves leave alone
  have keep₅ : ∀ r, NotTable r → s₅.v r = s₄.v r := fun r hr => o₅.2 r (by
    simp only [List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
    exact ⟨fun h => hr.ne 0 h.symm, fun a _ h => hr.ne a h⟩)
  have keep₂ : ∀ r, NotTable r → r ≠ .v7 → r ≠ dq 0 → r ≠ negBase → s₃.v r = s.v r := by
    intro r _ h7 hd hn
    rw [o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]
  have tab₃ : ∀ a < 16, s₃.v (treg a) = s.v (treg a) := by
    intro a ha
    rw [o₃.2 _ (by simp; exact fun h => absurd h (by revert a; decide)),
      v_setV_of_ne _ _ (by revert a; decide), v_setV_of_ne _ _ (by revert a; decide)]
  have g₆ : s₆.gpr = s.gpr := by
    show s₅.gpr = s.gpr; rw [o₅.gpr]; show s₃.gpr = s.gpr; rw [o₃.gpr]; rfl
  have m₇ : s₇.mem = s.mem := by
    show s₅.mem = s.mem; rw [o₅.mem]; show s₃.mem = s.mem; rw [o₃.mem]; rfl
  have rd₇ : s₇.rd = s.rd := by
    show s₅.rd = s.rd; rw [o₅.rd]; show s₃.rd = s.rd; rw [o₃.rd]; rfl
  have wr₇ : s₇.wr = s.wr := by
    show s₅.wr = s.wr; rw [o₅.wr]; show s₃.wr = s.wr; rw [o₃.wr]; rfl
  have sp₇ : s₇.sp = s.sp := by
    show s₅.sp = s.sp; rw [o₅.sp]; show s₃.sp = s.sp; rw [o₃.sp]; rfl
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, m₇, rd₇, wr₇, sp₇⟩
  · simp only [tbyte, v₇]
    by_cases h15 : k / 16 = 15
    · rw [h15, show s₆.v (treg 15) = s₅.v .v7 from v_setV_self _ _ _,
        keep₅ _ (by decide), v_setV_self, tab₃ 0 (by decide),
        show (k + 16) % 256 / 16 = 0 by omega_using [h15], show (k + 16) % 256 % 16 = k % 16 by omega_using []]
    · rw [v_setV_of_ne _ _ (fun e => h15 (treg_inj _ (by omega_using [hk]) _ (by decide) e)),
        v₅ _ (by omega_using [hk]), ite_eq_left (show k / 16 < 15 by omega_using [hk, h15]),
        v_setV_of_ne _ _ ((show NotTable .v7 by decide).ne _), tab₃ _ (by omega_using [hk, h15]),
        show (k + 16) % 256 / 16 = k / 16 + 1 by omega_using [hk, h15], show (k + 16) % 256 % 16 = k % 16 by omega_using []]
  · rw [v₇, v_setV_of_ne _ _ ((show NotTable (dq 0) by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), o₃.2 _ (by decide), j₂]
  · rw [v₇, v_setV_of_ne _ _ ((show NotTable negBase by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), n₃]
  · simp only [s₇, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [g₆]; rfl
  · simp only [s₇, State.write, BitVec.setWidth_eq, hr, ite_false]
    rw [g₆]
  · simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists,
      not_and] at hr
    obtain ⟨h7, hd, hn, ht⟩ := hr
    rw [v₇, v_setV_of_ne _ _ (fun e => ht 15 (by decide) e.symm), keep₅ r (fun a ha e => ht a (by omega_using [ha]) e),
      v_setV_of_ne _ _ h7, o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]

end VG.Proof.Rc4.AArch64

end

end

/-!
# The groups

`group_ok`: sixteen lanes and the rotation take a group with base `B` that
starts after `p` bytes to the next group, with base `B + 16`, after
`min N (p + 16 - sk)` bytes and no lanes to skip. `loop_ok`: the groups run
until the data has ended.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem lanesFrom_ok (g : Glob) (hg : DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {n : Nat} (hn : n ≤ 16)
    {s : State} (h : LaneInv g B p sk 0 s) : WP isa (lanesFrom n) s (LaneInv g B p sk n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega_using [hn])) fun t ht => lane_ok g hg hsk (by omega_using [hn]) ht)

theorem ofNat_wrap (B k : Nat) : BitVec.ofNat 8 (B + (k + 16) % 256) = BitVec.ofNat 8 (B + 16 + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega_using []

theorem byte_shift (x : BitVec 8) (B : Nat) : x - bB B - 16 = x - bB (B + 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
  omega_using []

theorem treg_step : ∀ a < 16, treg a ∈ stepRegs := by decide

theorem group_ok (g : Glob) (hg : DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {s : State}
    (h : LaneInv g B p sk 0 s) :
    WP isa group s (LaneInv g (B + 16) (doneAt g p sk 16) 0 0) := by
  apply WP.seq (WP.mono (lanesFrom_ok g hg hsk (Nat.le_refl 16) h) fun s₁ h₁ => ?_)
  refine WP.mono (rotate_ok true h₁.prga.consts h₁.prga.j fun _ => h₁.prga.nb) fun t ⟨tab, j, nb, x8, gg, vv, m, rd, wr, sp⟩ => ?_
  have hd0 : doneAt g (doneAt g p sk 16) 0 0 = doneAt g p sk 16 := by
    have := h₁.data.le; simp only [doneAt] at this ⊢; omega_using []
  let q := doneAt g p sk 16
  have notRot : ∀ r, r ∉ rotRegs → r ∉ stepRegs ∨ r = negBase → True := fun _ _ _ => trivial
  exact {
    prga := by
      rw [hd0]
      refine ⟨fun k hk => ?_, ?_, ?_, ?_⟩
      · rw [tab k hk, h₁.prga.table _ (by omega_using []), ofNat_wrap]
      · rw [j, byte_shift]
      · simp only [ite_true] at nb; rw [nb, byte_shift]
      · exact h₁.prga.consts.congr fun r hr => vv r (by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    data := by
      rw [hd0]
      exact ⟨h₁.data.le, by rw [gg _ (by decide), h₁.data.x1], by rw [gg _ (by decide), h₁.data.x2],
        fun k hk => by rw [m]; exact h₁.data.bytes k hk, by rw [m]; exact h₁.data.frame⟩
    x5 := by rw [gg _ (by decide), h₁.x5]; congr 1; omega_using [hsk]
    x8 := by
      rw [x8, h₁.x8, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    next := by
      rw [hd0]
      intro hlt
      obtain ⟨hi, hsi⟩ := h₁.next hlt
      rw [show max 16 sk = 16 by omega_using [hsk]] at hi hsi
      refine ⟨by rw [hi]; simp, ?_⟩
      rw [vv _ (by decide), hsi, show max 0 0 = 0 from rfl, tab 0 (by decide)]
    kept := ⟨fun r a b c d e f => by rw [gg r f, h₁.kept.gpr r a b c d e f], rd.trans h₁.kept.rd,
      wr.trans h₁.kept.wr, sp.trans h₁.kept.sp⟩
    vkept := fun r hr hn => by
      rw [vv r (by
        simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
        refine ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide), hn,
          fun a ha e => hr (e ▸ treg_step a ha)⟩), h₁.vkept r hr hn] }

/-- A group about to start, `m` bytes before the end. -/
def LoopInv (g : Glob) (m : Nat) (s : State) : Prop :=
  ∃ B p sk, B % 16 = 0 ∧ m = g.N - p ∧ p < g.N ∧ sk ≤ 15 ∧ LaneInv g B p sk 0 s

/-- The data has ended. -/
def LoopDone (g : Glob) (s : State) : Prop := ∃ B sk, B % 16 = 0 ∧ LaneInv g B g.N sk 0 s

theorem loop_ok (g : Glob) (hg : DataOk g) (m : Nat) {s : State} (h : LoopInv g m s) :
    WP isa (.loop group (.nonzero .x .x2)) s (LoopDone g) := by
  refine WP.loop (M := isa) (LoopInv g) ?_ m s h
  intro m s ⟨B, p, sk, hB, hm, hp, hsk, h⟩
  refine WP.mono (group_ok g hg hsk h) fun t ht => ?_
  have hfit := hg.fit
  let q := doneAt g p sk 16
  have hd0 : doneAt g q 0 0 = q := by
    have := ht.data.le; simp only [doneAt, q] at this ⊢; omega_using []
  have hq : q ≤ g.N := by have := ht.data.le; rw [hd0] at this; exact this
  have x2 : t.gpr .x2 = BitVec.ofNat 64 (g.N - q) := by rw [ht.data.x2, hd0]
  have flag := eval_nonzero' t .x2 x2 (by omega_using [hfit])
  by_cases hend : q = g.N
  · left
    exact ⟨by rw [flag]; simp [hend], B + 16, 0, by omega_using [hB], hend ▸ ht⟩
  · right
    exact ⟨by rw [flag]; simp; omega_using [hq, hend], g.N - q, by simp only [doneAt, q] at hend ⊢; omega_using [hm, hp, hsk],
      B + 16, q, 0, by omega_using [hB], rfl, by omega_using [hq, hend], by decide, ht⟩

end VG.Proof.Rc4.AArch64
