module

public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintBase
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.Pack.Hint
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.Arm.Pack.HintUnpackLoops`, which only this module used -/

section

/-! ### `MlDsa.Arm.Pack.HintUnpack`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, the steps

As on x86-64, the code follows the fold form of `HintBitUnpack`
(`hintBitUnpack_eq`, `Proof/MlDsa/Pack/Hint.lean`) step by step: while no
check has failed, the words of `h` are the hint of the spec (`HArr`) and `r1`
its index; once one has, `r1` is 256, which skips the rest (`SRel`). Here: the
arguments, zeroing `h`, and one coefficient (`first_ok`, `next_ok`); the loops
are in `HintUnpackLoops.lean`. They run from any state that permits reading
`y` and writing `h` (`MainPre`), so that constant time can narrow the state to
those two regions.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlKem (bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `y`, `len`, `ω`, `h` and `hlen`. -/
abbrev uY : BitVec 32 := s₀.gpr .r0
abbrev uL : BitVec 32 := s₀.gpr .r1
abbrev uW : BitVec 32 := s₀.gpr .r2
abbrev uH : BitVec 32 := s₀.gpr .r3
abbrev uHL : BitVec 32 := stackArg s₀ 0
abbrev uω : Nat := (uW s₀).toNat
abbrev uLen : Nat := (uL s₀).toNat
abbrev uk : Nat := uLen s₀ - uω s₀
abbrev uyR : Region := ⟨State.addr (uY s₀), uLen s₀⟩
abbrev uhR : Region := ⟨State.addr (uH s₀), (uHL s₀).toNat * 4⟩
abbrev uargR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The bytes of `y`, as the spec reads them. -/
abbrev uYs : Array Byte := (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)).toArray

end

/-- The precondition, as `sig_pre` states it. -/
structure UPre (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  spA : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [uyR s, uargR s]
  wr : s.wr = [uhR s]
  d_yh : (uyR s).Disjoint (uhR s)
  d_ha : (uhR s).Disjoint (uargR s)
  b_y : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uyR s)
  b_h : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uhR s)
  b_a : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uargR s)
  fitY : (uY s).toNat + uLen s ≤ 2 ^ 32
  fitH : (uH s).toNat + (uHL s).toNat * 4 ≤ 2 ^ 32
  par : (uω s, uk s) ∈ hintParams
  ωle : uω s ≤ uLen s
  hlen : (uHL s).toNat = 256 * uk s

theorem ufacts {s₀ : State} (hp : UPre s₀) : 4 ≤ uk s₀ ∧ uk s₀ ≤ 8 ∧ 55 ≤ uω s₀ ∧ uω s₀ ≤ 80 ∧
    uω s₀ + uk s₀ = uLen s₀ ∧ uLen s₀ ≤ 88 := by
  have := mem_hintParams hp.par
  have := hp.ωle
  have e : uk s₀ = uLen s₀ - uω s₀ := rfl
  omega_arith

/-! ## Zeroing `h` -/

theorem zeroPro_ok {s : State} :
    WP isa (.block [.dp .sub .r6 .r1 (.reg .r2), .mov .r4 (.reg .r12), .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
      s fun s' => s'.gpr .r6 = s.gpr .r1 - s.gpr .r2 ∧ s'.gpr .r4 = s.gpr .r12 ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r5 = s.gpr .r3 ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

theorem zeroStep_ok {s : State} {p c : BitVec 32} (h5 : s.gpr .r5 = p) (h4 : s.gpr .r4 = c)
    (o : InRegions s.wr (State.addr (p + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.str .r12 .r5 0, .dp .add .r5 .r5 (.imm 4), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = p + 4 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (p + BitVec.ofNat 32 0)) (s.gpr .r12) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r6 = s.gpr .r6 ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h5, h4, o]

theorem zeroEnd_ok {s : State} :
    WP isa (.block [.mov .r1 (.imm 0)]) s fun s' => s'.gpr .r1 = 0 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r1 → s'.gpr r = s.gpr r := by
  run_block []
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

/-- Zeroing the `hlen` words of `h`, from the entry values of the registers. -/
theorem zero_ok {s₀ : State} (hp : UPre s₀) {s : State} (h0 : s.gpr .r0 = uY s₀) (h1 : s.gpr .r1 = uL s₀)
    (h2 : s.gpr .r2 = uW s₀) (h3 : s.gpr .r3 = uH s₀) (h12 : s.gpr .r12 = uHL s₀) (hwr : uhR s₀ ∈ s.wr) :
    WP isa hbuZero s fun s' => s'.gpr .r0 = uY s₀ ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r2 = uW s₀ ∧
      s'.gpr .r3 = uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧
      (∀ t < 256 * uk s₀, coeffAt s'.mem (State.addr (uH s₀)) t = 0) ∧
      Frame [uhR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨hk4, hk8, -, -, hsum, hL88⟩ := ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  obtain hHL := (uHL s₀).isLt
  unfold hbuZero
  refine WP.seq (WP.mono zeroPro_ok fun s₁ ⟨r6₁, r4₁, r12₁, r5₁, r0₁, r2₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine WP.seq (wp_loop_ne (N := 256 * uk s₀) (fun t s' => s'.gpr .r5 = uH s₀ + BitVec.ofNat 32 (4 * t) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (1 * (256 * uk s₀ - t)) ∧ s'.gpr .r12 = 0 ∧ s'.gpr .r0 = uY s₀ ∧
      s'.gpr .r2 = uW s₀ ∧ s'.gpr .r3 = uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧
      Frame [uhR s₀] s.mem s'.mem ∧ (∀ u < t, coeffAt s'.mem (State.addr (uH s₀)) u = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by omega_arith)
    (fun t ht s' ⟨i5, i4, i12, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    (fun s₂ ⟨_, _, _, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    ⟨by rw [r5₁, h3]; simp, by rw [r4₁, h12, Nat.one_mul, Nat.sub_zero, ← hl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      r12₁, by rw [r0₁, h0], by rw [r2₁, h2], by rw [r3₁, h3], ?_, by rw [m₁]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), rd₁, wr₁, sp₁⟩)
  · have ea : State.addr (uH s₀ + BitVec.ofNat 32 (4 * t) + BitVec.ofNat 32 0) = coeffAddr (State.addr (uH s₀)) t :=
      by rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
    obtain hin : (uhR s₀).Contains (coeffAddr (State.addr (uH s₀)) t) 4 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine WP.mono (zeroStep_ok i5 i4 (by rw [ea, hwr']; exact ⟨_, hwr, hin⟩))
      fun s'' ⟨r5', r4', z', m', r0', r2', r3', r6', r12', rd', wr', sp'⟩ =>
        ⟨⟨by rw [r5', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, Nat.mul_succ],
          by rw [r4']; exact count_sub (k := 1) ht, by rw [r12', i12],
          by rw [r0', i0], by rw [r2', i2], by rw [r3', i3], by rw [r6', i6], ?_, fun u hu => ?_,
          by rw [rd', hrd], by rw [wr', hwr'], by rw [sp', hsp]⟩,
          by rw [z']; exact count_z (k := 1) ht (by decide) (by omega_arith)⟩
    · rw [m', ea]
      exact hf.writeW (List.mem_singleton_self _) _ hin
    · rw [m', ea, i12]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
      · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
          ← coeffAt_eq, hz u (by omega_arith)]
  · rw [r6₁, h1, h2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hp.ωle, toNat_ofNat32 (by omega_arith)]

  · refine WP.mono zeroEnd_ok
      fun s₃ ⟨r1₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ⟨by rw [g₃ _ (by decide), i0], r1₃, by rw [g₃ _ (by decide), i2],
        by rw [g₃ _ (by decide), i3], by rw [g₃ _ (by decide), i6], by rw [m₃]; exact hz,
        by rw [m₃]; exact hf, by rw [rd₃, hrd], by rw [wr₃, hwr'], by rw [sp₃, hsp]⟩

/-! ## The hint in memory -/

/-- The words of `h` are the hint `hA` of the spec. -/
def HArr (s₀ : State) (m : Mem) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = uk s₀ ∧ ∀ i < uk s₀, ∀ j < 256,
    coeffAt m (State.addr (uH s₀)) (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `r1`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .r1 = BitVec.ofNat 32 idx ∧ idx ≤ uω s₀ ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .r1 = 256

/-- What the loops that read `y` need of the state they start from:
permission to read it, and its bytes of the entry state. -/
structure YPre (s₀ sA : State) : Prop where
  rd : uyR s₀ ∈ sA.rd
  y : ∀ t < uLen s₀, sA.mem (State.addr (uY s₀) + BitVec.ofNat 64 t) = s₀.mem (State.addr (uY s₀) + BitVec.ofNat 64 t)

/-- ... and those that write `h`: permission to write it. -/
structure MainPre (s₀ sA : State) : Prop extends YPre s₀ sA where
  wr : uhR s₀ ∈ sA.wr

/-- What stays the same in the loops that start from `sA`. -/
structure UCom (s₀ sA s : State) : Prop where
  r0 : s.gpr .r0 = uY s₀
  r2 : s.gpr .r2 = uW s₀
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [uhR s₀] sA.mem s.mem

/-- A step of the loops over the coefficients: it writes at most `r1`, `r7`
and `r12`. -/
def KeepC (s s' : State) : Prop :=
  (∀ r, r ≠ .r1 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem KeepC.refl (s : State) : KeepC s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl⟩

theorem KeepC.trans {s s' s'' : State} (h : KeepC s s') (h' : KeepC s' s'') : KeepC s s'' :=
  ⟨fun r a b c => (h'.1 r a b c).trans (h.1 r a b c), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem UCom.of {s₀ sA s s' : State} (h : UCom s₀ sA s) (hk : KeepC s s') (hm : Frame [uhR s₀] s.mem s'.mem) :
    UCom s₀ sA s' :=
  ⟨(hk.1 _ (by decide) (by decide) (by decide)).trans h.r0, (hk.1 _ (by decide) (by decide) (by decide)).trans h.r2,
    hk.2.1.trans h.rd, hk.2.2.1.trans h.wr, hk.2.2.2.trans h.sp, h.frame.trans hm⟩

/-- Where the loops of polynomial `i` are. -/
structure PCom (s₀ sA : State) (i bound : Nat) (s : State) : Prop where
  com : UCom s₀ sA s
  r3 : s.gpr .r3 = uH s₀ + BitVec.ofNat 32 (1024 * i)
  r4 : s.gpr .r4 = BitVec.ofNat 32 bound

theorem PCom.of {s₀ sA s s' : State} {i bound : Nat} (h : PCom s₀ sA i bound s) (hk : KeepC s s')
    (hm : Frame [uhR s₀] s.mem s'.mem) : PCom s₀ sA i bound s' :=
  ⟨h.com.of hk hm, (hk.1 _ (by decide) (by decide) (by decide)).trans h.r3,
    (hk.1 _ (by decide) (by decide) (by decide)).trans h.r4⟩

theorem harr_set {s₀ : State} (hp : UPre s₀) {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) {i b : Nat}
    (hi : i < uk s₀) (hb : b < 256) :
    HArr s₀ (m.writeW (coeffAddr (State.addr (uH s₀)) (256 * i + b)) (1 : BitVec 32)) (huSet i b hA) := by
  obtain ⟨hk4, hk8, -, -, -, -⟩ := ufacts hp
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega_arith, by omega_arith⟩
      omega_arith) (by omega_arith) (by omega_arith)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

theorem harr_zero {s₀ : State} {m : Mem} (hz : ∀ t < 256 * uk s₀, coeffAt m (State.addr (uH s₀)) t = 0) :
    HArr s₀ m (Array.replicate (uk s₀) noHint) := by
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega_arith)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s₀ : State} (hp : UPre s₀) {sA s : State} (hA : YPre s₀ sA) (hc : UCom s₀ sA s) {t : Nat}
    (ht : t < uLen s₀) : s.mem (State.addr (uY s₀) + BitVec.ofNat 64 t) = (uYs s₀).getD t 0 := by
  have fY := hp.fitY
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht,
    ← hA.y t ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.d_yh _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc'

/-! ## Blocks -/

theorem ltBit_ok (t x y : Reg) (s : State) :
    WP isa (.block (ltBit t x y)) s fun s' => s'.gpr t = (s.gpr x - s.gpr y) >>> 31 ∧
      s'.z = ((s.gpr x - s.gpr y) >>> 31 - 0 == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r, r ≠ t → s'.gpr r = s.gpr r := by
  run_block [ltBit, eq_self_iff_true, true_and, and_true]
  intro r hr; rw [ite_neg' hr, ite_neg' hr]

theorem set_blk {s : State} {y i h : BitVec 32} {b : Byte} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (h3 : s.gpr .r3 = h) (ib : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1)
    (hb : s.mem (State.addr (y + i + BitVec.ofNat 32 0)) = b)
    (ow : InRegions s.wr (State.addr (h + (b.setWidth 32 <<< 2) + BitVec.ofNat 32 0)) 4) :
    WP isa (.block hbuSet) s fun s' => s'.gpr .r1 = i + 1 ∧
      s'.mem = s.mem.writeW (State.addr (h + (b.setWidth 32 <<< 2) + BitVec.ofNat 32 0)) (1 : BitVec 32) ∧
      KeepC s s' := by
  run_block [hbuSet, KeepC, h0, h1, h3, ib, hb, ow, true_and, and_true]
  intro r a b c; rw [ite_neg' a, ite_neg' b, ite_neg' c, ite_neg' c, ite_neg' c]

theorem fail_ok {s : State} :
    WP isa hbuFail s fun s' => s'.gpr .r1 = 256 ∧ s'.mem = s.mem ∧ KeepC s s' := by
  unfold hbuFail
  run_block [KeepC, true_and, and_true]
  intro r a _ _; rw [ite_neg' a]

theorem keepC_r7 {s s' : State} (h : ∀ r, r ≠ .r7 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : KeepC s s' := ⟨fun r _ b _ => h r b, hrd, hwr, hsp⟩

/-- The byte `strb`'s index of `h`, as a word offset. -/
theorem shl2_byte (b : Byte) : (b.setWidth 32 <<< 2 : BitVec 32) = BitVec.ofNat 32 (4 * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, toNat_ofNat32 (by have := b.isLt; omega_arith),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith), Nat.shiftLeft_eq]
  have := b.isLt
  omega_arith

theorem nextLoad_blk {s : State} {y i : BitVec 32} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (ic : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1)
    (ip : InRegions (s.rd ++ s.wr) (State.addr (y + i - 1 + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r12 .r0 (.reg .r1), .ldrb .r7 .r12 0, .dp .sub .r12 .r12 (.imm 1), .ldrb .r12 .r12 0])
      s fun s' => s'.gpr .r7 = (s.mem (State.addr (y + i + BitVec.ofNat 32 0))).setWidth 32 ∧
        s'.gpr .r12 = (s.mem (State.addr (y + i - 1 + BitVec.ofNat 32 0))).setWidth 32 ∧ s'.mem = s.mem ∧
        s'.gpr .r1 = i ∧ KeepC s s' := by
  run_block [KeepC, h0, h1, ic, ip, true_and, and_true]
  intro r _ b c; rw [ite_neg' c, ite_neg' c, ite_neg' b, ite_neg' c]

theorem ptr_pred (p : BitVec 32) {x : Nat} (h : 1 ≤ x) :
    p + BitVec.ofNat 32 x - 1 = p + BitVec.ofNat 32 (x - 1) := by
  rw [show x = (x - 1) + 1 by omega_arith, ← ofNat_succ32, ← BitVec.add_assoc, BitVec.add_sub_cancel,
    Nat.add_sub_cancel]

section
variable {s₀ : State} (hp : UPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- Setting coefficient `y[index]` of polynomial `i`. -/
theorem set_ok {i bound idx : Nat} (hi : i < uk s₀) (hidx : idx < uLen s₀) {hA' : Array (Vector Bool n)}
    {s : State} (hP : PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) (hh : HArr s₀ s.mem hA') :
    WP isa (.block hbuSet) s fun s' =>
      PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 (idx + 1) ∧
        HArr s₀ s'.mem (huSet i ((uYs s₀).getD idx 0).toNat hA') ∧ KeepC s s' := by
  obtain ⟨hk4, hk8, -, -, hsum, hL88⟩ := ufacts hp
  have fY := hp.fitY
  have fH := hp.fitH
  have hl := hp.hlen
  obtain hbl := ((uYs s₀).getD idx 0).isLt
  obtain ey : State.addr (uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0) = State.addr (uY s₀) + BitVec.ofNat 64 idx := by
    rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
  obtain hb : s.mem (State.addr (uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0)) = (uYs s₀).getD idx 0 := by
    rw [ey]; exact yByte hp hA.toYPre hP.com hidx
  obtain eh : State.addr (uH s₀ + BitVec.ofNat 32 (1024 * i) + (((uYs s₀).getD idx 0).setWidth 32 <<< 2) +
      BitVec.ofNat 32 0) = coeffAddr (State.addr (uH s₀)) (256 * i + ((uYs s₀).getD idx 0).toNat) := by
    rw [shl2_byte, ptr_add, addr_ptr _ _ _ (by omega_arith)]
    congr 2; omega_arith
  obtain hin : (uhR s₀).Contains (coeffAddr (State.addr (uH s₀)) (256 * i + ((uYs s₀).getD idx 0).toNat)) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.mono (set_blk hP.com.r0 h1 hP.r3 (by
      rw [ey, hP.com.rd, hP.com.wr]
      exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) hb
      (by rw [eh, hP.com.wr]; exact ⟨_, hA.wr, hin⟩))
    fun s' ⟨r1', m', k'⟩ => ⟨hP.of k' ?_, by rw [r1', ofNat_succ32], ?_, k'⟩
  · rw [m', eh]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hin
  · rw [m', eh]; exact harr_set hp hh hi hbl

/-- The first coefficient of polynomial `i`, from the index `first`. -/
theorem first_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first < bound) (hbω : bound ≤ uω s₀)
    {hA' : Array (Vector Bool n)} {s : State} (hP : PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 first)
    (hh : HArr s₀ s.mem hA') :
    WP isa (.block (hbuSet ++ hbuMore)) s fun s' =>
      PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 (first + 1) ∧
        HArr s₀ s'.mem (huSet i ((uYs s₀).getD first 0).toNat hA') ∧ s'.z = decide (bound ≤ first + 1) ∧
        KeepC s s' := by
  obtain ⟨-, -, -, hω80, hsum, -⟩ := ufacts hp
  rw [WP.block_append_iff]
  refine WP.mono (set_ok hp hA hi (by omega_arith) hP h1 hh) fun s₁ ⟨hP₁, r1₁, hh₁, k₁⟩ => ?_
  refine WP.mono (ltBit_ok .r7 .r1 .r4 s₁) fun s₂ ⟨_, z₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
  obtain k₂ := keepC_r7 g₂ rd₂ wr₂ sp₂
  refine ⟨hP₁.of k₂ (by rw [m₂]; exact Frame.refl _ _), by rw [g₂ _ (by decide), r1₁], by rw [m₂]; exact hh₁, ?_,
    k₁.trans k₂⟩
  rw [z₂, r1₁, hP₁.r4, ltBit_z (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith) (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith),
    toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)]

/-- A coefficient after the first: checked against the previous one. -/
theorem next_ok {i bound first idx : Nat} (hi : i < uk s₀) (hfi : first < idx) (hib : idx < bound)
    (hbω : bound ≤ uω s₀) {hA' : Array (Vector Bool n)} {s : State} (hP : PCom s₀ sA i bound s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) (hh : HArr s₀ s.mem hA') :
    WP isa hbuNext s fun s' => PCom s₀ sA i bound s' ∧
      (match huStep (uYs s₀) i first (hA', idx) 0 with
        | some (hA'', idx') => s'.gpr .r1 = BitVec.ofNat 32 idx' ∧ HArr s₀ s'.mem hA'' ∧
          s'.z = decide (bound ≤ idx')
        | none => s'.gpr .r1 = 256 ∧ s'.z = true) ∧ KeepC s s' := by
  obtain ⟨-, -, -, hω80, hsum, hL88⟩ := ufacts hp
  have fY := hp.fitY
  obtain ec : State.addr (uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0) = State.addr (uY s₀) + BitVec.ofNat 64 idx := by
    rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
  obtain ep : State.addr (uY s₀ + BitVec.ofNat 32 idx - 1 + BitVec.ofNat 32 0) =
      State.addr (uY s₀) + BitVec.ofNat 64 (idx - 1) := by
    rw [ptr_pred _ (by omega_arith), addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
  obtain hrw : s.rd ++ s.wr = sA.rd ++ sA.wr := by rw [hP.com.rd, hP.com.wr]
  unfold hbuNext
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (nextLoad_blk hP.com.r0 h1 (by
      rw [ec, hrw]; exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by rw [ep, hrw]; exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun s₁ ⟨r7₁, r12₁, m₁, r1₁, k₁⟩ => ?_
  rw [ec, yByte hp hA.toYPre hP.com (by omega_arith)] at r7₁
  rw [ep, yByte hp hA.toYPre hP.com (by omega_arith)] at r12₁
  obtain hP₁ : PCom s₀ sA i bound s₁ := hP.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.mono (ltBit_ok .r7 .r12 .r7 s₁) fun s₂ ⟨_, z₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
  obtain k₂ := keepC_r7 g₂ rd₂ wr₂ sp₂
  obtain hP₂ : PCom s₀ sA i bound s₂ := hP₁.of k₂ (by rw [m₂]; exact Frame.refl _ _)
  obtain hcb := ((uYs s₀).getD idx 0).isLt
  obtain hpb := ((uYs s₀).getD (idx - 1) 0).isLt
  rw [r7₁, r12₁, ltBit_z (by rw [byte_toNat32]; omega_arith) (by rw [byte_toNat32]; omega_arith), byte_toNat32,
    byte_toNat32] at z₂
  obtain h1₂ : s₂.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₂ _ (by decide), r1₁]
  refine WP.seq (WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_))
  · -- Not increasing: fail.
    obtain hge : ((uYs s₀).getD idx 0).toNat ≤ ((uYs s₀).getD (idx - 1) 0).toNat := by
      rw [z₂] at hge; simpa using hge
    obtain hs : huStep (uYs s₀) i first (hA', idx) 0 = none := by
      simp only [huStep]; rw [ite_pos' ⟨hfi, hge⟩]
    rw [hs]
    refine WP.mono fail_ok fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
    refine WP.mono (ltBit_ok .r7 .r1 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
    obtain k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
    refine ⟨hP₂.of (k₃.trans k₄) (by rw [m₄, m₃]; exact Frame.refl _ _), ⟨by rw [g₄ _ (by decide), r1₃], ?_⟩,
      ((k₁.trans k₂).trans k₃).trans k₄⟩
    rw [z₄, r1₃, (hP₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).r4,
      ltBit_z (by decide) (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith), toNat_ofNat32 (by omega_arith),
      show (256 : BitVec 32).toNat = 256 from rfl]
    exact decide_eq_true (by omega_arith)
  · -- `y[index - 1] < y[index]`: set it.
    obtain hlt : ((uYs s₀).getD (idx - 1) 0).toNat < ((uYs s₀).getD idx 0).toNat := by
      rw [z₂] at hlt; simpa using hlt
    obtain hs : huStep (uYs s₀) i first (hA', idx) 0 = some (huSet i ((uYs s₀).getD idx 0).toNat hA', idx + 1) := by
      simp only [huStep]; rw [ite_neg' (by omega_arith)]
    rw [hs]
    refine WP.mono (set_ok hp hA hi (hA' := hA') (by omega_arith) hP₂ h1₂ (by rw [m₂, m₁]; exact hh))
      fun s₃ ⟨hP₃, r1₃, hh₃, k₃⟩ => ?_
    refine WP.mono (ltBit_ok .r7 .r1 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
    obtain k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
    refine ⟨hP₃.of k₄ (by rw [m₄]; exact Frame.refl _ _), ⟨by rw [g₄ _ (by decide), r1₃], by rw [m₄]; exact hh₃, ?_⟩,
      ((k₁.trans k₂).trans k₃).trans k₄⟩
    rw [z₄, r1₃, hP₃.r4, ltBit_z (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith) (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith),
      toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)]

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

end

end


/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, the loops

The loops of `vg_mldsa_hint_bit_unpack`, as on x86-64: the coefficients of a
polynomial (`coefs_ok`), the polynomials (`main_ok`), each an iteration of the
fold `huPoly` of the spec, and the bytes after the last index (`trail_ok`),
from any state that permits reading `y` and writing `h` (`MainPre`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-- The state after the coefficients of a polynomial, up to the bound. -/
def SIn (s₀ : State) (bound : Nat) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => idx = bound ∧ s.gpr .r1 = BitVec.ofNat 32 idx ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .r1 = 256

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

section
variable {s₀ : State} (hp : UPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- The coefficients after the first. -/
theorem nexts_ok {i bound first : Nat} (hi : i < uk s₀) (hbω : bound ≤ uω s₀) {hA₀ : Array (Vector Bool n)}
    {t : Nat} (ht1 : 1 ≤ t) {hA' : Array (Vector Bool n)} {idx' : Nat}
    (hF : optFold (huStep (uYs s₀) i first) (List.range t) (hA₀, first) = some (hA', idx'))
    (hidx : idx' = first + t) (hlt : idx' < bound) {s : State} (hP : PCom s₀ sA i bound s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx') (hh : HArr s₀ s.mem hA') :
    WP isa (.loop hbuNext .ne) s fun s' => PCom s₀ sA i bound s' ∧
      SIn s₀ bound (optFold (huStep (uYs s₀) i first) (List.range (bound - first)) (hA₀, first)) s' ∧
      KeepC s s' := by
  refine WP.loop (M := isa) (fun m s' => ∃ t hA' idx', m = bound - idx' ∧ 1 ≤ t ∧
      optFold (huStep (uYs s₀) i first) (List.range t) (hA₀, first) = some (hA', idx') ∧ idx' = first + t ∧
      idx' < bound ∧ PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 idx' ∧ HArr s₀ s'.mem hA' ∧
      KeepC s s')
    (fun m s' ⟨t, hA', idx', hm, ht1, hF, hidx, hlt, hP', h1', hh', hk'⟩ => ?_) _ s
    ⟨t, hA', idx', rfl, ht1, hF, hidx, hlt, hP, h1, hh, KeepC.refl _⟩
  refine WP.mono (next_ok hp hA hi (first := first) (by omega_arith) hlt hbω hP' h1' hh') fun s'' ⟨hP'', hm'', hk''⟩ => ?_
  obtain hF1 : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA₀, first) =
      huStep (uYs s₀) i first (hA', idx') t := by rw [optFold_range_succ, hF]; rfl
  cases hs : huStep (uYs s₀) i first (hA', idx') 0 with
  | none =>
    rw [hs] at hm''
    obtain ⟨r1'', z''⟩ := hm''
    refine .inl ⟨by show some (!s''.z) = some false; rw [z'']; rfl, hP'', ?_, hk'.trans hk''⟩
    have : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA₀, first) = none := by
      rw [hF1]; exact hs
    rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega_arith) this]
    exact r1''
  | some st =>
    rw [hs] at hm''
    obtain ⟨hA'', idx''⟩ := st
    obtain ⟨r1'', hh'', z''⟩ := hm''
    obtain hi'' : idx'' = idx' + 1 := huStep_idx hs
    obtain hF2 : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA₀, first) = some (hA'', idx'') := by
      rw [hF1]; exact hs
    by_cases e : idx'' < bound
    · refine .inr ⟨by show some (!s''.z) = some true; rw [z'', decide_eq_false (by omega_arith)]; rfl, bound - idx'',
        by omega_arith, t + 1, hA'', idx'', rfl, by omega_arith, hF2, by omega_arith, e, hP'', r1'', hh'', hk'.trans hk''⟩
    · refine .inl ⟨by show some (!s''.z) = some false; rw [z'', decide_eq_true (by omega_arith)]; rfl, hP'', ?_,
        hk'.trans hk''⟩
      rw [show bound - first = t + 1 by omega_arith, hF2]
      exact ⟨by omega_arith, r1'', hh''⟩

/-- The coefficients of polynomial `i`, from the index `first`, up to the bound. -/
theorem coefs_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ uω s₀)
    {hA₀ : Array (Vector Bool n)} {s : State} (hP : PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 first)
    (hh : HArr s₀ s.mem hA₀) :
    WP isa hbuCoefs s fun s' => PCom s₀ sA i bound s' ∧
      SIn s₀ bound (optFold (huStep (uYs s₀) i first) (List.range (bound - first)) (hA₀, first)) s' ∧
      KeepC s s' := by
  obtain ⟨-, -, -, hω80, -, -⟩ := ufacts hp
  unfold hbuCoefs
  refine WP.seq (WP.mono (ltBit_ok .r7 .r1 .r4 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  obtain k₁ := keepC_r7 g₁ rd₁ wr₁ sp₁
  obtain hP₁ : PCom s₀ sA i bound s₁ := hP.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  obtain h1₁ : s₁.gpr .r1 = BitVec.ofNat 32 first := by rw [g₁ _ (by decide), h1]
  rw [h1, hP.r4, ltBit_z (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith) (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith),
    toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)] at z₁
  refine WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
  · -- No coefficient.
    obtain hge : bound ≤ first := by rw [z₁] at hge; simpa using hge
    refine WP.block_nil ⟨hP₁, ?_, k₁⟩
    rw [show bound - first = 0 by omega_arith]
    exact ⟨by omega_arith, h1₁, by rw [m₁]; exact hh⟩
  · -- The first coefficient, then the others.
    obtain hlt : first < bound := by rw [z₁] at hlt; simpa using hlt
    obtain hF1 : optFold (huStep (uYs s₀) i first) (List.range 1) (hA₀, first) =
        some (huSet i ((uYs s₀).getD first 0).toNat hA₀, first + 1) := by
      simp only [List.range_one, optFold, huStep, gt_iff_lt, Nat.lt_irrefl, false_and, ite_false]; rfl
    refine WP.seq (WP.mono (first_ok hp hA hi hlt hbω (hA' := hA₀) hP₁ h1₁ (by rw [m₁]; exact hh))
      fun s₂ ⟨hP₂, r1₂, hh₂, z₂, k₂⟩ => ?_)
    refine WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun hge₂ => ?_) (fun hlt₂ => ?_)
    · have hge₂ : bound ≤ first + 1 := by rw [z₂] at hge₂; simpa using hge₂
      refine WP.block_nil ⟨hP₂, ?_, k₁.trans k₂⟩
      rw [show bound - first = 1 by omega_arith, hF1]
      exact ⟨by omega_arith, r1₂, hh₂⟩
    · have hlt₂ : first + 1 < bound := by rw [z₂] at hlt₂; simpa using hlt₂
      exact WP.mono (nexts_ok hp hA hi hbω (Nat.le_refl 1) hF1 rfl hlt₂ hP₂ r1₂ hh₂) fun s₃ ⟨hP₃, hr₃, k₃⟩ =>
        ⟨hP₃, hr₃, (k₁.trans k₂).trans k₃⟩

end

/-! ## The polynomials -/

/-- The spec's state after `i` polynomials. -/
abbrev huS (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (uω s₀) (uYs s₀)) (List.range i) (Array.replicate (uk s₀) noHint, 0)

/-- Before polynomial `i`, in the loops that start from `sA`. -/
structure OInv (s₀ sA : State) (i : Nat) (s : State) : Prop where
  com : UCom s₀ sA s
  r5 : s.gpr .r5 = uY s₀ + BitVec.ofNat 32 (uω s₀ + i)
  r3 : s.gpr .r3 = uH s₀ + BitVec.ofNat 32 (1024 * i)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (1 * (uk s₀ - i))
  st : SRel s₀ (huS s₀ i) s

/-- A polynomial writes at most `r1`, `r4`, `r7` and `r12`. -/
def KeepP (s s' : State) : Prop :=
  (∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem KeepC.keepP {s s' : State} (h : KeepC s s') : KeepP s s' :=
  ⟨fun r a _ c d => h.1 r a c d, h.2⟩

theorem KeepP.trans {s s' s'' : State} (h : KeepP s s') (h' : KeepP s' s'') : KeepP s s'' :=
  ⟨fun r a b c d => (h'.1 r a b c d).trans (h.1 r a b c d), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem UCom.ofP {s₀ sA s s' : State} (h : UCom s₀ sA s) (hk : KeepP s s') (hm : Frame [uhR s₀] s.mem s'.mem) :
    UCom s₀ sA s' :=
  ⟨(hk.1 _ (by decide) (by decide) (by decide) (by decide)).trans h.r0,
    (hk.1 _ (by decide) (by decide) (by decide) (by decide)).trans h.r2,
    hk.2.1.trans h.rd, hk.2.2.1.trans h.wr, hk.2.2.2.trans h.sp, h.frame.trans hm⟩

theorem keepP_r4 {s s' : State} (h : ∀ r, r ≠ .r4 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : KeepP s s' := ⟨fun r _ b _ _ => h r b, hrd, hwr, hsp⟩

theorem keepP_r7 {s s' : State} (h : ∀ r, r ≠ .r7 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : KeepP s s' := ⟨fun r _ _ c _ => h r c, hrd, hwr, hsp⟩

theorem ldrb4_blk {s : State} {p : BitVec 32} (h5 : s.gpr .r5 = p)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (p + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.ldrb .r4 .r5 0]) s fun s' =>
      s'.gpr .r4 = (s.mem (State.addr (p + BitVec.ofNat 32 0))).setWidth 32 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r4 → s'.gpr r = s.gpr r := by
  run_block [h5, ib, true_and]
  intro r hr; rw [ite_neg' hr]

theorem ptail_blk {s : State} :
    WP isa (.block [.dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1024), .subs .r6 .r6 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = s.gpr .r5 + 1 ∧ s'.gpr .r3 = s.gpr .r3 + 1024 ∧ s'.gpr .r6 = s.gpr .r6 - 1 ∧
      s'.z = (s.gpr .r6 - 1 == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = s.gpr .r2 := by
  run_block []

section
variable {s₀ : State} (hp : UPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- Polynomial `i`: its checks and coefficients, unless a check failed. -/
theorem poly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ sA i s) :
    WP isa (.seq hbuPoly (.block [.dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1024), .subs .r6 .r6 (.imm 1)]))
      s fun s' => OInv s₀ sA (i + 1) s' ∧ s'.z = decide (i + 1 = uk s₀) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  have fY := hp.fitY
  obtain hsucc : huS s₀ (i + 1) = (huS s₀ i).bind fun st => huPoly (uω s₀) (uYs s₀) st i := optFold_range_succ _ _ _
  -- After the polynomial, whichever way it went.
  suffices h : WP isa hbuPoly s fun s' => UCom s₀ sA s' ∧ KeepP s s' ∧ SRel s₀ (huS s₀ (i + 1)) s' by
    refine WP.seq (WP.mono h fun s₁ ⟨hc₁, k₁, st₁⟩ => ?_)
    refine WP.mono ptail_blk fun s₂ ⟨r5₂, r3₂, r6₂, z₂, m₂, rd₂, wr₂, sp₂, r0₂, r1₂, r2₂⟩ =>
      ⟨⟨⟨by rw [r0₂, hc₁.r0], by rw [r2₂, hc₁.r2], by rw [rd₂, hc₁.rd], by rw [wr₂, hc₁.wr], by rw [sp₂, hc₁.sp],
        by rw [m₂]; exact hc₁.frame⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [r5₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r5, BitVec.add_assoc, ofNat_succ32,
        Nat.add_assoc]
    · rw [r3₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r3, BitVec.add_assoc,
        show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.ofNat_add_ofNat, Nat.mul_succ]
    · rw [r6₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r6]; exact count_sub (k := 1) hi
    · revert st₁
      cases huS s₀ (i + 1) with
      | none => exact fun h => by simp only [SRel] at h ⊢; rw [r1₂, h]
      | some st => obtain ⟨hA', idx⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨by rw [r1₂, h1], h2, by rw [m₂]; exact h3⟩
    · rw [z₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r6]
      exact count_z (k := 1) hi (by decide) (by omega_arith)
  unfold hbuPoly
  refine WP.seq (WP.mono (ltBit_ok .r7 .r2 .r1 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  obtain k₁ := keepP_r7 g₁ rd₁ wr₁ sp₁
  obtain hc₁ : UCom s₀ sA s₁ := hI.com.ofP k₁ (by rw [m₁]; exact Frame.refl _ _)
  have hst := hI.st
  cases hS : huS s₀ i with
  | none =>
    -- A check failed before: nothing.
    rw [hS] at hst
    have hst : s.gpr .r1 = 256 := hst
    rw [hI.com.r2, hst, ltBit_z (by omega_arith) (by decide), show (256 : BitVec 32).toNat = 256 from rfl] at z₁
    refine WP.ite (M := isa) false (by show some s₁.z = _; rw [z₁, decide_eq_false (by omega_arith)]) (fun h => by cases h)
      fun _ => WP.block_nil ⟨hc₁, k₁, ?_⟩
    rw [hsucc, hS]
    show s₁.gpr .r1 = 256
    rw [g₁ _ (by decide), hst]
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    obtain ⟨h1, hidx, hh⟩ := hst
    rw [hI.com.r2, h1, ltBit_z (by omega_arith) (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith), toNat_ofNat32 (by omega_arith)] at z₁
    obtain h1₁ : s₁.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₁ _ (by decide), h1]
    refine WP.ite (M := isa) true (by show some s₁.z = _; rw [z₁, decide_eq_true hidx]) (fun _ => ?_)
      (fun h => by cases h)
    -- The bound.
    obtain ebd : State.addr (uY s₀ + BitVec.ofNat 32 (uω s₀ + i) + BitVec.ofNat 32 0) =
        State.addr (uY s₀) + BitVec.ofNat 64 (uω s₀ + i) := by
      rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
    rw [WP.seq_iff, WP.block_append_iff]
    refine WP.mono (ldrb4_blk (p := uY s₀ + BitVec.ofNat 32 (uω s₀ + i)) (by rw [g₁ _ (by decide), hI.r5]) (by
        rw [ebd, hc₁.rd, hc₁.wr]
        exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
      fun s₂ ⟨r4₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
    rw [ebd, yByte hp hA.toYPre hc₁ (by omega_arith)] at r4₂
    obtain k₂ := keepP_r4 g₂ rd₂ wr₂ sp₂
    obtain hc₂ : UCom s₀ sA s₂ := hc₁.ofP k₂ (by rw [m₂]; exact Frame.refl _ _)
    obtain hbl := ((uYs s₀).getD (uω s₀ + i) 0).isLt
    refine WP.mono (ltBit_ok .r7 .r4 .r1 s₂) fun s₃ ⟨_, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ?_
    obtain k₃ := keepP_r7 g₃ rd₃ wr₃ sp₃
    obtain hc₃ : UCom s₀ sA s₃ := hc₂.ofP k₃ (by rw [m₃]; exact Frame.refl _ _)
    rw [r4₂, g₂ _ (by decide), h1₁, ltBit_z (by rw [byte_toNat32]; omega_arith) (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith),
      byte_toNat32, toNat_ofNat32 (by omega_arith)] at z₃
    have hpoly := hsucc
    rw [hS] at hpoly
    simp only [Option.bind_some, huPoly] at hpoly
    obtain r4₃ : s₃.gpr .r4 = BitVec.ofNat 32 ((uYs s₀).getD (uω s₀ + i) 0).toNat := by
      rw [g₃ _ (by decide), r4₂]; apply BitVec.eq_of_toNat_eq; rw [byte_toNat32, toNat_ofNat32 (by omega_arith)]
    obtain h1₃ : s₃.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₃ _ (by decide), g₂ _ (by decide), h1₁]
    refine WP.ite (M := isa) _ (show some s₃.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
    · have hge : idx ≤ ((uYs s₀).getD (uω s₀ + i) 0).toNat := by rw [z₃] at hge; simpa using hge
      refine WP.seq (WP.mono (ltBit_ok .r7 .r2 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_)
      obtain k₄ := keepP_r7 g₄ rd₄ wr₄ sp₄
      obtain hc₄ : UCom s₀ sA s₄ := hc₃.ofP k₄ (by rw [m₄]; exact Frame.refl _ _)
      rw [hc₃.r2, r4₃, ltBit_z (by omega_arith) (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith), toNat_ofNat32 (by omega_arith)] at z₄
      refine WP.ite (M := isa) _ (show some s₄.z = _ from rfl) (fun hle => ?_) (fun hgt => ?_)
      · -- The coefficients.
        obtain hle : ((uYs s₀).getD (uω s₀ + i) 0).toNat ≤ uω s₀ := by rw [z₄] at hle; simpa using hle
        obtain hP₄ : PCom s₀ sA i ((uYs s₀).getD (uω s₀ + i) 0).toNat s₄ :=
          ⟨hc₄, by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hI.r3],
            by rw [g₄ _ (by decide), r4₃]⟩
        refine WP.mono (coefs_ok hp hA hi (first := idx) (hA₀ := hA') hge hle hP₄
          (by rw [g₄ _ (by decide), h1₃]) (by rw [m₄, m₃, m₂, m₁]; exact hh)) fun s₅ ⟨hP₅, hin₅, k₅⟩ =>
            ⟨hP₅.com, (((k₁.trans k₂).trans k₃).trans k₄).trans k₅.keepP, ?_⟩
        rw [hpoly, ite_neg' (by omega_arith)]
        revert hin₅
        cases optFold (huStep (uYs s₀) i idx) (List.range (((uYs s₀).getD (uω s₀ + i) 0).toNat - idx)) (hA', idx) with
        | none => exact id
        | some st => obtain ⟨hA'', idx'⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨h2, by omega_arith, h3⟩
      · -- `bound > ω`: fail.
        obtain hgt : uω s₀ < ((uYs s₀).getD (uω s₀ + i) 0).toNat := by rw [z₄] at hgt; simpa using hgt
        refine WP.mono fail_ok fun s₅ ⟨r1₅, m₅, k₅⟩ => ⟨hc₄.of k₅ (by rw [m₅]; exact Frame.refl _ _),
          (((k₁.trans k₂).trans k₃).trans k₄).trans k₅.keepP, ?_⟩
        rw [hpoly, ite_pos' (.inr hgt)]; exact r1₅
    · -- `bound < index`: fail.
      obtain hlt : ((uYs s₀).getD (uω s₀ + i) 0).toNat < idx := by rw [z₃] at hlt; simpa using hlt
      refine WP.mono fail_ok fun s₄ ⟨r1₄, m₄, k₄⟩ => ⟨hc₃.of k₄ (by rw [m₄]; exact Frame.refl _ _),
        ((k₁.trans k₂).trans k₃).trans k₄.keepP, ?_⟩
      rw [hpoly, ite_pos' (.inl hlt)]; exact r1₄

omit hp hA in
theorem mainPro_blk {s : State} :
    WP isa (.block [.dp .add .r5 .r0 (.reg .r2)]) s fun s' => s'.gpr .r5 = s.gpr .r0 + s.gpr .r2 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r5 → s'.gpr r = s.gpr r := by
  run_block [true_and]
  intro r hr; rw [ite_neg' hr]

/-- The polynomials, from the state after zeroing `h`. -/
theorem main_ok (h0 : sA.gpr .r0 = uY s₀) (h1 : sA.gpr .r1 = 0) (h2 : sA.gpr .r2 = uW s₀)
    (h3 : sA.gpr .r3 = uH s₀) (h6 : sA.gpr .r6 = BitVec.ofNat 32 (uk s₀))
    (hz : ∀ t < 256 * uk s₀, coeffAt sA.mem (State.addr (uH s₀)) t = 0) :
    WP isa hbuMain sA fun s' => UCom s₀ sA s' ∧ SRel s₀ (huS s₀ (uk s₀)) s' := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuMain
  refine WP.seq (WP.mono mainPro_blk fun s₁ ⟨r5₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  refine wp_loop_ne (OInv s₀ sA) (N := uk s₀) (by omega_arith) (fun i hi s h => poly_ok hp hA hi h)
    (fun s hI => ⟨hI.com, hI.st⟩)
    ⟨⟨by rw [g₁ _ (by decide), h0], by rw [g₁ _ (by decide), h2], rd₁, wr₁, sp₁, by rw [m₁]; exact Frame.refl _ _⟩,
      by rw [r5₁, h0, h2, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [g₁ _ (by decide), h3]; simp, by rw [g₁ _ (by decide), h6, Nat.one_mul, Nat.sub_zero], ?_⟩
  show SRel s₀ (some (Array.replicate (uk s₀) noHint, 0)) s₁
  exact ⟨by rw [g₁ _ (by decide), h1]; rfl, Nat.zero_le _, by rw [m₁]; exact harr_zero hz⟩

end

section
variable {s₀ : State} (hp : UPre s₀) {sA : State} (hY : YPre s₀ sA)
include hp hY

/-! ## The bytes after the last index -/

omit hp hY in
theorem tload_blk {s : State} {y i : BitVec 32} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r12 .r0 (.reg .r1), .ldrb .r12 .r12 0, .cmp .r12 (.imm 0)]) s fun s' =>
      s'.z = ((s.mem (State.addr (y + i + BitVec.ofNat 32 0))).setWidth 32 - 0 == 0) ∧ s'.mem = s.mem ∧
      s'.gpr .r1 = i ∧ KeepC s s' := by
  run_block [KeepC, h0, h1, ib, true_and, and_true]
  intro r _ _ c; rw [ite_neg' c, ite_neg' c]

omit hp hY in
theorem inc_blk {s : State} :
    WP isa (.block [.dp .add .r1 .r1 (.imm 1)]) s fun s' => s'.gpr .r1 = s.gpr .r1 + 1 ∧ s'.mem = s.mem ∧
      KeepC s s' := by
  run_block [KeepC, true_and, and_true]
  intro r a _ _; rw [ite_neg' a]

omit hp hY in
theorem byte_z (b : Byte) : ((b.setWidth 32 : BitVec 32) - 0 == 0) = decide (b = 0) := by
  rw [sub_zero32]
  by_cases h : b = 0
  · subst h; rfl
  · rw [decide_eq_false h]
    apply beq_eq_false_iff_ne.mpr
    intro e; apply h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    rw [byte_toNat32] at this
    exact this

/-- The bytes from the index `idx` up to `ω`. -/
theorem trail_ok {idx : Nat} (hidx : idx ≤ uω s₀) {s : State} (hc : UCom s₀ sA s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) :
    WP isa hbuTrail s fun s' => UCom s₀ sA s' ∧ s'.mem = s.mem ∧
      (match optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () with
        | some _ => s'.gpr .r1 = BitVec.ofNat 32 (uω s₀)
        | none => s'.gpr .r1 = 256) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  have fY := hp.fitY
  unfold hbuTrail
  refine WP.seq (WP.mono (ltBit_ok .r7 .r1 .r2 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  obtain k₁ := keepC_r7 g₁ rd₁ wr₁ sp₁
  obtain hc₁ : UCom s₀ sA s₁ := hc.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  rw [h1, hc.r2, ltBit_z (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith) (by omega_arith), toNat_ofNat32 (by omega_arith)] at z₁
  refine WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
  · have hge : uω s₀ ≤ idx := by rw [z₁] at hge; simpa using hge
    refine WP.block_nil ⟨hc₁, m₁, ?_⟩
    rw [show uω s₀ - idx = 0 by omega_arith]
    show s₁.gpr .r1 = _
    rw [g₁ _ (by decide), h1, show idx = uω s₀ by omega_arith]
  · have hlt : idx < uω s₀ := by rw [z₁] at hlt; simpa using hlt
    refine WP.loop (M := isa) (fun m s' => ∃ u, m = uω s₀ - idx - u ∧ idx + u < uω s₀ ∧
        optFold (huTrail (uYs s₀)) (List.range' idx u) () = some () ∧ s'.gpr .r1 = BitVec.ofNat 32 (idx + u) ∧
        UCom s₀ sA s' ∧ s'.mem = s.mem)
      (fun m s' ⟨u, hm, hu, hF, h1', hc', hm'⟩ => ?_) _ s₁
      ⟨0, rfl, by omega_arith, rfl, by rw [g₁ _ (by decide), h1]; rfl, hc₁, m₁⟩
    obtain eb : State.addr (uY s₀ + BitVec.ofNat 32 (idx + u) + BitVec.ofNat 32 0) =
        State.addr (uY s₀) + BitVec.ofNat 64 (idx + u) := by
      rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
    refine WP.seq (WP.mono (tload_blk hc'.r0 h1' (by
        rw [eb, hc'.rd, hc'.wr]
        exact ⟨_, List.mem_append_left _ hY.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
      fun s₂ ⟨z₂, m₂, r1₂, k₂⟩ => ?_)
    rw [eb, yByte hp hY hc' (by omega_arith), byte_z] at z₂
    obtain hc₂ : UCom s₀ sA s₂ := hc'.of k₂ (by rw [m₂]; exact Frame.refl _ _)
    obtain hF1 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = huTrail (uYs s₀) () (idx + u) := by
      rw [optFold_range'_succ, hF]; rfl
    refine WP.seq (WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun heq => ?_) (fun hne => ?_))
    · -- A zero byte: next.
      obtain heq : (uYs s₀).getD (idx + u) 0 = 0 := by rw [z₂] at heq; simpa using heq
      obtain hF2 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = some () := by
        rw [hF1, huTrail, ite_neg' (by simpa using heq)]
      refine WP.mono inc_blk fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
      obtain r1₃' : s₃.gpr .r1 = BitVec.ofNat 32 (idx + (u + 1)) := by rw [r1₃, r1₂, ofNat_succ32, Nat.add_assoc]
      refine WP.mono (ltBit_ok .r7 .r1 .r2 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
      obtain k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
      obtain hc₄ : UCom s₀ sA s₄ := (hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).of k₄ (by rw [m₄]; exact Frame.refl _ _)
      rw [r1₃', (hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).r2,
        ltBit_z (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith) (by omega_arith), toNat_ofNat32 (by omega_arith)] at z₄
      obtain r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (idx + (u + 1)) := by rw [g₄ _ (by decide), r1₃']
      by_cases e : idx + (u + 1) < uω s₀
      · exact .inr ⟨by show some (!s₄.z) = some true; rw [z₄, decide_eq_false (by omega_arith)]; rfl, _, by omega_arith, u + 1,
          rfl, e, hF2, r1₄, hc₄, by rw [m₄, m₃, m₂, hm']⟩
      · refine .inl ⟨by show some (!s₄.z) = some false; rw [z₄, decide_eq_true (by omega_arith)]; rfl, hc₄,
          by rw [m₄, m₃, m₂, hm'], ?_⟩
        rw [show uω s₀ - idx = u + 1 by omega_arith, hF2]
        show s₄.gpr .r1 = _
        rw [r1₄, show idx + (u + 1) = uω s₀ by omega_arith]
    · -- A nonzero byte: fail.
      obtain hne : (uYs s₀).getD (idx + u) 0 ≠ 0 := by rw [z₂] at hne; simpa using hne
      obtain hn : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () = none :=
        optFold_range'_none _ _ (show u + 1 ≤ uω s₀ - idx by omega_arith) (by rw [hF1, huTrail, ite_pos' hne])
      refine WP.mono fail_ok fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
      refine WP.mono (ltBit_ok .r7 .r1 .r2 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
      obtain k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
      obtain hc₃ : UCom s₀ sA s₃ := hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)
      rw [r1₃, hc₃.r2, ltBit_z (by decide) (by omega_arith), show (256 : BitVec 32).toNat = 256 from rfl] at z₄
      refine .inl ⟨by show some (!s₄.z) = some false; rw [z₄, decide_eq_true (by omega_arith)]; rfl,
        hc₃.of k₄ (by rw [m₄]; exact Frame.refl _ _), by rw [m₄, m₃, m₂, hm'], ?_⟩
      rw [hn]
      show s₄.gpr .r1 = 256
      rw [g₄ _ (by decide), r1₃]

omit hY in
/-- After a failed check, the bytes after the last index are not checked. -/
theorem trail_fail {s : State} (hc : UCom s₀ sA s) (h1 : s.gpr .r1 = 256) :
    WP isa hbuTrail s fun s' => UCom s₀ sA s' ∧ s'.mem = s.mem ∧ s'.gpr .r1 = 256 := by
  obtain ⟨-, -, -, hω80, -, -⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  unfold hbuTrail
  refine WP.seq (WP.mono (ltBit_ok .r7 .r1 .r2 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  obtain k₁ := keepC_r7 g₁ rd₁ wr₁ sp₁
  rw [h1, hc.r2, ltBit_z (by decide) (by omega_arith), show (256 : BitVec 32).toNat = 256 from rfl] at z₁
  refine WP.ite (M := isa) true (by show some s₁.z = _; rw [z₁, decide_eq_true (by omega_arith)]) (fun _ => ?_)
    (fun h => by cases h)
  exact WP.block_nil ⟨hc.of k₁ (by rw [m₁]; exact Frame.refl _ _), m₁, by rw [g₁ _ (by decide), h1]⟩

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

end

end


/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, correct

The whole function: the load of `hlen`, the frame, and in it zeroing `h`, the
loops (`HintUnpackLoops.lean`), the return value and the reloads of the saved
registers; the result is `HintBitUnpack` (Algorithm 21) through its fold form
(`hintBitUnpack_eq`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-- The state the body runs from. -/
abbrev P1 (s₀ : State) : State := pushed [.r4, .r5, .r6, .r7] (s₀.setReg .r12 (uHL s₀))

/-- The state after zeroing `h`. -/
def UZ (s₀ a : State) : Prop :=
  a.gpr .r0 = uY s₀ ∧ a.gpr .r1 = 0 ∧ a.gpr .r2 = uW s₀ ∧ a.gpr .r3 = uH s₀ ∧
    a.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧ (∀ t < 256 * uk s₀, coeffAt a.mem (State.addr (uH s₀)) t = 0) ∧
    Frame [uhR s₀] (P1 s₀).mem a.mem ∧ a.rd = (P1 s₀).rd ∧ a.wr = (P1 s₀).wr ∧ a.sp = (P1 s₀).sp

/-- The state after the polynomials, in the run from `sa`. -/
def UM (s₀ a : State) : Prop :=
  ∃ sa, UZ s₀ sa ∧ UCom s₀ sa a ∧ SRel s₀ (huS s₀ (uk s₀)) a

/-- The result. -/
def UPost (s₀ : State) (m : Mem) (r : BitVec 32) : Prop :=
  match hintBitUnpack (uω s₀) (uk s₀) (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)) with
  | some hint => r = 1 ∧ HintIs m (State.addr (uH s₀)) (uk s₀) hint
  | none => r = 0

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem hsp16 : 4 * [Reg.r4, Reg.r5, Reg.r6, Reg.r7].length ≤ (s₀.setReg .r12 (uHL s₀)).sp.toNat := hp.sp

theorem hfr : frameR (s₀.setReg .r12 (uHL s₀)) [.r4, .r5, .r6, .r7] = ⟨State.addr s₀.sp - BitVec.ofNat 64 16, 16⟩ :=
  frameR_eq [.r4, .r5, .r6, .r7] (s := s₀.setReg .r12 (uHL s₀)) hp.sp

theorem zeroP_ok : WP isa hbuZero (P1 s₀) (UZ s₀) :=
  zero_ok hp rfl rfl rfl rfl rfl (by simp [RegUpd.wr_setReg, hp.wr])

/-- The body changes memory only in the frame and `h`. -/
theorem uz_frame {a : State} (hz : UZ s₀ a) :
    Frame [⟨State.addr s₀.sp - BitVec.ofNat 64 16, 16⟩, uhR s₀] s₀.mem a.mem := by
  obtain hpf := pushed_frame [.r4, .r5, .r6, .r7] (hsp16 hp)
  rw [hfr hp] at hpf
  exact (hpf.mono (by simp)).trans (hz.2.2.2.2.2.2.1.mono (by simp))

/-- The bytes of `y`, after zeroing `h`, and after the loops. -/
theorem uz_y {a : State} (hz : UZ s₀ a) {m : Mem} (hm : Frame [uhR s₀] a.mem m) :
    ∀ t < uLen s₀, m (State.addr (uY s₀) + BitVec.ofNat 64 t) = s₀.mem (State.addr (uY s₀) + BitVec.ofNat 64 t) := by
  intro t ht
  have fY := hp.fitY
  obtain hc : (uyR s₀).Contains (State.addr (uY s₀) + BitVec.ofNat 64 t) 1 := Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht, fY])
  rw [hm _ fun r hr hc' => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.d_yh _ hc hc',
    uz_frame hp hz _ fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.b_y _ hc' hc
      · exact hp.d_yh _ hc hc']

theorem mainPre_of {a : State} (hz : UZ s₀ a) {rd wr : List Region} (hr : uyR s₀ ∈ rd) (hw : uhR s₀ ∈ wr) :
    MainPre s₀ (a.withRegions rd wr) := ⟨⟨hr, uz_y hp hz (Frame.refl _ _)⟩, hw⟩

theorem uz_rd {a : State} (hz : UZ s₀ a) : uyR s₀ ∈ a.rd := by
  rw [hz.2.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp.rd]

theorem uz_wr {a : State} (hz : UZ s₀ a) : uhR s₀ ∈ a.wr := by
  rw [hz.2.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp.wr]

/-- The polynomials, from the state after zeroing `h`. -/
theorem mainP_ok {a : State} (hz : UZ s₀ a) : WP isa hbuMain a (UM s₀) := by
  obtain ⟨a0, a1, a2, a3, a6, az, -⟩ := id hz
  have := mainPre_of hp hz (rd := a.rd) (wr := a.wr) (uz_rd hp hz) (uz_wr hp hz)
  rw [State.withRegions_self] at this
  exact WP.mono (main_ok hp this a0 a1 a2 a3 a6 az) fun s' ⟨hc, hs⟩ => ⟨a, hz, hc, hs⟩

/-- The start of the loop over the trailing bytes, narrowed to `y`. -/
theorem um_trail {a : State} (hm : UM s₀ a) {rd wr : List Region} (hr : uyR s₀ ∈ rd) :
    YPre s₀ (a.withRegions rd wr) ∧ UCom s₀ (a.withRegions rd wr) (a.withRegions rd wr) := by
  obtain ⟨sa, hz, hc, -⟩ := hm
  exact ⟨⟨hr, uz_y hp hz hc.frame⟩, hc.r0, hc.r2, rfl, rfl, rfl, Frame.refl _ _⟩

end

theorem ret_blk {s : State} (i5 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4)
    (i6 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (i7 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 12)) 4) :
    WP isa (.block hbuRet) s fun s' => s'.gpr .r0 = 1 - ((s.gpr .r2 - s.gpr .r1) >>> 31) ∧
      s'.gpr .r5 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32 ∧
      s'.gpr .r6 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 ∧
      s'.gpr .r7 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 12)) 32 ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  run_block [hbuRet, i5, i6, i7]
  exact ⟨rfl, trivial⟩

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {s₀ : State} {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) :
    HintIs m (State.addr (uH s₀)) (uk s₀) hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

theorem ret_val (ω x : Nat) (hω : ω ≤ 80) (hx : x < 2 ^ 31) :
    (1 : BitVec 32) - ((BitVec.ofNat 32 ω - BitVec.ofNat 32 x) >>> 31) = if ω < x then 0 else 1 := by
  rw [ltBit_val (by rw [toNat_ofNat32 (by omega_arith)]; omega_arith) (by rw [toNat_ofNat32 (by omega_using [hx])]; omega_using [hx]),
    toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_using [hx])]
  split <;> rfl

theorem fail_val {s₀ : State} (hp : UPre s₀) : (1 : BitVec 32) - ((uW s₀ - 256) >>> 31) = 0 := by
  obtain ⟨-, -, -, hω80, -, -⟩ := ufacts hp
  obtain e := ret_val (uω s₀) 256 hω80 (by decide)
  rw [ite_pos' (by omega_arith), BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  exact e

/-- The body of the frame: the result, the reloads of `r5`–`r7`, and the word
the pop reloads into `r4`. -/
theorem body_ok {s₀ : State} (hp : UPre s₀) :
    WP isa hintBitUnpackBody (P1 s₀) fun s₂ => s₂.sp = (P1 s₀).sp ∧ s₂.gpr .r5 = s₀.gpr .r5 ∧
      s₂.gpr .r6 = s₀.gpr .r6 ∧ s₂.gpr .r7 = s₀.gpr .r7 ∧ s₂.mem.readW (State.addr s₂.sp) 32 = s₀.gpr .r4 ∧
      UPost s₀ s₂.mem (s₂.gpr .r0) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  obtain hsp := hsp16 hp
  unfold hintBitUnpackBody
  refine WP.seq (WP.mono (zeroP_ok hp) fun sa hz => ?_)
  refine WP.seq (WP.mono (mainP_ok hp hz) fun sb hm => ?_)
  obtain ⟨sa', hz', hcb, hst⟩ := id hm
  obtain hA := mainPre_of hp hz' (rd := sa'.rd) (wr := sa'.wr) (uz_rd hp hz') (uz_wr hp hz')
  rw [State.withRegions_self] at hA
  -- What the trailing bytes and the return leave, whichever way the checks went.
  suffices h : WP isa hbuTrail sb fun sc => UCom s₀ sa' sc ∧ UPost s₀ sc.mem (1 - ((sc.gpr .r2 - sc.gpr .r1) >>> 31)) by
    refine WP.seq (WP.mono h fun sc ⟨hcc, hpc⟩ => ?_)
    obtain hfc : Frame [uhR s₀] (P1 s₀).mem sc.mem := hz'.2.2.2.2.2.2.1.trans hcc.frame
    obtain hdh : ∀ r ∈ [uhR s₀], (frameR (s₀.setReg .r12 (uHL s₀)) [.r4, .r5, .r6, .r7]).Disjoint r := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hfr hp]; exact hp.b_h
    obtain hsc : sc.sp = (P1 s₀).sp := by rw [hcc.sp, hz'.2.2.2.2.2.2.2.2.2]
    obtain hin : ∀ i < 4, InRegions (sc.rd ++ sc.wr) (State.addr (sc.sp + BitVec.ofNat 32 (4 * i))) 4 := fun i hi => by
      rw [hcc.wr, hz'.2.2.2.2.2.2.2.2.1, pushed_wr, hsc]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains [.r4, .r5, .r6, .r7] hsp hi⟩
    refine WP.mono (ret_blk (hin 1 (by decide)) (hin 2 (by decide)) (hin 3 (by decide)))
      fun sd ⟨r0d, r5d, r6d, r7d, md, spd⟩ => ⟨by rw [spd, hsc], ?_, ?_, ?_, ?_, by rw [md, r0d]; exact hpc⟩
    · rw [r5d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 1) (by decide)]; rfl
    · rw [r6d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 2) (by decide)]; rfl
    · rw [r7d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 3) (by decide)]; rfl
    · rw [md, spd, hsc, show State.addr (P1 s₀).sp = State.addr ((P1 s₀).sp + BitVec.ofNat 32 (4 * 0)) by simp,
        frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 0) (by decide)]; rfl
  unfold UPost
  rw [hintBitUnpack_eq]
  cases hS : huS s₀ (uk s₀) with
  | none =>
    rw [hS] at hst
    have hst : sb.gpr .r1 = 256 := hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = none from hS]
    refine WP.mono (trail_fail hp hcb hst) fun sc ⟨hcc, _, r1c⟩ => ⟨hcc, ?_⟩
    show _ = 0
    rw [hcc.r2, r1c]
    exact fail_val hp
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    obtain ⟨h1, hidx, hh⟩ := hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = some (hA', idx) from hS]
    refine WP.mono (trail_ok hp hA.toYPre hidx hcb h1) fun sc ⟨hcc, mc, hr⟩ => ⟨hcc, ?_⟩
    dsimp only
    revert hr
    cases optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () with
    | none =>
      intro r1c
      show _ = 0
      rw [hcc.r2, r1c]
      exact fail_val hp
    | some _ =>
      intro r1c
      refine ⟨?_, by rw [mc]; exact harr_hintIs hh⟩
      rw [hcc.r2, r1c, ← eω, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self]
      rfl

/-- The whole function: the result, and the registers it saves and restores
(the others it never writes). -/
theorem correct {s₀ : State} (hp : UPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.hintBitUnpack s₀ fun s' => s'.gpr .r4 = s₀.gpr .r4 ∧ s'.gpr .r5 = s₀.gpr .r5 ∧
      s'.gpr .r6 = s₀.gpr .r6 ∧ s'.gpr .r7 = s₀.gpr .r7 ∧ s'.gpr .lr = s₀.gpr .lr ∧ s'.sp = s₀.sp ∧
      UPost s₀ s'.mem (s'.gpr .r0) := by
  unfold Impl.MlDsa.Arm.Pack.hintBitUnpack
  refine WP.seq (WP.mono (entry_ok (s := s₀) (by
    rw [hp.rd]; exact ⟨uargR s₀, by simp, Region.contains_self _ _⟩)) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.frame (rs := [.r4, .r5, .r6, .r7]) (r := .r4) rfl (hsp16 hp) (by decide)
    (WP.mono (WP.gpr (body_ok hp) (r := .lr) (noWrite (by decide +kernel))) fun s₂ ⟨⟨hsp, h5, h6, h7, h4, hr⟩, hlr⟩ => ?_)
  refine ⟨?_, by rw [popped_gpr (by decide), h5], by rw [popped_gpr (by decide), h6], by rw [popped_gpr (by decide), h7],
    by rw [popped_gpr (by decide), hlr]; rfl, ?_, by rw [popped_mem, popped_gpr (by decide)]; exact hr⟩
  · simp only [popped, State.setReg, ite_true]; exact h4
  · simp only [popped_sp, hsp, P1, pushed_sp]
    exact BitVec.sub_add_cancel _ _

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack
