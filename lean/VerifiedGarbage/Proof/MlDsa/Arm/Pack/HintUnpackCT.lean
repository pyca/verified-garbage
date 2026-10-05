import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPackCT

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpack`. -/
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
abbrev uω : Nat := (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀).toNat
abbrev uLen : Nat := (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uL s₀).toNat
abbrev uk : Nat := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀ - VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀
abbrev uyR : Region := ⟨State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀), VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀⟩
abbrev uhR : Region := ⟨State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀), (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀).toNat * 4⟩
abbrev uargR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The bytes of `y`, as the spec reads them. -/
abbrev uYs : Array Byte := (bytesAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀)).toArray

end

/-- The precondition, as `sig_pre` states it. -/
structure UPre (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  spA : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uargR s]
  wr : s.wr = [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s]
  d_yh : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s)
  d_ha : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uargR s)
  b_y : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s)
  b_h : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s)
  b_a : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uargR s)
  fitY : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s).toNat + VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s ≤ 2 ^ 32
  fitH : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s).toNat + (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s).toNat * 4 ≤ 2 ^ 32
  par : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s) ∈ hintParams
  ωle : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s
  hlen : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s).toNat = 256 * VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s

theorem ufacts {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) : 4 ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀ ≤ 8 ∧ 55 ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ ≤ 80 ∧
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀ = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀ ≤ 88 := by
  have := VG.Proof.MlDsa.Arm.Pack.Hint.mem_hintParams hp.par
  have := hp.ωle
  have e : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀ = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀ - VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ := rfl
  omega

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
theorem zero_ok {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {s : State} (h0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) (h1 : s.gpr .r1 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uL s₀)
    (h2 : s.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀) (h3 : s.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀) (h12 : s.gpr .r12 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀) (hwr : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀ ∈ s.wr) :
    WP isa hbuZero s fun s' => s'.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀ ∧
      s'.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) ∧
      (∀ t < 256 * VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀, coeffAt s'.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) t = 0) ∧
      Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨hk4, hk8, -, -, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  have hHL := (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀).isLt
  unfold hbuZero
  refine WP.seq (WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.zeroPro_ok fun s₁ ⟨r6₁, r4₁, r12₁, r5₁, r0₁, r2₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine WP.seq (wp_loop_ne (N := 256 * VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (fun t s' => s'.gpr .r5 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ + BitVec.ofNat 32 (4 * t) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (1 * (256 * VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀ - t)) ∧ s'.gpr .r12 = 0 ∧ s'.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ ∧
      s'.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀ ∧ s'.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) ∧
      Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] s.mem s'.mem ∧ (∀ u < t, coeffAt s'.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) u = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by omega)
    (fun t ht s' ⟨i5, i4, i12, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    (fun s₂ ⟨_, _, _, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    ⟨by rw [r5₁, h3]; simp, by rw [r4₁, h12, Nat.one_mul, Nat.sub_zero, ← hl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      r12₁, by rw [r0₁, h0], by rw [r2₁, h2], by rw [r3₁, h3], ?_, by rw [m₁]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), rd₁, wr₁, sp₁⟩)
  · have ea : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ + BitVec.ofNat 32 (4 * t) + BitVec.ofNat 32 0) = coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) t :=
      by rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    have hin : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀).Contains (coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) t) 4 := Offset.contains_base _ (by omega) (by omega)
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.zeroStep_ok i5 i4 (by rw [ea, hwr']; exact ⟨_, hwr, hin⟩))
      fun s'' ⟨r5', r4', z', m', r0', r2', r3', r6', r12', rd', wr', sp'⟩ =>
        ⟨⟨by rw [r5', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, Nat.mul_succ],
          by rw [r4']; exact count_sub (k := 1) ht, by rw [r12', i12],
          by rw [r0', i0], by rw [r2', i2], by rw [r3', i3], by rw [r6', i6], ?_, fun u hu => ?_,
          by rw [rd', hrd], by rw [wr', hwr'], by rw [sp', hsp]⟩,
          by rw [z']; exact count_z (k := 1) ht (by decide) (by omega)⟩
    · rw [m', ea]
      exact hf.writeW (List.mem_singleton_self _) _ hin
    · rw [m', ea, i12]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
      · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
          ← coeffAt_eq, hz u (by omega)]
  · rw [r6₁, h1, h2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hp.ωle, toNat_ofNat32 (by omega)]

  · refine WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.zeroEnd_ok
      fun s₃ ⟨r1₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ⟨by rw [g₃ _ (by decide), i0], r1₃, by rw [g₃ _ (by decide), i2],
        by rw [g₃ _ (by decide), i3], by rw [g₃ _ (by decide), i6], by rw [m₃]; exact hz,
        by rw [m₃]; exact hf, by rw [rd₃, hrd], by rw [wr₃, hwr'], by rw [sp₃, hsp]⟩

/-! ## The hint in memory -/

/-- The words of `h` are the hint `hA` of the spec. -/
def HArr (s₀ : State) (m : Mem) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀ ∧ ∀ i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀, ∀ j < 256,
    coeffAt m (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `r1`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .r1 = BitVec.ofNat 32 idx ∧ idx ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s.mem hA
  | none, s => s.gpr .r1 = 256

/-- What the loops that read `y` need of the state they start from:
permission to read it, and its bytes of the entry state. -/
structure YPre (s₀ sA : State) : Prop where
  rd : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₀ ∈ sA.rd
  y : ∀ t < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀, sA.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 t) = s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 t)

/-- ... and those that write `h`: permission to write it. -/
structure MainPre (s₀ sA : State) : Prop extends VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.YPre s₀ sA where
  wr : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀ ∈ sA.wr

/-- What stays the same in the loops that start from `sA`. -/
structure UCom (s₀ sA s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀
  r2 : s.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] sA.mem s.mem

/-- A step of the loops over the coefficients: it writes at most `r1`, `r7`
and `r12`. -/
def KeepC (s s' : State) : Prop :=
  (∀ r, r ≠ .r1 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem KeepC.refl (s : State) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl⟩

theorem KeepC.trans {s s' s'' : State} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s') (h' : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s' s'') : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s'' :=
  ⟨fun r a b c => (h'.1 r a b c).trans (h.1 r a b c), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem UCom.of {s₀ sA s s' : State} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s) (hk : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s') (hm : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] s.mem s'.mem) :
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s' :=
  ⟨(hk.1 _ (by decide) (by decide) (by decide)).trans h.r0, (hk.1 _ (by decide) (by decide) (by decide)).trans h.r2,
    hk.2.1.trans h.rd, hk.2.2.1.trans h.wr, hk.2.2.2.trans h.sp, h.frame.trans hm⟩

/-- Where the loops of polynomial `i` are. -/
structure PCom (s₀ sA : State) (i bound : Nat) (s : State) : Prop where
  com : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s
  r3 : s.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ + BitVec.ofNat 32 (1024 * i)
  r4 : s.gpr .r4 = BitVec.ofNat 32 bound

theorem PCom.of {s₀ sA s s' : State} {i bound : Nat} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s) (hk : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s')
    (hm : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] s.mem s'.mem) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s' :=
  ⟨h.com.of hk hm, (hk.1 _ (by decide) (by decide) (by decide)).trans h.r3,
    (hk.1 _ (by decide) (by decide) (by decide)).trans h.r4⟩

theorem harr_set {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {m : Mem} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ m hA) {i b : Nat}
    (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (hb : b < 256) :
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ (m.writeW (coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) (256 * i + b)) (1 : BitVec 32)) (huSet i b hA) := by
  obtain ⟨hk4, hk8, -, -, -, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

theorem harr_zero {s₀ : State} {m : Mem} (hz : ∀ t < 256 * VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀, coeffAt m (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) t = 0) :
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ m (Array.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) noHint) := by
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {sA s : State} (hA : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.YPre s₀ sA) (hc : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s) {t : Nat}
    (ht : t < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀) : s.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 t) = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD t 0 := by
  have fY := hp.fitY
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht,
    ← hA.y t ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.d_yh _ (Offset.contains_base _ (by omega) (by omega)) hc'

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
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  run_block [hbuSet, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC, h0, h1, h3, ib, hb, ow, true_and, and_true]
  intro r a b c; rw [ite_neg' a, ite_neg' b, ite_neg' c, ite_neg' c, ite_neg' c]

theorem fail_ok {s : State} :
    WP isa hbuFail s fun s' => s'.gpr .r1 = 256 ∧ s'.mem = s.mem ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  unfold hbuFail
  run_block [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC, true_and, and_true]
  intro r a _ _; rw [ite_neg' a]

theorem keepC_r7 {s s' : State} (h : ∀ r, r ≠ .r7 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := ⟨fun r _ b _ => h r b, hrd, hwr, hsp⟩

/-- The byte `strb`'s index of `h`, as a word offset. -/
theorem shl2_byte (b : Byte) : (b.setWidth 32 <<< 2 : BitVec 32) = BitVec.ofNat 32 (4 * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, toNat_ofNat32 (by have := b.isLt; omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega), Nat.shiftLeft_eq]
  have := b.isLt
  omega

theorem nextLoad_blk {s : State} {y i : BitVec 32} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (ic : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1)
    (ip : InRegions (s.rd ++ s.wr) (State.addr (y + i - 1 + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r12 .r0 (.reg .r1), .ldrb .r7 .r12 0, .dp .sub .r12 .r12 (.imm 1), .ldrb .r12 .r12 0])
      s fun s' => s'.gpr .r7 = (s.mem (State.addr (y + i + BitVec.ofNat 32 0))).setWidth 32 ∧
        s'.gpr .r12 = (s.mem (State.addr (y + i - 1 + BitVec.ofNat 32 0))).setWidth 32 ∧ s'.mem = s.mem ∧
        s'.gpr .r1 = i ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  run_block [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC, h0, h1, ic, ip, true_and, and_true]
  intro r _ b c; rw [ite_neg' c, ite_neg' c, ite_neg' b, ite_neg' c]

theorem ptr_pred (p : BitVec 32) {x : Nat} (h : 1 ≤ x) :
    p + BitVec.ofNat 32 x - 1 = p + BitVec.ofNat 32 (x - 1) := by
  rw [show x = (x - 1) + 1 by omega, ← ofNat_succ32, ← BitVec.add_assoc, BitVec.add_sub_cancel,
    Nat.add_sub_cancel]

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {sA : State} (hA : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.MainPre s₀ sA)
include hp hA

/-- Setting coefficient `y[index]` of polynomial `i`. -/
theorem set_ok {i bound idx : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (hidx : idx < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀) {hA' : Array (Vector Bool n)}
    {s : State} (hP : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) (hh : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s.mem hA') :
    WP isa (.block hbuSet) s fun s' =>
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 (idx + 1) ∧
        VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s'.mem (huSet i ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).toNat hA') ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  obtain ⟨hk4, hk8, -, -, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have fY := hp.fitY
  have fH := hp.fitH
  have hl := hp.hlen
  have hbl := ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).isLt
  have ey : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0) = State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 idx := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hb : s.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0)) = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0 := by
    rw [ey]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yByte hp hA.toYPre hP.com hidx
  have eh : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ + BitVec.ofNat 32 (1024 * i) + (((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).setWidth 32 <<< 2) +
      BitVec.ofNat 32 0) = coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) (256 * i + ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).toNat) := by
    rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.shl2_byte, ptr_add, addr_ptr _ _ _ (by omega)]
    congr 2; omega
  have hin : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀).Contains (coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) (256 * i + ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).toNat)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.set_blk hP.com.r0 h1 hP.r3 (by
      rw [ey, hP.com.rd, hP.com.wr]
      exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩) hb
      (by rw [eh, hP.com.wr]; exact ⟨_, hA.wr, hin⟩))
    fun s' ⟨r1', m', k'⟩ => ⟨hP.of k' ?_, by rw [r1', ofNat_succ32], ?_, k'⟩
  · rw [m', eh]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hin
  · rw [m', eh]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.harr_set hp hh hi hbl

/-- The first coefficient of polynomial `i`, from the index `first`. -/
theorem first_ok {i bound first : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (hfb : first < bound) (hbω : bound ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀)
    {hA' : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 first)
    (hh : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s.mem hA') :
    WP isa (.block (hbuSet ++ hbuMore)) s fun s' =>
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 (first + 1) ∧
        VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s'.mem (huSet i ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD first 0).toNat hA') ∧ s'.z = decide (bound ≤ first + 1) ∧
        VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  obtain ⟨-, -, -, hω80, hsum, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.set_ok hp hA hi (by omega) hP h1 hh) fun s₁ ⟨hP₁, r1₁, hh₁, k₁⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r4 s₁) fun s₂ ⟨_, z₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
  have k₂ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₂ rd₂ wr₂ sp₂
  refine ⟨hP₁.of k₂ (by rw [m₂]; exact Frame.refl _ _), by rw [g₂ _ (by decide), r1₁], by rw [m₂]; exact hh₁, ?_,
    k₁.trans k₂⟩
  rw [z₂, r1₁, hP₁.r4, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
    toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

/-- A coefficient after the first: checked against the previous one. -/
theorem next_ok {i bound first idx : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (hfi : first < idx) (hib : idx < bound)
    (hbω : bound ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) {hA' : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) (hh : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s.mem hA') :
    WP isa hbuNext s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s' ∧
      (match huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first (hA', idx) 0 with
        | some (hA'', idx') => s'.gpr .r1 = BitVec.ofNat 32 idx' ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s'.mem hA'' ∧
          s'.z = decide (bound ≤ idx')
        | none => s'.gpr .r1 = 256 ∧ s'.z = true) ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  obtain ⟨-, -, -, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have fY := hp.fitY
  have ec : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 idx + BitVec.ofNat 32 0) = State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 idx := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have ep : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 idx - 1 + BitVec.ofNat 32 0) =
      State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 (idx - 1) := by
    rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ptr_pred _ (by omega), addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hrw : s.rd ++ s.wr = sA.rd ++ sA.wr := by rw [hP.com.rd, hP.com.wr]
  unfold hbuNext
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.nextLoad_blk hP.com.r0 h1 (by
      rw [ec, hrw]; exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [ep, hrw]; exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩))
    fun s₁ ⟨r7₁, r12₁, m₁, r1₁, k₁⟩ => ?_
  rw [ec, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yByte hp hA.toYPre hP.com (by omega)] at r7₁
  rw [ep, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yByte hp hA.toYPre hP.com (by omega)] at r12₁
  have hP₁ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s₁ := hP.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r12 .r7 s₁) fun s₂ ⟨_, z₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
  have k₂ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₂ rd₂ wr₂ sp₂
  have hP₂ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s₂ := hP₁.of k₂ (by rw [m₂]; exact Frame.refl _ _)
  have hcb := ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).isLt
  have hpb := ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (idx - 1) 0).isLt
  rw [r7₁, r12₁, ltBit_z (by rw [byte_toNat32]; omega) (by rw [byte_toNat32]; omega), byte_toNat32,
    byte_toNat32] at z₂
  have h1₂ : s₂.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₂ _ (by decide), r1₁]
  refine WP.seq (WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_))
  · -- Not increasing: fail.
    have hge : ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).toNat ≤ ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (idx - 1) 0).toNat := by
      rw [z₂] at hge; simpa using hge
    have hs : huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first (hA', idx) 0 = none := by
      simp only [huStep]; rw [ite_pos' ⟨hfi, hge⟩]
    rw [hs]
    refine WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.fail_ok fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
    have k₄ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₄ rd₄ wr₄ sp₄
    refine ⟨hP₂.of (k₃.trans k₄) (by rw [m₄, m₃]; exact Frame.refl _ _), ⟨by rw [g₄ _ (by decide), r1₃], ?_⟩,
      ((k₁.trans k₂).trans k₃).trans k₄⟩
    rw [z₄, r1₃, (hP₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).r4,
      ltBit_z (by decide) (by rw [toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega),
      show (256 : BitVec 32).toNat = 256 from rfl]
    exact decide_eq_true (by omega)
  · -- `y[index - 1] < y[index]`: set it.
    have hlt : ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (idx - 1) 0).toNat < ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).toNat := by
      rw [z₂] at hlt; simpa using hlt
    have hs : huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first (hA', idx) 0 = some (huSet i ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD idx 0).toNat hA', idx + 1) := by
      simp only [huStep]; rw [ite_neg' (by omega)]
    rw [hs]
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.set_ok hp hA hi (hA' := hA') (by omega) hP₂ h1₂ (by rw [m₂, m₁]; exact hh))
      fun s₃ ⟨hP₃, r1₃, hh₃, k₃⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
    have k₄ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₄ rd₄ wr₄ sp₄
    refine ⟨hP₃.of k₄ (by rw [m₄]; exact Frame.refl _ _), ⟨by rw [g₄ _ (by decide), r1₃], by rw [m₄]; exact hh₃, ?_⟩,
      ((k₁.trans k₂).trans k₃).trans k₄⟩
    rw [z₄, r1₃, hP₃.r4, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
      toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackLoops`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, the loops

The loops of `vg_mldsa_hint_bit_unpack`, as on x86-64: the coefficients of a
polynomial (`coefs_ok`), the polynomials (`main_ok`), each an iteration of the
fold `huPoly` of the spec, and the bytes after the last index (`trail_ok`),
from any state that permits reading `y` and writing `h` (`MainPre`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-- The state after the coefficients of a polynomial, up to the bound. -/
def SIn (s₀ : State) (bound : Nat) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => idx = bound ∧ s.gpr .r1 = BitVec.ofNat 32 idx ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s.mem hA
  | none, s => s.gpr .r1 = 256

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {sA : State} (hA : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.MainPre s₀ sA)
include hp hA

/-- The coefficients after the first. -/
theorem nexts_ok {i bound first : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (hbω : bound ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) {hA₀ : Array (Vector Bool n)}
    {t : Nat} (ht1 : 1 ≤ t) {hA' : Array (Vector Bool n)} {idx' : Nat}
    (hF : optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range t) (hA₀, first) = some (hA', idx'))
    (hidx : idx' = first + t) (hlt : idx' < bound) {s : State} (hP : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx') (hh : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s.mem hA') :
    WP isa (.loop hbuNext .ne) s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s' ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SIn s₀ bound (optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range (bound - first)) (hA₀, first)) s' ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  refine WP.loop (M := isa) (fun m s' => ∃ t hA' idx', m = bound - idx' ∧ 1 ≤ t ∧
      optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range t) (hA₀, first) = some (hA', idx') ∧ idx' = first + t ∧
      idx' < bound ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 idx' ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s'.mem hA' ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s')
    (fun m s' ⟨t, hA', idx', hm, ht1, hF, hidx, hlt, hP', h1', hh', hk'⟩ => ?_) _ s
    ⟨t, hA', idx', rfl, ht1, hF, hidx, hlt, hP, h1, hh, KeepC.refl _⟩
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.next_ok hp hA hi (first := first) (by omega) hlt hbω hP' h1' hh') fun s'' ⟨hP'', hm'', hk''⟩ => ?_
  have hF1 : optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range (t + 1)) (hA₀, first) =
      huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first (hA', idx') t := by rw [optFold_range_succ, hF]; rfl
  cases hs : huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first (hA', idx') 0 with
  | none =>
    rw [hs] at hm''
    obtain ⟨r1'', z''⟩ := hm''
    refine .inl ⟨by show some (!s''.z) = some false; rw [z'']; rfl, hP'', ?_, hk'.trans hk''⟩
    have : optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range (t + 1)) (hA₀, first) = none := by
      rw [hF1]; exact hs
    rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega) this]
    exact r1''
  | some st =>
    rw [hs] at hm''
    obtain ⟨hA'', idx''⟩ := st
    obtain ⟨r1'', hh'', z''⟩ := hm''
    have hi'' : idx'' = idx' + 1 := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huStep_idx hs
    have hF2 : optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range (t + 1)) (hA₀, first) = some (hA'', idx'') := by
      rw [hF1]; exact hs
    by_cases e : idx'' < bound
    · refine .inr ⟨by show some (!s''.z) = some true; rw [z'', decide_eq_false (by omega)]; rfl, bound - idx'',
        by omega, t + 1, hA'', idx'', rfl, by omega, hF2, by omega, e, hP'', r1'', hh'', hk'.trans hk''⟩
    · refine .inl ⟨by show some (!s''.z) = some false; rw [z'', decide_eq_true (by omega)]; rfl, hP'', ?_,
        hk'.trans hk''⟩
      rw [show bound - first = t + 1 by omega, hF2]
      exact ⟨by omega, r1'', hh''⟩

/-- The coefficients of polynomial `i`, from the index `first`, up to the bound. -/
theorem coefs_ok {i bound first : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀)
    {hA₀ : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 first)
    (hh : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ s.mem hA₀) :
    WP isa hbuCoefs s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s' ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SIn s₀ bound (optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range (bound - first)) (hA₀, first)) s' ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  obtain ⟨-, -, -, hω80, -, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  unfold hbuCoefs
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r4 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₁ rd₁ wr₁ sp₁
  have hP₁ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i bound s₁ := hP.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  have h1₁ : s₁.gpr .r1 = BitVec.ofNat 32 first := by rw [g₁ _ (by decide), h1]
  rw [h1, hP.r4, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
    toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)] at z₁
  refine WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
  · -- No coefficient.
    have hge : bound ≤ first := by rw [z₁] at hge; simpa using hge
    refine WP.block_nil ⟨hP₁, ?_, k₁⟩
    rw [show bound - first = 0 by omega]
    exact ⟨by omega, h1₁, by rw [m₁]; exact hh⟩
  · -- The first coefficient, then the others.
    have hlt : first < bound := by rw [z₁] at hlt; simpa using hlt
    have hF1 : optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i first) (List.range 1) (hA₀, first) =
        some (huSet i ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD first 0).toNat hA₀, first + 1) := by
      simp only [List.range_one, optFold, huStep, gt_iff_lt, Nat.lt_irrefl, false_and, ite_false]; rfl
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.first_ok hp hA hi hlt hbω (hA' := hA₀) hP₁ h1₁ (by rw [m₁]; exact hh))
      fun s₂ ⟨hP₂, r1₂, hh₂, z₂, k₂⟩ => ?_)
    refine WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun hge₂ => ?_) (fun hlt₂ => ?_)
    · have hge₂ : bound ≤ first + 1 := by rw [z₂] at hge₂; simpa using hge₂
      refine WP.block_nil ⟨hP₂, ?_, k₁.trans k₂⟩
      rw [show bound - first = 1 by omega, hF1]
      exact ⟨by omega, r1₂, hh₂⟩
    · have hlt₂ : first + 1 < bound := by rw [z₂] at hlt₂; simpa using hlt₂
      exact WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.nexts_ok hp hA hi hbω (Nat.le_refl 1) hF1 rfl hlt₂ hP₂ r1₂ hh₂) fun s₃ ⟨hP₃, hr₃, k₃⟩ =>
        ⟨hP₃, hr₃, (k₁.trans k₂).trans k₃⟩

end

/-! ## The polynomials -/

/-- The spec's state after `i` polynomials. -/
abbrev huS (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀)) (List.range i) (Array.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) noHint, 0)

/-- Before polynomial `i`, in the loops that start from `sA`. -/
structure OInv (s₀ sA : State) (i : Nat) (s : State) : Prop where
  com : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s
  r5 : s.gpr .r5 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i)
  r3 : s.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ + BitVec.ofNat 32 (1024 * i)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (1 * (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀ - i))
  st : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SRel s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ i) s

/-- A polynomial writes at most `r1`, `r4`, `r7` and `r12`. -/
def KeepP (s s' : State) : Prop :=
  (∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem KeepC.keepP {s s' : State} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s') : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s s' :=
  ⟨fun r a _ c d => h.1 r a c d, h.2⟩

theorem KeepP.trans {s s' s'' : State} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s s') (h' : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s' s'') : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s s'' :=
  ⟨fun r a b c d => (h'.1 r a b c d).trans (h.1 r a b c d), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem UCom.ofP {s₀ sA s s' : State} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s) (hk : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s s') (hm : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] s.mem s'.mem) :
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s' :=
  ⟨(hk.1 _ (by decide) (by decide) (by decide) (by decide)).trans h.r0,
    (hk.1 _ (by decide) (by decide) (by decide) (by decide)).trans h.r2,
    hk.2.1.trans h.rd, hk.2.2.1.trans h.wr, hk.2.2.2.trans h.sp, h.frame.trans hm⟩

theorem keepP_r4 {s s' : State} (h : ∀ r, r ≠ .r4 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s s' := ⟨fun r _ b _ _ => h r b, hrd, hwr, hsp⟩

theorem keepP_r7 {s s' : State} (h : ∀ r, r ≠ .r7 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s s' := ⟨fun r _ _ c _ => h r c, hrd, hwr, hsp⟩

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
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {sA : State} (hA : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.MainPre s₀ sA)
include hp hA

/-- Polynomial `i`: its checks and coefficients, unless a check failed. -/
theorem poly_ok {i : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) {s : State} (hI : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.OInv s₀ sA i s) :
    WP isa (.seq hbuPoly (.block [.dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1024), .subs .r6 .r6 (.imm 1)]))
      s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.OInv s₀ sA (i + 1) s' ∧ s'.z = decide (i + 1 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have eω : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀).toNat = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ := rfl
  have fY := hp.fitY
  have hsucc : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (i + 1) = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ i).bind fun st => huPoly (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) st i := optFold_range_succ _ _ _
  -- After the polynomial, whichever way it went.
  suffices h : WP isa hbuPoly s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s' ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepP s s' ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SRel s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (i + 1)) s' by
    refine WP.seq (WP.mono h fun s₁ ⟨hc₁, k₁, st₁⟩ => ?_)
    refine WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ptail_blk fun s₂ ⟨r5₂, r3₂, r6₂, z₂, m₂, rd₂, wr₂, sp₂, r0₂, r1₂, r2₂⟩ =>
      ⟨⟨⟨by rw [r0₂, hc₁.r0], by rw [r2₂, hc₁.r2], by rw [rd₂, hc₁.rd], by rw [wr₂, hc₁.wr], by rw [sp₂, hc₁.sp],
        by rw [m₂]; exact hc₁.frame⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [r5₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r5, BitVec.add_assoc, ofNat_succ32,
        Nat.add_assoc]
    · rw [r3₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r3, BitVec.add_assoc,
        show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.ofNat_add_ofNat, Nat.mul_succ]
    · rw [r6₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r6]; exact count_sub (k := 1) hi
    · revert st₁
      cases VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (i + 1) with
      | none => exact fun h => by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SRel] at h ⊢; rw [r1₂, h]
      | some st => obtain ⟨hA', idx⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨by rw [r1₂, h1], h2, by rw [m₂]; exact h3⟩
    · rw [z₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r6]
      exact count_z (k := 1) hi (by decide) (by omega)
  unfold hbuPoly
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r2 .r1 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepP_r7 g₁ rd₁ wr₁ sp₁
  have hc₁ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₁ := hI.com.ofP k₁ (by rw [m₁]; exact Frame.refl _ _)
  have hst := hI.st
  cases hS : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ i with
  | none =>
    -- A check failed before: nothing.
    rw [hS] at hst
    have hst : s.gpr .r1 = 256 := hst
    rw [hI.com.r2, hst, ltBit_z (by omega) (by decide), show (256 : BitVec 32).toNat = 256 from rfl] at z₁
    refine WP.ite (M := isa) false (by show some s₁.z = _; rw [z₁, decide_eq_false (by omega)]) (fun h => by cases h)
      fun _ => WP.block_nil ⟨hc₁, k₁, ?_⟩
    rw [hsucc, hS]
    show s₁.gpr .r1 = 256
    rw [g₁ _ (by decide), hst]
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    obtain ⟨h1, hidx, hh⟩ := hst
    rw [hI.com.r2, h1, ltBit_z (by omega) (by rw [toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega)] at z₁
    have h1₁ : s₁.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₁ _ (by decide), h1]
    refine WP.ite (M := isa) true (by show some s₁.z = _; rw [z₁, decide_eq_true hidx]) (fun _ => ?_)
      (fun h => by cases h)
    -- The bound.
    have ebd : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) + BitVec.ofNat 32 0) =
        State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) := by
      rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    rw [WP.seq_iff, WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ldrb4_blk (p := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i)) (by rw [g₁ _ (by decide), hI.r5]) (by
        rw [ebd, hc₁.rd, hc₁.wr]
        exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨r4₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
    rw [ebd, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yByte hp hA.toYPre hc₁ (by omega)] at r4₂
    have k₂ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepP_r4 g₂ rd₂ wr₂ sp₂
    have hc₂ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₂ := hc₁.ofP k₂ (by rw [m₂]; exact Frame.refl _ _)
    have hbl := ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).isLt
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r4 .r1 s₂) fun s₃ ⟨_, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ?_
    have k₃ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepP_r7 g₃ rd₃ wr₃ sp₃
    have hc₃ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₃ := hc₂.ofP k₃ (by rw [m₃]; exact Frame.refl _ _)
    rw [r4₂, g₂ _ (by decide), h1₁, ltBit_z (by rw [byte_toNat32]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
      byte_toNat32, toNat_ofNat32 (by omega)] at z₃
    have hpoly := hsucc
    rw [hS] at hpoly
    simp only [Option.bind_some, huPoly] at hpoly
    have r4₃ : s₃.gpr .r4 = BitVec.ofNat 32 ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).toNat := by
      rw [g₃ _ (by decide), r4₂]; apply BitVec.eq_of_toNat_eq; rw [byte_toNat32, toNat_ofNat32 (by omega)]
    have h1₃ : s₃.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₃ _ (by decide), g₂ _ (by decide), h1₁]
    refine WP.ite (M := isa) _ (show some s₃.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
    · have hge : idx ≤ ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).toNat := by rw [z₃] at hge; simpa using hge
      refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r2 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_)
      have k₄ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepP_r7 g₄ rd₄ wr₄ sp₄
      have hc₄ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₄ := hc₃.ofP k₄ (by rw [m₄]; exact Frame.refl _ _)
      rw [hc₃.r2, r4₃, ltBit_z (by omega) (by rw [toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega)] at z₄
      refine WP.ite (M := isa) _ (show some s₄.z = _ from rfl) (fun hle => ?_) (fun hgt => ?_)
      · -- The coefficients.
        have hle : ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).toNat ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ := by rw [z₄] at hle; simpa using hle
        have hP₄ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.PCom s₀ sA i ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).toNat s₄ :=
          ⟨hc₄, by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hI.r3],
            by rw [g₄ _ (by decide), r4₃]⟩
        refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.coefs_ok hp hA hi (first := idx) (hA₀ := hA') hge hle hP₄
          (by rw [g₄ _ (by decide), h1₃]) (by rw [m₄, m₃, m₂, m₁]; exact hh)) fun s₅ ⟨hP₅, hin₅, k₅⟩ =>
            ⟨hP₅.com, (((k₁.trans k₂).trans k₃).trans k₄).trans k₅.keepP, ?_⟩
        rw [hpoly, ite_neg' (by omega)]
        revert hin₅
        cases optFold (huStep (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) i idx) (List.range (((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).toNat - idx)) (hA', idx) with
        | none => exact id
        | some st => obtain ⟨hA'', idx'⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨h2, by omega, h3⟩
      · -- `bound > ω`: fail.
        have hgt : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ < ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).toNat := by rw [z₄] at hgt; simpa using hgt
        refine WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.fail_ok fun s₅ ⟨r1₅, m₅, k₅⟩ => ⟨hc₄.of k₅ (by rw [m₅]; exact Frame.refl _ _),
          (((k₁.trans k₂).trans k₃).trans k₄).trans k₅.keepP, ?_⟩
        rw [hpoly, ite_pos' (.inr hgt)]; exact r1₅
    · -- `bound < index`: fail.
      have hlt : ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ + i) 0).toNat < idx := by rw [z₃] at hlt; simpa using hlt
      refine WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.fail_ok fun s₄ ⟨r1₄, m₄, k₄⟩ => ⟨hc₃.of k₄ (by rw [m₄]; exact Frame.refl _ _),
        ((k₁.trans k₂).trans k₃).trans k₄.keepP, ?_⟩
      rw [hpoly, ite_pos' (.inl hlt)]; exact r1₄

omit hp hA in
theorem mainPro_blk {s : State} :
    WP isa (.block [.dp .add .r5 .r0 (.reg .r2)]) s fun s' => s'.gpr .r5 = s.gpr .r0 + s.gpr .r2 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r5 → s'.gpr r = s.gpr r := by
  run_block [true_and]
  intro r hr; rw [ite_neg' hr]

/-- The polynomials, from the state after zeroing `h`. -/
theorem main_ok (h0 : sA.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) (h1 : sA.gpr .r1 = 0) (h2 : sA.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀)
    (h3 : sA.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀) (h6 : sA.gpr .r6 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀))
    (hz : ∀ t < 256 * VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀, coeffAt sA.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) t = 0) :
    WP isa hbuMain sA fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s' ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SRel s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀)) s' := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  unfold hbuMain
  refine WP.seq (WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainPro_blk fun s₁ ⟨r5₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.OInv s₀ sA) (N := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (by omega) (fun i hi s h => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.poly_ok hp hA hi h)
    (fun s hI => ⟨hI.com, hI.st⟩)
    ⟨⟨by rw [g₁ _ (by decide), h0], by rw [g₁ _ (by decide), h2], rd₁, wr₁, sp₁, by rw [m₁]; exact Frame.refl _ _⟩,
      by rw [r5₁, h0, h2, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [g₁ _ (by decide), h3]; simp, by rw [g₁ _ (by decide), h6, Nat.one_mul, Nat.sub_zero], ?_⟩
  show VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SRel s₀ (some (Array.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) noHint, 0)) s₁
  exact ⟨by rw [g₁ _ (by decide), h1]; rfl, Nat.zero_le _, by rw [m₁]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.harr_zero hz⟩

end

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {sA : State} (hY : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.YPre s₀ sA)
include hp hY

/-! ## The bytes after the last index -/

omit hp hY in
theorem tload_blk {s : State} {y i : BitVec 32} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r12 .r0 (.reg .r1), .ldrb .r12 .r12 0, .cmp .r12 (.imm 0)]) s fun s' =>
      s'.z = ((s.mem (State.addr (y + i + BitVec.ofNat 32 0))).setWidth 32 - 0 == 0) ∧ s'.mem = s.mem ∧
      s'.gpr .r1 = i ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  run_block [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC, h0, h1, ib, true_and, and_true]
  intro r _ _ c; rw [ite_neg' c, ite_neg' c]

omit hp hY in
theorem inc_blk {s : State} :
    WP isa (.block [.dp .add .r1 .r1 (.imm 1)]) s fun s' => s'.gpr .r1 = s.gpr .r1 + 1 ∧ s'.mem = s.mem ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC s s' := by
  run_block [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.KeepC, true_and, and_true]
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
theorem trail_ok {idx : Nat} (hidx : idx ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) {s : State} (hc : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) :
    WP isa hbuTrail s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s' ∧ s'.mem = s.mem ∧
      (match optFold (huTrail (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀)) (List.range' idx (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ - idx)) () with
        | some _ => s'.gpr .r1 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀)
        | none => s'.gpr .r1 = 256) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have eω : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀).toNat = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ := rfl
  have fY := hp.fitY
  unfold hbuTrail
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r2 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₁ rd₁ wr₁ sp₁
  have hc₁ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₁ := hc.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  rw [h1, hc.r2, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by omega), toNat_ofNat32 (by omega)] at z₁
  refine WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
  · have hge : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ ≤ idx := by rw [z₁] at hge; simpa using hge
    refine WP.block_nil ⟨hc₁, m₁, ?_⟩
    rw [show VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ - idx = 0 by omega]
    show s₁.gpr .r1 = _
    rw [g₁ _ (by decide), h1, show idx = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ by omega]
  · have hlt : idx < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ := by rw [z₁] at hlt; simpa using hlt
    refine WP.loop (M := isa) (fun m s' => ∃ u, m = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ - idx - u ∧ idx + u < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ ∧
        optFold (huTrail (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀)) (List.range' idx u) () = some () ∧ s'.gpr .r1 = BitVec.ofNat 32 (idx + u) ∧
        VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s' ∧ s'.mem = s.mem)
      (fun m s' ⟨u, hm, hu, hF, h1', hc', hm'⟩ => ?_) _ s₁
      ⟨0, rfl, by omega, rfl, by rw [g₁ _ (by decide), h1]; rfl, hc₁, m₁⟩
    have eb : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ + BitVec.ofNat 32 (idx + u) + BitVec.ofNat 32 0) =
        State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 (idx + u) := by
      rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.tload_blk hc'.r0 h1' (by
        rw [eb, hc'.rd, hc'.wr]
        exact ⟨_, List.mem_append_left _ hY.rd, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨z₂, m₂, r1₂, k₂⟩ => ?_)
    rw [eb, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yByte hp hY hc' (by omega), VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.byte_z] at z₂
    have hc₂ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₂ := hc'.of k₂ (by rw [m₂]; exact Frame.refl _ _)
    have hF1 : optFold (huTrail (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀)) (List.range' idx (u + 1)) () = huTrail (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀) () (idx + u) := by
      rw [optFold_range'_succ, hF]; rfl
    refine WP.seq (WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun heq => ?_) (fun hne => ?_))
    · -- A zero byte: next.
      have heq : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (idx + u) 0 = 0 := by rw [z₂] at heq; simpa using heq
      have hF2 : optFold (huTrail (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀)) (List.range' idx (u + 1)) () = some () := by
        rw [hF1, huTrail, ite_neg' (by simpa using heq)]
      refine WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.inc_blk fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
      have r1₃' : s₃.gpr .r1 = BitVec.ofNat 32 (idx + (u + 1)) := by rw [r1₃, r1₂, ofNat_succ32, Nat.add_assoc]
      refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r2 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
      have k₄ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₄ rd₄ wr₄ sp₄
      have hc₄ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₄ := (hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).of k₄ (by rw [m₄]; exact Frame.refl _ _)
      rw [r1₃', (hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).r2,
        ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by omega), toNat_ofNat32 (by omega)] at z₄
      have r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (idx + (u + 1)) := by rw [g₄ _ (by decide), r1₃']
      by_cases e : idx + (u + 1) < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀
      · exact .inr ⟨by show some (!s₄.z) = some true; rw [z₄, decide_eq_false (by omega)]; rfl, _, by omega, u + 1,
          rfl, e, hF2, r1₄, hc₄, by rw [m₄, m₃, m₂, hm']⟩
      · refine .inl ⟨by show some (!s₄.z) = some false; rw [z₄, decide_eq_true (by omega)]; rfl, hc₄,
          by rw [m₄, m₃, m₂, hm'], ?_⟩
        rw [show VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ - idx = u + 1 by omega, hF2]
        show s₄.gpr .r1 = _
        rw [r1₄, show idx + (u + 1) = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ by omega]
    · -- A nonzero byte: fail.
      have hne : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀).getD (idx + u) 0 ≠ 0 := by rw [z₂] at hne; simpa using hne
      have hn : optFold (huTrail (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀)) (List.range' idx (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ - idx)) () = none :=
        optFold_range'_none _ _ (show u + 1 ≤ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ - idx by omega) (by rw [hF1, huTrail, ite_pos' hne])
      refine WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.fail_ok fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
      refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r2 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
      have k₄ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₄ rd₄ wr₄ sp₄
      have hc₃ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s₃ := hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)
      rw [r1₃, hc₃.r2, ltBit_z (by decide) (by omega), show (256 : BitVec 32).toNat = 256 from rfl] at z₄
      refine .inl ⟨by show some (!s₄.z) = some false; rw [z₄, decide_eq_true (by omega)]; rfl,
        hc₃.of k₄ (by rw [m₄]; exact Frame.refl _ _), by rw [m₄, m₃, m₂, hm'], ?_⟩
      rw [hn]
      show s₄.gpr .r1 = 256
      rw [g₄ _ (by decide), r1₃]

omit hY in
/-- After a failed check, the bytes after the last index are not checked. -/
theorem trail_fail {s : State} (hc : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s) (h1 : s.gpr .r1 = 256) :
    WP isa hbuTrail s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sA s' ∧ s'.mem = s.mem ∧ s'.gpr .r1 = 256 := by
  obtain ⟨-, -, -, hω80, -, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have eω : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀).toNat = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ := rfl
  unfold hbuTrail
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ltBit_ok .r7 .r1 .r2 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.keepC_r7 g₁ rd₁ wr₁ sp₁
  rw [h1, hc.r2, ltBit_z (by decide) (by omega), show (256 : BitVec 32).toNat = 256 from rfl] at z₁
  refine WP.ite (M := isa) true (by show some s₁.z = _; rw [z₁, decide_eq_true (by omega)]) (fun _ => ?_)
    (fun h => by cases h)
  exact WP.block_nil ⟨hc.of k₁ (by rw [m₁]; exact Frame.refl _ _), m₁, by rw [g₁ _ (by decide), h1]⟩

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackMain`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, correct

The whole function: the load of `hlen`, the frame, and in it zeroing `h`, the
loops (`HintUnpackLoops.lean`), the return value and the reloads of the saved
registers; the result is `HintBitUnpack` (Algorithm 21) through its fold form
(`hintBitUnpack_eq`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-- The state the body runs from. -/
abbrev P1 (s₀ : State) : State := pushed [.r4, .r5, .r6, .r7] (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀))

/-- The state after zeroing `h`. -/
def UZ (s₀ a : State) : Prop :=
  a.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀ ∧ a.gpr .r1 = 0 ∧ a.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀ ∧ a.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀ ∧
    a.gpr .r6 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) ∧ (∀ t < 256 * VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀, coeffAt a.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) t = 0) ∧
    Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).mem a.mem ∧ a.rd = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).rd ∧ a.wr = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).wr ∧ a.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).sp

/-- The state after the polynomials, in the run from `sa`. -/
def UM (s₀ a : State) : Prop :=
  ∃ sa, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀ sa ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sa a ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.SRel s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀)) a

/-- The result. -/
def UPost (s₀ : State) (m : Mem) (r : BitVec 32) : Prop :=
  match hintBitUnpack (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) (bytesAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀)) with
  | some hint => r = 1 ∧ HintIs m (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) hint
  | none => r = 0

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀)
include hp

theorem hsp16 : 4 * [Reg.r4, Reg.r5, Reg.r6, Reg.r7].length ≤ (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀)).sp.toNat := hp.sp

theorem hfr : frameR (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀)) [.r4, .r5, .r6, .r7] = ⟨State.addr s₀.sp - BitVec.ofNat 64 16, 16⟩ :=
  frameR_eq [.r4, .r5, .r6, .r7] (s := s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀)) hp.sp

theorem zeroP_ok : WP isa hbuZero (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀) :=
  VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.zero_ok hp rfl rfl rfl rfl rfl (by simp [RegUpd.wr_setReg, hp.wr])

/-- The body changes memory only in the frame and `h`. -/
theorem uz_frame {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀ a) :
    Frame [⟨State.addr s₀.sp - BitVec.ofNat 64 16, 16⟩, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] s₀.mem a.mem := by
  have hpf := pushed_frame [.r4, .r5, .r6, .r7] (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hsp16 hp)
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hfr hp] at hpf
  exact (hpf.mono (by simp)).trans (hz.2.2.2.2.2.2.1.mono (by simp))

/-- The bytes of `y`, after zeroing `h`, and after the loops. -/
theorem uz_y {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀ a) {m : Mem} (hm : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] a.mem m) :
    ∀ t < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀, m (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 t) = s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 t) := by
  intro t ht
  have fY := hp.fitY
  have hc : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₀).Contains (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀) + BitVec.ofNat 64 t) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [hm _ fun r hr hc' => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.d_yh _ hc hc',
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_frame hp hz _ fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.b_y _ hc' hc
      · exact hp.d_yh _ hc hc']

theorem mainPre_of {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀ a) {rd wr : List Region} (hr : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₀ ∈ rd) (hw : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀ ∈ wr) :
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.MainPre s₀ (a.withRegions rd wr) := ⟨⟨hr, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_y hp hz (Frame.refl _ _)⟩, hw⟩

theorem uz_rd {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀ a) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₀ ∈ a.rd := by
  rw [hz.2.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp.rd]

theorem uz_wr {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀ a) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀ ∈ a.wr := by
  rw [hz.2.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp.wr]

/-- The polynomials, from the state after zeroing `h`. -/
theorem mainP_ok {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₀ a) : WP isa hbuMain a (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₀) := by
  obtain ⟨a0, a1, a2, a3, a6, az, -⟩ := id hz
  have := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainPre_of hp hz (rd := a.rd) (wr := a.wr) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_rd hp hz) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_wr hp hz)
  rw [State.withRegions_self] at this
  exact WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.main_ok hp this a0 a1 a2 a3 a6 az) fun s' ⟨hc, hs⟩ => ⟨a, hz, hc, hs⟩

/-- The start of the loop over the trailing bytes, narrowed to `y`. -/
theorem um_trail {a : State} (hm : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₀ a) {rd wr : List Region} (hr : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₀ ∈ rd) :
    VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.YPre s₀ (a.withRegions rd wr) ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ (a.withRegions rd wr) (a.withRegions rd wr) := by
  obtain ⟨sa, hz, hc, -⟩ := hm
  exact ⟨⟨hr, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_y hp hz hc.frame⟩, hc.r0, hc.r2, rfl, rfl, rfl, Frame.refl _ _⟩

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
theorem harr_hintIs {s₀ : State} {m : Mem} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.HArr s₀ m hA) :
    HintIs m (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

theorem ret_val (ω x : Nat) (hω : ω ≤ 80) (hx : x < 2 ^ 31) :
    (1 : BitVec 32) - ((BitVec.ofNat 32 ω - BitVec.ofNat 32 x) >>> 31) = if ω < x then 0 else 1 := by
  rw [ltBit_val (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
    toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  split <;> rfl

theorem fail_val {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) : (1 : BitVec 32) - ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀ - 256) >>> 31) = 0 := by
  obtain ⟨-, -, -, hω80, -, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have e := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ret_val (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) 256 hω80 (by decide)
  rw [ite_pos' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  exact e

/-- The body of the frame: the result, the reloads of `r5`–`r7`, and the word
the pop reloads into `r4`. -/
theorem body_ok {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) :
    WP isa hintBitUnpackBody (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀) fun s₂ => s₂.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).sp ∧ s₂.gpr .r5 = s₀.gpr .r5 ∧
      s₂.gpr .r6 = s₀.gpr .r6 ∧ s₂.gpr .r7 = s₀.gpr .r7 ∧ s₂.mem.readW (State.addr s₂.sp) 32 = s₀.gpr .r4 ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPost s₀ s₂.mem (s₂.gpr .r0) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ufacts hp
  have eω : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW s₀).toNat = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ := rfl
  have hsp := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hsp16 hp
  unfold hintBitUnpackBody
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.zeroP_ok hp) fun sa hz => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainP_ok hp hz) fun sb hm => ?_)
  obtain ⟨sa', hz', hcb, hst⟩ := id hm
  have hA := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainPre_of hp hz' (rd := sa'.rd) (wr := sa'.wr) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_rd hp hz') (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_wr hp hz')
  rw [State.withRegions_self] at hA
  -- What the trailing bytes and the return leave, whichever way the checks went.
  suffices h : WP isa hbuTrail sb fun sc => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UCom s₀ sa' sc ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPost s₀ sc.mem (1 - ((sc.gpr .r2 - sc.gpr .r1) >>> 31)) by
    refine WP.seq (WP.mono h fun sc ⟨hcc, hpc⟩ => ?_)
    have hfc : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀] (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).mem sc.mem := hz'.2.2.2.2.2.2.1.trans hcc.frame
    have hdh : ∀ r ∈ [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₀], (frameR (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₀)) [.r4, .r5, .r6, .r7]).Disjoint r := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hfr hp]; exact hp.b_h
    have hsc : sc.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).sp := by rw [hcc.sp, hz'.2.2.2.2.2.2.2.2.2]
    have hin : ∀ i < 4, InRegions (sc.rd ++ sc.wr) (State.addr (sc.sp + BitVec.ofNat 32 (4 * i))) 4 := fun i hi => by
      rw [hcc.wr, hz'.2.2.2.2.2.2.2.2.1, pushed_wr, hsc]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains [.r4, .r5, .r6, .r7] hsp hi⟩
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.ret_blk (hin 1 (by decide)) (hin 2 (by decide)) (hin 3 (by decide)))
      fun sd ⟨r0d, r5d, r6d, r7d, md, spd⟩ => ⟨by rw [spd, hsc], ?_, ?_, ?_, ?_, by rw [md, r0d]; exact hpc⟩
    · rw [r5d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 1) (by decide)]; rfl
    · rw [r6d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 2) (by decide)]; rfl
    · rw [r7d, hsc, frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 3) (by decide)]; rfl
    · rw [md, spd, hsc, show State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).sp = State.addr ((VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).sp + BitVec.ofNat 32 (4 * 0)) by simp,
        frame_saved [.r4, .r5, .r6, .r7] hsp hfc hdh (i := 0) (by decide)]; rfl
  unfold VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPost
  rw [hintBitUnpack_eq]
  cases hS : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) with
  | none =>
    rw [hS] at hst
    have hst : sb.gpr .r1 = 256 := hst
    rw [show optFold (huPoly (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) (bytesAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀)).toArray)
      (List.range (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀)) (Array.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) noHint, 0) = none from hS]
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_fail hp hcb hst) fun sc ⟨hcc, _, r1c⟩ => ⟨hcc, ?_⟩
    show _ = 0
    rw [hcc.r2, r1c]
    exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.fail_val hp
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    obtain ⟨h1, hidx, hh⟩ := hst
    rw [show optFold (huPoly (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀) (bytesAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₀)).toArray)
      (List.range (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀)) (Array.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) noHint, 0) = some (hA', idx) from hS]
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_ok hp hA.toYPre hidx hcb h1) fun sc ⟨hcc, mc, hr⟩ => ⟨hcc, ?_⟩
    dsimp only
    revert hr
    cases optFold (huTrail (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs s₀)) (List.range' idx (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω s₀ - idx)) () with
    | none =>
      intro r1c
      show _ = 0
      rw [hcc.r2, r1c]
      exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.fail_val hp
    | some _ =>
      intro r1c
      refine ⟨?_, by rw [mc]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.harr_hintIs hh⟩
      rw [hcc.r2, r1c, ← eω, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self]
      rfl

/-- The whole function: the result, and the registers it saves and restores
(the others it never writes). -/
theorem correct {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.hintBitUnpack s₀ fun s' => s'.gpr .r4 = s₀.gpr .r4 ∧ s'.gpr .r5 = s₀.gpr .r5 ∧
      s'.gpr .r6 = s₀.gpr .r6 ∧ s'.gpr .r7 = s₀.gpr .r7 ∧ s'.gpr .lr = s₀.gpr .lr ∧ s'.sp = s₀.sp ∧
      VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPost s₀ s'.mem (s'.gpr .r0) := by
  unfold Impl.MlDsa.Arm.Pack.hintBitUnpack
  refine WP.seq (WP.mono (entry_ok (s := s₀) (by
    rw [hp.rd]; exact ⟨VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uargR s₀, by simp, Region.contains_self _ _⟩)) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.frame (rs := [.r4, .r5, .r6, .r7]) (r := .r4) rfl (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hsp16 hp) (by decide)
    (WP.mono (WP.gpr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.body_ok hp) (r := .lr) (noWrite (by decide +kernel))) fun s₂ ⟨⟨hsp, h5, h6, h7, h4, hr⟩, hlr⟩ => ?_)
  refine ⟨?_, by rw [popped_gpr (by decide), h5], by rw [popped_gpr (by decide), h6], by rw [popped_gpr (by decide), h7],
    by rw [popped_gpr (by decide), hlr]; rfl, ?_, by rw [popped_mem, popped_gpr (by decide)]; exact hr⟩
  · simp only [popped, State.setReg, ite_true]; exact h4
  · simp only [popped_sp, hsp, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1, pushed_sp]
    exact BitVec.sub_add_cancel _ _

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackCT`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the lengths,
`ω`, the stack pointer and `y`, which the contract lets the function leak)
leak the same trace (`RelCT`), phase by phase: the load of `hlen` and the
return, with the reloads of the saved registers, access only the stack
(`RelCT.spBlock`); zeroing `h` is proved by the taint analysis; the
polynomials by `memTaint`, from the states narrowed to `y` and `h`
(`RelCT.narrow`), on which both runs agree once `h` is zeroed; and the bytes
after the last index likewise, from the states narrowed to `y`, which the
index, the same in both runs (that of the spec, from the same `y`), then
reads. What each run is at each point comes from the correctness proof
(`RelCT.wp`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

theorem pre_of {s : State} (h : (hintBitUnpackContract Arm.abi 16).pre s) : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem map_toNat_inj : ∀ {b₁ b₂ : List Byte}, b₁.map (·.toNat) = b₂.map (·.toNat) → b₁ = b₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A byte of the words of a region of zero words. -/
theorem byte_of_zero_words {m : Mem} {p : Addr} {N : Nat} (hz : ∀ t < N, coeffAt m p t = 0) {a : Addr}
    (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m a = 0 := by
  simp only [Region.Contains] at ha
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m (coeffAddr p _) ht, ← coeffAt_eq, hz _ (by omega)]
  simp

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₁
  hp₂ : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₂
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₁)) = leakBytes (bytesAt s₂.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₂)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₂))
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  arg : stackArg s₁ 0 = stackArg s₂ 0

section
variable {s₁ s₂ : State} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.Two s₁ s₂)
include h

theorem yR_eq : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁ = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₂ := by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uL, h.r0, h.r1]

theorem hR_eq : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₁ = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₂ := by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL, h.r3, h.arg]

theorem bytes_eq : bytesAt s₁.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₁) = bytesAt s₂.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₂)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₂) :=
  VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.map_toNat_inj h.leak

theorem huS_eq : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₁ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₁) = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₂ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₂) := by
  unfold VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uYs
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.bytes_eq h]
  simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uL, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW, h.r1, h.r2]

/-- A byte of `y`, the same in both runs. -/
theorem yByte_eq {a b : State} (ha : ∀ t < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₁, a.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁) + BitVec.ofNat 64 t) =
      s₁.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁) + BitVec.ofNat 64 t))
    (hb : ∀ t < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₂, b.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₂) + BitVec.ofNat 64 t) = s₂.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₂) + BitVec.ofNat 64 t))
    {x : Addr} (hx : (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁).Contains x 1) : a.mem x = b.mem x := by
  have hlt : (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁)).toNat < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₁ := by simp only [Region.Contains] at hx; omega
  have ea : x = State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁) + BitVec.ofNat 64 (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁)).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have eY : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₂ = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁ := by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY, h.r0]
  have eL : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₂ = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₁ := by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uL, h.r1]
  have e := congrArg (·.getD (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY s₁)).toNat 0) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.bytes_eq h)
  rw [bytesAt_getD _ _ hlt, bytesAt_getD _ _ (show _ < VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen s₂ by rw [eL]; exact hlt), eY, ← ea] at e
  have h1 : a.mem x = s₁.mem x := by have := ha _ hlt; rwa [← ea] at this
  have h2 : b.mem x = s₂.mem x := by have := hb _ (by rw [eL]; exact hlt); rwa [eY, ← ea] at this
  rw [h1, h2]; exact e

/-- The polynomials, from the states narrowed to `y` and `h`. -/
theorem main_ct : RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₁ a ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₂ b) hbuMain fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine Hint.RelCT.narrow (fun _ => [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁]) (fun _ => [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₁]) (fun a b ⟨ha, hb⟩ => ?_)
    (fun a b ⟨ha, hb⟩ => ?_) ?_
  · have hra := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_rd hp₁ ha
    have hwa := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_wr hp₁ ha
    have hrb : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁ ∈ b.rd := by rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yR_eq h]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_rd hp₂ hb
    have hwb : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₁ ∈ b.wr := by rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hR_eq h]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_wr hp₂ hb
    exact ⟨Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hra
        · exact List.mem_append_right _ hwa,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwa,
      Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hrb
        · exact List.mem_append_right _ hwb,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwb⟩
  · obtain ⟨a0, a1, a2, a3, a6, az, -⟩ := id ha
    obtain ⟨b0, b1, b2, b3, b6, bz, -⟩ := id hb
    obtain ⟨t₁, u₁, e₁, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.main_ok hp₁ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainPre_of hp₁ ha (rd := [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁]) (wr := [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₁])
      (List.mem_singleton_self _) (List.mem_singleton_self _)) a0 a1 a2 a3 a6 az
    obtain ⟨t₂, u₂, e₂, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.main_ok hp₂ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainPre_of hp₂ hb (rd := [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁]) (wr := [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₁])
      (by rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yR_eq h]; exact List.mem_singleton_self _) (by rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hR_eq h]; exact List.mem_singleton_self _))
      b0 b1 b2 b3 b6 bz
    exact ⟨⟨t₁, u₁, e₁⟩, t₂, u₂, e₂⟩
  · refine RelCT.taint (A := Hint.memTaint) (Taint.ofRegs [.r0, .r1, .r2, .r3, .r6])
      (fun a' b' ⟨a, b, ⟨ha, hb⟩, ea, eb⟩ => ?_) (by taint_decide)
    subst ea eb
    refine ⟨Taint.agree_ofRegs fun r hr => ?_, rfl, rfl, fun x ⟨r, hr, hc⟩ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simp only [State.withRegions_gpr, ha.1, hb.1, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY, h.r0]
      · simp only [State.withRegions_gpr, ha.2.1, hb.2.1]
      · simp only [State.withRegions_gpr, ha.2.2.1, hb.2.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW, h.r2]
      · simp only [State.withRegions_gpr, ha.2.2.2.1, hb.2.2.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uH, h.r3]
      · simp only [State.withRegions_gpr, ha.2.2.2.2.1, hb.2.2.2.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uLen, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uL, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uω, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW, h.r1, h.r2]
    · simp only [State.withRegions_rd, State.withRegions_wr, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yByte_eq h (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_y h.hp₁ ha (Frame.refl _ _)) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_y h.hp₂ hb (Frame.refl _ _)) hc
      · show a.mem x = b.mem x
        rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.byte_of_zero_words (N := (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₁).toNat) (fun t ht => ha.2.2.2.2.2.1 t (by rw [hp₁.hlen] at ht; exact ht)) hc,
          VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.byte_of_zero_words (N := (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₂).toNat) (fun t ht => hb.2.2.2.2.2.1 t (by rw [hp₂.hlen] at ht; exact ht))
            (show (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uhR s₂).Contains x 1 by rw [← VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.hR_eq h]; exact hc)]

omit h in
/-- The loop over the trailing bytes runs from the states after the
polynomials, narrowed to `rd` and `wr` (and from the actual one): whichever
way the checks went. -/
theorem trail_run {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {a : State} (hm : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₀ a) {rd wr : List Region}
    (hr : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₀ ∈ rd) : WP isa hbuTrail (a.withRegions rd wr) fun _ => True := by
  obtain ⟨hY, hc⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.um_trail hp hm (wr := wr) hr
  obtain ⟨-, -, -, hst⟩ := hm
  cases hS : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) with
  | none =>
    rw [hS] at hst
    exact WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_fail hp hc hst) fun _ _ => trivial
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    exact WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_ok hp hY hst.2.1 hc hst.1) fun _ _ => trivial

omit h in
theorem trail_sp {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UPre s₀) {a : State} (hm : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₀ a) :
    WP isa hbuTrail a fun s' => s'.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₀).sp := by
  obtain ⟨sa, hz, hc, hst⟩ := hm
  have hA := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainPre_of hp hz (rd := sa.rd) (wr := sa.wr) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_rd hp hz) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_wr hp hz)
  rw [State.withRegions_self] at hA
  cases hS : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₀ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₀) with
  | none =>
    rw [hS] at hst
    exact WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_fail hp hc hst) fun s' h' => h'.1.sp.trans hz.2.2.2.2.2.2.2.2.2
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    exact WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_ok hp hA.toYPre hst.2.1 hc hst.1) fun s' h' => h'.1.sp.trans hz.2.2.2.2.2.2.2.2.2

/-- The bytes after the last index, from the states narrowed to `y`. -/
theorem trail_ct : RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₁ a ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₂ b) hbuTrail fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine Hint.RelCT.narrow (fun _ => [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁]) (fun _ => []) (fun a b ⟨ha, hb⟩ => ?_)
    (fun a b ⟨ha, hb⟩ => ?_) ?_
  · obtain ⟨sa, hza, hca, -⟩ := ha
    obtain ⟨sb, hzb, hcb, -⟩ := hb
    have hra : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁ ∈ a.rd := by rw [hca.rd]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_rd hp₁ hza
    have hrb : VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁ ∈ b.rd := by rw [hcb.rd, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yR_eq h]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_rd hp₂ hzb
    refine ⟨fun x n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩, fun _ _ ⟨_, hr, _⟩ => (nomatch hr),
      fun x n ⟨r, hr, hc⟩ => ⟨r, ?_, hc⟩, fun _ _ ⟨_, hr, _⟩ => (nomatch hr)⟩
    · simp only [List.append_nil, List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hra
    · simp only [List.append_nil, List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hrb
  · obtain ⟨t₁, u₁, e₁, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_run hp₁ ha (rd := [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁]) (wr := []) (List.mem_singleton_self _)
    obtain ⟨t₂, u₂, e₂, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_run hp₂ hb (rd := [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uyR s₁]) (wr := [])
      (by rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yR_eq h]; exact List.mem_singleton_self _)
    exact ⟨⟨t₁, u₁, e₁⟩, t₂, u₂, e₂⟩
  · refine RelCT.taint (A := Hint.memTaint) (Taint.ofRegs [.r0, .r1, .r2])
      (fun a' b' ⟨a, b, ⟨ha, hb⟩, ea, eb⟩ => ?_) (by taint_decide)
    subst ea eb
    obtain ⟨sa, hza, hca, hsa⟩ := ha
    obtain ⟨sb, hzb, hcb, hsb⟩ := hb
    refine ⟨Taint.agree_ofRegs fun r hr => ?_, rfl, rfl, fun x ⟨r, hr, hc⟩ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only [State.withRegions_gpr, hca.r0, hcb.r0, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uY, h.r0]
      · simp only [State.withRegions_gpr]
        rw [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS_eq h] at hsa
        revert hsa hsb
        cases VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.huS s₂ (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uk s₂) with
        | none => exact fun h₁ h₂ => h₁.trans h₂.symm
        | some st => obtain ⟨hA', idx⟩ := st; exact fun h₁ h₂ => h₁.1.trans h₂.1.symm
      · simp only [State.withRegions_gpr, hca.r2, hcb.r2, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uW, h.r2]
    · simp only [State.withRegions_rd, State.withRegions_wr, List.append_nil, List.mem_singleton] at hr; subst hr
      exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.yByte_eq h (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_y hp₁ hza hca.frame) (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uz_y hp₂ hzb hcb.frame) hc

/-- The body of the frame. -/
theorem body_ct : RelCT isa (fun a b => a = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₁ ∧ b = VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₂) hintBitUnpackBody fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold hintBitUnpackBody
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₁ a ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UZ s₂ b) (relct_wp ?_ fun a b ⟨ea, eb⟩ =>
    ⟨by rw [ea]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.zeroP_ok hp₁, by rw [eb]; exact VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.zeroP_ok hp₂⟩) ?_
  · refine RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r1, .r2, .r3, .r12])
      (fun a b ⟨ea, eb⟩ => Taint.agree_ofRegs fun r hr => ?_) (by taint_decide)
    subst ea eb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1, pushed_gpr, RegUpd.gpr_setReg, h.r1]; rfl
    · simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1, pushed_gpr, RegUpd.gpr_setReg, h.r2]; rfl
    · simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1, pushed_gpr, RegUpd.gpr_setReg, h.r3]; rfl
    · simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1, pushed_gpr, RegUpd.gpr_setReg, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL, h.arg]; rfl
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₁ a ∧ VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.UM s₂ b) (relct_wp (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.main_ct h) fun a b hab =>
    ⟨VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainP_ok hp₁ hab.1, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.mainP_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => a.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₁).sp ∧ b.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1 s₂).sp)
    (relct_wp (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_ct h) fun a b hab => ⟨VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_sp hp₁ hab.1, VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.trail_sp hp₂ hab.2⟩) ?_
  exact Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by
    rw [ea, eb]; simp only [VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.P1, pushed_sp, RegUpd.sp_setReg, h.sp]

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) Impl.MlDsa.Arm.Pack.hintBitUnpack fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold Impl.MlDsa.Arm.Pack.hintBitUnpack
  refine RelCT.seq (R := fun a b => a = s₁.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₁) ∧ b = s₂.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uHL s₂))
    (relct_wp (Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by rw [ea, eb, h.sp]) fun a b ⟨ea, eb⟩ =>
      ⟨by rw [ea]; exact entry_ok (by rw [hp₁.rd]; exact ⟨VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uargR s₁, by simp, Region.contains_self _ _⟩),
       by rw [eb]; exact entry_ok (by rw [hp₂.rd]; exact ⟨VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.uargR s₂, by simp, Region.contains_self _ _⟩)⟩) ?_
  refine RelCT.frame (fun a b ⟨ea, eb⟩ => by rw [ea, eb]; simp only [RegUpd.sp_setReg, h.sp]) ?_
  refine RelCT.mono (VG.Proof.MlDsa.Arm.Pack.Hint.Unpack.body_ct h) (fun a b ⟨x, y, ⟨ex, ey⟩, px, py⟩ => ?_) fun _ _ h => h
  subst ex ey
  exact ⟨(push_pushed' px).1, (push_pushed' py).1⟩

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

/-- The memory of the satisfying state: `hlen = 1024` on the stack. -/
def unpackSatMem : Mem := fun a => if a = 0x8001 then 4 else 0

/-- A state satisfying the precondition. -/
def unpackSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 84 | .r2 => 80 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := VG.Proof.MlDsa.Arm.Pack.Hint.unpackSatMem
  rd := [⟨0x1000, 84⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 4096⟩]

theorem hintBitUnpack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.hintBitUnpack (hintBitUnpackContract Arm.abi 16) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · have hp := Unpack.pre_of hs
    obtain ⟨t, s', he, h4, h5, h6, h7, hlr, hsp, hr⟩ := Unpack.correct hp
    refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      rotate_right
      · exact hlr
      all_goals exact Exec.gpr (noWrite (by decide +kernel)) he
    · sig_post [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [VG.Proof.MlKem.Arm.setWidth_append32]
      exact hr
  · have hp₁ := Unpack.pre_of h₁
    have hp₂ := Unpack.pre_of h₂
    sig_pub [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, ha⟩ := hpub
    exact (Unpack.all_ct ⟨hp₁, hp₂, hsp, hl, h0, h1, h2, h3, ha⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlDsa.Arm.Pack.Hint.unpackSatState, ?_⟩
    sig_sat_check [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Pack.Hint

end
