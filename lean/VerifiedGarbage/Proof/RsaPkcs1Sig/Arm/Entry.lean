module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Lay
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Wrap
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The ARMv7 PKCS #1 v1.5 functions: the entry

What a shared contract says of an entry state `s` gives the layout of the
state the body starts from (`entered F s`, after the push and the
allocation): `ok_entered`, for the layout `layOf F A argv ro rw s` whose
frame's base is `sp - 56 - F`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm VG.Proof.Bignum.Arm

/-- The layout of an entry state's body. -/
def layOf (F A : Nat) (argv : List (BitVec 32)) (ro rw : List Region) (s : State) (C : Nat := 56) : Lay where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 F
  F := F
  A := A
  argv := argv
  ro := ro
  rw := rw
  C := C

/-- The register argument `j`. -/
def regArg : Nat → Reg
  | 0 => .r0 | 1 => .r1 | 2 => .r2 | _ => .r3

section

variable {F A C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

theorem layOf_B_toNat (hsp : 56 + F ≤ s.sp.toNat) :
    (layOf F A argv ro rw s C).B.toNat = s.sp.toNat - 56 - F := by
  simp only [layOf]
  rw [FrameStack.sub_toNat' (by rw [FrameStack.sub_toNat' (by omega)]; omega),
    FrameStack.sub_toNat' (by omega)]

theorem layOf_fr (hsp : 56 + F ≤ s.sp.toNat) (d : Nat) :
    (layOf F A argv ro rw s C).fr d = State.addr s.sp - BitVec.ofNat 64 (56 + F) + BitVec.ofNat 64 d := by
  simp only [Lay.fr, Lay.Q, layOf]
  rw [FrameStack.addr_sub' (by rw [FrameStack.sub_toNat' (by omega)]; omega),
    FrameStack.addr_sub' (by omega), BitVec.sub_sub, BitVec.ofNat_add]

theorem layOf_Q (hsp : 56 + F ≤ s.sp.toNat) :
    (layOf F A argv ro rw s C).Q = State.addr s.sp - BitVec.ofNat 64 (56 + F) := by
  have := layOf_fr (A := A) (C := C) (argv := argv) (ro := ro) (rw := rw) hsp 0
  simpa only [Lay.fr, BitVec.add_zero] using this

theorem layOf_STK (hsp : 56 + F ≤ s.sp.toNat) :
    (layOf F A argv ro rw s C).STK = ⟨State.addr s.sp - BitVec.ofNat 64 (56 + F + C), 56 + F + C⟩ := by
  show (⟨(layOf F A argv ro rw s C).Q - BitVec.ofNat 64 C, C + F + 56⟩ : Region) = _
  rw [layOf_Q hsp, BitVec.sub_sub, ← BitVec.ofNat_add, show C + F + 56 = 56 + F + C by omega]

theorem layOf_down (hsp : 56 + F ≤ s.sp.toNat) {a : Nat} (ha : a ≤ 56 + F) :
    (layOf F A argv ro rw s C).fr (56 + F - a) = State.addr s.sp - BitVec.ofNat 64 a := by
  rw [layOf_fr hsp]
  exact (Offset.sub_ofNat_eq _ ha).symm

theorem layOf_up (hsp : 56 + F ≤ s.sp.toNat) (i : Nat) :
    (layOf F A argv ro rw s C).fr (56 + F + i) = State.addr s.sp + BitVec.ofNat 64 i := by
  rw [layOf_fr hsp, BitVec.ofNat_add (56 + F), ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem layOf_ARGS (hsp : 56 + F ≤ s.sp.toNat) :
    (layOf F A argv ro rw s C).ARGS = ⟨stackArgAddr s 0, A⟩ := by
  show (⟨(layOf F A argv ro rw s C).fr (F + 56), A⟩ : Region) = _
  rw [show F + 56 = 56 + F + 0 by omega, layOf_up hsp]
  simp [stackArgAddr]

theorem layOf_PUSH (hsp : 56 + F ≤ s.sp.toNat) :
    (layOf F A argv ro rw s C).PUSH = ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ := by
  show (⟨(layOf F A argv ro rw s C).fr F, 56⟩ : Region) = _
  have := layOf_down (A := A) (C := C) (argv := argv) (ro := ro) (rw := rw) hsp (a := 56) (by omega)
  rw [show 56 + F - 56 = F by omega] at this
  rw [this, FrameStack.addr_sub' (by omega)]

/-- The layout of the state the body starts from. -/
theorem ok_entered (hF : 8 ≤ F) (hA : A % 4 = 0) (hn : argv.length = 4 + A / 4)
    (hsp : 56 + F + C ≤ s.sp.toNat) (hsa : s.sp.toNat + A ≤ 2 ^ 32)
    (hrd : s.rd = ro ++ [⟨stackArgAddr s 0, A⟩]) (hwr : s.wr = rw)
    (hres : ∀ r ∈ ro ++ rw ++ [⟨stackArgAddr s 0, A⟩],
      Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 (56 + F + C), 56 + F + C⟩ r)
    (hwro : ∀ w ∈ rw, ∀ r ∈ ro ++ [⟨stackArgAddr s 0, A⟩], w.Disjoint r)
    (hwrw : rw.Pairwise Region.Disjoint)
    (hfits : ∀ r ∈ ro ++ rw, r.base.toNat + r.len ≤ 2 ^ 32)
    (hregs : ∀ j < 4, s.gpr (regArg j) = argv.getD j 0)
    (hstack : ∀ i < A / 4, stackArg s i = argv.getD (i + 4) 0) :
    (layOf F A argv ro rw s C).Ok (entered F s) := by
  have hB := layOf_B_toNat (A := A) (C := C) (argv := argv) (ro := ro) (rw := rw) (show 56 + F ≤ s.sp.toNat by omega)
  have hs : 56 + F ≤ s.sp.toNat := by omega
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered F s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 (56 + F + C), 56 + F + C⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  have saved := pc_push_saved s (by omega)
  have sp56 : State.addr (s.sp - 56) = State.addr s.sp - BitVec.ofNat 64 56 :=
    FrameStack.addr_sub' (x := s.sp) (k := 56) (by omega)
  refine
    { sp := rfl
      rd := by rw [entered_rd, hrd, layOf_ARGS hs]; rfl
      wr := by rw [entered_wr, hwr, ← layOf_PUSH (F := F) (A := A) (C := C) (argv := argv) (ro := ro) (rw := rw) hs]; rfl
      B56 := by show C ≤ _; rw [hB]; omega
      fit := by show _ + F + 56 + A ≤ _; rw [hB]; omega
      F8 := hF
      nargs := hn
      A4 := hA
      stk := fun r hr => by
        rw [layOf_STK hs]
        refine hres r ?_
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ (List.mem_append_left _ hr)
        · exact List.mem_append_left _ (List.mem_append_right _ hr)
      wro := fun w hw r hr => by
        have hr' : r ∈ ro ++ [⟨stackArgAddr s 0, A⟩] := by rw [← layOf_ARGS (C := C) (argv := argv) (rw := rw) hs]; exact hr
        exact hwro w hw r hr'
      wrw := hwrw
      fits := hfits
      args := ?_ }
  intro j hj
  rcases (by omega : j < 4 ∨ 4 ≤ j) with hj4 | hj4
  · have ea : Impl.RsaPkcs1Sig.Arm.argOff F j = 56 + F - (56 - 4 * j) := by
      simp only [Impl.RsaPkcs1Sig.Arm.argOff, hj4, ite_true]; omega
    have e : (layOf F A argv ro rw s C).argA j = State.addr (s.sp - 56) + BitVec.ofNat 64 (4 * j) := by
      show (layOf F A argv ro rw s C).fr (Impl.RsaPkcs1Sig.Arm.argOff F j) = _
      rw [ea, layOf_down hs (by omega), sp56, Offset.sub_ofNat_eq _ (show 56 - 4 * j ≤ 56 by omega)]
      congr 2; omega
    show _ = argv.getD j 0
    rw [e, entered_mem, ← hregs j hj4]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · exact saved (.r0, 0) (by simp [pcAllSaved])
    · exact saved (.r1, 4) (by simp [pcAllSaved])
    · exact saved (.r2, 8) (by simp [pcAllSaved])
    · exact saved (.r3, 12) (by simp [pcAllSaved])
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
    have hj' : i + 4 < argv.length := hj
    have hi : i < A / 4 := by omega
    have ea : Impl.RsaPkcs1Sig.Arm.argOff F (i + 4) = 56 + F + 4 * i := by
      simp only [Impl.RsaPkcs1Sig.Arm.argOff, show ¬ (i + 4 < 4) by omega, ite_false]; omega
    have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
    have ai : stackArgAddr s i = State.addr s.sp + BitVec.ofNat 64 (4 * i) := addr_add (by omega)
    have e : (layOf F A argv ro rw s C).argA (i + 4) = stackArgAddr s i := by
      show (layOf F A argv ro rw s C).fr (Impl.RsaPkcs1Sig.Arm.argOff F (i + 4)) = _
      rw [ea, layOf_up hs, ai]
    show _ = argv.getD (i + 4) 0
    rw [e, ← hstack i hi]
    show _ = s.mem.readW (stackArgAddr s i) 32
    rw [ai]
    refine hpush.readW (r := ⟨State.addr s.sp, A⟩) (Offset.contains_base _ (by omega) (by omega)) ?_
      (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [← a0]
    exact ((hres _ (by simp)).sub_left below).symm

/-- A buffer only read has the same bytes after the push. -/
theorem entered_ro (h : (layOf F A argv ro rw s C).Ok (entered F s)) (hsp : 56 + F ≤ s.sp.toNat) {R : Region}
    (hR : R ∈ ro) : Spec.Rsa.bytesAt (entered F s).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered F s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega)
  refine bytesAt_frame hpush (fun r hr => ?_) (by have := h.fits R (List.mem_append_left _ hR); omega)
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩
  rw [← layOf_PUSH (A := A) (C := C) (argv := argv) (ro := ro) (rw := rw) hsp]
  exact ((h.stk R (List.mem_append_left _ hR)).sub_left (Lay.sub_stk (Nat.le_refl _))).symm

/-- The push's region is the layout's. -/
theorem pushRegion_eq (hsp : 56 + F ≤ s.sp.toNat) : pushRegion s = (layOf F A argv ro rw s C).PUSH := by
  rw [layOf_PUSH hsp]

end

end VG.Proof.RsaPkcs1Sig.Arm
