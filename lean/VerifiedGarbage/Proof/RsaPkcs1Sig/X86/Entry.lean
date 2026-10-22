module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Lay
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Wrap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt

/-!
# The x86 RSA padding functions: the layout on entry

`layOf F argv ro rw s C`: the layout of a function whose entry state is
`s`, with a frame of `F` bytes, the arguments `argv`, the buffers `ro` it
only reads and `rw` it writes, and `C` bytes below the frame for its calls.
`ok_entered`: from what the calling convention and a contract give on entry,
the state the body starts in (`entered F s`, `Proof/RsaPkcs1Sig/X86/Wrap.lean`)
has that layout. Every address of the layout is `esp`, on entry, plus or
minus an offset, without wrapping around (`fr_toNat`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86

/-- The layout of a function entered in `s`. -/
def layOf (F : Nat) (argv : List (BitVec 32)) (ro rw : List Region) (s : State) (C : Nat) : Lay where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 F
  F := F
  argv := argv
  ro := ro
  rw := rw
  C := C

section
variable {F C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

theorem layOf_B_toNat (hsp : 16 + F ≤ (s.gpr .esp).toNat) :
    (layOf F argv ro rw s C).B.toNat = (s.gpr .esp).toNat - 16 - F := by
  simp only [layOf]
  rw [sub_toNat (by rw [sub_toNat (by omega)]; omega), sub_toNat (by omega)]

theorem fr_toNat' (hsp : 16 + F ≤ (s.gpr .esp).toNat) {d : Nat} (hd : (s.gpr .esp).toNat + d < 2 ^ 32 + 16 + F) :
    ((layOf F argv ro rw s C).fr d).toNat = (s.gpr .esp).toNat - 16 - F + d := by
  have hB := layOf_B_toNat (argv := argv) (ro := ro) (rw := rw) (C := C) hsp
  simp only [Lay.fr, Lay.Q]
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hB,
    Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat - 16 - F) (by have := (s.gpr .esp).isLt; omega),
    Nat.mod_eq_of_lt (a := d) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem esp64_toNat (s : State) : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)

theorem ok_entered {S : Nat} (hS : S = C + 16 + F) (hF : FrameOk F) (hsp : S ≤ (s.gpr .esp).toNat)
    (hn : 0 < argv.length)
    (hfit : (s.gpr .esp).toNat + 4 + 4 * argv.length ≤ 2 ^ 32)
    (hrd : s.rd = ro) (hwr : s.wr = rw ++ [⟨argAddr s 0, 4 * argv.length⟩])
    (hstk : ∀ r ∈ ro ++ rw,
      (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 S, S⟩ : Region).Disjoint r)
    (hret : ∀ r ∈ rw, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (hwro : ∀ w ∈ rw, ∀ r ∈ ro ++ [⟨argAddr s 0, 4 * argv.length⟩], w.Disjoint r)
    (hwrw : rw.Pairwise Region.Disjoint) (hfits : ∀ r ∈ ro ++ rw, r.base.toNat + r.len ≤ 2 ^ 32)
    (hargs : ∀ j < argv.length, arg s j = argv.getD j 0) :
    (layOf F argv ro rw s C).Ok (entered F s) := by
  subst hS
  have hE := (s.gpr .esp).isLt
  have h16 : 16 + F ≤ (s.gpr .esp).toNat := by omega
  have hB := layOf_B_toNat (argv := argv) (ro := ro) (rw := rw) (C := C) h16
  have e64 := esp64_toNat s
  -- Every address of the layout is `esp` on entry plus or minus an offset.
  have hQ : (layOf F argv ro rw s C).Q = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (16 + F) := by
    simp only [Lay.Q, layOf]
    rw [Taint.sub_setWidth (by rw [sub_toNat (by omega)]; omega), Taint.sub_setWidth (by omega),
      BitVec.sub_sub, BitVec.ofNat_add]
  have hfr : ∀ d, (layOf F argv ro rw s C).fr d =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (16 + F) + BitVec.ofNat 64 d := by
    intro d; simp only [Lay.fr]; rw [hQ]
  have up : ∀ d, d ≤ 4 + 4 * argv.length →
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (16 + F) + BitVec.ofNat 64 (16 + F + d) =
        (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := by
    intro d _
    rw [show BitVec.ofNat 64 (16 + F + d) = BitVec.ofNat 64 (16 + F) + BitVec.ofNat 64 d from
      BitVec.ofNat_add _ _, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have argAddrJ : ∀ j < argv.length, argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) := by
    intro j hj
    apply BitVec.eq_of_toNat_eq
    rw [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, e64, Nat.mod_eq_of_lt (a := 4 + 4 * j) (by omega),
      Nat.mod_eq_of_lt (a := 4 + 4 * j) (by omega),
      Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat + (4 + 4 * j)) (by omega), Nat.mod_eq_of_lt (by omega)]
  have argA : ∀ j < argv.length, (layOf F argv ro rw s C).argA j = argAddr s j := by
    intro j hj
    simp only [Lay.argA, Impl.RsaPkcs1Sig.X86.argOff]
    rw [hfr]
    simp only [layOf]
    rw [show F + 20 + 4 * j = 16 + F + (4 + 4 * j) by omega, up _ (by omega), argAddrJ j hj]
  have argAddr0 : argAddr s 0 = (layOf F argv ro rw s C).fr (F + 20) := by
    have := argA 0 hn
    simp only [Lay.argA, Impl.RsaPkcs1Sig.X86.argOff, Nat.mul_zero, Nat.add_zero] at this
    exact this.symm
  refine
    { sp := ?_, rd := ?_, wr := ?_, BC := ?_, fit := ?_, stk := ?_, ret := ?_, wro := ?_,
      wrw := hwrw, fits := hfits, args := ?_ }
  · rw [entered_esp]; rfl
  · rw [entered_rd, hrd]; rfl
  · rw [entered_wr, hwr, argAddr0]
    have hsave : (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 = (layOf F argv ro rw s C).fr F := by
      rw [hfr, Taint.sub_setWidth (by omega)]
      try simp only [layOf]
      rw [show BitVec.ofNat 64 (16 + F) = BitVec.ofNat 64 16 + BitVec.ofNat 64 F from BitVec.ofNat_add _ _,
        ← BitVec.sub_sub, BitVec.sub_add_cancel]
    rw [hsave]
    rfl
  · show C ≤ (layOf F argv ro rw s C).B.toNat
    rw [hB]; omega
  · show (layOf F argv ro rw s C).B.toNat + F + 20 + 4 * argv.length ≤ 2 ^ 32
    rw [hB]; omega
  · intro r hr
    have e : (layOf F argv ro rw s C).STK =
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (C + 16 + F), C + 16 + F⟩ := by
      simp only [Lay.STK]
      rw [hQ, BitVec.sub_sub, ← BitVec.ofNat_add]
      simp only [layOf, Region.mk.injEq]
      exact ⟨by rw [show 16 + F + C = C + 16 + F by omega], by omega⟩
    rw [e]; exact hstk r hr
  · intro r hr
    have e : (layOf F argv ro rw s C).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
      simp only [Lay.RET]
      rw [hfr]
      simp only [layOf]
      rw [show F + 16 = 16 + F + 0 by omega, up 0 (by omega), BitVec.add_zero]
    rw [e]; exact hret r hr
  · intro w hw r hr
    refine hwro w hw r ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · simp only [List.mem_singleton] at hr; subst hr
      refine List.mem_append_right _ ?_
      simp only [Lay.ARGS, Lay.A, List.mem_singleton]
      rw [argAddr0]; rfl
  · intro j hj
    replace hj : j < argv.length := hj
    have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
        (pushed Impl.RsaPkcs1Sig.X86.savedRegs s).mem :=
      pushed_frame (by decide) (by simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega)
    rw [argA j hj, entered_mem]
    refine (hpush.readW (r := ⟨argAddr s j, 4⟩) (Region.contains_self _ _) ?_ (by decide)).trans (hargs j hj)
    intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega), argAddrJ j hj]
    exact Offset.disjoint_below _ (by omega)

end

section
variable {F C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

/-- The push's bytes are the layout's saved registers. -/
theorem save_eq (hsp : 16 + F ≤ (s.gpr .esp).toNat) : saveRegion s = (layOf F argv ro rw s C).SAVE := by
  have := (s.gpr .esp).isLt
  have h := fr_toNat' (argv := argv) (ro := ro) (rw := rw) (C := C) hsp (d := F) (by omega)
  simp only [saveRegion, Lay.SAVE]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show (layOf F argv ro rw s C).F = F from rfl, h, BitVec.toNat_setWidth, sub_toNat (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The return address is the layout's. -/
theorem ret_eq (hsp : 16 + F ≤ (s.gpr .esp).toNat) : retRegion s = (layOf F argv ro rw s C).RET := by
  have := (s.gpr .esp).isLt
  have h := fr_toNat' (argv := argv) (ro := ro) (rw := rw) (C := C) hsp (d := F + 16) (by omega)
  simp only [retRegion, Lay.RET]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show (layOf F argv ro rw s C).F = F from rfl, h, esp64_toNat]
  omega

/-- A buffer only read has the same bytes on entry to the body. -/
theorem entered_ro (hsp : 16 + F ≤ (s.gpr .esp).toNat) (h : (layOf F argv ro rw s C).Ok (entered F s))
    {R : Region} (hR : R ∈ ro) :
    Spec.Rsa.bytesAt (entered F s).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have hf : Frame [saveRegion s] s.mem (entered F s).mem := by
    rw [entered_mem]
    have := pushed_frame (s := s) pushRegs_noSp
      (by simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega)
    simpa [Impl.RsaPkcs1Sig.X86.savedRegs, below] using this
  refine Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => ?_) (by have := h.fits R (List.mem_append_left _ hR); omega)
  simp only [List.mem_singleton] at hr; subst hr
  rw [save_eq (argv := argv) (ro := ro) (rw := rw) (C := C) hsp]
  exact ((h.stk R (List.mem_append_left _ hR)).sub_left (Lay.sub_stk (by simp only [layOf]; omega))).symm

end

end VG.Proof.RsaPkcs1Sig.X86
