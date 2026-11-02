module
public import VerifiedGarbage.Proof.Rsa.Arm.RvBase
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords

/-! # `vg_rsa_recover_primes` on ARMv7: Montgomery multiplication's working space

Its base is `M0`, `256` bytes before the key array `mBase`, so that its array
`j` is the key array `mBase + j` (its stride, `8 (w6 + 2)`, is that of the key
working space with `w = 2 w6 + 2`), and its header lies in the key arrays
16–19. `MR P s`: it is ready for a multiplication but for `r0`
(`ArithmeticReady`, `MR.ready`); steps that write neither the key arrays
16–20 nor frame word 0 keep it (`MR.of_keep`). A number of the key working
space below `2^(64 w6)` is Montgomery multiplication's number of the same
array (`numAt_eq`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps)

/-- Ready for a multiplication, but for `r0`. -/
structure MR (P : RP) (s : State) : Prop where
  workspace : Workspace s P.M0 (8 * P.lenM)
  layout : Layout s.mem (State.addr P.M0) P.lenM
  width : wOf s.mem (State.addr P.M0) = P.w6
  inverse : ((word s.mem (State.addr P.M0) (arrAt P.w6 0)).toNat *
    (wordAt s.mem (State.addr P.M0) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  modulus : 1 < numAt s.mem (State.addr P.M0) P.w6 0
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr P.M0, 8 * P.lenM⟩
  saved : s.mem.readW (State.addr s.sp) 32 = P.M0

theorem MR.ready {P : RP} {s : State} (h : MR P s) (ptr : s.gpr .r0 = P.M0) :
    ArithmeticReady P.M0 P.lenM P.w6 s :=
  ⟨h.workspace, h.layout, h.width, ptr, h.inverse, h.modulus, h.stackRead, h.stackSep, h.saved⟩

theorem ArithmeticReady.mr {P : RP} {s : State} (h : ArithmeticReady P.M0 P.lenM P.w6 s) : MR P s :=
  ⟨h.workspace, h.layout, h.width, h.inverse, h.modulus, h.stackRead, h.stackSep, h.saved⟩

/-- The bytes of the header and of array 0. -/
abbrev mHd (P : RP) : Nat := arrAt P.w6 1

/-- The same header and array 0, and the same frame word 0. -/
theorem MR.of_read {P : RP} {s t : State} (h : MR P s)
    (e : ∀ d n, d + n ≤ mHd P → t.mem.read (off (State.addr P.M0) d) n = s.mem.read (off (State.addr P.M0) d) n)
    (sv : t.mem.readW (State.addr t.sp) 32 = s.mem.readW (State.addr s.sp) 32)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MR P t := by
  have hw : 2 ≤ P.w6 := h.width ▸ h.layout.1
  have hb : 128 ≤ mHd P := by simp only [mHd, arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  have ew : ∀ d, d + 8 ≤ mHd P → t.mem.readW (off (State.addr P.M0) d) 64 = s.mem.readW (off (State.addr P.M0) d) 64 :=
    fun d hd => by simp only [Mem.readW, e d 8 hd]
  have width : wOf t.mem (State.addr P.M0) = wOf s.mem (State.addr P.M0) :=
    congrArg BitVec.toNat (ew 48 (by omega))
  refine ⟨h.workspace.congr wr, ?_, width.trans h.width, ?_, ?_, ?_, ?_, ?_⟩
  · have layout := h.layout
    unfold Layout at layout ⊢
    rw [width]
    refine ⟨layout.1, layout.2.1, layout.2.2.1, fun j hj => ?_⟩
    unfold wordAt
    rw [ew _ (by simp only [Proof.Rsa.Mont.arrWord]; omega)]
    exact layout.2.2.2 j hj
  · change ((t.mem.readW (off (State.addr P.M0) (arrAt P.w6 0)) 64).toNat *
      (t.mem.readW (off (State.addr P.M0) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [ew _ (by simp only [mHd, arrAt]; omega), ew 56 (by omega)]
    exact h.inverse
  · unfold numAt
    rw [show State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w6 0) = off (State.addr P.M0) (arrAt P.w6 0) from rfl,
      e _ _ (by simp only [mHd, arrAt]; omega)]
    exact h.modulus
  · rw [rd, wr, sp]; exact h.stackRead
  · rw [sp]; exact h.stackSep
  · rw [sv]; exact h.saved

/-! ## The arrays -/

theorem M0_addr {P : RP} (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) :
    State.addr P.M0 = off (State.addr P.B) P.oM :=
  addr_add (by
    have := sz.hdrM; have := sz.endM; have := sz.fits; have := arr_mono (w := P.w) (show mBase + 8 ≤ nArr by decide)
    have : 0 < P.lenM := by simp only [RP.lenM]; omega
    omega)

/-- Montgomery multiplication's offsets are those of the key working space, past `oM`. -/
theorem oM_arrAt {P : RP} (sz : Sizes P) (j : Nat) : P.oM + arrAt P.w6 j = arr P.w (mBase + j) := by
  have := sz.hdrM; have sw := sz.sw
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, RP.oM, arr, Nat.add_mul] at *
  rw [← sw]; omega

theorem M0_off {P : RP} (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) (d : Nat) :
    off (State.addr P.M0) d = off (State.addr P.B) (P.oM + d) := by
  rw [M0_addr sz hf]; exact Offset.add_add _ _ _

/-- Montgomery multiplication's number of array `j` is the low `2 w6` words of the key array. -/
theorem numAt_val32 {P : RP} (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) (m : Mem) (j : Nat) :
    numAt m (State.addr P.M0) P.w6 j = val32 m (State.addr P.B) (arr P.w (mBase + j)) (2 * P.w6) := by
  unfold numAt
  rw [show State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w6 j) = off (State.addr P.M0) (arrAt P.w6 j) from rfl,
    M0_off sz hf, oM_arrAt sz, show 8 * P.w6 = 4 * (2 * P.w6) by omega, read_eq_val32]

/-- The key number, of `2 w6 + 2` words, is the low `2 w6` and the top two. -/
theorem num_split (m : Mem) (B : BitVec 32) {w6 j : Nat} :
    num m B (2 * w6 + 2) j = val32 m (State.addr B) (arr (2 * w6 + 2) j) (2 * w6) +
      2 ^ (32 * (2 * w6)) * val32 m (State.addr B) (arr (2 * w6 + 2) j + 4 * (2 * w6)) 2 := by
  simp only [num]; rw [val32_append]

theorem numAt_eq {P : RP} (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) {m : Mem} {j : Nat}
    (h : num m P.B P.w (mBase + j) < 2 ^ (64 * P.w6)) :
    numAt m (State.addr P.M0) P.w6 j = num m P.B P.w (mBase + j) := by
  rw [numAt_val32 sz hf]
  have e := num_split (w6 := P.w6) (j := mBase + j) m P.B
  rw [show 2 * P.w6 + 2 = P.w from rfl] at e
  rw [e] at h ⊢
  have : 2 ^ (32 * (2 * P.w6)) = 2 ^ (64 * P.w6) := by rw [← Nat.mul_assoc]
  rw [this] at h ⊢
  have : val32 m (State.addr P.B) (arr P.w (mBase + j) + 4 * (2 * P.w6)) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m (State.addr P.B) (arr P.w (mBase + j) + 4 * (2 * P.w6)) 2) with z | z
    · exact z
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * P.w6)) z; omega
  rw [this, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Rsa.Arm.Recover
