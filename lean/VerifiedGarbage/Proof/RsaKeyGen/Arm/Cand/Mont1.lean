module
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Vals
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
import VerifiedGarbage.Proof.Rsa.Arm.RvMont4

/-! # A candidate on ARMv7: Montgomery multiplication's working space

Its base is `M0`, 256 bytes before the key array `mBase`: its array `j` is
the key array `mBase + j` (`oM_arrAt`), and its header lies in the key arrays
15–20. `MS P σ s`: it is ready for a multiplication modulo `c` but for `r0`,
with `R² mod c` in its array 4 and the stride in its header word 28.
Steps of the key working space that write none of the key arrays 15–21
and 25 keep it (`MS.of_keep`); steps within its eight arrays write the key
arrays 15–28 (`keep_of_frameM`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- `R² mod c`. -/
abbrev r2v (P : CP) (σ : State) : Nat := 2 ^ (128 * P.w) % cv P σ

/-- Ready for a multiplication modulo `c`, but for `r0` and the stride. -/
structure MSp (P : CP) (σ : State) (s : State) : Prop where
  workspace : Workspace s P.M0 (8 * P.lenM)
  layout : Layout s.mem (State.addr P.M0) P.lenM
  width : wOf s.mem (State.addr P.M0) = P.w
  inverse : ((word s.mem (State.addr P.M0) (arrAt P.w 0)).toNat *
    (wordAt s.mem (State.addr P.M0) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  n0 : numAt s.mem (State.addr P.M0) P.w 0 = cv P σ
  r2 : numAt s.mem (State.addr P.M0) P.w 4 = r2v P σ
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr P.M0, 8 * P.lenM⟩
  saved : s.mem.readW (State.addr s.sp) 32 = P.M0

/-- Ready for a multiplication modulo `c`, but for `r0`, with the stride. -/
structure MS (P : CP) (σ : State) (s : State) : Prop extends MSp P σ s where
  stride : wordAt s.mem (State.addr P.M0) 28 = BitVec.ofNat 64 (8 * (P.w + 2))

section
variable {P : CP} {σ : State}

theorem In.oM_le (pre : In P σ) : arr P.W 15 ≤ P.oM := by
  have := pre.oM_eq; have := pre.W_eq; have := pre.w4; simp only [arr, S, hdr, mBase] at *; omega_arith

theorem In.S_eq (pre : In P σ) : S P.W = 8 * (P.w + 2) := by have := pre.W_eq; simp only [S]; omega_arith

theorem In.M0_toNat (pre : In P σ) : P.M0.toNat = P.B.toNat + P.oM := by
  have := pre.fits; have := pre.fS; have := pre.oM_eq
  have := arr_mono (w := P.W) (show mBase ≤ nArr by decide)
  simp only [CP.M0, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := P.oM) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem In.M0_addr (pre : In P σ) : State.addr P.M0 = off (State.addr P.B) P.oM := by
  have := pre.fits; have := pre.fS; have := pre.oM_eq
  have := arr_mono (w := P.W) (show mBase ≤ nArr by decide)
  exact addr_add (by omega_arith)

/-- Montgomery multiplication's offsets are those of the key working space, past `oM`. -/
theorem In.oM_arrAt (pre : In P σ) (j : Nat) : P.oM + arrAt P.w j = arr P.W (mBase + j) := by
  have e := pre.oM_eq
  have s := pre.S_eq
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, arr] at *
  rw [s] at e ⊢
  rw [Nat.add_mul]
  omega_arith

theorem In.M0_off (pre : In P σ) (d : Nat) : off (State.addr P.M0) d = off (State.addr P.B) (P.oM + d) := by
  rw [pre.M0_addr]; exact Offset.add_add _ _ _

theorem In.numAt_val32 (pre : In P σ) (m : Mem) (j : Nat) :
    numAt m (State.addr P.M0) P.w j = val32 m (State.addr P.B) (arr P.W (mBase + j)) (P.W - 2) := by
  unfold numAt
  rw [show State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w j) = off (State.addr P.M0) (arrAt P.w j) from rfl,
    pre.M0_off, pre.oM_arrAt, show 8 * P.w = 4 * (P.W - 2) by have := pre.W_eq; omega_arith, read_eq_val32]

/-- A key number below `2^(64 w)` is Montgomery multiplication's number of the same array. -/
theorem In.numAt_eq (pre : In P σ) {m : Mem} {j : Nat} (h : num m P.B P.W (mBase + j) < 2 ^ (64 * P.w)) :
    numAt m (State.addr P.M0) P.w j = num m P.B P.W (mBase + j) := by
  rw [pre.numAt_val32]
  have hW := pre.W_eq
  have e := val32_append m (State.addr P.B) (arr P.W (mBase + j)) (P.W - 2) 2
  rw [show P.W - 2 + 2 = P.W by omega_arith] at e
  simp only [num] at h ⊢
  rw [e] at h ⊢
  have p : 2 ^ (32 * (P.W - 2)) = 2 ^ (64 * P.w) := by congr 1; omega_arith
  rw [p] at h ⊢
  have : val32 m (State.addr P.B) (arr P.W (mBase + j) + 4 * (P.W - 2)) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m (State.addr P.B) (arr P.W (mBase + j) + 4 * (P.W - 2)) 2) with z | z
    · exact z
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * P.w)) z; omega_arith
  rw [this, Nat.mul_zero, Nat.add_zero]

theorem In.rM_sub (pre : In P σ) : Region.Sub P.rM P.rS := by
  show Region.Sub ⟨State.addr P.M0, 8 * P.lenM⟩ ⟨State.addr P.B, P.Z⟩
  rw [pre.M0_addr]
  refine Offset.sub_base _ ?_
  rw [pre.endM]; exact Nat.le_trans (arr_mono (show mBase + 8 ≤ nArr by decide)) pre.fits

theorem In.rW0_rM (pre : In P σ) : P.rW0.Disjoint P.rM :=
  (pre.sF.symm.sub_left (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 84) (by decide) |>
    fun h => by simpa using h)).sub_right pre.rM_sub

theorem In.workspaceM (pre : In P σ) {s : State} (wr : s.wr = σ.wr) : Workspace s P.M0 (8 * P.lenM) := by
  refine ⟨?_, by rw [wr, pre.wr]; simp⟩
  rw [pre.M0_toNat, Nat.add_assoc, pre.endM]
  have := Nat.le_trans (arr_mono (w := P.W) (show mBase + 8 ≤ nArr by decide)) pre.fits
  have := pre.fS
  simp only [CP.Z] at *; omega_arith

/-! ## Frames -/

/-- Memory that changed within the first `n` bytes of Montgomery
multiplication's working space changed within the key arrays `15` to `15 + k − 1`. -/
theorem keep_of_frameN (pre : In P σ) {n k : Nat} (hn : P.oM + n ≤ arr P.W (15 + k)) (hk : 15 + k ≤ nArr)
    {m m' : Mem} (f : Frame [⟨State.addr P.M0, n⟩] m m') : Keep P.B P.W (List.range' 15 k) [] m m' := by
  have hM := pre.M0_addr
  have hfit := Nat.le_trans (arr_mono (w := P.W) hk) pre.fits
  have l := pre.oM_le
  have hlt : P.oM + n ≤ 2 ^ 64 := Nat.le_trans hn (Nat.le_trans hfit (Nat.le_trans pre.Z_le (by decide)))
  intro x hx
  refine f x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hc
  rw [hM] at hc
  have hc' : (x - (State.addr P.B + BitVec.ofNat 64 P.oM)).toNat < n := by
    simp only [off] at hc; omega_arith
  have hin := (Offset.lt_iff x (State.addr P.B) (d := P.oM) (n := n) hlt).mp hc'
  generalize hXe : (x - State.addr P.B).toNat = X at hin
  have hS : 0 < S P.W := by simp only [S]; omega_arith
  have hd := Nat.div_add_mod (X - hdr) (S P.W)
  have hr := Nat.mod_lt (X - hdr) hS
  generalize (X - hdr) / S P.W = q at hd
  generalize (X - hdr) % S P.W = r at hd hr
  have h15 : hdr + 15 * S P.W ≤ P.oM := l
  have hk' : P.oM + n ≤ hdr + (15 + k) * S P.W := hn
  have hq : X = hdr + q * S P.W + r := by rw [Nat.mul_comm] at hd; omega_arith
  have h1 : 15 * S P.W < (q + 1) * S P.W := by rw [Nat.add_mul]; omega_arith
  have h2 : q * S P.W < (15 + k) * S P.W := by omega_arith
  have qa := Nat.lt_of_mul_lt_mul_right h1
  have qk := Nat.lt_of_mul_lt_mul_right h2
  have := hx (arr P.W q, S P.W) (by
    simp only [ranges, List.mem_append, List.mem_map, List.mem_range'_1]
    exact .inl ⟨q, ⟨by omega_arith, by omega_arith⟩, rfl⟩)
  simp only [arr, ofs] at this
  rw [hXe] at this
  omega_arith

/-- Memory that changed within Montgomery multiplication's eight arrays changed
within the key arrays 15–28. -/
theorem keep_of_frameM (pre : In P σ) {m m' : Mem} (f : Frame [P.rM] m m') :
    Keep P.B P.W (List.range' 15 14) [] m m' :=
  keep_of_frameN pre (by rw [pre.endM]; exact Nat.le_refl _) (by decide) f

/-- Memory that changed within its header changed within the key arrays 15–20. -/
theorem keep_of_frameH (pre : In P σ) {m m' : Mem} (f : Frame [⟨State.addr P.M0, 256⟩] m m') :
    Keep P.B P.W (List.range' 15 6) [] m m' :=
  keep_of_frameN pre (by have := pre.oM_eq; exact Nat.le_of_eq this) (by decide) f

/-- Memory that changed at offsets of its first `n` bytes. -/
theorem frame_of_outs {rs : List (Nat × Nat)} {n : Nat} {m m' : Mem}
    (o : Outs (State.addr P.M0) rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ n) :
    Frame [⟨State.addr P.M0, n⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  refine o x fun r hr => .inr ?_
  have := hrs r hr
  simp only [ofs]; omega_arith

/-- A Montgomery multiplication writes, of the key arrays, only its own two
and its result's. -/
theorem keep_of_mont (pre : In P σ) {o : Nat} {m m' : Mem}
    (keeps : Keeps (State.addr P.M0) P.lenM P.w o m m') (frame : Frame [P.rM] m m') :
    Keep P.B P.W [mBase + 2, mBase + 3, mBase + o] [] m m' := by
  have hz := pre.fS
  have hfit := Nat.le_trans (arr_mono (w := P.W) (show mBase + 8 ≤ nArr by decide)) pre.fits
  have e := pre.endM
  intro x hx
  have hM := pre.M0_addr
  by_cases hin : P.oM ≤ ofs (State.addr P.B) x ∧ ofs (State.addr P.B) x < P.oM + 8 * P.lenM
  · obtain ⟨i, hi⟩ : ∃ i, ofs (State.addr P.B) x = P.oM + i := ⟨ofs (State.addr P.B) x - P.oM, by omega_arith⟩
    have ex : x = State.addr P.M0 + BitVec.ofNat 64 i := by
      rw [hM, Offset.add_add, ← hi]
      simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    rw [ex]
    refine keeps i (by omega_arith) fun j hj => ?_
    have hj' : (arr P.W (mBase + j), S P.W) ∈ ranges P.W [mBase + 2, mBase + 3, mBase + o] [] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false]
      rcases hj with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)
    have := hx _ hj'
    rw [← pre.oM_arrAt j] at this
    have : 8 * (P.w + 2) = S P.W := by have := pre.W_eq; simp only [S]; omega_arith
    dsimp only at *
    omega_arith
  · refine frame x fun r hr hc => hin ?_
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Region.Contains] at hc
    rw [hM] at hc
    have hlt : P.oM + 8 * P.lenM ≤ 2 ^ 64 :=
      Nat.le_trans (by rw [e]; exact hfit) (Nat.le_trans pre.Z_le (by decide))
    have hc' : (x - (State.addr P.B + BitVec.ofNat 64 P.oM)).toNat < 8 * P.lenM := by
      simp only [off] at hc; omega_arith
    exact (Offset.lt_iff x (State.addr P.B) (d := P.oM) (n := 8 * P.lenM) hlt).mp hc'

end

end VG.Proof.RsaKeyGen.Arm.Cand
