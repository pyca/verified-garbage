module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Calls
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop

/-!
# ML-KEM on PPC64LE: copying bytes and zeroing a polynomial

As on 32-bit ARM (`Proof/MlKem/Arm/Loops.lean`): `copy` copies bytes one at
a time (`copyL`: the destination holds the source's bytes, and nothing else
changes), and `zeroPoly` stores zero to every coefficient (`zeroPoly_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem setWidth_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt this]

/-! ## `copy` -/

section
variable {s : State} {x y c : BitVec 64}

theorem copyBody_ok (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h5 : s.gpr .r5 = c)
    (ir : InRegions (s.rd ++ s.wr) x 1) (ow : InRegions s.wr y 1) :
    WP isa (.block copyBody) s fun s' =>
      s'.gpr .r3 = x + BitVec.ofNat 64 1 ∧ s'.gpr .r4 = y + BitVec.ofNat 64 1 ∧
      s'.gpr .r5 = c - BitVec.ofNat 64 1 ∧ s'.mem = s.mem.writeW y (s.mem x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  prun [copyBody, exec_lbz, exec_stb, Sample.read_one, setWidth_byte, h3, h4, h5, ir, ow]
  and_intros <;> first | exact trivial | rfl | pres_tac

end

/-- After copying `k` bytes of `len` from `S` to `D`. -/
structure CopyInv (S D : Addr) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = S + BitVec.ofNat 64 (1 * k)
  r4 : s.gpr .r4 = D + BitVec.ofNat 64 (1 * k)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (len - k)
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨D, len⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (D + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)

theorem copy_step {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : Covers [⟨S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨D, len⟩] s₀.wr)
    {k : Nat} (hk : k < len) {s : State} (h : CopyInv S D len s₀ k s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv S D len s₀ (k + 1) s' ∧ (s'.gpr .r5 != 0) = decide (k + 1 ≠ len) := by
  have cS : (⟨S, len⟩ : Region).Contains (S + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  have cD : (⟨D, len⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  have h3 := h.r3; have h4 := h.r4
  rw [Nat.one_mul] at h3 h4
  refine WP.mono (copyBody_ok h3 h4 h.r5 (by rw [h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_singleton_self _, cS⟩)
    (by rw [h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cD⟩))
    fun s' ⟨r3, r4, r5, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r3]; simpa using ptr_succ S 1 k
  · rw [r4]; simpa using ptr_succ D 1 k
  · rw [r5]; exact count_sub hk
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cD
  · rw [m, byte_writeW8 _ _ (by omega) (by omega)]
    have hsrc : s.mem (S + BitVec.ofNat 64 k) = s₀.mem (S + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd _ cS
    by_cases e : t = k
    · subst e; rw [ite_eq_left rfl, hsrc]
    · rw [ite_eq_right e]; exact h.bytes t (by omega)
  · rw [r5, count_sub hk]; exact count_nz hk hlen

/-- `len` bytes copied from `S` to `D`, with the pointers and the count set
up in `r3`–`r5`. -/
theorem copy_loop {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64) (hl0 : 0 < len)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : Covers [⟨S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨D, len⟩] s₀.wr)
    (h3 : s₀.gpr .r3 = S) (h4 : s₀.gpr .r4 = D) (h5 : s₀.gpr .r5 = BitVec.ofNat 64 len) :
    WP isa (.loop (.block copyBody) (.nonzero .d .r5)) s₀ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨D, len⟩] s₀.mem s.mem ∧ bytesAt s.mem D len = bytesAt s₀.mem S len :=
  wp_loop_nz (CopyInv S D len s₀) hl0 (fun k hk s h => copy_step hlen hd cr cw hk h)
    (fun s h => ⟨h.cs, h.rd, h.wr, h.sp, h.frame, bytesAt_eq (bytesAt_length _ _ _) fun t ht => by
      rw [h.bytes t ht, bytesAt_getElem]⟩)
    ⟨by rw [h3]; simp, by rw [h4]; simp, by rw [h5]; simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩

theorem copy_setup {s : State} {sb db : Reg} {so dO len : Nat} (hsb : sb ∈ preserved)
    (hdb : db ∈ preserved) (hse : so < 32768) (hde : dO < 32768) (hle : len < 32768) :
    WP isa (.block [.addi .r3 sb so, .addi .r4 db dO, .li .r5 len]) s fun s' =>
      Only s s' ∧ s'.gpr .r3 = s.gpr sb + BitVec.ofNat 64 so ∧ s'.gpr .r4 = s.gpr db + BitVec.ofNat 64 dO ∧
      s'.gpr .r5 = BitVec.ofNat 64 len := by
  obtain ⟨m0, m3, -, -, -, -, -⟩ := pres_ne hsb
  obtain ⟨n0, n3, -, -, -, -, -⟩ := pres_ne hdb
  prun [hse, hde, hle, m0, n0, n3, Ne.symm n3]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

/-- `copy`: `len` bytes from offset `so` of buffer `i` (in `sb`) to offset
`dO` of buffer `j` (in `db`). -/
theorem copyL {L : Lay} {s : State} (hL : L.Ok) {sb db : Reg} {so dO len i j : Nat}
    (hsb : sb ∈ preserved) (hdb : db ∈ preserved)
    (gs : s.gpr sb = L.ptr i) (gd : s.gpr db = L.ptr j) (hse : so < 32768) (hde : dO < 32768)
    (hle : len < 32768) (hl0 : 0 < len) (hs : sepB L.sizes (i, so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i so) len := by
  refine WP.seq (WP.mono (copy_setup hsb hdb hse hde hle) fun s₁ ⟨o₁, g3, g4, g5⟩ => ?_)
  rw [gs] at g3; rw [gd] at g4
  refine WP.mono (copy_loop (by omega) hl0 (Lay.disj hL hs)
    (by rw [o₁.rd, o₁.wr]; exact Lay.covers ri (sepB_bounds hs).2)
    (by rw [o₁.wr]; exact Lay.covers wj (sepB_bounds (sepB_symm hs)).2) g3 g4 g5)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨(o₁.kept _).trans ⟨cs, sp, rd, wr, fr⟩, ?_⟩
  rw [o₁.mem] at hb; exact hb

/-! ## `zeroPoly` -/

section
variable {s : State} {x c : BitVec 64}

theorem zeroBody_ok (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = 0) (h5 : s.gpr .r5 = c)
    (ow : InRegions s.wr x 4) :
    WP isa (.block zeroBody) s fun s' =>
      s'.gpr .r3 = x + BitVec.ofNat 64 4 ∧ s'.gpr .r4 = 0 ∧ s'.gpr .r5 = c - BitVec.ofNat 64 1 ∧
      s'.mem = s.mem.writeW x (0 : BitVec 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  prun [zeroBody, exec_store_w, h3, h4, h5, ow]
  and_intros <;> first | exact trivial | rfl | pres_tac

end

/-- After zeroing `k` coefficients of the polynomial at `P`. -/
structure ZeroInv (P : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = P + BitVec.ofNat 64 (4 * k)
  r4 : s.gpr .r4 = 0
  r5 : s.gpr .r5 = BitVec.ofNat 64 (256 - k)
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion P] s₀.mem s.mem
  zero : ∀ t < 256, coeffAt s.mem P t = if t < k then 0 else coeffAt s₀.mem P t

theorem zero_step {P : Addr} {s₀ : State} (cw : Covers [polyRegion P] s₀.wr) {k : Nat} (hk : k < 256) {s : State}
    (h : ZeroInv P s₀ k s) :
    WP isa (.block zeroBody) s fun s' => ZeroInv P s₀ (k + 1) s' ∧ (s'.gpr .r5 != 0) = decide (k + 1 ≠ 256) := by
  have cP : (polyRegion P).Contains (coeffAddr P k) 4 :=
    coeff_contains _ (by rw [VG.Proof.MlKem.n_eq]; exact hk)
  refine WP.mono (zeroBody_ok h.r3 h.r4 h.r5 (by rw [h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩))
    fun s' ⟨r3, r4, r5, m, rd, wr, sp, cs⟩ => ⟨⟨?_, r4, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 4 k
  · rw [r5]; exact count_sub hk
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m]; exact coeff_one hk h.zero rfl
  · rw [r5, count_sub hk]; exact count_nz hk (by decide)

theorem zeroPoly_ok {L : Lay} {s : State} (hc : Ctx L s) {off : Nat} (hoff : off + 1024 ≤ 32768) :
    WP isa (zeroPoly off) s fun s' => Kept (L.RL [(0, off, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 off) zero := by
  have hfin : ∀ s', ZeroInv (L.A 0 off) s 256 s' →
      Kept (L.RL [(0, off, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 off) zero := fun s' h => by
    refine ⟨⟨h.cs, h.sp, h.rd, h.wr, h.frame⟩, ?_⟩
    refine polyIs_of_coeffAt fun t ht => ?_
    rw [h.zero t (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht),
      ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht), zero,
      getElem!_pos (Vector.replicate n (0 : Zq)) t ht, Vector.getElem_replicate]
    rfl
  have ho : off < 32768 := by omega
  have e31 := hc.r31
  refine WP.seq ?_
  prun [ho, e31]
  refine wp_loop_nz (ZeroInv (L.A 0 off) s) (N := 256) (by decide)
    (fun k hk s h => zero_step (hc.cs hoff) hk h) hfin ?_
  refine ⟨by simp [State.write], rfl, rfl, by pres_tac, rfl, rfl, rfl, Frame.refl _ _, fun t _ => rfl⟩

end VG.Proof.MlKem.PPC64LE
