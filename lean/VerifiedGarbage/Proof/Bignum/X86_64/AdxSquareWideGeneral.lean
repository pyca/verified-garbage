import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow

/-! Long carry chains and exact tails for cross-product rows. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxSquare (RowInv)

theorem round16 (w : Nat) (hw : w < 2 ^ 64) :
    let q := BitVec.ofNat 64 w >>> 4
    let r := q + q + (q + q)
    r + r + (r + r) = BitVec.ofNat 64 (16 * (w / 16)) := by
  dsimp only
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem set16_ok {s : State} {w j : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hw : w < 2 ^ 64) (hj : j < 2 ^ 64) :
    WP isa (.block AdxSquareWide.limit16) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (16 * (w / 16)) ∧ t.zf = some (decide (j = 16 * (w / 16))) ∧
      t.mem = s.mem ∧ t.gpr .r14 = s.gpr .r14 ∧ Keep [.rbx, .r14] s t := by
  refine WP.mono (WP.keep [.rbx, .r14] (Q := fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (16 * (w / 16)) ∧ t.zf = some (decide (j = 16 * (w / 16))) ∧
      t.mem = s.mem ∧ t.gpr .r14 = s.gpr .r14) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold AdxSquareWide.limit16
  xrun [hbp, h14, round16 w hw]
  exact ofNat_sub_beq hj (by omega)

theorem set4_ok {s : State} {w j : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hw : w < 2 ^ 64) (hj : j < 2 ^ 64) :
    WP isa (.block AdxSquareWide.limit4) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (4 * (w / 4)) ∧ t.zf = some (decide (j = 4 * (w / 4))) ∧
      t.mem = s.mem ∧ t.gpr .r14 = s.gpr .r14 ∧ Keep [.rbx, .r14] s t := by
  refine WP.mono (WP.keep [.rbx, .r14] (Q := fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (4 * (w / 4)) ∧ t.zf = some (decide (j = 4 * (w / 4))) ∧
      t.mem = s.mem ∧ t.gpr .r14 = s.gpr .r14) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold AdxSquareWide.limit4
  xrun [hbp, h14, AdxSquare.round4 w hw]
  exact ofNat_sub_beq hj (by omega)

theorem set1_ok {s : State} {w j : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hw : w < 2 ^ 64) (hj : j < 2 ^ 64) :
    WP isa (.block AdxSquare.rowRemainder) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (w) ∧ t.zf = some (decide (j = w)) ∧
      t.mem = s.mem ∧ t.gpr .r14 = s.gpr .r14 ∧ Keep [.rbx, .r14] s t := by
  refine WP.mono (WP.keep [.rbx, .r14] (Q := fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (w) ∧ t.zf = some (decide (j = w)) ∧
      t.mem = s.mem ∧ t.gpr .r14 = s.gpr .r14) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold AdxSquare.rowRemainder
  xrun [hbp, h14]
  exact ofNat_sub_beq hj (by omega)

theorem RowInv.limit {s₀ s t : State} {B : Addr} {Z e eb j : Nat}
    (hi : RowInv s₀ B Z e eb j s) (hm : t.mem = s.mem)
    (h14 : t.gpr .r14 = s.gpr .r14) (hk : Keep [.rbx, .r14] s t) :
    RowInv s₀ B Z e eb j t :=
  ⟨hi.scr.congr hk.2.2, (hi.keep.trans hk).mono (by simp), h14.trans hi.r14,
    hm ▸ hi.out, by rw [hm, hk.gpr (by decide)]; exact hi.val⟩

theorem generalRow_ok {s : State} {B : Addr} {Z e eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) :
    WP isa AdxSquareWide.generalRow s fun t =>
      wv t.mem B e w + 2 ^ (64 * w) * (t.gpr .rcx).toNat =
        wv s.mem B e w + (s.gpr .rdx).toNat * wv s.mem B eb w ∧
      Outside B e (8 * w) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 w ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s t := by
  unfold AdxSquareWide.generalRow
  have init : WP isa (.block [.mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0)]) s fun t =>
      t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem ∧ Keep [.rcx, .r14] s t := by
    refine WP.mono (WP.keep [.rcx, .r14] (Q := fun t => t.gpr .rcx = 0 ∧
      t.gpr .r14 = 0 ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
    xrun
  refine WP.seq (WP.mono init fun u ⟨hcx, h14, hm, ku⟩ => ?_)
  have hu8 := (ku.gpr (by decide)).trans h8
  have hu9 := (ku.gpr (by decide)).trans h9
  have I0 : RowInv u B Z e eb 0 u :=
    ⟨hs.congr ku.2.2, Keep.refl _ _, h14, Outside.refl _ _ _ _, by simp [wv]⟩
  have bp1 : u.gpr .rbp = BitVec.ofNat 64 w :=
    (I0.keep.gpr (by decide)).trans ((ku.gpr (by decide)).trans hbp)
  refine WP.seq (WP.mono (set16_ok bp1 I0.r14 (by omega) (by omega))
    fun a1 ⟨bx1, z1, m1, r1, k1⟩ => ?_)
  have J1 := RowInv.limit I0 m1 r1 k1
  have phase1 : WP isa (.ite .ne (.loop (.block AdxSquareWide.block) .ne) (.block [])) a1
      (RowInv u B Z e eb (16 * (w / 16))) := by
    by_cases eq : 0 = 16 * (w / 16)
    · refine WP.ite false (by simp [eval, z1, eq]) (by simp) (fun _ => WP.block_nil ?_)
      exact eq ▸ J1
    · refine WP.ite true (by simp [eval, z1, eq]) (fun _ => ?_) (by simp)
      apply blocks_ok (a := 0) hu8 hu9 bx1 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      exact J1
  refine WP.seq (WP.mono phase1 fun u1 I1 => ?_)
  have bp2 : u1.gpr .rbp = BitVec.ofNat 64 w :=
    (I1.keep.gpr (by decide)).trans ((ku.gpr (by decide)).trans hbp)
  refine WP.seq (WP.mono (set4_ok bp2 I1.r14 (by omega) (by omega))
    fun a2 ⟨bx2, z2, m2, r2, k2⟩ => ?_)
  have J2 := RowInv.limit I1 m2 r2 k2
  have phase2 : WP isa (.ite .ne (.loop (.block AdxSquare.mac4Store) .ne) (.block [])) a2
      (RowInv u B Z e eb (4 * (w / 4))) := by
    by_cases eq : 16 * (w / 16) = 4 * (w / 4)
    · refine WP.ite false (by simp [eval, z2, eq]) (by simp) (fun _ => WP.block_nil ?_)
      exact eq ▸ J2
    · refine WP.ite true (by simp [eval, z2, eq]) (fun _ => ?_) (by simp)
      apply AdxSquare.blocks_ok (a := 4 * (w / 16)) hu8 hu9 bx2 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      simpa only [← Nat.mul_assoc, Nat.reduceMul] using J2
  refine WP.seq (WP.mono phase2 fun u2 I2 => ?_)
  have bp3 : u2.gpr .rbp = BitVec.ofNat 64 w :=
    (I2.keep.gpr (by decide)).trans ((ku.gpr (by decide)).trans hbp)
  refine WP.seq (WP.mono (set1_ok bp3 I2.r14 (by omega) (by omega))
    fun a3 ⟨bx3, z3, m3, r3, k3⟩ => ?_)
  have J3 := RowInv.limit I2 m3 r3 k3
  have phase3 : WP isa (.ite .ne (.loop (.block AdxSquare.mac1Store) .ne) (.block [])) a3
      (RowInv u B Z e eb (w)) := by
    by_cases eq : 4 * (w / 4) = w
    · refine WP.ite false (by simp [eval, z3, eq]) (by simp) (fun _ => WP.block_nil ?_)
      exact eq ▸ J3
    · refine WP.ite true (by simp [eval, z3, eq]) (fun _ => ?_) (by simp)
      exact AdxSquare.remainder_ok hu8 hu9 bx3 (by omega) hw hZ hZb sb J3
  refine WP.mono phase3 fun t hi => ⟨?_, ?_, hi.r14, (ku.trans hi.keep).mono (by simp)⟩
  · have hv := hi.val
    rw [hm, ku.gpr (by decide), hcx] at hv
    simpa using hv
  · have ho := hi.out; rw [hm] at ho; exact ho
end VG.Proof.Bignum.X86_64.AdxSquareWide
