module

public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! A shared public-pointer copy loop for comb construction and selection. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

private theorem count_one {x : BitVec 32} {N i : Nat} (h : x.toNat = N-i) (hi : i < N) :
    (x-1#32).toNat = N-(i+1) ∧ (x-1#32 == 0) = decide (i+1 = N) := by
  have value : (x-1#32).toNat = N-(i+1) := by
    rw [BitVec.toNat_sub, h]
    change (2^32 - 1 + (N-i)) % 2^32 = _
    have := x.isLt
    omega
  refine ⟨value, ?_⟩
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro hz; have := congrArg BitVec.toNat hz; rw [value] at this; change N-(i+1) = 0 at this; omega
  · intro hiN; apply BitVec.eq_of_toNat_eq; rw [value]; change N-(i+1) = 0; omega

/-- Both copy directions use the same proof. Only public pointers advance;
source and destination must be separate. -/
theorem copyLoop_ok {s : State} {W : Addr} {size x y sd dd N : Nat} {src dst : Reg}
    (hw : Ws s W size) (hN : 0 < N)
    (hs : src ∈ [.ecx, .ebp]) (hd : dst ∈ [.ecx, .ebp])
    (hx : x+sd+4*N ≤ size) (hy : y+dd+4*N ≤ size)
    (sep : x+sd+4*N ≤ y+dd ∨ y+dd+4*N ≤ x+sd)
    (ps : PtrAt s W src x) (pd : PtrAt s W dst y)
    (count : (s.gpr .ebx).toNat = N) :
    WP isa (VG.Impl.Mont.X86.Comb.copyLoop (at_ src sd) (at_ dst dd)) s fun t =>
      Outside W (y+dd) (4*N) s.mem t.mem ∧
      val32 t.mem W (y+dd) N = val32 s.mem W (x+sd) N ∧
      Keeps [.eax, .ebx, .ecx, .ebp] s t := by
  have nw := hw.nowrap
  unfold VG.Impl.Mont.X86.Comb.copyLoop
  refine WP.mono (countLoop hN (fun i t =>
      Keeps [.eax, .ebx, .ecx, .ebp] s t ∧ PtrAt t W src (x+4*i) ∧ PtrAt t W dst (y+4*i) ∧
      (t.gpr .ebx).toNat = N-i ∧ Outside W (y+dd) (4*i) s.mem t.mem ∧
      val32 t.mem W (y+dd) i = val32 s.mem W (x+sd) i) ?_
    ⟨Keeps.refl _ _, by simpa using ps, by simpa using pd, by simpa using count,
      Outside.refl _ _ _ _, rfl⟩) fun t ⟨K, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro i t hi ⟨K, PS, PD, C, O, V⟩
  have ht := hw.of_keeps K
  have dst_eax : dst ≠ .eax := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> decide
  refine wp_movS (readSrc_ptr ht PS (d := sd) (by omega)) fun u U _ => ?_
  have hu := ht.of_keeps U.keeps
  have PD' : PtrAt u W dst (y+4*i) := by rw [PtrAt, U.other dst dst_eax]; exact PD
  refine wp_storeS (ea_ptr hu PD' (d := dd) (by omega))
    (ws_write hu (y := y+4*i+dd) (n := 4) (by omega)) fun v M => ?_
  refine wp_addS rfl fun v₁ A _ => wp_addS rfl fun v₂ B _ => wp_subZ rfl fun v₃ D Z => WP.block_nil ?_
  have C' : v₂.gpr .ebx = t.gpr .ebx := by
    rw [B.other _ (by decide), A.other _ (by decide), M.gpr, U.other _ (by decide)]
  obtain ⟨newCount, zero⟩ := count_one C hi
  have pointers : ∀ r ∈ [.ecx, .ebp], v₃.gpr r = t.gpr r + 4 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [D.other _ (by decide), B.other _ (by decide), A.gpr, M.gpr, U.other _ (by decide)]; rfl
    · rw [D.other _ (by decide), B.gpr, A.other _ (by decide), M.gpr, U.other _ (by decide)]; rfl
  have mem : v₃.mem = u.mem.writeW (off W (y+4*i+dd)) (u.gpr .eax) := by
    rw [D.mem, B.mem, A.mem, M.mem]
  refine ⟨⟨((((K.widen U.keeps).trans (M.keeps _)).widen A.keeps).widen B.keeps).widen D.keeps,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, pointers src hs]; exact ptr4 PS
  · rw [PtrAt, pointers dst hd]; exact ptr4 PD
  · rw [D.gpr, C']; exact newCount
  · rw [mem, U.mem]
    exact (O.mono (Nat.le_refl _) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [mem, show y+4*i+dd = y+dd+4*i by omega, val32_store nw (by omega), U.mem, V, U.gpr]
    rw [val32_succ]
    congr 1
    congr 1
    change w32 t.mem W (x+4*i+sd) = w32 s.mem W (x+sd+4*i)
    rw [show x+4*i+sd = x+sd+4*i by omega]
    exact O.w32 (by omega) (by omega)
  · rw [Z, C', zero]

/-- The same public pointer setup serves both table reads and table writes. -/
theorem copySetup_ok {s : State} {W : Addr} {size n tab : Nat} {index : Src} {v : BitVec 32}
    (hs : Scr s W size) (hn : 8*n < 2^32) (hv : readSrc s index = some v) :
    WP isa (VG.Impl.Mont.X86.Comb.copySetup n tab index) s fun t =>
      t.mem = s.mem ∧ PtrAt t W .ecx (tab+8*n*v.toNat) ∧ PtrAt t W .ebp 0 ∧
      (t.gpr .ebx).toNat = 2*n ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.copySetup
  refine wp_movS hv fun s₁ U₁ _ => wp_movS rfl fun s₂ U₂ _ => wp_mul fun s₃ U₃ => ?_
  refine wp_addS rfl fun s₄ U₄ _ => wp_addS rfl fun s₅ U₅ _ => wp_movS rfl fun s₆ U₆ _ => ?_
  refine wp_movS rfl fun s₇ U₇ _ => wp_movS rfl fun t U₈ _ => WP.block_nil ?_
  have E : s₂.gpr .eax = v := by rw [U₂.other _ (by decide), U₁.gpr]
  have D : s₂.gpr .edx = BitVec.ofNat 32 (8*n) := U₂.gpr
  have base : s₃.gpr .edi = s.gpr .edi := by
    rw [U₃.other _ (by decide) (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t :=
    (((((((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps).widen U₄.keeps).widen
      U₅.keeps).widen U₆.keeps).widen U₇.keeps).widen U₈.keeps
  refine ⟨?_, ?_, ?_, ?_, K⟩
  · rw [U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  · unfold PtrAt
    rw [U₈.other _ (by decide), U₇.other _ (by decide), U₆.gpr, U₅.gpr, U₄.gpr, U₃.eax, E, D, base]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, hs.edi_toNat]
    rw [Nat.mul_comm v.toNat]
    omega
  · unfold PtrAt
    rw [U₈.other _ (by decide), U₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide),
      U₄.other _ (by decide), base, hs.edi_toNat, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (by rw [← hs.edi_toNat]; exact (s.gpr .edi).isLt)).symm
  · rw [U₈.gpr]
    change (2*n) % 2^32 = 2*n
    exact Nat.mod_eq_of_lt (by omega)

end VG.Proof.Mont.X86.Comb
