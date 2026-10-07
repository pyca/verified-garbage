import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.MlKem.X86_64.Groups
import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# ML-KEM-768 on x86-64: moves, byte stores and copies

The address of a pointer (`pa`), and what `setB` and `copy` do.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- A byte of a range. -/
theorem inRegions_byte {rs : List Region} {a : Addr} {n k : Nat} (h : InRegions rs a n) (hk : k < n)
    (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 k) 1 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hk)⟩

/-! ## A byte -/

theorem b8_ofNat {v : Nat} (_hv : v < 256) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.ofNat 32 v)) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem setB_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 256) (s : State)
    (hw : InRegions s.wr (pa s p) 1) :
    WP isa (.block (setB p v)) s fun s' =>
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v)) ?_ (by rfl))
    fun s' ⟨h, k⟩ => ⟨h, k⟩
  unfold setB
  xrun [hw, hr, b8_ofNat hv]


/-! ## A copy -/

theorem b8b (x : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) (h1 : InRegions s.wr (s.gpr .rdi) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax, .alu .add .rdi (.imm 8),
      .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rsi) 64) ∧ s'.gpr .rdi = s.gpr .rdi + 8 ∧
        s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1]

/-- Byte `j` of eight bytes at `p + e` copied from `q + e`, for `e ≤ j < e + 8`. -/
theorem copy8_in (m : Mem) (p q : Addr) {e j : Nat} (h₁ : e ≤ j) (h₂ : j < e + 8) :
    (m.writeW (p + BitVec.ofNat 64 e) (m.readW (q + BitVec.ofNat 64 e) 64)) (p + BitVec.ofNat 64 j) =
      m (q + BitVec.ofNat 64 j) := by
  have ej : ∀ r : Addr, r + BitVec.ofNat 64 j = r + BitVec.ofNat 64 e + BitVec.ofNat 64 (j - e) := fun r => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show e + (j - e) = j by omega]
  rw [ej p, writeW_byte _ _ _ (show 8 * (j - e + 1) ≤ 64 by omega) (by decide), byte_readW _ _ (by omega), ← ej q]

theorem copy_ok (dst src : Ptr) (n : Nat) (hn0 : 0 < n) (h8 : n % 8 = 0) (hn : n < 2 ^ 31) (hd : dst.2 < 2 ^ 31)
    (hs : src.2 < 2 ^ 31) (hsr : src.1 ≠ .rdi) (s : State)
    (hrd : InRegions (s.rd ++ s.wr) (pa s src) n) (hwr : InRegions s.wr (pa s dst) n)
    (hdj : Region.Disjoint ⟨pa s src, n⟩ ⟨pa s dst, n⟩) :
    WP isa (copy dst src n) s fun s' =>
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n ∧ Frame [⟨pa s dst, n⟩] s.mem s'.mem ∧
        Keep [.rax, .rcx, .rsi, .rdi] s s' := by
  unfold copy lea
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = pa s dst ∧
      s'.gpr .rsi = pa s src ∧ s'.gpr .rcx = BitVec.ofNat 64 (n / 8))
    (by xrun [sx_ofNat hd, sx_ofNat hs, hsr, List.cons_append, List.nil_append,
      sw_ofNat (show n / 8 < 2 ^ 32 by omega)])
    (by rfl)) fun s1 ⟨⟨hm1, hdi1, hsi1, hcx1⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := n / 8) (by omega) (by omega) (fun k s' =>
      s'.gpr .rdi = pa s dst + BitVec.ofNat 64 (8 * k) ∧ s'.gpr .rsi = pa s src + BitVec.ofNat 64 (8 * k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < 8 * k, s'.mem (pa s dst + BitVec.ofNat 64 j) = s.mem (pa s src + BitVec.ofNat 64 j)) ∧
      Keep [.rax, .rcx, .rsi, .rdi] s s')
    (fun k hk s' ⟨hdi, hsi, hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hdi1]; simp, by rw [hsi1]; simp, k1.2.1, k1.2.2, by rw [hm1]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega), k1.mono (by decide)⟩ hcx1)
    fun s' ⟨_, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · have r8 : InRegions (s'.rd ++ s'.wr) (s'.gpr .rsi) 8 := by
      rw [hrd', hwr', hsi]
      obtain ⟨r, hr, hcr⟩ := hrd
      exact ⟨r, hr, CallLay.contains_trans hcr (by omega) (by omega)⟩
    have w8 : InRegions s'.wr (s'.gpr .rdi) 8 := by
      rw [hwr', hdi]
      obtain ⟨r, hr, hcr⟩ := hwr
      exact ⟨r, hr, CallLay.contains_trans hcr (by omega) (by omega)⟩
    refine WP.mono (copyBody_ok s' r8 w8) fun s'' ⟨⟨hm, hdi', hsi', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hdi', hdi, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl,
          by rw [hsi', hsi, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl,
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, hdi]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · have hsrc : ∀ t < n, s'.mem (pa s src + BitVec.ofNat 64 t) = s.mem (pa s src + BitVec.ofNat 64 t) :=
        fun t ht => hf.bytes (R := ⟨pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega) ht
      rw [hm, hdi, hsi]
      by_cases e : 8 * k ≤ j
      · rw [copy8_in _ _ _ e (by omega), hsrc j (by omega)]
      · have hj' : j < 8 * k := by omega
        have := readW_writeW_off s'.mem (pa s dst) (s'.mem.readW (pa s src + BitVec.ofNat 64 (8 * k)) 64)
          (d := j) (e := 8 * k) (n := 1) (by omega) (by omega) (by omega)
        rw [Nat.mul_one, readW_8, readW_8] at this
        rw [this, hc j hj']
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (by have := List.mem_range.mp hi; omega)

end VG.Proof.MlKem.X86_64
