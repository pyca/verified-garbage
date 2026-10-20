module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Env
public import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math

/-! # Multiplications in the exponentiation of public RSA at a run-time width

The stages' changes as changes within `Chg` (`Outside.chg`, `mulFrame_chg`),
and a multiplication by a call in `Env`, of numbers in Montgomery form
(`mulEnv_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem ofs_in_off {base x : Addr} {d n : Nat} (h₁ : d ≤ ofs base x) (h₂ : ofs base x < d + n) :
    (⟨off base d, n⟩ : Region).Contains x 1 := by
  simp only [Region.Contains, off, ofs] at *
  bv_omega

theorem sub_off {base : Addr} {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) :
    Region.Sub ⟨off base d, n⟩ ⟨off base e, k⟩ := Offset.sub base h₁ h₂

/-- A change of a range of the header's words 128 to 139, or of the numbers from 1 on, is within `Chg`. -/
theorem Outside.chg {base : Addr} {len bytes d n : Nat} {sp : BitVec 32} {m m' : Mem}
    (O : Outside base d n m m')
    (hd : (128 ≤ d ∧ d + n ≤ 140) ∨ (numAt len 1 ≤ d ∧ d + n ≤ bytes)) :
    Frame (Chg base len bytes sp) m m' := by
  intro x hx
  refine O x ?_
  by_contra hc
  simp only [not_or, Nat.not_lt] at hc
  rcases hd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hx ⟨off base 128, 12⟩ (by simp [Chg]) (ofs_in_off (by omega) (by omega))
  · exact hx ⟨off base (numAt len 1), bytes - numAt len 1⟩ (by simp [Chg]) (ofs_in_off (by omega) (by omega))

/-- A multiplication's changes are within `Chg`. -/
theorem mulFrame_chg {base : Addr} {len bytes o : Nat} {sp : BitVec 32} {m m' : Mem} (ho : 1 ≤ o)
    (hb : numAt len 5 + (3 * wb len + 56) ≤ bytes)
    (F : Frame [⟨off base (numAt len o), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below sp 40] m m')
    (ho4 : numAt len o + wb len ≤ bytes) :
    Frame (Chg base len bytes sp) m m' := by
  have : numAt len 1 ≤ numAt len o := by
    have := Nat.mul_le_mul_right (wb len) ho; simp only [numAt]; omega
  have : numAt len 1 ≤ numAt len 5 := by simp only [numAt]; omega
  refine F.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨off base (numAt len 1), bytes - numAt len 1⟩, by simp [Chg], sub_off (by omega) (by omega)⟩
  · exact ⟨⟨off base (numAt len 1), bytes - numAt len 1⟩, by simp [Chg], sub_off (by omega) (by omega)⟩
  · exact ⟨below sp 40, by simp [Chg], fun _ h => h⟩

/-- A number apart from a multiplication's changes keeps its value. -/
theorem mulFrame_val32 {base : Addr} {len bytes o d : Nat} {sp : BitVec 32} {m m' : Mem}
    (R : CallRoom sp base bytes) (hn : base.toNat + bytes ≤ 2 ^ 32)
    (F : Frame [⟨off base (numAt len o), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below sp 40] m m')
    (hd : d + 4 * nw len ≤ numAt len o ∨ numAt len o + wb len ≤ d) (h5 : d + 4 * nw len ≤ numAt len 5)
    (hdb : d + 4 * nw len ≤ bytes) (ho : numAt len o + wb len ≤ bytes)
    (h5b : numAt len 5 + (3 * wb len + 56) ≤ bytes) :
    val32 m' base d (nw len) = val32 m base d (nw len) := by
  rw [← read_eq_val32, ← read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off base d, 4 * nw len⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by omega))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint base (by rw [← wb_eq] at *; omega) (by omega) (by omega)
  · exact Offset.disjoint base (by omega) (by omega) (by omega)
  · refine (R.apart.sub_right ?_).symm
    have := Offset.sub base (d := d) (n := 4 * nw len) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- The header keeps its bytes across a multiplication. -/
theorem mulFrame_hdr {base : Addr} {len bytes o d k : Nat} {sp : BitVec 32} {m m' : Mem}
    (R : CallRoom sp base bytes) (hn : base.toNat + bytes ≤ 2 ^ 32)
    (F : Frame [⟨off base (numAt len o), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below sp 40] m m')
    (hd : d + k ≤ numOff) (hdb : d + k ≤ bytes) (ho : numAt len o + wb len ≤ bytes)
    (h5b : numAt len 5 + (3 * wb len + 56) ≤ bytes) :
    m'.read (off base d) k = m.read (off base d) k := by
  have : numOff ≤ numAt len o := by simp [numAt]
  have : numOff ≤ numAt len 5 := by simp [numAt]
  refine F.read (r := ⟨off base d, k⟩) (Region.contains_self _ _) (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint base (by omega) (by omega) (by omega)
  · exact Offset.disjoint base (by omega) (by omega) (by omega)
  · refine (R.apart.sub_right ?_).symm
    have := Offset.sub base (d := d) (n := k) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- The modulus is odd, so `R` is invertible modulo it. -/
theorem Env.coprime {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat} {s : State}
    (E : Env base bytes len args M s) (k : Nat) : Nat.Coprime (2 ^ k) M := by
  have hi := E.inv
  have hmod : (M * w32 s.mem base invOff + 1) % 2 = 0 := by omega
  refine VG.Proof.Bignum.coprime_pow2 ?_ k
  rcases Nat.mod_two_eq_zero_or_one M with hm | hm
  · rw [Nat.add_mod, Nat.mul_mod, hm] at hmod; simp at hmod
  · exact hm

/-- A multiplication by a call in `Env`: the product's value, as `mul_ok` gives it. -/
theorem mulRaw_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbytes : bytes = (args 9).toNat * 8)
    {o a b : Nat} (ho : 1 ≤ o) (ho4 : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4)
    (hBlt : val32 s.mem base (numAt len b) (nw len) < M) :
    WP isa (PublicRt.mul o a b) s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t ∧
      Frame [⟨off base (numAt len o), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below (s.gpr .esp) 40]
        s.mem t.mem ∧
      val32 t.mem base (numAt len o) (nw len) < M ∧
      val32 t.mem base (numAt len o) (nw len) * 2 ^ (32 * nw len) % M =
        val32 s.mem base (numAt len a) (nw len) * val32 s.mem base (numAt len b) (nw len) % M := by
  have h := E.pi
  refine WP.mono (mul_ok h hbytes E.room ho4 ha hb (by omega) (by rw [E.mod]; exact E.inv)
    (by rw [E.mod]; exact hBlt)) fun t ⟨cs, rd, wr, F, L, C⟩ => ?_
  rw [E.mod] at L C
  have K : Keeps [.eax, .ecx, .edx] s t :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> simp [calleeSaved]), rd, wr⟩
  have Fc := mulFrame_chg (base := base) (bytes := bytes) ho (h.fits (j := 5) (by decide)).2 F
    (h.fits (j := o) (by omega)).1
  exact ⟨E.keep K (by decide) (by decide) Fc, Fc, K, F, L, C⟩

theorem mulEnv_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbytes : bytes = (args 9).toNat * 8)
    {o a b : Nat} (ho : 1 ≤ o) (ho4 : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4) {x y : Nat}
    (hA : val32 s.mem base (numAt len a) (nw len) % M = x * 2 ^ (32 * nw len) % M)
    (hB : val32 s.mem base (numAt len b) (nw len) % M = y * 2 ^ (32 * nw len) % M)
    (hBlt : val32 s.mem base (numAt len b) (nw len) < M) :
    WP isa (PublicRt.mul o a b) s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t ∧
      Frame [⟨off base (numAt len o), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below (s.gpr .esp) 40]
        s.mem t.mem ∧
      val32 t.mem base (numAt len o) (nw len) = x * y * 2 ^ (32 * nw len) % M := by
  have h := E.pi
  refine WP.mono (mul_ok h hbytes E.room ho4 ha hb (by omega) (by rw [E.mod]; exact E.inv)
    (by rw [E.mod]; exact hBlt)) fun t ⟨cs, rd, wr, F, L, C⟩ => ?_
  rw [E.mod] at L C
  have K : Keeps [.eax, .ecx, .edx] s t :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> simp [calleeSaved]), rd, wr⟩
  have Fc := mulFrame_chg (base := base) (bytes := bytes) ho (h.fits (j := 5) (by decide)).2 F
    (h.fits (j := o) (by omega)).1
  refine ⟨E.keep K (by decide) (by decide) Fc, Fc, K, F, ?_⟩
  have := VG.Proof.Dsa.mont_product (E.coprime _) hA hB C
  rwa [Nat.mod_eq_of_lt L] at this

end VG.Proof.Bignum.X86.PublicRt
