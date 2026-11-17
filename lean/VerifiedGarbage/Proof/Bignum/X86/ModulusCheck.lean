module

public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.ModulusCheckMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! ### `Bignum.X86.ModulusFinish`, which this module and modules that import it used -/

section

/-! # Combining modulus-rejection bits on i686 -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem modulusFinish_ok (s : State) :
    WP isa (.block modulusFinish) s fun t =>
      t.zf = some ((s.gpr .ebx ||| ((s.gpr .edx &&& 1) ^^^ 1) ||| s.gpr .ebp) == 0) ∧
      t.mem = s.mem ∧ Keeps [.edx, .ebx] s t := by
  unfold modulusFinish
  refine wp_logicS (.inl rfl) rfl fun s₁ u₁ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₂ u₂ => ?_
  refine wp_orS rfl fun s₃ u₃ => ?_
  refine wp_orS rfl fun s₄ u₄ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · have subzero : s₄.gpr .ebx - (0 : BitVec 32) = s₄.gpr .ebx := BitVec.sub_zero _
    rw [zt, subzero, u₄.gpr, u₃.gpr, u₂.other .ebx (by decide), u₁.other .ebx (by decide),
      u₂.gpr, u₁.gpr, u₃.other .ebp (by decide), u₂.other .ebp (by decide), u₁.other .ebp (by decide)]
    rfl
  · rw [ft.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · exact ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).trans (ft.keeps _)

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.ModulusBounds`, which this module and modules that import it used -/

section

/-! # Leading-byte and minimum-modulus checks on i686 -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem rotate_threshold (k : BitVec 32) (hk : 64 ≤ k.toNat) (hk' : k.toNat ≤ 1024) :
    (k - 64).rotateRight 24 = (k - 64) <<< 8 := by
  have high : (k - 64) >>> 24 = (0 : BitVec 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
    simp only [show (64 : BitVec 32).toNat = 64 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl]
    omega_using [hk, hk']
  rw [BitVec.rotateRight_def]
  change (k - 64) >>> 24 ||| (k - 64) <<< 8 = _
  rw [high]
  exact BitVec.zero_or

theorem modulusBounds_ok (s : State) (hk : 64 ≤ (s.gpr .ecx).toNat)
    (hk' : (s.gpr .ecx).toNat ≤ 1024) :
    WP isa (.block modulusBounds) s fun t =>
      t.gpr .ebx = (s.gpr .eax - 1) >>> 31 ∧
      t.gpr .ebp = ((((s.gpr .ecx - 64) <<< 8) + s.gpr .eax) - 128) >>> 31 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp] s t := by
  unfold modulusBounds
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_subS rfl fun s₂ u₂ _ => ?_
  refine wp_shr (by decide) fun s₃ u₃ _ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => ?_
  refine wp_subS rfl fun s₅ u₅ _ => ?_
  refine wp_ror (by decide) fun s₆ u₆ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_subS rfl fun s₈ u₈ _ => ?_
  refine wp_shr (by decide) fun t u₉ _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₉.other .ebx (by decide), u₈.other .ebx (by decide), u₇.other .ebx (by decide),
      u₆.other .ebx (by decide), u₅.other .ebx (by decide), u₄.other .ebx (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr,
      u₃.other .ecx (by decide), u₂.other .ecx (by decide), u₁.other .ecx (by decide),
      u₆.other .eax (by decide), u₅.other .eax (by decide), u₄.other .eax (by decide),
      u₃.other .eax (by decide), u₂.other .eax (by decide), u₁.other .eax (by decide),
      rotate_threshold _ hk hk']
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · exact ((((((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen
      u₄.keeps).widen u₅.keeps).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps).widen u₉.keeps

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.ModulusRead`, which this module and modules that import it used -/

section

/-! # Reading the first and last modulus bytes without crossing its buffer -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem modulusRead_ok (s : State) {k : Nat} (hk : 0 < k)
    (fit : (s.gpr .esi).toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi)) k)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa (.block modulusRead) s fun t =>
      t.gpr .eax = (s.mem (byteAddr (s.gpr .esi))).setWidth 32 ∧
      t.gpr .edx = (s.mem (byteAddr (s.gpr .esi) + BitVec.ofNat 64 (k - 1))).setWidth 32 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  have readable (i : Nat) (hi : i < k) :
      InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi) + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [fit, hi])]; omega_using [hi])⟩
  have first : InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi)) 1 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using readable 0 hk
  unfold modulusRead
  refine wp_loadByte (by simp only [State.ea, BitVec.add_zero]; rfl)
    first fun s₁ u₁ => ?_
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun s₄ u₄ _ => ?_
  have K : Keeps [.eax, .ebx, .edx] s s₄ :=
    (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps
  have ptr : s₄.gpr .ebx = s.gpr .esi + BitVec.ofNat 32 (k - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other .esi (by decide),
      u₂.other .ecx (by decide), u₁.other .ecx (by decide), count]
    change s.gpr .esi + BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega_using [hk])]
  have addr : s₄.ea ⟨.ebx, 0⟩ = byteAddr (s.gpr .esi) + BitVec.ofNat 64 (k - 1) := by
    simp only [State.ea, BitVec.add_zero]
    rw [ptr]
    exact byteAddr_add (by omega_using [fit])
  refine wp_loadByte addr (by rw [K.2.1, K.2.2]; exact readable (k - 1) (by omega_using [hk]))
    fun t u₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, K.widen u₅.keeps⟩
  · rw [u₅.other .eax (by decide), u₄.other .eax (by decide), u₃.other .eax (by decide),
      u₂.other .eax (by decide), u₁.gpr]
  · rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.Bignum.X86

end

end

/-! # i686 modulus validation agrees with the shared RSA specification -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem modulusCheck_ok (s : State) {k : Nat}
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (fit : (s.gpr .esi).toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi)) k)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa (.block modulusCheck) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (s.gpr .esi)) k)) k) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx, .ebp] s t := by
  unfold modulusCheck
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (modulusRead_ok s (by omega_using [hk]) fit read count)
    fun u ⟨first, last, M, K⟩ => ?_)
  have byteNat (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]
  have firstNat : (u.gpr .eax).toNat = (s.mem (byteAddr (s.gpr .esi))).toNat := by rw [first, byteNat]
  have lastNat : (u.gpr .edx).toNat =
      (s.mem (byteAddr (s.gpr .esi) + BitVec.ofNat 64 (k - 1))).toNat := by rw [last, byteNat]
  have countNat : (u.gpr .ecx).toNat = k := by
    rw [K.1 .ecx (by decide), count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk'])]
  refine WP.block_append (WP.mono (modulusBounds_ok u (by rw [countNat]; exact hk)
    (by rw [countNat]; exact hk')) fun v ⟨low, top, Mv, Kv⟩ => ?_)
  refine WP.mono (modulusFinish_ok v) fun t ⟨Z, Mt, Kt⟩ => ?_
  refine ⟨?_, Mt.trans (Mv.trans M),
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))⟩
  rw [Z, low, top, Kv.1 .edx (by decide), modulusCheck_value _ _ _
    (by rw [firstNat]; exact (s.mem _).isLt) (by rw [countNat]; exact hk) (by rw [countNat]; exact hk'),
    firstNat, lastNat, countNat]
  rw [modulusValid_iff (bytesAt_length _ _ _) hk hk']
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, BitVec.add_zero]

end VG.Proof.Bignum.X86
