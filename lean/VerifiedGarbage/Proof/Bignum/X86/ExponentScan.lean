module

public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.ExponentWords
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import all Init.Data.Nat.Bitwise.Basic

/-! ### `Bignum.X86.ExponentByte`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.ExponentAccumulate`, which this module and modules that import it used -/

section

/-! # Native-word effects of the public-exponent accumulation step -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem rotate_mask_byte (x : BitVec 32) :
    x.rotateRight 24 &&& 0xffffff00 = x <<< 8 := by
  change x.rotateRight (32 - 8) &&& (BitVec.allOnes 32 <<< 8) = x <<< 8
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_rotateRight]
  simp only [hp, decide_true, Bool.true_and]
  by_cases h : p < 8
  · simp [h]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and,
      ↓reduceIte,
      decide_eq_true (show p - 8 < 32 by omega_using [hp]), Bool.and_true]

theorem exponentAccumulate_ok (s : State) {p : Addr}
    (ptr : s.ea ⟨.esi, 0⟩ = p) (read : InRegions (s.rd ++ s.wr) p 1) :
    WP isa (.block exponentAccumulate) s fun t =>
      t.gpr .ebx = (s.gpr .ebx <<< 8) + (s.mem p).setWidth 32 ∧
      t.gpr .edx = (s.gpr .edx <<< 8) + (s.gpr .ebx >>> 24) ∧
      t.zf = some (((((s.gpr .edx <<< 8) + (s.gpr .ebx >>> 24)) >>> 1)) == 0) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx, .ebp] s t := by
  unfold exponentAccumulate
  refine wp_loadByte ptr read fun s1 u1 => ?_
  refine wp_movS rfl fun s2 u2 _ => ?_
  refine wp_shr (by decide) fun s3 u3 _ => ?_
  refine wp_ror (by decide) fun s4 u4 => ?_
  refine wp_logicS (.inl rfl) rfl fun s5 u5 => ?_
  refine wp_addS rfl fun s6 u6 _ => ?_
  refine wp_ror (by decide) fun s7 u7 => ?_
  refine wp_logicS (.inl rfl) rfl fun s8 u8 => ?_
  refine wp_addS rfl fun s9 u9 _ => ?_
  refine wp_movS rfl fun s10 u10 _ => ?_
  refine wp_shr (by decide) fun s11 u11 _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have high : s6.gpr .edx = (s.gpr .edx <<< 8) + (s.gpr .ebx >>> 24) := by
    rw [u6.gpr, u5.gpr, u4.gpr, u3.other .edx (by decide), u2.other .edx (by decide),
      u1.other .edx (by decide), u5.other .ebp (by decide),
      u4.other .ebp (by decide), u3.gpr, u2.gpr, u1.other .ebx (by decide)]
    simp only [ite_true, BitVec.ofNat_eq_ofNat]
    exact congrArg (fun v => v + (s.gpr .ebx >>> 24)) (rotate_mask_byte (s.gpr .edx))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ft.gpr, u11.other .ebx (by decide), u10.other .ebx (by decide), u9.gpr,
      u8.gpr, u7.gpr, u6.other .ebx (by decide), u5.other .ebx (by decide),
      u4.other .ebx (by decide), u3.other .ebx (by decide), u2.other .ebx (by decide),
      u1.other .ebx (by decide), u8.other .eax (by decide),
      u7.other .eax (by decide), u6.other .eax (by decide), u5.other .eax (by decide),
      u4.other .eax (by decide), u3.other .eax (by decide), u2.other .eax (by decide), u1.gpr]
    simp only [ite_true, BitVec.ofNat_eq_ofNat]
    exact congrArg (fun v => v + (s.mem p).setWidth 32) (rotate_mask_byte (s.gpr .ebx))
  · rw [ft.gpr, u11.other .edx (by decide), u10.other .edx (by decide),
      u9.other .edx (by decide), u8.other .edx (by decide), u7.other .edx (by decide), high]
  · rw [zt, u11.gpr, u10.gpr, u9.other .edx (by decide),
      u8.other .edx (by decide), u7.other .edx (by decide), high]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · rw [ft.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem,
      u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (((((((((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen
      u4.keeps).widen u5.keeps).widen u6.keeps).widen u7.keeps).widen u8.keeps).widen
      u9.keeps).widen u10.keeps).widen u11.keeps).trans (ft.keeps _)

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.ExponentSaturate`, which this module and modules that import it used -/

section

/-! # Saturate only the public exponent's upper word -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentSaturate_ok (s : State) {h : Nat}
    (high : s.gpr .edx = BitVec.ofNat 32 h) (zero : s.zf = some (decide (h < 2))) :
    WP isa (.ite .e (.block []) (.block [.mov .edx (.imm 2)])) s fun t =>
      t.gpr .edx = BitVec.ofNat 32 (min 2 h) ∧ t.mem = s.mem ∧ Keeps [.edx] s t := by
  refine WP.ite (decide (h < 2)) (by exact zero) ?_ ?_
  · intro valid
    have lt : h < 2 := of_decide_eq_true valid
    exact WP.block_nil ⟨by rw [high, Nat.min_eq_right (by omega_using [lt])], rfl, Keeps.refl _ _⟩
  · intro invalid
    have ge : 2 ≤ h := by have := of_decide_eq_false invalid; omega_using [this]
    refine wp_movS rfl fun t a _ => WP.block_nil ?_
    exact ⟨by rw [a.gpr, Nat.min_eq_left ge]; rfl, a.mem, a.keeps.mono (by decide)⟩

theorem exponentConsume_ok (s : State) {p : Addr} {x : Nat} {b : Byte}
    (ptr : s.ea ⟨.esi, 0⟩ = p)
    (read : InRegions (s.rd ++ s.wr) p 1) (byte : s.mem p = b)
    (low : s.gpr .ebx = BitVec.ofNat 32 (x % 2 ^ 32))
    (high : s.gpr .edx = BitVec.ofNat 32 (exponentHigh x)) :
    WP isa (.seq (.block exponentAccumulate)
      (.ite .e (.block []) (.block [.mov .edx (.imm 2)]))) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 ((256 * x + b.toNat) % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (256 * x + b.toNat)) ∧
      t.mem = s.mem ∧ Keeps [.ebx, .edx, .ebp, .eax] s t := by
  rw [WP.seq_iff]
  refine WP.mono (exponentAccumulate_ok s ptr read) ?_
  rintro u ⟨lo, hi, zero, mem, rest⟩
  rw [low, byte, exponent_low_word] at lo
  rw [low, high, exponent_high_word] at hi zero
  rw [exponent_high_zero _ (by have := exponentHigh_bound x; have := Nat.mod_lt x (by decide : 0 < 2 ^ 32); omega_arith)] at zero
  refine WP.mono (exponentSaturate_ok u hi zero) ?_
  rintro t ⟨value, memT, restT⟩
  rw [exponentHigh_step x b.toNat b.isLt] at value
  exact ⟨(restT.1 .ebx (by decide)).trans lo, value, memT.trans mem,
    (rest.mono (by decide)).trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.X86

end

end

/-! # Consume one public exponent byte and advance the public scan -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentAdvance_ok (s : State) {c : Nat} (hc : 0 < c) (hc' : c < 2 ^ 32)
    (count : s.gpr .ecx = BitVec.ofNat 32 c) :
    WP isa (.block exponentAdvance) s fun t => t.gpr .esi = s.gpr .esi + 1 ∧
      t.gpr .ecx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide (c = 1)) ∧
      t.mem = s.mem ∧ Keeps [.esi, .ecx] s t := by
  unfold exponentAdvance
  refine wp_addS rfl fun u a _ => ?_
  refine wp_subS rfl fun v b _ => ?_
  refine wp_cmpS rfl fun t f z => WP.block_nil ?_
  have value : u.gpr .ecx - (1 : BitVec 32) = BitVec.ofNat 32 (c - 1) := by
    rw [a.other .ecx (by decide), count, Dynamic.counter_sub hc' hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f.gpr, b.other .esi (by decide), a.gpr]
  · rw [f.gpr, b.gpr, value]
  · rw [z, b.gpr, a.other .ecx (by decide), count, Dynamic.counter_sub hc' hc, Dynamic.counter_zero hc' hc]
  · rw [f.mem, b.mem, a.mem]
  · exact ((a.keeps.mono (by decide)).widen b.keeps).trans (f.keeps _)

theorem exponentByte_ok (s : State) {p : BitVec 32} {x c : Nat} {b : Byte}
    (hc : 0 < c) (hc' : c < 2 ^ 32)
    (ptr : s.gpr .esi = p) (count : s.gpr .ecx = BitVec.ofNat 32 c)
    (read : InRegions (s.rd ++ s.wr) (byteAddr p) 1) (byte : s.mem (byteAddr p) = b)
    (low : s.gpr .ebx = BitVec.ofNat 32 (x % 2 ^ 32))
    (high : s.gpr .edx = BitVec.ofNat 32 (exponentHigh x)) :
    WP isa exponentByte s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 ((256 * x + b.toNat) % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (256 * x + b.toNat)) ∧
      t.gpr .esi = p + 1 ∧ t.gpr .ecx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide (c = 1)) ∧
      t.mem = s.mem ∧ Keeps [.esi, .ebx, .edx, .ebp, .eax, .ecx] s t := by
  rw [exponentByte, WP.seq_iff]
  refine WP.mono (exponentConsume_ok s (by simp only [State.ea, ptr, BitVec.add_zero]; rfl) read byte low high) ?_
  rintro u ⟨lowU, highU, memU, restU⟩
  refine WP.mono (exponentAdvance_ok u hc hc' ((restU.1 .ecx (by decide)).trans count)) ?_
  rintro t ⟨ptrT, countT, zero, memT, restT⟩
  exact ⟨(restT.1 .ebx (by decide)).trans lowU, (restT.1 .edx (by decide)).trans highU,
    by rw [ptrT, restU.1 .esi (by decide), ptr], countT, zero, memT.trans memU,
    (restU.mono (by decide)).trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.X86

end

end

/-! # The public-exponent scanner computes the exact low word and saturated high word -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

abbrev exponentClobbers : List Reg := [.esi, .ebx, .edx, .ebp, .eax, .ecx]

theorem exponentLoop_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length)
    (low : s.gpr .ebx = 0) (high : s.gpr .edx = 0) :
    WP isa (.loop exponentByte .ne) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  let I := fun k t => ∃ j, j + k = eb.length ∧ 0 < k ∧
    t.gpr .ebx = BitVec.ofNat 32 (pre eb j % 2 ^ 32) ∧
    t.gpr .edx = BitVec.ofNat 32 (exponentHigh (pre eb j)) ∧
    t.gpr .esi = ep + BitVec.ofNat 32 j ∧ t.gpr .ecx = BitVec.ofNat 32 k ∧
    t.mem = s.mem ∧ Keeps exponentClobbers s t
  refine WP.loop (M := isa) I ?_ eb.length s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, lo, hi, pointer, counter, mem, rest⟩ := inv
    have hj : j < eb.length := by omega_using [jk, hk]
    have address : byteAddr (ep + BitVec.ofNat 32 j) = byteAddr ep + BitVec.ofNat 64 j :=
      byteAddr_add (by omega_using [sourceFit, hj])
    have currentRead : InRegions (t.rd ++ t.wr) (byteAddr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [rest.2.1, rest.2.2, address]
      exact CallLay.inRegions_sub read (by omega_using [hj]) (by omega_using [countFit])
    have currentByte : t.mem (byteAddr (ep + BitVec.ofNat 32 j)) = eb[j] := by
      rw [mem, address]; exact bytes j hj
    refine WP.mono (exponentByte_ok t hk (by omega_using [countFit, jk]) pointer counter currentRead currentByte lo hi) ?_
    rintro u ⟨loU, hiU, ptrU, countU, zero, memU, restU⟩
    have next : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
      rw [pre_succ eb hj, Nat.mul_comm]
    rw [next] at loU hiU
    have ptrNext : u.gpr .esi = ep + BitVec.ofNat 32 (j + 1) := by
      rw [ptrU]
      change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    by_cases last : k = 1
    · left
      refine ⟨?_, ?_, ?_, memU.trans mem, rest.trans restU⟩
      · change u.zf.map not = some false
        simp only [zero, last, decide_true, Option.map_some, Bool.not_true]
      · simpa only [show j + 1 = eb.length by omega_using [jk, last], pre_len] using loU
      · simpa only [show j + 1 = eb.length by omega_using [jk, last], pre_len] using hiU
    · right
      refine ⟨?_, k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [hk, last], loU, hiU, ptrNext, countU,
        memU.trans mem, rest.trans restU⟩
      change u.zf.map not = some true
      simp only [zero, last, decide_false, Option.map_some, Bool.not_false]
  · exact ⟨0, by omega_using [], positive, low, by simpa [pre_zero, exponentHigh] using high, by simpa using ptr, count, rfl, Keeps.refl _ _⟩

theorem exponentScan_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length) :
    WP isa exponentScan s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  rw [exponentScan, WP.seq_iff]
  refine wp_movS rfl fun u a _ => ?_
  refine wp_movS rfl fun v b _ => WP.block_nil ?_
  have rest : Keeps [.ebx, .edx] s v := (a.keeps.mono (by decide)).trans (b.keeps.mono (by decide))
  have mem := b.mem.trans a.mem
  refine WP.mono (exponentLoop_ok v positive countFit sourceFit
    (by rw [rest.2.1, rest.2.2]; exact read) (by rw [mem]; exact bytes)
    ((rest.1 .esi (by decide)).trans ptr) ((rest.1 .ecx (by decide)).trans count)
    ((b.other .ebx (by decide)).trans a.gpr) b.gpr) ?_
  rintro t ⟨lo, hi, memT, restT⟩
  exact ⟨lo, hi, memT.trans mem, (rest.mono (by decide)).trans restT⟩

end VG.Proof.Bignum.X86
