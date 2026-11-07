module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! # FFDH parameter candidates on x86-64: exact small remainders -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem residue_ok {s : State} {B : Addr} {Z w divisor : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hd : 1 < divisor) (hd' : divisor < 2 ^ 31) :
    WP isa (residue divisor) s fun t =>
      (t.gpr .rsi).toNat = wv s.mem B (slot w aN) w % divisor ∧ t.mem = s.mem ∧
      Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hb : (BitVec.ofNat 32 divisor).setWidth 64 = BitVec.ofNat 64 divisor := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  unfold residue
  refine WP.seq (WP.mono (WP.keep [.rbx, .r12, .r8, .rsi, .r14]
    (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 divisor ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .rsi = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hg.hdr.hw,
      hg.hdr.harr aN (by decide), hb]) rfl) fun u ⟨⟨hbx, h12, h8, hsi, h14, hm⟩, k⟩ => ?_)
  refine WP.mono (modWords_ok (hg.scr.congr k.2.2) h8 h12 h14 hw hw'
    (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith) hsi
    (by rw [hbx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; exact hd))
    fun t ⟨hv, hm', k'⟩ => ?_
  exact ⟨by simpa only [hm, hbx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show divisor < 2 ^ 64 by omega_arith)] using hv,
    hm'.trans hm, (k.trans k').mono (by decide)⟩

/-! ## Membership of a small remainder -/

theorem memberStep_ok {s : State} {r v : Nat} {acc : Bool} (hr : r < 2 ^ 31) (hv : v < 2 ^ 31)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 r) (hcx : s.gpr .rcx = 1)
    (hax : s.gpr .rax = if acc then 1 else 0) :
    WP isa (.block (memberStep v)) s fun t =>
      (t.gpr .rax = if (acc || decide (r = v)) then 1 else 0) ∧ t.gpr .rsi = s.gpr .rsi ∧
        t.gpr .rcx = s.gpr .rcx ∧ t.mem = s.mem ∧ Keep [.rsi, .rax] s t := by
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t =>
    (t.gpr .rax = if (acc || decide (r = v)) then 1 else 0) ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ha, hs, hc, hm⟩, k⟩ => ⟨ha, hs, hc, hm, k.mono (by decide)⟩
  have hz := ofNat_sub_beq (j := r) (N := v) (by omega_arith) (by omega_arith)
  unfold memberStep
  by_cases h : r = v
  · xrun [hsi, hcx, hax, sx_ofNat hv, hz, h, execCmov, eval]
    cases acc <;> simp
  · xrun [hsi, hcx, hax, sx_ofNat hv, hz, h, execCmov, eval]
    cases acc <;> simp

theorem memberSteps_ok {r : Nat} (hr : r < 2 ^ 31) :
    ∀ (vals : List Nat) (_ : ∀ v ∈ vals, v < 2 ^ 31) {acc : Bool} {s : State}
      (_ : s.gpr .rsi = BitVec.ofNat 64 r) (_ : s.gpr .rcx = 1) (_ : s.gpr .rax = if acc then 1 else 0),
      WP isa (.block (vals.flatMap memberStep)) s fun t =>
        (t.gpr .rax = if (acc || decide (r ∈ vals)) then 1 else 0) ∧ t.gpr .rsi = s.gpr .rsi ∧
          t.gpr .rcx = s.gpr .rcx ∧ t.mem = s.mem ∧ Keep [.rsi, .rax] s t
  | [], _, acc, s, _, _, hax => WP.block_nil ⟨by simpa using hax, rfl, rfl, rfl, Keep.refl _ _⟩
  | v :: vs, hvals, acc, s, hsi, hcx, hax => by
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (memberStep_ok hr (hvals v (by simp)) hsi hcx hax)
      fun u ⟨hu, hus, huc, hum, k⟩ => ?_)
    refine WP.mono (memberSteps_ok hr vs (fun w hw => hvals w (by simp [hw])) (hus.trans hsi)
      (huc.trans hcx) hu) fun t ⟨ht, hts, htc, htm, k'⟩ => ?_
    refine ⟨?_, hts.trans hus, htc.trans huc, htm.trans hum, (k.trans k').mono (by decide)⟩
    rw [ht]
    by_cases h1 : r = v <;> by_cases h2 : r ∈ vs <;> cases acc <;> simp [h1, h2]

/-- `member vals`: ZF is whether the remainder in RSI is one of `vals`. -/
theorem member_ok {s : State} {r : Nat} {vals : List Nat} (hr : r < 2 ^ 31)
    (hvals : ∀ v ∈ vals, v < 2 ^ 31) (hsi : s.gpr .rsi = BitVec.ofNat 64 r) :
    WP isa (.block (member vals)) s fun t =>
      t.zf = some (decide (r ∈ vals)) ∧ t.mem = s.mem ∧ Keep [.rsi, .rax, .rcx] s t := by
  unfold member
  refine WP.block_append (WP.block_append ?_)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun u => u.gpr .rax = (if false then 1 else 0) ∧
    u.gpr .rcx = 1 ∧ u.gpr .rsi = s.gpr .rsi ∧ u.mem = s.mem) (by xrun) rfl)
    fun u ⟨⟨hua, huc, hus, hum⟩, k⟩ => ?_
  refine WP.mono (memberSteps_ok hr vals hvals (hus.trans hsi) huc hua)
    fun v ⟨hva, _, _, hvm, k'⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (r ∈ vals)) ∧ t.mem = v.mem) ?_ rfl)
    fun t ⟨⟨hz, hm⟩, k''⟩ => ⟨hz, hm.trans (hvm.trans hum), ((k.trans k').trans k'').mono (by decide)⟩
  simp only [Bool.false_or] at hva
  by_cases h : r ∈ vals
  · xrun [hva, h]
  · xrun [hva, h]

/-! ## The generators' congruences, with the small primes of p and q -/

/-- What the generator check accepts: `allowed2` modulo 840, or `allowed5`
modulo 420. -/
def screen (generator p : Nat) : Bool :=
  if generator = 2 then decide (p % 840 ∈ allowed2) else decide (p % 420 ∈ allowed5)

theorem allowed2_lt : ∀ v ∈ allowed2, v < 2 ^ 31 := by decide +kernel
theorem allowed5_lt : ∀ v ∈ allowed5, v < 2 ^ 31 := by decide +kernel

theorem generator2_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa generator2 s fun t => t.zf = some (decide (wv s.mem B (slot w aN) w % 840 ∈ allowed2)) ∧
      t.mem = s.mem ∧ Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  unfold generator2
  refine WP.seq (WP.mono (residue_ok hg hZ hw hw' (by decide : 1 < 840) (by decide))
    fun u ⟨hv, hm, k⟩ => ?_)
  have hsi : u.gpr .rsi = BitVec.ofNat 64 (wv s.mem B (slot w aN) w % 840) := by
    rw [← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact WP.mono (member_ok (by omega_arith) allowed2_lt hsi)
    fun t ⟨hz, hm', k'⟩ => ⟨hz, hm'.trans hm, (k.trans k').mono (by decide)⟩

theorem generator5_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa generator5 s fun t => t.zf = some (decide (wv s.mem B (slot w aN) w % 420 ∈ allowed5)) ∧
      t.mem = s.mem ∧ Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  unfold generator5
  refine WP.seq (WP.mono (residue_ok hg hZ hw hw' (by decide : 1 < 420) (by decide))
    fun u ⟨hv, hm, k⟩ => ?_)
  have hsi : u.gpr .rsi = BitVec.ofNat 64 (wv s.mem B (slot w aN) w % 420) := by
    rw [← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact WP.mono (member_ok (by omega_arith) allowed5_lt hsi)
    fun t ⟨hz, hm', k'⟩ => ⟨hz, hm'.trans hm, (k.trans k').mono (by decide)⟩

private theorem allowed2_shape : ∀ r < 840, r ∈ allowed2 → r % 24 = 11 := by decide +kernel
private theorem allowed5_shape : ∀ r < 420, r ∈ allowed5 → r % 10 = 3 ∨ r % 10 = 7 := by decide +kernel

/-- The accepted remainders have the generator's congruence. -/
theorem screen_shape {bits generator p : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hbits : Spec.RsaKeyGen.bitLength p = bits) (hgen : generator = 2 ∨ generator = 5) :
    (Spec.Ffdh.generationShape bits generator p && screen generator p) = screen generator p := by
  rcases hgen with rfl | rfl
  · by_cases h : p % 840 ∈ allowed2
    · have h24 := allowed2_shape _ (Nat.mod_lt _ (by decide)) h
      have : p % 24 = 11 := by omega
      simp [Spec.Ffdh.generationShape, screen, hb1, hb2, hbits, h, this]
    · simp [screen, h]
  · by_cases h : p % 420 ∈ allowed5
    · have h10 := allowed5_shape _ (Nat.mod_lt _ (by decide)) h
      have : p % 10 = 3 ∨ p % 10 = 7 := by omega
      simp [Spec.Ffdh.generationShape, screen, hb1, hb2, hbits, h, this]
    · simp [screen, h]

/-- The public generator selector implements `screen`, after the candidate's exact-width proof. -/
theorem generatorCheck_ok {s : State} {B : Addr} {Z w bits generator : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hbits : Spec.RsaKeyGen.bitLength (wv s.mem B (slot w aN) w) = bits)
    (hgen : generator = 2 ∨ generator = 5) (hreg : s.gpr .rdx = BitVec.ofNat 64 generator) :
    WP isa generatorCheck s fun t => t.zf = some (Spec.Ffdh.generationShape bits generator
        (wv s.mem B (slot w aN) w) && screen generator (wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep [.rbx, .r12, .r8, .rsi, .r14, .rax, .rcx, .rdx, .rbp, .r13] s t := by
  rw [screen_shape hb1 hb2 hbits hgen]
  rcases hgen with rfl | rfl
  · unfold generatorCheck
    refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some true ∧ u.mem = s.mem)
      (by xrun [hreg]) rfl) fun u ⟨⟨hz, hm⟩, k⟩ => ?_)
    have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
      by rw [hm]; exact hg.hdr⟩
    refine WP.ite true (by simp [eval, hz]) ?_ (fun h => by simp at h)
    intro _
    exact WP.mono (generator2_ok hgu hZ hw hw') fun t ⟨hz', hm', k'⟩ =>
      ⟨by simpa [screen, hm] using hz', hm'.trans hm, (k.trans k').mono (by decide)⟩
  · unfold generatorCheck
    refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some false ∧ u.mem = s.mem)
      (by xrun [hreg]) rfl) fun u ⟨⟨hz, hm⟩, k⟩ => ?_)
    have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
      by rw [hm]; exact hg.hdr⟩
    refine WP.ite false (by simp [eval, hz]) (fun h => by simp at h) ?_
    intro _
    exact WP.mono (generator5_ok hgu hZ hw hw') fun t ⟨hz', hm', k'⟩ =>
      ⟨by simpa [screen, hm] using hz', hm'.trans hm, (k.trans k').mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
