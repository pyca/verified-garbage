module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdFrame
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddModulus
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
/-! # Complete native GCD stage for the RSA LCM -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyEvenFlag.lean`, which only this module imported.
section

/-! # A secret parity selector for canonicalizing the LCM factors -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem evenFlag_ok {s : State} {B : Addr} {Z n input : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) :
    WP isa (.block (evenFlag n input)) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B n input % 2 = 0 then 1 else 0) ∧ Keeps [.eax] s t := by
  have fit := h.arr_fit hi
  have head := h.hdr_le
  unfold evenFlag
  refine wp_movS (readSrc_sc h.workspace
    (by change arr n input + 4 ≤ Z; unfold S at fit; omega)) fun u U _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v V => ?_
  refine wp_logicS (.inr rfl) rfl fun w W => ?_
  have K : Keeps [.eax] s w := (U.keeps.trans V.keeps).trans W.keeps
  have hw := h.rest K
  have memory : w.mem = s.mem := W.mem.trans (V.mem.trans U.mem)
  have value : w.gpr .eax =
      (s.mem.readW (off B (arr n input)) 32 &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32) := by
    rw [W.gpr, V.gpr, U.gpr]
    rfl
  have numeric : (w.gpr .eax).toNat = if num s.mem B n input % 2 = 0 then 1 else 0 := by
    rw [value, num_parity _ _ h.wpos input]
    have E := even_bit (s.mem.readW (off B (arr n input)) 32) (s.mem.readW (off B (arr n input)) 32)
    simpa only [BitVec.or_self, and_self] using E
  refine wp_storeS (hw.workspace.ea (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    (hw.workspace.write (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    fun t T => WP.block_nil ?_
  refine ⟨hw.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, numeric]

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyOddSecond.lean`, which only this module imported.
section

/-! # Canonicalize the LCM factors by a masked parity swap -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem oddSecond_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (oddSecond n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aU, aV] [kFlag] s.mem t.mem ∧
      num t.mem B n aU = (if num s.mem B n aV % 2 = 0 then num s.mem B n aV else num s.mem B n aU) ∧
      num t.mem B n aV = (if num s.mem B n aV % 2 = 0 then num s.mem B n aU else num s.mem B n aV) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  have fu := h.fit64 (j := aU) (by decide)
  have fv := h.fit64 (j := aV) (by decide)
  have ft := h.fit64 (j := aT1) (by decide)
  unfold oddSecond seqs
  refine WP.seq (WP.mono (evenFlag_ok h (by decide)) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have Uu : num u.mem B n aU = num s.mem B n aU :=
    Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fu
  have Vu : num u.mem B n aV = num s.mem B n aV :=
    Ou.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fv
  refine WP.seq (WP.mono (copy_ok hu (by decide) (by decide)) fun v ⟨hv, Ov, copied, Kv, _⟩ => ?_)
  have Uv : num v.mem B n aU = num s.mem B n aU := by rw [Ov.num (by decide) (by simp) fu, Uu]
  have Vv : num v.mem B n aV = num s.mem B n aV := by rw [Ov.num (by decide) (by simp) fv, Vu]
  have Tv : num v.mem B n aT1 = num s.mem B n aU := copied.trans Uu
  have flagV : slot v.mem B kFlag = slot u.mem B kFlag := Ov.slot hf (by simp)
  have bitV : slot v.mem B kFlag ≤ 1 := by rw [flagV, flag]; split <;> omega_arith
  refine WP.seq (WP.mono (sel_ok hv (by decide) (by decide) (by decide) hf bitV)
    fun w ⟨hw, Ow, selectedU, Kw⟩ => ?_)
  have Vw : num w.mem B n aV = num s.mem B n aV := by rw [Ow.num (by decide) (by simp) fv, Vv]
  have Tw : num w.mem B n aT1 = num s.mem B n aU := by rw [Ow.num (by decide) (by simp) ft, Tv]
  have flagW : slot w.mem B kFlag = slot u.mem B kFlag := by rw [Ow.slot hf (by simp), flagV]
  have bitW : slot w.mem B kFlag ≤ 1 := by rw [flagW, flag]; split <;> omega_arith
  refine WP.mono (sel_ok hw (by decide) (by decide) (by decide) hf bitW)
    fun t ⟨ht, Ot, selectedV, Kt⟩ => ?_
  have U : num t.mem B n aU = if slot u.mem B kFlag = 0 then num s.mem B n aU else num s.mem B n aV := by
    rw [Ot.num (by decide) (by simp) fu, selectedU, flagV, Uv, Vv]
  have V : num t.mem B n aV = if slot u.mem B kFlag = 0 then num s.mem B n aV else num s.mem B n aU := by
    rw [selectedV, flagW, Vw, Tw]
  refine ⟨ht, (((Ou.join Ov (js := [aT1, aU, aV]) (ds := [kFlag])).join Ow
    (js := [aT1, aU, aV]) (ds := [kFlag])).join Ot
    (js := [aT1, aU, aV]) (ds := [kFlag])), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kw.trans Kt))⟩
  · rw [U, flag]
    by_cases p : num s.mem B n aV % 2 = 0 <;> simp [p]
  · rw [V, flag]
    by_cases p : num s.mem B n aV % 2 = 0 <;> simp [p]

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def canonU (u v : Nat) : Nat := if v % 2 = 0 then v else u
def canonV (u v : Nat) : Nat := if v % 2 = 0 then u else v

theorem gcdPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundU : num s.mem B n aU < 2 ^ (32 * k)) (boundV : num s.mem B n aV < 2 ^ (32 * k))
    (odd : 2 ≤ canonV (num s.mem B n aU) (num s.mem B n aV) →
      canonV (num s.mem B n aU) (num s.mem B n aV) % 2 = 1)
    (one : num s.mem B n aOne = 1) :
    WP isa (gcdPart n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (gcdPartRanges n k) s.mem t.mem ∧
      num t.mem B n aDen =
        (if canonV (num s.mem B n aU) (num s.mem B n aV) ≤ 1 then 1 else
          Nat.gcd (canonU (num s.mem B n aU) (num s.mem B n aV))
            (canonV (num s.mem B n aU) (num s.mem B n aV))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let A := num s.mem B n aU
  let C := num s.mem B n aV
  have cbU : canonU A C < 2 ^ (32 * k) := by
    unfold canonU
    split
    · exact boundV
    · exact boundU
  have cbV : canonV A C < 2 ^ (32 * k) := by
    unfold canonV
    split
    · exact boundU
    · exact boundV
  have bound3 : 3 < 2 ^ (32 * k) := by
    have P : 2 ^ 32 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have oddLocal : 2 ≤ canonV A C → canonV A C % 2 = 1 := odd
  have valid : canonV A C % 2 = 1 ∧ 3 ≤ canonV A C ↔ ¬canonV A C ≤ 1 := by
    constructor
    · intro H
      omega
    · intro H
      have O := oddLocal (by omega)
      exact ⟨O, by omega⟩
  unfold gcdPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (oddSecond_ok h) fun u ⟨hu, Ou, U, V, Ku⟩ => ?_)
  change num u.mem B n aU = canonU A C at U
  change num u.mem B n aV = canonV A C at V
  have oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (oddModulus_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, flag, modulus, Kv⟩ => ?_)
  rw [V] at flag modulus
  have Uv : num v.mem B n aU = canonU A C := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), U]
  have oneV : num v.mem B n aOne = 1 := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), oneU]
  have inputBound : num v.mem B n aU < 2 ^ (32 * k) := by rw [Uv]; exact cbU
  have modulusBound : num v.mem B n aDen < 2 ^ (32 * k) := by
    rw [modulus]
    split
    · exact cbV
    · exact bound3
  have modulusOdd : num v.mem B n aDen % 2 = 1 := by
    rw [modulus]
    split
    · next H => exact H.1
    · decide
  have modulusLarge : 1 < num v.mem B n aDen := by rw [modulus]; split <;> omega
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (gcdFrom_ok hv width positive inputBound modulusBound modulusOdd modulusLarge oneV bit)
    fun t ⟨ht, Ot, computed, Kt⟩ => ?_
  refine ⟨ht, ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  · have first : Outs B (gcdPartRanges n k) s.mem u.mem :=
      VG.Proof.Mont.Outs.mono (Ou.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    have middle : Outs B (gcdPartRanges n k) u.mem v.mem :=
      VG.Proof.Mont.Outs.mono (Ov.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    exact (first.trans middle).trans (Ot.mono (fun r hr => List.mem_append_left _ hr))
  · change num t.mem B n aDen = if canonV A C ≤ 1 then 1 else Nat.gcd (canonU A C) (canonV A C)
    rw [computed, flag, Uv, modulus]
    by_cases H : canonV A C ≤ 1
    · have inactive : ¬(canonV A C % 2 = 1 ∧ 3 ≤ canonV A C) := fun P => valid.mp P H
      simp [H, inactive]
    · have active := valid.mpr H
      simp [H, active]

end VG.Proof.RsaKeyGen.X86.Key
