module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HeaderRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderFrame

import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderLayout
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderRead
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.RsaKeyGen.X86.InverseLift
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Impl.RsaKeyGen.X86.InverseLift
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
import VerifiedGarbage.Proof.Mont.X86.Inverse
/-! # A fresh candidate reaches the existing prepared Montgomery contract -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderContext.lean`, which only this module imported.
section

/-! # The public header prepares the native callable Miller–Rabin context -/

section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86

theorem low_word (m : Mem) (base : Addr) (d : Nat) : w32 m base d = (word m base d).toNat % 2 ^ 32 := by
  rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW (off base d) 32).isLt]

/-- The context and frame of any code that writes the header's memory. -/
theorem context_of {g : Geometry} (v : g.Valid) {s t : State} (scratch : Scr s g.W g.L) {rs : List Reg}
    (K : Keeps rs s t) (edi : .edi ∉ rs) (M : t.mem = headerMemory g.W (s.gpr .edi) g.w s.mem) :
    Context g t ∧ Outs g.W ranges s.mem t.mem := by
  have wBound : g.w < 2 ^ 32 := by have := v.maxWidth; omega
  have strideBound : VG.Impl.Bignum.X86.PublicContext.stride g.w < 2 ^ 32 := by
    have := v.maxWidth
    unfold VG.Impl.Bignum.X86.PublicContext.stride
    omega
  have baseBound : g.W.toNat < 2 ^ 32 := by have := scratch.nowrap; have := v.headerFit; omega
  refine ⟨⟨⟨K.2.2 ▸ scratch.wr, scratch.nowrap⟩, ?_, ?_, ?_, ?_⟩, M ▸ header_frame⟩
  · rw [PtrAt, K.1 .edi edi, scratch.edi_toNat, Nat.add_zero, Nat.mod_eq_of_lt baseBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_width, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt wBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_stride, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt strideBound]
    rfl
  · intro j index
    rw [M, low_word, VG.Proof.Mont.word, header_pointer index, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      Nat.mod_eq_of_lt (s.gpr .edi + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot g.w j)).isLt,
      BitVec.toNat_add, BitVec.toNat_ofNat, scratch.edi_toNat, Prepared.slot_eq]
    omega

theorem context_ok {g : Geometry} (v : g.Valid) {s : State} (scratch : Scr s g.W g.L) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Header.code g.w)) s fun t =>
      Context g t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps [.eax, .edx] s t ∧
      t.mem = headerMemory g.W (s.gpr .edi) g.w s.mem :=
  WP.mono (code_ok scratch v.headerFit) fun _ ⟨M, K⟩ =>
    ⟨(context_of v scratch K (by decide) M).1, (context_of v scratch K (by decide) M).2, K, M⟩

end VG.Proof.RsaKeyGen.X86.Header
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/InverseSetup.lean`, which only this module imported.
section

/-! # Complete the prepared workspace's 64-bit negative inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.RsaKeyGen.X86.InverseLift

theorem setup_ok {s : State} {base : Addr} {size mo inv : Nat}
    (scratch : Scr s base size) (modulus : mo + 8 ≤ size) (slot : inv + 8 ≤ size)
    (inverse : (w32 s.mem base mo * w32 s.mem base inv + 1) % 2 ^ 32 = 0) :
    WP isa (.block (setup mo inv)) s fun t =>
      ((w32 s.mem base mo + 2 ^ 32 * w32 s.mem base (mo + 4)) *
        (w32 s.mem base inv + 2 ^ 32 * w32 t.mem base (inv + 4)) + 1) % 2 ^ 64 = 0 ∧
      Outside base (inv + 4) 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold setup
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (by omega)) fun b B _ => ?_
  have Kb : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_movS (readSrc_sc Sb (by omega)) fun c C _ => ?_
  have lo : c.gpr .ebx = s.mem.readW (off base mo) 32 := by
    rw [C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]
  have hi : c.gpr .esi = s.mem.readW (off base (mo + 4)) 32 := by
    rw [C.other .esi (by decide), B.gpr, A.mem]
  have ix : c.gpr .ecx = s.mem.readW (off base inv) 32 := by
    rw [C.gpr, B.mem, A.mem]
  refine WP.block_append (WP.mono (inverse_ok c (by rw [lo, ix]; exact inverse)) fun d ⟨value, mem, Kd⟩ => ?_)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.widen C.keeps).widen Kd
  have Sd := scratch.of_keeps K (by decide)
  refine wp_storeS (Sd.ea (by omega)) (Sd.write (by omega)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self]
    rw [Kd.1 .ecx (by decide), lo, hi, ix] at value
    exact value
  · rw [T.mem, mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

end VG.Proof.RsaKeyGen.X86.InverseLift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MontInverse.lean`, which only this module imported.
section

/-! # The compact prepared kernel receives the reviewed full 64-bit inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.MontInverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.MontInverse

theorem code_ok {s : State} {base : Addr} {size modulus inverse : Nat} (scratch : Scr s base size)
    (modFit : modulus + 8 ≤ size) (invFit : inverse + 8 ≤ size)
    (apart : inverse + 8 ≤ modulus ∨ modulus + 8 ≤ inverse) (odd : w32 s.mem base modulus % 2 = 1) :
    WP isa (code modulus inverse) s fun t =>
      ((word t.mem base modulus).toNat * (word t.mem base inverse).toNat + 1) % 2 ^ 64 = 0 ∧
      Outside base inverse 8 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok scratch (by omega) (by omega) odd)
    fun a ⟨inverseA, Oa, Ka⟩ => ?_)
  have low : (w32 a.mem base modulus * w32 a.mem base inverse + 1) % 2 ^ 32 = 0 := by
    rw [Oa.w32 (by omega) (by have := scratch.nowrap; omega)]
    exact inverseA
  refine WP.mono (InverseLift.setup_ok (scratch.of_keeps Ka (by decide)) modFit invFit low)
    fun t ⟨inverseT, Ot, Kt⟩ => ?_
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), ?_⟩
  · rw [word_eq_w32, word_eq_w32,
      Ot.w32 (d := modulus) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := modulus + 4) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := inverse) (by omega) (by have := scratch.nowrap; omega)]
    exact inverseT
  · exact (Ka.mono (by decide)).trans Kt

end VG.Proof.RsaKeyGen.X86.MontInverse
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareHeader
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2

def ranges : List (Nat × Nat) := Header.ranges ++ [(56, 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

/-- The header written by any code that writes `Header.code`'s memory, then the inverse. -/
theorem codeWith_ok {hdr : List Instr} {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat}
    {p : BitVec 32} (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1)
    (header : WP isa (.block hdr) s fun t =>
      t.mem = Header.headerMemory g.W (s.gpr .edi) g.w s.mem ∧ Keeps [.eax, .ecx, .edx] s t) :
    WP isa (.seq (.block hdr) (VG.Impl.RsaKeyGen.X86.MontInverse.code (g.array 0) 56)) s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  refine WP.seq (WP.mono header fun a ⟨Ma, Ka⟩ => ?_)
  obtain ⟨Ca, Oa⟩ := Header.context_of v scratch Ka (by decide) Ma
  have Sa := scratch.of_keeps Ka (by decide)
  have candidateA : val32 a.mem g.W (g.array 0) g.words = c := by
    rw [Oa.val32 (fun r mem => by
      simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      have h := v.arrayHeader 0
      rcases mem with rfl | rfl | rfl <;> right <;> omega)
      (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega)]
    exact candidate
  have oddLow : w32 a.mem g.W (g.array 0) % 2 = 1 := by
    rw [← LowWord.parity _ _ _ g.words (by have := v.minWidth; unfold Geometry.words; omega), candidateA]
    exact odd
  have callerA := caller.keepOuts Ka (by decide) Oa (fun r mem => by
    simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    have := v.headerFit
    rcases mem with rfl | rfl | rfl <;> omega)
  have widthA : Proof.Rsa.Mont.wOf a.mem g.W = g.w := by
    rw [Ma]
    exact Header.width_eq (by have := v.maxWidth; omega)
  have layoutA : Proof.Rsa.Mont.Layout a.mem g.W capacity := by
    rw [Ma]
    apply Header.layout scratch.edi (by have := v.minWidth; omega) (by have := v.maxWidth; omega)
    · rw [← length]
      have fit := v.arraysFit
      unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at *
      omega
    · rw [← length]
      exact scratch.nowrap
  refine WP.mono (MontInverse.code_ok Sa
    (by have := v.arrayFit (j := 0) (by decide); have := v.minWidth; unfold Geometry.words at *; omega)
    (by have := v.headerFit; omega) (Or.inl (by have := v.arrayHeader 0; omega)) oddLow)
    fun t ⟨inverse, Ot, Kt⟩ => ?_
  have St := Sa.of_keeps Kt (by decide)
  have Ct : Context g t := by
    refine ⟨Ca.ws.of_keeps Kt, ?_, ?_, ?_, ?_⟩
    · rw [PtrAt, Kt.1 .edi (by decide)]; exact Ca.base
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.width
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.stride
    · intro j hj
      rw [Ot.w32 (by omega) (by omega)]; exact Ca.pointers j hj
  have Mt : Modulus g c t.mem := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (word t.mem g.W 48).toNat = g.w
      rw [Ot.word (by decide) (by decide)]
      exact widthA
    · intro j hj
      change word t.mem g.W (8 * Proof.Rsa.Mont.arrWord j) = _
      rw [Ot.word (Or.inr (by unfold Proof.Rsa.Mont.arrWord; omega)) (by unfold Proof.Rsa.Mont.arrWord; omega)]
      simpa only [widthA, Geometry.array, VG.Proof.Mont.word, VG.Proof.Mont.off, Proof.Rsa.Mont.wordAt] using layoutA.2.2.2 j hj
    · rw [Ot.val32 (Or.inr (by have := v.arrayHeader 0; omega))
        (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega)]
      exact candidateA
    · exact inverse
  refine ⟨⟨Ct, Mt, callerA.keepOuts Kt (by decide) (Outs.of_outside Ot (List.mem_singleton_self _))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; omega), St⟩, ?_, ?_, ?_⟩
  · exact (Oa.mono (fun r mem => List.mem_append_left _ mem)).trans
      (Outs.of_outside Ot (List.mem_append_right _ (List.mem_singleton_self _)))
  · exact (Ka.mono (by unfold clob; decide)).trans Kt
  · rw [Ot.word (by decide) (by decide), Ma]
    change (Header.headerMemory g.W (s.gpr .edi) g.w s.mem).readW (off g.W 224) 64 = _
    rw [Header.header_stride, Header.zeroHigh]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, VG.Impl.Bignum.X86.PublicContext.stride]
    have := v.maxWidth
    omega

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1) :
    WP isa (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w) s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  unfold VG.Impl.RsaKeyGen.X86.PrepareHeader.code
  rw [Prepared.slot_eq]
  exact codeWith_ok v scratch caller length candidate odd
    (WP.mono (Header.code_ok scratch v.headerFit) fun _ ⟨M, K⟩ => ⟨M, K.mono (by decide)⟩)

/-- `HeaderRt.prepare`: the header at the width that header byte 4 gives. -/
theorem prepareRt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1)
    (len : s.mem.readW (off g.W 4) 32 = BitVec.ofNat 32 (8 * g.w)) :
    WP isa VG.Impl.RsaKeyGen.X86.HeaderRt.prepare s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  have base : g.array 0 = 256 := by
    simp [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  unfold VG.Impl.RsaKeyGen.X86.HeaderRt.prepare
  rw [← base]
  exact codeWith_ok v scratch caller length candidate odd
    (HeaderRt.code_ok scratch v.headerFit v.maxWidth len)

end VG.Proof.RsaKeyGen.X86.PrepareHeader
