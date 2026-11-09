module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH key generation from the context on i686: the cut at the context's width

`metaCut` sets the cut of `GenerateKey.cut` from the context's public
width and its bytes (`metaCut_ok`): the first byte kept, `ld = p_len − bytes`,
and its mask `2^(width − 8 (bytes − 1)) − 1`, by doubling one that many
times; the cut is then `ScalarWidth.cut_value`'s.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86 VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A 32-bit word of the context, read through `ecx = ctx`. -/
theorem ctxWord_read (C : CtxRd base bytes len args s) (hc : s.gpr .ecx = args ctxArg) {d v : Nat}
    (hd : d + 4 ≤ 24) (hv : w32 s.mem (ctxAddr args) d = v) (hv' : v < 2 ^ 32) :
    readSrc s (.mem ⟨.ecx, d⟩) = some (BitVec.ofNat 32 v) := by
  have afit := C.afit
  have ad : addr (args ctxArg) d = off (ctxAddr args) d := addr_eq (by simp only [ctxBytes] at afit; omega)
  rw [readSrc_mem hc (by rw [ad]; exact (C.row (d := d) (n := 4) (by simp only [ctxBytes]; omega)).read), ad]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv']
  exact hv

/-- The cut's first byte and mask from the context's width `bits` and its bytes. -/
theorem metaHead_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s)
    (h3 : args 3 = BitVec.ofNat 32 len) {bits : Nat} (hb1 : 1 ≤ bits) (hb : bits ≤ 8 * len)
    (w0 : w32 s.mem (ctxAddr args) 0 = bits) (w8 : w32 s.mem (ctxAddr args) 8 = (bits + 7) / 8) :
    WP isa (.block metaHead) s fun u => Step Ex base bytes len args s u ∧
      Kept base len [] [ldOff] s.mem u.mem ∧ w32 u.mem base ldOff = len - (bits + 7) / 8 ∧
      u.gpr .edx = BitVec.ofNat 32 (bits + 8 - 8 * ((bits + 7) / 8)) ∧ u.gpr .eax = BitVec.ofNat 32 1 ∧
      Outside base ldOff 4 s.mem u.mem := by
  have lw := h.lower
  have up := h.upper
  have lo : ldOff = 24 := rfl
  have to : tOff = 28 := rfl
  have wd : VG.Proof.Ffdh.ScalarWidth.width bits = (bits + 7) / 8 := by
    simp only [VG.Proof.Ffdh.ScalarWidth.width]; omega
  have hd : VG.Proof.Ffdh.ScalarWidth.headBits bits = bits + 8 - 8 * ((bits + 7) / 8) := by
    simp only [VG.Proof.Ffdh.ScalarWidth.headBits, wd]; omega
  have hb8 : 1 ≤ bits + 8 - 8 * ((bits + 7) / 8) ∧ bits + 8 - 8 * ((bits + 7) / 8) ≤ 8 := by omega
  unfold metaHead
  refine wp_movS (h.arg (i := ctxArg) (by decide)) fun s₁ U₁ _ => ?_
  have C₁ := C.keep U₁.keeps
  refine wp_movS (ctxWord_read C₁ U₁.gpr (d := 8) (v := (bits + 7) / 8) (by decide) (by rw [U₁.mem]; exact w8) (by omega))
    fun s₂ U₂ _ => ?_
  have h₂ := h.regs ((U₁.keeps.mono (by decide)).widen U₂.keeps : Keeps [.eax, .ecx] s s₂) (by rw [U₂.mem, U₁.mem])
  refine wp_movS (h₂.arg (i := 3) (by decide)) fun s₃ U₃ _ => wp_subS rfl fun s₄ U₄ _ => ?_
  have K₄ : Keeps [.eax, .ecx, .edx] s s₄ :=
    (((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps).widen U₄.keeps
  have m₄ : s₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have h₄ := h.regs K₄ m₄
  have e₄ : s₄.gpr .edx = BitVec.ofNat 32 (len - (bits + 7) / 8) := by
    rw [U₄.gpr, U₃.gpr, h3, U₃.other _ (by decide), U₂.gpr,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine wp_storeS (h₄.scratch.ea (d := ldOff) (by omega)) (h₄.scratch.write (d := ldOff) (n := 4) (by omega))
    fun s₅ M₅ => ?_
  have O₅ : Outside base ldOff 4 s.mem s₅.mem := by rw [M₅.mem, m₄]; exact writeW32_outside _ _ _ (by omega)
  have W₅ : w32 s₅.mem base ldOff = len - (bits + 7) / 8 := by
    rw [M₅.mem, w32_write_self, e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have K₅ : Keeps [.eax, .ecx, .edx] s s₅ := K₄.trans ((M₅.keeps []).mono (by decide))
  have C₅ := C.keep K₅
  have ecx₅ : s₅.gpr .ecx = args ctxArg := by
    rw [M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr]
  have eax₅ : s₅.gpr .eax = BitVec.ofNat 32 ((bits + 7) / 8) := by
    rw [M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide), U₂.gpr]
  have w0₅ : w32 s₅.mem (ctxAddr args) 0 = bits := by
    rw [← w32_val32_one, val32_far (Outside.frame_span O₅ (by have := h.scratch.nowrap; omega))
      (fun r hr => ?_) (by decide), w32_val32_one, w0]
    obtain rfl := List.mem_singleton.mp hr
    exact (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega))).sub_right
      (Offset.sub_base _ (by omega))
  have h₅ := h.keep K₅ (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by omega))
  refine wp_addS rfl fun s₆ U₆ _ => wp_addS rfl fun s₇ U₇ _ => wp_addS rfl fun s₈ U₈ _ => ?_
  have K₅₈ : Keeps [.eax] s₅ s₈ := ((U₆.keeps.mono (by decide)).widen U₇.keeps).widen U₈.keeps
  have m₅₈ : s₈.mem = s₅.mem := by rw [U₈.mem, U₇.mem, U₆.mem]
  have eax₈ : s₈.gpr .eax = BitVec.ofNat 32 (8 * ((bits + 7) / 8)) := by
    rw [U₈.gpr, U₇.gpr, U₆.gpr, eax₅]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have ecx₈ : s₈.gpr .ecx = args ctxArg := by rw [K₅₈.1 _ (by decide), ecx₅]
  refine wp_movS (ctxWord_read (C₅.keep K₅₈) ecx₈ (d := 0) (v := bits) (by decide) (by rw [m₅₈]; exact w0₅)
    (by omega)) fun s₉ U₉ _ => wp_subS rfl fun s₁₀ U₁₀ _ => wp_addS rfl fun s₁₁ U₁₁ _ =>
      wp_movS rfl fun s₁₂ U₁₂ _ => WP.block_nil ?_
  have edx₁₂ : s₁₂.gpr .edx = BitVec.ofNat 32 (bits + 8 - 8 * ((bits + 7) / 8)) := by
    rw [U₁₂.other _ (by decide), U₁₁.gpr, U₁₀.gpr, U₉.gpr, U₉.other _ (by decide), eax₈]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (8 : BitVec 32) = 8 from rfl]
    omega
  have eax₁₂ : s₁₂.gpr .eax = BitVec.ofNat 32 1 := U₁₂.gpr
  have K₅₁₂ : Keeps [.eax, .ecx, .edx] s₅ s₁₂ := (K₅₈.mono (by decide)).trans
    ((((U₉.keeps.mono (by decide)).widen U₁₀.keeps).widen U₁₁.keeps).widen U₁₂.keeps)
  have m₁₂ : s₁₂.mem = s₅.mem := by rw [U₁₂.mem, U₁₁.mem, U₁₀.mem, U₉.mem, m₅₈]
  have K₁₂ : Keeps [.eax, .ecx, .edx] s s₁₂ := K₅.trans K₅₁₂
  have O₁₂ : Outside base ldOff 4 s.mem s₁₂.mem := by rw [m₁₂]; exact O₅
  refine ⟨Step.word h (d := ldOff) (by decide) O₁₂ K₁₂, (kept_word h (d := ldOff) (by decide) (by decide) O₁₂).mono,
    by rw [m₁₂]; exact W₅, edx₁₂, eax₁₂, O₁₂⟩

theorem metaCut_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s)
    (h3 : args 3 = BitVec.ofNat 32 len) {bits : Nat} (hb1 : 1 ≤ bits) (hb : bits ≤ 8 * len)
    (w0 : w32 s.mem (ctxAddr args) 0 = bits) (w8 : w32 s.mem (ctxAddr args) 8 = (bits + 7) / 8) :
    WP isa Generate.metaCut s fun u => Step Ex base bytes len args s u ∧
      Kept base len [] [ldOff, tOff] s.mem u.mem ∧
      w32 u.mem base ldOff = len - VG.Proof.Ffdh.ScalarWidth.width bits ∧
      w32 u.mem base tOff = (VG.Proof.Ffdh.ScalarWidth.mask bits).toNat := by
  have lw := h.lower
  have up := h.upper
  have lo : ldOff = 24 := rfl
  have to : tOff = 28 := rfl
  have wd : VG.Proof.Ffdh.ScalarWidth.width bits = (bits + 7) / 8 := by
    simp only [VG.Proof.Ffdh.ScalarWidth.width]; omega
  have hd : VG.Proof.Ffdh.ScalarWidth.headBits bits = bits + 8 - 8 * ((bits + 7) / 8) := by
    simp only [VG.Proof.Ffdh.ScalarWidth.headBits, wd]; omega
  have hb8 : 1 ≤ bits + 8 - 8 * ((bits + 7) / 8) ∧ bits + 8 - 8 * ((bits + 7) / 8) ≤ 8 := by omega
  unfold Generate.metaCut
  refine WP.seq (WP.mono (metaHead_ok h C h3 hb1 hb w0 w8) fun s₁₂ ⟨S₅, k₅, W₅, edx₁₂, eax₁₂, _⟩ => ?_)
  have h₅ := S₅.inp
  generalize hN : bits + 8 - 8 * ((bits + 7) / 8) = N at edx₁₂ hb8 hd
  refine WP.seq (WP.mono (VG.Proof.Ffdh.X86.KeyScan.count_loop (n := N) (by omega)
    (fun j t => t.gpr .eax = BitVec.ofNat 32 (2 ^ j) ∧ t.gpr .edx = BitVec.ofNat 32 (N - j) ∧ t.mem = s₁₂.mem ∧
      Keeps [.eax, .edx] s₁₂ t) (fun j hj t ⟨ea, ed, mt, Kt⟩ => ?_) ⟨by simpa using eax₁₂, by simpa using edx₁₂,
      rfl, Keeps.refl _ _⟩) fun t ⟨ea, _, mt, Kt⟩ => ?_)
  · refine wp_addS rfl fun t₁ V₁ _ => wp_subZ rfl fun t₂ V₂ z₂ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [V₂.other _ (by decide), V₁.gpr, ea, BitVec.ofNat_add_ofNat, Nat.pow_succ, Nat.mul_two]
    · rw [V₂.gpr, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), Nat.sub_sub]
    · rw [V₂.mem, V₁.mem, mt]
    · exact Kt.trans ((V₁.keeps.mono (by decide)).widen V₂.keeps)
    · rw [z₂, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1
      by_cases e : j + 1 = N
      · simp [e, show N - j - 1 = 0 by omega]
      · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro c
        have := congrArg BitVec.toNat c
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
  · refine wp_subS rfl fun t₁ V₁ _ => ?_
    have K₅₁ : Keeps [.eax, .ecx, .edx] s₁₂ t₁ := (Kt.mono (by decide)).trans (V₁.keeps.mono (by decide))
    have m₁ : t₁.mem = s₁₂.mem := by rw [V₁.mem, mt]
    have h₁ : In Ex base bytes len args t₁ := h₅.regs K₅₁ m₁
    have p8 : 2 ^ N ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hb8.2
    have eax₁ : t₁.gpr .eax = BitVec.ofNat 32 (2 ^ N - 1) := by
      rw [V₁.gpr, ea, VG.Proof.Mont.X86.Dynamic.counter_sub (by omega) (Nat.two_pow_pos N)]
    refine WP.mono (storeW_ok h₁ (d := tOff) (by decide) .eax) fun u ⟨I, O, W, K⟩ => ⟨?_, ?_, ?_, ?_⟩
    · rw [m₁] at O
      exact S₅.trans (Step.word h₅ (d := tOff) (by decide) O (K₅₁.trans (K.mono (by decide))))
    · rw [m₁] at O
      exact k₅.mono.trans (kept_word h₅ (d := tOff) (by decide) (by decide) O).mono
    · rw [O.w32 (by decide) (by decide), m₁, W₅, wd]
    · rw [W, eax₁, VG.Proof.Ffdh.ScalarWidth.mask_toNat, hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end

end VG.Proof.Ffdh.X86.Cached
