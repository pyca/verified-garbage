module

public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Proof.Ffdh.CachedSat
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenCT
import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGenCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
meta import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.ContextRows
meta import VerifiedGarbage.Proof.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Mont.X86.PowerInit
meta import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
meta import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.X86.Ops
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
meta import VerifiedGarbage.Proof.Ffdh.ScalarWidth
meta import VerifiedGarbage.Proof.Ffdh.X86.Stages
meta import VerifiedGarbage.Proof.Mont.X86.PowerInit

/-! ### `Ffdh.X86.Cached.AttemptCT`, which only this module used -/

section

/-! ### `Ffdh.X86.Cached.AttemptTop`, which only this module used -/

section

/-! ### `Ffdh.X86.Cached.MetaCut`, which this module and modules that import it used -/

section

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
  obtain ad : addr (args ctxArg) d = off (ctxAddr args) d := addr_eq (by simp only [ctxBytes] at afit; omega_using [hd, afit])
  rw [readSrc_mem hc (by rw [ad]; exact (C.row (d := d) (n := 4) (by simp only [ctxBytes]; omega_using [hd])).read), ad]
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
    simp only [VG.Proof.Ffdh.ScalarWidth.width]; omega_using [hb1]
  have hd : VG.Proof.Ffdh.ScalarWidth.headBits bits = bits + 8 - 8 * ((bits + 7) / 8) := by
    simp only [VG.Proof.Ffdh.ScalarWidth.headBits, wd]; omega_using [hb1]
  have hb8 : 1 ≤ bits + 8 - 8 * ((bits + 7) / 8) ∧ bits + 8 - 8 * ((bits + 7) / 8) ≤ 8 := by omega_using []
  unfold metaHead
  refine wp_movS (h.arg (i := ctxArg) (by decide)) fun s₁ U₁ _ => ?_
  have C₁ := C.keep U₁.keeps
  refine wp_movS (ctxWord_read C₁ U₁.gpr (d := 8) (v := (bits + 7) / 8) (by decide) (by rw [U₁.mem]; exact w8) (by omega_using [hb, up]))
    fun s₂ U₂ _ => ?_
  have h₂ := h.regs ((U₁.keeps.mono (by decide)).widen U₂.keeps : Keeps [.eax, .ecx] s s₂) (by rw [U₂.mem, U₁.mem])
  refine wp_movS (h₂.arg (i := 3) (by decide)) fun s₃ U₃ _ => wp_subS rfl fun s₄ U₄ _ => ?_
  have K₄ : Keeps [.eax, .ecx, .edx] s s₄ :=
    (((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps).widen U₄.keeps
  have m₄ : s₄.mem = s.mem := by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have h₄ := h.regs K₄ m₄
  have e₄ : s₄.gpr .edx = BitVec.ofNat 32 (len - (bits + 7) / 8) := by
    rw [U₄.gpr, U₃.gpr, h3, U₃.other _ (by decide), U₂.gpr,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hb, up]) (by omega_using [hb])]
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine wp_storeS (h₄.scratch.ea (d := ldOff) (by omega_using [lo, nd, en, nb])) (h₄.scratch.write (d := ldOff) (n := 4) (by omega_using [lo, nd, en, nb]))
    fun s₅ M₅ => ?_
  have O₅ : Outside base ldOff 4 s.mem s₅.mem := by rw [M₅.mem, m₄]; exact writeW32_outside _ _ _ (by omega_using [lo])
  have W₅ : w32 s₅.mem base ldOff = len - (bits + 7) / 8 := by
    rw [M₅.mem, w32_write_self, e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [up])]
  have K₅ : Keeps [.eax, .ecx, .edx] s s₅ := K₄.trans ((M₅.keeps []).mono (by decide))
  have C₅ := C.keep K₅
  have ecx₅ : s₅.gpr .ecx = args ctxArg := by
    rw [M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr]
  have eax₅ : s₅.gpr .eax = BitVec.ofNat 32 ((bits + 7) / 8) := by
    rw [M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide), U₂.gpr]
  have w0₅ : w32 s₅.mem (ctxAddr args) 0 = bits := by
    rw [← w32_val32_one, val32_far (Outside.frame_span O₅ (by have := h.scratch.nowrap; omega_using [lo, this]))
      (fun r hr => ?_) (by decide), w32_val32_one, w0]
    obtain rfl := List.mem_singleton.mp hr
    exact (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega_using []))).sub_right
      (Offset.sub_base _ (by omega_using [lo, nd, en, nb]))
  have h₅ := h.keep K₅ (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by omega_using [lo, nd, en, nb]))
  refine wp_addS rfl fun s₆ U₆ _ => wp_addS rfl fun s₇ U₇ _ => wp_addS rfl fun s₈ U₈ _ => ?_
  have K₅₈ : Keeps [.eax] s₅ s₈ := ((U₆.keeps.mono (by decide)).widen U₇.keeps).widen U₈.keeps
  have m₅₈ : s₈.mem = s₅.mem := by rw [U₈.mem, U₇.mem, U₆.mem]
  have eax₈ : s₈.gpr .eax = BitVec.ofNat 32 (8 * ((bits + 7) / 8)) := by
    rw [U₈.gpr, U₇.gpr, U₆.gpr, eax₅]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using []
  have ecx₈ : s₈.gpr .ecx = args ctxArg := by rw [K₅₈.1 _ (by decide), ecx₅]
  refine wp_movS (ctxWord_read (C₅.keep K₅₈) ecx₈ (d := 0) (v := bits) (by decide) (by rw [m₅₈]; exact w0₅)
    (by omega_using [hb, up])) fun s₉ U₉ _ => wp_subS rfl fun s₁₀ U₁₀ _ => wp_addS rfl fun s₁₁ U₁₁ _ =>
      wp_movS rfl fun s₁₂ U₁₂ _ => WP.block_nil ?_
  have edx₁₂ : s₁₂.gpr .edx = BitVec.ofNat 32 (bits + 8 - 8 * ((bits + 7) / 8)) := by
    rw [U₁₂.other _ (by decide), U₁₁.gpr, U₁₀.gpr, U₉.gpr, U₉.other _ (by decide), eax₈]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (8 : BitVec 32) = 8 from rfl]
    omega_using []
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
  obtain wd : VG.Proof.Ffdh.ScalarWidth.width bits = (bits + 7) / 8 := by
    simp only [VG.Proof.Ffdh.ScalarWidth.width]; omega_using [hb1]
  obtain hd : VG.Proof.Ffdh.ScalarWidth.headBits bits = bits + 8 - 8 * ((bits + 7) / 8) := by
    simp only [VG.Proof.Ffdh.ScalarWidth.headBits, wd]; omega_using [hb1]
  obtain hb8 : 1 ≤ bits + 8 - 8 * ((bits + 7) / 8) ∧ bits + 8 - 8 * ((bits + 7) / 8) ≤ 8 := by omega_using []
  unfold Generate.metaCut
  refine WP.seq (WP.mono (metaHead_ok h C h3 hb1 hb w0 w8) fun s₁₂ ⟨S₅, k₅, W₅, edx₁₂, eax₁₂, _⟩ => ?_)
  have h₅ := S₅.inp
  generalize hN : bits + 8 - 8 * ((bits + 7) / 8) = N at edx₁₂ hb8 hd
  refine WP.seq (WP.mono (VG.Proof.Ffdh.X86.KeyScan.count_loop (n := N) (by omega_using [hN])
    (fun j t => t.gpr .eax = BitVec.ofNat 32 (2 ^ j) ∧ t.gpr .edx = BitVec.ofNat 32 (N - j) ∧ t.mem = s₁₂.mem ∧
      Keeps [.eax, .edx] s₁₂ t) (fun j hj t ⟨ea, ed, mt, Kt⟩ => ?_) ⟨by simpa using eax₁₂, by simpa using edx₁₂,
      rfl, Keeps.refl _ _⟩) fun t ⟨ea, _, mt, Kt⟩ => ?_)
  · refine wp_addS rfl fun t₁ V₁ _ => wp_subZ rfl fun t₂ V₂ z₂ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [V₂.other _ (by decide), V₁.gpr, ea, BitVec.ofNat_add_ofNat, Nat.pow_succ, Nat.mul_two]
    · rw [V₂.gpr, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hj]), Nat.sub_sub]
    · rw [V₂.mem, V₁.mem, mt]
    · exact Kt.trans ((V₁.keeps.mono (by decide)).widen V₂.keeps)
    · rw [z₂, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hj])]
      congr 1
      by_cases e : j + 1 = N
      · simp [e, show N - j - 1 = 0 by omega_using [e]]
      · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro c
        have := congrArg BitVec.toNat c
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hN])] at this
        simp at this; omega_using [h3, hb1, hb, w0, w8, lw, up, lo, to, wd, W₅, eax₁₂, hN, edx₁₂, hb8, hd, hj, ea, ed, e, c, this]
  · refine wp_subS rfl fun t₁ V₁ _ => ?_
    obtain K₅₁ : Keeps [.eax, .ecx, .edx] s₁₂ t₁ := (Kt.mono (by decide)).trans (V₁.keeps.mono (by decide))
    obtain m₁ : t₁.mem = s₁₂.mem := by rw [V₁.mem, mt]
    obtain h₁ : In Ex base bytes len args t₁ := h₅.regs K₅₁ m₁
    obtain p8 : 2 ^ N ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hb8.2
    obtain eax₁ : t₁.gpr .eax = BitVec.ofNat 32 (2 ^ N - 1) := by
      rw [V₁.gpr, ea, VG.Proof.Mont.X86.Dynamic.counter_sub (by omega_using [p8]) (Nat.two_pow_pos N)]
    refine WP.mono (storeW_ok h₁ (d := tOff) (by decide) .eax) fun u ⟨I, O, W, K⟩ => ⟨?_, ?_, ?_, ?_⟩
    · rw [m₁] at O
      exact S₅.trans (Step.word h₅ (d := tOff) (by decide) O (K₅₁.trans (K.mono (by decide))))
    · rw [m₁] at O
      exact k₅.mono.trans (kept_word h₅ (d := tOff) (by decide) (by decide) O).mono
    · rw [O.w32 (by decide) (by decide), m₁, W₅, wd]
    · rw [W, eax₁, VG.Proof.Ffdh.ScalarWidth.mask_toNat, hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [p8])]

end

end VG.Proof.Ffdh.X86.Cached

end

end

/-! # `vg_ffdh_generate_key_cached` on i686 against its contract -/

@[expose] public section

/-!
# FFDH key generation from the context on i686: the attempt's body

`body_ok`: `vg_ffdh_generate_key`'s body with the cut at the context's
public width (`metaCut`, by `KeyGen.prefixWith_ok`) and y by the context's
comb (`comb`, by `KeyGen.tailWith_ok`), for a valid domain and its context.
-/

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.KeyGen
open VG.Impl.Ffdh.X86 VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate

/-- The context's public words and entries, for the width `bits`, p `P` and g `G`. -/
structure CtxVals (len : Nat) (args : Nat → BitVec 32) (P G bits : Nat) (m : Mem) : Prop where
  w0 : w32 m (ctxAddr args) 0 = bits
  w8 : w32 m (ctxAddr args) 8 = (bits + 7) / 8
  w16 : w32 m (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows bits
  ents : ∀ e < 32, val32 m (ctxAddr args) (24 + bc len .wide * (2 + e)) (cwc len .wide) =
    Spec.Rsa.powMod G (Spec.Rsa.FixedBaseComb.exponent bits e) P * 2 ^ (8 * bc len .wide) % P

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The context's values through writes apart from it. -/
theorem CtxVals.keep {P G bits : Nat} {m m' : Mem} (V : CtxVals len args P G bits m) {rs : List Region}
    (F : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ r)
    (hn : ctxBytes len < 2 ^ 64) : CtxVals len args P G bits m' := by
  obtain bw := bc_eq_cwc len .wide
  obtain far : ∀ {d N : Nat}, d + 4 * N ≤ ctxBytes len → val32 m' (ctxAddr args) d N = val32 m (ctxAddr args) d N :=
    fun {d N} h => val32_far F (fun r hr => (hd r hr).sub_left (Offset.sub_base _ h)) (by omega_using [hn, h])
  obtain w : ∀ {d : Nat}, d + 4 ≤ ctxBytes len → w32 m' (ctxAddr args) d = w32 m (ctxAddr args) d := fun {d} h => by
    rw [← w32_val32_one, ← w32_val32_one]; exact far (by omega_using [h])
  refine ⟨by rw [w (by simp only [ctxBytes]; omega_using [])]; exact V.w0, by rw [w (by simp only [ctxBytes]; omega_using [])]; exact V.w8,
    by rw [w (by simp only [ctxBytes]; omega_using [])]; exact V.w16, fun e he => ?_⟩
  have : bc len .wide * (2 + e) + bc len .wide ≤ bc len .wide * 34 := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_using [he])
  rw [far (by simp only [ctxBytes]; omega_using [bw, this])]; exact V.ents e he

/-- The context is apart from the working space's frame. -/
theorem ctx_frameR (C : CtxRd base bytes len args s) {sp : BitVec 32}
    (hstk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below sp 96)) {ws : List (Nat × Nat)}
    (hws : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    ∀ r ∈ frameR base sp ws, Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ r := by
  intro r hr
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact hstk
  · exact C.apart.sub_right (Offset.sub_base _ (hws p hp))

/-- The comb as a stage computing y into slot 6. -/
theorem combStage_ok (h : In Ex base bytes len args s) {P G x bits : Nat}
    (E : CombEnv Ex base bytes len args P G x bits s)
    (hP : safeM (sv s.mem base len .wide 9) = P) (hx : x < 2 ^ bits) (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hrows : w32 s.mem (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa Generate.comb s fun u => Step Ex base bytes len args s u ∧
      Kept base len [] [rowsOff, iOff] s.mem u.mem ∧ sv u.mem base len .wide 6 = Spec.Rsa.powMod G x P := by
  refine WP.mono (comb_ok h E hP hx hR hrows) fun u ⟨C, Y, _, F, K⟩ => ?_
  obtain inF : ∀ p ∈ combR len, InF len p := by
    obtain hs := stR_inF h
    have nb : numBase = 3336 := rfl
    have hn := h.need
    have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
    intro p hp
    simp only [combR, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact .inr ⟨by simp only [rowsOff]; omega_using [], by simp only [rowsOff]; omega_using [nb, en]⟩
    · exact .inr ⟨by simp only [iOff]; omega_using [], by simp only [iOff]; omega_using [nb, en]⟩
    · exact hs p (by simpa only [stR, List.mem_cons, List.not_mem_nil, or_false] using hp)
  refine ⟨⟨C.inp, fR_widen F inF, K⟩, ⟨fun j a b _ => combR_sv h F h.room a b, fun d a b c hd => ?_⟩, Y⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  exact combR_w32 h F h.room a b c hd.1 hd.2

end

/-! ## The body -/

/-- What the contract asks of the status and the outputs. -/
def CachedKeyPost (len dlen : Nat) (m : Mem) (args : Nat → BitVec 32) (r : Nat) (m' : Mem) : Prop :=
  let a := CheckPrivate.params m args len dlen
  let x := Spec.Ffdh.vettedScalarOfOctets a (Spec.Rsa.bytesAt m (byteAddr (args 10)) len)
  r = Spec.Ffdh.keyStatus a x ∧
    if Spec.Ffdh.keyStatus a x = 1 then
      Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = Spec.Rsa.i2osp x len ∧
        Spec.Rsa.bytesAt m' (byteAddr (args 8)) len = Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) len
    else Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = List.replicate len 0 ∧
      Spec.Rsa.bytesAt m' (byteAddr (args 8)) len = List.replicate len 0

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The width's cut of `rand` is the vetted scalar. -/
theorem cut_vetted {m : Mem} {bits : Nat} (hb : bits ≤ 8 * len) (hl : 0 < len) :
    cutOf m args len (len - VG.Proof.Ffdh.ScalarWidth.width bits) (VG.Proof.Ffdh.ScalarWidth.mask bits) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 10)) len) % 2 ^ bits := by
  have := VG.Proof.Ffdh.ScalarWidth.cut_value (r := Spec.Rsa.bytesAt m (byteAddr (args 10)) len) (bits := bits)
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hl) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hb)
  rw [VG.Proof.Bignum.bytesAt_length] at this
  exact this

theorem body_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (C : KeyCut.CutGeo base bytes len (args 10) (args 0) (s.gpr .esp) s.rd s.wr)
    (rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩)
    (r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below (s.gpr .esp) 96))
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr)
    (h9a : args 9 = BitVec.ofNat 32 len) (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩)
    (CR : CtxRd base bytes len args s)
    (cstk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below (s.gpr .esp) 96))
    (cx : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨byteAddr (args 0), len⟩)
    (dv : Spec.Ffdh.domainValid len (domOf s.mem args dlen) = true)
    (CV : CtxVals len args (comp s.mem args len 0) (comp s.mem args len 1)
      (Spec.Ffdh.generationScalarBits (CheckPrivate.params s.mem args len dlen)) s.mem) :
    WP isa Generate.body s fun t => ∃ r, t.gpr .eax = BitVec.ofNat 32 r ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ CachedKeyPost len dlen s.mem args r t.mem := by
  have fit := G.fit
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  obtain h2 : 2 * len ≤ dlen := by omega_arith
  obtain hn : ctxBytes len < 2 ^ 64 := by
    have := CR.afit; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega_arith
  -- The width.
  generalize hbits : Spec.Ffdh.generationScalarBits (CheckPrivate.params s.mem args len dlen) = bits at CV
  obtain bf := VG.Proof.Ffdh.ContextRows.genBits_facts dv
  obtain hb1 : 1 ≤ bits := by rw [← hbits]; exact bf.1
  obtain hb : bits ≤ 8 * len := by rw [← hbits]; exact bf.2
  obtain sm := (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := bits) (by omega_arith)).1
  obtain hR := VG.Proof.Rsa.FixedBaseComb.rows_pos (bits := bits) (by omega_arith)
  unfold Generate.body
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide) (h.arg (i := 2) (by decide))
    (h.arg (i := 3) (by decide))) fun u ⟨P, Cc, M, K⟩ => ?_)
  obtain S₁ : Step Ex base bytes len args s u := Step.regs h M K
  obtain rd : InRegions (u.rd ++ u.wr) (byteAddr (u.gpr .esi)) len := by
    rw [P, K.2.1, K.2.2]
    have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  refine WP.seq (WP.mono (modulusCheck_ok u (k := len) h.lower' h.upper' (by rw [P]; omega_arith) rd (by rw [Cc, G.e3]))
    fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  obtain e0 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) = comp s.mem args len 0 :=
    CheckDomain.argNum_comp s.mem args len
  rw [e0] at Z
  obtain S := S₁.trans (Step.regs S₁.inp Mv Kv)
  obtain Mvs : v.mem = s.mem := Mv.trans M
  -- The valid domain's modulus is valid.
  obtain mv : Spec.Rsa.modulusValid (comp s.mem args len 0) len = true := by
    have := VG.Proof.Ffdh.domainValid_mod dv
    rwa [← comp_p s.mem args h2] at this
  refine WP.ite _ Z (fun _ => ?_) (fun invalid => absurd mv (by rw [invalid]; decide))
  have sp : v.gpr .esp = s.gpr .esp := S.esp
  obtain G' := G.keep ⟨rfl, rfl⟩ S.keeps
  obtain Cv : KeyCut.CutGeo base bytes len (args 10) (args 0) (v.gpr .esp) v.rd v.wr := by
    rw [sp, S.keeps.2.1, S.keeps.2.2]; exact C
  obtain CVv : CtxVals len args (comp s.mem args len 0) (comp s.mem args len 1) bits v.mem := by rw [Mvs]; exact CV
  obtain wlt : len - VG.Proof.Ffdh.ScalarWidth.width bits < len := by
    have := VG.Proof.Ffdh.ScalarWidth.width_pos bits; omega_arith
  -- The front, with the cut at the context's width.
  obtain front := frontWith_ok G' (prefixWith_ok S.inp G' (by rw [sp]; exact hb40) Cv rWs (by rw [sp]; exact r40) domX
    wlt fun w Sw => by
      obtain CVw := CVv.keep Sw.frame (ctx_frameR CR (by rw [sp]; exact cstk) (fR_fit S.inp)) hn
      refine WP.mono (metaCut_ok Sw.inp (CR.keep (S.keeps.trans Sw.keeps)) G.e3 hb1 hb CVw.w0 CVw.w8)
        fun t ⟨St, k, ld, tt⟩ => ⟨St, k.mono, ld, tt⟩)
  rw [show Generate.main = Prog.chain (mainFrontWith Generate.metaCut)
    (.ite .e GenerateKey.fail (tailWith Generate.comb)) from rfl]
  refine WP.chain_split front fun u F => ?_
  obtain Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := S.keeps.trans F.keeps
  obtain spu : u.gpr .esp = s.gpr .esp := by rw [F.keeps.1 _ (by decide), sp]
  obtain Ox' : OutAt args base bytes len 0 (u.gpr .esp) u.wr := by rw [spu]; exact Ox.keep rfl Ku
  obtain Oy' : OutAt args base bytes len 8 (u.gpr .esp) u.wr := by rw [spu]; exact Oy.keep rfl Ku
  obtain FF : ∀ {t : State}, Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ ::
      frameR base (u.gpr .esp) (fR len)) u.mem t.mem →
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem := fun {t} Ft => by
    have Fv := F.frame
    have Fs := S.frame
    rw [sp] at Fv
    rw [spu] at Ft
    refine ((Fs.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans
      (Fv.mono fun r hr => ?_)).trans Ft
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  obtain pv0 : Spec.Ffdh.parametersValid (CheckPrivate.params s.mem args len dlen) = true := by
    have e := dv
    unfold Spec.Ffdh.domainValid at e
    simp only [Bool.and_eq_true] at e
    exact e.1
  obtain vs : Spec.Ffdh.vettedScalarOfOctets (CheckPrivate.params s.mem args len dlen)
      (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) % 2 ^ bits := by
    rw [← hbits]; rfl
  have gate := F.gate
  rw [Mvs, cut_vetted hb (by omega_arith)] at gate
  refine WP.gate gate (fun inval => WP.mono (fail_ok F.inp Ox' Oy' h9a xy) fun t ⟨E, Bx, By, Ft, Kt⟩ =>
    ⟨2, E, FF Ft, Ku.trans Kt, ?_⟩) (fun val => ?_)
  · have ks : Spec.Ffdh.keyStatus (CheckPrivate.params s.mem args len dlen)
        (Spec.Ffdh.vettedScalarOfOctets (CheckPrivate.params s.mem args len dlen)
          (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len)) = 2 := by
      rw [vs]; unfold Spec.Ffdh.keyStatus; rw [inval]; rfl
    refine ⟨ks.symm, ?_⟩
    simp only [ks]
    exact ⟨Bx, By⟩
  · have v9 := F.v9
    have v10 := F.v10
    have v13 := F.v13
    have v15 := F.v15
    have v16 := F.v16
    rw [Mvs] at v9 v10 v15 v16
    rw [Mvs, cut_vetted hb (by omega_arith)] at v13
    generalize hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) % 2 ^ bits = x at v13 val vs
    obtain xb : x < 2 ^ bits := by rw [← hx]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain xlt : x < 2 ^ (8 * len) := Nat.lt_of_lt_of_le xb (Nat.pow_le_pow_right (by decide) hb)
    have mv' := mv
    unfold Spec.Rsa.modulusValid at mv'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv'
    obtain p1 : 1 < comp s.mem args len 0 := by have := Nat.two_pow_pos 511; have := mv'.1.1.2; omega_arith
    obtain sP : safeM (comp s.mem args len 0) = comp s.mem args len 0 := safeM_of p1 mv'.1.1.1
    obtain Plt : comp s.mem args len 0 < 2 ^ (8 * len) := comp_lt s.mem 0
    obtain ylt : Spec.Rsa.powMod (comp s.mem args len 1) x (comp s.mem args len 0) < 2 ^ (8 * len) := by
      rw [VG.Proof.Bignum.powMod_eq]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt
    obtain CVu : CtxVals len args (comp s.mem args len 0) (comp s.mem args len 1) bits u.mem := by
      have Fv := F.frame
      rw [sp, Mvs] at Fv
      have Fu := Fv
      refine CV.keep Fu (fun r hr => ?_) hn
      rcases List.mem_cons.mp hr with rfl | hr
      · exact cx
      · exact ctx_frameR CR cstk (fR_fit h) r hr
    obtain E : CombEnv Ex base bytes len args (comp s.mem args len 0) (comp s.mem args len 1) x bits u :=
      ⟨CR.keep Ku, by rw [spu]; exact cstk, CVu.ents, v13, sm⟩
    refine WP.mono (tailWith_ok (G.keep ⟨rfl, rfl⟩ Ku) Ox' Oy' h9a xy v9 sP v13 F.v14 v15 v16 xlt ylt
      (combStage_ok F.inp E (by rw [v9, sP]) xb hR CVu.w16)) fun t ⟨E', Bx, By, Ft, Kt⟩ =>
      ⟨_, E', FF Ft, Ku.trans Kt, ?_⟩
    dsimp only [CachedKeyPost]
    obtain hpa := comp_p s.mem args h2
    obtain hga := comp_g s.mem args h2
    obtain hqa : (CheckPrivate.params s.mem args len dlen).q =
        if dlen = 2 * len then none else some (comp s.mem args len 2) := by
      rcases dl with e | e
      · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_arith)
      · have : ¬ 3 * len = 2 * len := by omega_arith
        simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
    obtain pv : Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) x = true := by
      cases c : Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) x
      · exact absurd c val
      · rfl
    rw [vs]
    rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq pv0, pv]
    simp only [VG.Proof.Bignum.powMod_eq] at E' Bx By ⊢
    obtain ai := accept_iff (len := len) (dlen := dlen) (y := comp s.mem args len 1 ^ x % comp s.mem args len 0)
      hpa.symm p1 hqa
    rw [show (CheckPrivate.params s.mem args len dlen).g = comp s.mem args len 1 from hga.symm,
      show (CheckPrivate.params s.mem args len dlen).p = comp s.mem args len 0 from hpa.symm]
    simp only [Bool.true_eq_false, ↓reduceIte]
    by_cases hc : accept len dlen (comp s.mem args len 0) (comp s.mem args len 2) (comp s.mem args len 0)
      (comp s.mem args len 1 ^ x % comp s.mem args len 0) = true
    · rw [hc] at E' Bx By ⊢
      rw [ai.mp hc]
      simp only [↓reduceIte] at E' Bx By ⊢
      exact ⟨trivial, Bx, By⟩
    · have hc' : accept len dlen (comp s.mem args len 0) (comp s.mem args len 2) (comp s.mem args len 0)
          (comp s.mem args len 1 ^ x % comp s.mem args len 0) = false := by simpa using hc
      obtain hv : Spec.Ffdh.publicValid ⟨CheckPrivate.params s.mem args len dlen,
          comp s.mem args len 1 ^ x % comp s.mem args len 0⟩ = false := by
        cases c : Spec.Ffdh.publicValid ⟨CheckPrivate.params s.mem args len dlen,
          comp s.mem args len 1 ^ x % comp s.mem args len 0⟩
        · rfl
        · exact absurd (ai.mpr c) hc
      rw [hc'] at E' Bx By ⊢
      rw [hv]
      simp only [Bool.false_eq_true, ↓reduceIte] at E' Bx By ⊢
      exact ⟨trivial, by rw [Bx]; exact VG.Proof.Bignum.i2osp_zero' _, by rw [By]; exact VG.Proof.Bignum.i2osp_zero' _⟩

end

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In safeM safeM_of bc cwc mw)
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)
open VG.Impl.Ffdh.X86.Cached

/-! ## The context's values -/

/-- The context's words give its public words and entries. -/
theorem ctxVals_of {m : Mem} {args : Nat → BitVec 32} {len : Nat} {dom : List Byte}
    (h : Spec.Rsa.wordsAt m (ctxAddr args) (3 + 34 * mw len) = generationValues len dom)
    (dv : Spec.Ffdh.domainValid len dom = true) (hl : len ≤ 1024) (hp : 0 < (Spec.Ffdh.domainOf len dom).p)
    (hpl : (Spec.Ffdh.domainOf len dom).p < 2 ^ (8 * len)) :
    CtxVals len args (Spec.Ffdh.domainOf len dom).p (Spec.Ffdh.domainOf len dom).g
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom)) m := by
  obtain ⟨e0, e8, e16, _, _, ee⟩ := VG.Proof.Ffdh.ContextRows.ctx_of_values h
  obtain bf := VG.Proof.Ffdh.ContextRows.genBits_facts dv
  generalize Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) = bits at bf e0 e8 e16 ee ⊢
  generalize (Spec.Ffdh.domainOf len dom).p = P at hp hpl ee ⊢
  obtain b32 : bits < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_trans bf.2 (Nat.mul_le_mul_left 8 hl)) (by decide)
  obtain b64 : (2 : Nat) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
  obtain rs := (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := bits) (by omega_using [hl, bf])).1
  obtain small : ∀ {v : Nat}, v < 2 ^ 32 → (BitVec.ofNat 64 v).toNat % 2 ^ 32 = v := fun {v} hv => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv b64), Nat.mod_eq_of_lt hv]
  have hb : bc len .wide = 8 * mw len := rfl
  obtain hc : cwc len .wide = 2 * mw len := by simp only [cwc, hb]; omega_using []
  obtain hpw : 2 ^ (8 * len) ≤ 2 ^ (64 * mw len) :=
    Nat.pow_le_pow_right (by decide) (by simp only [mw, Spec.Rsa.modulusWords]; omega_using [])
  refine ⟨?_, ?_, ?_, fun e he => ?_⟩
  · rw [VG.Proof.Ffdh.ContextRows.w32_of_word, e0, small b32]
  · rw [VG.Proof.Ffdh.ContextRows.w32_of_word, e8, small (by omega_using [b32])]
  · rw [VG.Proof.Ffdh.ContextRows.w32_of_word, e16, small (by omega_using [rs])]
  · rw [hc, VG.Proof.Ffdh.ContextRows.val32_eq_wv, hb, show 8 * (8 * mw len) = 64 * mw len by omega_using []]
    exact VG.Proof.Ffdh.ContextRows.value_of_row (ee e he)
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) (Nat.le_of_lt hpl)) hpw)

/-! ## The ABI -/

/-- What the contract gives `vg_ffdh_generate_key_cached(x, x_len, y, y_len, domain, domain_len, p_len,
rand, rand_len, scratch, scratch_len, ctx, ctx_len)`. -/
structure CachedABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 52 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩,
    ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩, ⟨argAddr s 0, 52⟩]
  xy : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  xDom : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  xRand : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  xScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  xCtx : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  xArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  yDom : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  yRand : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  yScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  yCtx : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  yArgs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  domScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  domArgs : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  randScratch : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  randArgs : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  scratchCtx : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  ctxArgs : (⟨argumentPointer s 11, (arg s 12).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  retX : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retY : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  retDom : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  retCtx : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  belowX : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowY : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  belowRand : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowCtx : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  xBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  domBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  randBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  ctxBound : (arg s 11).toNat + (arg s 12).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 6).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 6).toNat (arg s 5).toNat
  xLen : (arg s 1).toNat = (arg s 6).toNat
  yLen : (arg s 3).toNat = (arg s 6).toNat
  randLen : (arg s 8).toNat = (arg s 6).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 6).toNat ≤ (arg s 10).toNat
  valid : Spec.Ffdh.domainValid (arg s 6).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat) = true
  ctxLen : (arg s 12).toNat = Spec.Ffdh.generationPrecomputedWords (arg s 6).toNat
  ctx : Spec.Ffdh.generationPrecompute (arg s 6).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat) =
    some (Spec.Rsa.wordsAt s.mem (argumentPointer s 11) (arg s 12).toNat)

theorem cachedABI_of {s : State} (h : (Proof.Ffdh.cachedGenerateKeyContract abi stack).pre s) : CachedABI s := by
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

abbrev gArgs : Impl.Ffdh.X86.Args := Impl.Ffdh.X86.Cached.Generate.args

theorem wrapABI {s : State} (A : CachedABI s) : WrapABI gArgs 13 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h; decide),
    (fun _ h => by cases h; decide), by decide, (fun _ h => by cases h; decide)⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega_using [this]
  argsIn := by
    rw [A.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  wsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill gArgs)) Impl.Ffdh.X86.Cached.Generate.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- The bytes of the domain and of `rand` at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat
abbrev entryRand (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat

/-- What the body may read: the domain, `rand` and the context; and write: x and y. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 4) (arg s 5).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 7) (arg s 8).toNat ∧
    InRegions wr (argumentPointer s 0) (arg s 1).toNat ∧ InRegions wr (argumentPointer s 2) (arg s 3).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 11) ((arg s 12).toNat * 8)

/-- The 96 bytes below the frame, and the frame, below the caller's stack pointer. -/
theorem frame_subs {s : State} (A : CachedABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) :
    Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ∧
      Region.Sub ⟨sp.setWidth 64, 76⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have fb : argsFrame = 76 := rfl
  obtain hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, low, st'])
  obtain espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega_using [fb, low, st'])
  refine ⟨?_, ?_⟩
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega_using [low, st']), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  · rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)

theorem frame_geo {s : State} (A : CachedABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    Geo (synth gArgs (arg s)) (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (arg s 5).toNat sp rd wr := by
  obtain ⟨sub40, subF⟩ := frame_subs A espf
  have xL : (arg s 1).toNat = pLenOf gArgs s := A.xLen
  have yL : (arg s 3).toNat = pLenOf gArgs s := A.yLen
  have rL : (arg s 8).toNat = pLenOf gArgs s := A.randLen
  obtain ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain dx : Region.Disjoint ⟨argumentPointer s 0, pLenOf gArgs s⟩ ⟨argumentPointer s 2, pLenOf gArgs s⟩ := by
    have := A.xy; rw [xL, yL] at this; exact this
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, (A.belowDom.sub_left sub40).symm, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, (ofn _).symm, dx⟩
  · show (arg s 7).toNat + _ ≤ _
    rw [← rL]; exact A.randBound
  · show (arg s 0).toNat + _ ≤ _
    rw [← xL]; exact A.xBound
  · show InRegions _ (argumentPointer s 7) _
    rw [← rL]; exact hrd.2.1
  · show InRegions _ (argumentPointer s 0) _
    rw [← xL]; exact hrd.2.2.1
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ ⟨argumentPointer s 0, _⟩
    have := A.xRand.symm; rw [rL, xL] at this; exact this
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← xL]; exact A.xScratch
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.belowX.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← rL]; exact A.randScratch
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← rL]; exact (A.belowRand.sub_left sub40).symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.xDom.symm
  · show (arg s 0).toNat + _ ≤ _
    rw [← xL]; exact A.xBound
  · show InRegions _ (argumentPointer s 0) _
    rw [← xL]; exact hrd.2.2.1
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.xScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.belowX.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← xL]; exact (A.belowX.sub_left sub40).symm
  · show (arg s 2).toNat + _ ≤ _
    rw [← yL]; exact A.yBound
  · show InRegions _ (argumentPointer s 2) _
    rw [← yL]; exact hrd.2.2.2.1
  · show Region.Disjoint _ ⟨argumentPointer s 2, _⟩
    rw [← yL]; exact A.yScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 2, _⟩
    rw [← yL]; exact A.belowY.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 2, _⟩ _
    rw [← yL]; exact (A.belowY.sub_left sub40).symm

theorem genWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
  omega_using []

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_far {s : State} (A : CachedABI s) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase gArgs s, wsSize gArgs s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) :
    ∀ r ∈ [(⟨wsBase gArgs s, wsSize gArgs s⟩ : Region), ⟨frameAt s, argsFrame⟩], Region.Disjoint ⟨p, n⟩ r := by
  obtain hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hws
  · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm

theorem frame_keep {s : State} (A : CachedABI s) {m : Mem}
    (Ft : Frame [⟨wsBase gArgs s, wsSize gArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase gArgs s, wsSize gArgs s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n :=
  frame_bytes Ft (frame_far A hws hb) hn

/-- The context's bytes. -/
theorem ctxBytes_eq {s : State} (A : CachedABI s) : (arg s 12).toNat * 8 = ctxBytes (pLenOf gArgs s) := by
  have := A.ctxLen
  rw [genWords_eq] at this
  simp only [ctxBytes, bc, mw, Spec.Rsa.modulusWords]
  show _ = 24 + 8 * (((arg s 6).toNat + 7) / 8) * 34
  omega_using [this]

/-- The context, as the body reads it. -/
theorem frame_ctx {s : State} (A : CachedABI s) {f : State} (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (hrd : Rd s f.rd f.wr) :
    CtxRd (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (synth gArgs (arg s)) f ∧
      Region.Disjoint ⟨ctxAddr (synth gArgs (arg s)), ctxBytes (pLenOf gArgs s)⟩ (below (f.gpr .esp) 96) ∧
      Region.Disjoint ⟨ctxAddr (synth gArgs (arg s)), ctxBytes (pLenOf gArgs s)⟩
        ⟨byteAddr (synth gArgs (arg s) 0), pLenOf gArgs s⟩ := by
  obtain ⟨sub40, _⟩ := frame_subs A espf
  obtain cb := ctxBytes_eq A
  have xL : (arg s 1).toNat = pLenOf gArgs s := A.xLen

  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · show InRegions _ (off (argumentPointer s 11) 0) _
    rw [← cb, show off (argumentPointer s 11) 0 = argumentPointer s 11 from BitVec.add_zero _]; exact hrd.2.2.2.2
  · show (argumentPointer s 11).toNat + 0 + ctxBytes (pLenOf gArgs s) ≤ 2 ^ 32
    rw [← cb]
    have := A.ctxBound
    obtain hv : (argumentPointer s 11).toNat = (arg s 11).toNat := by
      simp only [argumentPointer, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega_using [])
    rw [hv]; omega_using [this]
  · show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ _
    rw [← cb]; exact A.scratchCtx.symm
  · show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ _
    rw [← cb]; exact (A.belowCtx.sub_left sub40).symm
  · show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ ⟨argumentPointer s 0, _⟩
    rw [← cb, ← xL]; exact A.xCtx.symm

/-- What the contract asks of the status and the outputs. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  let a := Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)
  let x := Spec.Ffdh.vettedScalarOfOctets a (entryRand s)
  r.toNat = Spec.Ffdh.keyStatus a x ∧
    if Spec.Ffdh.keyStatus a x = 1 then
      Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 6).toNat = Spec.Rsa.i2osp x (arg s 6).toNat ∧
        Spec.Rsa.bytesAt m (argumentPointer s 2) (arg s 6).toNat =
          Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (arg s 6).toNat
    else Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 6).toNat = List.replicate (arg s 6).toNat 0 ∧
      Spec.Rsa.bytesAt m (argumentPointer s 2) (arg s 6).toNat = List.replicate (arg s 6).toNat 0

/-- The context's values at the frame's state. -/
theorem frame_vals {s : State} (A : CachedABI s) {m : Mem}
    (Ft : Frame [⟨wsBase gArgs s, wsSize gArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem m) :
    CtxVals (pLenOf gArgs s) (synth gArgs (arg s)) (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).p
      (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).g
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s))) m := by
  have dl : (arg s 5).toNat = 2 * (arg s 6).toNat ∨ (arg s 5).toNat = 3 * (arg s 6).toNat := A.dLen
  have lw := A.pLen.1
  have up := A.pLen.2
  obtain mv := VG.Proof.Ffdh.domainValid_mod A.valid
  have mv' := mv
  unfold Spec.Rsa.modulusValid at mv'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv'
  obtain hp : 0 < (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).p := by
    exact Nat.lt_of_lt_of_le (Nat.two_pow_pos 511) mv'.1.1.2
  obtain hpl : (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).p < 2 ^ (8 * (arg s 6).toNat) := by
    obtain h1 := VG.Proof.Bignum.os2ip_lt ((entryDom s).take (arg s 6).toNat)
    obtain h2 : 256 ^ ((entryDom s).take (arg s 6).toNat).length ≤ 2 ^ (8 * (arg s 6).toNat) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega_using [])
    change Spec.Rsa.os2ip ((entryDom s).take (arg s 6).toNat) < _
    omega_using [h1, h2]
  obtain dlen : (arg s 6).toNat ≤ (entryDom s).length := by
    rw [VG.Proof.Bignum.bytesAt_length]; omega_using [dl]
  obtain W : Spec.Rsa.wordsAt s.mem (ctxAddr (synth gArgs (arg s))) (3 + 34 * mw (arg s 6).toNat) =
      generationValues (arg s 6).toNat (entryDom s) := by
    have c := A.ctx
    rw [VG.Proof.Ffdh.generationPrecompute_eq dlen mv, A.ctxLen, genWords_eq] at c
    exact (Option.some.inj c).symm
  obtain CV0 : CtxVals (pLenOf gArgs s) (synth gArgs (arg s)) _ _ _ s.mem := ctxVals_of W A.valid A.pLen.2 hp hpl
  obtain cb := ctxBytes_eq A
  obtain hn : ctxBytes (pLenOf gArgs s) < 2 ^ 64 := by
    have := A.ctxBound; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega_using [cb]
  exact CV0.keep Ft (frame_far A (by
    show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ _
    rw [← cb]; exact A.scratchCtx.symm)
    (by show Region.Disjoint _ ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩
        rw [← cb]; exact A.belowCtx)) hn

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : CachedABI s) (f : State)
    (I : In (Rd s) (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (synth gArgs (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase gArgs s, wsSize gArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.Cached.Generate.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([xR s, yR s] ++ CrtRt.frameR (wsBase gArgs s) (f.gpr .esp) (fR (pLenOf gArgs s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain Gm := frame_geo A espf I.extra
  obtain ⟨CR, cstk, cx⟩ := frame_ctx A espf I.extra
  have xL : (arg s 1).toNat = pLenOf gArgs s := A.xLen
  have yL : (arg s 3).toNat = pLenOf gArgs s := A.yLen
  have rL : (arg s 8).toNat = pLenOf gArgs s := A.randLen
  obtain hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  obtain D : Spec.Rsa.bytesAt f.mem (byteAddr (synth gArgs (arg s) 2)) (arg s 5).toNat = entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega_using [])
  obtain R : Spec.Rsa.bytesAt f.mem (byteAddr (synth gArgs (arg s) 10)) (pLenOf gArgs s) = entryRand s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _ = _
    rw [← rL]
    exact frame_keep A Ft A.randScratch A.belowRand (by have := A.randBound; omega_using [])
  have pl : pLenOf gArgs s = (arg s 6).toNat := rfl
  have dl := Gm.dom.dl
  have lw := Gm.dom.lower
  have up := Gm.dom.upper
  obtain h2 : 2 * pLenOf gArgs s ≤ (arg s 5).toNat := by omega_using [dl]
  obtain dv : Spec.Ffdh.domainValid (pLenOf gArgs s) (domOf f.mem (synth gArgs (arg s)) (arg s 5).toNat) = true := by
    rw [domOf, D]; exact A.valid
  obtain CVf := frame_vals A Ft
  obtain CV : CtxVals (pLenOf gArgs s) (synth gArgs (arg s)) (comp f.mem (synth gArgs (arg s)) (pLenOf gArgs s) 0)
      (comp f.mem (synth gArgs (arg s)) (pLenOf gArgs s) 1)
      (Spec.Ffdh.generationScalarBits (CheckPrivate.params f.mem (synth gArgs (arg s)) (pLenOf gArgs s)
        (arg s 5).toNat)) f.mem := by
    rw [comp_p f.mem _ h2, comp_g f.mem _ h2]
    simp only [CheckPrivate.params, CheckDomain.domBytes]
    rw [D]; exact CVf
  refine WP.mono (body_ok I Gm.dom Gm.dom40 Gm.cut Gm.rWs Gm.r40 Gm.domX Gm.ox Gm.oy Gm.e9 Gm.xy CR cstk cx dv CV)
    fun t ⟨r, E, F, K, P⟩ => ⟨?_, ?_, K⟩
  · simp only [CachedKeyPost, CheckPrivate.params, CheckDomain.domBytes] at P
    rw [D, R] at P
    obtain ⟨hr, hb⟩ := P
    refine ⟨?_, hb⟩
    rw [E, BitVec.toNat_ofNat, hr]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (keyStatus_le _ _) (by decide))
  · rw [List.cons_append, List.singleton_append, xR, yR, xL, yL]; exact F

theorem operation_ok {s : State} (A : CachedABI s) :
    WP isa Impl.Ffdh.X86.Cached.Generate.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  obtain hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions _ _ _ ∧ InRegions _ _ _ ∧
      InRegions (s.rd ++ _) _ _
    rw [A.rd, A.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := [xR s, yR s])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.retX
      · exact A.retY)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.xScratch.symm
      · exact A.yScratch.symm)
    (P := fun m e => spec s m e) (hP := fun m m' e F h => by
      obtain hx := VG.Proof.Rsa.rsa_bytes_frame F (src := argumentPointer s 0) (k := (arg s 6).toNat)
        (by have := (arg s 6).isLt; omega_arith) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr; rw [← A.xLen]; exact A.belowX.symm)
      obtain hy := VG.Proof.Rsa.rsa_bytes_frame F (src := argumentPointer s 2) (k := (arg s 6).toNat)
        (by have := (arg s 6).isLt; omega_arith) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr; rw [← A.yLen]; exact A.belowY.symm)
      simpa only [spec, hx, hy] using h)
    fun f I espf Ft => frame_ok A f I espf Ft

theorem correct (s : State) (h : (Proof.Ffdh.cachedGenerateKeyContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Cached.Generate.code s trace t ∧ abiPreserved s t ∧
      (Proof.Ffdh.cachedGenerateKeyContract abi stack).post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (cachedABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Ffdh.X86.Cached

end

end

/-!
# `vg_ffdh_generate_key_cached` on i686 in time that depends on the domain and the status only

The contract releases the domain and the status. The context is the
domain's (`generationPrecompute`), so runs with the same domain read the same
public width from it: the cut at that width (`metaCut_trace`) and the comb
(`comb_trace`) are related with its values, and the rest is
`vg_ffdh_generate_key`'s.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate

/-! ## The taint checks -/

theorem metaHead_check : ACheck (.block metaHead) := by dsimp only [ACheck]; taint_decide
theorem metaLoop_check : ACheck (.block [.alu .add .eax (.reg .eax), .alu .sub .edx (.imm 1)]) := by
  dsimp only [ACheck]; taint_decide
theorem metaTail_check : ACheck (.block [.alu .sub .eax (.imm 1), .store (sc Impl.Ffdh.X86.tOff) .eax]) := by
  dsimp only [ACheck]; taint_decide
theorem pSetup_check : ACheck Impl.Ffdh.X86.pSetup := by dsimp only [ACheck]; taint_decide
theorem loadG_check : ACheck (load (.slot .wide 10) (one .wide) 4 5) := by dsimp only [ACheck]; taint_decide
theorem cutLoad_check : ACheck (.seq Impl.Ffdh.X86.GenerateKey.cut (.seq (load (.slot .wide 13) (one .wide) 0 1)
    (.block []))) := by
  dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Generate.args)) (.block [])).isSome = true := by
  taint_decide

/-! ## The cut at the context's width -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run the cut starts from, with the context's width `bits`. -/
abbrev MW (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (bits : Nat) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ CtxRd base bytes len args u ∧ w32 u.mem (ctxAddr args) 0 = bits ∧
    w32 u.mem (ctxAddr args) 8 = (bits + 7) / 8 ∧ args 3 = BitVec.ofNat 32 len

theorem metaCut_trace {bits : Nat} (hb1 : 1 ≤ bits) (hb : bits ≤ 8 * len) :
    RelCT isa (Both (MW Ex base bytes len args sp bits)) Generate.metaCut fun _ _ => True := by
  have hb8 : 1 ≤ bits + 8 - 8 * ((bits + 7) / 8) ∧ bits + 8 - 8 * ((bits + 7) / 8) ≤ 8 := by omega_using []
  generalize hN : bits + 8 - 8 * ((bits + 7) / 8) = N at hb8
  unfold Generate.metaCut
  refine VG.RelCT.seq (taint_both (F := fun u => Run Ex base bytes len args sp u ∧
      u.gpr .edx = BitVec.ofNat 32 (N - 0)) (fun _ _ M₁ M₂ => M₁.1.agree M₂.1) _ metaHead_check fun x M =>
    WP.mono (metaHead_ok M.1.1 M.2.1 M.2.2.2.2 hb1 hb M.2.2.1 M.2.2.2.1) fun u ⟨S, _, _, e, _⟩ =>
      ⟨run_step M.1 S, by rw [e, hN, Nat.sub_zero]⟩) ?_
  refine VG.RelCT.seq (relCT_countLoop (N := N) (I := fun j u => Run Ex base bytes len args sp u ∧
      u.gpr .edx = BitVec.ofNat 32 (N - j)) (by omega_using [hN]) fun j hj => ?_) ?_
  · refine taint_both (fun _ _ M₁ M₂ => M₁.1.agree M₂.1) _ metaLoop_check fun x ⟨R, ed⟩ =>
      wp_addS rfl fun t₁ V₁ _ => wp_subZ rfl fun t₂ V₂ z₂ => WP.block_nil ⟨⟨?_, ?_⟩, ?_⟩
    · have K : Keeps [.eax, .edx] x t₂ := (V₁.keeps.mono (by decide)).widen V₂.keeps
      exact ⟨R.1.regs K (by rw [V₂.mem, V₁.mem]), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
    · rw [V₂.gpr, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hj]), Nat.sub_sub]
    · rw [z₂, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hj])]
      congr 1
      by_cases e : j + 1 = N
      · simp [e, show N - j - 1 = 0 by omega_using [e]]
      · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro c
        have := congrArg BitVec.toNat c
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hN])] at this
        simp at this; omega_using [hj, e, this]
  exact VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.1.agree h.2.1) metaTail_check

end

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D : List Byte} {St : Nat}

/-- The context's width for the domain `D`. -/
abbrev cBits (len : Nat) (D : List Byte) : Nat := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len D)

/-- A run of the body, with the domain `D`, its context and the status `St`. -/
structure KAtC (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (St : Nat) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  geo : KeyGen.Geo args base bytes len dlen sp u.rd u.wr
  dom : KeyGen.domOf u.mem args dlen = D
  st : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf len D)
    (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf len D) (Spec.Rsa.bytesAt u.mem (byteAddr (args 10)) len)) = St
  rd : CtxRd base bytes len args u
  stk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below sp 96)
  cx : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨byteAddr (args 0), len⟩
  dv : Spec.Ffdh.domainValid len D = true
  vals : CtxVals len args (Spec.Ffdh.domainOf len D).p (Spec.Ffdh.domainOf len D).g (cBits len D) u.mem

theorem KAtC.keep {x u : State} (A : KAtC Ex base bytes len dlen args sp D St x)
    (S : Step Ex base bytes len args x u) (m : u.mem = x.mem) : KAtC Ex base bytes len dlen args sp D St u := by
  refine ⟨run_step A.run S, ?_, by rw [m]; exact A.dom, by rw [m]; exact A.st, A.rd.keep S.keeps, A.stk, A.cx, A.dv,
    by rw [m]; exact A.vals⟩
  rw [S.keeps.2.1, S.keeps.2.2]; exact A.geo

/-- The context's values through a stage. -/
theorem KAtC.vals_step {x u : State} (A : KAtC Ex base bytes len dlen args sp D St x)
    (S : Step Ex base bytes len args x u) :
    CtxVals len args (Spec.Ffdh.domainOf len D).p (Spec.Ffdh.domainOf len D).g (cBits len D) u.mem := by
  have hn : ctxBytes len < 2 ^ 64 := by
    have := A.rd.afit; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega_arith
  have F := S.frame
  rw [A.run.2.2] at F
  exact A.vals.keep F (ctx_frameR A.rd A.stk (fR_fit A.run.1)) hn

/-- A run the front's stages after the first reach. -/
abbrev FW (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (St : Nat) (u : State) : Prop :=
  ∃ x, KAtC Ex base bytes len dlen args sp D St x ∧ Step Ex base bytes len args x u

theorem FW.run {u : State} (W : FW Ex base bytes len dlen args sp D St u) : Run Ex base bytes len args sp u :=
  let ⟨_, A, S⟩ := W
  run_step A.run S

theorem prefix_trace (hD : Spec.Ffdh.domainValid len D = true) :
    RelCT isa (Both (KAtC Ex base bytes len dlen args sp D St)) (Prog.chain (KeyGen.prefixWith Generate.metaCut)
      (.block [])) fun _ _ => True := by
  show RelCT isa _ (.seq Impl.Ffdh.X86.pSetup (.seq (load (.slot .wide 10) (one .wide) 4 5) (.seq Generate.metaCut
    (.seq Impl.Ffdh.X86.GenerateKey.cut (.seq (load (.slot .wide 13) (one .wide) 0 1) (.block [])))))) _
  refine VG.RelCT.seq (aRel (F := FW Ex base bytes len dlen args sp D St) (fun _ A => A.run) pSetup_check
    fun x A => ?_) ?_
  · have G := A.geo.dom
    have dl := G.dl
    have fit := G.fit
    have lw := G.lower
    exact WP.mono (pSetup_ok A.run.1 G.e3 (by omega_arith)
      (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
          rwa [BitVec.add_zero] at this)
      (G.apart.sub_left (Region.sub_prefix (by omega_arith)))) fun u ⟨I, F, _, _, _, _, K⟩ => ⟨x, A, I, F, K⟩
  refine VG.RelCT.seq (aRel (F := FW Ex base bytes len dlen args sp D St) (fun _ W => W.run) loadG_check
    fun u ⟨x, A, S⟩ => ?_) ?_
  · have G := A.geo.dom
    have dl := G.dl
    have lw := G.lower
    exact WP.mono (loadComp_ok S.inp (G.keep ⟨rfl, rfl⟩ S.keeps) (k := 1) (j := 10) (by decide) (by omega_arith)
      (by decide)) fun t ⟨_, O, K⟩ => ⟨x, A, S.trans (Step.slot S.inp (by decide) O K)⟩
  refine VG.RelCT.seq (relCT_both (F := Run Ex base bytes len args sp)
    ((metaCut_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp)
      (bits := cBits len D) ?_ ?_).mono (fun _ _ h => ?_) fun _ _ h => h) fun u M => ?_) ?_
  · exact (VG.Proof.Ffdh.ContextRows.genBits_facts hD).1
  · exact (VG.Proof.Ffdh.ContextRows.genBits_facts hD).2
  · obtain ⟨⟨x₁, A₁, S₁⟩, ⟨x₂, A₂, S₂⟩⟩ := h
    exact ⟨⟨run_step A₁.run S₁, A₁.rd.keep S₁.keeps, (A₁.vals_step S₁).w0, (A₁.vals_step S₁).w8, A₁.geo.dom.e3⟩,
      ⟨run_step A₂.run S₂, A₂.rd.keep S₂.keeps, (A₂.vals_step S₂).w0, (A₂.vals_step S₂).w8, A₂.geo.dom.e3⟩⟩
  · obtain ⟨x, A, S⟩ := M
    have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
    exact WP.mono (metaCut_ok S.inp (A.rd.keep S.keeps) A.geo.dom.e3 bf.1 bf.2 (A.vals_step S).w0
      (A.vals_step S).w8) fun t ⟨St, _⟩ => run_step (run_step A.run S) St
  exact aEnd (fun _ R => R) cutLoad_check


/-- The prefix's run, with the cut at the context's width. -/
theorem prefixC_ok (hD : Spec.Ffdh.domainValid len D = true) {x : State}
    (A : KAtC Ex base bytes len dlen args sp D St x) :
    WP isa (Prog.chain (KeyGen.prefixWith Generate.metaCut) (.block [])) x
      (KeyGen.PrefW Ex base bytes len dlen args x (Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (byteAddr (args 10)) len) %
        2 ^ cBits len D)) := by
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
  have lw := A.geo.dom.lower
  have sp' := A.run.2.2
  have wlt : len - VG.Proof.Ffdh.ScalarWidth.width (cBits len D) < len := by
    have := VG.Proof.Ffdh.ScalarWidth.width_pos (cBits len D); omega_using [bf, this]
  rw [← cut_vetted bf.2 (by omega_using [bf])]
  exact KeyGen.prefixWith_ok A.run.1 A.geo.dom (by rw [sp']; exact A.geo.dom40) (by rw [sp']; exact A.geo.cut)
    A.geo.rWs (by rw [sp']; exact A.geo.r40) A.geo.domX wlt fun w Sw =>
      WP.mono (metaCut_ok Sw.inp (A.rd.keep Sw.keeps) A.geo.dom.e3 bf.1 bf.2 (A.vals_step Sw).w0
        (A.vals_step Sw).w8) fun t ⟨St', k, ld, tt⟩ => ⟨St', k.mono, ld, tt⟩

theorem front_trace (hD : Spec.Ffdh.domainValid len D = true) :
    RelCT isa (Both (KAtC Ex base bytes len dlen args sp D St))
      (Prog.chain (KeyGen.mainFrontWith Generate.metaCut) (.block [])) fun _ _ => True := by
  show RelCT isa _ (Prog.chain (KeyGen.prefixWith Generate.metaCut) (.seq Impl.Ffdh.X86.CheckPrivate.bound
    (Prog.chain [Impl.Ffdh.X86.CheckPrivate.scalarMask, testMask] (.block [])))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (relCT_both (F := CheckPrivate.RG Ex base bytes len dlen args sp) (prefix_trace hD)
    fun x A => ?_) (VG.RelCT.seq CheckPrivate.bound_relCT (aEnd (fun _ h => h) CheckPrivate.mask_check))
  exact WP.mono (prefixC_ok hD A) fun u P => ⟨⟨P.inp, A.run.2.1.keep P.keeps, (P.keeps.1 _ (by decide)).trans A.run.2.2⟩,
    A.geo.dom.keep ⟨rfl, rfl⟩ P.keeps⟩

/-- A run the tail starts from: the comb's, and the tail's. -/
abbrev TC (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  KeyGen.TP Ex base bytes len dlen args sp u ∧ CS Ex base bytes len args sp (Spec.Ffdh.domainOf len D).p (cBits len D) u

/-- The front's runs: the tail's start, and the gate on the scalar, whether the status is 2. -/
theorem frontC_ok (hD : Spec.Ffdh.domainValid len D = true) (hm : KeyGen.modOk len D) {x : State}
    (A : KAtC Ex base bytes len dlen args sp D St x) :
    WP isa (Prog.chain (KeyGen.mainFrontWith Generate.metaCut) (.block [])) x fun u =>
      TC Ex base bytes len dlen args sp D u ∧ Gate u (St = 2) := by
  have G := A.geo.dom
  have dl := G.dl
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega_arith
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
  have sm := (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := cBits len D)
    (Nat.le_trans bf.2 (by have := G.upper; omega_arith))).1
  refine WP.mono (KeyGen.frontWith_ok G (prefixC_ok hD A)) fun u F => ?_
  have sp' := A.run.2.2
  have Fu := F.frame
  rw [sp'] at Fu
  have hn : ctxBytes len < 2 ^ 64 := by
    have := A.rd.afit; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega_arith
  have Vu := A.vals.keep Fu (fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact A.cx
    · exact ctx_frameR A.rd A.stk (fR_fit A.run.1) r hr) hn
  have spu : u.gpr .esp = sp := (F.keeps.1 _ (by decide)).trans sp'
  have pa : comp x.mem args len 0 = (Spec.Ffdh.domainOf len D).p := by rw [comp_p x.mem args h2]; rw [← A.dom]
  have mv : Spec.Rsa.modulusValid (Spec.Ffdh.domainOf len D).p len = true := hm
  unfold Spec.Rsa.modulusValid at mv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
  have p1 : 1 < (Spec.Ffdh.domainOf len D).p := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega_arith
  refine ⟨⟨⟨⟨F.inp, A.run.2.1.keep F.keeps, spu⟩, G.keep ⟨rfl, rfl⟩ F.keeps⟩, _, _,
    Nat.mod_lt _ (Nat.two_pow_pos _), F.inp, ⟨A.rd.keep F.keeps, by rw [spu]; exact A.stk, Vu.ents, F.v13, sm⟩,
    by rw [F.v9, pa]; exact safeM_of p1 mv.1.1.1, Vu.w16, A.run.2.1.keep F.keeps, spu⟩, F.gate.congr ?_⟩
  have hp : CheckPrivate.params x.mem args len dlen = Spec.Ffdh.domainOf len D := congrArg (Spec.Ffdh.domainOf len) A.dom
  rw [← A.st, KeyGen.keyStatus_two, hp]
  rfl

theorem main_trace (hD : Spec.Ffdh.domainValid len D = true) (hl : len ≤ 1024) :
    RelCT isa (Both fun x => KAtC Ex base bytes len dlen args sp D St x ∧ KeyGen.modOk len D) Generate.main
      fun _ _ => True := by
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
  have hR0 := VG.Proof.Rsa.FixedBaseComb.rows_pos (bits := cBits len D) (Nat.lt_of_lt_of_le Nat.zero_lt_one bf.1)
  have hR : Spec.Rsa.FixedBaseComb.rows (cBits len D) ≤ 1639 :=
    (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := cBits len D) (Nat.le_trans bf.2 ?_)).1
  rw [show Generate.main = Prog.chain (KeyGen.mainFrontWith Generate.metaCut)
    (.ite .e Impl.Ffdh.X86.GenerateKey.fail (KeyGen.tailWith Generate.comb)) from rfl]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (relCT_both (F := fun u => TC Ex base bytes len dlen args sp D u ∧ Gate u (St = 2))
    ((front_trace hD).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) fun x ⟨A, hm⟩ => frontC_ok hD hm A) ?_
  refine gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.1.1) KeyGen.fail_check) ?_
  · refine KeyGen.tailWith_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (dlen := dlen)
      (args := args) (sp := sp) (relCT_both ((comb_trace (P := (Spec.Ffdh.domainOf len D).p) hR0 hR).mono
      (fun _ _ h => ⟨h.1.1.1.2, h.2.1.1.2⟩) fun _ _ h => h) fun x T => ?_)
    obtain ⟨⟨⟨T, G, xx, hx, h, E, hP, hrows, _, _⟩, _⟩, _⟩ := T
    exact WP.mono (combStage_ok h E hP hx hR0 hrows) fun u ⟨S, _, _⟩ => KeyGen.tp_step T S
  · omega_using [hl]


theorem body_trace (hD : Spec.Ffdh.domainValid len D = true) (hl : len ≤ 1024) :
    RelCT isa (Both (KAtC Ex base bytes len dlen args sp D St)) Generate.body fun _ _ => True := by
  show RelCT isa _ (Prog.chain [.block PublicFn.modulusArgs, .block modulusCheck]
    (.ite .e Generate.main (ret 0))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (relCT_both (F := fun u => KAtC Ex base bytes len dlen args sp D St u ∧ Gate u (KeyGen.modOk len D))
    (aEnd (fun _ A => A.run) KeyGen.mod_check) fun x A => ?_) ?_
  · have h := A.run.1
    have G := A.geo.dom
    have fit := G.fit
    have dl := G.dl
    have lw := G.lower
    refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide) (h.arg (i := 2) (by decide))
      (h.arg (i := 3) (by decide))) fun u ⟨P, C, M, K⟩ => ?_)
    have S₁ : Step Ex base bytes len args x u := Step.regs h M K
    have rd : InRegions (u.rd ++ u.wr) (byteAddr (u.gpr .esi)) len := by
      rw [P, K.2.1, K.2.2]
      have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_using [dl]) (by omega_using [fit])
      rwa [BitVec.add_zero] at this
    refine WP.seq (WP.mono (modulusCheck_ok u (k := len) h.lower' h.upper' (by rw [P]; omega_using [fit, dl]) rd (by rw [C, G.e3]))
      fun v ⟨Z, Mv, Kv⟩ => WP.block_nil ⟨(A.keep S₁ M).keep (Step.regs S₁.inp Mv Kv) Mv, Gate.of_eval Z ?_⟩)
    rw [P, M, ← A.dom, KeyGen.modOk, VG.Proof.Ffdh.domainOf_p x.mem _ (by omega_using [dl])]
  · exact gate_relCT (fun _ h => h.2) ((main_trace hD hl).mono (fun _ _ h => ⟨⟨h.1.1.1, h.1.2⟩, h.2.1.1, h.2.2⟩)
      fun _ _ h => h) (aEnd (fun _ h => h.1.1.run) KeyGen.ret0_check)

/-- The context's values, as `body_ok` takes them. -/
theorem KAtC.cv {u : State} (A : KAtC Ex base bytes len dlen args sp D St u) :
    CtxVals len args (comp u.mem args len 0) (comp u.mem args len 1)
      (Spec.Ffdh.generationScalarBits (CheckPrivate.params u.mem args len dlen)) u.mem := by
  have dl := A.geo.dom.dl
  have lw := A.geo.dom.lower
  have h2 : 2 * len ≤ dlen := by omega_arith
  rw [comp_p u.mem args h2, comp_g u.mem args h2]
  have hp : CheckPrivate.params u.mem args len dlen = Spec.Ffdh.domainOf len D := congrArg (Spec.Ffdh.domainOf len) A.dom
  rw [hp, show Spec.Rsa.bytesAt u.mem (byteAddr (args 2)) dlen = D from A.dom]
  exact A.vals

end


/-! ## Against the contract -/

section

/-- The status at entry. -/
abbrev status (s : State) : Nat :=
  Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s))
    (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)) (entryRand s))

theorem pub_facts {s t : State} (H : (Proof.Ffdh.cachedGenerateKeyContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 13, arg s i = arg t i) ∧ entryDom s = entryDom t ∧ status s = status t := by
  sig_pub [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a5])
  refine ⟨SP, fun i hi => ?_, inj L₁, List.cons.inj L₂ |>.1⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
    i = 12 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7
  · exact a8
  · exact a9
  · exact a10
  · exact a11
  · exact a12

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) :
    Rd s (rd ++ wr) [x, KeyGen.xR s, KeyGen.yR s] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩, _, _, ⟨r'', hr'', hc''⟩⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩,
    ⟨r'', List.mem_append_left _ hr'', hc''⟩⟩

/-- The narrowed state the body runs from, x and y writable. -/
theorem kAt_of {s f : State} (A : CachedABI s) (Bf : BodyAt (Rd s) gArgs s f) :
    KAtC (Rd s) (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (arg s 5).toNat (synth gArgs (arg s))
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s) (status s)
      (narrowed (wsBase gArgs s) (wsSize gArgs s) f [KeyGen.xR s, KeyGen.yR s]) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase gArgs s, wsSize gArgs s⟩
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  have sub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have rL : (arg s 8).toNat = pLenOf gArgs s := A.randLen
  have D : KeyGen.domOf f.mem (synth gArgs (arg s)) (arg s 5).toNat = entryDom s :=
    frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega_using [])
  have R : Spec.Rsa.bytesAt f.mem (byteAddr (synth gArgs (arg s) 10)) (pLenOf gArgs s) = entryRand s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _ = _
    rw [← rL]
    exact frame_keep A Bf.2.2.2.2 A.randScratch A.belowRand (by have := A.randBound; omega_using [])
  obtain ⟨CR, cstk, cx⟩ := frame_ctx (f := narrowed (wsBase gArgs s) (wsSize gArgs s) f [KeyGen.xR s, KeyGen.yR s])
    A Bf.2.1 hx
  refine ⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A) (Out := [KeyGen.xR s, KeyGen.yR s])
    fun r hr => ?_, Bf.2.1⟩, frame_geo A rfl hx, D, ?_, CR, by rw [← Bf.2.1]; exact cstk, cx, A.valid,
    frame_vals A Bf.2.2.2.2⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.belowX.sub_left sub
    · exact A.belowY.sub_left sub
  · show Spec.Ffdh.keyStatus _ (Spec.Ffdh.vettedScalarOfOctets _ (Spec.Rsa.bytesAt f.mem _ _)) = _
    rw [R]
    rfl


theorem constantTime : ConstantTime isa (Proof.Ffdh.cachedGenerateKeyContract abi stack).pre
    (Proof.Ffdh.cachedGenerateKeyContract abi stack).pub Impl.Ffdh.X86.Cached.Generate.code := by
  intro s t tr ur sf tf S T H E F
  have A := cachedABI_of S
  have B := cachedABI_of T
  obtain ⟨SP, args, dom, st⟩ := pub_facts H
  have hws : wsBase gArgs s = wsBase gArgs t := by
    show (arg s 9).setWidth 64 = (arg t 9).setWidth 64
    rw [args 9 (by decide)]
  have hwz : wsSize gArgs s = wsSize gArgs t := by
    show (arg s 10).toNat * 8 = (arg t 10).toNat * 8
    rw [args 10 (by decide)]
  have hpl : pLenOf gArgs s = pLenOf gArgs t := by
    show (arg s 6).toNat = (arg t 6).toNat
    rw [args 6 (by decide)]
  have hsy : synth gArgs (arg t) = synth gArgs (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hxR : KeyGen.xR t = KeyGen.xR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hyR : KeyGen.yR t = KeyGen.yR s := by
    show (⟨(arg t 2).setWidth 64, (arg t 3).toNat⟩ : Region) = ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    rw [args 2 (by decide), args 3 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 4).setWidth 64) (arg t 5).toNat ∧
        InRegions (rd ++ wr) ((arg t 7).setWidth 64) (arg t 8).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat ∧ InRegions wr ((arg t 2).setWidth 64) (arg t 3).toNat ∧
        InRegions (rd ++ wr) ((arg t 11).setWidth 64) ((arg t 12).toNat * 8)) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 4).setWidth 64) (arg s 5).toNat ∧
        InRegions (rd ++ wr) ((arg s 7).setWidth 64) (arg s 8).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat ∧ InRegions wr ((arg s 2).setWidth 64) (arg s 3).toNat ∧
        InRegions (rd ++ wr) ((arg s 11).setWidth 64) ((arg s 12).toNat * 8)
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide), args 4 (by decide),
      args 5 (by decide), args 7 (by decide), args 8 (by decide), args 11 (by decide), args 12 (by decide)]
  have hl5 : (arg t 5).toNat = (arg s 5).toNat := by rw [args 5 (by decide)]
  have hx : ∀ {x : State}, CachedABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions _ _ _ ∧ InRegions _ _ _ ∧
      InRegions (x.rd ++ _) _ _
    rw [X.rd, X.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : CachedABI x) (Bf : BodyAt (Rd x) gArgs x f),
      ∃ F, WP isa Impl.Ffdh.X86.Cached.Generate.body
        (narrowed (wsBase gArgs x) (wsSize gArgs x) f [KeyGen.xR x, KeyGen.yR x]) F := fun X Bf => by
    have K := kAt_of X Bf
    have sp' := K.run.2.2
    exact ⟨_, body_ok K.run.1 K.geo.dom (by rw [sp']; exact K.geo.dom40) (by rw [sp']; exact K.geo.cut) K.geo.rWs
      (by rw [sp']; exact K.geo.r40) K.geo.domX (by rw [sp']; exact K.geo.ox) (by rw [sp']; exact K.geo.oy)
      K.geo.e9 K.geo.xy K.rd (by rw [sp']; exact K.stk) K.cx (by rw [K.dom]; exact K.dv) K.cv⟩
  have ho : ∀ {x f : State}, CachedABI x → BodyAt (Rd x) gArgs x f →
      ∀ r ∈ [KeyGen.xR x, KeyGen.yR x], r ∈ f.wr := fun X Bf r hr => by
    rw [Bf.2.2.2.1, X.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body (Out := [KeyGen.xR s, KeyGen.yR s]) hws hwz (fun f Bf => hw A Bf)
      (fun g Bg => by rw [← hxR, ← hyR]; exact hw B Bg)
      (fun f g Bf Bg => ⟨kAt_of A Bf, ?_⟩) (body_trace A.valid A.pLen.2) (fun f Bf => ho A Bf)
      (fun g Bg => by rw [← hxR, ← hyR]; exact ho B Bg)) E F
  have D₂ := kAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl5, ← SP, hxR, hyR, ← dom, ← st] at D₂
  rw [← hws, ← hwz]
  exact D₂

end

end VG.Proof.Ffdh.X86.Cached

end

end

/-! ### `Ffdh.X86.Cached.Search.Frame`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86.Cached.Search.Steps`, which this module and modules that import it used -/

section

/-! # Steps of the key search (x86)

`St o ds f`: a state of the run from the entry state `o`, `esi` at the
state, whose words at the offsets `ds` hold `f`, whose memory differs from
the entry's only where the run may write. A load of a word (`St.ld`), a
store (`St.stw`), a register-only instruction (`St.reg`, `St.fupd`) and the
zeros at the outputs (`St.zeroOutputs`) keep it.
-/

@[expose] public section

/-! ## Zeros at an output (x86)

`zeroOut d` writes `p_len` zeros at the pointer in the state's word at `d`,
one byte at a time (`zeroOut_ok`), changing only `eax`, `ecx` and `edx`.
-/

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search

/-- A byte of a store of one byte. -/
theorem byte_write {m : Mem} {a x : Addr} {v : BitVec 8} : (m.writeW a v) x = if x = a then v else m x := by
  have e : (x - a).toNat < 8 / 8 ↔ x = a := by
    rw [show 8 / 8 = 1 from rfl, Nat.lt_one_iff, ← BitVec.toNat_zero (w := 64), BitVec.toNat_inj]
    constructor
    · intro h; rw [← BitVec.sub_add_cancel x a, h, BitVec.zero_add]
    · intro h; rw [h, BitVec.sub_self]
  simp only [Mem.writeW, Mem.write, e]
  split
  · next h => subst h; simp
  · rfl

/-- `mov byte [m], r`. -/
theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {r : Reg8} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)})
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- The output after `k` of its `n` bytes are zeroed. -/
structure ZInv (s₀ : State) (P : BitVec 32) (n k : Nat) (t : State) : Prop where
  edx : t.gpr .edx = P + BitVec.ofNat 32 k
  ecx : t.gpr .ecx = BitVec.ofNat 32 (n - k)
  eax : t.gpr .eax = 0
  frame : Frame [⟨P.setWidth 64, n⟩] s₀.mem t.mem
  zero : ∀ i < k, t.mem (P.setWidth 64 + BitVec.ofNat 64 i) = 0
  keeps : Keeps [.eax, .ecx, .edx] s₀ t

theorem zeroStep_ok {s₀ t : State} {P : BitVec 32} {n k : Nat} (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s₀.wr)
    (hb : P.toNat + n ≤ 2 ^ 32) (hn : n < 2 ^ 32) (hk : k < n) (I : ZInv s₀ P n k t) :
    WP isa (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun u => ZInv s₀ P n (k + 1) u ∧ u.zf = some (decide (n - (k + 1) = 0)) := by
  have hp : t.ea (at_ .edx 0) = P.setWidth 64 + BitVec.ofNat 64 k := by
    show (t.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, I.edx]; exact addr_eq (by omega_using [hb, hk])
  have hw : InRegions t.wr (P.setWidth 64 + BitVec.ofNat 64 k) 1 :=
    ⟨_, by rw [I.keeps.2.2]; exact hR, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hb, hk])⟩
  refine wp_store8 hp hw fun u₁ m₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
  have hv : (t.gpr (Reg8.al).reg).setWidth 8 = 0 := by show (t.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at m₁
  have kk : Keeps [.eax, .ecx, .edx] t u₃ :=
    ((m₁.keeps _).trans (v₂.keeps.mono (by decide))).trans (v₃.keeps.mono (by decide))
  have mem₃ : u₃.mem = t.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [⟨P.setWidth 64, n⟩] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hb, hk]))
  refine ⟨⟨?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans kk⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.edx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.ecx, ofNat_pred (by omega_using [hk])]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.eax]
  · rw [mem₃, byte_write]
    by_cases hik : i = k
    · subst hik; simp
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega_using [hb, hk, hi]) (by omega_using [hb, hk]) hik)]
      exact I.zero i (by omega_using [hi, hik])
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega_using [hn]) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hk]))

/-- `p_len` zeros at the pointer `P` in the state's word at `d`. -/
theorem zeroOut_ok {s : State} {S P : BitVec 32} {d n : Nat} (hesi : s.gpr .esi = S)
    (hd : InRegions (s.rd ++ s.wr) (addr S d) 4) (hl : InRegions (s.rd ++ s.wr) (addr S lenOff) 4)
    (hP : s.mem.readW (addr S d) 32 = P) (hn : s.mem.readW (addr S lenOff) 32 = BitVec.ofNat 32 n)
    (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s.wr) (h0 : 0 < n) (hb : P.toNat + n ≤ 2 ^ 32) (hn32 : n < 2 ^ 32) :
    WP isa (zeroOut d) s fun u => Frame [⟨P.setWidth 64, n⟩] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) n = List.replicate n 0 ∧ Keeps [.eax, .ecx, .edx] s u := by
  unfold zeroOut
  refine WP.seq (wp_ldm hesi hd fun t₁ u₁ => ?_)
  refine wp_ldm ((u₁.other _ (by decide)).trans hesi) (by rw [u₁.rd, u₁.wr]; exact hl) fun t₂ u₂ => ?_
  refine wp_movi fun t₃ u₃ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .edx] s t₃ :=
    ((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))
  have m₃ : t₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have I₀ : ZInv s P n 0 t₃ := ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hP, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, hn, Nat.sub_zero],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), k₃⟩
  refine WP.loop (M := isa) (fun (j : Nat) (u : State) => ∃ k, j = n - k ∧ k < n ∧ ZInv s P n k u)
    (fun j u hu => ?_) _ t₃ ⟨0, rfl, h0, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok hR hb hn32 hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : n - (k + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], J.frame, ?_, J.keeps⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega_using [he, h₁])
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega_using [hk],
      k + 1, rfl, by omega_using [he], J⟩

end VG.Proof.Ffdh.X86.Cached.Search

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The registers the controller uses for itself. -/
abbrev Scratch (r : Reg) : Prop := r = .eax ∨ r = .ecx ∨ r = .edx

structure St (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : KeySearchABI o
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  esp : s.gpr .esp = o.gpr .esp
  esi : s.gpr .esi = arg o 12
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 12) ds f

theorem saved_ne {r q : Reg} (hq : Scratch q) (hr : r ∈ calleeSaved) : r ≠ q := by
  rcases hq with rfl | rfl | rfl <;> simp [calleeSaved] at hr <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem St.reg {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} {v : BitVec 32}
    (U : Upd s t r v) (hr : Scratch r) : St o ds f t := by
  refine ⟨h.abi, U.rd.trans h.rd, U.wr.trans h.wr, ?_, ?_, fun q hq hne => ?_, U.mem ▸ h.frame, U.mem ▸ h.words⟩
  · rw [U.other _ (saved_ne hr (by decide)), h.esp]
  · rw [U.other _ (saved_ne hr (by decide)), h.esi]
  · rw [U.other _ (saved_ne hr hq), h.saved q hq hne]

theorem St.fupd {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (F : Fupd s t) :
    St o ds f t :=
  ⟨h.abi, F.rd.trans h.rd, F.wr.trans h.wr, by rw [F.gpr, h.esp], by rw [F.gpr, h.esi],
    fun q hq hne => by rw [F.gpr, h.saved q hq hne], F.mem ▸ h.frame, F.mem ▸ h.words⟩

theorem Live.st {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    St o liveDs (liveF p (o.gpr .esi) used keys scalars) s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨A, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem liveDs_aligned : Aligned liveDs := by decide

/-- The state's words are readable and writable. -/
theorem St.wIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions s.wr (addr (arg o 12) d) 4 := by
  rw [h.wr]; exact ⟨_, sR_mem h.abi, st_in h.abi hd⟩

theorem St.rIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions (s.rd ++ s.wr) (addr (arg o 12) d) 4 :=
  let ⟨r, hr, hc⟩ := h.wIn hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- `mov r, [esi + d]`. -/
theorem St.ld {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} (hr : Scratch r)
    {d : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o ds f t → t.gpr r = f d → (∀ q, q ≠ r → t.gpr q = s.gpr q) → t.cf = s.cf →
      t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.mov r (.mem (st d)) :: rest)) s Q := by
  show WP isa (.block (.mov r (.mem ⟨.esi, d⟩) :: rest)) s Q
  refine wp_movS (readSrc_mem h.esi (h.rIn hd4)) fun t U c => k t (h.reg U hr) ?_ U.other c U.mem
  rw [U.gpr]; exact h.words.get hd

/-- A store and the word it keeps. -/
theorem Ctl.write' {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0)
    (v : BitVec 32) : Ctl (m.writeW (addr S d) v) S (d :: ds) (upd f d v) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rw [readW_write hS v hd hd (Or.inl rfl)]; simp [upd]
  · exact h.write hS hA hd hd4 v e he

theorem Aligned.cons {ds : List Nat} (h : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) :
    Aligned (d :: ds) := fun e he => by
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨hd, hd4⟩
  · exact h e he

/-- `mov [esi + d], r`. -/
theorem St.stw {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds) {r : Reg}
    {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o (d :: ds) (upd f d (s.gpr r)) t → t.gpr = s.gpr → t.zf = s.zf → t.cf = s.cf →
      Frame [sR o] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.store (st d) r :: rest)) s Q := by
  refine wp_storeS (st_ea h.esi d) (h.wIn hd) fun t M => k t ?_ M.gpr M.zf M.cf
    (by rw [M.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (st_in h.abi hd))
  refine ⟨h.abi, M.rd.trans h.rd, M.wr.trans h.wr, by rw [M.gpr, h.esp], by rw [M.gpr, h.esi],
    fun q hq hne => by rw [M.gpr, h.saved q hq hne], ?_, ?_⟩
  · rw [M.mem]; exact h.frame.writeW (List.mem_append_left _ (sR_mem h.abi)) _ (st_in h.abi hd)
  · rw [M.mem]; exact h.words.write' h.abi.sBound hA hd hd4 _

theorem Ctl.sub {m : Mem} {S : BitVec 32} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f)
    (hs : ∀ d ∈ ds', d ∈ ds) : Ctl m S ds' f := fun d hd => h d (hs d hd)

theorem St.sub {o s : State} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : St o ds f s)
    (hs : ∀ d ∈ ds', d ∈ ds) : St o ds' f s :=
  ⟨h.abi, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.sub hs⟩

theorem St.congr {o s : State} {ds : List Nat} {f g : Nat → BitVec 32} (h : St o ds f s)
    (e : ∀ d ∈ ds, f d = g d) : St o ds g s :=
  ⟨h.abi, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.congr e⟩

/-- The outputs' regions. -/
theorem xR_eq {o : State} (A : KeySearchABI o) : xR o = ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
  rw [xR, A.xLen]
theorem yR_eq {o : State} (A : KeySearchABI o) : yR o = ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
  rw [yR, A.yLen]

/-- Zeros at the output `P` (`x` or `y`). -/
theorem St.zeroOne {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    {d : Nat} {P : BitVec 32} (hdP : f d = P) (hl : f lenOff = BitVec.ofNat 32 (arg o 7).toNat)
    (hdd : d ∈ ds) (hdl : lenOff ∈ ds) (hd4 : d + 4 ≤ 128)
    (hin : (⟨P.setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr)
    (hs : (stR (arg o 12)).Disjoint ⟨P.setWidth 64, (arg o 7).toNat⟩) (hb : P.toNat + (arg o 7).toNat ≤ 2 ^ 32) :
    WP isa (zeroOut d) s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      Frame [⟨P.setWidth 64, (arg o 7).toNat⟩] s.mem u.mem ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  refine WP.mono (zeroOut_ok h.esi (h.rIn hd4) (h.rIn (by decide)) ((h.words.get hdd).trans hdP)
    ((h.words.get hdl).trans hl) (by rw [h.wr]; exact hin) (by omega_using [hp]) hb (by omega_using [])) fun t ⟨F, Z, K⟩ => ?_
  refine ⟨⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame A.sBound hA F fun r hr => ?_⟩, Z, F, fun r hr => K.1 _ fun hm => hr (by simp at hm; omega)⟩
  · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hin
  · simp only [List.mem_singleton] at hr; subst hr; exact hs

/-- Zeros at `x` and `y`. -/
theorem St.zeroOutputs {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hx : f xOff = arg o 0) (hy : f yOff = arg o 2) (hl : f lenOff = BitVec.ofNat 32 (arg o 7).toNat)
    (hdx : xOff ∈ ds) (hdy : yOff ∈ ds) (hdl : lenOff ∈ ds) :
    WP isa zeroOutputs s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 0) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 2) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      u.gpr .esp = s.gpr .esp ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hS := A.sBound
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  have xb : (arg o 0).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.xBound; rw [A.xLen] at this; exact this
  have yb : (arg o 2).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.yBound; rw [A.yLen] at this; exact this
  have xin : (⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← xR_eq A, A.wr]; exact List.mem_cons_self ..
  have yin : (⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← yR_eq A, A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have xs : (stR (arg o 12)).Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xR_eq A]; exact A.xs.symm
  have ys : (stR (arg o 12)).Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yR_eq A]; exact A.ys.symm
  refine WP.seq (WP.mono (zeroOut_ok h.esi (h.rIn (by decide)) (h.rIn (by decide)) ((h.words.get hdx).trans hx)
    ((h.words.get hdl).trans hl) (by rw [h.wr]; exact xin) (by omega_using [hp]) xb (by omega_using [])) fun t ⟨F, Z, K⟩ => ?_)
  have ht : St o ds f t := by
    refine ⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame hS hA F fun r hr => ?_⟩
    · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ xin
    · simp only [List.mem_singleton] at hr; subst hr; exact xs
  refine WP.mono (zeroOut_ok ht.esi (ht.rIn (by decide)) (ht.rIn (by decide)) ((ht.words.get hdy).trans hy)
    ((ht.words.get hdl).trans hl) (by rw [ht.wr]; exact yin) (by omega_using [hp]) yb (by omega_using [])) fun u ⟨F', Z', K'⟩ => ?_
  refine ⟨⟨A, K'.2.1.trans ht.rd, K'.2.2.trans ht.wr, by rw [K'.1 _ (by decide), ht.esp],
      by rw [K'.1 _ (by decide), ht.esi], fun q hq hne => ?_, ht.frame.trans (F'.mono fun r hr => ?_),
      ht.words.frame hS hA F' fun r hr => ?_⟩, ?_, Z', ?_, fun r hr => ?_⟩
  · rw [K'.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), ht.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ yin
  · simp only [List.mem_singleton] at hr; subst hr; exact ys
  · rw [bytes_frame F' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← xR_eq A, ← yR_eq A]; exact A.xy) (by omega_using [])]
    exact Z
  · rw [K'.1 _ (by decide), K.1 _ (by decide)]
  · rw [K'.1 _ (fun hm => hr (by simp at hm; omega)), K.1 _ (fun hm => hr (by simp at hm; omega))]

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # The attempt's frame of arguments (x86)

The attempt allocates 44 bytes below the entry's stack pointer and stores
`vg_ffdh_generate_key`'s eleven arguments there (`arguments_ok`). With the
call's return address and the callee's 172 bytes below them, they are the
228 bytes below the entry's stack pointer, at offsets of `low o`
(`low_sub`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The base of the stack the controller uses. -/
abbrev low (o : State) : Addr := (o.gpr .esp).setWidth 64 - 228#64

theorem low_toNat {o : State} (A : KeySearchABI o) : (low o).toNat = (o.gpr .esp).toNat - 228 := by
  have : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have := (o.gpr .esp).isLt
  simp only [low, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- A stack pointer `k ≤ 228` bytes below the entry's, at its offset from `low o`. -/
theorem sw_sub {o : State} (A : KeySearchABI o) {k : Nat} (hk : k ≤ 228) :
    (o.gpr .esp - BitVec.ofNat 32 k).setWidth 64 = low o + BitVec.ofNat 64 (228 - k) := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

/-- A word at `d` above a stack pointer `k` bytes below the entry's. -/
theorem addr_sub {o : State} (A : KeySearchABI o) {k d : Nat} (hk : k ≤ 228) (hd : d ≤ k) :
    addr (o.gpr .esp - BitVec.ofNat 32 k) d = low o + BitVec.ofNat 64 (228 - k + d) := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := (o.gpr .esp).isLt
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega_arith

/-- A range at offsets of `low o` lies in the stack the controller uses. -/
theorem low_sub {o : State} {d n : Nat} (h : d + n ≤ 228) : Region.Sub ⟨low o + BitVec.ofNat 64 d, n⟩ (lowR o) :=
  Offset.sub_base _ h

theorem low_contains {o : State} (A : KeySearchABI o) {d n : Nat} (h : d + n ≤ 228) :
    (lowR o).Contains (low o + BitVec.ofNat 64 d) n := by
  have : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  exact Offset.contains_base _ h (by omega_arith)

/-- The frame's region. -/
abbrev frR (o : State) : Region := ⟨low o + BitVec.ofNat 64 176, 52⟩

/-- A state in the attempt's frame: `St` but for the stack pointer and the frame's region. -/
structure Fr (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : KeySearchABI o
  rd : s.rd = o.rd
  wr : s.wr = frR o :: o.wr
  esp : s.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes
  esi : s.gpr .esi = arg o 12
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .esp → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 12) ds f

theorem St.alloc {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) :
    Fr o ds f (allocFrame argsBytes s) := by
  refine ⟨h.abi, h.rd, ?_, by rw [allocFrame_esp, h.esp], by rw [allocFrame_gpr _ _ (by decide), h.esi],
    fun r hr hne hsp => by rw [allocFrame_gpr _ _ hsp, h.saved r hr hne], h.frame, h.words⟩
  rw [allocFrame_wr, h.esp, h.wr, sw_sub h.abi (by decide)]; rfl

/-- `vg_ffdh_generate_key_cached`'s arguments for `used` octets consumed. -/
def callArg (o : State) (used : Nat) (j : Nat) : BitVec 32 :=
  if j = 0 then arg o 0 else
  if j = 2 then arg o 2 else
  if j = 4 then arg o 5 else
  if j = 5 then arg o 6 else
  if j = 7 then arg o 8 + BitVec.ofNat 32 used else
  if j = 9 then arg o 10 else
  if j = 10 then arg o 11 else
  if j = 11 then arg o 13 else
  if j = 12 then arg o 14 else arg o 7

/-- The first `k` arguments are in the frame. -/
def ArgsAt (o : State) (used k : Nat) (m : Mem) : Prop :=
  ∀ j < k, m.readW (low o + BitVec.ofNat 64 (176 + 4 * j)) 32 = callArg o used j

/-- `pass d j`: the state's word at `d`, argument `j`, to the frame. -/
theorem pass_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f s)
    (hA : Aligned ds) {d j : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) (hj : j < 13) (hv : f d = callArg o used j)
    (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr o ds f t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (pass d j ++ rest)) s Q := by
  have A := h.abi
  have hS := A.sBound
  show WP isa (.block (.mov .eax (.mem ⟨.esi, d⟩) :: .store ⟨.esp, 4 * j⟩ .eax :: rest)) s Q
  have rin : InRegions (s.rd ++ s.wr) (addr (arg o 12) d) 4 := by
    rw [h.rd, h.wr]; exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (sR_mem A)), st_in A hd4⟩
  refine wp_movS (readSrc_mem h.esi rin) fun t U _ => ?_
  have ea : addr (t.gpr .esp) (4 * j) = low o + BitVec.ofNat 64 (176 + 4 * j) := by
    rw [U.other _ (by decide), h.esp, addr_sub A (by decide) (by unfold argsBytes; omega_arith)]; rfl
  have win : (frR o).Contains (low o + BitVec.ofNat 64 (176 + 4 * j)) 4 := by
    have : 228 ≤ (o.gpr .esp).toNat := A.stackLow
    exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_storeS (show t.ea ⟨.esp, 4 * j⟩ = _ by rw [ea_mk, ea])
    (by rw [U.wr, h.wr]; exact ⟨_, List.mem_cons_self .., win⟩) fun t' M => k t' ?_ ?_
  · have lc := low_contains A (d := 176 + 4 * j) (n := 4) (by omega_arith)
    have fr : Frame [lowR o] s.mem t'.mem := by
      rw [M.mem, U.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ lc
    refine ⟨A, M.rd.trans (U.rd.trans h.rd), M.wr.trans (U.wr.trans h.wr), ?_, ?_, fun r hr hne hsp => ?_,
      h.frame.trans (fr.mono fun r hr => ?_), h.words.frame hS hA fr fun r hr => ?_⟩
    · rw [M.gpr, U.other _ (by decide), h.esp]
    · rw [M.gpr, U.other _ (by decide), h.esi]
    · rw [M.gpr, U.other _ (saved_ne (Or.inl rfl) hr), h.saved r hr hne hsp]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.lowS.symm
  · have hl := low_toNat A
    have hb := A.stackBound
    intro i hi
    rw [M.mem, U.gpr, U.mem]
    by_cases hij : i = j
    · subst hij; rw [Mem.readW_writeW_self32, h.words.get hd, hv]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact ha i (by omega_arith)

theorem arguments_ok {o s : State} {e : BitVec 32} {used keys scalars : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used keys scalars) s) :
    WP isa (.block arguments) s fun t => Fr o liveDs (liveF (ofState o) e used keys scalars) t ∧
      ArgsAt o used 13 t.mem := by
  have hA : Aligned liveDs := by decide
  show WP isa (.block (pass xOff 0 ++ pass lenOff 1 ++ pass yOff 2 ++ pass lenOff 3 ++ pass domOff 4 ++
    pass dlenOff 5 ++ pass lenOff 6 ++ pass randOff 7 ++ pass lenOff 8 ++ pass scratchOff 9 ++
    pass slenOff 10 ++ pass ctxOff 11 ++ pass ctxLenOff 12 ++ [])) s _
  simp only [List.append_assoc]
  refine pass_ok (used := used) h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, xOff])
    (fun _ h => absurd h (Nat.not_lt_zero _)) fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, yOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, domOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, dlenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, randOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, lenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, scratchOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, slenOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, ctxOff]) a
    fun t h a => ?_
  refine pass_ok h hA (by decide) (by decide) (by decide) (by simp [liveF, callArg, ofState, ctxLenOff]) a
    fun t h a => WP.block_nil ⟨h, a⟩

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # `vg_ffdh_generate_key_cached` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86

/-- The stack arguments: x, y and `rand` of 64 bytes, the domain of 128 (`CachedSat.domain`), the
working space of 1056 words and the domain's context. -/
def satBase (a : Addr) : Byte :=
  if a = 0x20005 then 0x10
  else if a = 0x20008 then 64
  else if a = 0x2000d then 0x20
  else if a = 0x20010 then 64
  else if a = 0x20015 then 0x30
  else if a = 0x20018 then 128
  else if a = 0x2001c then 64
  else if a = 0x20021 then 0x40
  else if a = 0x20024 then 64
  else if a = 0x20029 then 0x90
  else if a = 0x2002c then 0x20
  else if a = 0x2002d then 4
  else if a = 0x20032 then 0x10
  else if a = 0x20034 then 0x13
  else if a = 0x20035 then 1 else CachedSat.domainMem a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := CachedSat.withContext satBase
  rd := [⟨0x3000, 128⟩, ⟨0x4000, 64⟩, ⟨0x100000, 2200⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x9000, 8448⟩, ⟨0x20004, 52⟩]

theorem sat_arg (i : Nat) (hi : i < 13) : arg satState i = Mem.readW satBase (argAddr satState i) 32 := by
  unfold arg
  refine CachedSat.readW_outside _ ?_
  have small : ∀ i < 13, (argAddr satState i).toNat + 32 / 8 ≤ 0x100000 := by decide
  exact small i hi

theorem sat_domain : Spec.Rsa.bytesAt satState.mem 0x3000 128 = CachedSat.domain := by
  rw [show satState.mem = CachedSat.withContext satBase from rfl, CachedSat.domain_unchanged]
  apply CachedSat.bytesAt_eq
  have : ∀ i < 128, satBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this

theorem satisfiable : ∃ s, (Proof.Ffdh.cachedGenerateKeyContract abi stack).pre s := by
  have a0 : arg satState 0 = 0x1000 := by rw [sat_arg 0 (by decide)]; decide
  have a1 : arg satState 1 = 64 := by rw [sat_arg 1 (by decide)]; decide
  have a2 : arg satState 2 = 0x2000 := by rw [sat_arg 2 (by decide)]; decide
  have a3 : arg satState 3 = 64 := by rw [sat_arg 3 (by decide)]; decide
  have a4 : arg satState 4 = 0x3000 := by rw [sat_arg 4 (by decide)]; decide
  have a5 : arg satState 5 = 128 := by rw [sat_arg 5 (by decide)]; decide
  have a6 : arg satState 6 = 64 := by rw [sat_arg 6 (by decide)]; decide
  have a7 : arg satState 7 = 0x4000 := by rw [sat_arg 7 (by decide)]; decide
  have a8 : arg satState 8 = 64 := by rw [sat_arg 8 (by decide)]; decide
  have a9 : arg satState 9 = 0x9000 := by rw [sat_arg 9 (by decide)]; decide
  have a10 : arg satState 10 = 1056 := by rw [sat_arg 10 (by decide)]; decide
  have a11 : arg satState 11 = 0x100000 := by rw [sat_arg 11 (by decide)]; decide
  have a12 : arg satState 12 = 275 := by rw [sat_arg 12 (by decide)]; decide
  have e : argAddr satState 0 = 0x20004 := by decide
  refine ⟨satState, ?_⟩
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes, stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
    Spec.Ffdh.generationContextAt]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e]
  repeat' apply And.intro
  all_goals first
    | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt satState.mem 0x3000 128) = true
       rw [sat_domain]; exact CachedSat.domain_valid)
    | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt satState.mem 0x3000 128) =
          some (Spec.Rsa.wordsAt satState.mem 0x100000 275)
       rw [sat_domain]; exact (CachedSat.canonical satBase).2)
    | (apply Region.disjoint_of_sep; decide)
    | rfl
    | decide

theorem verified :
    Verified target Impl.Ffdh.X86.Cached.Generate.code (Proof.Ffdh.cachedGenerateKeyContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Cached
