module

import VerifiedGarbage.Proof.MlKem.X86.TopSeq
public import VerifiedGarbage.Proof.MlKem.X86.Top
public import VerifiedGarbage.Proof.MlKem.PolyContract
public import VerifiedGarbage.Proof.MlKem.X86.Sample
public import VerifiedGarbage.Proof.MlKem.X86.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86.Table
import VerifiedGarbage.Proof.MlKem.X86.TopPrim
public import VerifiedGarbage.Proof.MlKem.X86.TopKeep
public import VerifiedGarbage.Impl.MlKem.X86.Kem
public import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.MlKem.X86.AddSub
public import VerifiedGarbage.Proof.MlKem.X86.CallRet
public import VerifiedGarbage.Proof.MlKem.X86.Cbd
public import VerifiedGarbage.Proof.MlKem.X86.Decode12
public import VerifiedGarbage.Proof.MlKem.X86.Encode12
public import VerifiedGarbage.Proof.MlKem.X86.Mul
public import VerifiedGarbage.Proof.MlKem.X86.NttInv
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Sha256.X86.Compress
public import VerifiedGarbage.Proof.Sha256.X86.Lit
public import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
public import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
public import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
import VerifiedGarbage.Impl.MlKem.X86.CheckEk
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.MlKem.X86.NttSetup
import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.MlKem.X86.TopHash
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.TopPrim2
import VerifiedGarbage.Proof.Sha512.Spec

/-! ### `MlKem.X86.TopSeq2`, which only this module used -/

section

/-! ### `MlKem.X86.TopPrim3`, which only this module used -/

section

/-!
# ML-KEM on x86 (32-bit): calls of `vg_mlkem_sample_ntt`, `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`

As `TopPrim.lean`. `vg_mlkem_sample_ntt` returns a value, so its arguments are
popped into `ecx` (`callRet`), and its public data includes its seed: two runs
agree on it when the caller's seeds agree (`hseed`). The calls of compression
are proven for any leaf with the contract of `vg_mlkem_compress_encode` or
`vg_mlkem_decode_decompress` for some widths (`CeFn`, `DdFn`: `ce768` and
`dd768` for 1, 4 and 10 bits; ML-KEM-1024's own leaves for 5 and 11).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem sample_nosp : NoSp Impl.MlKem.X86.sampleNTT := NoSp.of_all (by decide +kernel)
theorem sample_stack : stackUse Impl.MlKem.X86.sampleNTT = 56 := by decide +kernel

/-- `a ← SampleNTT(seed)`, returning 1 or 0 in `eax`, with the 34 bytes `seed` at `(da, dO)`, `a` at
`(aa, ao)` and the scratch at `(ca, co)`, in `eax`, `ecx` and `edx`. -/
theorem sample_call (da dO aa ao ca co : Nat)
    (hc : (Y.ok ⟨da, dO, 34⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨ca, co, 2048⟩ && Y.sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 34⟩ ⟨ca, co, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true) (hN : 88 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧ s.gpr .edx = Buf.ptr s₀ ⟨ca, co, 2048⟩)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 72]) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun iters => sampleNTT iters (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callRet [.edx, .ecx, .eax] "vg_mlkem_sample_ntt" Impl.MlKem.X86.sampleNTT) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hA'⟩, hC⟩, dDA⟩, dDC⟩, dAC⟩ := hc
  have hA₁ := (Lay.okW_iff.mp hA').1
  have hC₁ := (Lay.okW_iff.mp hC).1
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      arg (pushed [.edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧
      arg (pushed [.edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ca, co, 2048⟩ := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 72) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨fit, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
  refine callR_piece Sample.verified sample_nosp (by decide) (by decide)
    (by rw [sample_stack]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨da, dO, 34⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨aa, ao, 1024⟩, Buf.rgn s₀ ⟨ca, co, 2048⟩] ++ [below (E1 s₀) 12])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩]) (by simp [hA', hC]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2⟩ := entry s₀ s hp ha
    have hE' : 72 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 72) (by omega_arith)
    have eA : argAddr (pushed [.edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 12).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 16 := by
      rw [callEntry_esp', h.esp]; rfl
    have bD := Buf.stkD hp hD (N := 4 * 3 + 4 + 56) (by omega_arith)
    have bA := Buf.stkD hp hA₁ (N := 4 * 3 + 4 + 56) (by omega_arith)
    have bC := Buf.stkD hp hC₁ (N := 4 * 3 + 4 + 56) (by omega_arith)
    obtain ⟨rD₁, rD₂, rD₃⟩ := entry_regions hE' bD
    obtain ⟨rA₁, rA₂, rA₃⟩ := entry_regions hE' bA
    obtain ⟨rC₁, rC₂, rC₃⟩ := entry_regions hE' bC
    obtain ⟨rG₂, rG₃⟩ := entry_self (E := E1 s₀) (k := 3) (K := 56) hE'
    have cv := covers_of (s := s) (n := 3) (rd := [Buf.rgn s₀ ⟨da, dO, 34⟩])
      (wr := [Buf.rgn s₀ ⟨aa, ao, 1024⟩, Buf.rgn s₀ ⟨ca, co, 2048⟩] ++ [below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp hD h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hA₁ (Lay.okW_iff.mp hA').2 h.wr)
      · exact .inr (Buf.withinW hp hC₁ (Lay.okW_iff.mp hC).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.edx, .ecx, .eax] s).callEntry = e
    sig_pre [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp hD hA₁ dDA, Buf.disj hp hD hC₁ dDC, rD₁, Buf.disj hp hA₁ hC₁ dAC, rA₁,
      rC₁, rD₂, rA₂, rC₂, rG₂, rD₃, rA₃, rC₃, rG₃, Buf.fit hp hD, Buf.fit hp hA₁, Buf.fit hp hC₁⟩
  · have h := (hA s₀ s hp ha).1
    have h' := (hA s₀' s' hp' ha').1
    obtain ⟨fit, a0, -, -⟩ := entry s₀ s hp ha
    obtain ⟨fit', a0', -, -⟩ := entry s₀' s' hp' ha'
    obtain ⟨-, hax, hcx, hdx⟩ := hA s₀ s hp ha
    obtain ⟨-, hax', hcx', hdx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hdx, hdx', hq.ptr hC₁]
      · rw [hcx, hcx', hq.ptr hA₁]
      · rw [hax, hax', hq.ptr hD]
    have ek := @ent_keep Y s₀ s hp h [.edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    have ek' := @ent_keep Y s₀' s' hp' h' [.edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    refine ⟨by simp only [Buf.rgn, hq.ptr hD], by simp only [Buf.rgn, hq.ptr hA₁, hq.ptr hC₁, hq.E1], ?_⟩
    generalize he : (pushed [.edx, .ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.edx, .ecx, .eax] s').callEntry = e'
    sig_pub [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    refine ⟨trivial, ?_, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
    rw [a0, a0', bytesAt_congr (ek hD), bytesAt_congr (ek' hD), hseed s₀ s₀' s s' hp hp' hq ha ha']
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, -⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, g₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.edx, .ecx, .eax] s).callEntry = e at post
    sig_post [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂, setWidth_append32, g₂] at post
    rw [bytesAt_congr (ek hD)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 12) (N := 72) (by omega_arith) (by omega_arith)
      (by rw [sample_stack] at fr; exact fr)) post.1 post.2

theorem ce_nosp : NoSp Impl.MlKem.X86.compressEncode := NoSp.of_all (by decide +kernel)
theorem ce_stack : stackUse Impl.MlKem.X86.compressEncode = 16 := by decide +kernel
theorem dd_nosp : NoSp Impl.MlKem.X86.decodeDecompress := NoSp.of_all (by decide +kernel)
theorem dd_stack : stackUse Impl.MlKem.X86.decodeDecompress = 16 := by decide +kernel

theorem width_lt {d : Nat} (hd : d ∈ compressWidths) : 32 * d < 2 ^ 32 := by
  simp only [compressWidths, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide

/-- The contract of `vg_mlkem_compress_encode` (`compressEncodeContract`), for the widths `ws`. -/
def ceCon (ws : List Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  compressEncodeSig.contract A
    (pre := fun f d _out len m => d.toNat ∈ ws ∧ len.toNat = 32 * d.toNat ∧ Reduced m f)
    (post := fun f d out len m m' _ => Spec.Sha3.bytesAt m' out len.toNat = compressEncode d.toNat (polyAt m f))
    (writeArgs := true)
    (stack := stack)

/-- The contract of `vg_mlkem_decode_decompress` (`decodeDecompressContract`), for the widths `ws`. -/
def ddCon (ws : List Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decodeDecompressSig.contract A
    (pre := fun _b len d _f _m => d.toNat ∈ ws ∧ len.toNat = 32 * d.toNat)
    (post := fun b len d f m m' _ => PolyIs m' f (decodeDecompress d.toNat (Spec.Sha3.bytesAt m b len.toNat)))
    (writeArgs := true)
    (stack := stack)

/-- A leaf that compresses to the widths `ws` and encodes, as `vg_mlkem_compress_encode`
(`ce768`) for 1, 4 and 10 bits. -/
structure CeFn (c : Prog isa) (ws : List Nat) : Prop where
  verified : Verified X86.target c (ceCon ws X86.abi 16)
  nosp : NoSp c
  stack : stackUse c = 16
  width : ∀ d ∈ ws, 32 * d < 2 ^ 32

/-- A leaf that decodes and decompresses from the widths `ws`, as `vg_mlkem_decode_decompress`
(`dd768`). -/
structure DdFn (c : Prog isa) (ws : List Nat) : Prop where
  verified : Verified X86.target c (ddCon ws X86.abi 16)
  nosp : NoSp c
  stack : stackUse c = 16
  width : ∀ d ∈ ws, 32 * d < 2 ^ 32

theorem ce768 : CeFn Impl.MlKem.X86.compressEncode compressWidths :=
  ⟨CompressEncode.verified, ce_nosp, ce_stack, fun _ => width_lt⟩

theorem dd768 : DdFn Impl.MlKem.X86.decodeDecompress compressWidths :=
  ⟨DecodeDecompress.verified, dd_nosp, dd_stack, fun _ => width_lt⟩

/-- `out ← ByteEncode_d(Compress_d(f))`, with `f` at `(fa, fo)` and the `32d` bytes `out` at `(oa, oo)`,
and `f`, `d`, `out`, `32d` in `eax`, `ecx`, `edx` and `edi`. -/
theorem ce_call {nm : String} {c : Prog isa} {ws : List Nat} (F : CeFn c ws) (d : Nat) (hd : d ∈ ws)
    (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = BitVec.ofNat 32 d ∧ s.gpr .edx = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      s.gpr .edi = BitVec.ofNat 32 (32 * d) ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO₁ := (Lay.okW_iff.mp hO).1
  have hd32 := F.width d hd
  have hd' : d < 2 ^ 32 := by omega_arith
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = BitVec.ofNat 32 d ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = BitVec.ofNat 32 (32 * d) := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨fit, ?_, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
  refine call_piece F.verified F.nosp (by decide) (by decide)
    (by rw [F.stack]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 32 * d⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨oa, oo, 32 * d⟩]) (by simp [hO]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, -, -, -, -, rF⟩ := hA s₀ s hp ha
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    have hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega_arith)
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bF := Buf.stkD hp hF (N := 4 * 4 + 4 + 16) (by omega_arith)
    have bO := Buf.stkD hp hO₁ (N := 4 * 4 + 4 + 16) (by omega_arith)
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rO₁, rO₂, rO₃⟩ := entry_regions hE' bO
    obtain ⟨rG₂, rG₃⟩ := entry_self (E := E1 s₀) (k := 4) (K := 16) hE'
    have cv := covers_of (s := s) (n := 4) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 32 * d⟩] ++ [below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp hF h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp hO₁ (Lay.okW_iff.mp hO).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    sig_pre [ceCon, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd',
      toNat_ofNat32 hd32]
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp hF hO₁ dFO, rF₁, rO₁, rF₂, rO₂, rG₂, rF₃, rO₃, rG₃,
      Buf.fit hp hF, Buf.fit hp hO₁, hd, trivial, reduced_congr (ek hF) rF⟩
  · have h := (hA s₀ s hp ha).1
    have h' := (hA s₀' s' hp' ha').1
    obtain ⟨fit, -⟩ := entry s₀ s hp ha
    obtain ⟨-, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    obtain ⟨-, hax', hcx', hdx', hdi', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edi, Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hdi, hdi']
      · rw [hdx, hdx', hq.ptr hO₁]
      · rw [hcx, hcx']
      · rw [hax, hax', hq.ptr hF]
    refine ⟨by simp only [Buf.rgn, hq.ptr hF], by simp only [Buf.rgn, hq.ptr hO₁, hq.E1], ?_⟩
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.edi, .edx, .ecx, .eax] s').callEntry = e'
    sig_pub [ceCon, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [ceCon, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, toNat_ofNat32 hd', toNat_ofNat32 hd32] at post
    rw [polyAt_congr (ek hF)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega_arith) (by omega_arith)
      (by rw [F.stack] at fr; exact fr)) post

/-- `f ← Decompress_d(ByteDecode_d(b))`, with the `32d` bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`,
and `b`, `32d`, `d`, `f` in `eax`, `ecx`, `edx` and `edi`. -/
theorem dd_call {nm : String} {c : Prog isa} {ws : List Nat} (F : DdFn c ws) (d : Nat) (hd : d ∈ ws)
    (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      s.gpr .ecx = BitVec.ofNat 32 (32 * d) ∧ s.gpr .edx = BitVec.ofNat 32 d ∧
      s.gpr .edi = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hB, hF⟩, dBF⟩ := hc
  have hF₁ := (Lay.okW_iff.mp hF).1
  have hd32 := F.width d hd
  have hd' : d < 2 ^ 32 := by omega_arith
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = BitVec.ofNat 32 (32 * d) ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = BitVec.ofNat 32 d ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx, hdi⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega_arith); simp only [List.length_cons, List.length_nil]; omega_arith
    refine ⟨fit, ?_, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
  refine call_piece F.verified F.nosp (by decide) (by decide)
    (by rw [F.stack]; simp only [List.length_cons, List.length_nil]; omega_arith)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 32 * d⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [hF]) (by omega_arith))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    have hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega_arith)
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bB := Buf.stkD hp hB (N := 4 * 4 + 4 + 16) (by omega_arith)
    have bF := Buf.stkD hp hF₁ (N := 4 * 4 + 4 + 16) (by omega_arith)
    obtain ⟨rB₁, rB₂, rB₃⟩ := entry_regions hE' bB
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rG₂, rG₃⟩ := entry_self (E := E1 s₀) (k := 4) (K := 16) hE'
    have cv := covers_of (s := s) (n := 4) (rd := [Buf.rgn s₀ ⟨ba, bo, 32 * d⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp hB h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp hF₁ (Lay.okW_iff.mp hF).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    sig_pre [ddCon, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd',
      toNat_ofNat32 hd32]
    refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (E1 s₀).isLt; omega_arith,
      trivial, trivial, Buf.disj hp hB hF₁ dBF, rB₁, rF₁, rB₂, rF₂, rG₂, rB₃, rF₃, rG₃,
      Buf.fit hp hB, Buf.fit hp hF₁, hd, trivial⟩
  · have h := (hA s₀ s hp ha).1
    have h' := (hA s₀' s' hp' ha').1
    obtain ⟨fit, -⟩ := entry s₀ s hp ha
    obtain ⟨-, hax, hcx, hdx, hdi⟩ := hA s₀ s hp ha
    obtain ⟨-, hax', hcx', hdx', hdi'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edi, Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hdi, hdi', hq.ptr hF₁]
      · rw [hdx, hdx']
      · rw [hcx, hcx']
      · rw [hax, hax', hq.ptr hB]
    refine ⟨by simp only [Buf.rgn, hq.ptr hB], by simp only [Buf.rgn, hq.ptr hF₁, hq.E1], ?_⟩
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.edi, .edx, .ecx, .eax] s').callEntry = e'
    sig_pub [ddCon, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega_arith)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [ddCon, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, toNat_ofNat32 hd', toNat_ofNat32 hd32] at post
    rw [bytesAt_congr (ek hB)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega_arith) (by omega_arith)
      (by rw [F.stack] at fr; exact fr)) post

end VG.Proof.MlKem.X86.Top

end

end


/-!
# ML-KEM on x86 (32-bit): the calls of three and four arguments, with their arguments

As `TopSeq.lean`, for `vg_mlkem_multiply_ntts`, `vg_mlkem_sample_ntt`, and
the leaves that compress and decompress (`CeFn`, `DdFn`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem mulC_piece (oa oo fa fo ga go sa so : Nat)
    (hc : (Y.okW ⟨oa, oo, 1024⟩ && Y.ok ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ && Y.sep ⟨oa, oo, 1024⟩ ⟨ga, go, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩ &&
      Y.sep ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) = true) (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨oa, oo, 1024⟩ ++
      ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .edx ⟨ga, go, 1024⟩ ++ ptrTo Y.sc .edi ⟨sa, so, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (multiplyNTTs (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (mulC Y.sc ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨oa, oo, 1024⟩ ∧
      s₁.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧
      s₁.gpr .edi = Buf.ptr s₀ ⟨sa, so, 1024⟩) (fun s₀ s hp h => ?_) (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (mul_call oa oo fa fo ga go sa so hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ =>
      ⟨h₁, e₁, e₂, e₃, e₄, m₁ ▸ (hA s₀ s hp ha).2.1, m₁ ▸ (hA s₀ s hp ha).2.2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc]
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ h1 fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine ptrTo_ok hp c₂ h2 fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h3).1 fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem sampleC_piece (da dO aa ao ca co : Nat)
    (hc : (Y.ok ⟨da, dO, 34⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨ca, co, 2048⟩ && Y.sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 34⟩ ⟨ca, co, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true) (hN : 88 ≤ Y.stk)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨da, dO, 34⟩ ++
      ptrTo Y.sc .ecx ⟨aa, ao, 1024⟩ ++ ptrTo Y.sc .edx ⟨ca, co, 2048⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 72]) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun iters => sampleNTT iters (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (sampleC Y.sc ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      s₁.gpr .ecx = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨ca, co, 2048⟩)
      (fun s₀ s hp h => ?_) hA tt)
    (sample_call da dO aa ao ca co hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂, e₃⟩ => ⟨h₁, e₁, e₂, e₃⟩)
      (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, _, m₁, _⟩ ⟨s', ha', _, m₁', _⟩ => by
        rw [m₁, m₁']; exact hseed s₀ s₀' s s' hp hp' hq ha ha')
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ out => ?_)
  · simp only [List.append_assoc]
    rw [← List.append_nil (ptrTo Y.sc .edx _)]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ (Lay.okW_iff.mp h1).1 fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine ptrTo_ok hp c₂ (Lay.okW_iff.mp h2).1 fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  · rw [m₁] at fr out
    exact hQ s₀ s s' hp ha h' fr r₁ out

theorem ceC_piece {nm : String} {c : Prog isa} {ws : List Nat} (F : CeFn c ws) (d : Nat) (hd : d ∈ ws)
    (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) (callWith [.edi, .edx, .ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 d ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      s₁.gpr .edi = BitVec.ofNat 32 (32 * d)) (fun s₀ s hp h => ?_) (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (ce_call F d hd fa fo oa oo hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ =>
      ⟨h₁, e₁, e₂, e₃, e₄, m₁ ▸ (hA s₀ s hp ha).2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine ptrTo_ok hp c₂ (Lay.okW_iff.mp h1).1 fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem ddC_piece {nm : String} {c : Prog isa} {ws : List Nat} (F : DdFn c ws) (d : Nat) (hd : d ∈ ws)
    (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.seq (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) (callWith [.edi, .edx, .ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 (32 * d) ∧ s₁.gpr .edx = BitVec.ofNat 32 d ∧
      s₁.gpr .edi = Buf.ptr s₀ ⟨fa, fo, 1024⟩) (fun s₀ s hp h => ?_) hA tt)
    (dd_call F d hd ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂, e₃, e₄⟩ => ⟨h₁, e₁, e₂, e₃, e₄⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h1).1 fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlKem.X86.Top

end

end


/-!
# ML-KEM on x86 (32-bit): the code of a parameter set

The code over the `k` rows, entries or polynomials is a sequence (`seqs`) of
one piece per index (`Piece.seqs`). A parameter set's functions that compress
to `d_u` and `d_v` bits and decompress from them (`KemLay.ceCode`,
`KemLay.ddCode`) are leaves of the contracts of `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` for widths that include `d_u` and `d_v` (`CeOK`),
so their calls are pieces (`ceK_piece`, `ddK_piece`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open Lean Meta Elab Tactic in
/-- Proves `(Taint.check A τ c ?hint).isSome = true` with the hint `Taint.hintOf A τ c`, by the
kernel's evaluation of the check: for code that mentions the offsets of a parameter set that is not
given, which `taint_decide` cannot compute (it compiles the code), but whose analysis does not depend
on them. The goal is closed by `Eq.refl true` without the elaborator's check of it, whose heuristics
give up on some of these evaluations; the kernel checks it with the declaration (and rejects the
declaration if the check fails). -/
elab "taint_rfl" : tactic => do
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
    | throwError "taint_rfl: the goal is not an equation"
  unless rhs.isConstOf ``Bool.true do throwError "taint_rfl: the goal is not `… = true`"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "taint_rfl: the goal is not about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let h := args[4]!
  if h.isMVar then h.mvarId!.assign (mkApp4 (mkConst ``Taint.hintOf) args[0]! args[1]! args[2]! args[3]!)
  g.assign (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  replaceMainGoal []

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- `decide`, for a goal that mentions a parameter set that is not given but evaluates without it. -/
macro "rdecide" : tactic => `(tactic| exact of_decide_eq_true rfl)

/-- `f a`, …, `f (a + n - 1)`, then `c`, each from `P i` to `P (i + 1)`. -/
theorem _root_.VG.Proof.MlKem.X86.Piece.seqs {Pre : State → Prop} {Pub : State → State → Prop}
    {P : Nat → State → State → Prop} {f : Nat → Prog isa} {Q : State → State → Prop} {c : Prog isa} :
    ∀ (n a : Nat), (∀ i, a ≤ i → i < a + n → Piece Pre Pub (P i) (P (i + 1)) (f i)) →
      Piece Pre Pub (P (a + n)) Q c → Piece Pre Pub (P a) Q (seqs ((List.range' a n).map f) c)
  | 0, _, _, hc => hc
  | n + 1, a, h, hc => by
    rw [List.range'_succ, List.map_cons, Impl.MlKem.X86.seqs]
    exact .seq (h a (Nat.le_refl _) (by omega_using [])) (Piece.seqs n (a + 1) (fun i h₁ h₂ => h i (by omega_using [h₁]) (by omega_using [h₂]))
      (by rw [show a + 1 + n = a + (n + 1) by omega_using []]; exact hc))

/-- `f 0`, …, `f (n - 1)`, then `c`. -/
theorem _root_.VG.Proof.MlKem.X86.Piece.seqs0 {Pre : State → Prop} {Pub : State → State → Prop}
    {P : Nat → State → State → Prop} {f : Nat → Prog isa} {Q : State → State → Prop} {c : Prog isa} (n : Nat)
    (h : ∀ i < n, Piece Pre Pub (P i) (P (i + 1)) (f i)) (hc : Piece Pre Pub (P n) Q c) :
    Piece Pre Pub (P 0) Q (seqs ((List.range n).map f) c) := by
  rw [List.range_eq_range']
  exact Piece.seqs n 0 (fun i _ h₂ => h i (by omega_using [h₂])) (by rw [Nat.zero_add]; exact hc)

/-! ## Indices of a `k × k` matrix, row by row -/

theorem idx_mod {k i j : Nat} (hj : j < k) : (k * i + j) % k = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem idx_div {k i j : Nat} (hj : j < k) : (k * i + j) / k = i := by
  rw [Nat.mul_add_div (by omega_using [hj]), Nat.div_eq_of_lt hj, Nat.add_zero]

theorem idx_lt {k i j : Nat} (hi : i < k) (hj : j < k) : k * i + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)

/-! ## Buffers of `k` parts -/

theorem catK_congr {f g : Nat → List Byte} : ∀ {k : Nat}, (∀ i < k, f i = g i) → KPke.catK f k = KPke.catK g k
  | 0, _ => rfl
  | 1, h => h 0 (by decide)
  | k + 2, h => by
    show KPke.catK f (k + 1) ++ f (k + 1) = KPke.catK g (k + 1) ++ g (k + 1)
    rw [catK_congr fun i hi => h i (by omega_using [hi]), h (k + 1) (by omega_using [])]

/-- A part of a buffer within an argument is within it. -/
theorem Lay.ok_sub {Y : Lay} {a o l o' l' : Nat} (h : Y.ok ⟨a, o, l⟩ = true) (h₀ : 0 < l')
    (h₂ : o' + l' ≤ o + l) : Y.ok ⟨a, o', l'⟩ = true := by
  simp only [Lay.ok, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega_using [h₀, h₂, h]

/-- The bytes of `n` parts of `c` bytes each. -/
theorem bytes_catK {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o c : Nat} :
    ∀ {n : Nat}, Y.ok ⟨a, o, c * n⟩ = true →
      Spec.Sha3.bytesAt m (Buf.addr s₀ ⟨a, o, c * n⟩) (c * n) =
        KPke.catK (fun i => Spec.Sha3.bytesAt m (Buf.addr s₀ ⟨a, o + c * i, c⟩) c) n
  | 0, h => absurd h (by simp [Lay.ok])
  | 1, _ => by simp only [Nat.mul_one]; rfl
  | n + 2, h => by
    have hc : 0 < c := by
      simp only [Lay.ok, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Nat.pos_of_mul_pos_right h.1.2
    have e : c * (n + 2) = c * (n + 1) + c := Nat.mul_succ c (n + 1)
    rw [bytes_split hp m (o' := o + c * (n + 1)) (l₁ := c * (n + 1)) (l₂ := c) rfl e.symm
      (Lay.ok_sub h (Nat.mul_pos hc (Nat.succ_pos _)) (by omega_using [e]))
      (Lay.ok_sub h hc (by omega_using [e])),
      bytes_catK hp m (n := n + 1) (Lay.ok_sub h (Nat.mul_pos hc (Nat.succ_pos _))
        (by omega_using [e]))]
    rfl

/-- `copyW_piece`, for `l = 4n` bytes. -/
theorem copyW_piece' (sa so da dO n l : Nat) (hl : 4 * n = l) (hn : 0 < n) (hn' : n < 2 ^ 30)
    (hc : (Y.ok ⟨sa, so, l⟩ && Y.okW ⟨da, dO, l⟩ && Y.sep ⟨sa, so, l⟩ ⟨da, dO, l⟩) = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .edi ⟨sa, so, l⟩ ++
      ptrTo Y.sc .ebp ⟨da, dO, l⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 n))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, l⟩] s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, l⟩) l = Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨sa, so, l⟩) l →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (copyW Y.sc ⟨sa, so, l⟩ ⟨da, dO, l⟩ n) := by
  subst hl
  exact copyW_piece sa so da dO n hn hn' hc t₁ t₂ hA hQ

/-- The parameter set's leaves compress to `d_u` and `d_v` bits, and decompress from them. -/
class CeOK (L : KemLay) : Prop where
  ce : ∃ ws, L.p.du ∈ ws ∧ L.p.dv ∈ ws ∧ CeFn L.ceCode ws
  dd : ∃ ws, L.p.du ∈ ws ∧ L.p.dv ∈ ws ∧ DdFn L.ddCode ws

instance : CeOK L768 := ⟨⟨_, by decide, by decide, ce768⟩, ⟨_, by decide, by decide, dd768⟩⟩

variable {L : KemLay} [CeOK L]

theorem ceK_piece (d : Nat) (hd : d = L.p.du ∨ d = L.p.dv) (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ceK L Y.sc d ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) := by
  obtain ⟨ws, hu, hv, F⟩ := CeOK.ce (L := L)
  exact ceC_piece F d (by rcases hd with rfl | rfl <;> with_reducible assumption) fa fo oa oo hc hN tt hA hQ

theorem ddK_piece (d : Nat) (hd : d = L.p.du ∨ d = L.p.dv) (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ddK L Y.sc d ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) := by
  obtain ⟨ws, hu, hv, F⟩ := CeOK.dd (L := L)
  exact ddC_piece F d (by rcases hd with rfl | rfl <;> with_reducible assumption) ba bo fa fo hc hN tt hA hQ

end VG.Proof.MlKem.X86.Top
