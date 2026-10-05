import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86.CheckEk
import VerifiedGarbage.Proof.MlKem.X86.Sample
import VerifiedGarbage.Proof.MlKem.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86.Kem
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.MlKem.Contract
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86.Encrypt

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopPrim3`. -/
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
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧ s.gpr .edx = Buf.ptr s₀ ⟨ca, co, 2048⟩)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
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
      have := ctx_E hp h (N := 72) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨fit, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
  refine callR_piece Sample.verified VG.Proof.MlKem.X86.Top.sample_nosp (by decide) (by decide)
    (by rw [VG.Proof.MlKem.X86.Top.sample_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨da, dO, 34⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨aa, ao, 1024⟩, Buf.rgn s₀ ⟨ca, co, 2048⟩] ++ [below (E1 s₀) 12])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩]) (by simp [hA', hC]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2⟩ := entry s₀ s hp ha
    have hE' : 72 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 72) (by omega)
    have eA : argAddr (pushed [.edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 12).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 16 := by
      rw [callEntry_esp', h.esp]; rfl
    have bD := Buf.stkD hp hD (N := 4 * 3 + 4 + 56) (by omega)
    have bA := Buf.stkD hp hA₁ (N := 4 * 3 + 4 + 56) (by omega)
    have bC := Buf.stkD hp hC₁ (N := 4 * 3 + 4 + 56) (by omega)
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
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
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
    have ek := @ent_keep Y s₀ s hp h [.edx, .ecx, .eax] (by decide) (by simp; omega)
    have ek' := @ent_keep Y s₀' s' hp' h' [.edx, .ecx, .eax] (by decide) (by simp; omega)
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
    have ek := @ent_keep Y s₀ s hp h [.edx, .ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.edx, .ecx, .eax] s).callEntry = e at post
    sig_post [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂, setWidth_append32, g₂] at post
    rw [bytesAt_congr (ek hD)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 12) (N := 72) (by omega) (by omega)
      (by rw [VG.Proof.MlKem.X86.Top.sample_stack] at fr; exact fr)) post.1 post.2

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
  verified : Verified X86.target c (VG.Proof.MlKem.X86.Top.ceCon ws X86.abi 16)
  nosp : NoSp c
  stack : stackUse c = 16
  width : ∀ d ∈ ws, 32 * d < 2 ^ 32

/-- A leaf that decodes and decompresses from the widths `ws`, as `vg_mlkem_decode_decompress`
(`dd768`). -/
structure DdFn (c : Prog isa) (ws : List Nat) : Prop where
  verified : Verified X86.target c (VG.Proof.MlKem.X86.Top.ddCon ws X86.abi 16)
  nosp : NoSp c
  stack : stackUse c = 16
  width : ∀ d ∈ ws, 32 * d < 2 ^ 32

theorem ce768 : VG.Proof.MlKem.X86.Top.CeFn Impl.MlKem.X86.compressEncode compressWidths :=
  ⟨CompressEncode.verified, VG.Proof.MlKem.X86.Top.ce_nosp, VG.Proof.MlKem.X86.Top.ce_stack, fun _ => VG.Proof.MlKem.X86.Top.width_lt⟩

theorem dd768 : VG.Proof.MlKem.X86.Top.DdFn Impl.MlKem.X86.decodeDecompress compressWidths :=
  ⟨DecodeDecompress.verified, VG.Proof.MlKem.X86.Top.dd_nosp, VG.Proof.MlKem.X86.Top.dd_stack, fun _ => VG.Proof.MlKem.X86.Top.width_lt⟩

/-- `out ← ByteEncode_d(Compress_d(f))`, with `f` at `(fa, fo)` and the `32d` bytes `out` at `(oa, oo)`,
and `f`, `d`, `out`, `32d` in `eax`, `ecx`, `edx` and `edi`. -/
theorem ce_call {nm : String} {c : Prog isa} {ws : List Nat} (F : VG.Proof.MlKem.X86.Top.CeFn c ws) (d : Nat) (hd : d ∈ ws)
    (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = BitVec.ofNat 32 d ∧ s.gpr .edx = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      s.gpr .edi = BitVec.ofNat 32 (32 * d) ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO₁ := (Lay.okW_iff.mp hO).1
  have hd32 := F.width d hd
  have hd' : d < 2 ^ 32 := by omega
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = BitVec.ofNat 32 d ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = BitVec.ofNat 32 (32 * d) := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨fit, ?_, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
  refine call_piece F.verified F.nosp (by decide) (by decide)
    (by rw [F.stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 32 * d⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨oa, oo, 32 * d⟩]) (by simp [hO]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, -, -, -, -, rF⟩ := hA s₀ s hp ha
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    have hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega)
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bF := Buf.stkD hp hF (N := 4 * 4 + 4 + 16) (by omega)
    have bO := Buf.stkD hp hO₁ (N := 4 * 4 + 4 + 16) (by omega)
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
    sig_pre [VG.Proof.MlKem.X86.Top.ceCon, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd',
      toNat_ofNat32 hd32]
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
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
    sig_pub [VG.Proof.MlKem.X86.Top.ceCon, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [VG.Proof.MlKem.X86.Top.ceCon, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, toNat_ofNat32 hd', toNat_ofNat32 hd32] at post
    rw [polyAt_congr (ek hF)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [F.stack] at fr; exact fr)) post

/-- `f ← Decompress_d(ByteDecode_d(b))`, with the `32d` bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`,
and `b`, `32d`, `d`, `f` in `eax`, `ecx`, `edx` and `edi`. -/
theorem dd_call {nm : String} {c : Prog isa} {ws : List Nat} (F : VG.Proof.MlKem.X86.Top.DdFn c ws) (d : Nat) (hd : d ∈ ws)
    (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      s.gpr .ecx = BitVec.ofNat 32 (32 * d) ∧ s.gpr .edx = BitVec.ofNat 32 d ∧
      s.gpr .edi = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hB, hF⟩, dBF⟩ := hc
  have hF₁ := (Lay.okW_iff.mp hF).1
  have hd32 := F.width d hd
  have hd' : d < 2 ^ 32 := by omega
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = BitVec.ofNat 32 (32 * d) ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = BitVec.ofNat 32 d ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx, hdi⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨fit, ?_, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
  refine call_piece F.verified F.nosp (by decide) (by decide)
    (by rw [F.stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 32 * d⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [hF]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    have hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega)
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bB := Buf.stkD hp hB (N := 4 * 4 + 4 + 16) (by omega)
    have bF := Buf.stkD hp hF₁ (N := 4 * 4 + 4 + 16) (by omega)
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
    sig_pre [VG.Proof.MlKem.X86.Top.ddCon, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd',
      toNat_ofNat32 hd32]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
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
    sig_pub [VG.Proof.MlKem.X86.Top.ddCon, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [VG.Proof.MlKem.X86.Top.ddCon, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, toNat_ofNat32 hd', toNat_ofNat32 hd32] at post
    rw [bytesAt_congr (ek hB)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [F.stack] at fr; exact fr)) post

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopSeq`. -/
section

/-!
# ML-KEM on x86 (32-bit): the calls of the top-level functions, with their arguments

A buffer's address, computed by `ptrTo` from `esi` or from the argument on the
stack (`ptrTo_ok`); the block that sets a call's arguments (`setup_piece`,
whose addresses depend only on `esp` and `esi`); and each call with it
(`nttC_piece`, …), whose postcondition relates the state before the block to
the state after the call.
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## Single instructions -/

theorem Only.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) :
    Only [d] s ((arithFlags s x c o).setReg d x) :=
  ⟨fun r hr => by
    simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : r = d) => absurd (e ▸ List.mem_singleton_self d) hr]
    rfl, rfl, rfl, rfl⟩

theorem wp_movi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  wp_cons (s' := s.setReg d v) (by simp only [exec, readSrc, Option.map_some])
    (k _ (Only.setReg s d v) (by simp [State.setReg]))

theorem wp_addi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + v → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d + v) (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat))
      (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d (s.gpr d + v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_movr' {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  wp_movr (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem wp_movm' {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 4)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.mem.readW (s.ea (at_ b disp)) 32 → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ b disp)) :: is)) s Q :=
  wp_movm hin (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem Ctx.only {s₀ s s' : State} (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) {ds : List Reg} (o : Only ds s s')
    (hd : Reg.esp ∉ ds) (hd' : Reg.esi ∉ ds) : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' :=
  h.same (o.gpr _ hd) (o.gpr _ hd') o.rd o.wr o.mem

/-! ## Addresses -/

theorem ptrTo_ok {s₀ s : State} (hp : TPre Y s₀) (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) {b : Buf} (hb : Y.ok b = true) {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = b.ptr s₀ → WP isa (.block is) s' Q) :
    WP isa (.block (ptrTo Y.sc r b ++ is)) s Q := by
  obtain ⟨hb₁, -, -⟩ := Lay.ok_iff.mp hb
  unfold ptrTo
  rw [List.cons_append, List.singleton_append]
  split
  · rename_i e
    refine VG.Proof.MlKem.X86.Top.wp_movr' fun s₁ o₁ v₁ => ?_
    exact VG.Proof.MlKem.X86.Top.wp_addi fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂ |>.mono (by simp)) (by rw [v₂, v₁, h.esi, Buf.ptr, e])
  · have ea : s.ea (at_ .esp (20 + 4 * b.arg)) = argAddr s₀ b.arg := h.argEa
    refine VG.Proof.MlKem.X86.Top.wp_movm' (by rw [ea]; exact h.argIn hp hb₁) fun s₁ o₁ v₁ => ?_
    exact VG.Proof.MlKem.X86.Top.wp_addi fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂ |>.mono (by simp))
      (by rw [v₂, v₁, ea, h.argw hp hb₁])

/-- A block that sets registers, whose addresses depend only on `esp` and `esi`. -/
theorem setup_piece {is : List Instr} (P : State → State → Prop)
    (hw : ∀ s₀ s, TPre Y s₀ → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s → WP isa (.block is) s fun s₁ => VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    {ht : Taint.Hint VG.X86.Taint.T} (t : (VG.X86.taint.check (τr [.esp, .esi]) (.block is) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
      (.block is) :=
  Piece.taint [.esp, .esi] (fun s₀ s hp ha => (hw s₀ s hp (hA s₀ s hp ha)).mono fun s₁ h₁ => ⟨s, ha, h₁⟩)
    (fun s₀ s₀' s s' hp _ hq ha ha' r hr => by
      have h := hA s₀ s hp ha
      have h' := hA s₀' s' ‹_› ha'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.esp, h'.esp, hq.E1]
      · rw [h.esi, h'.esi, hq.sc hp]) t

/-- Two addresses, in `eax` and `ecx`. -/
theorem ptr2_ok {s₀ s : State} (hp : TPre Y s₀) (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) {b₀ b₁ : Buf} (h₀ : Y.ok b₀ = true)
    (h₁ : Y.ok b₁ = true) :
    WP isa (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) s fun s' => VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .eax = b₀.ptr s₀ ∧ s'.gpr .ecx = b₁.ptr s₀ := by
  rw [← List.append_nil (ptrTo Y.sc .ecx b₁)]
  refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h h₀ fun s₁ o₁ v₁ => ?_
  have c₁ := h.only o₁ (by decide) (by decide)
  refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₁ h₁ fun s₂ o₂ v₂ => WP.block_nil_iff.mpr ?_
  exact ⟨c₁.only o₂ (by decide) (by decide), o₂.mem.trans o₁.mem, by rw [o₂.gpr _ (by decide), v₁], v₂⟩

/-- The block setting two addresses. -/
theorem setup2 {b₀ b₁ : Buf} (h₀ : Y.ok b₀ = true) (h₁ : Y.ok b₁ = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    {ht : Taint.Hint VG.X86.Taint.T}
    (t : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧
      (s₁.gpr .eax = b₀.ptr s₀ ∧ s₁.gpr .ecx = b₁.ptr s₀)) (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) :=
  VG.Proof.MlKem.X86.Top.setup_piece _ (fun _ _ hp h => (VG.Proof.MlKem.X86.Top.ptr2_ok hp h h₀ h₁).mono fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩) hA t

/-- `f ← NTT(f)` or `NTT⁻¹(f)`, with its arguments. -/
theorem inPlaceC_piece {t : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (hsp : NoSp c) (hst : stackUse c = 16)
    (fa fo sa so : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨sa, so, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨sa, so, 1024⟩)) (callWith [.ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup2 (Lay.okW_iff.mp hc'.1.1).1 (Lay.okW_iff.mp hc'.1.2).1 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (inPlace_call hv hsp hst fa fo sa so hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2⟩) fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← op(f, g)` (`vg_mlkem_add` or `vg_mlkem_sub`), with its arguments. -/
theorem accC_piece {op : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (hsp : NoSp c) (hst : stackUse c = 16) (fa fo ga go : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨ga, go, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨ga, go, 1024⟩)) (callWith [.ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup2 (Lay.okW_iff.mp hc'.1.1).1 hc'.1.2 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (acc_call hv hsp hst fa fo ga go hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2.1, m₁ ▸ (hA s₀ s hp ha).2.2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← SamplePolyCBD₂(b)`, with its arguments. -/
theorem cbd2C_piece (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 128⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨ba, bo, 128⟩ ++ ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 128⟩) 128)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (cbd2C Y.sc ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 hA tt)
    (cbd2_call ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂⟩ => ⟨h₁, e₁, e₂⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `o ← ByteEncode₁₂(f)`, with its arguments. -/
theorem enc12C_piece (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 384⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨oa, oo, 384⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 384⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 384⟩) 384 =
        encode12 (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (enc12C Y.sc ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (encode12_call fa fo oa oo hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2⟩) fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← ByteDecode₁₂(b)`, with its arguments. -/
theorem dec12C_piece (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 384⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨ba, bo, 384⟩ ++ ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decode12 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 384⟩) 384)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (dec12C Y.sc ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 hA tt)
    (decode12_call ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂⟩ => ⟨h₁, e₁, e₂⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopSeq2`. -/
section

/-!
# ML-KEM on x86 (32-bit): the calls of three and four arguments, with their arguments

As `TopSeq.lean`, for `vg_mlkem_multiply_ntts`, `vg_mlkem_sample_ntt`, and
the leaves that compress and decompress (`CeFn`, `DdFn`).
-/

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
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (multiplyNTTs (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (mulC Y.sc ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨oa, oo, 1024⟩ ∧
      s₁.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧
      s₁.gpr .edi = Buf.ptr s₀ ⟨sa, so, 1024⟩) (fun s₀ s hp h => ?_) (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (mul_call oa oo fa fo ga go sa so hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ =>
      ⟨h₁, e₁, e₂, e₃, e₄, m₁ ▸ (hA s₀ s hp ha).2.1, m₁ ▸ (hA s₀ s hp ha).2.2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc]
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₁ h1 fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₂ h2 fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₃ (Lay.okW_iff.mp h3).1 fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
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
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 72]) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun iters => sampleNTT iters (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (sampleC Y.sc ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      s₁.gpr .ecx = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨ca, co, 2048⟩)
      (fun s₀ s hp h => ?_) hA tt)
    (VG.Proof.MlKem.X86.Top.sample_call da dO aa ao ca co hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂, e₃⟩ => ⟨h₁, e₁, e₂, e₃⟩)
      (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, _, m₁, _⟩ ⟨s', ha', _, m₁', _⟩ => by
        rw [m₁, m₁']; exact hseed s₀ s₀' s s' hp hp' hq ha ha')
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ out => ?_)
  · simp only [List.append_assoc]
    rw [← List.append_nil (ptrTo Y.sc .edx _)]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₁ (Lay.okW_iff.mp h1).1 fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₂ (Lay.okW_iff.mp h2).1 fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  · rw [m₁] at fr out
    exact hQ s₀ s s' hp ha h' fr r₁ out

theorem ceC_piece {nm : String} {c : Prog isa} {ws : List Nat} (F : VG.Proof.MlKem.X86.Top.CeFn c ws) (d : Nat) (hd : d ∈ ws)
    (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) (callWith [.edi, .edx, .ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 d ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      s₁.gpr .edi = BitVec.ofNat 32 (32 * d)) (fun s₀ s hp h => ?_) (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (VG.Proof.MlKem.X86.Top.ce_call F d hd fa fo oa oo hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ =>
      ⟨h₁, e₁, e₂, e₃, e₄, m₁ ▸ (hA s₀ s hp ha).2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₂ (Lay.okW_iff.mp h1).1 fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem ddC_piece {nm : String} {c : Prog isa} {ws : List Nat} (F : VG.Proof.MlKem.X86.Top.DdFn c ws) (d : Nat) (hd : d ∈ ws)
    (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.seq (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) (callWith [.edi, .edx, .ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 (32 * d) ∧ s₁.gpr .edx = BitVec.ofNat 32 d ∧
      s₁.gpr .edi = Buf.ptr s₀ ⟨fa, fo, 1024⟩) (fun s₀ s hp h => ?_) hA tt)
    (VG.Proof.MlKem.X86.Top.dd_call F d hd ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂, e₃, e₄⟩ => ⟨h₁, e₁, e₂, e₃, e₄⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₃ (Lay.okW_iff.mp h1).1 fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopHash`. -/
section

/-!
# ML-KEM on x86 (32-bit): SHA-3 and SHAKE in the top-level functions

The Keccak state set to zero (`zeroTop_piece`), the Keccak calls with their
arguments (`absorbC_piece`, `padC_piece`, `squeezeC_piece`), and a SHA-3 or
SHAKE function of one or two buffers (`hash1_piece`, `hash2_piece`): the
output is `squeezeFrom` of the padded state (`Proof/MlKem/KPke.lean`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (Repr bytesAt stateAt squeezeFrom absorb pad rates)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- A loop of `N ≥ 1` iterations of a block, counting down with `sub ecx, 1`. -/
theorem wp_count {body : List Instr} {N : Nat} (hN : 0 < N) (I : Nat → State → Prop) {s : State}
    (h0 : I 0 s)
    (hs : ∀ k < N, ∀ s, I k s → WP isa (.block body) s fun s' => I (k + 1) s' ∧
      isa.eval .ne s' = some (decide (k + 1 < N))) :
    WP isa (.loop (.block body) .ne) s (I N) := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = N - k ∧ k < N ∧ I k s)
    (fun n s hi => ?_) N s ⟨0, (Nat.sub_zero N).symm, hN, h0⟩
  obtain ⟨k, hn, hk, hi⟩ := hi
  refine (hs k hk _ hi).mono fun s' ⟨hi', hc⟩ => ?_
  by_cases h : k + 1 < N
  · exact .inr ⟨by rw [hc, decide_eq_true h], N - (k + 1), by omega, k + 1, rfl, h, hi'⟩
  · exact .inl ⟨by rw [hc, decide_eq_false h], by rw [show N = k + 1 by omega]; exact hi'⟩

theorem wp_subi_last {d : Reg} {v : BitVec 32} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.zf = some (s.gpr d - v == 0) → Q s') :
    WP isa (.block [.alu .sub d (.imm v)]) s Q := by
  refine wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some]) (WP.block_nil_iff.mpr ?_)
  exact k _ (Only.flags s d _ _ _) (by simp [State.setReg]) rfl

/-! ## The Keccak state set to zero -/

theorem zeroTop_piece (st : Nat) (hc : Y.okW ⟨Y.sc, st, 200⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (zeroTop st) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 0]) s.mem s'.mem →
      stateAt s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (zeroTop st) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have fit : (Buf.ptr s₀ ⟨Y.sc, st, 200⟩).toNat + 200 ≤ 2 ^ 32 := Buf.fit hp hc₁
    refine WP.seq (VG.Proof.MlKem.X86.Top.wp_movr' fun s₁ o₁ v₁ => VG.Proof.MlKem.X86.Top.wp_addi fun s₂ o₂ v₂ => VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ =>
      VG.Proof.MlKem.X86.Top.wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_)
    have o := (((o₁.trans o₂).trans o₃).trans o₄).mono (es := [.edx, .eax, .ecx]) (by simp)
    have c₄ := h.only o (by decide) (by decide)
    let I : Nat → State → Prop := fun k u => VG.Proof.MlKem.X86.Top.Ctx Y s₀ u ∧
      u.gpr .edx = Buf.ptr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (50 - k) ∧
      u.gpr .eax = 0 ∧ Frame [Buf.rgn s₀ ⟨Y.sc, st, 200⟩] s.mem u.mem ∧
      ∀ j < 4 * k, u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 j) = 0
    have i0 : I 0 s₄ := ⟨c₄, by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂, v₁, h.esi]; simp,
      v₄, by rw [o₄.gpr _ (by decide), v₃], by rw [o.mem]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    refine (VG.Proof.MlKem.X86.Top.wp_count (N := 50) (by decide) I i0 fun k hk u hu => ?_).mono fun u hu => ?_
    · obtain ⟨cu, eu, ecu, eau, fu, zu⟩ := hu
      have ea : u.ea (at_ .edx 0) = Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, eu]
        rw [ea_add (by omega)]
        rfl
      have hin : InRegions u.wr (u.ea (at_ .edx 0)) 4 := by
        rw [ea]; exact Buf.inRegW hp hc₁ hc₂ cu.wr (by show 4 * k + 4 ≤ 200; omega)
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 4 * k) (n := 4) (by show 4 * k + 4 ≤ 200; omega)
      have cm : VG.Proof.MlKem.X86.Top.Ctx Y s₀ { u with
                                  mem := u.mem.writeW (u.ea (at_ .edx 0)) (u.gpr .eax) } :=
        ⟨cu.esp, cu.rd, cu.wr, cu.esi, by rw [ea]; exact cu.frame.writeW hr _ hcr⟩
      refine wp_store hin (VG.Proof.MlKem.X86.Top.wp_addi fun u₁ o₁ v₁ => VG.Proof.MlKem.X86.Top.wp_subi_last fun u₂ o₂ v₂ z₂ => ?_)
      have cm₂ := (cm.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
      have m₂ : u₂.mem = u.mem.writeW (Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32) := by
        rw [o₂.mem, o₁.mem, ← eau, ← ea]
      have x₂ : u₂.gpr .ecx = BitVec.ofNat 32 (50 - (k + 1)) := by
        rw [v₂, o₁.gpr _ (by decide)]; exact (congrArg (· - 1) ecu).trans (cnt_next hk)
      refine ⟨⟨cm₂, ?_, x₂, by rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide)]; exact eau, ?_, ?_⟩, ?_⟩
      · rw [o₂.gpr _ (by decide), v₁, eu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [m₂]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨Buf.addr s₀ ⟨Y.sc, st, 200⟩, 200⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      · rw [m₂]; exact Sample.zero_write zu
      · show u₂.zf.map (!·) = _
        have e₁ : u₁.gpr .ecx = BitVec.ofNat 32 (50 - k) := (o₁.gpr _ (by decide)).trans ecu
        rw [z₂, e₁]; exact cnt_ne hk (by decide)
    · obtain ⟨cu, -, -, -, fu, zu⟩ := hu
      exact hQ s₀ s u hp ha cu (fu.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
        (Sample.stateAt_zero fun j hj => zu j (by omega))
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## The Keccak calls, with their arguments -/

theorem absorbC_piece (st wk rate pos : Nat) (b : Buf) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ &&
      Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : b.len < 2 ^ 32)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 pos))] : List Instr) ++
      ptrTo Y.sc .ebx b ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate msg → pos = msg.length % rate →
        Repr s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (msg ++ bytesAt s.mem (b.addr s₀) b.len)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (absorbC Y.sc st wk rate pos b) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩) (b.ptr s₀)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate pos b.len) (fun s₀ s hp h => ?_) hA tt)
    (absorb_call Y.sc st Y.sc wk b rate pos hr hpos hc hN hlen (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₃ h2 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem padC_piece (st wk rate pos sfx : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true)
    (hN : 56 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 pos)),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate msg → pos = msg.length % rate →
        stateAt s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) =
          absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (padC Y.sc st wk rate pos sfx) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => PadArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate pos sfx) (fun s₀ s hp h => ?_) hA tt)
    (pad_call Y.sc st Y.sc wk rate pos sfx hr hpos hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => VG.Proof.MlKem.X86.Top.wp_movi fun s₄ o₄ v₄ => ?_
    have c₄ := ((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
      (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₄ (Lay.okW_iff.mp h1).1 fun s₅ o₅ v₅ => WP.block_nil_iff.mpr ?_
    refine ⟨c₄.only o₅ (by decide) (by decide),
      o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem))), ⟨?_, ?_, ?_, ?_, v₅⟩⟩
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₅.gpr _ (by decide), v₄]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem squeezeC_piece (st wk rate : Nat) (o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.okW o && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ &&
      Y.sep ⟨Y.sc, st, 200⟩ o && Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : o.len < 2 ^ 32)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, o, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩)) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (squeezeC Y.sc st wk rate o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩) (o.ptr s₀)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate 0 o.len) (fun s₀ s hp h => ?_) hA tt)
    (squeeze_call Y.sc st Y.sc wk o rate 0 hr (Nat.zero_le _) hc hN hlen
      (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ _ => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₂ o₂ v₂ => VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₃ (Lay.okW_iff.mp h2).1 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]; rfl
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr r₁
    exact hQ s₀ s s' hp ha h' fr r₁

/-! ## Hashes -/

/-- The frame of the Keccak calls: the state, the working space and their stack. -/
abbrev kF (st wk : Nat) (Y : Lay) (s₀ : State) : List Region :=
  [⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]

theorem kF_zero {s₀ : State} (hp : TPre Y s₀) {st wk : Nat} (hN : 56 ≤ Y.stk) {m m' : Mem}
    (fr : Frame ([⟨Y.sc, st, 200⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 0]) m m') : Frame (VG.Proof.MlKem.X86.Top.kF st wk Y s₀) m m' :=
  fr.sub fun r hr => by
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (E1 s₀) 40, by simp, stk_sub hp (by omega) (by omega)⟩

theorem kF_bytes {s₀ : State} (hp : TPre Y s₀) {st wk : Nat} (hN : 56 ≤ Y.stk) {b : Buf} (hb : Y.ok b = true)
    (hs : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩) = true)
    {m m' : Mem} (fr : Frame (VG.Proof.MlKem.X86.Top.kF st wk Y s₀) m m') : bytesAt m' (b.addr s₀) b.len = bytesAt m (b.addr s₀) b.len := by
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨h₁, h₂⟩, d₁⟩, d₂⟩ := hs
  exact bytesAt_frame fr (Buf.frD hp hb (bs := [⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩])
    (by simp [(Lay.okW_iff.mp h₁).1, (Lay.okW_iff.mp h₂).1, d₁, d₂]) (by omega))
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega)

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b₁` and `b₂`, into `o`. -/
theorem hash2_piece (st wk rate sfx : Nat) (b₁ b₂ o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b₁ && Y.ok b₂ && Y.okW o &&
      Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ && Y.sep b₁ ⟨Y.sc, st, 200⟩ && Y.sep b₁ ⟨Y.sc, wk, 640⟩ &&
      Y.sep b₂ ⟨Y.sc, st, 200⟩ && Y.sep b₂ ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ o &&
      Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk)
    (hl₁ : b₁.len < 2 ^ 32) (hl₂ : b₂.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    {h₀ h₁ h₂ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₀ : (VG.X86.taint.check (τr [.esi]) (zeroTop st) h₀).isSome = true)
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 0))] : List Instr) ++
      ptrTo Y.sc .ebx b₁ ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b₁.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 (b₁.len % rate)))] : List Instr) ++
      ptrTo Y.sc .ebx b₂ ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b₂.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 ((b₁.len + b₂.len) % rate))),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₃).isSome = true)
    (t₄ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₄).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len))) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (hash2 Y.sc st wk rate sfx b₁ b₂ o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb₁⟩, hb₂⟩, hO⟩, dSW⟩, d₁S⟩, d₁W⟩, d₂S⟩, d₂W⟩, dSO⟩, dOW⟩ := hc'
  have hrate := (rate_lt hr)
  have hr0 : 0 < rate := by simp [rates] at hr; omega
  -- after zeroing, absorbing `b₁`, absorbing `b₂`, padding
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx Y s₀ u ∧ Frame (VG.Proof.MlKem.X86.Top.kF st wk Y s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (bytesAt s.mem (b₁.addr s₀) b₁.len)) ∧
    (i = 2 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)))
  have cS : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (VG.Proof.MlKem.X86.Top.zeroTop_piece st hS t₀ hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', VG.Proof.MlKem.X86.Top.kF_zero hp hN fr, fun _ => z, by simp, by simp, by simp⟩) ?_
  refine Piece.seq (B := P 1) (VG.Proof.MlKem.X86.Top.absorbC_piece st wk rate 0 b₁ hr hr0 (by simp [hS, hW, hb₁, dSW, d₁S, d₁W])
    hN hl₁ t₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, VG.Proof.MlKem.X86.Top.kF_bytes hp hN hb₁ (by simp [hS, hW, d₁S, d₁W]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp, by simp⟩
  refine Piece.seq (B := P 2) (VG.Proof.MlKem.X86.Top.absorbC_piece st wk rate (b₁.len % rate) b₂ hr (Nat.mod_lt _ hr0)
    (by simp [hS, hW, hb₂, dSW, d₂S, d₂W]) hN hl₂ t₂ (fun s₀ u _ ⟨_, _, h, _⟩ => h)
    fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · have r' := post _ (r rfl) (by rw [bytesAt_length])
    rw [VG.Proof.MlKem.X86.Top.kF_bytes hp hN hb₂ (by simp [hS, hW, d₂S, d₂W]) fu] at r'
    exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => r', by simp⟩
  refine Piece.seq (B := P 3) (VG.Proof.MlKem.X86.Top.padC_piece st wk rate ((b₁.len + b₂.len) % rate) sfx hr (Nat.mod_lt _ hr0) cS hN t₃
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, by simp,
      fun _ => post _ (r rfl) (by rw [List.length_append, bytesAt_length, bytesAt_length])⟩
  refine VG.Proof.MlKem.X86.Top.squeezeC_piece st wk rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hN hlo t₄
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [VG.Proof.MlKem.X86.Top.kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b`, into `o`. -/
theorem hash1_piece (st wk rate sfx : Nat) (b o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b && Y.okW o &&
      Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ && Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩ &&
      Y.sep ⟨Y.sc, st, 200⟩ o && Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk)
    (hl : b.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    {h₀ h₁ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₀ : (VG.X86.taint.check (τr [.esi]) (zeroTop st) h₀).isSome = true)
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 0))] : List Instr) ++
      ptrTo Y.sc .ebx b ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₁).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 (b.len % rate))),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₃).isSome = true)
    (t₄ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₄).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b.addr s₀) b.len))) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (hash1 Y.sc st wk rate sfx b o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb⟩, hO⟩, dSW⟩, dbS⟩, dbW⟩, dSO⟩, dOW⟩ := hc'
  have hr0 : 0 < rate := by simp [rates] at hr; omega
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Top.Ctx Y s₀ u ∧ Frame (VG.Proof.MlKem.X86.Top.kF st wk Y s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (bytesAt s.mem (b.addr s₀) b.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b.addr s₀) b.len)))
  have cS : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (VG.Proof.MlKem.X86.Top.zeroTop_piece st hS t₀ hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', VG.Proof.MlKem.X86.Top.kF_zero hp hN fr, fun _ => z, by simp, by simp⟩) ?_
  refine Piece.seq (B := P 1) (VG.Proof.MlKem.X86.Top.absorbC_piece st wk rate 0 b hr hr0 (by simp [hS, hW, hb, dSW, dbS, dbW])
    hN hl t₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, VG.Proof.MlKem.X86.Top.kF_bytes hp hN hb (by simp [hS, hW, dbS, dbW]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp⟩
  refine Piece.seq (B := P 3) (VG.Proof.MlKem.X86.Top.padC_piece st wk rate (b.len % rate) sfx hr (Nat.mod_lt _ hr0) cS hN t₃
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => post _ (r rfl) (by rw [bytesAt_length])⟩
  refine VG.Proof.MlKem.X86.Top.squeezeC_piece st wk rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hN hlo t₄
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [VG.Proof.MlKem.X86.Top.kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopLocal`. -/
section

/-!
# ML-KEM on x86 (32-bit): the code of the top-level functions between calls

Storing a byte in `scratch` (`st8_piece`), copying words (`copyW_piece`), and,
after a call of `vg_mlkem_sample_ntt`, keeping the AND of the values it
returned and masking the polynomial it sampled (`maskA_piece`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem wp_andr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d &&& s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d &&& s.gpr r) false false).setReg d (s.gpr d &&& s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_subr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - s.gpr r) (decide ((s.gpr d).toNat < (s.gpr r).toNat))
      (subOverflow (s.gpr d) (s.gpr r) (s.gpr d - s.gpr r))).setReg d (s.gpr d - s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_store' {b r : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 4)
    (k : ∀ s', (∀ x, s'.gpr x = s.gpr x) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (s.ea (at_ b disp)) (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ b disp) r :: is)) s Q :=
  wp_store hin (k _ (fun _ => rfl) rfl rfl rfl)

theorem wp_store8 {b : Reg} {r : Reg8} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 1)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (s.ea (at_ b disp)) ((s.gpr r.reg).setWidth 8) } Q) :
    WP isa (.block (.store8 (at_ b disp) r :: is)) s Q :=
  wp_cons (by simp only [exec, State.store8, hin, ite_true]) k

/-! ## A byte -/

theorem st8_piece (o v : Nat) (hc : Y.okW ⟨Y.sc, o, 1⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block (st8 o v)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block (st8 o v)) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have ea : (s.gpr .esi + BitVec.ofNat 32 o).setWidth 64 = Buf.addr s₀ ⟨Y.sc, o, 1⟩ := by rw [h.esi]
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 1) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    have hin : InRegions s.wr (Buf.addr s₀ ⟨Y.sc, o, 1⟩) 1 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 1) (Nat.le_refl _)
      simpa using this
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₁ o₁ v₁ => ?_
    have h₁ := h.only o₁ (by decide) (by decide)
    have ea₁ : s₁.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 1⟩ := by
      simp only [State.ea, at_]; rw [o₁.gpr _ (by decide)]; exact ea
    refine VG.Proof.MlKem.X86.Top.wp_store8 (by rw [ea₁, h₁.wr, ← h.wr]; exact hin) (WP.block_nil_iff.mpr ?_)
    refine hQ s₀ s _ hp ha ⟨h₁.esp, h₁.rd, h₁.wr, h₁.esi, ?_⟩ ?_
    · show Frame _ _ (s₁.mem.writeW _ _)
      rw [ea₁]; exact h₁.frame.writeW (w := 8) hr _ hcr
    · show s₁.mem.writeW _ _ = _
      rw [ea₁, o₁.mem, show s₁.gpr Reg8.al.reg = BitVec.ofNat 32 v from v₁]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## Copying words -/

/-- The bytes after a word is written at offset `4k`. -/
theorem wordw_bytes {m : Mem} {d : Addr} {w : BitVec 32} {k j : Nat} (hk : 4 * k + 4 < 2 ^ 64)
    (hj : j < 4 * k + 4) :
    (m.writeW (d + BitVec.ofNat 64 (4 * k)) w) (d + BitVec.ofNat 64 j) =
      if 4 * k ≤ j then w.extractLsb' (8 * (j - 4 * k)) 8 else m (d + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW, Mem.write]
  by_cases e : 4 * k ≤ j
  · have t : (d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k))).toNat = j - 4 * k := by
      rw [show d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 (j - 4 * k) by
        rw [show j = 4 * k + (j - 4 * k) by omega, BitVec.ofNat_add]; bv_omega]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left e, t, ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right e, ite_eq_right fun h => ?_]
    have t : (d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k))).toNat = 2 ^ 64 - (4 * k - j) := by
      have : d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 j - BitVec.ofNat 64 (4 * k) := by
        bv_omega
      rw [this, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
        Nat.mod_eq_of_lt (a := 4 * k) (by omega)]
      omega
    rw [t] at h
    omega

theorem copyW_piece (sa so da dO n : Nat) (hn : 0 < n) (hn' : n < 2 ^ 30)
    (hc : (Y.ok ⟨sa, so, 4 * n⟩ && Y.okW ⟨da, dO, 4 * n⟩ && Y.sep ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩) = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .edi ⟨sa, so, 4 * n⟩ ++
      ptrTo Y.sc .ebp ⟨da, dO, 4 * n⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 n))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, 4 * n⟩] s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, 4 * n⟩) (4 * n) = bytesAt s.mem (Buf.addr s₀ ⟨sa, so, 4 * n⟩) (4 * n) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (copyW Y.sc ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩ n) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, hD⟩, dSD⟩ := hc'
  have hD₁ := (Lay.okW_iff.mp hD).1
  let S : Buf := ⟨sa, so, 4 * n⟩
  let D : Buf := ⟨da, dO, 4 * n⟩
  refine Piece.seq (VG.Proof.MlKem.X86.Top.setup_piece (fun s₀ s₁ => s₁.gpr .edi = S.ptr s₀ ∧ s₁.gpr .ebp = D.ptr s₀ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n) (fun s₀ s hp h => ?_) hA t₁) ?_
  · simp only [List.append_assoc]
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp h hS fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.ptrTo_ok hp c₁ hD₁ fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  refine Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃⟩ => ?_)
    (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃⟩ ⟨_, _, _, _, e₁', e₂', e₃'⟩ r hr => ?_) t₂
  · have fS : (S.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hS
    have fD : (D.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hD₁
    have dd := Buf.disj hp hS hD₁ dSD
    let I : Nat → State → Prop := fun k u => VG.Proof.MlKem.X86.Top.Ctx Y s₀ u ∧ u.gpr .edi = S.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ebp = D.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (n - k) ∧
      Frame [D.rgn s₀] s.mem u.mem ∧ ∀ j < 4 * k, u.mem (D.addr s₀ + BitVec.ofNat 64 j) = s.mem (S.addr s₀ + BitVec.ofNat 64 j)
    have i0 : I 0 s₁ := ⟨h₁, by rw [e₁]; simp, by rw [e₂]; simp, e₃, by rw [m₁]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    refine (VG.Proof.MlKem.X86.Top.wp_count hn I i0 fun k hk u ⟨cu, du, bu, xu, fu, cpu⟩ => ?_).mono fun u ⟨cu, _, _, _, fu, cpu⟩ => ?_
    · have eS : u.ea (at_ .edi 0) = S.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, du]; rw [ea_add (by omega)]; rfl
      have eD : u.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, bu]; rw [ea_add (by omega)]; rfl
      have hinS : InRegions (u.rd ++ u.wr) (S.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegR hp hS cu.rd cu.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine VG.Proof.MlKem.X86.Top.wp_movm' (by rw [eS]; exact hinS) fun u₁ o₁ v₁ => ?_
      have c₁ := cu.only o₁ (by decide) (by decide)
      have eD₁ : u₁.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        rw [← eD]; simp only [State.ea, at_, o₁.gpr _ (by decide : Reg.ebp ∉ [Reg.eax])]
      have hinD : InRegions u₁.wr (D.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegW hp hD₁ (Lay.okW_iff.mp hD).2 c₁.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine VG.Proof.MlKem.X86.Top.wp_store' (by rw [eD₁]; exact hinD) fun u₂ g₂ r₂ w₂ m₂ => ?_
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hD₁ (Lay.okW_iff.mp hD).2 (o := 4 * k) (n := 4)
        (show 4 * k + 4 ≤ 4 * n by omega)
      have c₂ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ u₂ := ⟨by rw [g₂]; exact c₁.esp, by rw [r₂]; exact c₁.rd, by rw [w₂]; exact c₁.wr,
        by rw [g₂]; exact c₁.esi, by rw [m₂, eD₁]; exact c₁.frame.writeW hr _ hcr⟩
      refine VG.Proof.MlKem.X86.Top.wp_addi fun u₃ o₃ v₃ => VG.Proof.MlKem.X86.Top.wp_addi fun u₄ o₄ v₄ => VG.Proof.MlKem.X86.Top.wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
      have c₅ := ((c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)).only o₅ (by decide)
        (by decide)
      have m₅ : u₅.mem = u₁.mem.writeW (D.addr s₀ + BitVec.ofNat 64 (4 * k)) (u.mem.readW (S.addr s₀ +
          BitVec.ofNat 64 (4 * k)) 32) := by
        rw [o₅.mem, o₄.mem, o₃.mem, m₂, eD₁, v₁, eS]
      have ex : u₄.gpr .ecx = BitVec.ofNat 32 (n - k) := by
        rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), xu]
      refine ⟨⟨c₅, ?_, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_⟩, ?_⟩
      · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃, g₂, o₁.gpr _ (by decide), du]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [o₅.gpr _ (by decide), v₄, o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), bu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [m₅, o₁.mem]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨D.addr s₀, 4 * n⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      · intro j hj
        rw [m₅, o₁.mem, VG.Proof.MlKem.X86.Top.wordw_bytes (by omega) hj]
        split
        · rename_i e
          rw [← Mem.readW_byte _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
            show 4 * k + (j - 4 * k) = j by omega]
          exact fu.bytes (R := S.rgn s₀) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact dd) (by show 4 * n ≤ 2 ^ 64; omega)
            (show j < 4 * n by omega)
        · exact cpu j (by omega)
      · show u₅.zf.map (!·) = _
        rw [z₅, ex]; exact cnt_ne hk (by omega)
    · refine hQ s₀ s u hp ha cu fu ?_
      exact List.map_congr_left fun j hj => cpu j (List.mem_range.mp hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.ptr hS]
    · rw [e₂, e₂', hq.ptr hD₁]
    · rw [e₃, e₃']

/-! ## After `SampleNTT` -/

theorem maskA_piece (ao po : Nat)
    (hc : (Y.okW ⟨Y.sc, ao, 4⟩ && Y.okW ⟨Y.sc, po, 1024⟩ && Y.sep ⟨Y.sc, ao, 4⟩ ⟨Y.sc, po, 1024⟩) = true)
    {ht : Taint.Hint VG.X86.Taint.T} (tt : (VG.X86.taint.check (τr [.esi]) (maskA ao po) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨Y.sc, ao, 4⟩, Buf.rgn s₀ ⟨Y.sc, po, 1024⟩] s.mem s'.mem →
      s'.mem.readW (Buf.addr s₀ ⟨Y.sc, ao, 4⟩) 32 = s.mem.readW (Buf.addr s₀ ⟨Y.sc, ao, 4⟩) 32 &&& s.gpr .eax →
      (∀ i < 256, coeffAt s'.mem (Buf.addr s₀ ⟨Y.sc, po, 1024⟩) i =
        coeffAt s.mem (Buf.addr s₀ ⟨Y.sc, po, 1024⟩) i &&& (0 - s.gpr .eax)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (maskA ao po) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hC, hP⟩, dCP⟩ := hc'
  have hC₁ := (Lay.okW_iff.mp hC).1
  have hP₁ := (Lay.okW_iff.mp hP).1
  let C : Buf := ⟨Y.sc, ao, 4⟩
  let P : Buf := ⟨Y.sc, po, 1024⟩
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have dd := Buf.disj hp hC₁ hP₁ dCP
    have fP : (P.ptr s₀).toNat + 1024 ≤ 2 ^ 32 := Buf.fit hp hP₁
    have eC : ∀ u : State, u.gpr .esi = arg s₀ Y.sc → u.ea (at_ .esi ao) = C.addr s₀ := fun u e => by
      simp only [State.ea, at_, e]; rfl
    obtain ⟨rC, hrC, hcC⟩ := Buf.contains hp hC₁ (Lay.okW_iff.mp hC).2 (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcC
    have inC : InRegions (s.rd ++ s.wr) (C.addr s₀) 4 := by
      have := Buf.inRegR hp hC₁ h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have inCw : InRegions s.wr (C.addr s₀) 4 := by
      have := Buf.inRegW hp hC₁ (Lay.okW_iff.mp hC).2 h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine WP.seq (VG.Proof.MlKem.X86.Top.wp_movi fun s₁ o₁ v₁ => VG.Proof.MlKem.X86.Top.wp_subr fun s₂ o₂ v₂ => ?_)
    have c₂ := (h.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
    have inC₂ : InRegions (s₂.rd ++ s₂.wr) (C.addr s₀) 4 := by
      have := Buf.inRegR hp hC₁ c₂.rd c₂.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine VG.Proof.MlKem.X86.Top.wp_movm' (by rw [eC s₂ c₂.esi]; exact inC₂) fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_andr fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_store' (by rw [eC s₄ c₄.esi, c₄.wr, ← h.wr]; exact inCw) fun s₅ g₅ r₅ w₅ m₅ => ?_
    have c₅ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s₅ := ⟨by rw [g₅]; exact c₄.esp, by rw [r₅]; exact c₄.rd, by rw [w₅]; exact c₄.wr,
      by rw [g₅]; exact c₄.esi, by rw [m₅, eC s₄ c₄.esi]; exact c₄.frame.writeW hrC _ hcC⟩
    refine VG.Proof.MlKem.X86.Top.wp_movr' fun s₆ o₆ v₆ => VG.Proof.MlKem.X86.Top.wp_addi fun s₇ o₇ v₇ => VG.Proof.MlKem.X86.Top.wp_movi fun s₈ o₈ v₈ => WP.block_nil_iff.mpr ?_
    have c₈ := ((c₅.only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)).only o₈ (by decide)
      (by decide)
    -- the state after the first block
    have rE : s₈.gpr .edx = 0 - s.gpr .eax := by
      rw [o₈.gpr _ (by decide), o₇.gpr _ (by decide), o₆.gpr _ (by decide), g₅, o₄.gpr _ (by decide),
        o₃.gpr _ (by decide), v₂, v₁, o₁.gpr _ (by decide)]
    have m₈ : s₈.mem = s.mem.writeW (C.addr s₀) (s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax) := by
      rw [o₈.mem, o₇.mem, o₆.mem, m₅, eC s₄ c₄.esi, v₄, v₃, eC s₂ c₂.esi, o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), o₁.gpr _ (by decide), o₄.mem, o₃.mem, o₂.mem, o₁.mem]
    have fC : Frame [C.rgn s₀] s.mem s₈.mem := by
      rw [m₈]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have cP : ∀ i < 256, coeffAt s₈.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i := fun i hi =>
      Frame.readW fC (coeff_contains _ (show i < n by rw [n_eq]; exact hi)) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact dd.symm) (by decide)
    have aC : s₈.mem.readW (C.addr s₀) 32 = s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax := by
      rw [m₈]; exact Mem.readW_writeW_self32 _ _ _
    let I : Nat → State → Prop := fun k u => VG.Proof.MlKem.X86.Top.Ctx Y s₀ u ∧ u.gpr .edi = P.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ecx = BitVec.ofNat 32 (256 - k) ∧ u.gpr .edx = 0 - s.gpr .eax ∧
      Frame [C.rgn s₀, P.rgn s₀] s.mem u.mem ∧ u.mem.readW (C.addr s₀) 32 = s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax ∧
      (∀ i < k, coeffAt u.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i &&& (0 - s.gpr .eax)) ∧
      (∀ i, k ≤ i → i < 256 → coeffAt u.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i)
    have i0 : I 0 s₈ := ⟨c₈, by rw [o₈.gpr _ (by decide), v₇, v₆, g₅, c₄.esi]; simp; rfl,
      v₈, rE, fC.mono (by simp), aC, fun i hi => absurd hi (by omega), fun i _ hi => cP i hi⟩
    refine (VG.Proof.MlKem.X86.Top.wp_count (N := 256) (by decide) I i0 fun k hk u ⟨cu, du, xu, eu, fu, au, lo, hi⟩ => ?_).mono
      fun u ⟨cu, _, _, _, fu, au, lo, _⟩ => hQ s₀ s u hp ha cu fu au lo
    have eP : u.ea (at_ .edi 0) = coeffAddr (P.addr s₀) k := by
      simp only [State.ea, at_, du]; rw [ea_add (by omega)]; rfl
    have hk' : k < n := by rw [n_eq]; exact hk
    have inP : InRegions u.wr (coeffAddr (P.addr s₀) k) 4 :=
      Buf.inRegW hp hP₁ (Lay.okW_iff.mp hP).2 cu.wr (show 4 * k + 4 ≤ 1024 by omega)
    obtain ⟨rP, hrP, hcP⟩ := Buf.contains hp hP₁ (Lay.okW_iff.mp hP).2 (o := 4 * k) (n := 4)
      (show 4 * k + 4 ≤ 1024 by omega)
    have inP' : InRegions (u.rd ++ u.wr) (coeffAddr (P.addr s₀) k) 4 :=
      Buf.inRegR hp hP₁ cu.rd cu.wr (show 4 * k + 4 ≤ 1024 by omega)
    refine VG.Proof.MlKem.X86.Top.wp_movm' (by rw [eP]; exact inP') fun u₁ o₁ v₁ => ?_
    have c₁ := cu.only o₁ (by decide) (by decide)
    refine VG.Proof.MlKem.X86.Top.wp_andr fun u₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    have eP₂ : u₂.ea (at_ .edi 0) = coeffAddr (P.addr s₀) k := by
      rw [← eP]; simp only [State.ea, at_]; rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide)]
    refine VG.Proof.MlKem.X86.Top.wp_store' (by rw [eP₂, c₂.wr, ← cu.wr]; exact inP) fun u₃ g₃ r₃ w₃ m₃ => ?_
    have c₃ : VG.Proof.MlKem.X86.Top.Ctx Y s₀ u₃ := ⟨by rw [g₃]; exact c₂.esp, by rw [r₃]; exact c₂.rd, by rw [w₃]; exact c₂.wr,
      by rw [g₃]; exact c₂.esi, by rw [m₃, eP₂]; exact c₂.frame.writeW hrP _ hcP⟩
    refine VG.Proof.MlKem.X86.Top.wp_addi fun u₄ o₄ v₄ => VG.Proof.MlKem.X86.Top.wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
    have c₅ := (c₃.only o₄ (by decide) (by decide)).only o₅ (by decide) (by decide)
    have val : u₂.gpr .eax = coeffAt s.mem (P.addr s₀) k &&& (0 - s.gpr .eax) := by
      rw [v₂, v₁, o₁.gpr _ (by decide), eu, eP, ← coeffAt_eq, hi k (Nat.le_refl _) hk]
    have m₅ : u₅.mem = u.mem.writeW (coeffAddr (P.addr s₀) k) (coeffAt s.mem (P.addr s₀) k &&& (0 - s.gpr .eax)) := by
      rw [o₅.mem, o₄.mem, m₃, eP₂, val, o₂.mem, o₁.mem]
    have ex : u₄.gpr .ecx = BitVec.ofNat 32 (256 - k) := by
      rw [o₄.gpr _ (by decide), g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), xu]
    refine ⟨⟨c₅, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_, ?_, fun i hi' => ?_, fun i hi₁ hi₂ => ?_⟩, ?_⟩
    · rw [o₅.gpr _ (by decide), v₄, g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), du]
      show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), eu]
    · rw [m₅]; exact fu.writeW (r := P.rgn s₀) (by simp) _ (coeff_contains _ hk')
    · rw [m₅, Mem.readW_writeW_sep (dd.sep (Region.contains_self _ _) (coeff_contains _ hk')) (by decide)]
      exact au
    · rw [m₅, coeffAt_writeW _ _ (by rw [n_eq]; omega) hk']
      split
      · rename_i e; subst e; rfl
      · exact lo i (by omega)
    · rw [m₅, coeffAt_writeW_ne _ _ (by rw [n_eq]; omega) hk' (by omega)]
      exact hi i (by omega) hi₂
    · show u₅.zf.map (!·) = _
      rw [z₅, ex]; exact cnt_ne hk (by decide)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## `esi`, a word, and the value returned -/

/-- `esi ← scratch`, at the start of the body. -/
theorem ldsc_piece {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * Y.sc)))]) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) (VG.Proof.MlKem.X86.Top.Ctx Y) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * Y.sc)))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) tt
  · subst e
    have ea : (P0 s₀).ea (at_ .esp (20 + 4 * Y.sc)) = argAddr s₀ Y.sc := P0_argAddr s₀ Y.sc
    refine VG.Proof.MlKem.X86.Top.wp_movm' (by rw [ea]; exact P0_argIn hp.sc_lt hp.sp' hp.gwr) fun s₁ o₁ v₁ => WP.block_nil_iff.mpr ?_
    refine ⟨by rw [o₁.gpr _ (by decide)], o₁.rd, o₁.wr, ?_, by rw [o₁.mem]; exact Frame.refl _ _⟩
    rw [v₁, ea]
    exact P0_arg hp.E0_big hp.sc_lt hp.sp' (by rw [hp.fr16]; exact hp.stk_g.sub_left hp.frame_sub)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-- A word of `scratch` set to `v`. -/
theorem st32_piece (o v : Nat) (hc : Y.okW ⟨Y.sc, o, 4⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (at_ .esi o) .eax])
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) (BitVec.ofNat 32 v) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (at_ .esi o) .eax]) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    have hin : InRegions s.wr (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 4 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine VG.Proof.MlKem.X86.Top.wp_movi fun s₁ o₁ v₁ => ?_
    have h₁ := h.only o₁ (by decide) (by decide)
    have ea₁ : s₁.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 4⟩ := by
      simp only [State.ea, at_]; rw [h₁.esi]
    refine VG.Proof.MlKem.X86.Top.wp_store' (by rw [ea₁, h₁.wr, ← h.wr]; exact hin) fun s₂ g₂ r₂ w₂ m₂ => WP.block_nil_iff.mpr ?_
    refine hQ s₀ s _ hp ha ⟨by rw [g₂]; exact h₁.esp, by rw [r₂]; exact h₁.rd, by rw [w₂]; exact h₁.wr,
      by rw [g₂]; exact h₁.esi, ?_⟩ ?_
    · rw [m₂, ea₁]; exact h₁.frame.writeW hr _ hcr
    · rw [m₂, ea₁, o₁.mem, v₁]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-- `eax ←` a word of `scratch`. -/
theorem ld32_piece (o : Nat) (hc : Y.ok ⟨Y.sc, o, 4⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.mem (at_ .esi o))]) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → s'.mem = s.mem →
      s'.gpr .eax = s.mem.readW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 32 → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.mov .eax (.mem (at_ .esi o))]) := by
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have hin : InRegions (s.rd ++ s.wr) (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 4 := by
      have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have ea : s.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 4⟩ := by simp only [State.ea, at_]; rw [h.esi]
    refine VG.Proof.MlKem.X86.Top.wp_movm' (by rw [ea]; exact hin) fun s₁ o₁ v₁ => WP.block_nil_iff.mpr ?_
    exact hQ s₀ s s₁ hp ha (h.only o₁ (by decide) (by decide)) o₁.mem (by rw [v₁, ea])
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopKeep`. -/
section

/-!
# ML-KEM on x86 (32-bit): what a call leaves unchanged

A buffer apart from the regions a call or a block changes (`Frame`) keeps its
bytes (`keep`), and so the polynomial, bytes or word it holds (`keepPoly`,
`keepBytes`, `keepW`, `keepRed`), when its separation from them is computed
(`decide`). The bytes of a buffer are those of its two parts (`bytes_split`).
The body of a top-level function, which ends in `Ctx`, makes a leaf
(`topLeaf`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {s₀ : State}

/-- The frame of a block or call: buffers, and the stack below the leaf's frame. -/
abbrev FR (s₀ : State) (bs : List Buf) (N : Nat) : List Region :=
  bs.map (Buf.rgn s₀) ++ [below (E1 s₀) N]

/-- Whether `b` is a buffer apart from each of `bs`. -/
def Lay.apart (Y : Lay) (b : Buf) (bs : List Buf) : Bool := Y.ok b && bs.all fun c => Y.ok c && Y.sep b c

theorem keep (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {b : Buf} (hs : Y.apart b bs = true)
    {m m' : Mem} (fr : Frame (VG.Proof.MlKem.X86.Top.FR s₀ bs N) m m') :
    ∀ i < b.len, m' (b.addr s₀ + BitVec.ofNat 64 i) = m (b.addr s₀ + BitVec.ofNat 64 i) := by
  simp only [Lay.apart, Bool.and_eq_true] at hs
  exact bytes_frame fr (Buf.frD hp hs.1 hs.2 hN) (by have := Buf.fit hp hs.1; omega)

theorem keepPoly (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {a o : Nat}
    (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (VG.Proof.MlKem.X86.Top.FR s₀ bs N) m m') {f : VG.Spec.MlKem.Poly}
    (h : PolyIs m (Buf.addr s₀ ⟨a, o, 1024⟩) f) : PolyIs m' (Buf.addr s₀ ⟨a, o, 1024⟩) f :=
  polyIs_congr (VG.Proof.MlKem.X86.Top.keep hp hN hs fr) h

theorem keepRed (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {a o : Nat}
    (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (VG.Proof.MlKem.X86.Top.FR s₀ bs N) m m')
    (h : Reduced m (Buf.addr s₀ ⟨a, o, 1024⟩)) : Reduced m' (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  reduced_congr (VG.Proof.MlKem.X86.Top.keep hp hN hs fr) h

theorem keepBytes (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {b : Buf}
    (hs : Y.apart b bs = true) {m m' : Mem} (fr : Frame (VG.Proof.MlKem.X86.Top.FR s₀ bs N) m m') :
    bytesAt m' (b.addr s₀) b.len = bytesAt m (b.addr s₀) b.len :=
  bytesAt_congr (VG.Proof.MlKem.X86.Top.keep hp hN hs fr)

theorem keepW (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {a o : Nat}
    (hs : Y.apart ⟨a, o, 4⟩ bs = true) {m m' : Mem} (fr : Frame (VG.Proof.MlKem.X86.Top.FR s₀ bs N) m m') :
    m'.readW (Buf.addr s₀ ⟨a, o, 4⟩) 32 = m.readW (Buf.addr s₀ ⟨a, o, 4⟩) 32 :=
  Mem.readW_congr fun i hi => VG.Proof.MlKem.X86.Top.keep hp hN hs fr i hi

/-- A single region, as a frame. -/
theorem fr1 {b : Buf} {m m' : Mem} (fr : Frame [b.rgn s₀] m m') : Frame (VG.Proof.MlKem.X86.Top.FR s₀ [b] 0) m m' :=
  fr.mono (by simp)

/-- Two regions, as a frame. -/
theorem fr2 {b c : Buf} {m m' : Mem} (fr : Frame [b.rgn s₀, c.rgn s₀] m m') : Frame (VG.Proof.MlKem.X86.Top.FR s₀ [b, c] 0) m m' :=
  fr.mono (by simp)

/-- A byte written. -/
theorem frW8 {o : Nat} {m : Mem} {v : Byte} :
    Frame (VG.Proof.MlKem.X86.Top.FR s₀ [⟨Y.sc, o, 1⟩] 0) m (m.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) v) :=
  VG.Proof.MlKem.X86.Top.fr1 ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    show (⟨Buf.addr s₀ ⟨Y.sc, o, 1⟩, 1⟩ : Region).Contains _ (8 / 8); exact Region.contains_self _ _))

/-- A word written. -/
theorem frW32 {o : Nat} {m : Mem} {v : BitVec 32} :
    Frame (VG.Proof.MlKem.X86.Top.FR s₀ [⟨Y.sc, o, 4⟩] 0) m (m.writeW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) v) :=
  VG.Proof.MlKem.X86.Top.fr1 ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    show (⟨Buf.addr s₀ ⟨Y.sc, o, 4⟩, 4⟩ : Region).Contains _ (32 / 8); exact Region.contains_self _ _))

/-- The bytes of a buffer, as those of its two parts. -/
theorem bytes_split (hp : TPre Y s₀) (m : Mem) {a o o' l₁ l₂ L : Nat} (ho : o + l₁ = o') (hL : l₁ + l₂ = L)
    (h₁ : Y.ok ⟨a, o, l₁⟩ = true) (h₂ : Y.ok ⟨a, o', l₂⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o, L⟩) L =
      bytesAt m (Buf.addr s₀ ⟨a, o, l₁⟩) l₁ ++ bytesAt m (Buf.addr s₀ ⟨a, o', l₂⟩) l₂ := by
  have e : Buf.addr s₀ ⟨a, o', l₂⟩ = Buf.addr s₀ ⟨a, o, l₁⟩ + BitVec.ofNat 64 l₁ := by
    rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h₁, BitVec.add_assoc, ← BitVec.ofNat_add, ho]
  rw [e, ← hL]
  exact bytesAt_add m _ l₁ l₂

/-- A top-level function, from its body. -/
theorem topLeaf {lk : State → List Byte} {body : Prog isa} {B : State → State → Prop} (hsp : NoSp body)
    (hb : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) (fun s₀ s => VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ B s₀ s) body) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (B s₀) s₀ s') (leaf body) :=
  Piece.leaf (VG.Proof.MlKem.X86.Top.W Y) hsp (fun _ hp => ⟨hp.E0_big, by have := hp.sp'; omega⟩) (fun _ hp => hp.hW)
    (fun _ _ _ _ hq => hq.1) (hb.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopKem`. -/
section

/-!
# ML-KEM on x86 (32-bit): the code of a parameter set

The code over the `k` rows, entries or polynomials is a sequence (`seqs`) of
one piece per index (`Piece.seqs`). A parameter set's functions that compress
to `d_u` and `d_v` bits and decompress from them (`KemLay.ceCode`,
`KemLay.ddCode`) are leaves of the contracts of `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` for widths that include `d_u` and `d_v` (`CeOK`),
so their calls are pieces (`ceK_piece`, `ddK_piece`).
-/

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
      Piece Pre Pub (P (a + n)) Q c → Piece Pre Pub (P a) Q (VG.Impl.MlKem.X86.seqs ((List.range' a n).map f) c)
  | 0, _, _, hc => hc
  | n + 1, a, h, hc => by
    rw [List.range'_succ, List.map_cons, Impl.MlKem.X86.seqs]
    exact .seq (h a (Nat.le_refl _) (by omega)) (Piece.seqs n (a + 1) (fun i h₁ h₂ => h i (by omega) (by omega))
      (by rw [show a + 1 + n = a + (n + 1) by omega]; exact hc))

/-- `f 0`, …, `f (n - 1)`, then `c`. -/
theorem _root_.VG.Proof.MlKem.X86.Piece.seqs0 {Pre : State → Prop} {Pub : State → State → Prop}
    {P : Nat → State → State → Prop} {f : Nat → Prog isa} {Q : State → State → Prop} {c : Prog isa} (n : Nat)
    (h : ∀ i < n, Piece Pre Pub (P i) (P (i + 1)) (f i)) (hc : Piece Pre Pub (P n) Q c) :
    Piece Pre Pub (P 0) Q (VG.Impl.MlKem.X86.seqs ((List.range n).map f) c) := by
  rw [List.range_eq_range']
  exact Piece.seqs n 0 (fun i _ h₂ => h i (by omega)) (by rw [Nat.zero_add]; exact hc)

/-! ## Indices of a `k × k` matrix, row by row -/

theorem idx_mod {k i j : Nat} (hj : j < k) : (k * i + j) % k = j := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem idx_div {k i j : Nat} (hj : j < k) : (k * i + j) / k = i := by
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]

theorem idx_lt {k i j : Nat} (hi : i < k) (hj : j < k) : k * i + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)

/-! ## Buffers of `k` parts -/

theorem catK_congr {f g : Nat → List Byte} : ∀ {k : Nat}, (∀ i < k, f i = g i) → KPke.catK f k = KPke.catK g k
  | 0, _ => rfl
  | 1, h => h 0 (by decide)
  | k + 2, h => by
    show KPke.catK f (k + 1) ++ f (k + 1) = KPke.catK g (k + 1) ++ g (k + 1)
    rw [VG.Proof.MlKem.X86.Top.catK_congr fun i hi => h i (by omega), h (k + 1) (by omega)]

/-- A part of a buffer within an argument is within it. -/
theorem Lay.ok_sub {Y : Lay} {a o l o' l' : Nat} (h : Y.ok ⟨a, o, l⟩ = true) (h₀ : 0 < l')
    (h₂ : o' + l' ≤ o + l) : Y.ok ⟨a, o', l'⟩ = true := by
  simp only [Lay.ok, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

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
    rw [VG.Proof.MlKem.X86.Top.bytes_split hp m (o' := o + c * (n + 1)) (l₁ := c * (n + 1)) (l₂ := c) rfl e.symm
      (Lay.ok_sub h (Nat.mul_pos hc (Nat.succ_pos _)) (by omega))
      (Lay.ok_sub h hc (by omega)),
      VG.Proof.MlKem.X86.Top.bytes_catK hp m (n := n + 1) (Lay.ok_sub h (Nat.mul_pos hc (Nat.succ_pos _))
        (by omega))]
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
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, l⟩] s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, l⟩) l = Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨sa, so, l⟩) l →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (copyW Y.sc ⟨sa, so, l⟩ ⟨da, dO, l⟩ n) := by
  subst hl
  exact VG.Proof.MlKem.X86.Top.copyW_piece sa so da dO n hn hn' hc t₁ t₂ hA hQ

/-- The parameter set's leaves compress to `d_u` and `d_v` bits, and decompress from them. -/
class CeOK (L : KemLay) : Prop where
  ce : ∃ ws, L.p.du ∈ ws ∧ L.p.dv ∈ ws ∧ VG.Proof.MlKem.X86.Top.CeFn L.ceCode ws
  dd : ∃ ws, L.p.du ∈ ws ∧ L.p.dv ∈ ws ∧ VG.Proof.MlKem.X86.Top.DdFn L.ddCode ws

instance : VG.Proof.MlKem.X86.Top.CeOK L768 := ⟨⟨_, by decide, by decide, VG.Proof.MlKem.X86.Top.ce768⟩, ⟨_, by decide, by decide, VG.Proof.MlKem.X86.Top.dd768⟩⟩

variable {L : KemLay} [VG.Proof.MlKem.X86.Top.CeOK L]

theorem ceK_piece (d : Nat) (hd : d = L.p.du ∨ d = L.p.dv) (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ceK L Y.sc d ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) := by
  obtain ⟨ws, hu, hv, F⟩ := CeOK.ce (L := L)
  exact VG.Proof.MlKem.X86.Top.ceC_piece F d (by rcases hd with rfl | rfl <;> with_reducible assumption) fa fo oa oo hc hN tt hA hQ

theorem ddK_piece (d : Nat) (hd : d = L.p.du ∨ d = L.p.dv) (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ddK L Y.sc d ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) := by
  obtain ⟨ws, hu, hv, F⟩ := CeOK.dd (L := L)
  exact VG.Proof.MlKem.X86.Top.ddC_piece F d (by rcases hd with rfl | rfl <;> with_reducible assumption) ba bo fa fo hc hN tt hA hQ

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.CheckEkBody`. -/
section

/-!
# ML-KEM on x86 (32-bit): the encapsulation key check

`checkEkN (128k)`, for a parameter set `p` with `k = p.k`: after `t` groups,
`ebx` is all ones if both fields of every group so far are less than `q`, and
0 otherwise (`mask`); the modulus check is that for all `128k` groups
(`ekCheck_iff`). Each parameter set's contract implies `Pre p`
(`Proof/MlKem/X86/CheckEk.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.CheckEk

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev eP : BitVec 32 := arg s₀ 0
abbrev eA : Addr := (VG.Proof.MlKem.X86.CheckEk.eP s₀).setWidth 64
end

section
variable (p : Params) (s₀ : State)
abbrev eR : Region := ⟨VG.Proof.MlKem.X86.CheckEk.eA s₀, p.ekLen⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 4 * 1⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.X86.CheckEk.eA s₀) p.ekLen
end

structure Pre (p : Params) (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * 1 ≤ 2 ^ 32
  rd : s₀.rd = [VG.Proof.MlKem.X86.CheckEk.eR p s₀, VG.Proof.MlKem.X86.CheckEk.aR s₀]
  wr : s₀.wr = []
  ret_e : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.CheckEk.eR p s₀)
  ret_a : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.CheckEk.aR s₀)
  stk_e : (VG.Proof.MlKem.X86.CheckEk.stkR s₀).Disjoint (VG.Proof.MlKem.X86.CheckEk.eR p s₀)
  stk_a : (VG.Proof.MlKem.X86.CheckEk.stkR s₀).Disjoint (VG.Proof.MlKem.X86.CheckEk.aR s₀)
  e_fit : (VG.Proof.MlKem.X86.CheckEk.eP s₀).toNat + p.ekLen ≤ 2 ^ 32

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0

/-- Both fields of every group before `t` are less than `q`. -/
def ok (L : List Byte) (t : Nat) : Prop := ∀ g < t, field0 L g < q ∧ field1 L g < q

instance (L : List Byte) (t : Nat) : Decidable (VG.Proof.MlKem.X86.CheckEk.ok L t) := by unfold VG.Proof.MlKem.X86.CheckEk.ok; infer_instance

/-- All ones if `ok`, 0 otherwise. -/
def mask (p : Prop) [Decidable p] : BitVec 32 := if p then 0xffffffff else 0

variable {p : Params}

/-- After `t` groups. -/
structure Inv (p : Params) (s₀ : State) (t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = VG.Proof.MlKem.X86.CheckEk.eP s₀ + BitVec.ofNat 32 (3 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (128 * p.k - t)
  ebx : s.gpr .ebx = VG.Proof.MlKem.X86.CheckEk.mask (VG.Proof.MlKem.X86.CheckEk.ok (VG.Proof.MlKem.X86.CheckEk.K p s₀) t)

theorem sbb_mask (x : BitVec 32) (c : Bool) :
    x - x - (BitVec.ofBool c).setWidth 32 = if c then 0xffffffff else 0 := by
  rw [BitVec.sub_self]; cases c <;> rfl

theorem ok_succ (L : List Byte) (t : Nat) :
    VG.Proof.MlKem.X86.CheckEk.ok L (t + 1) ↔ VG.Proof.MlKem.X86.CheckEk.ok L t ∧ field0 L t < q ∧ field1 L t < q :=
  ⟨fun h => ⟨fun g hg => h g (by omega), h t (by omega)⟩, fun ⟨h, h'⟩ g hg => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | rfl
    · exact h g hg
    · exact h'⟩

theorem mask_succ (L : List Byte) (t : Nat) :
    VG.Proof.MlKem.X86.CheckEk.mask (VG.Proof.MlKem.X86.CheckEk.ok L t) &&& (if decide (field0 L t < 3329) then 0xffffffff else 0) &&&
      (if decide (field1 L t < 3329) then 0xffffffff else 0) = VG.Proof.MlKem.X86.CheckEk.mask (VG.Proof.MlKem.X86.CheckEk.ok L (t + 1)) := by
  have e : VG.Proof.MlKem.X86.CheckEk.ok L (t + 1) ↔ VG.Proof.MlKem.X86.CheckEk.ok L t ∧ field0 L t < 3329 ∧ field1 L t < 3329 := by rw [VG.Proof.MlKem.X86.CheckEk.ok_succ, q_eq]
  simp only [VG.Proof.MlKem.X86.CheckEk.mask]
  by_cases h : VG.Proof.MlKem.X86.CheckEk.ok L t <;> by_cases h0 : field0 L t < 3329 <;> by_cases h1 : field1 L t < 3329 <;>
    simp only [h, h0, h1, e, decide_true, decide_false, ite_true, ite_false, and_self, and_true,
      and_false] <;> decide

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlKem.X86.CheckEk.Pre p s₀)
include hp

theorem stk_eq : VG.Proof.MlKem.X86.CheckEk.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlKem.X86.CheckEk.stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem byte {j : Nat} (hj : j < p.ekLen) : (P0 s₀).mem (VG.Proof.MlKem.X86.CheckEk.eA s₀ + BitVec.ofNat 64 j) = (VG.Proof.MlKem.X86.CheckEk.K p s₀).getD j 0 := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf
  rw [bytesAt_getD _ _ hj, hf.bytes (R := VG.Proof.MlKem.X86.CheckEk.eR p s₀) (by simpa [← hp.stk_eq] using hp.stk_e.symm)
    (by show p.ekLen ≤ 2 ^ 64; have := hp.e_fit; omega) hj]

end Pre

theorem init_piece : Piece (VG.Proof.MlKem.X86.CheckEk.Pre p) VG.Proof.MlKem.X86.CheckEk.Pub (fun s₀ s => s = P0 s₀) (VG.Proof.MlKem.X86.CheckEk.Inv p · 0) (.block (ekInitN (128 * p.k))) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_rfl)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have i₀ := P0_argIn (s₀ := s₀) (n := 1) (i := 0) (by omega) fit (by simp [hp.rd])
    have v₀ := P0_arg hp.sp (n := 1) (i := 0) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero] at a₀
    apply WP.of_runBlock
    simp only [↓reduceIte, ekInitN, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, i₀, v₀,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, rfl, by simp, by simp, ?_⟩
    simp only [ite_true, VG.Proof.MlKem.X86.CheckEk.mask]
    rw [ite_eq_left (show VG.Proof.MlKem.X86.CheckEk.ok (VG.Proof.MlKem.X86.CheckEk.K p s₀) 0 from fun g hg => absurd hg (Nat.not_lt_zero g))]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem step {s₀ : State} (hp : VG.Proof.MlKem.X86.CheckEk.Pre p s₀) {t : Nat} (ht : t < 128 * p.k) {s : State} (h : VG.Proof.MlKem.X86.CheckEk.Inv p s₀ t s) :
    WP isa (.block ekBody) s fun s' => VG.Proof.MlKem.X86.CheckEk.Inv p s₀ (t + 1) s' ∧ VG.X86.eval .ne s' = some (decide (t + 1 < 128 * p.k)) := by
  have fe := hp.e_fit
  have hE : p.ekLen = 384 * p.k + 32 := rfl
  have eb : ∀ o < 3, (VG.Proof.MlKem.X86.CheckEk.eP s₀ + BitVec.ofNat 32 (3 * t) + BitVec.ofNat 32 o).setWidth 64 =
      VG.Proof.MlKem.X86.CheckEk.eA s₀ + BitVec.ofNat 64 (3 * t + o) := fun o ho => ea_add (by omega)
  have e0 := eb 0 (by omega)
  have e1 := eb 1 (by omega)
  have e2 := eb 2 (by omega)
  have inE : ∀ o < 3, InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86.CheckEk.eA s₀ + BitVec.ofNat 64 (3 * t + o)) 1 := fun o ho =>
    ⟨VG.Proof.MlKem.X86.CheckEk.eR p s₀, List.mem_append_left _ (by rw [h.rd, pushed_rd, hp.rd]; simp), contains_at (by omega) fe⟩
  have i0 := inE 0 (by omega)
  have i1 := inE 1 (by omega)
  have i2 := inE 2 (by omega)
  have v : ∀ o < 3, s.mem (VG.Proof.MlKem.X86.CheckEk.eA s₀ + BitVec.ofNat 64 (3 * t + o)) = (VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + o) 0 :=
    fun o ho => by rw [h.mem, hp.byte (by omega)]
  have v0 := v 0 (by omega)
  have v1 := v 1 (by omega)
  have v2 := v 2 (by omega)
  simp only [Nat.add_zero] at e0 i0 v0
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, ekBody, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, e1, e2, i0, i1, i2, v0, v1, v2, VG.Proof.MlKem.X86.CheckEk.sbb_mask,
    Option.some.injEq, exists_eq_left']
  have x0 : (BitVec.setWidth 32 ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t) 0) +
      (BitVec.setWidth 32 ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 1) 0) &&& 15).rotateRight 24).toNat = field0 (VG.Proof.MlKem.X86.CheckEk.K p s₀) t := by
    have l0 := ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t) 0).isLt
    have l1 := ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 1) 0).isLt
    have hm : (BitVec.setWidth 32 ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 1) 0) &&& 15).toNat =
        ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 1) 0).toNat % 16 := by
      rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [hm]; omega), hm, toNat_byte32,
      Nat.mod_eq_of_lt (by omega), field0]
    omega
  have x1 : (BitVec.setWidth 32 ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 1) 0) >>> 4 +
      (BitVec.setWidth 32 ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 2) 0)).rotateRight 28).toNat = field1 (VG.Proof.MlKem.X86.CheckEk.K p s₀) t := by
    have l1 := ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 1) 0).isLt
    have l2 := ((VG.Proof.MlKem.X86.CheckEk.K p s₀).getD (3 * t + 2) 0).isLt
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [toNat_byte32]; omega), toNat_shr,
      toNat_byte32, toNat_byte32, Nat.mod_eq_of_lt (by omega), field1]
    omega
  simp only [x0, x1, show Q.toNat = 3329 from rfl, h.ebx, VG.Proof.MlKem.X86.CheckEk.mask_succ]
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, h.mem, ?_, ?_, by simp⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, ite_false, ite_true]
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · simp only [VG.X86.eval, h.ecx]
    exact cnt_ne ht (by omega)

theorem mask_and1 (p : Prop) [Decidable p] : VG.Proof.MlKem.X86.CheckEk.mask p &&& 1 = if p then 1 else 0 := by
  unfold VG.Proof.MlKem.X86.CheckEk.mask
  by_cases e : p
  · rw [ite_eq_left e, ite_eq_left e]; decide
  · rw [ite_eq_right e, ite_eq_right e]; decide

/-- The end: the result in `eax`. -/
structure Fin (p : Params) (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = if VG.Proof.MlKem.X86.CheckEk.ok (VG.Proof.MlKem.X86.CheckEk.K p s₀) (128 * p.k) then 1 else 0

theorem end_piece : Piece (VG.Proof.MlKem.X86.CheckEk.Pre p) VG.Proof.MlKem.X86.CheckEk.Pub (VG.Proof.MlKem.X86.CheckEk.Inv p · (128 * p.k)) (VG.Proof.MlKem.X86.CheckEk.Fin p) (.block ekEnd) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [ekEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.map_some,
    Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨by simp [h.esp], h.rd, h.wr, h.mem, ?_⟩
  simp only [ite_true]
  rw [h.ebx, VG.Proof.MlKem.X86.CheckEk.mask_and1]

theorem loop_piece (hk : 0 < p.k) : Piece (VG.Proof.MlKem.X86.CheckEk.Pre p) VG.Proof.MlKem.X86.CheckEk.Pub (VG.Proof.MlKem.X86.CheckEk.Inv p · 0) (VG.Proof.MlKem.X86.CheckEk.Inv p · (128 * p.k)) (.loop (.block ekBody) .ne) :=
  Piece.countLoop (by omega) (fun t s₀ s => VG.Proof.MlKem.X86.CheckEk.Inv p s₀ t s) [.esp, .esi, .ecx]
    (fun t ht s₀ s hp h => VG.Proof.MlKem.X86.CheckEk.step hp ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
      · rw [h.esi, h'.esi, VG.Proof.MlKem.X86.CheckEk.eP, VG.Proof.MlKem.X86.CheckEk.eP, hq.2]
      · rw [h.ecx, h'.ecx]) (by taint_decide)

theorem piece (hk : 0 < p.k) (hsp : NoSp (.seq (.block (ekInitN (128 * p.k)))
      (.seq (.loop (.block ekBody) .ne) (.block ekEnd)))) :
    Piece (VG.Proof.MlKem.X86.CheckEk.Pre p) VG.Proof.MlKem.X86.CheckEk.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem.X86.CheckEk.Fin p s₀) s₀ s') (checkEkN (128 * p.k)) :=
  Piece.leaf (fun _ => []) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ _ r hr => absurd hr (by simp)) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq VG.Proof.MlKem.X86.CheckEk.init_piece (Piece.seq (VG.Proof.MlKem.X86.CheckEk.loop_piece hk) VG.Proof.MlKem.X86.CheckEk.end_piece)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨by rw [h.mem]; exact Frame.refl _ _, h.esp, h.rd, h.wr⟩ |> fun e => ⟨e, h⟩)

theorem ok_iff {s₀ : State} : ekCheck p (VG.Proof.MlKem.X86.CheckEk.K p s₀) = true ↔ VG.Proof.MlKem.X86.CheckEk.ok (VG.Proof.MlKem.X86.CheckEk.K p s₀) (128 * p.k) :=
  ekCheck_iff p _ (bytesAt_length _ _ _)

end VG.Proof.MlKem.X86.CheckEk

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.CheckEk`. -/
section

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_check_ek`

The key check (`CheckEkBody.lean`) of ML-KEM-768: its 384 groups of
`ek[0 : 1152]`.
-/

namespace VG.Proof.MlKem.X86.CheckEk

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem Pre.of {s₀ : State} (h : (checkEkContract X86.abi 16).pre s₀) : VG.Proof.MlKem.X86.CheckEk.Pre mlKem768 s₀ := by
  sig_pre [checkEkContract, checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- All-zero memory. -/
def satMem : Mem := fun _ => 0

theorem verified : Verified X86.target Impl.MlKem.X86.checkEk (checkEkContract X86.abi 16) := by
  refine Piece.verified (((VG.Proof.MlKem.X86.CheckEk.piece (p := mlKem768) (by decide) (NoSp.of_all (by decide +kernel))).pre_mono
    (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [checkEkContract, checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [checkEkContract, checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hinv.eax]
    by_cases e : VG.Proof.MlKem.X86.CheckEk.ok (VG.Proof.MlKem.X86.CheckEk.K mlKem768 s₀) (128 * mlKem768.k)
    · rw [ite_eq_left e]; exact (ite_eq_left (ok_iff.mpr e)).symm
    · rw [ite_eq_right e]; exact (ite_eq_right fun h => e (ok_iff.mp h)).symm
  · let st := VG.Proof.MlKem.X86.satState VG.Proof.MlKem.X86.CheckEk.satMem [⟨0, 1184⟩, ⟨0x5004, 4⟩] []
    refine ⟨st, ?_⟩
    sig_sat_check [checkEkContract, checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.CheckEk

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Extra`. -/
section

/-!
# ML-KEM: lemmas the x86 (32-bit) proofs use that do not depend on the target

* `Samp B a`: `SampleNTT(B)` finishes, with `a`, within some bound on its
  iterations; `a` is then unique (`Samp.unique`), and is `sv B`
  (`sv_eq`). Finitely many that each finish within some bound all finish
  within one (`samp_bound`).
* A polynomial whose coefficients are ANDed with `0 - r`, for `r` 1 or 0:
  unchanged or zero (`mask_poly`); the AND of such values (`acc_step`), and
  that the value a function returns with `Outcome` is 0 or 1 (`outcome_01`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- `SampleNTT(B)` finishes within some bound on its iterations, with `a`. -/
def Samp (B : List Byte) (a : VG.Spec.MlKem.Poly) : Prop := ∃ it, VG.Spec.MlKem.sampleNTT it B = some a

theorem Samp.unique {B : List Byte} {a b : VG.Spec.MlKem.Poly} (h₁ : VG.Proof.MlKem.Samp B a) (h₂ : VG.Proof.MlKem.Samp B b) : a = b := by
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  have e₁ := sampleNTT_mono hi (Nat.le_max_left i j)
  have e₂ := sampleNTT_mono hj (Nat.le_max_right i j)
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- The polynomial `SampleNTT(B)` gives, if it finishes. -/
noncomputable def sv (B : List Byte) : VG.Spec.MlKem.Poly :=
  @dite _ (∃ a, VG.Proof.MlKem.Samp B a) (Classical.propDecidable _) (fun h => Classical.choose h) (fun _ => VG.Spec.MlKem.zero)

theorem sv_eq {B : List Byte} {a : VG.Spec.MlKem.Poly} (h : VG.Proof.MlKem.Samp B a) : VG.Proof.MlKem.sv B = a := by
  unfold VG.Proof.MlKem.sv
  split
  · exact (Classical.choose_spec ‹∃ a, Samp B a›).unique h
  · exact absurd (⟨a, h⟩ : ∃ a, VG.Proof.MlKem.Samp B a) ‹_›

/-- Finitely many samples, within one bound. -/
theorem samp_bound : ∀ (L : List (List Byte × VG.Spec.MlKem.Poly)), (∀ p ∈ L, VG.Proof.MlKem.Samp p.1 p.2) →
    ∃ M, ∀ p ∈ L, VG.Spec.MlKem.sampleNTT M p.1 = some p.2
  | [], _ => ⟨0, fun _ h => absurd h (List.not_mem_nil)⟩
  | p :: L, h => by
    obtain ⟨M, hM⟩ := VG.Proof.MlKem.samp_bound L fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨i, hi⟩ := h p (List.mem_cons_self ..)
    refine ⟨max M i, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact sampleNTT_mono hi (Nat.le_max_right _ _)
    · exact sampleNTT_mono (hM q hq) (Nat.le_max_left _ _)

/-- A polynomial with its coefficients ANDed with `0 - r`, for `r` 1 or 0: unchanged, or zero. -/
theorem mask_poly {m m' : Mem} {p : Addr} {r : BitVec 32} (hr : r = 0 ∨ r = 1)
    (h : ∀ i < 256, coeffAt m' p i = coeffAt m p i &&& (0 - r)) (hred : r = 1 → Reduced m p) :
    Reduced m' p ∧ (r = 1 → polyAt m' p = polyAt m p) := by
  rcases hr with rfl | rfl
  · refine ⟨fun i hi => ?_, fun h => absurd h (by decide)⟩
    rw [h i (by rw [n_eq] at hi; exact hi)]
    simp [q_eq]
  · have e : ∀ i < 256, coeffAt m' p i = coeffAt m p i := fun i hi => by
      rw [h i hi, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    refine ⟨fun i hi => ?_, fun _ => ?_⟩
    · rw [e i (by rw [n_eq] at hi; exact hi)]; exact hred rfl i hi
    · apply Vector.ext
      intro i hi
      simp only [polyAt, Vector.getElem_ofFn]
      rw [e i (by rw [n_eq] at hi; exact hi)]

/-- `a &&& r`, for `a` and `r` each 0 or 1. -/
theorem acc_step {a r : BitVec 32} (ha : a = 0 ∨ a = 1) (hr : r = 0 ∨ r = 1) :
    (a &&& r = 0 ∨ a &&& r = 1) ∧ (a &&& r = 1 → a = 1 ∧ r = 1) ∧ (a &&& r = 0 → a = 0 ∨ r = 0) := by
  rcases ha with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

theorem outcome_01 {f : Nat → Option VG.Spec.MlKem.Poly} {r : BitVec 32} {out : VG.Spec.MlKem.Poly} (h : Outcome f r out) : r = 0 ∨ r = 1 := by
  rcases h with ⟨e, _⟩ | ⟨e, _⟩
  exacts [.inr e, .inl e]

end VG.Proof.MlKem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.EncBase`. -/
section

/-!
# ML-KEM on x86 (32-bit): the setting of K-PKE.Encrypt

`encrypt L sc` is proven once, for any parameter set `L` and any layout whose
`scratch` has `L.scratch` bytes and whose stack is 88 bytes (`SOK`), which
encapsulation and decapsulation both have. The facts of the layout of its
buffers, all in `scratch`, that the proofs use are stated once for any such
layout (the classes `EncBaseOK`, …), and each parameter set has them by
computing them from its offsets (`ok_sc`, `sep_sc`: `sc_decide`). Its code
reaches the buffers through `esi`, so does not depend on the argument
`scratch` is (`ptrTo_sc`: `sc_taint`).

Its inputs (`Inp`) are `ek`, `m` and 64 bytes whose last 32 are `r`, at
`eEK`, `eM` and `eKR` (`Base`). A step's frame is within what a predicate
keeps (`Keeps`) if it is within a larger one (`Keeps.widen`).
`SamplePolyCBD₂(PRF₂(r, N))` is `cbd_piece`.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A layout whose `scratch` has `L.scratch` bytes, written, and whose stack is 88 bytes. -/
structure SOK (L : KemLay) (Y : Lay) : Prop where
  lt : Y.sc < Y.n
  wr : Y.awr Y.sc = true
  len : Y.alen Y.sc = L.scratch
  stk : Y.stk = 88

theorem SOK.le {L : KemLay} {Y : Lay} (h : VG.Proof.MlKem.X86.Enc.SOK L Y) {n : Nat} (hn : n ≤ 88 := by decide) : n ≤ Y.stk :=
  h.stk ▸ hn

theorem ok_sc {L : KemLay} {Y : Lay} (h : VG.Proof.MlKem.X86.Enc.SOK L Y) (o l : Nat) :
    Y.ok ⟨Y.sc, o, l⟩ = (decide (0 < l) && decide (o + l ≤ L.scratch)) := by
  simp only [Lay.ok, h.lt, h.len, decide_true, Bool.true_and]

theorem okW_sc {L : KemLay} {Y : Lay} (h : VG.Proof.MlKem.X86.Enc.SOK L Y) (o l : Nat) :
    Y.okW ⟨Y.sc, o, l⟩ = (decide (0 < l) && decide (o + l ≤ L.scratch)) := by
  simp only [Lay.okW, VG.Proof.MlKem.X86.Enc.ok_sc h, h.wr, Bool.and_true]

theorem sep_sc {Y : Lay} (o l o' l' : Nat) :
    Y.sep ⟨Y.sc, o, l⟩ ⟨Y.sc, o', l'⟩ = (decide (o + l ≤ o') || decide (o' + l' ≤ o)) := by
  simp only [Lay.sep, ite_true]

theorem ptrTo_sc (sc : Nat) (r : Reg) (o l : Nat) :
    ptrTo sc r ⟨sc, o, l⟩ = [.mov r (.reg .esi), .alu .add r (.imm (BitVec.ofNat 32 o))] := by
  simp only [ptrTo, ite_true]

/-! ## Inputs -/

/-- `ek`, `m`, and 64 bytes whose last 32 are `r`, as functions of the entry state. -/
structure Inp where
  ek : State → List Byte
  m : State → List Byte
  kr : State → List Byte

section
variable (L : KemLay) (I : VG.Proof.MlKem.X86.Enc.Inp) (s₀ : State)
/-- `ρ`. -/
abbrev ρE : List Byte := ekRho L.p (I.ek s₀)
/-- `r`. -/
abbrev rE : List Byte := (I.kr s₀).drop 32
/-- `Â[i, j]`, if sampled. -/
noncomputable abbrev aE (i j : Nat) : VG.Spec.MlKem.Poly := VG.Proof.MlKem.sv (matSeed (VG.Proof.MlKem.X86.Enc.ρE L I s₀) i j)
/-- `ŷ[j]`. -/
abbrev yE (j : Nat) : VG.Spec.MlKem.Poly := encY (VG.Proof.MlKem.X86.Enc.rE I s₀) j
end

section
variable (L : KemLay) (sc : Nat)
abbrev bY (j : Nat) : Buf := ⟨sc, 1024 * j, 1024⟩
abbrev bE : Buf := ⟨sc, L.eE, 1024⟩
abbrev bU : Buf := ⟨sc, L.eU, 1024⟩
abbrev bA : Buf := ⟨sc, L.eA, 1024⟩
abbrev bP : Buf := ⟨sc, L.eP, 1024⟩
abbrev bT : Buf := ⟨sc, L.eT, 1024⟩
abbrev bMU : Buf := ⟨sc, L.eMU, 1024⟩
abbrev bNS : Buf := ⟨sc, L.eNS, 1024⟩
abbrev bSS : Buf := ⟨sc, L.eSS, 2048⟩
abbrev bST : Buf := ⟨sc, L.eST, 200⟩
abbrev bWK : Buf := ⟨sc, L.eWK, 640⟩
abbrev bPRF : Buf := ⟨sc, L.ePRF, 128⟩
abbrev bACC : Buf := ⟨sc, L.eACC, 4⟩
abbrev bEK : Buf := ⟨sc, L.eEK, L.p.ekLen⟩
abbrev bM : Buf := ⟨sc, L.eM, 32⟩
abbrev bKR : Buf := ⟨sc, L.eKR, 64⟩
abbrev bC : Buf := ⟨sc, L.eC, L.p.ctLen⟩
/-- `r ‖ N`. -/
abbrev bRN : Buf := ⟨sc, L.eKR + 32, 33⟩
/-- `N`. -/
abbrev bN : Buf := ⟨sc, L.eKR + 64, 1⟩
/-- `ρ ‖ i ‖ j`. -/
abbrev bSeed : Buf := ⟨sc, L.eEK + 384 * L.p.k, 34⟩
end

/-- Whether `bs` is apart from the inputs. -/
def inApart (L : KemLay) (Y : Lay) (bs : List Buf) : Bool :=
  Y.apart (VG.Proof.MlKem.X86.Enc.bEK L Y.sc) bs && Y.apart (VG.Proof.MlKem.X86.Enc.bM L Y.sc) bs && Y.apart (VG.Proof.MlKem.X86.Enc.bKR L Y.sc) bs

/-- A fact of the layout of buffers of `scratch`, computed from their offsets. -/
macro "sc_decide" : tactic => `(tactic| (simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true,
  ok_sc ‹SOK _ _›, okW_sc ‹SOK _ _›, sep_sc, (‹SOK _ _›).stk, inApart]; decide))

/-- The facts of the layout that `rn_split` and `cbd_piece` use. -/
class BaseOK (L : KemLay) : Prop where
  n : ∀ {Y : Lay}, VG.Proof.MlKem.X86.Enc.SOK L Y → Y.okW (VG.Proof.MlKem.X86.Enc.bN L Y.sc) = true
  rn : ∀ {Y : Lay}, VG.Proof.MlKem.X86.Enc.SOK L Y →
    Y.ok ⟨Y.sc, L.eKR + 32, 32⟩ = true ∧ Y.ok (VG.Proof.MlKem.X86.Enc.bN L Y.sc) = true ∧ Y.ok (VG.Proof.MlKem.X86.Enc.bKR L Y.sc) = true
  hash : ∀ {Y : Lay}, VG.Proof.MlKem.X86.Enc.SOK L Y → (Y.okW (VG.Proof.MlKem.X86.Enc.bST L Y.sc) && Y.okW (VG.Proof.MlKem.X86.Enc.bWK L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bRN L Y.sc) &&
    Y.okW (VG.Proof.MlKem.X86.Enc.bPRF L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bST L Y.sc) (VG.Proof.MlKem.X86.Enc.bWK L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bRN L Y.sc) (VG.Proof.MlKem.X86.Enc.bST L Y.sc) &&
    Y.sep (VG.Proof.MlKem.X86.Enc.bRN L Y.sc) (VG.Proof.MlKem.X86.Enc.bWK L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bST L Y.sc) (VG.Proof.MlKem.X86.Enc.bPRF L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bPRF L Y.sc) (VG.Proof.MlKem.X86.Enc.bWK L Y.sc)) = true

/-- A taint check of code that reaches buffers of `scratch` through `esi`, for any parameter set. -/
macro "sc_taint" : tactic => `(tactic| ((try simp only [ptrTo_sc]); (try simp only [ptrTo, reduceIte,
  Nat.reduceEqDiff, List.cons_append, List.nil_append]); taint_rfl))

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

/-- The inputs, in `scratch`. -/
structure Base (L : KemLay) (Y : Lay) (I : VG.Proof.MlKem.X86.Enc.Inp) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s
  ek : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bEK L Y.sc)) L.p.ekLen = I.ek s₀
  m : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bM L Y.sc)) 32 = I.m s₀
  kr : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bKR L Y.sc)) 64 = I.kr s₀

theorem Base.keep {I : VG.Proof.MlKem.X86.Enc.Inp} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : VG.Proof.MlKem.X86.Enc.inApart L Y bs = true) (fr : Frame (VG.Proof.MlKem.X86.Top.FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.Enc.Base L Y I s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s') :
    VG.Proof.MlKem.X86.Enc.Base L Y I s₀ s' := by
  simp only [VG.Proof.MlKem.X86.Enc.inApart, Bool.and_eq_true] at hs
  exact ⟨c, by rw [VG.Proof.MlKem.X86.Top.keepBytes hp hM hs.1.1 fr]; exact h.ek, by rw [VG.Proof.MlKem.X86.Top.keepBytes hp hM hs.1.2 fr]; exact h.m,
    by rw [VG.Proof.MlKem.X86.Top.keepBytes hp hM hs.2 fr]; exact h.kr⟩

/-- `Q` holds after anything whose frame is within `bs` and `M` bytes of stack. -/
def Keeps (Y : Lay) (Q : State → State → Prop) (bs : List Buf) (M : Nat) : Prop :=
  ∀ s₀ s s', TPre Y s₀ → Q s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → Frame (VG.Proof.MlKem.X86.Top.FR s₀ bs M) s.mem s'.mem → Q s₀ s'

theorem Keeps.widen {Q : State → State → Prop} {bs : List Buf} {M : Nat} (h : VG.Proof.MlKem.X86.Enc.Keeps Y Q bs M) (hM : M + 16 ≤ Y.stk)
    {bs' : List Buf} {M' : Nat} (hb : ∀ b ∈ bs', b ∈ bs) (hM' : M' ≤ M) : VG.Proof.MlKem.X86.Enc.Keeps Y Q bs' M' :=
  fun s₀ s s' hp hq c fr => h s₀ s s' hp hq c (fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (hb b hb')), fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp hM' hM⟩)

/-! ## `SamplePolyCBD₂(PRF₂(r, N))` -/

theorem st8_byte {s₀ : State} (m : Mem) (o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨Y.sc, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp only [BitVec.add_zero, VG.WriteBytes.writeW8_apply, List.getElem_cons_zero, ite_true]
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

variable [VG.Proof.MlKem.X86.Enc.BaseOK L]

/-- `r ‖ N`. -/
theorem rn_split {s₀ : State} (hS : VG.Proof.MlKem.X86.Enc.SOK L Y) (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bRN L Y.sc)) 33 =
      (bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bKR L Y.sc)) 64).drop 32 ++ bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bN L Y.sc)) 1 := by
  obtain ⟨o₁, o₂, o₃⟩ := BaseOK.rn hS
  rw [VG.Proof.MlKem.X86.Top.bytes_split hp m (o' := L.eKR + 64) (l₁ := 32) (l₂ := 1) rfl rfl o₁ o₂,
    bytesAt_drop _ _ (show 32 ≤ 64 by decide)]
  have e : Buf.addr s₀ ⟨Y.sc, L.eKR + 32, 32⟩ = Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bKR L Y.sc) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := ⟨Y.sc, L.eKR + 32, 32⟩) o₁, Buf.addr_eq hp (b := VG.Proof.MlKem.X86.Enc.bKR L Y.sc) o₃,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
end VG.Proof.MlKem.X86.Enc

end
