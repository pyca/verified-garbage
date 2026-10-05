import VerifiedGarbage.Impl.MlKem1024.X86_64.Compress
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.X86_64.Contracts`. -/
section

/-!
# ML-KEM-1024 on x86-64: the contracts of the compressions the proofs are written against

As `Proof/MlKem/X86_64/Contracts.lean`, for `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress`, whose widths are ML-KEM-1024's
(`Spec.MlKem1024.compressWidths`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem1024_compress_encode(f = rdi, d = esi, out = rdx, len = rcx)`. -/
abbrev compressEncode1024K : Contract isa := compressEncodeWK Spec.MlKem1024.compressWidths

/-- `vg_mlkem1024_decode_decompress(b = rdi, len = rsi, d = edx, f = rcx)`. -/
abbrev decodeDecompress1024K : Contract isa := decodeDecompressWK Spec.MlKem1024.compressWidths

end VG.Proof.MlKem1024.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode`. -/
section

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_compress_encode`

A segment of a group is bytes of the encoding (`ce_seg`); a group's segments
write its `d` bytes (`grp5_ok`, `grp11_ok`); the loop is ML-KEM-768's
(`CE.loop_ok`, `Proof/MlKem/X86_64/CompressEncode.lean`), with groups of 8
coefficients and `d` bytes, and the function is proven by its two cases.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Impl.MlKem.X86_64 (ceAcc ceSt ceTail ceLoopW ddLd ddVals ddTail ddLoopW)
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem widths1024 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : d = 5 ∨ d = 11 :=
  mem_compressWidths1024 hd

/-- Bytes of a segment of group `i`: the number of its `c` values from `o`,
shifted right by `s + p` bits, is byte `j` of the group. -/
theorem ce_seg {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (F : Poly) {i o c s p j : Nat} (hi : i < 32)
    (hoc : o + c ≤ 8) (hp : s + p + 8 ≤ d * c) (hj : 8 * j = d * o + s + p) (hjd : j < d) :
    BitVec.ofNat 8 (digits d ((List.range c).map fun t => compress d F[8 * i + (o + t)]!) / 2 ^ s / 2 ^ p) =
      (compressEncode d F)[d * i + j]! := by
  have hd0 : 0 < d := by rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with rfl | rfl <;> decide
  have hL := map_toList_lt F (compress_lt d)
  have hk : d * i + j < 32 * d := by
    have := Nat.mul_le_mul_left d (show i + 1 ≤ 32 by omega); rw [Nat.mul_succ] at this
    rw [Nat.mul_comm 32 d]; omega
  rw [compressEncode, byteEncode_getElem hd0 hL hk]
  apply ofNat8_eq
  have e : (List.range c).map (fun t => compress d F[8 * i + (o + t)]!) =
      ((F.map (compress d)).toList.drop (8 * i + o)).take c := by
    rw [take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
    refine List.map_congr_left fun t ht => ?_
    rw [map_toList_getD _ _ (by have := List.mem_range.mp ht; omega), Nat.add_assoc]
  have ex : d * (8 * i + o) + s + p = 8 * (d * i + j) := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_add 8]; omega
  rw [e, show (256 : Nat) = 2 ^ 8 from rfl, chunk_eq hL (8 * i + o) c s p 8 hp, ex]

theorem shr10_ok (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 63) (s : State) :
    WP isa (.block [.shift .shr .r10 n]) s fun s' =>
      (s'.gpr .r10 = s.gpr .r10 >>> n ∧ s'.mem = s.mem) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hn, hn']

theorem grp5_ok (F : Poly) {i : Nat} (hi : i < 32) {s : State} (h : CE.GrpIn 261888 5 8 5 F i s) :
    WP isa (.block (ceAcc 261888 5 0 8 ++ ceSt 0 5)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) 5 (fun k => (compressEncode 5 F)[5 * i + k]!) ∧ Keep [.rax, .rdx, .r10] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (ceAcc_ok (o := 0) (c := 8) (by decide) (by decide) (by decide) (by decide) s
    (fun j hj => by rw [Nat.zero_add]; exact h.rd j hj) (fun j => compress 5 F[8 * i + (0 + j)]!)
    (fun j hj => by rw [Nat.zero_add]; exact h.v j hj) (fun _ _ => compress_lt 5 _)) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 0) (nb := 5) (by decide) s₁ (fun k hk => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr k hk)) fun s₂ ⟨w₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by decide)⟩
  rw [k₁.gpr (by decide), add_ofNat_zero, m₁, r₁] at w₂
  refine w₂.congr fun k hk => ?_
  rw [← VG.Proof.MlKem1024.X86_64.ce_seg (o := 0) (c := 8) (s := 0) (p := 8 * k) (by decide) F hi (by decide) (by omega) (by omega) hk,
    Nat.pow_zero, Nat.div_one]

theorem grp11_ok (F : Poly) {i : Nat} (hi : i < 32) {s : State} (h : CE.GrpIn 261888 11 8 11 F i s) :
    WP isa (.block (ceAcc 261888 11 0 5 ++ ceSt 0 6 ++ ceAcc 261888 11 4 4 ++ ([.shift .shr .r10 4] : List Instr) ++ ceSt 6 5)) s
      fun s' => Written s.mem s'.mem (s.gpr .r8) 11 (fun k => (compressEncode 11 F)[11 * i + k]!) ∧
        Keep [.rax, .rdx, .r10] s s' := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- Values 0–4, and bytes 0–5.
  refine WP.mono (ceAcc_ok (o := 0) (c := 5) (by decide) (by decide) (by decide) (by decide) s
    (fun j hj => by rw [Nat.zero_add]; exact h.rd j (by omega)) (fun j => compress 11 F[8 * i + (0 + j)]!)
    (fun j hj => by rw [Nat.zero_add]; exact h.v j (by omega)) (fun _ _ => compress_lt 11 _)) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 0) (nb := 6) (by decide) s₁ (fun k hk => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr k (by omega))) fun s₂ ⟨w₂, k₂⟩ => ?_
  rw [k₁.gpr (by decide), add_ofNat_zero, m₁, r₁] at w₂
  -- Values 4–7, shifted, and bytes 6–10.
  have di₂ : s₂.gpr .rdi = s.gpr .rdi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have r9₂ : s₂.gpr .r9 = s.gpr .r9 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have r8₂ : s₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]
  have ww₂ : s₂.wr = s.wr := by rw [k₂.2.2, k₁.2.2]
  have hf₂ : Frame [⟨s.gpr .r8, 6⟩] s.mem s₂.mem := w₂.frame (Region.contains_self _ _)
  have hv₂ : ∀ j < 8, s₂.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 =
      s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 := fun j hj =>
    hf₂.readW (r := ⟨s.gpr .rdi, 32⟩) (contains_offset' (by omega) (by decide)) (fun r' hr' => by
      rw [List.mem_singleton] at hr'; subst hr'; exact h.dj.sub_right (Region.sub_prefix (by decide))) (by decide)
  refine WP.mono (ceAcc_ok (o := 4) (c := 4) (by decide) (by decide) (by decide) (by decide) s₂
    (fun j hj => by rw [rw₂, di₂]; exact h.rd _ (by omega)) (fun j => compress 11 F[8 * i + (4 + j)]!)
    (fun j hj => by rw [di₂, r9₂, hv₂ _ (by omega)]; exact h.v _ (by omega)) (fun _ _ => compress_lt 11 _))
    fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  refine WP.mono (VG.Proof.MlKem1024.X86_64.shr10_ok 4 (by decide) (by decide) s₃) fun s₄ ⟨⟨r₄, m₄⟩, k₄⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 6) (nb := 5) (by decide) s₄ (fun k hk => by
      rw [k₄.2.2, k₃.2.2, ww₂, k₄.gpr (by decide), k₃.gpr (by decide), r8₂]; exact h.wr _ (by omega)))
    fun s₅ ⟨w₅, k₅⟩ => ⟨?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  rw [k₄.gpr (by decide), k₃.gpr (by decide), r8₂, m₄, m₃, r₄, shr_toNat, r₃] at w₅
  refine (Written.append w₂ w₅ (by decide)).congr fun k hk => ?_
  by_cases hk6 : k < 6
  · rw [ifp hk6, ← VG.Proof.MlKem1024.X86_64.ce_seg (o := 0) (c := 5) (s := 0) (p := 8 * k) (by decide) F hi (by decide) (by omega) (by omega) (by omega),
      Nat.pow_zero, Nat.div_one]
  · rw [ifn hk6, ← VG.Proof.MlKem1024.X86_64.ce_seg (o := 4) (c := 4) (s := 4) (p := 8 * (k - 6)) (j := k) (by decide) F hi (by decide) (by omega)
      (by omega) hk]

/-- The loop for the width `d`, from a state with `f` in `rdi` and `out` in `r8`. -/
theorem ceLoop_ok {s₀ : State} (hp : compressEncode1024K.pre s₀) {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths)
    (hdd : dArg s₀ .rsi = d) {grp : List Instr}
    (hgrp : ∀ i < 32, ∀ s, CE.GrpIn 261888 d 8 d (CE.F s₀) i s → WP isa (.block grp) s (CE.GrpOut d d (CE.F s₀) i s))
    {s : State} (hdi : s.gpr .rdi = CE.fP s₀) (h8 : s.gpr .r8 = CE.oP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ceLoopW (ceMul1024 d) 32 (grp ++ ceTail 8 d)) s fun s' =>
      bytesAt s'.mem (CE.oP s₀) (32 * d) = compressEncode d (CE.F s₀) ∧
        Frame [⟨CE.oP s₀, 32 * d⟩] s₀.mem s'.mem := by
  have hd11 : 1 ≤ d ∧ d ≤ 11 := by rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with rfl | rfl <;> decide
  exact CE.loop_ok (c := 8) (b := d) (r := 261888) hp hd11 (by decide) (by decide) (by omega) (by omega) (by decide)
    hdd (fun x => ⟨compress1024_arg_lt hd x, compress1024_eq hd x⟩) hgrp
    (by rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with rfl | rfl <;> decide) hdi h8 hrd hwr hm

theorem cePrologue_ok (s₀ : State) :
    WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 5)]) s₀ fun s =>
      (s.gpr .rsi = BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.gpr .rsi)) ∧ s.gpr .r8 = s₀.gpr .rdx ∧
        s.zf = some (BitVec.setWidth 32 (s₀.gpr .rsi) - 5 == 0) ∧ s.mem = s₀.mem) ∧ Keep [.rsi, .r8] s₀ s := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem ce_wp {s₀ : State} (hp : compressEncode1024K.pre s₀) :
    WP isa compressEncode1024 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [CE.lenEq hp rfl]
  unfold compressEncode1024
  refine WP.seq (WP.mono (VG.Proof.MlKem1024.X86_64.cePrologue_ok s₀) fun s₁ ⟨⟨_, r8₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h5 : dArg s₀ .rsi = 5 := by simp only [dArg, h]; rfl
    rw [h5]
    exact VG.Proof.MlKem1024.X86_64.ceLoop_ok hp (by rw [← h5]; exact hd) h5 (fun i hi s hs => VG.Proof.MlKem1024.X86_64.grp5_ok _ hi hs) di₁ r8₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    have h11 : dArg s₀ .rsi = 11 := by
      rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
      · exact e
    rw [h11]
    exact VG.Proof.MlKem1024.X86_64.ceLoop_ok hp (by rw [← h11]; exact hd) h11 (fun i hi s hs => VG.Proof.MlKem1024.X86_64.grp11_ok _ hi hs) di₁ r8₁ k₁.2.1 k₁.2.2 m₁

theorem compressEncode1024_correct (s : State) (hs : compressEncode1024K.pre s) :
    ∃ t s', Exec isa compressEncode1024 s t s' ∧ abiPreserved s s' ∧ compressEncode1024K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := compressEncode1024)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] (VG.Proof.MlKem1024.X86_64.ce_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem compressEncode1024_ct :
    ConstantTime isa compressEncode1024K.pre compressEncode1024K.pub compressEncode1024 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def compressEncode1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 5 | .rdx => 0x2000 | .rcx => 160 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 160⟩]

theorem compressEncode1024_verified :
    Verified X86_64.target compressEncode1024 (Spec.MlKem1024.compressEncodeContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem1024.X86_64.compressEncode1024_correct VG.Proof.MlKem1024.X86_64.compressEncode1024_ct (by
    mlkem_implies [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, VG.Proof.MlKem1024.X86_64.compressEncode1024K,
      X86_64.abi, X86_64.argRegs] [compressEncode1024Sat] using VG.Proof.MlKem1024.X86_64.compressEncode1024Sat)

theorem ce4_nosp : NoSp compressEncode1024 := nosp_of (by decide +kernel)
theorem ce4_depth : compressEncode1024.depth = 0 := by decide +kernel

/-- `vg_mlkem1024_compress_encode`, for the calls of the top-level functions. -/
theorem ceImpl1024 : CEImpl "vg_mlkem1024_compress_encode" compressEncode1024 Spec.MlKem1024.compressWidths :=
  ⟨fun _ hd => by rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with rfl | rfl <;> decide, VG.Proof.MlKem1024.X86_64.compressEncode1024_correct, VG.Proof.MlKem1024.X86_64.compressEncode1024_ct, VG.Proof.MlKem1024.X86_64.ce4_nosp,
    VG.Proof.MlKem1024.X86_64.ce4_depth⟩

end VG.Proof.MlKem1024.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress`. -/
section

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decode_decompress`

A group of 5 bytes is decoded as ML-KEM-768's are (`DD.grp_ok`), one of 11
bytes in two segments (`dgrp11_ok`, from `DD.seg`); the loop is ML-KEM-768's
(`DD.loop_ok`, `Proof/MlKem/X86_64/DecodeDecompress.lean`), and the function
is proven by its two cases.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Impl.MlKem.X86_64 (ceAcc ceSt ceTail ceLoopW ddLd ddVals ddTail ddLoopW)
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A group of 11 bytes: values 0–4 (55 bits) are the low 6 bytes 0–5; values
4–7 (44 bits) shifted right by 4 are bytes 5–10. -/
theorem dgrp11_ok (B : List Byte) (hB : B.length = 32 * 11) {i : Nat} (hi : i < 32) {s : State}
    (h : DD.GrpIn 8 11 B i s) :
    WP isa (.block (ddLd 0 6 ++ ddVals 11 0 4 ++ ddLd 5 6 ++ ([.shift .shr .r10 4] : List Instr) ++ ddVals 11 4 4)) s
      (DD.GrpOut 11 8 B i s) := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- Bytes 0–5, and values 0–3.
  refine WP.mono (ddLd_ok (o := 0) (b := 6) (by decide) s (fun k hk => by rw [Nat.zero_add]; exact h.rd k (by omega)))
    fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ddVals_ok (o := 0) (c := 4) (d := 11) (by decide) (by decide) (by decide) s₁ (fun j hj => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr j (by omega))) fun s₂ ⟨w₂, f₂, k₂⟩ => ?_
  have si₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.gpr (by decide)
  rw [si₁, Nat.mul_zero, add_ofNat_zero, m₁] at f₂
  -- Bytes 5–10, shifted, and values 4–7.
  have di₂ : s₂.gpr .rdi = s.gpr .rdi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have si₂ : s₂.gpr .rsi = s.gpr .rsi := by rw [k₂.gpr (by decide), si₁]
  have b₂ : ∀ k < 11, s₂.mem (s.gpr .rdi + BitVec.ofNat 64 k) = s.mem (s.gpr .rdi + BitVec.ofNat 64 k) :=
    fun k hk => f₂.bytes (R := ⟨s.gpr .rdi, 11⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h.dj.sub_right (Region.sub_prefix (by decide))) (show 11 ≤ 2 ^ 64 by decide) hk
  refine WP.mono (ddLd_ok (o := 5) (b := 6) (by decide) s₂ (fun k hk => by
      rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2, di₂]; exact h.rd _ (by omega))) fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  refine WP.mono (VG.Proof.MlKem1024.X86_64.shr10_ok 4 (by decide) (by decide) s₃) fun s₄ ⟨⟨r₄, m₄⟩, k₄⟩ => ?_
  have si₄ : s₄.gpr .rsi = s.gpr .rsi := by rw [k₄.gpr (by decide), k₃.gpr (by decide), si₂]
  refine WP.mono (ddVals_ok (o := 4) (c := 4) (d := 11) (by decide) (by decide) (by decide) s₄ (fun j hj => by
      rw [k₄.2.2, k₃.2.2, k₂.2.2, k₁.2.2, si₄]; exact h.wr _ (by omega))) fun s₅ ⟨w₅, f₅, k₅⟩ => ?_
  rw [si₄, m₄, m₃] at f₅
  have r9₄ : (s₄.gpr .r9).toNat = 3329 := by
    rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact h.r9
  have r9₁ : (s₁.gpr .r9).toNat = 3329 := by rw [k₁.gpr (by decide)]; exact h.r9
  refine ⟨fun j hj => ?_, ?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · by_cases hj4 : j < 4
    · -- Written by the first segment, kept by the second.
      have hk : s₅.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 =
          s₂.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 :=
        f₅.readW (r := ⟨s.gpr .rsi + BitVec.ofNat 64 (4 * j), 4⟩) (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact off_disj (by omega) (by decide)) (by decide)
      have := w₂ j hj4
      rw [si₁, Nat.zero_add] at this
      rw [hk, this, ddW_toNat (by decide) (by decide) _ r9₁, shr_toNat, r₁]
      have e : (List.range 6).map (fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (0 + k))).toNat) =
          (List.range 6).map fun t => (B.getD (11 * i + (0 + t)) 0).toNat :=
        List.map_congr_left fun t ht => by
          simp only [Nat.zero_add, h.bytes t (by have := List.mem_range.mp ht; omega)]
      rw [e, ← DD.seg (o := 0) (l := 6) (s := 0) (p := 11 * j) (c := 8) (b := 11) (by decide) (by decide) (by decide) B
        (by omega) (by omega) (by omega) (by omega),
        Nat.pow_zero, Nat.div_one]
    · have := w₅ (j - 4) (by omega)
      rw [si₄, show 4 + (j - 4) = j by omega] at this
      rw [this, ddW_toNat (by decide) (by decide) _ r9₄, shr_toNat, r₄, shr_toNat, r₃, di₂]
      have e : (List.range 6).map (fun k => (s₂.mem (s.gpr .rdi + BitVec.ofNat 64 (5 + k))).toNat) =
          (List.range 6).map fun t => (B.getD (11 * i + (5 + t)) 0).toNat :=
        List.map_congr_left fun t ht => by
          have := List.mem_range.mp ht
          rw [b₂ _ (by omega), h.bytes _ (by omega)]
      rw [e, ← DD.seg (o := 5) (l := 6) (s := 4) (p := 11 * (j - 4)) (c := 8) (b := 11) (by decide) (by decide)
        (by decide) B (by omega) (by omega) (by omega) (by omega)]
  · refine (f₂.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, sub_offset' (by decide) (by decide)⟩

/-- The loop for the width `d`, from a state with `b` in `rdi` and `f` in `rsi`. -/
theorem ddLoop_ok {s₀ : State} (hp : decodeDecompress1024K.pre s₀) {d : Nat}
    (hd : d ∈ Spec.MlKem1024.compressWidths) (hdd : dArg s₀ .rdx = d) {grp : List Instr}
    (hgrp : ∀ i < 32, ∀ s, DD.GrpIn 8 d (DD.B s₀ d) i s → WP isa (.block grp) s (DD.GrpOut d 8 (DD.B s₀ d) i s))
    {s : State} (hdi : s.gpr .rdi = DD.bP s₀) (hsi : s.gpr .rsi = DD.fP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ddLoopW 32 (grp ++ ddTail 8 d)) s fun s' =>
      PolyIs s'.mem (DD.fP s₀) (decodeDecompress d (DD.B s₀ d)) ∧ Frame [pR (DD.fP s₀)] s₀.mem s'.mem := by
  have hd11 : d ≤ 11 := by rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with rfl | rfl <;> decide
  exact DD.loop_ok (c := 8) (b := d) hp hd11 (by decide) (by decide) hd11 (by omega) (by decide) hdd hgrp
    hdi hsi hrd hwr hm

theorem ddPrologue_ok (s₀ : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 5)]) s₀ fun s =>
      (s.gpr .rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.gpr .rdx)) ∧ s.gpr .rsi = s₀.gpr .rcx ∧
        s.zf = some (BitVec.setWidth 32 (s₀.gpr .rdx) - 5 == 0) ∧ s.mem = s₀.mem) ∧ Keep [.rdx, .rsi] s₀ s := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem dd_wp {s₀ : State} (hp : decodeDecompress1024K.pre s₀) :
    WP isa decodeDecompress1024 s₀ fun s' =>
      PolyIs s'.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)) ∧
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [DD.lenEq hp rfl]
  unfold decodeDecompress1024
  refine WP.seq (WP.mono (VG.Proof.MlKem1024.X86_64.ddPrologue_ok s₀) fun s₁ ⟨⟨_, si₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h5 : dArg s₀ .rdx = 5 := by simp only [dArg, h]; rfl
    rw [h5]
    exact VG.Proof.MlKem1024.X86_64.ddLoop_ok hp (by rw [← h5]; exact hd) h5 (fun i hi s hs => DD.grp_ok (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by rw [bytesAt_length]; omega) (by omega) hs)
      di₁ si₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    have h11 : dArg s₀ .rdx = 11 := by
      rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
      · exact e
    rw [h11]
    exact VG.Proof.MlKem1024.X86_64.ddLoop_ok hp (by rw [← h11]; exact hd) h11 (fun i hi s hs => VG.Proof.MlKem1024.X86_64.dgrp11_ok _ (bytesAt_length _ _ _) hi hs)
      di₁ si₁ k₁.2.1 k₁.2.2 m₁

theorem decodeDecompress1024_correct (s : State) (hs : decodeDecompress1024K.pre s) :
    ∃ t s', Exec isa decodeDecompress1024 s t s' ∧ abiPreserved s s' ∧ decodeDecompress1024K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := decodeDecompress1024)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .r10] (VG.Proof.MlKem1024.X86_64.dd_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem decodeDecompress1024_ct :
    ConstantTime isa decodeDecompress1024K.pre decodeDecompress1024K.pub decodeDecompress1024 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def decodeDecompress1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 160 | .rdx => 5 | .rcx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 160⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decodeDecompress1024_verified :
    Verified X86_64.target decodeDecompress1024 (Spec.MlKem1024.decodeDecompressContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem1024.X86_64.decodeDecompress1024_correct VG.Proof.MlKem1024.X86_64.decodeDecompress1024_ct (by
    mlkem_implies [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig,
      VG.Proof.MlKem1024.X86_64.decodeDecompress1024K, X86_64.abi, X86_64.argRegs] [decodeDecompress1024Sat] using VG.Proof.MlKem1024.X86_64.decodeDecompress1024Sat)

theorem dd4_nosp : NoSp decodeDecompress1024 := nosp_of (by decide +kernel)
theorem dd4_depth : decodeDecompress1024.depth = 0 := by decide +kernel

/-- `vg_mlkem1024_decode_decompress`, for the calls of the top-level functions. -/
theorem ddImpl1024 : DDImpl "vg_mlkem1024_decode_decompress" decodeDecompress1024 Spec.MlKem1024.compressWidths :=
  ⟨fun _ hd => by rcases VG.Proof.MlKem1024.X86_64.widths1024 hd with rfl | rfl <;> decide, VG.Proof.MlKem1024.X86_64.decodeDecompress1024_correct, VG.Proof.MlKem1024.X86_64.decodeDecompress1024_ct, VG.Proof.MlKem1024.X86_64.dd4_nosp,
    VG.Proof.MlKem1024.X86_64.dd4_depth⟩

end VG.Proof.MlKem1024.X86_64

end
