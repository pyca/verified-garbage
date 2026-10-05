import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.AArch64.Mul
import VerifiedGarbage.Proof.MlKem.AArch64.NttInv
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.MlKem.AArch64.Kem
import Lean.Meta.Tactic.Delta
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Range

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.PrimCall`. -/
section

/-!
# ML-KEM-768 on AArch64: calling the primitives

Each call of a verified polynomial primitive, from its proof (with `WP.call`;
`sample_ntt` with `WP.callF`, as its Keccak calls have frames): what it needs
of the state it is called from, and what holds when it returns (`Kept`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem entry (s : State) {r : Reg} (h : r ∉ linkRegs := by decide) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

/-- `vg_mlkem_cbd2(b, f)`. -/
theorem cbd2_call {s : State} {b f : Addr} (h0 : s.gpr .x0 = b) (h1 : s.gpr .x1 = f)
    (hd : Region.Disjoint ⟨b, 128⟩ ⟨f, 1024⟩) (hc : Covers [⟨b, 128⟩, ⟨f, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨f, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) → Q s') :
    WP isa (.call "vg_mlkem_cbd2" cbd2) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = f := (VG.Proof.MlKem.AArch64.entry s).trans h1
  refine WP.callV (k := cbd2AArch64) Cbd2.correct (rd := [⟨b, 128⟩]) (wr := [⟨f, 1024⟩]) ?_ hc hw ?_
  · simp only [cbd2AArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hd⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [cbd2AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1]
      at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- `vg_mlkem_ntt(f, scratch)` or `vg_mlkem_inv_ntt(f, scratch)`. -/
theorem inPlace_call {t : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {c : Prog isa} {name : String}
    (hv : ∀ s, (inPlaceAArch64 t).pre s →
      ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (inPlaceAArch64 t).post s s')
    (hn : c.noFrames = true) {s : State} {f w : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = w)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩) (hr : Reduced s.mem f)
    (hw : Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (t (polyAt s.mem f)) → Q s') :
    WP isa (.call name c) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = w := (VG.Proof.MlKem.AArch64.entry s).trans h1
  refine WP.callV (k := inPlaceAArch64 t) hv (rd := []) (wr := [⟨f, 1024⟩, ⟨w, 1024⟩]) ?_
    (covers_rw' hw) hw ?_ hn
  · simp only [inPlaceAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1]
    exact ⟨trivial, trivial, hd, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [inPlaceAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0]
      at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

theorem ntt_call {s : State} {f w : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = w)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩) (hr : Reduced s.mem f)
    (hw : Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (ntt (polyAt s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem_ntt" Impl.MlKem.AArch64.ntt) s Q :=
  VG.Proof.MlKem.AArch64.inPlace_call Ntt.correct (by decide +kernel) h0 h1 hd hr hw hQ

theorem nttInv_call {s : State} {f w : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = w)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩) (hr : Reduced s.mem f)
    (hw : Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (nttInv (polyAt s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem_inv_ntt" Impl.MlKem.AArch64.nttInv) s Q :=
  VG.Proof.MlKem.AArch64.inPlace_call Ntt.correctInv (by decide +kernel) h0 h1 hd hr hw hQ

/-- `vg_mlkem_add(f, g)` or `vg_mlkem_sub(f, g)`. -/
theorem acc_call {op : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {c : Prog isa} {name : String}
    (hv : ∀ s, (accAArch64 op).pre s →
      ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accAArch64 op).post s s')
    (hn : c.noFrames = true) {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (op (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call name c) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = g := (VG.Proof.MlKem.AArch64.entry s).trans h1
  refine WP.callV (k := accAArch64 op) hv (rd := [⟨g, 1024⟩]) (wr := [⟨f, 1024⟩]) ?_ hc hw ?_ hn
  · simp only [accAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1]
    exact ⟨trivial, trivial, hd, hrf, hrg⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [accAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1]
      at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

theorem add_call {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (add (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_add" Impl.MlKem.AArch64.add) s Q :=
  VG.Proof.MlKem.AArch64.acc_call add_correct (by decide +kernel) h0 h1 hd hrf hrg hc hw hQ

theorem sub_call {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (VG.Spec.MlKem.sub (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.AArch64.sub) s Q :=
  VG.Proof.MlKem.AArch64.acc_call sub_correct (by decide +kernel) h0 h1 hd hrf hrg hc hw hQ

/-- `vg_mlkem_multiply_ntts(h, f, g, scratch)`. -/
theorem mul_call {s : State} {h f g w : Addr} (h0 : s.gpr .x0 = h) (h1 : s.gpr .x1 = f)
    (h2 : s.gpr .x2 = g) (h3 : s.gpr .x3 = w)
    (d₁ : Region.Disjoint ⟨h, 1024⟩ ⟨f, 1024⟩) (d₂ : Region.Disjoint ⟨h, 1024⟩ ⟨g, 1024⟩)
    (d₃ : Region.Disjoint ⟨h, 1024⟩ ⟨w, 1024⟩) (d₄ : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩)
    (d₅ : Region.Disjoint ⟨g, 1024⟩ ⟨w, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨f, 1024⟩, ⟨g, 1024⟩, ⟨h, 1024⟩, ⟨w, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨h, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨h, 1024⟩, ⟨w, 1024⟩] s s' →
      PolyIs s'.mem h (multiplyNTTs (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_multiply_ntts" Impl.MlKem.AArch64.multiplyNTTs) s Q := by
  have c0 : s.callEntry.gpr .x0 = h := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = f := (VG.Proof.MlKem.AArch64.entry s).trans h1
  have c2 : s.callEntry.gpr .x2 = g := (VG.Proof.MlKem.AArch64.entry s).trans h2
  have c3 : s.callEntry.gpr .x3 = w := (VG.Proof.MlKem.AArch64.entry s).trans h3
  refine WP.callV (k := mulAArch64) Mul.correct (rd := [⟨f, 1024⟩, ⟨g, 1024⟩])
    (wr := [⟨h, 1024⟩, ⟨w, 1024⟩]) ?_ hc hw ?_
  · simp only [mulAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
    exact ⟨trivial, trivial, d₁, d₂, d₃, d₄, d₅, hrf, hrg⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [mulAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1,
      c2] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- `vg_mlkem_encode12(f, out)`. -/
theorem encode12_call {s : State} {f o : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = o)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 384⟩) (hr : Reduced s.mem f)
    (hc : Covers [⟨f, 1024⟩, ⟨o, 384⟩] (s.rd ++ s.wr)) (hw : Covers [⟨o, 384⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 384⟩] s s' → bytesAt s'.mem o 384 = encode12 (polyAt s.mem f) → Q s') :
    WP isa (.call "vg_mlkem_encode12" Impl.MlKem.AArch64.encode12) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = o := (VG.Proof.MlKem.AArch64.entry s).trans h1
  refine WP.callV (k := encode12AArch64) Encode12.correct (rd := [⟨f, 1024⟩]) (wr := [⟨o, 384⟩]) ?_
    hc hw ?_
  · simp only [encode12AArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1]
    exact ⟨trivial, trivial, hd, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [encode12AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0,
      c1] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- `vg_mlkem_decode12(b, f)`. -/
theorem decode12_call {s : State} {b f : Addr} (h0 : s.gpr .x0 = b) (h1 : s.gpr .x1 = f)
    (hd : Region.Disjoint ⟨b, 384⟩ ⟨f, 1024⟩) (hc : Covers [⟨b, 384⟩, ⟨f, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨f, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (decode12 (bytesAt s.mem b 384)) → Q s') :
    WP isa (.call "vg_mlkem_decode12" Impl.MlKem.AArch64.decode12) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = f := (VG.Proof.MlKem.AArch64.entry s).trans h1
  refine WP.callV (k := decode12AArch64) Decode12.correct (rd := [⟨b, 384⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [decode12AArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hd⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [decode12AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0,
      c1] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- `vg_mlkem_compress_encode(f, d, out, 32 d)`. -/
theorem compressEncode_call {s : State} {f o : Addr} {d : Nat} (h0 : s.gpr .x0 = f)
    (h1 : ((s.gpr .x1).setWidth 32).toNat = d) (h2 : s.gpr .x2 = o) (h3 : (s.gpr .x3).toNat = 32 * d)
    (hdw : d ∈ compressWidths) (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩) (hr : Reduced s.mem f)
    (hc : Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr)) (hw : Covers [⟨o, 32 * d⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) →
      Q s') :
    WP isa (.call "vg_mlkem_compress_encode" Impl.MlKem.AArch64.compressEncode) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : ((s.callEntry.gpr .x1).setWidth 32).toNat = d := by rw [VG.Proof.MlKem.AArch64.entry s]; exact h1
  have c2 : s.callEntry.gpr .x2 = o := (VG.Proof.MlKem.AArch64.entry s).trans h2
  have c3 : (s.callEntry.gpr .x3).toNat = 32 * d := by rw [VG.Proof.MlKem.AArch64.entry s]; exact h3
  refine WP.callV (k := compressEncodeAArch64) CE.correct (rd := [⟨f, 1024⟩]) (wr := [⟨o, 32 * d⟩]) ?_
    hc hw ?_
  · simp only [compressEncodeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [compressEncodeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- `vg_mlkem_decode_decompress(b, 32 d, d, f)`. -/
theorem decodeDecompress_call {s : State} {b f : Addr} {d : Nat} (h0 : s.gpr .x0 = b)
    (h1 : (s.gpr .x1).toNat = 32 * d) (h2 : ((s.gpr .x2).setWidth 32).toNat = d) (h3 : s.gpr .x3 = f)
    (hdw : d ∈ compressWidths) (hd : Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩)
    (hc : Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' →
      PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') :
    WP isa (.call "vg_mlkem_decode_decompress" Impl.MlKem.AArch64.decodeDecompress) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = 32 * d := by rw [VG.Proof.MlKem.AArch64.entry s]; exact h1
  have c2 : ((s.callEntry.gpr .x2).setWidth 32).toNat = d := by rw [VG.Proof.MlKem.AArch64.entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = f := (VG.Proof.MlKem.AArch64.entry s).trans h3
  refine WP.callV (k := decodeDecompressAArch64) DD.correct (rd := [⟨b, 32 * d⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

theorem sampleNTTWith_fdepth (v : VG.Proof.Sha3.AArch64.Permutation) :
    (Impl.MlKem.AArch64.sampleNTTWith v.callee).aarch64Depth = 1 := by
  simp only [Impl.MlKem.AArch64.sampleNTTWith, Impl.MlKem.AArch64.sampleFastWith,
    Impl.MlKem.AArch64.sampleFullWith, Impl.MlKem.AArch64.sampleSqueezeWith,
    Impl.MlKem.AArch64.sampleSqueezeNWith, Impl.MlKem.AArch64.sampleZero,
    Impl.MlKem.AArch64.sampleLoop, Impl.MlKem.AArch64.sampleBody, Code.aarch64Depth,
    v.absorb_depth, v.pad_depth, v.squeeze_depth, Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem sampleNTT_fdepth : Impl.MlKem.AArch64.sampleNTT.aarch64Depth = 1 := by decide +kernel

/-- `vg_mlkem_sample_ntt(seed, a, scratch)`. -/
theorem sample_callWith (v : VG.Proof.Sha3.AArch64.Permutation) {s : State} {sd a w : Addr} (h0 : s.gpr .x0 = sd) (h1 : s.gpr .x1 = a)
    (h2 : s.gpr .x2 = w) (d₁ : Region.Disjoint ⟨sd, 34⟩ ⟨a, 1024⟩)
    (d₂ : Region.Disjoint ⟨sd, 34⟩ ⟨w, 2048⟩) (d₃ : Region.Disjoint ⟨a, 1024⟩ ⟨w, 2048⟩)
    (hsp : 16 ≤ s.sp.toNat) (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sd, 34⟩) (k₂ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨a, 1024⟩)
    (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨w, 2048⟩)
    (hc : Covers [⟨sd, 34⟩, ⟨a, 1024⟩, ⟨w, 2048⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨a, 1024⟩, ⟨w, 2048⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨a, 1024⟩, ⟨w, 2048⟩, below s.sp 16] s s' → Reduced s'.mem a →
      ((s'.gpr .x0 = 1 ∧ sampleNTT 280 (bytesAt s.mem sd 34) = some (polyAt s'.mem a)) ∨
        (s'.gpr .x0 = 0 ∧ sampleNTT 280 (bytesAt s.mem sd 34) = none)) → Q s') :
    WP isa (.call ("vg_mlkem_sample_ntt" ++ v.callee.suffix) (Impl.MlKem.AArch64.sampleNTTWith v.callee)) s Q := by
  have c0 : s.callEntry.gpr .x0 = sd := (VG.Proof.MlKem.AArch64.entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = a := (VG.Proof.MlKem.AArch64.entry s).trans h1
  have c2 : s.callEntry.gpr .x2 = w := (VG.Proof.MlKem.AArch64.entry s).trans h2
  refine WP.callFV (k := Sample.sampleStrong) (Sample.sample_strongWith v) (rd := [⟨sd, 34⟩])
    (wr := [⟨a, 1024⟩, ⟨w, 2048⟩]) ?_ hc hw ?_ (by rw [VG.Proof.MlKem.AArch64.sampleNTTWith_fdepth v]; decide)
  · simp only [Sample.sampleStrong, sampleAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2]
    exact ⟨trivial, trivial, d₁, d₂, d₃, hsp, k₁, k₂, k₃⟩
  · intro s' hrd hwr hsp' hf hcs hvec hpost
    rw [VG.Proof.MlKem.AArch64.sampleNTTWith_fdepth v, Nat.mul_one] at hf
    simp only [Sample.sampleStrong, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c0, c1] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, frame3 hf, hvec⟩ hpost.1 hpost.2

theorem sample_call {s : State} {sd a w : Addr} (h0 : s.gpr .x0 = sd) (h1 : s.gpr .x1 = a)
    (h2 : s.gpr .x2 = w) (d₁ : Region.Disjoint ⟨sd, 34⟩ ⟨a, 1024⟩)
    (d₂ : Region.Disjoint ⟨sd, 34⟩ ⟨w, 2048⟩) (d₃ : Region.Disjoint ⟨a, 1024⟩ ⟨w, 2048⟩)
    (hsp : 16 ≤ s.sp.toNat) (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sd, 34⟩) (k₂ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨a, 1024⟩)
    (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨w, 2048⟩)
    (hc : Covers [⟨sd, 34⟩, ⟨a, 1024⟩, ⟨w, 2048⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨a, 1024⟩, ⟨w, 2048⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨a, 1024⟩, ⟨w, 2048⟩, below s.sp 16] s s' → Reduced s'.mem a →
      ((s'.gpr .x0 = 1 ∧ sampleNTT 280 (bytesAt s.mem sd 34) = some (polyAt s'.mem a)) ∨
        (s'.gpr .x0 = 0 ∧ sampleNTT 280 (bytesAt s.mem sd 34) = none)) → Q s') :
    WP isa (.call "vg_mlkem_sample_ntt" Impl.MlKem.AArch64.sampleNTT) s Q :=
  VG.Proof.MlKem.AArch64.sample_callWith .scalar h0 h1 h2 d₁ d₂ d₃ hsp k₁ k₂ k₃ hc hw hQ

/-- What a call of `sample_ntt` needs. -/
structure SampleArgs (s : State) (sd a w : Addr) : Prop where
  h0 : s.gpr .x0 = sd
  h1 : s.gpr .x1 = a
  h2 : s.gpr .x2 = w
  d₁ : Region.Disjoint ⟨sd, 34⟩ ⟨a, 1024⟩
  d₂ : Region.Disjoint ⟨sd, 34⟩ ⟨w, 2048⟩
  d₃ : Region.Disjoint ⟨a, 1024⟩ ⟨w, 2048⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sd, 34⟩
  k₂ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨a, 1024⟩
  k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨w, 2048⟩
  hc : Covers [⟨sd, 34⟩, ⟨a, 1024⟩, ⟨w, 2048⟩] (s.rd ++ s.wr)
  hw : Covers [⟨a, 1024⟩, ⟨w, 2048⟩] s.wr

theorem SampleArgs.pre {s : State} {sd a w : Addr} (h : VG.Proof.MlKem.AArch64.SampleArgs s sd a w) :
    Sample.sampleStrong.pre (s.callEntry.withRegions [⟨sd, 34⟩] [⟨a, 1024⟩, ⟨w, 2048⟩]) := by
  have c0 : s.callEntry.gpr .x0 = sd := (VG.Proof.MlKem.AArch64.entry s).trans h.h0
  have c1 : s.callEntry.gpr .x1 = a := (VG.Proof.MlKem.AArch64.entry s).trans h.h1
  have c2 : s.callEntry.gpr .x2 = w := (VG.Proof.MlKem.AArch64.entry s).trans h.h2
  simp only [Sample.sampleStrong, sampleAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃⟩

/-- A call of `sample_ntt` returns with the stack pointer it was called with. -/
theorem SampleArgs.spWith (v : VG.Proof.Sha3.AArch64.Permutation) {s : State} {sd a w : Addr} (h : VG.Proof.MlKem.AArch64.SampleArgs s sd a w) :
    WP isa (.call ("vg_mlkem_sample_ntt" ++ v.callee.suffix) (Impl.MlKem.AArch64.sampleNTTWith v.callee)) s fun s' => s'.sp = s.sp :=
  VG.Proof.MlKem.AArch64.sample_callWith v h.h0 h.h1 h.h2 h.d₁ h.d₂ h.d₃ h.hsp h.k₁ h.k₂ h.k₃ h.hc h.hw fun _ k _ _ => k.sp

theorem SampleArgs.sp {s : State} {sd a w : Addr} (h : VG.Proof.MlKem.AArch64.SampleArgs s sd a w) :
    WP isa (.call "vg_mlkem_sample_ntt" Impl.MlKem.AArch64.sampleNTT) s fun s' => s'.sp = s.sp :=
  VG.Proof.MlKem.AArch64.sample_call h.h0 h.h1 h.h2 h.d₁ h.d₂ h.d₃ h.hsp h.k₁ h.k₂ h.k₃ h.hc h.hw fun _ k _ _ => k.sp

/-- Two calls of `sample_ntt` on the same seed, at the same addresses, leak the same. -/
theorem sample_ctWith (v : VG.Proof.Sha3.AArch64.Permutation) {P : State → State → Prop} {sd a w : Addr}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.MlKem.AArch64.SampleArgs s₁ sd a w ∧ VG.Proof.MlKem.AArch64.SampleArgs s₂ sd a w ∧
      bytesAt s₁.mem sd 34 = bytesAt s₂.mem sd 34 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call ("vg_mlkem_sample_ntt" ++ v.callee.suffix) (Impl.MlKem.AArch64.sampleNTTWith v.callee)) fun _ _ => True :=
  AArch64.RelCT.call (Sample.sample_strongWith v) (Sample.ct_strongWith v) [⟨sd, 34⟩] [⟨a, 1024⟩, ⟨w, 2048⟩] fun s₁ s₂ h => by
    obtain ⟨A₁, A₂, hb, hsp⟩ := hP s₁ s₂ h
    refine ⟨A₁.pre, A₂.pre, ?_, A₁.hc, A₁.hw, A₂.hc, A₂.hw⟩
    have c0 : ∀ {u : State}, VG.Proof.MlKem.AArch64.SampleArgs u sd a w → u.callEntry.gpr .x0 = sd := fun hu => (VG.Proof.MlKem.AArch64.entry _).trans hu.h0
    have c1 : ∀ {u : State}, VG.Proof.MlKem.AArch64.SampleArgs u sd a w → u.callEntry.gpr .x1 = a := fun hu => (VG.Proof.MlKem.AArch64.entry _).trans hu.h1
    have c2 : ∀ {u : State}, VG.Proof.MlKem.AArch64.SampleArgs u sd a w → u.callEntry.gpr .x2 = w := fun hu => (VG.Proof.MlKem.AArch64.entry _).trans hu.h2
    simp only [Sample.sampleStrong, sampleAArch64, State.withRegions_gpr, State.withRegions_sp,
      State.withRegions_mem, State.callEntry_sp, State.callEntry_mem, c0 A₁, c1 A₁, c2 A₁, c0 A₂, c1 A₂,
      c2 A₂, hsp, hb]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem sample_ct {P : State → State → Prop} {sd a w : Addr}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.MlKem.AArch64.SampleArgs s₁ sd a w ∧ VG.Proof.MlKem.AArch64.SampleArgs s₂ sd a w ∧
      bytesAt s₁.mem sd 34 = bytesAt s₂.mem sd 34 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call "vg_mlkem_sample_ntt" Impl.MlKem.AArch64.sampleNTT) fun _ _ => True :=
  VG.Proof.MlKem.AArch64.sample_ctWith .scalar hP

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.TopArgs`. -/
section

/-!
# ML-KEM-768 on AArch64: buffers of the top-level functions

The top-level functions use buffers at offsets of their arguments: bytes `[o,
o + l)` of argument `b` (`R A b o l`, with `A b` its pointer and `L b` its
length). Two such buffers are disjoint if they are in different arguments,
which are disjoint, or apart in the same one (`R.disj`); each lies within its
argument (`R.sub`), and so apart from the stack below the stack pointer
(`R.stk`). These reduce the region facts the calls need to arithmetic on the
offsets.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64

/-- Bytes `[o, o + l)` of argument `b`. -/
abbrev R (A : Nat → Addr) (b o l : Nat) : Region := ⟨A b + BitVec.ofNat 64 o, l⟩

/-- The arguments' regions `⟨A b, L b⟩` (for `b < nb`) are pairwise
disjoint, at most 32 KiB, and apart from the 16 bytes below `sp`. -/
structure ArgsOk (A : Nat → Addr) (L : Nat → Nat) (nb : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → Region.Disjoint ⟨A b, L b⟩ ⟨A c, L c⟩
  len : ∀ b < nb, L b ≤ 32768
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, L b⟩

theorem R.sub {A : Nat → Addr} {b o l len : Nat} (h : o + l ≤ len) :
    Region.Sub (VG.Proof.MlKem.AArch64.R A b o l) ⟨A b, len⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - A b).toNat ≤ (x - (A b + BitVec.ofNat 64 o)).toNat + o := by
    rw [show x - A b = (x - (A b + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o by bv_omega, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem sub_offset' {p : Addr} {k n len : Nat} (h : k + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 k, n⟩ ⟨p, len⟩ :=
  R.sub (A := fun _ => p) (b := 0) h

theorem R.sub2 {A : Nat → Addr} {b o l o' l' : Nat} (h₁ : o' ≤ o) (h₂ : o + l ≤ o' + l') :
    Region.Sub (VG.Proof.MlKem.AArch64.R A b o l) (VG.Proof.MlKem.AArch64.R A b o' l') := by
  have e : VG.Proof.MlKem.AArch64.R A b o l = ⟨A b + BitVec.ofNat 64 o' + BitVec.ofNat 64 (o - o'), l⟩ := by
    simp only [VG.Proof.MlKem.AArch64.R, ptr_add, Nat.add_sub_cancel' h₁]
  rw [e]; exact VG.Proof.MlKem.AArch64.sub_offset' (by omega)

theorem R.disj {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : VG.Proof.MlKem.AArch64.ArgsOk A L nb sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ L b₁)
    (f₂ : o₂ + l₂ ≤ L b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (VG.Proof.MlKem.AArch64.R A b₁ o₁ l₁).Disjoint (VG.Proof.MlKem.AArch64.R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    have hl := h.len b₁ hb₁
    have hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem R.stk {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : VG.Proof.MlKem.AArch64.ArgsOk A L nb sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ L b) : Region.Disjoint ⟨sp - 16, 16⟩ (VG.Proof.MlKem.AArch64.R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

theorem R.cov {A : Nat → Addr} {b o l len : Nat} {X : List Region} (hm : (⟨A b, len⟩ : Region) ∈ X)
    (f : o + l ≤ len) : Covers [VG.Proof.MlKem.AArch64.R A b o l] X :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, hm, o, rfl, f⟩

theorem in_R {A : Nat → Addr} {b o l : Nat} {X : List Region} (hc : Covers [VG.Proof.MlKem.AArch64.R A b o l] X) {k n : Nat}
    (hk : k + n ≤ l) (hl : l < 2 ^ 64) : InRegions X (A b + BitVec.ofNat 64 (o + k)) n :=
  hc _ _ ⟨_, List.mem_singleton_self _, by rw [← ptr_add]; exact contains_off hk hl⟩

theorem R.contains {A : Nat → Addr} {b o l k n : Nat} (hk : k + n ≤ l) (hl : l < 2 ^ 64) :
    (VG.Proof.MlKem.AArch64.R A b o l).Contains (A b + BitVec.ofNat 64 (o + k)) n := by
  rw [← ptr_add]; exact contains_off hk hl

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Lay`. -/
section

/-!
# ML-KEM on AArch64: the parameter sets of the top-level functions

The proofs of `keygen`, `encaps` and `decaps` are stated once for a
parameter set `P` (`KemLay`) that is well formed (`KemLay.Wf`): the facts
about `k`, the widths and the size of `scratch` that the buffers in
`scratch` need, each decided for ML-KEM-768 and ML-KEM-1024 on their
literals; and whose functions at the widths `d_u` and `d_v` meet their
contracts (`KemLay.Calls`). `lom` does the arithmetic on the offsets.

Their code runs steps one after another (`seqs`): `WPs` and `RelCTs` are
the weakest precondition and the constant time of such a list of steps, by
an invariant over the steps of a loop (`WPs.range`, `WPs.matrix`, `RelCTs.matrix`)
or over the products of a sum (`WPs.dot`).
-/

namespace VG.Impl.MlKem.AArch64.KemLay

open VG VG.AArch64 VG.Spec.MlKem

/-- The parameter set of FIPS 203 (`η₁ = η₂ = 2`). -/
def params (P : KemLay) : Params := { k := P.k, η₁ := 2, η₂ := 2, du := P.du, dv := P.dv }

/-- What the buffers in `scratch` need: `1 ≤ k ≤ 4`, widths of at most 11
bits, and room for the buffers of `KG` and `KEM` in `scratch` and below 32 KiB, and
`scratch` below 64 KiB. -/
structure Wf (P : KemLay) : Prop where
  facts : 1 ≤ P.k ∧ P.k ≤ 4 ∧ P.k * P.k ≤ 16 ∧ 1 ≤ P.du ∧ P.du ≤ 11 ∧ 1 ≤ P.dv ∧ P.dv ≤ 11 ∧
    P.du * P.k ≤ 44 ∧ 4128 + 1024 * (P.k * P.k) + 1024 * P.k + 3072 + 48 ≤ P.scl ∧
    4248 + 1024 * (P.k * P.k) + 1024 * P.k + 5120 + 32 * (P.du * P.k + P.dv) + 48 ≤ P.scl ∧
    4248 + 1024 * (P.k * P.k) + 1024 * P.k + 5120 + 32 * (P.du * P.k + P.dv) + 48 ≤ 32768 ∧
    P.scl < 65536

end VG.Impl.MlKem.AArch64.KemLay

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-- The offsets of `KG` and `KEM` and the lengths of a `KemLay`. -/
def offsetNames : Array Lean.Name :=
  #[``KG.ST, ``KG.WK, ``KG.SB, ``KG.SG, ``KG.BK, ``KG.PB, ``KG.SS, ``KG.NS, ``KG.AH, ``KG.SH,
    ``KG.EP, ``KG.TP, ``KG.PP, ``KG.SV, ``KG.aOff, ``KG.sOff, ``KEM.ST, ``KEM.WK, ``KEM.SB,
    ``KEM.HB, ``KEM.MB, ``KEM.RB, ``KEM.KP, ``KEM.JB, ``KEM.PB, ``KEM.SS, ``KEM.NS, ``KEM.AH,
    ``KEM.YH, ``KEM.EP, ``KEM.TP, ``KEM.PP, ``KEM.TH, ``KEM.CB, ``KEM.SV, ``KEM.aOff,
    ``KEM.yOff, ``KemLay.ctLen, ``KemLay.ekLen, ``KemLay.dkLen]

open Lean Meta Elab Tactic in
/-- Unfolds the offsets (`offsetNames`) in the goal and every hypothesis.
Like `delta` (and unlike `simp only [KG.ST, …]`, which builds its lemmas
from the definitions at every call) it only replaces each constant by its
value. -/
elab "lom_unfold" : tactic => withMainContext do
  let p := (offsetNames.contains ·)
  let mut g ← getMainGoal
  for fv in (← getLCtx).getFVarIds do
    let d ← fv.getDecl
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t' ← deltaExpand t p
    if t' != t then g ← g.replaceLocalDeclDefEq fv t'
  let t ← instantiateMVars (← g.getType)
  let t' ← deltaExpand t p
  if t' != t then g ← g.replaceTargetDefEq t'
  replaceMainGoal [g]

/-- Arithmetic on the offsets of a well-formed parameter set (`‹KemLay.Wf _›`
in the context) and the facts `hs`. -/
syntax "lom" ("[" term,* "]")? : tactic

macro_rules
  | `(tactic| lom) => `(tactic| (
      (try have := (‹KemLay.Wf _›).facts); clear_non_arith; lom_unfold; omega))
  | `(tactic| lom []) => `(tactic| lom)
  | `(tactic| lom [$h:term, $hs:term,*]) => `(tactic| (have := $h; lom [$hs,*]))
  | `(tactic| lom [$h:term]) => `(tactic| (have := $h; lom))

/-- Entry `k i + j` of a `k × k` matrix. -/
theorem ij_lt {k i j : Nat} (hi : i < k) (hj : j < k) : k * i + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)

theorem ij_div {k i j : Nat} (hj : j < k) : (k * i + j) / k = i ∧ (k * i + j) % k = j := by
  have hk : 0 < k := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem div_lt {k e : Nat} (he : e < k * k) : e / k < k := Nat.div_lt_of_lt_mul he

theorem mod_lt {k e : Nat} (he : e < k * k) : e % k < k :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by subst h; simp at he)

theorem div_add_mod' {k e : Nat} : k * (e / k) + e % k = e := Nat.div_add_mod e k

/-- `a i + a ≤ a k` for `i < k`. -/
theorem mul_succ_le {a i k : Nat} (hi : i < k) : a * i + a ≤ a * k := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-! ## Steps one after another -/

theorem map_range_ne_nil {α : Type} {k : Nat} (hk : 1 ≤ k) (f : Nat → α) : (List.range k).map f ≠ [] := by
  simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega

theorem matrix_ne_nil {α : Type} {k : Nat} (hk : 1 ≤ k) {g : Nat → Nat → α} :
    ((List.range k).flatMap fun i => (List.range k).map (g i)) ≠ [] := by
  intro h
  exact VG.Proof.MlKem.AArch64.map_range_ne_nil hk (g 0) (List.flatMap_eq_nil_iff.mp h 0 (List.mem_range.mpr (by omega)))

/-- `WP` of running `cs` one after another. -/
def WPs : List (Prog isa) → State → (State → Prop) → Prop
  | [], s, Q => Q s
  | c :: cs, s, Q => WP isa c s fun s' => VG.Proof.MlKem.AArch64.WPs cs s' Q

namespace WPs

theorem mono : ∀ {cs : List (Prog isa)} {s : State} {Q Q' : State → Prop}, VG.Proof.MlKem.AArch64.WPs cs s Q →
    (∀ s, Q s → Q' s) → VG.Proof.MlKem.AArch64.WPs cs s Q'
  | [], _, _, _, h, hq => hq _ h
  | _ :: _, _, _, _, h, hq => WP.mono h fun _ h' => VG.Proof.MlKem.AArch64.WPs.mono h' hq

theorem seqs : ∀ {cs : List (Prog isa)} {s : State} {Q : State → Prop}, cs ≠ [] → VG.Proof.MlKem.AArch64.WPs cs s Q →
    WP isa (Impl.MlKem.AArch64.seqs cs) s Q
  | [_], _, _, _, h => WP.mono h fun _ h' => h'
  | _ :: _ :: _, _, _, _, h => WP.seq (WP.mono h fun _ h' => VG.Proof.MlKem.AArch64.WPs.seqs (List.cons_ne_nil _ _) h')

theorem append : ∀ {l₁ l₂ : List (Prog isa)} {s : State} {Q : State → Prop},
    VG.Proof.MlKem.AArch64.WPs l₁ s (fun s' => VG.Proof.MlKem.AArch64.WPs l₂ s' Q) → VG.Proof.MlKem.AArch64.WPs (l₁ ++ l₂) s Q
  | [], _, _, _, h => h
  | _ :: _, _, _, _, h => WP.mono h fun _ h' => VG.Proof.MlKem.AArch64.WPs.append h'

theorem cons {c : Prog isa} {cs : List (Prog isa)} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => VG.Proof.MlKem.AArch64.WPs cs s' Q) : VG.Proof.MlKem.AArch64.WPs (c :: cs) s Q := h

theorem single {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) : VG.Proof.MlKem.AArch64.WPs [c] s Q :=
  WP.mono h fun _ h' => h'

/-- A loop over `i < n`, by an invariant `I i` before step `i`. -/
theorem range {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, ∀ s, I i s → WP isa (f i) s (I (i + 1))) →
      ∀ {s : State}, I 0 s → VG.Proof.MlKem.AArch64.WPs ((List.range n).map f) s (I n)
  | 0, _, _, h => h
  | n + 1, hf, _, h => by
    rw [List.range_succ, List.map_append]
    exact VG.Proof.MlKem.AArch64.WPs.append (VG.Proof.MlKem.AArch64.WPs.mono (VG.Proof.MlKem.AArch64.WPs.range (fun i hi => hf i (by omega)) h) fun s' h' =>
      VG.Proof.MlKem.AArch64.WPs.single (hf n (by omega) s' h'))

/-- The `k²` steps of a matrix, row by row, by an invariant `I e` before
entry `e = k i + j`. -/
theorem matrix {k : Nat} {g : Nat → Nat → Prog isa} {I : Nat → State → Prop}
    (hg : ∀ i < k, ∀ j < k, ∀ s, I (k * i + j) s → WP isa (g i j) s (I (k * i + j + 1))) :
    ∀ {n : Nat}, n ≤ k → ∀ {s : State}, I 0 s →
      VG.Proof.MlKem.AArch64.WPs ((List.range n).flatMap fun i => (List.range k).map (g i)) s (I (k * n))
  | 0, _, _, h => h
  | n + 1, hn, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.MlKem.AArch64.WPs.append (VG.Proof.MlKem.AArch64.WPs.mono (VG.Proof.MlKem.AArch64.WPs.matrix hg (by omega) h) fun s' h' => ?_)
    have r := VG.Proof.MlKem.AArch64.WPs.range (f := g n) (I := fun j => I (k * n + j)) (n := k)
      (fun j hj s hs => hg n (by omega) j hj s hs) h'
    rwa [← Nat.mul_succ] at r

/-- A sum of `n` products into `tp` (`T`), each other one first into `pp`
(`Q`), by an invariant `E`: after the steps, `tp` holds `v 0 + ⋯ + v (n - 1)`. -/
theorem dot {tp pp : Nat} {term : Nat → Nat → List (Prog isa)} {E : State → Prop}
    {T Q : State → Spec.MlKem.Poly → Prop} {v : Nat → Spec.MlKem.Poly} {N : Nat}
    (h0 : ∀ s, E s → VG.Proof.MlKem.AArch64.WPs (term 0 tp) s fun s' => E s' ∧ T s' (v 0))
    (hj : ∀ j, 1 ≤ j → j < N → ∀ s a, E s → T s a →
      VG.Proof.MlKem.AArch64.WPs (term j pp) s fun s' => E s' ∧ T s' a ∧ Q s' (v j))
    (hadd : ∀ s a b, E s → T s a → Q s b →
      WP isa (addAt tp pp) s fun s' => E s' ∧ T s' (Spec.MlKem.add a b)) :
    ∀ {n : Nat}, 1 ≤ n → n ≤ N → ∀ {s : State}, E s →
      VG.Proof.MlKem.AArch64.WPs (dotSteps tp pp term n) s fun s' => E s' ∧ T s' (KPke.foldK Spec.MlKem.add Spec.MlKem.zero v n)
  | 1, _, _, _, h => h0 _ h
  | n + 2, _, hn, _, h => by
    rw [dotSteps, List.append_assoc]
    refine VG.Proof.MlKem.AArch64.WPs.append (VG.Proof.MlKem.AArch64.WPs.mono (VG.Proof.MlKem.AArch64.WPs.dot h0 hj hadd (n := n + 1) (by omega) (by omega) h) fun s₁ ⟨e₁, t₁⟩ => ?_)
    refine VG.Proof.MlKem.AArch64.WPs.append (VG.Proof.MlKem.AArch64.WPs.mono (hj (n + 1) (by omega) (by omega) s₁ _ e₁ t₁) fun s₂ ⟨e₂, t₂, q₂⟩ => ?_)
    exact VG.Proof.MlKem.AArch64.WPs.single (hadd s₂ _ _ e₂ t₂ q₂)

end WPs

/-- Constant time of running `cs` one after another, through relations
between the steps. -/
def RelCTs : (State → State → Prop) → List (Prog isa) → (State → State → Prop) → Prop
  | P, [], Q => ∀ s₁ s₂, P s₁ s₂ → Q s₁ s₂
  | P, c :: cs, Q => ∃ R, RelCT isa P c R ∧ VG.Proof.MlKem.AArch64.RelCTs R cs Q

namespace RelCTs

theorem seqs : ∀ {cs : List (Prog isa)} {P Q : State → State → Prop}, cs ≠ [] → VG.Proof.MlKem.AArch64.RelCTs P cs Q →
    RelCT isa P (Impl.MlKem.AArch64.seqs cs) Q
  | [_], _, _, _, ⟨_, h, hq⟩ => RelCT.mono h (fun _ _ h => h) hq
  | _ :: _ :: _, _, _, _, ⟨_, h, hr⟩ => RelCT.seq h (VG.Proof.MlKem.AArch64.RelCTs.seqs (List.cons_ne_nil _ _) hr)

theorem append : ∀ {l₁ l₂ : List (Prog isa)} {P R Q : State → State → Prop},
    VG.Proof.MlKem.AArch64.RelCTs P l₁ R → VG.Proof.MlKem.AArch64.RelCTs R l₂ Q → VG.Proof.MlKem.AArch64.RelCTs P (l₁ ++ l₂) Q
  | [], [], _, _, _, h₁, h₂ => fun _ _ h => h₂ _ _ (h₁ _ _ h)
  | [], _ :: _, _, _, _, h₁, ⟨R', h, hr⟩ => ⟨R', RelCT.mono h h₁ fun _ _ h => h, hr⟩
  | _ :: _, _, _, _, _, ⟨R', h, hr⟩, h₂ => ⟨R', h, VG.Proof.MlKem.AArch64.RelCTs.append hr h₂⟩

theorem range {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, RelCT isa (I i) (f i) (I (i + 1))) → VG.Proof.MlKem.AArch64.RelCTs (I 0) ((List.range n).map f) (I n)
  | 0, _ => fun _ _ h => h
  | n + 1, hf => by
    rw [List.range_succ, List.map_append]
    exact VG.Proof.MlKem.AArch64.RelCTs.append (VG.Proof.MlKem.AArch64.RelCTs.range fun i hi => hf i (by omega)) ⟨_, hf n (by omega), fun _ _ h => h⟩

theorem matrix {k : Nat} {g : Nat → Nat → Prog isa} {I : Nat → State → State → Prop}
    (hg : ∀ i < k, ∀ j < k, RelCT isa (I (k * i + j)) (g i j) (I (k * i + j + 1))) :
    ∀ {n : Nat}, n ≤ k → VG.Proof.MlKem.AArch64.RelCTs (I 0) ((List.range n).flatMap fun i => (List.range k).map (g i)) (I (k * n))
  | 0, _ => fun _ _ h => h
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have r := VG.Proof.MlKem.AArch64.RelCTs.range (f := g n) (I := fun j => I (k * n + j)) (n := k) fun j hj => hg n (by omega) j hj
    rw [Nat.add_zero, ← Nat.mul_succ] at r
    exact VG.Proof.MlKem.AArch64.RelCTs.append (VG.Proof.MlKem.AArch64.RelCTs.matrix hg (by omega)) r

end RelCTs

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KgCommon`. -/
section

/-!
# ML-KEM on AArch64: what the proof of `keygen` shares

For a well-formed parameter set `P` (ML-KEM-768 or ML-KEM-1024): the
per-target contract, the arguments as buffers (`kA`, `kL`: 0 `seed`, 1 `ek`,
2 `dk`, 3 `scratch`), and what holds from the prologue to the epilogue
(`KB`): the pointers in `x25`–`x28`, our caller's registers saved in
`scratch`, the other callee-saved registers, and the seed.
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.AArch64 (KemLay)

/-- AArch64 contract for `keyGen(seed = x0, ek = x1, dk = x2, scratch = x3) ->
w0` of the parameter set `P`. -/
def keyGenAArch64 (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 64⟩
    let ek : Region := ⟨s.gpr .x1, P.ekLen⟩
    let dk : Region := ⟨s.gpr .x2, P.dkLen⟩
    let scratch : Region := ⟨s.gpr .x3, P.scl⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [ek, dk, scratch] ∧ seed.Disjoint ek ∧ seed.Disjoint dk ∧
    seed.Disjoint scratch ∧ ek.Disjoint dk ∧ ek.Disjoint scratch ∧ dk.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint ek ∧ stack.Disjoint dk ∧
    stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => keyGenInternal P.params iters (bytesAt s.mem (s.gpr .x0) 32)
        (bytesAt s.mem (s.gpr .x0 + 32) 32)) ((s'.gpr .x0).setWidth 32)
      (bytesAt s'.mem (s.gpr .x1) P.ekLen, bytesAt s'.mem (s.gpr .x2) P.dkLen)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
      leakRho (keyGenRho P.params (bytesAt s₁.mem (s₁.gpr .x0) 32)) =
        leakRho (keyGenRho P.params (bytesAt s₂.mem (s₂.gpr .x0) 32))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- The arguments: 0 `seed`, 1 `ek`, 2 `dk`, 3 `scratch`. -/
def kA (s₀ : State) : Nat → Addr
  | 0 => s₀.gpr .x0
  | 1 => s₀.gpr .x1
  | 2 => s₀.gpr .x2
  | _ => s₀.gpr .x3

/-- Their lengths. -/
def kL (P : KemLay) : Nat → Nat
  | 0 => 64
  | 1 => P.ekLen
  | 2 => P.dkLen
  | _ => P.scl

/-- The register we keep each in. -/
def breg : Nat → Reg
  | 0 => .x25
  | 1 => .x26
  | 2 => .x27
  | _ => .x28

theorem kL0 : VG.Proof.MlKem.AArch64.KeyGen.kL P 0 = 64 := rfl
theorem kL1 : VG.Proof.MlKem.AArch64.KeyGen.kL P 1 = P.ekLen := rfl
theorem kL2 : VG.Proof.MlKem.AArch64.KeyGen.kL P 2 = P.dkLen := rfl
theorem kL3 : VG.Proof.MlKem.AArch64.KeyGen.kL P 3 = P.scl := rfl

/-- The arguments' regions `⟨A b, len b⟩` (for `b < nb`) are pairwise
disjoint, at most 64 KiB, and apart from the 16 bytes below `sp`. -/
structure Args (A : Nat → Addr) (ln : Nat → Nat) (nb : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → Region.Disjoint ⟨A b, ln b⟩ ⟨A c, ln c⟩
  len : ∀ b < nb, ln b ≤ 65536
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, ln b⟩

theorem Args.rdisj {A : Nat → Addr} {ln : Nat → Nat} {nb : Nat} {sp : Addr} (h : VG.Proof.MlKem.AArch64.KeyGen.Args A ln nb sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ ln b₁)
    (f₂ : o₂ + l₂ ≤ ln b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (VG.Proof.MlKem.AArch64.R A b₁ o₁ l₁).Disjoint (VG.Proof.MlKem.AArch64.R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    have hl := h.len b₁ hb₁
    have hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem Args.rstk {A : Nat → Addr} {ln : Nat → Nat} {nb : Nat} {sp : Addr} (h : VG.Proof.MlKem.AArch64.KeyGen.Args A ln nb sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ ln b) : Region.Disjoint ⟨sp - 16, 16⟩ (VG.Proof.MlKem.AArch64.R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

structure Pre (P : KemLay) (s₀ : State) : Prop where
  rd : s₀.rd = [⟨VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0, VG.Proof.MlKem.AArch64.KeyGen.kL P 0⟩]
  wr : s₀.wr = [⟨VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 1, VG.Proof.MlKem.AArch64.KeyGen.kL P 1⟩, ⟨VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2, VG.Proof.MlKem.AArch64.KeyGen.kL P 2⟩, ⟨VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3, VG.Proof.MlKem.AArch64.KeyGen.kL P 3⟩]
  args : VG.Proof.MlKem.AArch64.KeyGen.Args (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) (VG.Proof.MlKem.AArch64.KeyGen.kL P) 4 s₀.sp
  sp16 : 16 ≤ s₀.sp.toNat
  wf : P.Wf

theorem kL_le (hP : P.Wf) : ∀ b, VG.Proof.MlKem.AArch64.KeyGen.kL P b ≤ 65536
  | 0 => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; decide
  | 1 => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  | 2 => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  | _ + 3 => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom

/-- `scratch` holds the saved registers. -/
theorem Pre.sv {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) : SV P + 48 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by
  have := hp.wf; simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom

theorem pre_of (hP : P.Wf) {s₀ : State} (h : (VG.Proof.MlKem.keyGenAArch64 P).pre s₀) : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀ := by
  obtain ⟨rd, wr, d01, d02, d03, d12, d13, d23, sp16, k0, k1, k2, k3⟩ := h
  refine ⟨rd, wr, ⟨fun b hb c hc hbc => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16, hP⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | assumption | exact e ‹_›
  · exact VG.Proof.MlKem.AArch64.KeyGen.kL_le hP b
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    exacts [k0, k1, k2, k3]

/-! ## What holds throughout -/

/-- Our caller's `x24`–`x28` and `x30`, saved in `scratch`. -/
def Saved (P : KemLay) (s₀ : State) (m : Mem) : Prop :=
  ∀ k < 6, m.readW (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 64 =
    s₀.gpr ([Reg.x24, .x25, .x26, .x27, .x28, .x30].getD k .x0)

/-- The registers the function keeps for itself. -/
abbrev own : List Reg := [.x24, .x25, .x26, .x27, .x28, .x30]

/-- From the prologue on. -/
structure KB (P : KemLay) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x25 : s.gpr .x25 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0
  x26 : s.gpr .x26 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 1
  x27 : s.gpr .x27 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2
  x28 : s.gpr .x28 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3
  cs : ∀ r ∈ preserved, r ∉ VG.Proof.MlKem.AArch64.KeyGen.own → s.gpr r = s₀.gpr r
  sv : VG.Proof.MlKem.AArch64.KeyGen.Saved P s₀ s.mem
  seed : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 0) 64 = bytesAt s₀.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 0) 64
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

theorem KB.breg {s₀ s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) : ∀ {b : Nat}, b < 4 → s.gpr (VG.Proof.MlKem.AArch64.KeyGen.breg b) = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ b
  | 0, _ => h.x25
  | 1, _ => h.x26
  | 2, _ => h.x27
  | 3, _ => h.x28

/-- The saved registers are bytes `[SV, SV P + 48)` of `scratch`. -/
abbrev svR (P : KemLay) (s₀ : State) : Region := VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SV P) 48

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : VG.Proof.MlKem.AArch64.KeyGen.Saved P s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.AArch64.KeyGen.svR P s₀).Disjoint r) : VG.Proof.MlKem.AArch64.KeyGen.Saved P s₀ m' := fun k hk => by
  rw [← h k hk]
  refine hf.readW (r := VG.Proof.MlKem.AArch64.KeyGen.svR P s₀) ?_ hd (by decide)
  rw [show VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k) = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P) + BitVec.ofNat 64 (8 * k)
    by rw [ptr_add]]
  exact contains_off (by omega) (by decide)

/-- The callee-saved registers but `x24` and `x30`. -/
abbrev kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem pres_kept : ∀ r ∈ preserved, r ∉ VG.Proof.MlKem.AArch64.KeyGen.own → r ∈ VG.Proof.MlKem.AArch64.KeyGen.kept := by decide

/-- Memory changes only in `rs`, apart from the saved registers and the seed;
the function's own registers are kept. -/
theorem KB.frame {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {rs : List Region} {regs : List Reg}
    (hk : Keep regs s s') (hf : Frame rs s.mem s'.mem) (hr : ∀ r ∈ VG.Proof.MlKem.AArch64.KeyGen.kept, r ∉ regs)
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.AArch64.KeyGen.svR P s₀).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 0 0 64).Disjoint r) : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.get .x25 (hr _ (by decide)), h.x25], by rw [hk.get .x26 (hr _ (by decide)), h.x26],
    by rw [hk.get .x27 (hr _ (by decide)), h.x27], by rw [hk.get .x28 (hr _ (by decide)), h.x28],
    fun r hp ho => by rw [hk.get r (hr r (VG.Proof.MlKem.AArch64.KeyGen.pres_kept r hp ho)), h.cs r hp ho],
    h.sv.frame hf fun r hr => (hd r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hd r hr).2) (by decide), h.seed], fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

theorem KB.block {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {regs : List Reg} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ VG.Proof.MlKem.AArch64.KeyGen.kept, r ∉ regs) : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' :=
  h.frame (rs := []) hk (by rw [hm]; exact Frame.refl _ _) hr (fun _ h => by cases h)

/-- A call, which changes only memory in `rs` and registers that are not
callee-saved. -/
theorem KB.call {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {rs : List Region} (hk : Kept rs s s')
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.AArch64.KeyGen.svR P s₀).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 0 0 64).Disjoint r) : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.cs _ (by decide) (by decide), h.x25], by rw [hk.cs _ (by decide) (by decide), h.x26],
    by rw [hk.cs _ (by decide) (by decide), h.x27], by rw [hk.cs _ (by decide) (by decide), h.x28],
    fun r hp ho => by
      rw [hk.cs r hp (fun e => ho (by rw [e]; decide)), h.cs r hp ho],
    h.sv.frame hk.frame fun r hr => (hd r hr).1,
    by rw [bytesAt_frame hk.frame (fun r hr => (hd r hr).2) (by decide), h.seed], fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

/-! ## Regions -/

/-- A bound on an offset into argument `b`. -/
macro "kl" : tactic => `(tactic| first | decide |
  ((try have := (‹Pre _ _›).wf.facts); clear_non_arith; simp -failIfUnchanged only [kL] at *; lom))

theorem sv_disj {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b)
    (hs : b ≠ 3 ∨ SV P + 48 ≤ o ∨ o + l ≤ SV P) : (VG.Proof.MlKem.AArch64.KeyGen.svR P s₀).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l) :=
  hp.args.rdisj (by decide) hb hp.sv f (by omega)

theorem seed_disj {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b)
    (hs : b ≠ 0) : (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 0 0 64).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l) :=
  hp.args.rdisj (by decide) hb (by kl) f (.inl (Ne.symm hs))

/-- Both, as `KB.call` needs them. -/
theorem kb_disj {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b)
    (hs : b ≠ 3 ∨ SV P + 48 ≤ o ∨ o + l ≤ SV P) (h0 : b ≠ 0) :
    (VG.Proof.MlKem.AArch64.KeyGen.svR P s₀).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l) ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 0 0 64).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l) :=
  ⟨VG.Proof.MlKem.AArch64.KeyGen.sv_disj hp hb f hs, VG.Proof.MlKem.AArch64.KeyGen.seed_disj hp hb f h0⟩

/-- `kA s₀ b` as a region's base, for the regions the callees are given. -/
theorem stk_R {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b) :
    (VG.Proof.MlKem.AArch64.stk s).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l) := by
  rw [stk_sp h.sp]; exact hp.args.rstk hb f

theorem below_R {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b) :
    (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l).Disjoint (below s₀.sp 16) := by
  rw [below16]; exact (hp.args.rstk hb f).symm

theorem kb_below {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) :
    (VG.Proof.MlKem.AArch64.KeyGen.svR P s₀).Disjoint (below s₀.sp 16) ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 0 0 64).Disjoint (below s₀.sp 16) :=
  ⟨VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) hp.sv, VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl)⟩

/-- Regions a callee may write: in `ek`, `dk` or `scratch`. -/
theorem cov_w {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {b o l : Nat} (hb : 1 ≤ b ∧ b < 4)
    (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b) : Covers [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l] s.wr := by
  rw [h.wr, hp.wr]
  refine R.cov ?_ f
  rcases (by omega : b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl <;> simp

theorem cov_r {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {b o l : Nat} (hb : b < 4)
    (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b) : Covers [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  refine R.cov ?_ f
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> simp

theorem hsetup {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {rate : Nat} (hr : rate ∈ Spec.Sha3.rates) :
    HSetup .x28 ST WK rate s := by
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 o l := fun o l => by
    rw [h.x28]
  have f : ∀ {o l : Nat}, o + l ≤ 840 → o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := fun h => by have := hp.wf; simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  refine ⟨by decide, by decide, by decide, hr, ?_, by rw [h.sp]; exact hp.sp16, ?_, ?_, ?_⟩
  · rw [e, e]; exact hp.args.rdisj (by decide) (by decide) (f (by decide)) (f (by decide)) (by decide)
  · rw [e]; exact VG.Proof.MlKem.AArch64.KeyGen.stk_R hp h (by decide) (f (by decide))
  · rw [e]; exact VG.Proof.MlKem.AArch64.KeyGen.stk_R hp h (by decide) (f (by decide))
  · rw [e, e]; exact covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp h (by decide) (f (by decide))) (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp h (by decide) (f (by decide)))

/-- A piece at bytes `[o, o + l)` of argument `b`, apart from the Keccak
state and working space. -/
theorem pieceOk {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {w : Bool} {b o l : Nat} (hb : b < 4)
    (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b) (hs : b ≠ 3 ∨ 840 ≤ o) (hl : l < 65536) (hw : w = true → 1 ≤ b) :
    PieceOk .x28 ST WK s w ⟨VG.Proof.MlKem.AArch64.KeyGen.breg b, o, l⟩ := by
  have eb : preg s ⟨VG.Proof.MlKem.AArch64.KeyGen.breg b, o, l⟩ = VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l := by simp only [preg, h.breg hb]
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 o l := fun o l => by
    rw [h.x28]
  have ho : o < 65536 := by
    have := hp.wf
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlKem.AArch64.KeyGen.kL] at f <;> lom
  refine ⟨?_, ho, hl, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> decide
  · rw [eb, VG.Proof.MlKem.AArch64.STr, e]
    exact hp.args.rdisj hb (by decide) f (by have := hp.wf; simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom) (by simp only [KG.ST]; omega)
  · rw [eb, VG.Proof.MlKem.AArch64.WKr, e]
    exact hp.args.rdisj hb (by decide) f (by have := hp.wf; simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom) (by simp only [KG.WK]; omega)
  · rw [eb]; exact VG.Proof.MlKem.AArch64.KeyGen.stk_R hp h hb f
  · rw [eb]
    cases w
    · exact VG.Proof.MlKem.AArch64.KeyGen.cov_r hp h hb f
    · exact VG.Proof.MlKem.AArch64.KeyGen.cov_w hp h ⟨hw rfl, hb⟩ f

end VG.Proof.MlKem.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KgA`. -/
section

/-!
# ML-KEM on AArch64: `keygen`, the prologue and `G(d ‖ k)`
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `d`, bytes `[0, 32)` of the seed. -/
abbrev dB (s₀ : State) : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 0) 32
/-- `z`, bytes `[32, 64)` of the seed. -/
abbrev zB (s₀ : State) : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 32) 32

theorem KB.d {s₀ s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 0) 32 = VG.Proof.MlKem.AArch64.KeyGen.dB s₀ := by
  rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), h.seed, bytesAt_take _ _ (by decide)]

theorem KB.z {s₀ s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 32) 32 = VG.Proof.MlKem.AArch64.KeyGen.zB s₀ := by
  have e : ∀ m : Mem, bytesAt m (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 32) 32 =
      (bytesAt m (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 + BitVec.ofNat 64 0) 64).drop 32 := fun m => by
    rw [bytesAt_drop _ _ (by decide), ptr_add]
  rw [e, h.seed, ← e]

/-- Stores of the registers `rs` at `B + off + 8k`. -/
theorem saves_ok (B : Addr) (base : Reg) (off : Nat) (rs : List Reg) (hoff : off + 8 * rs.length ≤ 32768)
    (h8 : off % 8 = 0) :
    ∀ n ≤ rs.length, ∀ {s : State}, s.gpr base = B →
      (∀ k < rs.length, InRegions s.wr (B + BitVec.ofNat 64 (off + 8 * k)) 8) →
      WP isa (.block ((List.range n).map fun k => .str .x (rs.getD k .x0) base (off + 8 * k))) s fun s' =>
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        (∀ k < n, s'.mem.readW (B + BitVec.ofNat 64 (off + 8 * k)) 64 = s.gpr (rs.getD k .x0)) ∧
        Frame [⟨B + BitVec.ofNat 64 off, 8 * rs.length⟩] s.mem s'.mem := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | succ n ih =>
    intro hn s hb hin
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega) hb hin) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := B + BitVec.ofNat 64 (off + 8 * n)) (by constructor <;> omega) (by rw [g₁, hb])
      (by rw [w₁]; exact hin n (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      refine f₁.writeW (List.mem_singleton_self _) _ ?_
      rw [show B + BitVec.ofNat 64 (off + 8 * n) = B + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * n) by
        rw [ptr_add]]
      exact contains_off (by omega) (by omega)

theorem prologue_eq : P.kgPrologue =
    (List.range 6).map (fun k => .str .x (own.getD k .x0) .x3 (SV P + 8 * k)) ++
      ([mov .x25 .x0, mov .x26 .x1, mov .x27 .x2, mov .x28 .x3, .movz .x .x24 1 0,
        .movz .x .x9 (BitVec.ofNat 16 P.k) 0, .strb .x9 .x28 BK] : List Instr) := rfl

/-- What the prologue leaves. -/
structure AfterPro (P : KemLay) (s₀ s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s
  x24 : s.gpr .x24 = 1
  bk : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 BK) 1 = [BitVec.ofNat 8 P.k]

theorem pres_pro : ∀ r ∈ preserved, r ∉ VG.Proof.MlKem.AArch64.KeyGen.own → r ∉ [Reg.x25, .x26, .x27, .x28, .x24, .x9] := by decide

theorem prologue_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) : WP isa (.block P.kgPrologue) s₀ (VG.Proof.MlKem.AArch64.KeyGen.AfterPro P s₀) := by
  have hw := hp.wf
  rw [VG.Proof.MlKem.AArch64.KeyGen.prologue_eq, WP.block_append_iff]
  have hin : ∀ k < own.length, InRegions s₀.wr (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 8 := fun k hk => by
    rw [hp.wr]
    exact in_regions (R := ⟨VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3, VG.Proof.MlKem.AArch64.KeyGen.kL P 3⟩) (by simp) (contains_off (by simp at hk; simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom)
      (by have := VG.Proof.MlKem.AArch64.KeyGen.kL_le hw 3; omega))
  have hsv : SV P + 8 * own.length ≤ 32768 := by simp only [VG.Proof.MlKem.AArch64.KeyGen.own, List.length_cons, List.length_nil]; lom
  have h8 : SV P % 8 = 0 := by lom
  refine WP.mono (WP.preservedV (VG.Proof.MlKem.AArch64.KeyGen.saves_ok (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3) .x3 (SV P) VG.Proof.MlKem.AArch64.KeyGen.own hsv h8 6 (by decide) rfl hin)
    (hc := rfl))
    fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, vc₁⟩ => ?_
  refine wp_mov fun s₂ h₂ e₂ => wp_mov fun s₃ h₃ e₃ => wp_mov fun s₄ h₄ e₄ => wp_mov fun s₅ h₅ e₅ =>
    wp_movz fun s₆ h₆ e₆ => wp_movz fun s₇ h₇ e₇ => ?_
  have k₇ := (((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).keep
  have c28 : s₇.gpr .x28 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 := by
    rw [h₇.get .x28, h₆.get .x28, e₅, h₄.get .x3, h₃.get .x3, h₂.get .x3, g₁]; rfl
  refine wp_strb (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 BK) (by decide) (by rw [c28])
    (by rw [k₇.wr, w₁, hp.wr]
        exact in_regions (R := ⟨VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3, VG.Proof.MlKem.AArch64.KeyGen.kL P 3⟩) (by simp) (contains_off (by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom)
          (by have := VG.Proof.MlKem.AArch64.KeyGen.kL_le hw 3; omega)))
    fun s₈ h₈ => wp_nil ?_
  have m₈ : s₈.mem = s₁.mem.writeW (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 BK) ((s₇.gpr .x9).setWidth 8) := by
    rw [h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem]
  have k₈ := k₇.trans h₈.keep
  have hf : Frame [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SV P) 48, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 BK 1] s₀.mem s₈.mem := by
    rw [m₈]
    refine Frame.writeW (r := VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 BK 1) (Frame.mono f₁ fun r hr => ?_)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
  refine ⟨⟨by rw [k₈.rd, r₁], by rw [k₈.wr, w₁], by rw [k₈.sp, p₁], ?_, ?_, ?_, by rw [h₈.gpr]; exact c28,
    fun r hr ho => ?_, ?_, ?_, fun r hr => (k₈.vcs r hr).trans (vc₁ r hr)⟩, ?_, ?_⟩
  · rw [h₈.gpr, h₇.get .x25, h₆.get .x25, h₅.get .x25, h₄.get .x25, h₃.get .x25, e₂, g₁]; rfl
  · rw [h₈.gpr, h₇.get .x26, h₆.get .x26, h₅.get .x26, h₄.get .x26, e₃, h₂.get .x1, g₁]; rfl
  · rw [h₈.gpr, h₇.get .x27, h₆.get .x27, h₅.get .x27, e₄, h₃.get .x2, h₂.get .x2, g₁]; rfl
  · rw [k₈.gpr r (VG.Proof.MlKem.AArch64.KeyGen.pres_pro r hr ho), g₁]
  · intro k hk
    rw [← z₁ k hk, m₈]
    exact Mem.readW_writeW_sep (sep_off _ (by lom) (by lom) (by decide)) (by decide)
  · refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    rcases mem2' hr with rfl | rfl
    · exact hp.args.rdisj (by decide) (by decide) (by kl) hp.sv (.inl (by decide))
    · exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by decide)
  · rw [h₈.gpr, h₇.get .x24, e₆]; rfl
  · rw [m₈]
    refine bytesAt_eq (by rfl) fun i hi => ?_
    have : i = 0 := by omega
    subst this
    rw [ptr_zero, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, e₇]
    exact sfx8 (by lom)

/-! ## Hashes -/

/-- An output of a hash: bytes `[o, o + l)` of `ek`, `dk` or `scratch`, apart
from the saved registers. -/
def OutOk (P : KemLay) (p : Piece) : Prop :=
  ∃ b o l, p = ⟨VG.Proof.MlKem.AArch64.KeyGen.breg b, o, l⟩ ∧ 1 ≤ b ∧ b < 4 ∧ o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b ∧ (b ≠ 3 ∨ SV P + 48 ≤ o ∨ o + l ≤ SV P)

/-- A hash keeps what holds throughout. -/
theorem KB.hash {s₀ s s' : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) (h : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) {outs : List Piece}
    (hk : Kept (STr .x28 ST s :: WKr .x28 WK s :: below s.sp 16 :: outs.map (preg s)) s s')
    (ho : ∀ p ∈ outs, VG.Proof.MlKem.AArch64.KeyGen.OutOk P p) : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' := by
  have hw := hp.wf
  refine h.call hk fun r hr => ?_
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 o l := fun o l => by
    rw [h.x28]
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.STr, e]
    exact ⟨hp.args.rdisj (by decide) (by decide) hp.sv (by kl) (by lom),
      hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by decide)⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.WKr, e]
    exact ⟨hp.args.rdisj (by decide) (by decide) hp.sv (by kl) (by lom),
      hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by decide)⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [h.sp]
    exact VG.Proof.MlKem.AArch64.KeyGen.kb_below hp
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
  obtain ⟨b, o, l, rfl, h1, h4, f, hs⟩ := ho p hp'
  simp only [preg, h.breg h4]
  exact ⟨hp.args.rdisj (by decide) h4 hp.sv f (by omega),
    hp.args.rdisj (by decide) h4 (by kl) f (by omega)⟩

theorem sha3Suffix_eq : Spec.Sha3.sha3Suffix = BitVec.ofNat 8 6 := rfl
theorem shakeSuffix_eq : Spec.Sha3.shakeSuffix = BitVec.ofNat 8 0x1f := rfl

/-- After `G(d ‖ k)`. -/
structure AfterA (P : KemLay) (s₀ s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s
  x24 : s.gpr .x24 = 1
  rho : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB) 32 = KPke.kgRho P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)
  sig : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)

theorem g_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.AfterPro P s₀ s) :
    WP isa (KemLay.kgGWith keccak.callee) s (VG.Proof.MlKem.AArch64.KeyGen.AfterA P s₀) := by
  have hw := hp.wf
  have f : ∀ {o l : Nat}, o + l ≤ 960 → o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := fun h => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  have e : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 o := fun o => by
    rw [h.kb.x28]
  refine WP.mono (hashWith_ok keccak (VG.Proof.MlKem.AArch64.KeyGen.hsetup hp h.kb (by decide : 72 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x25, 0, 32⟩, ⟨.x28, BK, 1⟩]) (outs := [⟨.x28, SB, 32⟩, ⟨.x28, SG, 32⟩]) (by simp)
    (fun p hp' => ?_) (fun p hp' => ?_) ?_) fun s' ⟨k', o'⟩ => ?_
  · rcases mem2' hp' with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 0) hp h.kb (by decide) (by kl) (by decide) (by decide) (by decide)
    · exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 3) hp h.kb (by decide) (f (by decide)) (by decide) (by decide) (by decide)
  · rcases mem2' hp' with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 3) hp h.kb (by decide) (f (by decide)) (by decide) (by decide) (by decide)
    · exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 3) hp h.kb (by decide) (f (by decide)) (by decide) (by decide) (by decide)
  · refine List.pairwise_pair.mpr ?_
    simp only [preg, e]
    exact hp.args.rdisj (by decide) (by decide) (f (by decide)) (f (by decide)) (by decide)
  have kb' := h.kb.hash hp k' fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, SB, 32, rfl, by decide, by decide, f (by decide), .inr (.inr (by lom))⟩
    · exact ⟨3, SG, 32, rfl, by decide, by decide, f (by decide), .inr (.inr (by lom))⟩
  have msg : (List.map (pbytes s) [⟨.x25, 0, 32⟩, ⟨.x28, BK, 1⟩]).flatten =
      VG.Proof.MlKem.AArch64.KeyGen.dB s₀ ++ [BitVec.ofNat 8 P.k] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      h.kb.x25, e]
    rw [show VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0 from rfl, KB.d h.kb, h.bk]
  obtain ⟨o₁, o₂, -⟩ := o'
  rw [msg, e] at o₁ o₂
  have hG := G_eq (VG.Proof.MlKem.AArch64.KeyGen.dB s₀ ++ [BitVec.ofNat 8 P.params.k])
  refine ⟨kb', by rw [k'.cs _ (by decide) (by decide), h.x24], ?_, ?_⟩
  · rw [o₁, KPke.kgRho, hG]; rfl
  · rw [o₂, KPke.kgSigma, hG]; rfl

end VG.Proof.MlKem.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KgB`. -/
section

/-!
# ML-KEM on AArch64: `keygen`, the matrix `Â`

`Â[i, j]` for the `k²` entries `(i, j)` (entry `e = k i + j`), each with `sample_ntt`'s
stronger contract: it is reduced, and the result is 1 exactly when `SampleNTT`
with 280 iterations succeeds; `x24` is the AND of the results.
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `ρ`. -/
abbrev rhoK (P : KemLay) (s₀ : State) : List Byte := KPke.kgRho P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)

/-- Entry `e` of `Â`, at `s`. -/
abbrev aAt (s₀ : State) (m : Mem) (e : Nat) : VG.Spec.MlKem.Poly := polyAt m (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))

/-- Whether the first `n` `SampleNTT`s succeed. -/
def allOk (P : KemLay) (s₀ : State) (n : Nat) : Prop :=
  ∀ e < n, (sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (e / P.k) (e % P.k))).isSome

instance (s₀ : State) (n : Nat) : Decidable (VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ n) := by unfold VG.Proof.MlKem.AArch64.KeyGen.allOk; infer_instance

/-- After `n` entries of `Â`. -/
structure BInv (P : KemLay) (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s
  rho : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB) 32 = VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀
  sig : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)
  acc : s.gpr .x24 = if VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ n then 1 else 0
  red : ∀ e < n, Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))
  res : ∀ e < n, sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (e / P.k) (e % P.k)) = none ∨
    sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (e / P.k) (e % P.k)) = some (VG.Proof.MlKem.AArch64.KeyGen.aAt s₀ s.mem e)

theorem BInv.zero {s₀ s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.AfterA P s₀ s) : VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ 0 s :=
  ⟨h.kb, h.rho, h.sig, by rw [h.x24, ite_eq_left (show VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ 0 from fun e he => absurd he (Nat.not_lt_zero e))],
    fun e he => absurd he (Nat.not_lt_zero e), fun e he => absurd he (Nat.not_lt_zero e)⟩

theorem and_acc {a b : BitVec 64} {p q : Prop} [Decidable p] [Decidable q]
    (ha : a = if p then 1 else 0) (hb : (b = 1 ∧ q) ∨ (b = 0 ∧ ¬ q)) :
    a &&& b = if p ∧ q then 1 else 0 := by
  rcases hb with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · by_cases hp : p
    · rw [ha, ite_eq_left hp, ite_eq_left ⟨hp, hq⟩]; rfl
    · rw [ha, ite_eq_right hp, ite_eq_right (fun h => hp h.1)]; rfl
  · rw [ite_eq_right (fun h => hq h.2)]
    by_cases hp : p
    · rw [ha, ite_eq_left hp]; rfl
    · rw [ha, ite_eq_right hp]; rfl

theorem allOk_succ {s₀ : State} {k : Nat} :
    VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ (k + 1) ↔ VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ k ∧ (sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (k / P.k) (k % P.k))).isSome := by
  constructor
  · intro h; exact ⟨fun e he => h e (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ e he
    rcases (by omega : e < k ∨ e = k) with he | rfl
    · exact h e he
    · exact hk

/-- Before `SampleNTT(ρ ‖ j ‖ i)`: its seed, and its arguments. -/
structure Mid (P : KemLay) (s₀ : State) (i j : Nat) (s : State) : Prop where
  b : VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * i + j) s
  seed : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB) 34 = matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) i j
  x0 : s.gpr .x0 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB
  x1 : s.gpr .x1 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)
  x2 : s.gpr .x2 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SS

theorem setup_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i j : Nat} (hi : i < P.k) (hj : j < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * i + j) s) : WP isa (.block (P.kgSetup i j)) s (VG.Proof.MlKem.AArch64.KeyGen.Mid P s₀ i j) := by
  have hw := hp.wf
  have hij := VG.Proof.MlKem.AArch64.ij_lt hi hj
  have f : ∀ {o l : Nat}, o + l ≤ 4128 → o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := fun h => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  have e : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 o := fun o => by
    rw [h.kb.x28]
  rw [KemLay.kgSetup, List.append_assoc, List.append_assoc]
  have in₁ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SB + 32)) 1 :=
    fun hu => by
      rw [hu]
      exact VG.Proof.MlKem.AArch64.in_R (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp h.kb (b := 3) (o := SB + 32) (l := 2) (by decide) (f (by decide))) (k := 0)
        (by decide) (by decide)
  have in₂ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SB + 33)) 1 :=
    fun hu => by
      rw [hu]
      exact VG.Proof.MlKem.AArch64.in_R (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp h.kb (b := 3) (o := SB + 32) (l := 2) (by decide) (f (by decide))) (k := 1)
        (by decide) (by decide)
  refine wp_movz fun s₁ h₁ e₁ => wp_strb (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SB + 32)) (by decide)
    (by rw [h₁.get .x28, e]) (in₁ h₁.wr) fun s₂ h₂ => ?_
  refine wp_movz fun s₃ h₃ e₃ => wp_strb (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SB + 33)) (by decide)
    (by rw [h₃.get .x28, h₂.gpr, h₁.get .x28, e]) (in₂ (by rw [h₃.wr, h₂.wr, h₁.wr])) fun s₄ h₄ => ?_
  refine wp_ptrTo (by decide) (by decide) fun s₅ h₅ e₅ => wp_ptrTo (by decide)
    (by lom) fun s₆ h₆ e₆ => wp_ptrTo' (by decide) (by decide)
    fun s₇ h₇ e₇ => ?_
  have g28 : s₄.gpr .x28 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 := by rw [h₄.gpr, h₃.get .x28, h₂.gpr, h₁.get .x28, h.kb.x28]
  have k₇ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep).trans
    h₇.keep
  have m₇ : s₇.mem = (s.mem.writeW (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SB + 32)) ((s₁.gpr .x9).setWidth 8)).writeW
      (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SB + 33)) ((s₃.gpr .x9).setWidth 8) := by
    rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have f₇ : Frame [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SB + 32) 2] s.mem s₇.mem := by
    rw [m₇]
    have hm : VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SB + 32) 2 ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SB + 32) 2] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (R.contains (k := 0) (by decide) (by decide))).writeW hm _
      (R.contains (k := 1) (by decide) (by decide))
  have kb₇ : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s₇ := h.kb.frame k₇ f₇ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) (f (by decide)) (.inr (.inr (by lom))) (by decide)
  have sd : ∀ o, o < 32 → s₇.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB + BitVec.ofNat 64 o) =
      s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB + BitVec.ofNat 64 o) := fun o ho => by
    rw [ptr_add]
    exact f₇ _ fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact hp.args.rdisj (b₁ := 3) (o₁ := SB + o) (l₁ := 1) (by decide) (by decide)
        (by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom) (f (by decide)) (by simp only [SB]; omega) _
        (Region.contains_self _ _) hc
  have ae : ∀ {e : Nat}, e < P.k * i + j →
      ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SB + 32) 2], (polyRegion (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))).Disjoint r :=
    fun he r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom) (f (by decide))
        (by simp only [AH, SB]; omega)
  refine ⟨⟨kb₇, by rw [bytesAt_congr sd]; exact h.rho, ?_, by rw [k₇.get .x24]; exact h.acc,
    fun e he => reduced_frame f₇ (ae he) (h.red e he), fun e he => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [bytesAt_frame f₇ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (f (by decide)) (f (by decide)) (by decide)) (by decide)]
    exact h.sig
  · rw [VG.Proof.MlKem.AArch64.KeyGen.aAt, polyAt_frame f₇ (ae he)]; exact h.res e he
  · refine seed_eq (by rw [bytesAt_congr sd]; exact h.rho) ?_ ?_
    · rw [m₇, ptr_add, VG.WriteBytes.writeW8_apply, ite_eq_right (addr_ne _ (by decide) (by decide) (by decide)),
        VG.WriteBytes.writeW8_apply, ite_eq_left rfl, e₁]
      exact sfx8 (by lom)
    · rw [m₇, ptr_add, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, e₃]
      exact sfx8 (by lom)
  · rw [h₇.get .x0, h₆.get .x0, e₅, g28]
  · rw [h₇.get .x1, e₆, h₅.get .x28, g28]
  · rw [e₇, h₆.get .x28, h₅.get .x28, g28]

/-- The arguments of `SampleNTT` for `Â[i, j]`. -/
theorem Mid.args {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i j : Nat} (hi : i < P.k) (hj : j < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.Mid P s₀ i j s) : VG.Proof.MlKem.AArch64.SampleArgs s (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB) (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (aOff P i j))
      (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SS) := by
  have hw := hp.wf
  have hij := VG.Proof.MlKem.AArch64.ij_lt hi hj
  have kb := h.b.kb
  have f : ∀ {o l : Nat}, o + l ≤ 4128 → o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := fun h => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  have fa : aOff P i j + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  exact ⟨h.x0, h.x1, h.x2,
    hp.args.rdisj (by decide) (by decide) (f (by decide)) fa (by lom),
    hp.args.rdisj (by decide) (by decide) (f (by decide)) (f (by decide)) (by decide),
    hp.args.rdisj (by decide) (by decide) fa (f (by decide)) (by lom),
    by rw [kb.sp]; exact hp.sp16, VG.Proof.MlKem.AArch64.KeyGen.stk_R hp kb (by decide) (f (by decide)), VG.Proof.MlKem.AArch64.KeyGen.stk_R hp kb (by decide) fa,
    VG.Proof.MlKem.AArch64.KeyGen.stk_R hp kb (by decide) (f (by decide)),
    covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb (by decide) (f (by decide))) (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb (by decide) fa)
      (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb (by decide) (f (by decide)))),
    covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb (by decide) fa) (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb (by decide) (f (by decide)))⟩

theorem call_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i j : Nat} (hi : i < P.k) (hj : j < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.Mid P s₀ i j s) : WP isa (kgCallWith keccak.callee) s (VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * i + j + 1)) := by
  have hw := hp.wf
  have hij := VG.Proof.MlKem.AArch64.ij_lt hi hj
  have kb := h.b.kb
  have f : ∀ {o l : Nat}, o + l ≤ 4128 → o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := fun h => by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  have fa : aOff P i j + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom
  have A := h.args hp hi hj
  refine WP.seq <| sample_callWith keccak A.h0 A.h1 A.h2 A.d₁ A.d₂ A.d₃ A.hsp A.k₁ A.k₂ A.k₃ A.hc A.hw
    fun s₈ k₈ r₈ o₈ => ?_
  rw [kb.sp] at k₈
  have kb₈ : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s₈ := kb.call k₈ fun r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    · exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) fa (.inr (.inr (by lom))) (by decide)
    · exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) (f (by decide)) (.inr (.inr (by lom))) (by decide)
    · exact VG.Proof.MlKem.AArch64.KeyGen.kb_below hp
  refine wp_and fun s₉ h₉ e₉ => wp_nil ?_
  have kb₉ := kb₈.block h₉.keep h₉.mem (by decide)
  have fr : Frame [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (aOff P i j) 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SS 2048, below s₀.sp 16] s.mem s₉.mem := by
    rw [h₉.mem]; exact k₈.frame
  have far : ∀ {o l : Nat}, o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 → (o + l ≤ aOff P i j ∨ aOff P i j + 1024 ≤ o) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) →
      ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (aOff P i j) 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SS 2048, below s₀.sp 16],
        (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 o l).Disjoint r := fun fo h2 h3 r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    · exact hp.args.rdisj (by decide) (by decide) fo fa (by omega)
    · exact hp.args.rdisj (by decide) (by decide) fo (f (by decide)) (by omega)
    · exact VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) fo
  have hke := VG.Proof.MlKem.AArch64.ij_div (i := i) hj
  have ae : ∀ {e : Nat}, e < P.k * i + j →
      ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (aOff P i j) 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SS 2048, below s₀.sp 16],
        (polyRegion (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))).Disjoint r :=
    fun he => far (by simp only [VG.Proof.MlKem.AArch64.KeyGen.kL]; lom) (by lom) (by lom)
  rw [h.seed] at o₈
  have x0v : (s₈.gpr .x0 = 1 ∧ (sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) i j)).isSome) ∨
      (s₈.gpr .x0 = 0 ∧ ¬ (sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) i j)).isSome) := by
    rcases o₈ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2]; rfl⟩
    · exact .inr ⟨h1, by rw [h2]; simp⟩
  have g24 : s₈.gpr .x24 = s.gpr .x24 := k₈.cs _ (by decide) (by decide)
  have acc : s₉.gpr .x24 = if VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ (P.k * i + j) ∧ (sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) i j)).isSome
      then 1 else 0 := by
    rw [e₉, g24, VG.Proof.MlKem.AArch64.KeyGen.and_acc h.b.acc x0v]
  refine ⟨kb₉, ?_, ?_, ?_, fun e he => ?_, fun e he => ?_⟩
  · rw [bytesAt_frame fr (far (f (by decide)) (.inl (by lom)) (by decide)) (by decide)]
    exact h.b.rho
  · rw [bytesAt_frame fr (far (f (by decide)) (.inl (by lom)) (by decide)) (by decide)]
    exact h.b.sig
  · rw [acc]
    by_cases hA : VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ (P.k * i + j + 1)
    · have hA' := allOk_succ.mp hA
      rw [hke.1, hke.2] at hA'
      rw [ite_eq_left hA', ite_eq_left hA]
    · have hA' : ¬ (VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ (P.k * i + j) ∧ (sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) i j)).isSome) := fun h' =>
        hA (allOk_succ.mpr (by rw [hke.1, hke.2]; exact h'))
      rw [ite_eq_right hA', ite_eq_right hA]
  · rcases (by omega : e < P.k * i + j ∨ e = P.k * i + j) with he | rfl
    · exact reduced_frame fr (ae he) (h.b.red e he)
    · rw [h₉.mem]; simpa only [aOff] using r₈
  · rcases (by omega : e < P.k * i + j ∨ e = P.k * i + j) with he | rfl
    · rw [VG.Proof.MlKem.AArch64.KeyGen.aAt, polyAt_frame fr (ae he)]; exact h.b.res e he
    · rw [hke.1, hke.2, VG.Proof.MlKem.AArch64.KeyGen.aAt, h₉.mem]
      rcases o₈ with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact .inr (by simpa only [aOff] using h2)
      · exact .inl h2

theorem sample_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i j : Nat} (hi : i < P.k) (hj : j < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * i + j) s) :
    WP isa (P.kgSampleWith keccak.callee i j) s (VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * i + j + 1)) :=
  WP.seq (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.setup_ok hp hi hj h) fun _ m => VG.Proof.MlKem.AArch64.KeyGen.call_ok hp hi hj m)

theorem b_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.AfterA P s₀ s) :
    WP isa (P.kgBWith keccak.callee) s (VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * P.k)) :=
  WPs.seqs (VG.Proof.MlKem.AArch64.matrix_ne_nil hp.wf.facts.1)
    (WPs.matrix (fun _ hi _ hj _ h => VG.Proof.MlKem.AArch64.KeyGen.sample_step hp hi hj h) (Nat.le_refl _) (BInv.zero h))

end VG.Proof.MlKem.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KgC`. -/
section

/-!
# ML-KEM on AArch64: `keygen`, the calls of phase C

Each building block of the computation of `ŝ`, `ê` and `t̂` (`(kgCbdNttWith
keccak.callee)`, `kgEnc`, `kgMul`, `kgAdd`): what it needs, what it computes,
what it keeps (`KB`), and the only memory it changes (`Frame`), so that the
facts established before it survive it.
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- Two buffers are apart: in different arguments, or at offsets apart. -/
macro "rdisj" : tactic => `(tactic|
  exact (‹Pre _ _›).args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))

/-- A polynomial buffer in `scratch` for phase C: past `Â`'s start, below
the saved registers. -/
def PolyOff (P : KemLay) (off : Nat) : Prop := AH ≤ off ∧ off + 1024 ≤ SV P

/-- What `(kgCbdNttWith keccak.callee)` writes. -/
abbrev cnW (s₀ : State) (off : Nat) : List Region :=
  [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 ST 200, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 WK 640, below s₀.sp 16, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SG + 32) 1, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 PB 128,
    VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 off 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 NS 1024]

/-- `SamplePolyCBD₂(PRF₂(σ, N))`. -/
theorem cbdNtt_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {N off : Nat} (hN : N < 256) (ho : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P off) {s : State}
    (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) (hs : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) :
    WP isa (KemLay.kgCbdNttWith keccak.callee N off) s fun s' => VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' ∧ Frame (VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ off) s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 off) (ntt (cbd (KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) N)) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have e : ∀ {u : State}, VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ u → ∀ o, u.gpr .x28 + BitVec.ofNat 64 o = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 o :=
    fun hu o => by rw [hu.x28]
  obtain ⟨ho1, ho2⟩ := ho
  have fo : off + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  -- `N` after `σ`
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_strb (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SG + 32)) (by decide)
    (by rw [h₁.get .x28, e hk]) (by
      rw [h₁.wr]; exact VG.Proof.MlKem.AArch64.in_R (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp hk (b := 3) (o := SG + 32) (l := 1) (by decide) (by kl))
        (k := 0) (by decide) (by decide)) fun s₂ h₂ => wp_nil ?_)
  have m₂ : s₂.mem = s.mem.writeW (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SG + 32)) ((s₁.gpr .x9).setWidth 8) := by
    rw [h₂.mem, h₁.mem]
  have f₂ : Frame [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SG + 32) 1] s.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (R.contains (k := 0) (by decide)
      (by decide))
  have kb₂ : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s₂ := hk.frame (h₁.keep.trans h₂.keep) f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) (by kl) (by kl) (by decide)
  have msg : bytesAt s₂.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SG) 33 =
      KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++ [BitVec.ofNat 8 N] := by
    rw [show 33 = 32 + 1 from rfl, bytesAt_add, bytesAt_frame (p := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SG) (len := 32)
      f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        show (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SG 32).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (SG + 32) 1)
        rdisj) (by decide), hs]
    refine congrArg (KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++ ·) (bytesAt_eq rfl fun k hk' => ?_)
    have : k = 0 := by omega
    subst this
    rw [ptr_zero, ptr_add, m₂, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, e₁]
    exact sfx8 hN
  -- `PRF₂(σ, N)`
  refine WP.seq (WP.mono (hashWith_ok keccak (VG.Proof.MlKem.AArch64.KeyGen.hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 0x1f)
    (by decide) (ins := [⟨.x28, SG, 33⟩]) (outs := [⟨.x28, PB, 128⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 3) hp kb₂ (by decide) (by kl) (by decide) (by decide) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 3) hp kb₂ (by decide) (by kl) (by decide) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s₃ := kb₂.hash hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']; exact ⟨3, PB, 128, rfl, by decide, by decide, by kl, by kl⟩
  have prf₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 PB) 128 =
      prf 2 (KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) (BitVec.ofNat 8 N) := by
    obtain ⟨o, -⟩ := o₃
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e kb₂] at o
    rw [msg] at o
    rw [o, prf_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  -- `SamplePolyCBD₂`
  refine WP.seq (WP.seq (wp_ptrTo (by decide) (by decide) fun s₄ h₄ e₄ => wp_ptrTo' (by decide)
    (by kl) fun s₅ h₅ e₅ => ?_))
  have kb₅ := kb₃.block (h₄.trans h₅).keep (by rw [h₅.mem, h₄.mem]) (by decide)
  refine VG.Proof.MlKem.AArch64.cbd2_call (b := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 PB) (f := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 off)
    (by rw [h₅.get .x0, e₄, e kb₃]) (by rw [e₅, h₄.get .x28, e kb₃])
    (by show (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 PB 128).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 off 1024); rdisj)
    (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₅ (b := 3) (o := PB) (l := 128) (by decide) (by kl))
      (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₅ (b := 3) (by decide) fo))
    (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₅ (b := 3) (by decide) fo) fun s₆ k₆ p₆ => ?_
  have kb₆ := kb₅.call k₆ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) fo (by kl) (by decide)
  rw [show s₅.mem = s₃.mem by rw [h₅.mem, h₄.mem], prf₃] at p₆
  -- the NTT
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₇ h₇ e₇ => wp_ptrTo'
    (by decide) (by decide) fun s₈ h₈ e₈ => ?_)
  have kb₈ := kb₆.block (h₇.trans h₈).keep (by rw [h₈.mem, h₇.mem]) (by decide)
  refine VG.Proof.MlKem.AArch64.ntt_call (f := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 off) (w := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 NS)
    (by rw [h₈.get .x0, e₇, e kb₆]) (by rw [e₈, h₇.get .x28, e kb₆])
    (by show (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 off 1024).Disjoint (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 NS 1024); rdisj)
    (by rw [h₈.mem, h₇.mem]; exact p₆.1)
    (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₈ (b := 3) (by decide) fo) (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₈ (b := 3) (o := NS) (l := 1024)
      (by decide) (by kl))) fun s₉ k₉ p₉ => ?_
  have kb₉ := kb₈.call k₉ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) fo (by kl) (by decide)
    · exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) (by kl) (by kl) (by decide)
  have m₈ : s₈.mem = s₆.mem := by rw [h₈.mem, h₇.mem]
  have m₅ : s₅.mem = s₃.mem := by rw [h₅.mem, h₄.mem]
  have F₁ : Frame (VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ off) s.mem s₂.mem := f₂.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  have F₂ : Frame (VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ off) s₂.mem s₃.mem := k₃'.frame.mono fun r hr => by
    rcases mem4 hr with rfl | rfl | rfl | rfl <;> simp
  have F₃ : Frame (VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ off) s₅.mem s₆.mem := k₆.frame.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  have F₄ : Frame (VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ off) s₈.mem s₉.mem := k₉.frame.mono fun r hr => by
    rcases mem2' hr with rfl | rfl <;> simp
  rw [m₅] at F₃
  rw [m₈] at F₄
  have pv : polyAt s₈.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 off) = cbd (KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) N := by
    rw [m₈]; exact p₆.2
  rw [pv] at p₉
  refine ⟨kb₉, F₁.trans (F₂.trans (F₃.trans F₄)), p₉, ?_⟩
  rw [k₉.cs _ (by decide) (by decide), h₈.get .x24, h₇.get .x24, k₆.cs _ (by decide) (by decide),
    h₅.get .x24, h₄.get .x24, k₃.cs _ (by decide) (by decide), h₂.gpr, h₁.get .x24]

/-- `ByteEncode₁₂` of the polynomial at `off` into bytes `[o, o + 384)` of `ek`
(`b = 1`) or `dk` (`b = 2`). -/
theorem enc_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {off b o : Nat} (ho : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P off) (hb : b = 1 ∨ b = 2)
    (fo : o + 384 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b) {s : State} (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s) (hr : Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 off)) :
    WP isa (kgEnc off (VG.Proof.MlKem.AArch64.KeyGen.breg b) o) s fun s' => VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' ∧ Frame [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o 384] s.mem s'.mem ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ b + BitVec.ofNat 64 o) 384 = encode12 (polyAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 off)) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨ho1, ho2⟩ := ho
  have hb4 : b < 4 := by omega
  have fo3 : off + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  have hol : o < 65536 := by have := VG.Proof.MlKem.AArch64.KeyGen.kL_le hp.wf b; omega
  have hx : Reg.x1 ≠ VG.Proof.MlKem.AArch64.KeyGen.breg b := by rcases hb with rfl | rfl <;> decide
  have hx0 : VG.Proof.MlKem.AArch64.KeyGen.breg b ≠ Reg.x0 := by rcases hb with rfl | rfl <;> decide
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo' hx hol fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine VG.Proof.MlKem.AArch64.encode12_call (f := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 off) (o := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ b + BitVec.ofNat 64 o)
    (by rw [h₂.get .x0, e₁, hk.x28]) (by rw [e₂, h₁.get (VG.Proof.MlKem.AArch64.KeyGen.breg b) (by simpa using hx0), hk.breg hb4])
    (hp.args.rdisj (b₁ := 3) (o₁ := off) (l₁ := 1024) (by decide) hb4 fo3 fo (by omega))
    (by rw [m₂]; exact hr)
    (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₂ (b := 3) (by decide) fo3) (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₂ hb4 fo)) (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₂ ⟨by omega, hb4⟩ fo)
    fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp hb4 fo (.inl (by omega)) (by omega), by rw [← m₂]; exact k₃.frame,
    by rw [p₃, m₂], by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

/-- `h ← f ×_T g`, for polynomials in `scratch`. -/
theorem mul_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {h f g : Nat} (hh : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P h) (hf : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P f) (hg : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P g)
    (d₁ : h + 1024 ≤ f ∨ f + 1024 ≤ h) (d₂ : h + 1024 ≤ g ∨ g + 1024 ≤ h) {s : State} (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s)
    (rf : Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 f)) (rg : Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 g)) :
    WP isa (kgMul h f g) s fun s' => VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' ∧ Frame [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 h 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 h)
        (multiplyNTTs (polyAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 f)) (polyAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨hh1, hh2⟩ := hh
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  have fh : h + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  have ff : f + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  have fg : g + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  rw [kgMul, List.append_assoc, List.append_assoc]
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo (by decide) (by kl)
    fun s₂ h₂ e₂ => wp_ptrTo (by decide) (by kl) fun s₃ h₃ e₃ => wp_ptrTo' (by decide) (by decide)
    fun s₄ h₄ e₄ => ?_)
  have kb₄ := hk.block (((h₁.trans h₂).trans h₃).trans h₄).keep (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem])
    (by decide)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have c28 : ∀ {u : State}, Only [.x0] s u ∨ Only [.x1] s u ∨ True → True := fun _ => trivial
  refine VG.Proof.MlKem.AArch64.mul_call (h := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 h) (f := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 f)
    (g := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 g) (w := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 NS)
    (by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, hk.x28])
    (by rw [h₄.get .x1, h₃.get .x1, e₂, h₁.get .x28, hk.x28])
    (by rw [h₄.get .x2, e₃, h₂.get .x28, h₁.get .x28, hk.x28])
    (by rw [e₄, h₃.get .x28, h₂.get .x28, h₁.get .x28, hk.x28])
    (hp.args.rdisj (by decide) (by decide) fh ff (by omega))
    (hp.args.rdisj (by decide) (by decide) fh fg (by omega))
    (hp.args.rdisj (by decide) (by decide) fh (by kl) (by kl))
    (hp.args.rdisj (by decide) (by decide) ff (by kl) (by kl))
    (hp.args.rdisj (by decide) (by decide) fg (by kl) (by kl))
    (by rw [m₄]; exact rf) (by rw [m₄]; exact rg)
    (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₄ (b := 3) (by decide) ff) (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₄ (b := 3) (by decide) fg)
      (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₄ (b := 3) (by decide) fh) (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₄ (b := 3) (o := NS) (l := 1024)
        (by decide) (by kl)))))
    (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₄ (b := 3) (by decide) fh) (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₄ (b := 3) (o := NS) (l := 1024)
      (by decide) (by kl)))
    fun s₅ k₅ p₅ => ?_
  refine ⟨kb₄.call k₅ fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) fh (by kl) (by decide)
      · exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) (by kl) (by kl) (by decide),
    by rw [← m₄]; exact k₅.frame, by rw [← m₄]; exact p₅,
    by rw [k₅.cs _ (by decide) (by decide), h₄.get .x24, h₃.get .x24, h₂.get .x24, h₁.get .x24]⟩

/-- `f ← f + g`, for polynomials in `scratch`. -/
theorem add_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {f g : Nat} (hf : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P f) (hg : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s)
    (rf : Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 f)) (rg : Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 g)) :
    WP isa (addAt f g) s fun s' => VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' ∧ Frame [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 f)
        (add (polyAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 f)) (polyAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  have ff : f + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  have fg : g + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kl)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine VG.Proof.MlKem.AArch64.add_call (f := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 f) (g := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 g)
    (by rw [h₂.get .x0, e₁, hk.x28]) (by rw [e₂, h₁.get .x28, hk.x28])
    (hp.args.rdisj (by decide) (by decide) ff fg (by omega)) (by rw [m₂]; exact rf) (by rw [m₂]; exact rg)
    (covers_cons (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₂ (b := 3) (by decide) fg) (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₂ (b := 3) (by decide) ff))
    (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₂ (b := 3) (by decide) ff) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (by decide) ff (by kl) (by decide),
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KgC2`. -/
section

/-!
# ML-KEM on AArch64: `keygen`, `ŝ` and `t̂`

`ŝ[j]` and its encoding into `dk` (`s_step`), then `ê[i]` and `t̂[i]` and its
encodings into `ek` and `dk` (`t_step`), each keeping what the steps before
established (`CInv`).
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `Â[e]`'s buffer. -/
abbrev AR (s₀ : State) (e : Nat) : Addr := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e)

/-- What phase C keeps: `ρ`, `σ`, `x24`, and `Â` as the matrix left it
(in `mB`). -/
structure CInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s
  rho : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SB) 32 = VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀
  sig : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)
  x24 : s.gpr .x24 = v
  ahat : ∀ e < P.k * P.k, Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.AR s₀ e) ∧ polyAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.AR s₀ e) = polyAt mB (VG.Proof.MlKem.AArch64.KeyGen.AR s₀ e)

/-- Memory changed only in `W`, which is apart from `ρ`, `σ` and `Â`. -/
theorem CInv.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {s s' : State} (h : VG.Proof.MlKem.AArch64.KeyGen.CInv P s₀ mB v s)
    (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SB 32).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SG 32).Disjoint r ∧
      (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) : VG.Proof.MlKem.AArch64.KeyGen.CInv P s₀ mB v s' := by
  have ha : ∀ e < P.k * P.k, ∀ r ∈ W, (polyRegion (VG.Proof.MlKem.AArch64.KeyGen.AR s₀ e)).Disjoint r := fun e he r hr =>
    (hW r hr).2.2.sub_left (by
      rw [show VG.Proof.MlKem.AArch64.KeyGen.AR s₀ e = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 AH + BitVec.ofNat 64 (1024 * e) by rw [ptr_add]]
      exact VG.Proof.MlKem.AArch64.sub_offset' (by omega))
  refine ⟨hk, ?_, ?_, by rw [hx, h.x24], fun e he => ⟨reduced_frame hf (ha e he) (h.ahat e he).1, ?_⟩⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.rho
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.sig
  · rw [polyAt_frame hf (ha e he)]; exact (h.ahat e he).2

/-- A buffer apart from everything `(kgCbdNttWith keccak.callee)` writes. -/
theorem cnW_apart {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {off b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b)
    (h : b ≠ 3 ∨ (840 ≤ o ∧ (o + l ≤ 912 ∨ 913 ≤ o) ∧ (o + l ≤ 928 ∨ 1056 ≤ o) ∧
      (o + l ≤ off ∨ off + 1024 ≤ o) ∧ (o + l ≤ 3104 ∨ 4128 ≤ o))) (ho : off + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3) :
    ∀ r ∈ VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ off, (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l).Disjoint r := by
  intro r hr
  rcases mem7 hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.ST]; omega
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.WK]; omega
  · exact VG.Proof.MlKem.AArch64.KeyGen.below_R hp hb f
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.SG]; omega
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.PB]; omega
  · refine hp.args.rdisj hb (by decide) f ho ?_; omega
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.NS]; omega

/-- `ρ`, `σ` and `Â` are apart from what `(kgCbdNttWith keccak.callee)` writes, for a polynomial past `Â`. -/
theorem cnW_far {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {off : Nat} (ho : SH P ≤ off ∧ off + 1024 ≤ SV P) :
    ∀ r ∈ VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ off, (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SB 32).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SG 32).Disjoint r ∧
      (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r := by
  obtain ⟨ho1, ho2⟩ := ho
  have hoL : off + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  intro r hr
  exact ⟨VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) (by kl) (.inr (by kl)) hoL r hr,
    VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) (by kl) (.inr (by kl)) hoL r hr,
    VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) (by kl) (.inr (by kl)) hoL r hr⟩

/-- A single buffer of `ek`, `dk` or past `Â` in `scratch` is apart from `ρ`, `σ` and `Â`. -/
theorem one_far {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b)
    (h : b ≠ 3 ∨ SH P ≤ o) :
    ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l], (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SB 32).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SG 32).Disjoint r ∧
      (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨hp.args.rdisj (by decide) hb (by kl) f (by kl),
    hp.args.rdisj (by decide) hb (by kl) f (by kl),
    hp.args.rdisj (by decide) hb (by kl) f (by kl)⟩

/-- After `ŝ[j']` for `j' < j`. -/
structure SInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (j : Nat) (s : State) : Prop where
  c : VG.Proof.MlKem.AArch64.KeyGen.CInv P s₀ mB v s
  sp : ∀ j' < j, PolyIs s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (sOff P j')) (KPke.kgS P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) j')
  dk : ∀ j' < j, bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2 + BitVec.ofNat 64 (384 * j')) 384 =
    encode12 (KPke.kgS P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) j')

theorem s_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {j : Nat} (hj : j < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.SInv P s₀ mB v j s) : WP isa (P.kgSWith keccak.callee j) s (VG.Proof.MlKem.AArch64.KeyGen.SInv P s₀ mB v (j + 1)) := by
  have hj' : SH P + 1024 * j + 1024 ≤ SV P := by kl
  have hpo : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P (sOff P j) := ⟨by kl, hj'⟩
  have hoL : sOff P j + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  have fd : 384 * j + 384 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 2 := by kl
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.cbdNtt_ok hp (N := j) (off := sOff P j) (by kl) hpo h.c.kb h.c.sig)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.AArch64.KeyGen.enc_ok hp (off := sOff P j) (b := 2) (o := 384 * j) hpo (.inr rfl) fd kb₁ p₁.1)
    fun s₂ ⟨kb₂, f₂, b₂, x₂⟩ => ?_
  have c₂ := (h.c.frame kb₁ x₁ f₁ (VG.Proof.MlKem.AArch64.KeyGen.cnW_far hp ⟨by kl, hj'⟩)).frame kb₂ x₂ f₂
    (VG.Proof.MlKem.AArch64.KeyGen.one_far hp (by decide) fd (.inl (by decide)))
  refine ⟨c₂, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · have hS : ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 2 (384 * j) 384], (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (sOff P j') 1024).Disjoint r := fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inl (by decide))
    rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
    · refine polyIs_frame f₂ hS (polyIs_frame f₁ (VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide)
        (by kl) (.inr (by kl)) hoL)
        (h.sp j' hj'))
    · exact polyIs_frame f₂ hS p₁
  · rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
    · rw [bytesAt_frame f₂ (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact hp.args.rdisj (by decide) (by decide) (by kl) fd (by omega))
          (by decide),
        bytesAt_frame f₁ (VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) (by kl) (.inl (by decide)) hoL)
          (by decide)]
      exact h.dk j' hj'
    · rw [b₂, p₁.2, KPke.kgS]

end VG.Proof.MlKem.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KgT`. -/
section

/-!
# ML-KEM on AArch64: `keygen`, `t̂`

`ê[i]`, `t̂[i]` and its encodings (`t_step`), keeping the facts established
before (`TL`), which every buffer the step writes is apart from (`Apart`).
The sum of products in `t̂[i]` is a loop over `j < k` (`WPs.dot`).
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `Â[i, j]` as the matrix left it. -/
abbrev aM (P : KemLay) (s₀ : State) (mB : Mem) (i j : Nat) : VG.Spec.MlKem.Poly := polyAt mB (VG.Proof.MlKem.AArch64.KeyGen.AR s₀ (P.k * i + j))

/-- `t̂[i]`. -/
abbrev tV (P : KemLay) (s₀ : State) (mB : Mem) (i : Nat) : VG.Spec.MlKem.Poly := KPke.kgT P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) i

/-- After `t̂[i']` for `i' < i`. -/
structure TL (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop where
  c : VG.Proof.MlKem.AArch64.KeyGen.CInv P s₀ mB v s
  sp : ∀ j < P.k, PolyIs s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) j)
  dk : ∀ j < P.k, bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) j)
  ek : ∀ i' < i, bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (VG.Proof.MlKem.AArch64.KeyGen.tV P s₀ mB i') ∧
    bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (VG.Proof.MlKem.AArch64.KeyGen.tV P s₀ mB i')

/-- A region apart from what `TL i` describes. -/
def Apart (P : KemLay) (s₀ : State) (i : Nat) (r : Region) : Prop :=
  (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SB 32).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 SG 32).Disjoint r ∧
    (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 AH (1024 * (P.k * P.k) + 1024 * P.k)).Disjoint r ∧
    (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 1 0 (384 * i)).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 2 0 (384 * P.k + 384 * i)).Disjoint r

theorem TL.frame {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat} {s s' : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v i s) (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i r) : VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v i s' := by
  have hw := hp.wf
  refine ⟨h.c.frame hk hx hf fun r hr => ⟨(hW r hr).1, (hW r hr).2.1,
    (hW r hr).2.2.1.sub_left (R.sub2 (Nat.le_refl _) (by omega))⟩, fun j hj => ?_, fun j hj => ?_,
    fun i' hi' => ⟨?_, ?_⟩⟩
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))) (h.sp j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega)
      (by have := VG.Proof.MlKem.AArch64.mul_succ_le (a := 384) hj; omega))) (by decide)]
    exact h.dk j hj
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left (R.sub2 (by omega)
      (by have := VG.Proof.MlKem.AArch64.mul_succ_le (a := 384) hi'; omega))) (by decide)]
    exact (h.ek i' hi').1
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega)
      (by have := VG.Proof.MlKem.AArch64.mul_succ_le (a := 384) hi'; omega))) (by decide)]
    exact (h.ek i' hi').2

/-- A buffer of `scratch` past `ŝ`, or the NTT's working space. -/
theorem apart_scr {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i o l : Nat} (hi : i < P.k) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3)
    (h : EP P ≤ o ∨ (o = 3104 ∧ l = 1024)) : VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 o l) := by
  have hi' : 0 + 384 * i ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) hi' f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) hi'' f (.inl (by decide))⟩

theorem apart_cnW {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i : Nat} (hi : i < P.k) :
    ∀ r ∈ VG.Proof.MlKem.AArch64.KeyGen.cnW s₀ (EP P), VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i r := by
  have hi' : 0 + 384 * i ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 2 := by kl
  have ho : EP P + 1024 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 3 := by kl
  intro r hr
  exact ⟨VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) hi' (.inl (by decide)) ho r hr,
    VG.Proof.MlKem.AArch64.KeyGen.cnW_apart hp (by decide) hi'' (.inl (by decide)) ho r hr⟩

theorem apart_ek {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i : Nat} (hi : i < P.k) :
    VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 1 (384 * i) 384) := by
  have f : 384 * i + 384 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 1 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega))),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide))⟩

theorem apart_dk {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i : Nat} (hi : i < P.k) :
    VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 2 (384 * P.k + 384 * i) 384) := by
  have f : 384 * P.k + 384 * i + 384 ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega)))⟩

theorem po_a (hP : P.Wf) {i j : Nat} (hi : i < P.k) (hj : j < P.k) : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P (aOff P i j) :=
  have := VG.Proof.MlKem.AArch64.ij_lt hi hj; ⟨by lom, by lom⟩
theorem po_s (hP : P.Wf) {j : Nat} (hj : j < P.k) : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P (sOff P j) := ⟨by lom, by lom⟩
theorem po_TP (hP : P.Wf) : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P (TP P) := ⟨by lom, by lom⟩
theorem po_PP (hP : P.Wf) : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P (PP P) := ⟨by lom, by lom⟩
theorem po_EP (hP : P.Wf) : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P (EP P) := ⟨by lom, by lom⟩

/-- `ê[i]`'s polynomial and `t̂[i]`'s are apart from what a product into `PP` writes. -/
theorem far_PP {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {o : Nat} (ho : o = EP P ∨ o = TP P) :
    ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (PP P) 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 NS 1024],
      (polyRegion (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 o)).Disjoint r := by
  intro r hr
  rcases ho with rfl | rfl <;> rcases mem2' hr with rfl | rfl <;> rdisj

theorem far_TP {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) :
    ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (TP P) 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 NS 1024],
      (polyRegion (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (EP P))).Disjoint r := by
  intro r hr
  rcases mem2' hr with rfl | rfl <;> rdisj

theorem apart_mul {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i o : Nat} (hi : i < P.k) (ho : o = TP P ∨ o = PP P) :
    ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 o 1024, VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 NS 1024], VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · rcases ho with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.KeyGen.apart_scr hp hi (by kl) (.inl (by kl))
    · exact VG.Proof.MlKem.AArch64.KeyGen.apart_scr hp hi (by kl) (.inl (by kl))
  · exact VG.Proof.MlKem.AArch64.KeyGen.apart_scr hp hi (by kl) (.inr ⟨rfl, rfl⟩)

theorem apart_TP {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i : Nat} (hi : i < P.k) :
    ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 3 (TP P) 1024], VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.KeyGen.apart_scr hp hi (by kl) (.inl (by kl))

/-- During `t̂[i]`: `TL i`, and `ê[i]` at `EP`. -/
abbrev TE (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop :=
  VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v i s ∧ PolyIs s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (EP P)) (KPke.kgE P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) i)

/-- `Â[i, j] ŝ[j]` into `h` (`TP` or `PP`). -/
theorem prod_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {i j h : Nat} (hi : i < P.k)
    (hj : j < P.k) (hh : h = TP P ∨ h = PP P) {s : State} (e : VG.Proof.MlKem.AArch64.KeyGen.TE P s₀ mB v i s) :
    WP isa (kgMul h (aOff P i j) (sOff P j)) s fun s' => VG.Proof.MlKem.AArch64.KeyGen.TE P s₀ mB v i s' ∧
      (∀ a, h = PP P → PolyIs s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (TP P)) a →
        PolyIs s'.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (TP P)) a) ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 h)
        (multiplyNTTs (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB i j) (KPke.kgS P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) j)) := by
  have hw := hp.wf
  have hij := VG.Proof.MlKem.AArch64.ij_lt hi hj
  have a₁ : Reduced s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) ∧
      polyAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) = polyAt mB (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) :=
    e.1.c.ahat (P.k * i + j) hij
  have s₁ := e.1.sp j hj
  have ph : VG.Proof.MlKem.AArch64.KeyGen.PolyOff P h := by rcases hh with rfl | rfl; exacts [VG.Proof.MlKem.AArch64.KeyGen.po_TP hw, VG.Proof.MlKem.AArch64.KeyGen.po_PP hw]
  refine WP.mono (VG.Proof.MlKem.AArch64.KeyGen.mul_ok hp (h := h) (f := aOff P i j) (g := sOff P j) ph (VG.Proof.MlKem.AArch64.KeyGen.po_a hw hi hj) (VG.Proof.MlKem.AArch64.KeyGen.po_s hw hj)
    (.inr (by rcases hh with rfl | rfl <;> lom)) (.inr (by rcases hh with rfl | rfl <;> lom)) e.1.c.kb a₁.1 s₁.1)
    fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_
  rw [a₁.2, s₁.2] at t₂
  have ho : h = TP P ∨ h = PP P := hh
  refine ⟨⟨e.1.frame hp kb₂ x₂ f₂ (VG.Proof.MlKem.AArch64.KeyGen.apart_mul hp hi hh),
    polyIs_frame f₂ (by rcases ho with rfl | rfl; exacts [VG.Proof.MlKem.AArch64.KeyGen.far_TP hp, VG.Proof.MlKem.AArch64.KeyGen.far_PP hp (.inl rfl)]) e.2⟩,
    fun a ep ta => ?_, t₂⟩
  subst ep
  exact polyIs_frame f₂ (VG.Proof.MlKem.AArch64.KeyGen.far_PP hp (.inr rfl)) ta

theorem t_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v i s) : WP isa (P.kgTWith keccak.callee i) s (VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v (i + 1)) := by
  have hw := hp.wf
  have k1 := hw.facts.1
  refine WPs.seqs (List.cons_ne_nil _ _) (WPs.cons ?_)
  refine WP.mono (VG.Proof.MlKem.AArch64.KeyGen.cbdNtt_ok hp (N := P.k + i) (off := EP P) (by lom) (VG.Proof.MlKem.AArch64.KeyGen.po_EP hw) h.c.kb h.c.sig)
    fun s₁ ⟨kb₁, f₁, e₁, x₁⟩ => ?_
  have te₁ : VG.Proof.MlKem.AArch64.KeyGen.TE P s₀ mB v i s₁ := ⟨h.frame hp kb₁ x₁ f₁ (VG.Proof.MlKem.AArch64.KeyGen.apart_cnW hp hi), e₁⟩
  refine WPs.append (WPs.mono (WPs.dot (tp := TP P) (pp := PP P) (E := VG.Proof.MlKem.AArch64.KeyGen.TE P s₀ mB v i)
      (term := fun j h => [kgMul h (aOff P i j) (sOff P j)])
      (T := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (TP P)) a)
      (Q := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (PP P)) a)
      (v := fun j => multiplyNTTs (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB i j) (KPke.kgS P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) j)) (N := P.k)
      (fun s e => WPs.single (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.prod_ok hp hi k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩))
      (fun j _ hj s a e t => WPs.single (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.prod_ok hp hi hj (.inr rfl) e)
        fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩))
      (fun s a b e t q => WP.mono (VG.Proof.MlKem.AArch64.KeyGen.add_ok hp (f := TP P) (g := PP P) (VG.Proof.MlKem.AArch64.KeyGen.po_TP hw) (VG.Proof.MlKem.AArch64.KeyGen.po_PP hw) (.inl (by lom))
        e.1.c.kb t.1 q.1) fun s' ⟨kb', f', t', x'⟩ => ⟨⟨e.1.frame hp kb' x' f' (VG.Proof.MlKem.AArch64.KeyGen.apart_TP hp hi),
          polyIs_frame f' (fun r hr => by rw [List.mem_singleton.mp hr]; rdisj) e.2⟩, by rw [t.2, q.2] at t'; exact t'⟩)
      k1 (Nat.le_refl _) te₁) ?_)
  intro s₂ ⟨⟨tl₂, e₂⟩, t₂⟩
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.add_ok hp (f := TP P) (g := EP P) (VG.Proof.MlKem.AArch64.KeyGen.po_TP hw) (VG.Proof.MlKem.AArch64.KeyGen.po_EP hw) (.inr (by lom)) tl₂.c.kb
    t₂.1 e₂.1) fun s₇ ⟨kb₇, f₇, t₇, x₇⟩ => ?_)
  have tl₇ := tl₂.frame hp kb₇ x₇ f₇ (VG.Proof.MlKem.AArch64.KeyGen.apart_TP hp hi)
  rw [t₂.2, e₂.2] at t₇
  have tv : PolyIs s₇.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (TP P)) (VG.Proof.MlKem.AArch64.KeyGen.tV P s₀ mB i) := t₇
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.enc_ok hp (off := TP P) (b := 1) (o := 384 * i) (VG.Proof.MlKem.AArch64.KeyGen.po_TP hw) (.inl rfl)
    (by kl) kb₇ tv.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_)
  have tl₈ := tl₇.frame hp kb₈ x₈ f₈ fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.KeyGen.apart_ek hp hi
  have tv₈ := polyIs_frame f₈ (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) tv
  refine WPs.single (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.enc_ok hp (off := TP P) (b := 2) (o := 384 * P.k + 384 * i) (VG.Proof.MlKem.AArch64.KeyGen.po_TP hw) (.inr rfl)
    (by kl) kb₈ tv₈.1) fun s₉ ⟨kb₉, f₉, b₉, x₉⟩ => ?_)
  have tl₉ := tl₈.frame hp kb₉ x₉ f₉ fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.KeyGen.apart_dk hp hi
  refine ⟨tl₉.c, tl₉.sp, tl₉.dk, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact tl₉.ek i' hi'
  · refine ⟨?_, by rw [b₉, tv₈.2]⟩
    rw [bytesAt_frame f₉ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) (by decide), b₈, tv.2]

end VG.Proof.MlKem.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KgEnd`. -/
section

/-!
# ML-KEM on AArch64: `keygen`, the end

The copies of `ρ` into `ek` and `dk`, `H(ek)` into `dk`, the copy of `z`, and
our caller's registers back (`end_ok`); then the bytes of `ek` and `dk` as the
standard puts them together (`ek_at`, `dk_at`).
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-! ## Copies of 32 bytes -/

theorem readW64_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    (m.readW a 64).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

theorem writeW64_byte (m : Mem) (a : Addr) (v : BitVec 64) {i : Nat} (hi : i < 8) :
    m.writeW a v (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega),
    show i < 64 / 8 by omega, ite_true]
  rfl

theorem writeW64_off (m : Mem) (a x : Addr) (v : BitVec 64) (h : ¬ (x - a).toNat < 8) :
    m.writeW a v x = m x := Mem.write_apply h

/-- The 32 bytes at `S + so` copied to `D + dO`, through `x9`. -/
theorem copy_ok {S D : Addr} {sb db : Reg} {so dO : Nat} (hs9 : sb ≠ .x9) (hd9 : db ≠ .x9)
    (hso : so % 8 = 0 ∧ so + 32 ≤ 32768) (hdo : dO % 8 = 0 ∧ dO + 32 ≤ 32768)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 32⟩ ⟨D + BitVec.ofNat 64 dO, 32⟩)
    {s : State} (hS : s.gpr sb = S) (hD : s.gpr db = D)
    (hin : Covers [⟨S + BitVec.ofNat 64 so, 32⟩] (s.rd ++ s.wr))
    (hout : Covers [⟨D + BitVec.ofNat 64 dO, 32⟩] s.wr) :
    WP isa (.block (copy32 sb so db dO)) s fun s' => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (D + BitVec.ofNat 64 dO) 32 = bytesAt s.mem (S + BitVec.ofNat 64 so) 32 := by
  have n9s : sb ∉ [Reg.x9] := by simpa using hs9
  have n9d : db ∉ [Reg.x9] := by simpa using hd9
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k (s' : State) => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 32⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (D + BitVec.ofNat 64 (dO + i)) = s.mem (S + BitVec.ofNat 64 (so + i)))
    (fun k s₁ hk ⟨k₁, f₁, b₁⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun s' ⟨k', f', b'⟩ =>
      ⟨k', f', ?_⟩
  · refine wp_ldrx (a := S + BitVec.ofNat 64 (so + 8 * k)) ⟨by omega, by omega⟩ (by rw [k₁.get sb n9s, hS])
      (by rw [k₁.rd, k₁.wr]; exact VG.Proof.MlKem.AArch64.in_R (A := fun _ => S) (b := 0) hin (k := 8 * k) (by omega) (by decide))
      fun s₂ h₂ e₂ => wp_strx (a := D + BitVec.ofNat 64 (dO + 8 * k)) ⟨by omega, by omega⟩
      (by rw [h₂.get db n9d, k₁.get db n9d, hD])
      (by rw [h₂.wr, k₁.wr]; exact VG.Proof.MlKem.AArch64.in_R (A := fun _ => D) (b := 0) hout (k := 8 * k) (by omega) (by decide))
      fun s₃ h₃ => wp_nil ?_
    have m₃ : s₃.mem = s₁.mem.writeW (D + BitVec.ofNat 64 (dO + 8 * k))
        (s₁.mem.readW (S + BitVec.ofNat 64 (so + 8 * k)) 64) := by
      rw [h₃.mem, e₂, h₂.mem]
    refine ⟨((k₁.trans h₂.keep).trans h₃.keep).mono, ?_, fun i hi => ?_⟩
    · rw [m₃]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [← ptr_add]; exact contains_off (by omega) (by decide))
    · rw [m₃]
      rcases (by omega : i < 8 * k ∨ 8 * k ≤ i) with hi' | hi'
      · rw [VG.Proof.MlKem.AArch64.KeyGen.writeW64_off _ _ _ _ (sep_off D (a := dO + i) (n := 1) (b := dO + 8 * k) (k := 8) (by omega)
          (by omega) (by omega) _ (by rw [BitVec.sub_self]; decide))]
        exact b₁ i hi'
      · rw [show D + BitVec.ofNat 64 (dO + i) = D + BitVec.ofNat 64 (dO + 8 * k) + BitVec.ofNat 64 (i - 8 * k) by
          rw [ptr_add, show dO + 8 * k + (i - 8 * k) = dO + i by omega], VG.Proof.MlKem.AArch64.KeyGen.writeW64_byte _ _ _ (by omega),
          VG.Proof.MlKem.AArch64.KeyGen.readW64_byte _ _ (by omega), ptr_add, show so + 8 * k + (i - 8 * k) = so + i by omega]
        refine f₁ _ fun r hr hc => ?_
        rw [List.mem_singleton.mp hr] at hc
        exact hsep _ (R.contains (A := fun _ => S) (b := 0) (k := i) (n := 1) (by omega) (by decide)) hc
  · refine List.ext_getElem (by simp only [bytesAt_length]) fun i h₁ _ => ?_
    rw [bytesAt_length] at h₁
    rw [bytesAt_getElem, bytesAt_getElem, ptr_add, ptr_add]
    exact b' i (by omega)

/-! ## The bytes of `ek` and `dk` -/

/-- `n` encoded polynomials at `p`. -/
theorem cat_at {m : Mem} {p : Addr} {T : Nat → VG.Spec.MlKem.Poly} : ∀ {n : Nat},
    (∀ i < n, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i)) →
    bytesAt m p (384 * n) = KPke.catK (fun i => encode12 (T i)) n
  | 0, _ => rfl
  | n + 1, h => by
    rw [Nat.mul_succ, bytesAt_add, VG.Proof.MlKem.AArch64.KeyGen.cat_at fun i hi => h i (by omega), h n (by omega)]
    exact (KPke.foldK_succ (op := fun a b => a ++ b) (fun x => List.nil_append x) _ n).symm

variable {P : KemLay}

/-- `ek`'s bytes: the `k` `t̂[i]` and `ρ`, at `p`. -/
theorem ek_at {m : Mem} {p : Addr} {T : Nat → VG.Spec.MlKem.Poly} {ρ : List Byte}
    (h : ∀ i < P.k, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i))
    (hr : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) 32 = ρ) :
    bytesAt m p P.ekLen = KPke.catK (fun i => encode12 (T i)) P.k ++ ρ := by
  rw [KemLay.ekLen, bytesAt_add, VG.Proof.MlKem.AArch64.KeyGen.cat_at h, hr]

/-- `dk`'s bytes: `dk_PKE ‖ ek ‖ h ‖ z`, at `p`. -/
theorem dk_at {m : Mem} {p : Addr} {a b c d : List Byte} (ha : bytesAt m p (384 * P.k) = a)
    (hb : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) P.ekLen = b)
    (hc : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 32)) 32 = c)
    (hd : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 64)) 32 = d) : bytesAt m p P.dkLen = a ++ b ++ c ++ d := by
  have hc' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen)) 32 = c := by
    rw [show 384 * P.k + P.ekLen = 768 * P.k + 32 by simp only [KemLay.ekLen]; omega]; exact hc
  have hd' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen + 32)) 32 = d := by
    rw [show 384 * P.k + P.ekLen + 32 = 768 * P.k + 64 by simp only [KemLay.ekLen]; omega]; exact hd
  rw [show P.dkLen = 384 * P.k + P.ekLen + 32 + 32 by simp only [KemLay.ekLen, KemLay.dkLen]; omega,
    bytesAt_add, bytesAt_add, bytesAt_add, ha, hb, hc', hd']

/-! ## Regions -/

/-- A buffer apart from what `TL i` describes. -/
theorem apart_R {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {i b o l : Nat} (hi : i ≤ P.k) (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b = 1 → 384 * i ≤ o) (h2 : b = 2 → 384 * P.k + 384 * i ≤ o) :
    VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l) := by
  have hi' : 0 + 384 * i ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb (by kl) f ?_,
    hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb hi' f ?_,
    hp.args.rdisj (by decide) hb hi'' f ?_⟩ <;>
  · by_cases e : b = 3
    · have := h3 e; subst e; kl
    · by_cases e1 : b = 1
      · have := h1 e1; subst e1; kl
      · by_cases e2 : b = 2
        · have := h2 e2; subst e2; kl
        · kl

theorem apart_below {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) (i : Nat) (hi : i ≤ P.k) : VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ i (below s₀.sp 16) :=
  ⟨VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl), VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl), VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl),
    VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl), VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl)⟩

/-! ## The end -/

/-- What the function leaves. -/
structure Done (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  ek : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 1) P.ekLen = KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)
  dk : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2) P.dkLen = KPke.dkPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++
    KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++ H (KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) ++ VG.Proof.MlKem.AArch64.KeyGen.zB s₀

theorem pres_own : ∀ r ∈ preserved, r ∉ VG.Proof.MlKem.AArch64.KeyGen.own → r ∉ [Reg.x0, .x30, .x24, .x25, .x26, .x27, .x28] := by decide

/-- Our caller's registers back, and the result. -/
theorem restore_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {u : State} (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ u) :
    WP isa (.block [mov .x0 .x24, .ldr .x .x30 .x28 (SV P + 40), .ldr .x .x24 .x28 (SV P),
      .ldr .x .x25 .x28 (SV P + 8), .ldr .x .x26 .x28 (SV P + 16), .ldr .x .x27 .x28 (SV P + 24),
      .ldr .x .x28 .x28 (SV P + 32)]) u fun u' =>
      abiPreserved s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have hw := hp.wf
  have hsv : SV P % 8 = 0 ∧ SV P + 48 ≤ 32768 := by lom
  have cv := VG.Proof.MlKem.AArch64.KeyGen.cov_r hp hk (b := 3) (o := SV P) (l := 48) (by decide) hp.sv
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV P + 8 * k) = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 8 ∧
      w.mem.readW (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (own.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by rw [hr, hw]; exact VG.Proof.MlKem.AArch64.in_R cv (by omega) (by decide), by rw [hm]; exact hk.sv k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 →
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ w'.mem = u.mem ∧ w'.gpr .x28 = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  refine wp_mov fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, hk.x28⟩
  have l₁ := ld 5 (by decide) g₁
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 5)) (by kl) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 0)) (by kl) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 1)) (by kl) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 2)) (by kl) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 3)) (by kl) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 4)) (by kl) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp], fun r hr => (o₇.vcs r hr).trans (hk.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ VG.Proof.MlKem.AArch64.KeyGen.own
    · rcases mem6 ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₇.get .x27, e₆]; exact l₅.2.2
      · rw [e₇]; exact l₆.2.2
      · rw [h₇.get .x30, h₆.get .x30, h₅.get .x30, h₄.get .x30, h₃.get .x30, e₂]; exact l₁.2.2
    · rw [o₇.get r (VG.Proof.MlKem.AArch64.KeyGen.pres_own r hr ho), hk.cs r hr ho]
  · rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁]

/-- What holds from the copies of `ρ` on. -/
structure EndInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  tl : VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v P.k s
  rek : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 1 + BitVec.ofNat 64 (384 * P.k)) 32 = VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀
  rdk : bytesAt s.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2 + BitVec.ofNat 64 (768 * P.k)) 32 = VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀

/-- A region apart from what `EndInv` describes. -/
abbrev Far (P : KemLay) (s₀ : State) (r : Region) : Prop :=
  VG.Proof.MlKem.AArch64.KeyGen.Apart P s₀ P.k r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 1 (384 * P.k) 32).Disjoint r ∧ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 2 (768 * P.k) 32).Disjoint r

theorem EndInv.frame {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {s s' : State}
    (h : VG.Proof.MlKem.AArch64.KeyGen.EndInv P s₀ mB v s) (hk : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, VG.Proof.MlKem.AArch64.KeyGen.Far P s₀ r) : VG.Proof.MlKem.AArch64.KeyGen.EndInv P s₀ mB v s' :=
  ⟨h.tl.frame hp hk hx hf fun r hr => (hW r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.rek,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2) (by decide)]; exact h.rdk⟩

theorem far_R {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ VG.Proof.MlKem.AArch64.KeyGen.kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b ≠ 1) (h2 : b = 2 → 768 * P.k + 32 ≤ o) :
    VG.Proof.MlKem.AArch64.KeyGen.Far P s₀ (VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) b o l) :=
  ⟨VG.Proof.MlKem.AArch64.KeyGen.apart_R hp (Nat.le_refl _) hb f h3 (fun e => absurd e h1) (fun e => by have := h2 e; omega),
    hp.args.rdisj (by decide) hb (by kl) f (.inl (Ne.symm h1)),
    hp.args.rdisj (by decide) hb (by kl) f (by
      by_cases e : b = 2
      · have := h2 e; subst e; omega
      · exact .inl (Ne.symm e))⟩

theorem far_below {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) : VG.Proof.MlKem.AArch64.KeyGen.Far P s₀ (below s₀.sp 16) :=
  ⟨VG.Proof.MlKem.AArch64.KeyGen.apart_below hp P.k (Nat.le_refl _), VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl), VG.Proof.MlKem.AArch64.KeyGen.below_R hp (by decide) (by kl)⟩

/-- `ρ` into `ek` and `dk`. -/
theorem rho_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v P.k s) :
    WP isa (.block (copy32 .x28 SB .x26 (384 * P.k) ++ copy32 .x28 SB .x27 (768 * P.k))) s fun s' =>
      VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' ∧ VG.Proof.MlKem.AArch64.KeyGen.EndInv P s₀ mB v s' := by
  have hw := hp.wf
  have kb := h.c.kb
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.AArch64.KeyGen.copy_ok (S := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3) (D := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 1) (so := SB) (dO := 384 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x26 (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb (b := 3) (by decide) (by kl))
    (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb (b := 1) (by decide) (by kl))) fun sa ⟨ka, fa, ba⟩ => ?_
  have kba := kb.frame ka fa (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (b := 1) (o := 384 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have tla := h.frame hp kba (ka.get .x24) fa fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.KeyGen.apart_R hp (b := 1) (o := 384 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (fun _ => Nat.le_refl _) (by kl)
  refine WP.mono (VG.Proof.MlKem.AArch64.KeyGen.copy_ok (S := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3) (D := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2) (so := SB) (dO := 768 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kba.x28 kba.x27 (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kba (b := 3) (by decide) (by kl))
    (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kba (b := 2) (by decide) (by kl))) fun sb ⟨kb', fb, bb⟩ => ?_
  have kbb := kba.frame kb' fb (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (b := 2) (o := 768 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  refine ⟨kbb, tla.frame hp kbb (kb'.get .x24) fb (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.KeyGen.apart_R hp (b := 2) (o := 768 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (by kl) (fun _ => by omega)), ?_, ?_⟩
  · rw [bytesAt_frame fb (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide), ba]
    exact h.c.rho
  · rw [bb, bytesAt_frame fa (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact h.c.rho

/-- `H(ek)` into `dk`. -/
theorem hek_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (kb : VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s)
    (h : VG.Proof.MlKem.AArch64.KeyGen.EndInv P s₀ mB v s) :
    WP isa (hashWith keccak.callee .x28 ST WK 136 6 [⟨.x26, 0, P.ekLen⟩] [⟨.x27, 768 * P.k + 32, 32⟩]) s
      fun s' => VG.Proof.MlKem.AArch64.KeyGen.KB P s₀ s' ∧ VG.Proof.MlKem.AArch64.KeyGen.EndInv P s₀ mB v s' ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
        H (KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) := by
  have hw := hp.wf
  have e28 : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 3 + BitVec.ofNat 64 o := fun o => by rw [kb.x28]
  refine WP.mono (hashWith_ok keccak (VG.Proof.MlKem.AArch64.KeyGen.hsetup hp kb (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x26, 0, P.ekLen⟩]) (outs := [⟨.x27, 768 * P.k + 32, 32⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 1) hp kb (by decide) (by kl) (by decide) (by kl) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.KeyGen.pieceOk (b := 2) hp kb (by decide) (by kl) (by kl) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ?_
  have kb' := kb.hash hp k' fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨2, 768 * P.k + 32, 32, rfl, by decide, by decide, by kl, .inl (by decide)⟩
  have msg : (List.map (pbytes s) [⟨.x26, 0, P.ekLen⟩]).flatten = KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb.x26, ptr_zero]
    exact VG.Proof.MlKem.AArch64.KeyGen.ek_at (T := VG.Proof.MlKem.AArch64.KeyGen.tV P s₀ mB) (ρ := VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (fun i hi => (h.tl.ek i hi).1) h.rek
  obtain ⟨o, -⟩ := o'
  rw [msg, kb.x27] at o
  refine ⟨kb', h.frame hp kb' (k'.cs _ (by decide) (by decide)) k'.frame fun r hr => ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil] at hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [VG.Proof.MlKem.AArch64.STr, e28]
      exact VG.Proof.MlKem.AArch64.KeyGen.far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [VG.Proof.MlKem.AArch64.WKr, e28]
      exact VG.Proof.MlKem.AArch64.KeyGen.far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [kb.sp]; exact VG.Proof.MlKem.AArch64.KeyGen.far_below hp
    · simp only [preg, kb.x27]
      exact VG.Proof.MlKem.AArch64.KeyGen.far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  · rw [o, H_eq]; rfl

/-- `z` into `dk`, and the rest. -/
theorem end_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ mB v P.k s) :
    WP isa (P.kgEndWith keccak.callee) s (VG.Proof.MlKem.AArch64.KeyGen.Done P s₀ mB v) := by
  have hw := hp.wf
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.rho_ok hp h) fun s₁ ⟨kb₁, h₁⟩ => WP.seq (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.hek_ok hp kb₁ h₁)
    fun s₂ ⟨kb₂, h₂, hh₂⟩ => ?_))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.AArch64.KeyGen.copy_ok (S := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 0) (D := VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2) (so := 32) (dO := 768 * P.k + 64) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb₂.x25 kb₂.x27 (VG.Proof.MlKem.AArch64.KeyGen.cov_r hp kb₂ (b := 0) (by decide) (by kl))
    (VG.Proof.MlKem.AArch64.KeyGen.cov_w hp kb₂ (b := 2) (by decide) (by kl))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  have kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.KeyGen.kb_disj hp (b := 2) (o := 768 * P.k + 64) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have far₃ : ∀ r ∈ [VG.Proof.MlKem.AArch64.R (VG.Proof.MlKem.AArch64.KeyGen.kA s₀) 2 (768 * P.k + 64) 32], VG.Proof.MlKem.AArch64.KeyGen.Far P s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.KeyGen.far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  have h₃ := h₂.frame hp kb₃ (k₃.get .x24) f₃ far₃
  have hh₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
      H (KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  have z₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = VG.Proof.MlKem.AArch64.KeyGen.zB s₀ := by rw [b₃]; exact kb₂.z
  have ek₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 1) P.ekLen = KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) :=
    VG.Proof.MlKem.AArch64.KeyGen.ek_at (T := VG.Proof.MlKem.AArch64.KeyGen.tV P s₀ mB) (ρ := VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  have dk₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.KeyGen.kA s₀ 2) P.dkLen = KPke.dkPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++
      KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++ H (KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ mB) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) ++ VG.Proof.MlKem.AArch64.KeyGen.zB s₀ :=
    VG.Proof.MlKem.AArch64.KeyGen.dk_at (VG.Proof.MlKem.AArch64.KeyGen.cat_at (T := KPke.kgS P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) fun j hj => h₃.tl.dk j hj)
      (VG.Proof.MlKem.AArch64.KeyGen.ek_at (T := VG.Proof.MlKem.AArch64.KeyGen.tV P s₀ mB) (ρ := VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (VG.Proof.MlKem.AArch64.KeyGen.restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

end VG.Proof.MlKem.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KeyGen`. -/
section

/-!
# ML-KEM on AArch64: `vg_mlkem768_keygen` and `vg_mlkem1024_keygen`

Correctness is the prologue and `G` (`a_ok`), the matrix (`b_ok`), then `ŝ`,
`ê`, `t̂` and the end (`c_ok`); the result is 1 exactly when every `SampleNTT`
finishes within 280 iterations (`post_of`).

Constant time up to `ρ`, relating two runs (`RelCT`) from states that agree
on the pointers and on `ρ`: the prologue and `G`, and everything after the
matrix, by the taint analysis (their addresses and branches depend only on
the pointers); each entry of the matrix by the taint analysis for the
arguments of `sample_ntt`, then `sample_ntt`'s own constant time
(`RelCT.call`), since both runs call it on the same seed `ρ ‖ j ‖ i`.

The proof is stated once for a well-formed parameter set (`KemLay.Wf`),
with the taint analyses of its code (`KgTaints`), which are decided on the
code of each parameter set; the end of this file is ML-KEM-768's instance
(and `Proof/MlKem1024/AArch64/KeyGen.lean` ML-KEM-1024's).
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-! ## Correctness -/

theorem a_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) : WP isa (P.kgAWith keccak.callee) s₀ (VG.Proof.MlKem.AArch64.KeyGen.AfterA P s₀) :=
  WP.seq (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.prologue_ok hp) fun _ h => VG.Proof.MlKem.AArch64.KeyGen.g_ok hp h)

theorem c_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.KeyGen.Pre P s₀) {s : State} (h : VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * P.k) s) :
    WP isa (P.kgCWith keccak.callee) s (VG.Proof.MlKem.AArch64.KeyGen.Done P s₀ s.mem (s.gpr .x24)) := by
  have k1 := hp.wf.facts.1
  have c : VG.Proof.MlKem.AArch64.KeyGen.CInv P s₀ s.mem (s.gpr .x24) s := ⟨h.kb, h.rho, h.sig, rfl, fun e he => ⟨h.red e he, rfl⟩⟩
  have s0 : VG.Proof.MlKem.AArch64.KeyGen.SInv P s₀ s.mem (s.gpr .x24) 0 s :=
    ⟨c, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (WPs.range (I := VG.Proof.MlKem.AArch64.KeyGen.SInv P s₀ s.mem (s.gpr .x24))
    (fun j hj _ h => VG.Proof.MlKem.AArch64.KeyGen.s_step hp hj h) s0) fun s₁ h₁ => ?_)))
  have t0 : VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ s.mem (s.gpr .x24) 0 s₁ := ⟨h₁.c, h₁.sp, h₁.dk, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact WPs.mono (WPs.range (I := VG.Proof.MlKem.AArch64.KeyGen.TL P s₀ s.mem (s.gpr .x24)) (fun i hi _ h => VG.Proof.MlKem.AArch64.KeyGen.t_step hp hi h) t0)
    fun s₂ h₂ => WPs.single (VG.Proof.MlKem.AArch64.KeyGen.end_ok hp h₂)

theorem post_of {s₀ sB s' : State} (hB : VG.Proof.MlKem.AArch64.KeyGen.BInv P s₀ (P.k * P.k) sB) (hD : VG.Proof.MlKem.AArch64.KeyGen.Done P s₀ sB.mem (sB.gpr .x24) s') :
    (VG.Proof.MlKem.keyGenAArch64 P).post s₀ s' := by
  show Outcome (fun iters => keyGenInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) 32)
    (bytesAt s₀.mem (s₀.gpr .x0 + 32) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x1) P.ekLen, bytesAt s'.mem (s₀.gpr .x2) P.dkLen)
  have ed : bytesAt s₀.mem (s₀.gpr .x0) 32 = VG.Proof.MlKem.AArch64.KeyGen.dB s₀ := by
    show _ = bytesAt s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 0) 32
    rw [ptr_zero]
  have ez : bytesAt s₀.mem (s₀.gpr .x0 + 32) 32 = VG.Proof.MlKem.AArch64.KeyGen.zB s₀ := rfl
  have ek : bytesAt s'.mem (s₀.gpr .x1) P.ekLen = KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ sB.mem) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) := hD.ek
  have dk : bytesAt s'.mem (s₀.gpr .x2) P.dkLen = KPke.dkPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++
      KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ sB.mem) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) ++ H (KPke.ekPKE P.params (VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ sB.mem) (VG.Proof.MlKem.AArch64.KeyGen.dB s₀)) ++
      VG.Proof.MlKem.AArch64.KeyGen.zB s₀ := hD.dk
  rw [ed, ez, ek, dk, hD.x0, hB.acc]
  by_cases hA : VG.Proof.MlKem.AArch64.KeyGen.allOk P s₀ (P.k * P.k)
  · rw [ite_eq_left hA]
    refine .inl ⟨rfl, 280, ?_⟩
    show keyGenInternal P.params 280 (VG.Proof.MlKem.AArch64.KeyGen.dB s₀) (VG.Proof.MlKem.AArch64.KeyGen.zB s₀) = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some (p := P.params) rfl (a := VG.Proof.MlKem.AArch64.KeyGen.aM P s₀ sB.mem)
      fun i hi j hj => ?_]
    · rfl
    · have hi : i < P.k := hi
      have hj : j < P.k := hj
      have he : P.k * i + j < P.k * P.k := VG.Proof.MlKem.AArch64.ij_lt hi hj
      have hke := VG.Proof.MlKem.AArch64.ij_div (i := i) hj
      have r := hB.res (P.k * i + j) he
      have ok := hA (P.k * i + j) he
      rw [hke.1, hke.2] at r ok
      rcases r with r | r
      · rw [r] at ok; simp at ok
      · exact r
  · rw [ite_eq_right hA]
    refine .inr ⟨rfl, ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < P.k * P.k ∧ ¬ (sampleNTT 280 (matSeed (VG.Proof.MlKem.AArch64.KeyGen.rhoK P s₀) (e / P.k) (e % P.k))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    show keyGenInternal P.params 280 _ _ = none
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none (p := P.params) (i := e / P.k) (j := e % P.k)
      (VG.Proof.MlKem.AArch64.div_lt he) (VG.Proof.MlKem.AArch64.mod_lt he) (Option.not_isSome_iff_eq_none.mp hn)]
    rfl

theorem correct (hP : P.Wf) {s₀ : State} (hs : (VG.Proof.MlKem.keyGenAArch64 P).pre s₀) :
    WP isa (P.keyGenWith keccak.callee) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MlKem.keyGenAArch64 P).post s₀ s' := by
  have hp := VG.Proof.MlKem.AArch64.KeyGen.pre_of hP hs
  exact WP.seq (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.a_ok hp) fun _ hA => WP.seq (WP.mono (VG.Proof.MlKem.AArch64.KeyGen.b_ok hp hA) fun _ hB =>
    WP.mono (VG.Proof.MlKem.AArch64.KeyGen.c_ok hp hB) fun _ hD => ⟨hD.abi, VG.Proof.MlKem.AArch64.KeyGen.post_of hB hD⟩))

/-! ## Constant time -/

/-- The taint analyses of `P`'s code, decided for each parameter set: the
code before and after the matrix (with the Keccak functions `keccak`), and
the arguments of each `sample_ntt`. -/
structure KgTaints (P : KemLay) (keccak : VG.Proof.Sha3.AArch64.Permutation) : Prop where
  a : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (P.kgAWith keccak.callee) h).isSome = true
  c : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (P.kgCWith keccak.callee) h).isSome = true
  setup : ∀ i < P.k, ∀ j < P.k, ∃ hc : Taint.Hint taint.T,
    (taint.check (Taint.ofRegs [.x28]) (.block (P.kgSetup i j)) hc).isSome = true

/-- Two runs from states the contract relates. -/
abbrev Pub3 (P : KemLay) (σ₁ σ₂ : State) : Prop :=
  (VG.Proof.MlKem.keyGenAArch64 P).pre σ₁ ∧ (VG.Proof.MlKem.keyGenAArch64 P).pre σ₂ ∧ (VG.Proof.MlKem.keyGenAArch64 P).pub σ₁ σ₂

theorem Pub3.kA {σ₁ σ₂ : State} (h : VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂) : ∀ b, VG.Proof.MlKem.AArch64.KeyGen.kA σ₁ b = VG.Proof.MlKem.AArch64.KeyGen.kA σ₂ b
  | 0 => h.2.2.1
  | 1 => h.2.2.2.1
  | 2 => h.2.2.2.2.1
  | _ + 3 => h.2.2.2.2.2.1

theorem Pub3.sp {σ₁ σ₂ : State} (h : VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂) : σ₁.sp = σ₂.sp := h.2.2.2.2.2.2.1

theorem Pub3.rho {σ₁ σ₂ : State} (h : VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂) : VG.Proof.MlKem.AArch64.KeyGen.rhoK P σ₁ = VG.Proof.MlKem.AArch64.KeyGen.rhoK P σ₂ := by
  have e := map_toNat_inj h.2.2.2.2.2.2.2
  show KPke.kgRho P.params (bytesAt σ₁.mem (σ₁.gpr .x0 + BitVec.ofNat 64 0) 32) =
    KPke.kgRho P.params (bytesAt σ₂.mem (σ₂.gpr .x0 + BitVec.ofNat 64 0) 32)
  rw [ptr_zero, ptr_zero]
  exact e

variable (hP : P.Wf)
include hP

/-- `SampleNTT` on the same seed in both runs. -/
theorem call_rct {σ₁ σ₂ : State} (hpub : VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂) {i j : Nat} (hi : i < P.k) (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => VG.Proof.MlKem.AArch64.KeyGen.Mid P σ₁ i j s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.Mid P σ₂ i j s₂) (kgCallWith keccak.callee) fun _ _ => True := by
  have hp₁ := VG.Proof.MlKem.AArch64.KeyGen.pre_of hP hpub.1
  have hp₂ := VG.Proof.MlKem.AArch64.KeyGen.pre_of hP hpub.2.1
  refine RelCT.seq (RelCT.wp (F₁ := fun s : State => s.sp = σ₁.sp) (F₂ := fun s : State => s.sp = σ₂.sp)
    (VG.Proof.MlKem.AArch64.sample_ctWith keccak (sd := VG.Proof.MlKem.AArch64.KeyGen.kA σ₁ 3 + BitVec.ofNat 64 SB) (a := VG.Proof.MlKem.AArch64.KeyGen.kA σ₁ 3 + BitVec.ofNat 64 (aOff P i j))
      (w := VG.Proof.MlKem.AArch64.KeyGen.kA σ₁ 3 + BitVec.ofNat 64 SS) fun s₁ s₂ h => ?_) fun s₁ s₂ h => ⟨?_, ?_⟩)
    (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => agree_of (by rw [h.2.1, h.2.2, hpub.sp])
      fun r hr => by cases hr) (by taint_decide))
  · have A₂ := h.2.args hp₂ hi hj
    rw [← hpub.kA 3] at A₂
    refine ⟨h.1.args hp₁ hi hj, A₂, ?_, by rw [h.1.b.kb.sp, h.2.b.kb.sp, hpub.sp]⟩
    rw [h.1.seed, hpub.kA 3, h.2.seed, hpub.rho]
  · exact WP.mono ((h.1.args hp₁ hi hj).spWith keccak) fun s' e => by rw [e, h.1.b.kb.sp]
  · exact WP.mono ((h.2.args hp₂ hi hj).spWith keccak) fun s' e => by rw [e, h.2.b.kb.sp]

/-- `Â[i, j]` in both runs. -/
theorem sample_rct (ht : VG.Proof.MlKem.AArch64.KeyGen.KgTaints P keccak) {σ₁ σ₂ : State} (hpub : VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂) {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₁ (P.k * i + j) s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₂ (P.k * i + j) s₂)
      (P.kgSampleWith keccak.callee i j)
      fun s₁ s₂ => VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₁ (P.k * i + j + 1) s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₂ (P.k * i + j + 1) s₂ := by
  have hp₁ := VG.Proof.MlKem.AArch64.KeyGen.pre_of hP hpub.1
  have hp₂ := VG.Proof.MlKem.AArch64.KeyGen.pre_of hP hpub.2.1
  have hck := (ht.setup i hi j hj).choose_spec
  refine RelCT.seq (R := fun s₁ s₂ => VG.Proof.MlKem.AArch64.KeyGen.Mid P σ₁ i j s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.Mid P σ₂ i j s₂)
    (RelCT.mono (RelCT.wp (F₁ := VG.Proof.MlKem.AArch64.KeyGen.Mid P σ₁ i j) (F₂ := VG.Proof.MlKem.AArch64.KeyGen.Mid P σ₂ i j)
      (RelCT.taint (A := taint) (Taint.ofRegs [.x28]) (fun s₁ s₂ h =>
        agree_of (by rw [h.1.kb.sp, h.2.kb.sp, hpub.sp]) fun r hr => by
          rw [List.mem_singleton.mp hr, h.1.kb.x28, h.2.kb.x28, hpub.kA 3]) hck)
      fun s₁ s₂ h => ⟨VG.Proof.MlKem.AArch64.KeyGen.setup_ok hp₁ hi hj h.1, VG.Proof.MlKem.AArch64.KeyGen.setup_ok hp₂ hi hj h.2⟩) (fun _ _ h => h) fun _ _ h => h.2)
    (RelCT.mono (RelCT.wp (F₁ := VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₁ (P.k * i + j + 1)) (F₂ := VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₂ (P.k * i + j + 1))
      (VG.Proof.MlKem.AArch64.KeyGen.call_rct hP hpub hi hj) fun s₁ s₂ h => ⟨VG.Proof.MlKem.AArch64.KeyGen.call_ok hp₁ hi hj h.1, VG.Proof.MlKem.AArch64.KeyGen.call_ok hp₂ hi hj h.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2)

theorem b_rct (ht : VG.Proof.MlKem.AArch64.KeyGen.KgTaints P keccak) :
    RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂ ∧ VG.Proof.MlKem.AArch64.KeyGen.AfterA P σ₁ s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.AfterA P σ₂ s₂)
      (P.kgBWith keccak.callee)
      fun s₁ s₂ => ∃ σ₁ σ₂, VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₁ (P.k * P.k) s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₂ (P.k * P.k) s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State) s₁ s₂ =>
      VG.Proof.MlKem.AArch64.KeyGen.Pub3 P x.1 x.2 ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P x.1 0 s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P x.2 0 s₂) fun x => ?_)
    (fun _ _ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂), hpub, BInv.zero a₁, BInv.zero a₂⟩) fun _ _ h => h
  by_cases hpub : VG.Proof.MlKem.AArch64.KeyGen.Pub3 P x.1 x.2
  · refine RelCT.mono (P := fun s₁ s₂ => VG.Proof.MlKem.AArch64.KeyGen.BInv P x.1 0 s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P x.2 0 s₂)
      (Q := fun s₁ s₂ => VG.Proof.MlKem.AArch64.KeyGen.BInv P x.1 (P.k * P.k) s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P x.2 (P.k * P.k) s₂) ?_ (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2, hpub, h⟩
    exact RelCTs.seqs (VG.Proof.MlKem.AArch64.matrix_ne_nil hP.facts.1) (RelCTs.matrix (I := fun e s₁ s₂ => VG.Proof.MlKem.AArch64.KeyGen.BInv P x.1 e s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P x.2 e s₂)
      (fun i hi j hj => VG.Proof.MlKem.AArch64.KeyGen.sample_rct hP ht hpub hi hj) (Nat.le_refl _))
  · exact RelCT.of_false fun _ _ h => hpub h.1

omit hP in
theorem c_rct (ht : VG.Proof.MlKem.AArch64.KeyGen.KgTaints P keccak) :
    RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂, VG.Proof.MlKem.AArch64.KeyGen.Pub3 P σ₁ σ₂ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₁ (P.k * P.k) s₁ ∧ VG.Proof.MlKem.AArch64.KeyGen.BInv P σ₂ (P.k * P.k) s₂)
      (P.kgCWith keccak.callee) fun _ _ => True :=
  VectorTaint.relCT (Taint.ofRegs [.x25, .x26, .x27, .x28]) (fun s₁ s₂ ⟨σ₁, σ₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, hpub.sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25, hpub.kA 0]
      · rw [b₁.kb.x26, b₂.kb.x26, hpub.kA 1]
      · rw [b₁.kb.x27, b₂.kb.x27, hpub.kA 2]
      · rw [b₁.kb.x28, b₂.kb.x28, hpub.kA 3]) ht.c.choose_spec

theorem ct (ht : VG.Proof.MlKem.AArch64.KeyGen.KgTaints P keccak) :
    ConstantTime isa (VG.Proof.MlKem.keyGenAArch64 P).pre (VG.Proof.MlKem.keyGenAArch64 P).pub (P.keyGenWith keccak.callee) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, -, -⟩ := h
        simp [e0, e1, e2, e3])) ht.a.choose_spec).wpDep (F := fun σ s => VG.Proof.MlKem.AArch64.KeyGen.AfterA P σ s)
      fun _ _ h => ⟨VG.Proof.MlKem.AArch64.KeyGen.a_ok (VG.Proof.MlKem.AArch64.KeyGen.pre_of hP h.1), VG.Proof.MlKem.AArch64.KeyGen.a_ok (VG.Proof.MlKem.AArch64.KeyGen.pre_of hP h.2.1)⟩)
    (RelCT.seq (VG.Proof.MlKem.AArch64.KeyGen.b_rct hP ht) (VG.Proof.MlKem.AArch64.KeyGen.c_rct ht)))

theorem keyGen_correct {s : State} (hs : (VG.Proof.MlKem.keyGenAArch64 P).pre s) :
    ∃ t s', Exec isa (P.keyGenWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.keyGenAArch64 P).post s s' :=
  VG.Proof.MlKem.AArch64.KeyGen.correct hP hs

omit hP

/-! ## ML-KEM-768 -/

theorem wf768 : lay768.Wf := ⟨by decide⟩

theorem taints768 : VG.Proof.MlKem.AArch64.KeyGen.KgTaints lay768 keccak :=
  ⟨keccak.mlkemKgATaint, keccak.mlkemKgCTaint, by
    intro i hi j hj
    change i < 3 at hi
    change j < 3 at hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
    exact ⟨_, by taint_decide⟩⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

theorem keyGen_correctWith (s : State) (hs : (VG.Proof.MlKem.keyGenAArch64 lay768).pre s) :
    ∃ t s', Exec isa (keyGenWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.keyGenAArch64 lay768).post s s' :=
  VG.Proof.MlKem.AArch64.KeyGen.keyGen_correct VG.Proof.MlKem.AArch64.KeyGen.wf768 hs

theorem keyGen_verifiedWith :
    Verified AArch64.target (keyGenWith keccak.callee) (Spec.MlKem.keyGenContract AArch64.abi 16) :=
  Verified.of_correct (VG.Proof.MlKem.AArch64.KeyGen.keyGen_correctWith (keccak := keccak)) (VG.Proof.MlKem.AArch64.KeyGen.ct VG.Proof.MlKem.AArch64.KeyGen.wf768 VG.Proof.MlKem.AArch64.KeyGen.taints768) (by
    mlkem_implies [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, VG.Proof.MlKem.keyGenAArch64, lay768, KemLay.params, Spec.MlKem.mlKem768,
      KemLay.ekLen, KemLay.dkLen, AArch64.abi, AArch64.argRegs] [sat] using VG.Proof.MlKem.AArch64.KeyGen.sat)

theorem keyGen_verified :
    Verified AArch64.target keyGen (Spec.MlKem.keyGenContract AArch64.abi 16) :=
  VG.Proof.MlKem.AArch64.KeyGen.keyGen_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem.AArch64.KeyGen

end
