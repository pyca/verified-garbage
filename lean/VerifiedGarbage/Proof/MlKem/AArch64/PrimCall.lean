module

public import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
public import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.AArch64.Sample
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Base
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.MlKem.AArch64.Encode
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec

/-!
# ML-KEM-768 on AArch64: calling the primitives

Each call of a verified polynomial primitive, from its proof (with `WP.call`;
`sample_ntt` with `WP.callF`, as its Keccak calls have frames): what it needs
of the state it is called from, and what holds when it returns (`Kept`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem entry (s : State) {r : Reg} (h : r ∉ linkRegs := by decide) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

/-- `vg_mlkem_add(f, g)` or `vg_mlkem_sub(f, g)`. -/
theorem acc_call {op : Poly → Poly → Poly} {c : Prog isa} {name : String}
    (hv : ∀ s, (accAArch64 op).pre s →
      ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accAArch64 op).post s s')
    (hn : c.noFrames = true) {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (op (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call name c) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = g := (entry s).trans h1
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
  acc_call add_correct (by decide +kernel) h0 h1 hd hrf hrg hc hw hQ

theorem sub_call {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (sub (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.AArch64.sub) s Q :=
  acc_call sub_correct (by decide +kernel) h0 h1 hd hrf hrg hc hw hQ

/-- `vg_mlkem_compress_encode(f, d, out, 32 d)`. -/
theorem compressEncode_call {s : State} {f o : Addr} {d : Nat} (h0 : s.gpr .x0 = f)
    (h1 : ((s.gpr .x1).setWidth 32).toNat = d) (h2 : s.gpr .x2 = o) (h3 : (s.gpr .x3).toNat = 32 * d)
    (hdw : d ∈ compressWidths) (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩) (hr : Reduced s.mem f)
    (hc : Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr)) (hw : Covers [⟨o, 32 * d⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) →
      Q s') :
    WP isa (.call "vg_mlkem_compress_encode" Impl.MlKem.AArch64.compressEncode) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : ((s.callEntry.gpr .x1).setWidth 32).toNat = d := by rw [entry s]; exact h1
  have c2 : s.callEntry.gpr .x2 = o := (entry s).trans h2
  have c3 : (s.callEntry.gpr .x3).toNat = 32 * d := by rw [entry s]; exact h3
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
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = 32 * d := by rw [entry s]; exact h1
  have c2 : ((s.callEntry.gpr .x2).setWidth 32).toNat = d := by rw [entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = f := (entry s).trans h3
  refine WP.callV (k := decodeDecompressAArch64) DD.correct (rd := [⟨b, 32 * d⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem.AArch64
