module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Consts
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.MatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.Scrubbed
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.AArch64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! ### `MlKem.AArch64.Hybrid.Start`, which this module and modules that import it used -/

section

/-!
# The hashing encapsulation's first phase

`startH_ok`: the prologue, `m`, the all-zero third state and `ρ`
(`Hybrid.startH`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay}

/-- After the first phase. -/
structure AfterS (P : KemLay) (s₀ s : State) : Prop where
  kb : KB P (enL P) s₀ s
  x24 : s.gpr .x24 = 1
  m : bytesAt s.mem (sA (enL P) s₀ MB) 32 = mE s₀
  rho : bytesAt s.mem (sA (enL P) s₀ SB) 32 = rhoE P s₀
  zero : stateAt s.mem (kA s₀ (enL P).sc) = Spec.Sha3.zero

theorem startH_ok {s₀ : State} (hp : Pre P (enL P) s₀) :
    WP isa (Impl.MlKem.AArch64.Hybrid.startH P) s₀ (AfterS P s₀) := by
  have hw := hp.wf
  unfold Impl.MlKem.AArch64.Hybrid.startH
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- the prologue and `m`
  refine WP.mono (prologue_ok hp) fun s₁ h₁ => ?_
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 1) (D := kA s₀ 4) (so := 0) (dO := MB) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk) (hp.fs (by lom)) (by enk)
      (by decide)) (by rw [h₁.keep.get .x1 (by decide)]; rfl) h₁.kb.x28
    (cov_r hp h₁.kb (b := 1) (by enk) (by enk)) (cov_s hp h₁.kb (by lom)))
    fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  have kb₂ := h₁.kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by enk)
  have m₂ : bytesAt s₂.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [show sA (enL P) s₀ MB = kA s₀ 4 + BitVec.ofNat 64 MB from rfl, b₂,
      h₁.kb.ro_bytes (b := 1) (by enk) (by enk), ptr_zero]
  have x24₂ : s₂.gpr .x24 = 1 := by rw [k₂.get .x24, h₁.x24]
  -- the third state
  have hS := hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)
  refine WP.mono (zeroState_ok hS (s := s₂) ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun s₃ ⟨k₃, z₃⟩ => ?_
  have e28' : ∀ o l, (⟨s₂.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) (enL P).sc o l :=
    fun o l => by rw [kb₂.x28]
  have kb₃ := kb₂.call k₃ fun r hr => by
    rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']; exact safe_scr hp (by lom)
  have m₃ : bytesAt s₃.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame k₃.frame (fun r hr => by
      rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']
      exact sdisj hp (by lom) (by lom) (by lom)) (by decide)]
    exact m₂
  have z₃' : stateAt s₃.mem (kA s₀ (enL P).sc) = Spec.Sha3.zero := by
    rw [kb₂.x28, show KEM.ST = 0 from rfl, ptr_zero] at z₃; exact z₃
  have x24₃ : s₃.gpr .x24 = 1 := by rw [k₃.cs _ (by decide) (by decide), x24₂]
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 4) (so := 384 * P.k) (dO := SB) (by decide)
    (by decide) (by lom) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk)
      (hp.fs (by lom)) (by enk) (by enk)) kb₃.x25 kb₃.x28 (cov_r hp kb₃ (b := 0) (by enk)
      (by enk)) (cov_s hp kb₃ (by lom)))
    fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by enk)
  have far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₄.mem (sA (enL P) s₀ o) l = bytesAt s₃.mem (sA (enL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₄ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by lom) h
  refine ⟨kb₄, by rw [k₄.get .x24, x24₃], by rw [far₄ (o := MB) (l := 32) (by lom) (by decide)]; exact m₃,
    ?_, ?_⟩
  · rw [show sA (enL P) s₀ SB = kA s₀ 4 + BitVec.ofNat 64 SB from rfl, b₄,
      kb₃.ro_bytes (b := 0) (by enk) (by enk),
      ← bytesAt_slice _ _ (show 384 * P.k + 32 ≤ P.ekLen from Nat.le_refl _)]
    rfl
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₄ (fun r hr => by
      rw [List.mem_singleton.mp hr, stR_sc]; exact sdisj hp (by lom) (by lom) (by lom))]
    exact z₃'

end VG.Proof.MlKem.AArch64.Hybrid

end

end

/-! ### `MlKem.AArch64.Optimized.ContractSat`, which the modules that import this one used -/

section

/-! ### `MlKem1024.AArch64.Decaps`, which this module and modules that import it used -/

section

/-! ### `MlKem1024.AArch64.Encaps`, which this module and modules that import it used -/

section

/-! ### `MlKem1024.AArch64.Args`, which only this module used -/

section

/-!
# ML-KEM-1024 on AArch64: the calls of the compression functions

The calls of ML-KEM-1024's compression functions, from their proofs (as
`PrimCall.lean` of ML-KEM-768), which the top-level functions make at the
widths `d_u` and `d_v`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem1024_compress_encode(f, d, out, 32 d)`. -/
theorem compressEncode1024_call {s : State} {f o : Addr} {d : Nat} (h0 : s.gpr .x0 = f)
    (h1 : ((s.gpr .x1).setWidth 32).toNat = d) (h2 : s.gpr .x2 = o) (h3 : (s.gpr .x3).toNat = 32 * d)
    (hdw : d ∈ Proof.MlKem1024.compressWidths) (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩)
    (hr : Reduced s.mem f) (hc : Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨o, 32 * d⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) →
      Q s') :
    WP isa (.call "vg_mlkem1024_compress_encode" Impl.MlKem1024.AArch64.compressEncode) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : ((s.callEntry.gpr .x1).setWidth 32).toNat = d := by rw [entry s]; exact h1
  have c2 : s.callEntry.gpr .x2 = o := (entry s).trans h2
  have c3 : (s.callEntry.gpr .x3).toNat = 32 * d := by rw [entry s]; exact h3
  refine WP.callV (k := MlKem1024.compressEncodeAArch64) MlKem1024.AArch64.CE.correct (rd := [⟨f, 1024⟩]) (wr := [⟨o, 32 * d⟩]) ?_
    hc hw ?_
  · simp only [MlKem1024.compressEncodeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [MlKem1024.compressEncodeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- `vg_mlkem1024_decode_decompress(b, 32 d, d, f)`. -/
theorem decodeDecompress1024_call {s : State} {b f : Addr} {d : Nat} (h0 : s.gpr .x0 = b)
    (h1 : (s.gpr .x1).toNat = 32 * d) (h2 : ((s.gpr .x2).setWidth 32).toNat = d) (h3 : s.gpr .x3 = f)
    (hdw : d ∈ Proof.MlKem1024.compressWidths) (hd : Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩)
    (hc : Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' →
      PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') :
    WP isa (.call "vg_mlkem1024_decode_decompress" Impl.MlKem1024.AArch64.decodeDecompress) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = 32 * d := by rw [entry s]; exact h1
  have c2 : ((s.callEntry.gpr .x2).setWidth 32).toNat = d := by rw [entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = f := (entry s).trans h3
  refine WP.callV (k := MlKem1024.decodeDecompressAArch64) MlKem1024.AArch64.DD.correct (rd := [⟨b, 32 * d⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [MlKem1024.decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [MlKem1024.decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem1024.AArch64

end

end

/-! ### `MlKem1024.AArch64.KeyGen`, which this module and modules that import it used -/

section

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kg*.lean`, `KeyGen.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`):
that it is well formed, and the taint analyses of its code, are decided on
its literals.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.KeyGen
open VG.Impl.MlKem.AArch64 (KemLay)

theorem wf1024 : lay1024.Wf := ⟨by decide⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

end VG.Proof.MlKem1024.AArch64.KeyGen

end

end

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_encaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Encaps.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`),
whose compression functions at the widths 11 and 5 are ML-KEM-1024's own
(`calls1024`); the taint analyses of its code are decided on its literals.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem1024.AArch64 (compressEncode1024_call decodeDecompress1024_call)
open VG.Impl.MlKem.AArch64 (KemLay)

theorem calls1024 : Calls lay1024 :=
  ⟨fun h0 h1 h2 h3 hd => compressEncode1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide),
    fun h0 h1 h2 h3 hd => decodeDecompress1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide)⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

end VG.Proof.MlKem1024.AArch64.Encaps

end

end

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Decaps*.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`); the
taint analyses of its code are decided on its literals.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Decaps
open VG.Impl.MlKem.AArch64 (KemLay)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

end VG.Proof.MlKem1024.AArch64.Decaps

end

end

/-! ### `MlKem.AArch64.Optimized.ConstsSat`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16 VG.Impl.MlKem.AArch64.Ntt16.Readonly

def tableSyms (name : String) : Addr :=
 if name="VG_MLKEM_REJ_SHUFFLE" then 0x200000 else
 if name="VG_MLKEM_GAMMA" then 0x210000 else
 if name="VG_MLKEM_NTT16_ZETAS" then 0x220000 else
 if name="VG_MLKEM16_INTT_ZETAS" then 0x230000 else 0x240000

def tableMem : Mem := fun a =>
 if a.toNat<0x210000 then constMem 0x200000 Impl.MlKem.AArch64.Rej8.tableWords a else
 if a.toNat<0x220000 then constMem 0x210000 (words 32 gammaTable) a else
 if a.toNat<0x230000 then constMem 0x220000 (words 16 tableHalves) a else
 if a.toNat<0x240000 then constMem 0x230000 FastInv.tabWords a else
 constMem 0x240000 Fast.tabWords a

theorem tableMem_word {n i : Nat} (hn : n<5) (hi : i<512) :
 tableMem.readW (BitVec.ofNat 64 (0x200000+65536*n)+BitVec.ofNat 64 (8*i)) 64 =
 (constMem (BitVec.ofNat 64 (0x200000+65536*n))
  ([Impl.MlKem.AArch64.Rej8.tableWords,words 32 gammaTable,words 16 tableHalves,FastInv.tabWords,
    Fast.tabWords].getD n [])).readW
   (BitVec.ofNat 64 (0x200000+65536*n)+BitVec.ofNat 64 (8*i)) 64 := by
 apply Mem.readW_congr
 intro j hj
 have e : (BitVec.ofNat 64 (0x200000+65536*n)+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j).toNat =
  0x200000+65536*n+8*i+j := by
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hn, hi, hj])]
 rcases (by omega_using [hn] : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4) with rfl|rfl|rfl|rfl|rfl
 · simp only [tableMem,e,ite_eq_left (by omega_using [hi, hj] : 0x200000+65536*0+8*i+j<0x210000)]
   simp only [List.getD_cons_zero,Nat.reduceMul,Nat.reduceAdd]
   rfl
 · simp only [tableMem,e,ite_eq_right (by omega_using [] : ¬0x200000+65536*1+8*i+j<0x210000),
    ite_eq_left (by omega_using [hi, hj] : 0x200000+65536*1+8*i+j<0x220000)]
   simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.reduceMul,Nat.reduceAdd]
   rfl
 · simp only [tableMem,e,ite_eq_right (by omega_using [] : ¬0x200000+65536*2+8*i+j<0x210000),
    ite_eq_right (by omega_using [] : ¬0x200000+65536*2+8*i+j<0x220000),
    ite_eq_left (by omega_using [hi, hj] : 0x200000+65536*2+8*i+j<0x230000)]
   simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.reduceMul,Nat.reduceAdd]
   rfl
 · simp only [tableMem,e,ite_eq_right (by omega_using [] : ¬0x200000+65536*3+8*i+j<0x210000),
    ite_eq_right (by omega_using [] : ¬0x200000+65536*3+8*i+j<0x220000),
    ite_eq_right (by omega_using [] : ¬0x200000+65536*3+8*i+j<0x230000),
    ite_eq_left (by omega_using [hi, hj] : 0x200000+65536*3+8*i+j<0x240000)]
   simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.reduceMul,Nat.reduceAdd]
   rfl
 · simp only [tableMem,e,ite_eq_right (by omega_using [] : ¬0x200000+65536*4+8*i+j<0x210000),
    ite_eq_right (by omega_using [] : ¬0x200000+65536*4+8*i+j<0x220000),
    ite_eq_right (by omega_using [] : ¬0x200000+65536*4+8*i+j<0x230000),
    ite_eq_right (by omega_using [] : ¬0x200000+65536*4+8*i+j<0x240000)]
   simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.reduceMul,Nat.reduceAdd]
   rfl

theorem tableMem_held : Abi.constsHeld tableMem tableSyms constants := by
 simp only [Abi.constsHeld,constants,List.forall_mem_cons]
 refine ⟨?_,?_,?_,?_,?_,fun _ h=>nomatch h⟩
 all_goals intro i hi
 · change i<Impl.MlKem.AArch64.Rej8.tableWords.length at hi
   rw [Rej8.tableWords_length] at hi
   rw [show tableSyms "VG_MLKEM_REJ_SHUFFLE"=0x200000 by rfl]
   have hx := tableMem_word (n:=0) (i:=i) (by decide) (by omega_using [hi])
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero] at hx
   exact hx.trans (constMem_held _ _ (by rw [Rej8.tableWords_length]; decide) i (by rw [Rej8.tableWords_length]; exact hi))
 · change i<(words 32 gammaTable).length at hi
   rw [Ntt16.Readonly.gamma_length] at hi
   rw [show tableSyms "VG_MLKEM_GAMMA"=0x210000 by rfl]
   have hx := tableMem_word (n:=1) (i:=i) (by decide) (by omega_using [hi])
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero,List.getD_cons_succ] at hx
   exact hx.trans (constMem_held _ _ (by rw [Ntt16.Readonly.gamma_length]; decide) i (by rw [Ntt16.Readonly.gamma_length]; exact hi))
 · change i<(words 16 tableHalves).length at hi
   rw [Ntt16.Readonly.forward_length] at hi
   rw [show tableSyms "VG_MLKEM_NTT16_ZETAS"=0x220000 by rfl]
   have hx := tableMem_word (n:=2) (i:=i) (by decide) (by omega_using [hi])
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero,List.getD_cons_succ] at hx
   exact hx.trans (constMem_held _ _ (by rw [Ntt16.Readonly.forward_length]; decide) i (by rw [Ntt16.Readonly.forward_length]; exact hi))
 · change i<FastInv.tabWords.length at hi
   rw [NttR.tabWordsI_length] at hi
   rw [show tableSyms "VG_MLKEM16_INTT_ZETAS"=0x230000 by rfl]
   have hx := tableMem_word (n:=3) (i:=i) (by decide) (by omega_using [hi])
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero,List.getD_cons_succ] at hx
   exact hx.trans (constMem_held _ _ (by rw [NttR.tabWordsI_length]; decide) i (by rw [NttR.tabWordsI_length]; exact hi))
 · change i<Fast.tabWords.length at hi
   rw [NttR.tabWords_length] at hi
   rw [show tableSyms "VG_MLKEM16_NTT_ZETAS"=0x240000 by rfl]
   have hx := tableMem_word (n:=4) (i:=i) (by decide) (by omega_using [hi])
   simp only [Nat.reduceMul,Nat.reduceAdd,List.getD_cons_zero,List.getD_cons_succ] at hx
   exact hx.trans (constMem_held _ _ (by rw [NttR.tabWords_length]; decide) i (by rw [NttR.tabWords_length]; exact hi))
end VG.Proof.MlKem.AArch64.Optimized

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64

def addTables (s : State) : State :=
 {s with mem:=tableMem,syms:=tableSyms,rd:=s.rd++Abi.constRegions tableSyms constants}

theorem strip_addTables (s : State) : stripConsts constants (addTables s) =
 {s with mem:=tableMem,syms:=tableSyms} := by
 have hl : (Abi.constRegions tableSyms constants).length=constants.length := by
  simp only [Abi.constRegions,List.length_map]
 simp only [stripConsts,addTables,State.withRegions,List.length_append,hl,Nat.add_sub_cancel,List.take_left]

end VG.Proof.MlKem.AArch64.Optimized

end

end

/-! ### `MlKem.AArch64.Optimized.Entry`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64

theorem keygen_unstrip {P : KemLay} {s : State}
 (h : KeyGen.Pre P (stripConsts constants s)) : KeyGen.Pre P s := by
 refine ⟨?_,h.wr,h.args,h.sp16,h.wf⟩
 exact List.mem_of_mem_take h.rd

theorem kem_unstrip {P : KemLay} {L : Kem.Layout} {s : State}
 (h : Kem.Pre P L (stripConsts constants s)) : Kem.Pre P L s := by
 refine ⟨?_,h.wr,h.args,h.sp16,h.slots,h.scw,h.scl,h.wf⟩
 intro b hb
 exact List.mem_of_mem_take (h.rd b hb)

/-- Entry contracts keep the original mathematical postconditions and public
input relation; the extra hypotheses describe emitted immutable tables. -/
def entryContract (base : Contract isa) : Contract isa where
 pre s := base.pre (stripConsts constants s) ∧ ConstsOk constants 16 s
 post := base.post
 pub s t := base.pub s t ∧ ∀c∈constants,s.syms c.1=t.syms c.1

end VG.Proof.MlKem.AArch64.Optimized

end

end

/-!
# The hashing encapsulation's contract and constant time

`encapsAArch64S`: `encapsAArch64` with the 128 bytes below the stack pointer
the x3 calls use (rather than 16) apart from the buffers, and
`entryContractS`: with the constant tables apart from them too.
-/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Optimized/KeyGenTiming.lean`, which only this module imported.
section

/-! # Constant-time key generation under the emitted read-only table contract -/
section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.KeyGen
variable {P : KemLay} {keccak : Sha3.AArch64.Permutation}

theorem entry_symbols {base : Contract isa} {s u : State} (h : (entryContract base).pub s u) :
    (s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE") ∧
    ∀name∈restSymbols,s.syms name=u.syms name := by
  refine ⟨h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inl rfl),?_⟩
  intro name hn
  simp only [restSymbols,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl|rfl
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inl rfl))
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end VG.Proof.MlKem.AArch64.Optimized
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps (enL ekE rhoE)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {P : KemLay}

/-- `encapsAArch64 P`, with 128 bytes of stack. -/
def encapsAArch64S (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let ek : Region := ⟨s.gpr .x0, P.ekLen⟩
    let msg : Region := ⟨s.gpr .x1, 32⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let ct : Region := ⟨s.gpr .x3, P.ctLen⟩
    let scratch : Region := ⟨s.gpr .x4, P.scl⟩
    let stack : Region := ⟨s.sp - 128, 128⟩
    ek ∈ s.rd ∧ msg ∈ s.rd ∧ s.wr = [key, ct, scratch] ∧ ek.Disjoint key ∧ ek.Disjoint ct ∧
    ek.Disjoint scratch ∧ msg.Disjoint key ∧ msg.Disjoint ct ∧ msg.Disjoint scratch ∧ key.Disjoint ct ∧
    key.Disjoint scratch ∧ ct.Disjoint scratch ∧ 128 ≤ s.sp.toNat ∧ stack.Disjoint ek ∧ stack.Disjoint msg ∧
    stack.Disjoint key ∧ stack.Disjoint ct ∧ stack.Disjoint scratch
  post := (encapsAArch64 P).post
  pub := (encapsAArch64 P).pub

theorem preS {s : State} (h : (encapsAArch64S P).pre s) : (encapsAArch64 P).pre s ∧ Stk128 P (enL P) s := by
  obtain ⟨rd0, rd1, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, sp128, k0, k1, k2, k3, k4⟩ := h
  have sub : Region.Sub ⟨s.sp - 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  refine ⟨⟨rd0, rd1, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, by omega_using [sp128],
    k0.sub_left sub, k1.sub_left sub, k2.sub_left sub, k3.sub_left sub, k4.sub_left sub⟩, sp128, ?_⟩
  intro b hb
  have hb : b < 5 := hb
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl
  · exact k0
  · exact k1
  · exact k2
  · exact k3
  · exact k4

/-- `entryContract`, with the tables apart from 128 bytes of stack. -/
def entryContractS (base : Contract isa) : Contract isa where
  pre s := base.pre (stripConsts constants s) ∧ ConstsOk constants 128 s
  post := base.post
  pub s t := base.pub s t ∧ ∀c∈constants,s.syms c.1=t.syms c.1

theorem consts16 {s : State} (h : ConstsOk constants 128 s) : ConstsOk constants 16 s ∧ TStk s := by
  have sub : Region.Sub ⟨s.sp - BitVec.ofNat 64 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  have st : ∀ t ∈ constRegs constants s, t.Disjoint (frame s.sp) := fun t ht =>
    (h.2.2.1 t ht).2.2 _ (by simp [abi, stackBelow])
  refine ⟨⟨h.1, h.2.1, fun t ht => ⟨(h.2.2.1 t ht).1, (h.2.2.1 t ht).2.1, fun r hr => ?_⟩, h.2.2.2⟩, ?_⟩
  · simp only [abi, stackBelow, List.mem_singleton] at hr
    subst hr
    exact (st t ht).sub_right sub
  · have mem : ∀ {r : Region}, r ∈ constRegs constants s → r.Disjoint (frame s.sp) := fun hr => st _ hr
    refine ⟨mem ?_, mem ?_, mem ?_, mem ?_, mem ?_⟩ <;> rw [constants_regions] <;> simp [Impl.MlKem.AArch64.Ntt16.Fast.name, Impl.MlKem.AArch64.Ntt16.FastInv.name]

theorem entryS_tables {base : Contract isa} {s : State} (h : (entryContractS base).pre s) :
    Tables s ∧ TStk s :=
  let c := consts16 h.2
  ⟨tables_of_consts c.1, c.2⟩

theorem entryS_symbols {base : Contract isa} {s u : State} (h : (entryContractS base).pub s u) :
    (s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE") ∧
    ∀name∈restSymbols,s.syms name=u.syms name :=
  entry_symbols (base := base) h

end VG.Proof.MlKem.AArch64.Hybrid
