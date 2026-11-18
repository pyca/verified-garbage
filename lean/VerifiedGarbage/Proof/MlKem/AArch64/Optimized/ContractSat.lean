module

meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
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
