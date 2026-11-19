module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Wipe
public import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.RISCV64
public import VerifiedGarbage.Proof.MlKem.RISCV64.EncapsCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.DecapsCT
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Impl.MlKem1024.RISCV64.Top
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.EncapsHSat
public import VerifiedGarbage.Spec.MlKem.EncapsH
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.MlKem.RISCV64.EncryptCT
import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.RowSum
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.MlKem.RISCV64.EncryptCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.RowSum
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.RISCV64.KemLay
public import VerifiedGarbage.Proof.MlKem.RISCV64.Lay
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
meta import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.Decompress
import VerifiedGarbage.Proof.MlKem.RISCV64.Calls
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.MlKem.RISCV64.KemLay
meta import VerifiedGarbage.Proof.MlKem1024.RISCV64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.RISCV64.Decompress
meta import VerifiedGarbage.Impl.MlKem1024.RISCV64.Top
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Calls
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Covers

/-! ### `MlKem1024.RISCV64.Calls`, which only this module used -/

section

/-!
# ML-KEM-1024 on RISC-V: the parameter set

As on PPC64LE (`Proof/MlKem/PPC64LE/CallWipe.lean`): key generation,
encapsulation and decapsulation are the functions of
`Impl/MlKem/RISCV64/Top.lean` for `kl1024`, proven once for any parameter set
(`Proof/MlKem/RISCV64/`). What they need of `kl1024` it proves here: its
well-formedness (`kl1024_wf`, by `decide`), and what `KemLay.CallsOk` asks of
its code (`kl1024_calls`). As `Proof/MlKem/RISCV64/Calls.lean` and
`CallsCT.lean` for the other primitives: a contract written with the
precondition of the proof of `vg_mlkem1024_compress_encode` (and of
`vg_mlkem1024_decode_decompress`) and what it shows, the call of it with its
arguments at offsets in the buffers of a layout (`compressL4`,
`decompressL4`), and that it is constant time from any state whose argument
registers are public (`compress4T`, `decompress4T`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64 VG.Impl.MlKem1024.RISCV64
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.RISCV64

/-! ## `vg_mlkem1024_compress_encode`, `vg_mlkem1024_decode_decompress` -/

def kCmp4 : Contract isa := mkK CompressEncode.Pre
  (fun s₀ s => bytesAt s.mem (CompressEncode.O s₀) (CompressEncode.L s₀) = CompressEncode.E s₀)
  (regsEq [.a0, .a1, .a2, .a3])

theorem kCmp4_ok : ∀ s, kCmp4.pre s → ∃ t s', Exec isa compressEncode1024 s t s' ∧
    abiPreserved s s' ∧ kCmp4.post s s' :=
  mkK_ok fun _ hp => WP.mono (CompressEncode.correct hp) fun _ ⟨h1, h2, h3, h⟩ =>
    ⟨h1, h2, h3, bytesAt_eq! (compressEncode_length _ _ ▸ hp.len.symm) h⟩

def kDcm4 : Contract isa := mkK Decompress.Pre
  (fun s₀ s => PolyIs s.mem (Decompress.F s₀) (Decompress.D s₀)) (regsEq [.a0, .a1, .a2, .a3])

theorem kDcm4_ok : ∀ s, kDcm4.pre s → ∃ t s', Exec isa decodeDecompress1024 s t s' ∧
    abiPreserved s s' ∧ kDcm4.post s s' :=
  mkK_ok fun s₀ hp => WP.mono (Decompress.correct hp) fun _ ⟨h1, h2, h3, h⟩ =>
    ⟨h1, h2, h3, polyIs_of_coeffAt (p := Decompress.F s₀) fun j hj => by
      rw [h j (by rw [VG.Proof.MlKem.n_eq] at hj; exact hj)]; rfl⟩

theorem width_lt4 {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) : d < 2 ^ 32 ∧ 32 * d < 2 ^ 32 := by
  rcases mem_compressWidths1024 hd with rfl | rfl <;> decide

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `(i, o)` into the `32 d` bytes at `(j, o')`. -/
theorem compressL4 {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = BitVec.ofNat 64 d)
    (g5 : s.gpr .a2 = L.A j o') (g6 : s.gpr .a3 = BitVec.ofNat 64 (32 * d))
    (hd : d ∈ Proof.MlKem1024.compressWidths) (hs : sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {f : Poly} (hf : PolyIs s.mem (L.A i o) f)
    (ai : L.Al i o) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' → bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f →
      Q s') :
    WP isa kl1024.callCU s Q := by
  have ⟨d1, d2⟩ := width_lt4 hd
  have hd0 : 0 < 32 * d := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  let V := view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]
  have eF : CompressEncode.F V = L.A i o := by simp only [V, CompressEncode.F, view_r3, g3]
  have eO : CompressEncode.O V = L.A j o' := by simp only [V, CompressEncode.O, view_r5, g5]
  have eD : CompressEncode.dN V = d := by simp only [V, CompressEncode.dN, view_r4, g4, dN_eq d1]
  have eL : CompressEncode.L V = 32 * d := by simp only [V, CompressEncode.L, view_r6, g6, len_eq d2]
  have cw : Covers [⟨L.A j o', 32 * d⟩] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  have hpre : CompressEncode.Pre V :=
    ⟨by simp only [V, eF, State.withRegions_rd], by simp only [V, CompressEncode.outR, eO, eL, State.withRegions_wr],
      by simp only [CompressEncode.outR, eF, eO, eL]; exact Lay.disj hL hs,
      by rw [eF]; exact Lay.fitB hL (sepB_bounds hs) (by decide),
      by rw [eO, eL]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) hd0,
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact hf.1, by rw [eF]; exact ai.four⟩
  refine call_kept (k := kCmp4) kCmp4_ok (by decide +kernel) (rd := [polyRegion (L.A i o)])
    (wr := [⟨L.A j o', 32 * d⟩]) hpre
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  have hq' : bytesAt (s'.withRegions _ _).mem (CompressEncode.O V) (CompressEncode.L V) = CompressEncode.E V := hq
  simp only [CompressEncode.E, CompressEncode.P, eF, eO, eL, eD, State.withRegions_mem, V,
    State.callEntry_mem, hf.2] at hq'
  exact hq'

/-- `Decompress_d(ByteDecode_d(·))` of the `32 d` bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decompressL4 {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g3 : s.gpr .a0 = L.A i o) (g4 : s.gpr .a1 = BitVec.ofNat 64 (32 * d))
    (g5 : s.gpr .a2 = BitVec.ofNat 64 d) (g6 : s.gpr .a3 = L.A j o')
    (hd : d ∈ Proof.MlKem1024.compressWidths) (hs : sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) (aj : L.Al j o') {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') :
    WP isa kl1024.callDU s Q := by
  have ⟨d1, d2⟩ := width_lt4 hd
  have hd0 : 0 < 32 * d := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  let V := view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]
  have eB : Decompress.B V = L.A i o := by simp only [V, Decompress.B, view_r3, g3]
  have eF : Decompress.F V = L.A j o' := by simp only [V, Decompress.F, view_r6, g6]
  have eD : Decompress.dN V = d := by simp only [V, Decompress.dN, view_r5, g5, dN_eq d1]
  have eL : Decompress.L V = 32 * d := by simp only [V, Decompress.L, view_r4, g4, len_eq d2]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  have hpre : Decompress.Pre V :=
    ⟨by simp only [V, Decompress.inR, eB, eL, State.withRegions_rd], by simp only [V, eF, State.withRegions_wr],
      by simp only [Decompress.inR, eB, eF, eL]; exact Lay.disj hL hs,
      by rw [eB, eL]; exact Lay.fitB hL (sepB_bounds hs) hd0,
      by rw [eF]; exact Lay.fitB hL (sepB_bounds (sepB_symm hs)) (by decide),
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact aj.four⟩
  refine call_kept (k := kDcm4) kDcm4_ok (by decide +kernel) (rd := [⟨L.A i o, 32 * d⟩])
    (wr := [polyRegion (L.A j o')]) hpre
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  have hq' : PolyIs (s'.withRegions _ _).mem (Decompress.F V) (Decompress.D V) := hq
  simp only [Decompress.D, Decompress.Bl, eB, eF, eL, eD, State.withRegions_mem, V,
    State.callEntry_mem] at hq'
  exact hq'

theorem compress4T :
    ConstantTime isa (fun _ => True) (regsEq [.a0, .a1, .a2, .a3]) compressEncode1024 := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.seq (VG.Proof.MlKem.RISCV64.CompressEncode.zext_rel.mono (fun s₁ s₂ ⟨_, _, hsp, hr⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)))
  refine ⟨hsp, fun r hm => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp),
    by rw [hr .a1 (by simp)]⟩

theorem decompress4T :
    ConstantTime isa (fun _ => True) (regsEq [.a0, .a1, .a2, .a3]) decodeDecompress1024 := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.seq (VG.Proof.MlKem.RISCV64.DecodeDecompress.zext_rel.mono (fun s₁ s₂ ⟨_, _, hsp, hr⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)))
  refine ⟨hsp, fun r hm => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rcases hm with rfl | rfl | rfl <;> simp),
    by rw [hr .a2 (by simp)]⟩

/-! ## The parameter set -/

theorem kl1024_wf : kl1024.WF := .of (by decide)

theorem kl1024_calls : kl1024.CallsOk :=
  ⟨fun hL _ _ _ _ _ g3 g4 g5 g6 hd => compressL4 hL g3 g4 g5 g6 (by rcases hd with rfl | rfl <;> decide),
    fun hL _ _ _ _ _ g3 g4 g5 g6 hd => decompressL4 hL g3 g4 g5 g6 (by rcases hd with rfl | rfl <;> decide),
    compress4T, decompress4T, fun t => by cases t <;> exact ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.MlKem1024.RISCV64

end

end

/-! ### `MlKem.RISCV64.KeyGenCT`, which only this module used -/

section

/-! ### `MlKem.RISCV64.KeyGen`, which this module and modules that import it used -/

section

/-!
# ML-KEM on RISC-V: key generation, correctness

As on PPC64LE (`Proof/MlKem/PPC64LE/KeyGenCT.lean`): `K.keygen` for any
parameter set `K` (`KemLay.WF`). The buffers of the function (`lay`):
`scratch`, the stack, `seed`, `ek` and `dk`; what every phase keeps (`KEnv`:
the pointers, our caller's registers in `scratch`, the seed); and the
phases: the setup, `G(d ‖ k)` into `ρ` and `σ`, the `PRF`s into `ŝ` and `ê`,
the rows of `t̂ = Â ∘ ŝ + ê` encoded into `ek`, `ŝ` encoded into `dk`, the
copies of `ρ`, `ek` and `z`, and `H(ek)`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.KeyGen

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64.Enc (bytes_catK catK_congr flagInit_ok ptrSlot_ok)
open VG.Impl.Sha3.RISCV64.Stream (mov)

section
variable (s₀ : State)

abbrev pSeed : Addr := s₀.gpr .a0
abbrev pEk : Addr := s₀.gpr .a1
abbrev pDk : Addr := s₀.gpr .a2
abbrev pScr : Addr := s₀.gpr .a3

/-- The buffers: `scratch`, the 1168 bytes below the stack pointer, `seed`,
`ek` and `dk`. -/
def lay (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 1168, pSeed s₀, pEk s₀, pDk s₀].getD i 0,
    [K.scratch, 1168, 64, K.ekLen, K.dkLen]⟩

end

/-- The sizes of the buffers. -/
abbrev kSz (K : KemLay) : List Nat := [K.scratch, 1168, 64, K.ekLen, K.dkLen]

theorem lay_sizes (K : KemLay) (s₀ : State) : (lay s₀ K).sizes = kSz K := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  al : s.sp.toNat % 16 = 0
  sp1168 : 1168 ≤ s.sp.toNat
  rd : s.rd = [⟨pSeed s, 64⟩]
  wr : s.wr = [⟨pEk s, K.ekLen⟩, ⟨pDk s, K.dkLen⟩, ⟨pScr s, K.scratch⟩]
  d_se : (⟨pSeed s, 64⟩ : Region).Disjoint ⟨pEk s, K.ekLen⟩
  d_sd : (⟨pSeed s, 64⟩ : Region).Disjoint ⟨pDk s, K.dkLen⟩
  d_ss : (⟨pSeed s, 64⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_ed : (⟨pEk s, K.ekLen⟩ : Region).Disjoint ⟨pDk s, K.dkLen⟩
  d_es : (⟨pEk s, K.ekLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_ds : (⟨pDk s, K.dkLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  b_s : (below s.sp 1168).Disjoint ⟨pSeed s, 64⟩
  b_e : (below s.sp 1168).Disjoint ⟨pEk s, K.ekLen⟩
  b_d : (below s.sp 1168).Disjoint ⟨pDk s, K.dkLen⟩
  b_c : (below s.sp 1168).Disjoint ⟨pScr s, K.scratch⟩
  f_s : (pSeed s).toNat + 64 ≤ 2 ^ 64
  f_e : (pEk s).toNat + K.ekLen ≤ 2 ^ 64
  f_d : (pDk s).toNat + K.dkLen ≤ 2 ^ 64
  f_c : (pScr s).toNat + K.scratch ≤ 2 ^ 64
  alS : (pScr s).toNat % 8 = 0

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem stack_fit : (s₀.sp - BitVec.ofNat 64 1168).toNat + 1168 ≤ 2 ^ 64 := by
  have := hp.sp1168
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this]), BitVec.toNat_ofNat]
  have := s₀.sp.isLt; omega_using []

theorem lay_ok : (lay s₀ K).Ok := by
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · exact stack_fit hp
    · exact hp.f_s
    · exact hp.f_e
    · exact hp.f_d
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega_using [hj, hij] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega_using [hj, hij] : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · exact hp.b_c.symm
    · exact hp.d_ss.symm
    · exact hp.d_es.symm
    · exact hp.d_ds.symm
    · exact hp.b_s
    · exact hp.b_e
    · exact hp.b_d
    · exact hp.d_se
    · exact hp.d_sd
    · exact hp.d_ed

end

/-- What every phase keeps: the pointers, the callee-saved registers we do
not save, our caller's registers in `scratch`, and the seed. -/
structure KEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀ K) s
  s10 : s.gpr .s10 = pSeed s₀
  s9 : s.gpr .s9 = pEk s₀
  s8 : s.gpr .s8 = pDk s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r
  sav : TopSaved s.mem (pScr s₀) s₀
  seed : bytesAt s.mem ((lay s₀ K).A 2 0) 64 = bytesAt s₀.mem ((lay s₀ K).A 2 0) 64

/-- A region the phases may change: apart from the saved registers and the seed. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := sepB (kSz K) (0, 1288, 80) w && sepB (kSz K) (2, 0, 64) w

/-- The buffer of each pointer register. -/
def kidx : Reg → Nat
  | .s10 => 2 | .s9 => 3 | .s8 => 4 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
tactic_template "ldecide" : tactic => `(tactic| first
                   | decide
                   | ((try simp only [lay_sizes, kSz, kidx, okW, kRegs, List.all_cons, List.all_nil, List.all_append,
                         List.map_cons, List.map_nil, trip, Bool.and_true])
                      (try have := (‹KemLay.WF _›).scr)
                      kdecide))

theorem saveR_eq (K : KemLay) (s₀ : State) : saveR (pScr s₀) = (lay s₀ K).R 0 1288 80 := rfl

theorem KEnv.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : KEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .s10 ∧ x ≠ .s9 ∧ x ≠ .s8 ∧ x ≠ .s11) (hW : W.all (okW K) = true) :
    KEnv K s₀ s' := by
  have hL := lay_ok hp
  have h1 : sepAll (lay s₀ K).sizes (0, 1288, 80) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀ K).sizes (2, 0, 64) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have nx : ∀ r, r = .s10 ∨ r = .s9 ∨ r = .s8 ∨ r = .s11 → r ∉ xs := fun r hr hm => by
    obtain ⟨-, a, b, c, d⟩ := hx r hm
    rcases hr with rfl | rfl | rfl | rfl <;> simp_all
  refine ⟨hk.ctx (nx _ (by simp)) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun r hr hs => ?_, h.sav.keep hk.frame (by rw [saveR_eq K]; exact Lay.disjAll hL h1), ?_⟩
  · rw [hk.cs .s10 (by decide) (nx _ (by simp)), h.s10]
  · rw [hk.cs .s9 (by decide) (nx _ (by simp)), h.s9]
  · rw [hk.cs .s8 (by decide) (nx _ (by simp)), h.s8]
  · rw [hk.cs r hr (fun hm => hs (hx r hm).1), h.cs r hr hs]
  · rw [Lay.bytes_keep hL hk.frame h2 (by decide)]; exact h.seed

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 4 ∈ s₀.wr ∧
      (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay]

/-! ## The setup -/

theorem setup_ok {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa (.block K.kgSetup) s₀ fun s => KEnv K s₀ s ∧ s.mem ((lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k := by
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₀.wr (pScr s₀ + BitVec.ofNat 64 o) n := fun h =>
    Lay.covers w0 (by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [scr, h]) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [KemLay.kgSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok rfl hp.alS fun o _ h₂ => wS (by omega_using [h₂]))
    fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .a0 = pSeed s₀ := by rw [g₁]
  have g4 : s₁.gpr .a1 = pEk s₀ := by rw [g₁]
  have g5 : s₁.gpr .a2 = pDk s₀ := by rw [g₁]
  have g6 : s₁.gpr .a3 = pScr s₀ := by rw [g₁]
  have i1184 : InRegions s₁.wr (pScr s₀ + BitVec.ofNat 64 oK) 1 := by rw [wr₁]; exact wS (by decide)
  have ek : K.k < 2048 := by have := hK.k4; omega_using [this]
  have sk := setWidth8_ofNat (N := K.k) (by omega_using [ek])
  have hmv : WP isa (.block [mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s11 .a3, .li .t0 K.k,
      .store .b .t0 .s11 oK]) s₁ fun s =>
      s.gpr .s10 = pSeed s₀ ∧ s.gpr .s9 = pEk s₀ ∧ s.gpr .s8 = pDk s₀ ∧ s.gpr .s11 = pScr s₀ ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem.writeW (pScr s₀ + BitVec.ofNat 64 oK) (BitVec.ofNat 8 K.k) ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp :=
    wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => wp_li ek fun u₅ h₅ =>
      wp_sb (a := pScr s₀ + BitVec.ofNat 64 oK) (by decide)
        (by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g6])
        (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact i1184) fun u₆ m₆ => WP.block_nil
        ⟨by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g3],
          by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g4],
          by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g5],
          by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g6],
          fun r hr hs => by
            have h0 := (pres_ne hr).1
            simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
            obtain ⟨-, -, -, -, -, a8, a9, a10, a11⟩ := hs
            simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, a8, a9, a10, a11, h0,
              ↓reduceIte],
          by rw [m₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₅.gpr, sk],
          by rw [m₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [m₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
          by rw [m₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, cs, m, rd, wr, sp⟩ => ?_
  have c1184 : ((lay s₀ K).R 0 1184 1).Contains (pScr s₀ + BitVec.ofNat 64 oK) (8 / 8) :=
    Region.contains_self _ _
  have fr' : Frame ((lay s₀ K).RL [(0, 1288, 80), (0, 1184, 1)]) s₀.mem s.mem := by
    rw [m]
    exact (fr.mono (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp [saveR_eq K])).writeW
      (by simp) _ c1184
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp1168, by rw [sp, sp₁]; exact hp.al,
    hp.alS, by rw [sp, sp₁]; rfl, by rw [wr, wr₁, hp.wr]; simp [lay]⟩, g30, g29, g28, rd.trans rd₁, wr.trans wr₁,
    sp.trans sp₁, fun r hr hs => ?_, ?_, ?_⟩, ?_⟩
  · rw [cs r hr hs, g₁]
  · rw [m]
    exact sav.keep ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c1184) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [saveR_eq K]; exact Lay.disj hL (by ldecide))
  · exact Lay.bytes_keep hL fr' (by ldecide) (by decide)
  · show s.mem (pScr s₀ + BitVec.ofNat 64 oK) = _
    rw [m, writeW8_apply, ite_eq_left rfl]

/-! ## Pieces of the hashes -/

theorem pieceK {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .s10 ∨ p.base = .s9 ∨ p.base = .s8 ∨ p.base = .s11) (hw : w = true → p.base ≠ .s10)
    (hoe : p.off < 32768) (hle : p.len < 2048) (hpos : 0 < p.len)
    (hsep : sepAll (kSz K) (kidx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀ K) kidx s w p := by
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  rw [← h.wr] at w0 w3 w4
  rw [← h.wr, ← h.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hsep, ?_⟩
  · rcases hb with e | e | e | e <;> rw [e] <;> decide
  · rcases hb with e | e | e | e <;> rw [e]
    · exact h.s10
    · exact h.s9
    · exact h.s8
    · exact h.ctx.s11
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e | e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w3
      · exact mem_rd_wr w4
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rcases hb with e | e | e | e
      · exact absurd e (hw rfl)
      all_goals rw [e]
      · exact w3
      · exact w4
      · exact w0

/-! ## `G(d ‖ k)` -/

/-- `d`, the first half of the seed. -/
abbrev D (s₀ : State) : List Byte := bytesAt s₀.mem (pSeed s₀) 32

/-- `z`, the second half of the seed. -/
abbrev Z (s₀ : State) : List Byte := bytesAt s₀.mem (pSeed s₀ + BitVec.ofNat 64 32) 32

theorem g_ins {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s10, 0, 32⟩ : Piece), ⟨.s11, oK, 1⟩], PieceOk (lay s₀ K) kidx s false p := by
  have hK := hp.wf
  intro p hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · exact pieceK hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by ldecide)
  · exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by ldecide)

theorem g_outs {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s11, oG, 64⟩ : Piece)], PieceOk (lay s₀ K) kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by ldecide)

theorem g_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (h3 : s.mem ((lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k) :
    WP isa (hash 72 0x06 [⟨.s10, 0, 32⟩, ⟨.s11, oK, 1⟩] [⟨.s11, oG, 64⟩]) s fun s' =>
      KEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀) := by
  have hK := hp.wf
  have hin := g_ins hp h
  have hout := g_outs hp h
  have hD : bytesAt s.mem ((lay s₀ K).A 2 0) 32 = D s₀ := by
    have := congrArg (List.take 32) h.seed
    rw [bytesAt_take _ _ (by decide), bytesAt_take _ _ (by decide)] at this
    rw [this]; show bytesAt s₀.mem (pSeed s₀ + BitVec.ofNat 64 0) 32 = _; rw [BitVec.add_zero]
  have hin' : (List.map ((lay s₀ K).pb kidx s.mem) [⟨.s10, 0, 32⟩, ⟨.s11, oK, 1⟩]).flatten =
      D s₀ ++ [BitVec.ofNat 8 K.k] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀ K).A 2 0) 32 ++ bytesAt s.mem ((lay s₀ K).A 0 oK) 1 = _
    rw [hD, bytes_one, h3]
  refine WP.mono (hash_ok VG.Proof.MlKem.rate72 (by decide) h.ctx (List.cons_ne_nil _ _) hin hout
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by ldecide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((lay s₀ K).A 0 oG) 64 = (G (D s₀ ++ [BitVec.ofNat 8 K.k])).1 ++
        (G (D s₀ ++ [BitVec.ofNat 8 K.k])).2 := e1.trans (G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((lay s₀ K).A 0 oG) 32).length = (G (D s₀ ++ [BitVec.ofNat 8 K.k])).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem ((lay s₀ K).ptr 0 + BitVec.ofNat 64 (920 + 32)) 32 = _
    rw [← ptr_add]; exact r2

theorem rho_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀))
    (hs : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) :
    WP isa (copy .s11 oG .s11 oSeed 32) s fun s' => KEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀) := by
  have hL := lay_ok hp
  have hK := hp.wf
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  refine WP.mono (copyL hL (i := 0) (j := 0) (by decide) (by decide) h.ctx.s11 h.ctx.s11
    (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w0)) fun s' ⟨k', b'⟩ =>
    ⟨h.keep hp (k'.x []) (by simp) (by ldecide), b'.trans hr,
      (Lay.bytes_keep hL k'.frame (by ldecide) (by decide)).trans hs⟩

/-! ## The `PRF`s -/

theorem prf_phase {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀))
    (hs : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) :
    WP isa (K.prfLoop true 0 (2 * K.k)) s fun s' => KEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      ∀ N < 2 * K.k, PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
        (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N)) := by
  have hK := hp.wf
  exact WP.mono (prfLoop_ok hK h.ctx true (by have := hK.k1; omega_using [this]) (by omega_using []) hs) fun s' ⟨k', p'⟩ =>
    ⟨h.keep hp k' (by simp [savedTop]) (by ldecide),
      by rw [← hr]; exact Lay.bytes_keep (lay_ok hp) k'.frame (by ldecide) (by decide),
      fun N hN => p' N (Nat.zero_le _) hN⟩

/-! ## Pointers into `ek` and `dk` -/

/-- `a0` at polynomial `j` of `scratch`, `a1` at `b + 384 i`. -/
theorem ptrMul_ok {s : State} {P B : BitVec 64} {b : Reg} {i j : Nat} (hb : b = .s9 ∨ b = .s8)
    (h11 : s.gpr .s11 = P) (hB : s.gpr b = B) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) (hj : j + 2 < 2048) :
    WP isa (.block (polyAddr .a0 j ++ atMul .a1 b .s6 384)) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 (oPoly j) ∧ s'.gpr .a1 = B + BitVec.ofNat 64 (384 * i) := by
  have hb0 : b ≠ .t0 := by rcases hb with rfl | rfl <;> decide
  have hba : b ≠ .a0 := by rcases hb with rfl | rfl <;> decide
  rw [← List.append_nil (atMul .a1 b .s6 384)]
  refine wp_polyAddr hj (by decide) fun s₁ h₁ => wp_atMul (by decide) hb0 (by decide) fun s₂ u₂ => WP.block_nil
    ⟨⟨fun r hr => ?_, by rw [u₂.mem, h₁.mem], by rw [u₂.rd, h₁.rd], by rw [u₂.wr, h₁.wr], by rw [u₂.sp, h₁.sp]⟩,
      ?_, ?_⟩
  · obtain ⟨n0, n1, n2, -, -, -⟩ := pres_ne hr
    rw [u₂.other _ n2 n0, h₁.other _ n1]
  · rw [u₂.other _ (by decide) (by decide), h₁.gpr, h11]
  · rw [u₂.gpr, h₁.other _ hba, h₁.other _ (by decide), hB, h6, mul_eq]

/-- `a0` at polynomial `i` of the array from polynomial `j`, `a1` at `b + 384 i`. -/
theorem slotMul_ok {s : State} {P B : BitVec 64} {b : Reg} {i j : Nat} (hb : b = .s9 ∨ b = .s8)
    (h11 : s.gpr .s11 = P) (hB : s.gpr b = B) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) (hj : j + 2 < 2048)
    (hi : i + j + 2 < 2 ^ 50) :
    WP isa (.block (slotAt .a0 .s6 j ++ atMul .a1 b .s6 384)) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 (oPoly j + 1024 * i) ∧
      s'.gpr .a1 = B + BitVec.ofNat 64 (384 * i) := by
  have hb0 : b ≠ .t0 := by rcases hb with rfl | rfl <;> decide
  have hba : b ≠ .a0 := by rcases hb with rfl | rfl <;> decide
  rw [← List.append_nil (atMul .a1 b .s6 384)]
  refine wp_slotAt hj hi (by decide) h6 fun s₁ h₁ => wp_atMul (by decide) hb0 (by decide) fun s₂ u₂ =>
    WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₂.mem, h₁.mem], by rw [u₂.rd, h₁.rd], by rw [u₂.wr, h₁.wr],
      by rw [u₂.sp, h₁.sp]⟩, ?_, ?_⟩
  · obtain ⟨n0, n1, n2, -, -, -⟩ := pres_ne hr
    rw [u₂.other _ n2 n0, h₁.other _ n1]
  · rw [u₂.other _ (by decide) (by decide), h₁.gpr, h11]
  · rw [u₂.gpr, h₁.other _ hba, h₁.other _ (by decide), hB, h6, mul_eq]

/-! ## The rows of `t̂` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ρ`. -/
abbrev ρ₀ : List Byte := VG.Proof.MlKem.KPke.kgRho K.p (D s₀)

/-- `ŝ`. -/
abbrev sK : Nat → Poly := VG.Proof.MlKem.KPke.kgS K.p (D s₀)

/-- The entries of `Â` the products use. -/
abbrev aK (i j : Nat) : Poly := effA false (ρ₀ K s₀) i j (sK K s₀ j)

/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
def okK (i : Nat) : Bool := (List.range i).all fun i' => okRow false (ρ₀ K s₀) i' K.k

/-- `t̂`. -/
abbrev tK : Nat → Poly := VG.Proof.MlKem.KPke.kgT K.p (aK K s₀) (D s₀)

end

theorem okK_succ (K : KemLay) (s₀ : State) (i : Nat) :
    okK K s₀ (i + 1) = (okK K s₀ i && okRow false (ρ₀ K s₀) i K.k) := by
  simp only [okK, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- After the first `i` rows. -/
structure KRow (K : KemLay) (s₀ : State) (i : Nat) (s : State) : Prop where
  env : KEnv K s₀ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 i
  s4 : s.gpr .s4 = if okK K s₀ i then 1 else 0
  rho : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀
  slots : ∀ N < 2 * K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
    (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N))
  ek : ∀ i' < i, bytesAt s.mem ((lay s₀ K).A 3 (384 * i')) 384 = encode12 (tK K s₀ i')

/-- What a row changes. -/
abbrev rowK (K : KemLay) (i : Nat) : List (Nat × Nat × Nat) :=
  [(0, 1280, 2), (0, K.oAcc, 3072), (0, K.oSample, 3072), (1, 0, 1168), (0, K.oAcc, 1024), (3, 384 * i, 384)]

/-- `rowK_ok` with the sizes `sz` of the buffers. -/
abbrev RowKF (K : KemLay) (sz : List Nat) : Prop := ∀ i < K.k,
    (rowK K i).all (fun w => sepB sz (0, 1288, 80) w && sepB sz (2, 0, 64) w) = true ∧
    sepAll sz (0, oSeed, 32) (rowK K i) = true ∧
    (∀ N < 2 * K.k, sepAll sz (0, oPoly (K.k + N), 1024) (rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → sepAll sz (3, 384 * i', 384) (rowK K i) = true) ∧
    sepB sz (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    sepB sz (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true

theorem rowK_ok {K : KemLay} (hK : K.WF) {i : Nat} (hi : i < K.k) : (rowK K i).all (okW K) = true ∧
    sepAll (kSz K) (0, oSeed, 32) (rowK K i) = true ∧
    (∀ N < 2 * K.k, sepAll (kSz K) (0, oPoly (K.k + N), 1024) (rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → sepAll (kSz K) (3, 384 * i', 384) (rowK K i) = true) ∧
    sepB (kSz K) (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    sepB (kSz K) (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, RowKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega_using [this]) i hi
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, sepAll_scr c2 scr, fun N hN => sepAll_scr (c3 N hN) scr,
    fun i' hi' hne => sepAll_scr (c4 i' hi' hne) scr, sepB_scr c5 scr, sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [okW, Bool.and_eq_true] at this ⊢
  exact ⟨sepB_scr this.1 scr, sepB_scr this.2 scr⟩

/-- The row's facts at its start `s`, for its `RowSum`. -/
theorem KRow.rowPre {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : KRow K s₀ i s) : RowPre K (lay s₀ K) (ρ₀ K s₀) (sK K s₀) i (okK K s₀ i) s :=
  ⟨hp.wf, h.env.ctx, hi, h.s6, h.s4, h.rho, fun j hj => h.slots j (by omega_using [hj])⟩

section
variable (K : KemLay) (s₀ : State) (i : Nat) (s : State)

/-- After the arguments of `t̂[i] += ê[i]`. -/
structure KR2 (s₂ : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s₂
  s6 : s₂.gpr .s6 = BitVec.ofNat 64 i
  a0 : s₂.gpr .a0 = (lay s₀ K).A 0 K.oAcc
  a1 : s₂.gpr .a1 = (lay s₀ K).A 0 (oPoly (K.k + (K.k + i)))
  s4 : s₂.gpr .s4 = if okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₂.mem ((lay s₀ K).A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (aK K s₀ i) (sK K s₀) K.k)

/-- After `t̂[i]`. -/
structure KR3 (s₃ : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s₃
  s6 : s₃.gpr .s6 = BitVec.ofNat 64 i
  s4 : s₃.gpr .s4 = if okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₃.mem ((lay s₀ K).A 0 K.oAcc) (tK K s₀ i)

/-- After the arguments of its encoding. -/
structure KR4 (s₄ : State) : Prop where
  a0 : KR3 K s₀ i s s₄
  a3 : s₄.gpr .a0 = (lay s₀ K).A 0 K.oAcc
  a4 : s₄.gpr .a1 = (lay s₀ K).A 3 (384 * i)

/-- After its encoding. -/
structure KR5 (s₅ : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s₅
  s6 : s₅.gpr .s6 = BitVec.ofNat 64 i
  s4 : s₅.gpr .s4 = if okK K s₀ (i + 1) then 1 else 0
  enc : bytesAt s₅.mem ((lay s₀ K).A 3 (384 * i)) 384 = encode12 (tK K s₀ i)

end

theorem KRow.ctxOf {K : KemLay} {s₀ : State} {i : Nat} {s : State} (h : KRow K s₀ i s) {x : State} {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (k : KeptX xs ((lay s₀ K).RL W) s x) (h31 : Reg.s11 ∉ xs) : Ctx (lay s₀ K) x :=
  k.ctx h31 h.env.ctx

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State} (h : KRow K s₀ i s)
include hp hi h

theorem kr2_ok {s₁ : State}
    (r : RowInv K (lay s₀ K) false (ρ₀ K s₀) (sK K s₀) i (okK K s₀ i) s K.k s₁) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ slotAt .a1 .s6 (2 * K.k))) s₁ (KR2 K s₀ i s) := by
  have hK := hp.wf
  have hc₁ := h.ctxOf r.kx (by decide)
  have g26₁ : s₁.gpr .s6 = BitVec.ofNat 64 i := by rw [r.kx.cs .s6 (by decide) (by decide), h.s6]
  refine WP.mono (ptrSlot_ok (i := i) hc₁.s11 g26₁ (by offs) (by offs) (by offs)) fun s₂ ⟨o₂, a3, a4⟩ => ?_
  rw [show oPoly (2 * K.k) + 1024 * i = oPoly (K.k + (K.k + i)) by offs] at a4
  exact ⟨((r.kx.weaken (by simp)).monoL (by simp)).trans (o₂.x _ _),
    by rw [o₂.cs .s6 (by decide), g26₁], a3, a4,
    by rw [o₂.cs .s4 (by decide), r.s4, ← okK_succ],
    by rw [o₂.mem, ← rowAcc_eq]; exact r.acc⟩

theorem kr3_ok {s₂ : State} (r : KR2 K s₀ i s s₂) : WP isa callAdd s₂ (KR3 K s₀ i s) := by
  have hL := lay_ok hp
  have hc₂ := h.ctxOf r.kx (by decide)
  obtain ⟨-, -, c_slots, -, -, c_add⟩ := rowK_ok hp.wf hi
  have sl₂ : PolyIs s₂.mem ((lay s₀ K).A 0 (oPoly (K.k + (K.k + i))))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) (K.k + i))) :=
    Lay.polyIs_keep hL r.kx.frame (c_slots (K.k + i) (by omega_using [hi])) (h.slots (K.k + i) (by omega_using [hi]))
  exact addL hL r.a0 r.a1 c_add hc₂.cw (mem_rd_wr hc₂.cw) r.acc sl₂ (hc₂.alP _) (hc₂.alP _) fun s₃ k₃ p₃ =>
    ⟨r.kx.trans ((k₃.x _).monoL (by simp)), by rw [k₃.cs .s6 (by decide), r.s6],
      by rw [k₃.cs .s4 (by decide), r.s4], p₃⟩

omit hi in
theorem kr4_ok {s₃ : State} (r : KR3 K s₀ i s s₃) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ atMul .a1 .s9 .s6 384)) s₃ (KR4 K s₀ i s) := by
  have hK := hp.wf
  have hc₃ := h.ctxOf r.kx (by decide)
  have g29₃ : s₃.gpr .s9 = pEk s₀ := by rw [r.kx.cs .s9 (by decide) (by decide), h.env.s9]
  refine WP.mono (ptrMul_ok (b := .s9) (.inl rfl) hc₃.s11 g29₃ r.s6 (by offs)) fun s₄ ⟨o₄, b3, b4⟩ =>
    ⟨⟨r.kx.trans (o₄.x _ _), by rw [o₄.cs .s6 (by decide), r.s6],
      by rw [o₄.cs .s4 (by decide), r.s4], by rw [o₄.mem]; exact r.acc⟩, b3, b4⟩

theorem kr5_ok {s₄ : State} (r : KR4 K s₀ i s s₄) : WP isa callEncode12 s₄ (KR5 K s₀ i s) := by
  have hL := lay_ok hp
  have hc₄ := h.ctxOf r.a0.kx (by decide)
  obtain ⟨-, -, -, -, c_enc, -⟩ := rowK_ok hp.wf hi
  obtain ⟨-, w3, -, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 3) (o' := 384 * i) r.a3 r.a4 c_enc (mem_rd_wr hc₄.cw)
    (by rw [r.a0.kx.wr, h.env.wr]; exact w3) r.a0.acc (hc₄.alP _) fun s₅ k₅ e₅ =>
    ⟨r.a0.kx.trans ((k₅.x _).monoL (by simp)), by rw [k₅.cs .s6 (by decide), r.a0.s6],
      by rw [k₅.cs .s4 (by decide), r.a0.s4], e₅⟩

theorem kr6_ok {s₅ : State} (r : KR5 K s₀ i s s₅) :
    WP isa (.block (count .s6 K.k)) s₅ fun s' =>
      KRow K s₀ (i + 1) s' ∧ (s'.gpr .t0 != 0) = decide (i + 1 ≠ K.k) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_slots, c_ek, -, -⟩ := rowK_ok hK hi
  refine WP.mono (count_ok (by decide) (by omega_using [hi, k4]) (by omega_using [k4]) r.s6) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s' :=
    r.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp [savedTop]) c_ok
  · rw [k'.cs .s4 (by decide) (by decide), r.s4]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun N hN => Lay.polyIs_keep hL K'.frame (c_slots N hN) (h.slots N hN)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · rw [← h.ek i' (by omega_using [hi', e])]; exact Lay.bytes_keep hL K'.frame (c_ek i' (by omega_using [hi, hi']) e) (by decide)

end

theorem kgRow_step {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : KRow K s₀ i s) :
    WP isa K.kgRowBody s fun s' => KRow K s₀ (i + 1) s' ∧ (s'.gpr .t0 != 0) = decide (i + 1 ≠ K.k) :=
  WP.seq (WP.mono (rowSum_ok (transpose := false) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (kr2_ok hp hi h r₁) fun _ r₂ => WP.seq (WP.mono (kr3_ok hp hi h r₂) fun _ r₃ =>
    WP.seq (WP.mono (kr4_ok hp h r₃) fun _ r₄ => WP.seq (WP.mono (kr5_ok hp hi h r₄) fun _ r₅ =>
      kr6_ok hp hi h r₅)))))

theorem rows_init {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀)
    (hs : ∀ N < 2 * K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N))) :
    WP isa (.block [.li .s4 1, .li .s6 0]) s (KRow K s₀ 0) :=
  WP.mono flagInit_ok fun _ ⟨k₁, g24, g26, m₁⟩ =>
    ⟨h.keep hp (xs := [.s6, .s4]) (W := []) k₁ (by simp [savedTop]) rfl, g26, by rw [g24]; rfl,
      by rw [m₁]; exact hr, by rw [m₁]; exact hs, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

/-! ## `ŝ` into `dk` -/

/-- After encoding the first `j` polynomials of `ŝ`. -/
structure KS (K : KemLay) (s₀ : State) (j : Nat) (s : State) : Prop where
  env : KEnv K s₀ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 j
  s4 : s.gpr .s4 = if okK K s₀ K.k then 1 else 0
  rho : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀
  ek : ∀ i' < K.k, bytesAt s.mem ((lay s₀ K).A 3 (384 * i')) 384 = encode12 (tK K s₀ i')
  slots : ∀ j' < K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + j'))) (sK K s₀ j')
  dk : ∀ j' < j, bytesAt s.mem ((lay s₀ K).A 4 (384 * j')) 384 = encode12 (sK K s₀ j')

/-- `sK_ok` with the sizes `sz` of the buffers. -/
abbrev SKF (K : KemLay) (sz : List Nat) : Prop := ∀ j < K.k,
    [((4 : Nat), 384 * j, (384 : Nat))].all (fun w => sepB sz (0, 1288, 80) w && sepB sz (2, 0, 64) w) = true ∧
    sepAll sz (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, sepAll sz (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, sepAll sz (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → sepAll sz (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    sepB sz (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true

theorem sK_ok {K : KemLay} (hK : K.WF) {j : Nat} (hj : j < K.k) :
    [((4 : Nat), 384 * j, (384 : Nat))].all (okW K) = true ∧
    sepAll (kSz K) (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, sepAll (kSz K) (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, sepAll (kSz K) (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → sepAll (kSz K) (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    sepB (kSz K) (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, SKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega_using [this]) j hj
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, sepAll_scr c2 scr, fun i' hi' => sepAll_scr (c3 i' hi') scr,
    fun j' hj' => sepAll_scr (c4 j' hj') scr, fun j' hj' hne => sepAll_scr (c5 j' hj' hne) scr, sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [okW, Bool.and_eq_true] at this ⊢
  exact ⟨sepB_scr this.1 scr, sepB_scr this.2 scr⟩

theorem s_init {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KRow K s₀ K.k s) :
    WP isa (.block [.li .s6 0]) s (KS K s₀ 0) :=
  WP.mono (li_ok .s6 (N := 0) (by decide)) fun _ ⟨k₆, g26', m₆⟩ =>
    ⟨h.env.keep hp (xs := [.s6]) (W := []) k₆ (by simp [savedTop]) rfl, g26',
      by rw [k₆.cs .s4 (by decide) (by decide), h.s4], by rw [m₆]; exact h.rho,
      by rw [m₆]; exact h.ek, fun j' hj' => by rw [m₆]; exact h.slots j' (by omega_using [hj']),
      fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩

section
variable (K : KemLay) (s₀ : State) (j : Nat) (s : State)

/-- After the arguments of the encoding of `ŝ[j]`. -/
structure KS1 (s₁ : State) : Prop where
  o : Only s s₁
  a3 : s₁.gpr .a0 = (lay s₀ K).A 0 (oPoly (K.k + j))
  a4 : s₁.gpr .a1 = (lay s₀ K).A 4 (384 * j)

/-- After the encoding of `ŝ[j]`. -/
structure KS2 (s₂ : State) : Prop where
  kx : KeptX [.s6] ((lay s₀ K).RL [(4, 384 * j, 384)]) s s₂
  s6 : s₂.gpr .s6 = BitVec.ofNat 64 j
  enc : bytesAt s₂.mem ((lay s₀ K).A 4 (384 * j)) 384 = encode12 (sK K s₀ j)

end

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀) {j : Nat} (hj : j < K.k) {s : State} (h : KS K s₀ j s)
include hp hj h

theorem ks1_ok : WP isa (.block (slotAt .a0 .s6 K.k ++ atMul .a1 .s8 .s6 384)) s (KS1 K s₀ j s) := by
  have hK := hp.wf
  refine WP.mono (slotMul_ok (b := .s8) (.inr rfl) h.env.ctx.s11 h.env.s8 h.s6 (by offs) (by offs))
    fun s₁ ⟨o₁, a3, a4⟩ => ⟨o₁, ?_, a4⟩
  rw [a3, show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]

theorem ks2_ok {s₁ : State} (r : KS1 K s₀ j s s₁) : WP isa callEncode12 s₁ (KS2 K s₀ j s) := by
  have hL := lay_ok hp
  have hc₁ := h.env.ctx.only r.o
  obtain ⟨-, -, -, -, -, c_enc⟩ := sK_ok hp.wf hj
  obtain ⟨-, -, w4, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 4) (o' := 384 * j) r.a3 r.a4 c_enc (mem_rd_wr hc₁.cw)
    (by rw [r.o.wr, h.env.wr]; exact w4) (by rw [r.o.mem]; exact h.slots j hj) (hc₁.alP _) fun s₂ k₂ e₂ =>
    ⟨(r.o.x _ _).trans ((k₂.x _).monoL (by simp)),
      by rw [k₂.cs .s6 (by decide), r.o.cs .s6 (by decide), h.s6], e₂⟩

theorem ks3_ok {s₂ : State} (r : KS2 K s₀ j s s₂) :
    WP isa (.block (count .s6 K.k)) s₂ fun s' => KS K s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_ek, c_slots, c_dk, -⟩ := sK_ok hK hj
  refine WP.mono (count_ok (by decide) (by omega_using [hj, k4]) (by omega_using [k4]) r.s6) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.s6] ((lay s₀ K).RL [(4, 384 * j, 384)]) s s' :=
    r.kx.trans (k'.mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp [savedTop]) c_ok
  · rw [K'.cs .s4 (by decide) (by decide), h.s4]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun i' hi' => (Lay.bytes_keep hL K'.frame (c_ek i' hi') (by decide)).trans (h.ek i' hi')
  · exact fun j' hj' => Lay.polyIs_keep hL K'.frame (c_slots j' hj') (h.slots j' hj')
  · intro j' hj'
    by_cases e : j' = j
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · exact (Lay.bytes_keep hL K'.frame (c_dk j' (by omega_using [hj, hj']) e) (by decide)).trans (h.dk j' (by omega_using [hj', e]))

end

theorem kgS_step {K : KemLay} {s₀ : State} (hp : Pre K s₀) {j : Nat} (hj : j < K.k) {s : State}
    (h : KS K s₀ j s) :
    WP isa K.kgSBody s fun s' => KS K s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) :=
  WP.seq (WP.mono (ks1_ok hp hj h) fun _ r₁ => WP.seq (WP.mono (ks2_ok hp hj h r₁) fun _ r₂ => ks3_ok hp hj h r₂))

/-! ## The encapsulation key, `H(ek)` and `z` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ek`. -/
abbrev EK : List Byte := VG.Proof.MlKem.KPke.ekPKE K.p (aK K s₀) (D s₀)

/-- `dk`. -/
abbrev DK : List Byte := VG.Proof.MlKem.KPke.dkPKE K.p (D s₀) ++ EK K s₀ ++ H (EK K s₀) ++ Z s₀

end

theorem ek_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.ekLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) 32 :=
  bytesAt_add _ _ (384 * K.k) 32

theorem dk_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.dkLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) K.ekLen ++
      bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 32)) 32 ++ bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 64)) 32 := by
  rw [show K.dkLen = 384 * K.k + (K.ekLen + (32 + 32)) by simp only [KemLay.dkLen, KemLay.ekLen]; omega_using [],
    bytesAt_add _ _ (384 * K.k), bytesAt_add _ _ K.ekLen, bytesAt_add _ _ 32 32, VG.Offset.add_ofNat_add_ofNat,
    VG.Offset.add_ofNat_add_ofNat, show 384 * K.k + K.ekLen = 768 * K.k + 32 by simp only [KemLay.ekLen]; omega_using [],
    show 768 * K.k + 32 + 32 = 768 * K.k + 64 by omega_using []]
  simp only [List.append_assoc]

/-- What a region of `KEnv` must be apart from, with the sizes `sz` of the buffers. -/
abbrev okWz (sz : List Nat) (w : Nat × Nat × Nat) : Bool := sepB sz (0, 1288, 80) w && sepB sz (2, 0, 64) w

theorem okWz_scr {K : KemLay} {W : List (Nat × Nat × Nat)} (h : W.all (okWz (32768 :: (kSz K).tail)) = true)
    (hs : 32768 ≤ K.scratch) : W.all (okW K) = true :=
  List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp h w hw
    simp only [okWz, okW, Bool.and_eq_true] at this ⊢
    exact ⟨sepB_scr this.1 hs, sepB_scr this.2 hs⟩

/-- The separations of the copies and the hash of `tail_ok`, with the sizes `sz` of the buffers. -/
abbrev TailF (K : KemLay) (sz : List Nat) : Prop :=
  sepB sz (0, oSeed, 32) (3, 384 * K.k, 32) = true ∧ [(3, 384 * K.k, 32)].all (okWz sz) = true ∧
  (∀ i < K.k, sepAll sz (3, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  sepB sz (3, 0, K.ekLen) (4, 384 * K.k, K.ekLen) = true ∧ [(4, 384 * K.k, K.ekLen)].all (okWz sz) = true ∧
  sepAll sz (3, 0, K.ekLen) [(4, 384 * K.k, K.ekLen)] = true ∧
  (kRegs ++ [(4, 768 * K.k + 32, 32)]).all (okWz sz) = true ∧
  sepB sz (2, 32, 32) (4, 768 * K.k + 64, 32) = true ∧ [(4, 768 * K.k + 64, 32)].all (okWz sz) = true ∧
  sepAll sz (3, 0, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (3, 0, K.ekLen) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  (∀ i < K.k, sepAll sz (4, 384 * i, 384) [(4, 768 * K.k + 64, 32)] = true ∧
    sepAll sz (4, 384 * i, 384) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
    sepAll sz (4, 384 * i, 384) [(4, 384 * K.k, K.ekLen)] = true ∧
    sepAll sz (4, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  sepAll sz (4, 384 * K.k, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (4, 384 * K.k, K.ekLen) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  sepAll sz (4, 768 * K.k + 32, 32) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (0, 1288, 80) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true

theorem tail_facts {K : KemLay} (hK : K.WF) : TailF K (kSz K) := by
  have s := hK.scr
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    (by decide : ∀ k < 5, TailF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega_using [this])
  exact ⟨sepB_scr f1 s, okWz_scr f2 s, fun i hi => sepAll_scr (f3 i hi) s, sepB_scr f4 s, okWz_scr f5 s,
    sepAll_scr f6 s, okWz_scr f7 s, sepB_scr f8 s, okWz_scr f9 s, sepAll_scr f10 s, sepAll_scr f11 s,
    fun i hi => ⟨sepAll_scr (f12 i hi).1 s, sepAll_scr (f12 i hi).2.1 s, sepAll_scr (f12 i hi).2.2.1 s,
      sepAll_scr (f12 i hi).2.2.2 s⟩, sepAll_scr f13 s, sepAll_scr f14 s, sepAll_scr f15 s, sepAll_scr f16 s⟩

theorem h_ins {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s9, 0, K.ekLen⟩ : Piece)], PieceOk (lay s₀ K) kidx s false p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inl rfl)) (by simp) (by show 0 < 32768; decide)
    (by show K.ekLen < 2048; have := hK.k4; simp only [KemLay.ekLen]; omega_using [this])
    (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega_using []) (by ldecide)

theorem h_outs {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s8, 768 * K.k + 32, 32⟩ : Piece)], PieceOk (lay s₀ K) kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inl rfl))) (by simp)
    (by show 768 * K.k + 32 < 32768; have := hK.k4; omega_using [this]) (by show 32 < 2048; decide) (by show 0 < 32; decide)
    (by ldecide)

/-- The end: our caller's registers restored, and `a0` the flag. -/
theorem end_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.gpr .a0 = s.gpr .s4 ∧ s'.mem = s.mem ∧ s'.sp = s₀.sp := by
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  have hK := hp.wf
  refine WP.mono (topEnd_ok h.ctx.s11 hp.alS h.sav (fun o h₁ h₂ => ?_) h.cs) fun s' ⟨pr, lr, a0, m, sp, _, _⟩ =>
    ⟨pr, lr, a0, m, sp.trans h.sp⟩
  rw [h.rd, h.wr]
  have scr := hK.scr
  have hb : o + 8 ≤ (lay s₀ K).size 0 := by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [h₂, scr]
  exact mem_rd_wr' (Lay.covers w0 hb _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)

/-! What each step of the end keeps, for the proof of constant time. -/

section
variable {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
include hp h

theorem cpRho_env : WP isa (copy .s11 oSeed .s9 (384 * K.k) 32) s (KEnv K s₀) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨w0, w3, -, -⟩ := buf_wr hp
  obtain ⟨f1, f2, -⟩ := tail_facts hK
  exact WP.mono (copyL (lay_ok hp) (i := 0) (j := 3) (by decide) (by decide) h.ctx.s11 h.s9
    (by decide) (by show 384 * K.k < 32768; omega_using [k4]) (by decide) (by decide) f1
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w3)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f2

theorem cpEk_env : WP isa (copy .s9 0 .s8 (384 * K.k) K.ekLen) s (KEnv K s₀) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨-, w3, w4, -⟩ := buf_wr hp
  obtain ⟨-, -, -, f4, f5, -⟩ := tail_facts hK
  exact WP.mono (copyL (lay_ok hp) (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen)
    (by decide) (by decide) h.s9 h.s8 (by decide) (by show 384 * K.k < 32768; omega_using [k4])
    (by show K.ekLen < 2048; simp only [KemLay.ekLen]; omega_using [k4]) (by simp only [KemLay.ekLen]; omega_using []) f4
    (by rw [h.rd, h.wr]; exact mem_rd_wr w3) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f5

theorem hashH_env :
    WP isa (hash 136 0x06 [⟨.s9, 0, K.ekLen⟩] [⟨.s8, 768 * K.k + 32, 32⟩]) s (KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨-, -, -, -, -, -, f7, -⟩ := tail_facts hK
  exact WP.mono (hash_ok (idx := kidx) VG.Proof.MlKem.rate136 (by decide) h.ctx
    (List.cons_ne_nil _ _) (h_ins hp h) (h_outs hp h) (List.pairwise_singleton _ _)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f7

theorem cpZ_env : WP isa (copy .s10 32 .s8 (768 * K.k + 64) 32) s (KEnv K s₀) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨-, -, w4, w2⟩ := buf_wr hp
  obtain ⟨-, -, -, -, -, -, -, f8, f9, -⟩ := tail_facts hK
  exact WP.mono (copyL (lay_ok hp) (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    (by decide) (by decide) h.s10 h.s8 (by decide) (by show 768 * K.k + 64 < 32768; omega_using [k4]) (by decide)
    (by decide) f8 (by rw [h.rd, h.wr]; exact w2) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f9

end

theorem tail_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KS K s₀ K.k s) :
    WP isa (.seq (copy .s11 oSeed .s9 (384 * K.k) 32) <| .seq (copy .s9 0 .s8 (384 * K.k) K.ekLen) <|
      .seq (hash 136 0x06 [⟨.s9, 0, K.ekLen⟩] [⟨.s8, 768 * K.k + 32, 32⟩]) <|
      .seq (copy .s10 32 .s8 (768 * K.k + 64) 32) (.block topEnd)) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.gpr .ra = s₀.gpr .ra ∧
        s'.gpr .a0 = (if okK K s₀ K.k then 1 else 0) ∧ bytesAt s'.mem (pEk s₀) K.ekLen = EK K s₀ ∧
        bytesAt s'.mem (pDk s₀) K.dkLen = DK K s₀ := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, -⟩ := tail_facts hK
  -- `ρ` into `ek`
  have h₀ := h.env
  refine WP.seq (WP.mono (copyL hL (i := 0) (j := 3) (by decide) (by decide) h₀.ctx.s11 h₀.s9
    (by decide) (by show 384 * K.k < 32768; omega_using [k4]) (by decide) (by decide) f1
    (by rw [h₀.rd, h₀.wr]; exact mem_rd_wr w0) (by rw [h₀.wr]; exact w3)) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h₀.keep hp (k₁.x []) (by simp) f2
  have ek₁ : bytesAt s₁.mem ((lay s₀ K).A 3 0) K.ekLen = EK K s₀ := by
    rw [ek_split, bytes_catK, VG.Offset.add_ofNat_add_ofNat, Nat.zero_add, b₁, h.rho]
    refine congrArg (· ++ _) (catK_congr fun i hi => ?_)
    rw [VG.Offset.add_ofNat_add_ofNat, Nat.zero_add]
    exact (Lay.bytes_keep hL k₁.frame (f3 i hi) (by decide)).trans (h.ek i hi)
  -- `ek` into `dk`
  refine WP.seq (WP.mono (copyL hL (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen) (by decide)
    (by decide) h₁.s9 h₁.s8 (by decide) (by show 384 * K.k < 32768; omega_using [k4])
    (by show K.ekLen < 2048; simp only [KemLay.ekLen]; omega_using [k4]) (by simp only [KemLay.ekLen]; omega_using []) f4
    (by rw [h₁.rd, h₁.wr]; exact mem_rd_wr w3) (by rw [h₁.wr]; exact w4)) fun s₂ ⟨k₂, b₂⟩ => ?_)
  rw [ek₁] at b₂
  have h₂ := h₁.keep hp (k₂.x []) (by simp) f5
  have ek₂ : bytesAt s₂.mem ((lay s₀ K).A 3 0) K.ekLen = EK K s₀ :=
    (Lay.bytes_keep hL k₂.frame f6 (by simp only [KemLay.ekLen]; omega_using [k4])).trans ek₁
  -- `H(ek)`
  refine WP.seq (WP.mono (hash_ok (idx := kidx) VG.Proof.MlKem.rate136 (by decide) h₂.ctx
    (List.cons_ne_nil _ _) (h_ins hp h₂) (h_outs hp h₂) (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have h₃ := h₂.keep hp (k₃.x []) (by simp) f7
  have hek₃ : bytesAt s₃.mem ((lay s₀ K).A 4 (768 * K.k + 32)) 32 = H (EK K s₀) := by
    have e := o₃.1
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
    refine e.trans ?_
    show _ = H (EK K s₀)
    rw [VG.Proof.MlKem.H_eq, ← ek₂]; rfl
  -- `z`
  refine WP.seq (WP.mono (copyL hL (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    (by decide) (by decide) h₃.s10 h₃.s8 (by decide) (by show 768 * K.k + 64 < 32768; omega_using [k4]) (by decide) (by decide)
    f8 (by rw [h₃.rd, h₃.wr]; exact w2) (by rw [h₃.wr]; exact w4)) fun s₄ ⟨k₄, b₄⟩ => ?_)
  have h₄ := h₃.keep hp (k₄.x []) (by simp) f9
  have z₄ : bytesAt s₄.mem ((lay s₀ K).A 4 (768 * K.k + 64)) 32 = Z s₀ := by
    rw [b₄]
    have := congrArg (List.drop 32) h₃.seed
    rw [bytesAt_drop _ _ (by decide), bytesAt_drop _ _ (by decide)] at this
    rw [show (lay s₀ K).A 2 32 = (lay s₀ K).A 2 0 + BitVec.ofNat 64 32 by
      simp only [Lay.A, VG.Offset.add_ofNat_add_ofNat], this]
    simp only [Lay.A, BitVec.add_zero]; rfl
  have g24 : s₄.gpr .s4 = if okK K s₀ K.k then 1 else 0 := by
    rw [k₄.cs .s4 (by decide), k₃.cs .s4 (by decide), k₂.cs .s4 (by decide), k₁.cs .s4 (by decide), h.s4]
  refine WP.mono (end_ok hp h₄) fun s' ⟨pr, lr, a0, m', sp'⟩ => ⟨pr, sp', lr, a0.trans g24, ?_, ?_⟩
  · rw [m', show pEk s₀ = (lay s₀ K).A 3 0 from (BitVec.add_zero _).symm,
      Lay.bytes_keep hL k₄.frame f10 (by simp only [KemLay.ekLen]; omega_using [k4]),
      Lay.bytes_keep hL k₃.frame f11 (by simp only [KemLay.ekLen]; omega_using [k4]), ek₂]
  · have kd : ∀ i < K.k, bytesAt s₄.mem ((lay s₀ K).A 4 (384 * i)) 384 = bytesAt s.mem ((lay s₀ K).A 4 (384 * i)) 384 :=
      fun i hi => (Lay.bytes_keep hL k₄.frame (f12 i hi).1 (by decide)).trans
        ((Lay.bytes_keep hL k₃.frame (f12 i hi).2.1 (by decide)).trans
        ((Lay.bytes_keep hL k₂.frame (f12 i hi).2.2.1 (by decide)).trans
          (Lay.bytes_keep hL k₁.frame (f12 i hi).2.2.2 (by decide))))
    have e4 := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 384 * K.k) (l := K.ekLen) f13
      (by simp only [KemLay.ekLen]; omega_using [k4])).trans ((Lay.bytes_keep hL k₃.frame f14
        (by simp only [KemLay.ekLen]; omega_using [k4])).trans b₂)
    have hh := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 768 * K.k + 32) (l := 32) f15 (by decide)).trans hek₃
    simp only [Lay.A] at e4 hh z₄ kd
    rw [m', show pDk s₀ = (lay s₀ K).ptr 4 from rfl, dk_split, bytes_catK, e4, hh, z₄]
    refine congrArg (· ++ _ ++ _ ++ _) (catK_congr fun i hi => ?_)
    exact (kd i hi).trans (h.dk i hi)

/-! ## The whole function -/

theorem correct {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa K.keygen s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
      s.gpr .a0 = (if okK K s₀ K.k then 1 else 0) ∧ bytesAt s.mem (pEk s₀) K.ekLen = EK K s₀ ∧
      bytesAt s.mem (pDk s₀) K.dkLen = DK K s₀ := by
  have hK := hp.wf
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (g_ok hp h₁ b₁) fun s₂ ⟨h₂, r₂, σ₂⟩ => ?_)
  refine WP.seq (WP.mono (rho_ok hp h₂ r₂ σ₂) fun s₂' ⟨h₂', r₂', σ₂'⟩ => ?_)
  refine WP.seq (WP.mono (prf_phase hp h₂' r₂' σ₂') fun s₃ ⟨h₃, r₃, p₃⟩ => ?_)
  refine WP.seq (WP.mono (rows_init hp h₃ r₃ p₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (wp_loop_nz (KRow K s₀) (N := K.k) hK.k1 (fun i hi s h => kgRow_step hp hi h)
    (fun _ h => h) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (s_init hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_nz (KS K s₀) (N := K.k) hK.k1 (fun j hj s h => kgS_step hp hj h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  exact tail_ok hp h₇

end VG.Proof.MlKem.RISCV64.KeyGen

end

end

/-!
# ML-KEM on RISC-V: key generation in constant time

As on PPC64LE (`Proof/MlKem/PPC64LE/KeyGenCT.lean`): two runs from states that
agree on the public data (the pointers, the stack pointer and `ρ`, which the
contract lets the function leak, since `ek` publishes it) leak the same trace
(`all_ct`), phase by phase: the blocks by the taint analysis, from the
pointers, or because they access no memory (`relct_noMem`); the hashes by
`hash_ct`; the `PRF`s by `prfLoop_ct`; the rows of `t̂` by `rowSum_ct`, whose
`SampleNTT`s take the same seeds in both runs; and the calls of the
primitives on the same pointers (`RelCT.callT`). What each run is at each
point comes from its correctness (`KeyGen.lean`).

All of it holds for any parameter set: the taint analyses of the blocks whose
immediates depend on it are facts of `KemLay.CallsOk`, which the parameter set
checks by evaluation.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.KeyGen

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  a0 : s₁.gpr .a0 = s₂.gpr .a0
  a1 : s₁.gpr .a1 = s₂.gpr .a1
  a2 : s₁.gpr .a2 = s₂.gpr .a2
  a3 : s₁.gpr .a3 = s₂.gpr .a3
  rho : ρ₀ K s₁ = ρ₀ K s₂

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.lay : lay s₂ K = lay s₁ K := by
  simp only [KeyGen.lay, pSeed, pEk, pDk, pScr, two.a0, two.a1, two.a2, two.a3, two.sp]

/-- The registers that hold pointers are the same in both runs. -/
theorem Two.regs {a b : State} (ha : KEnv K s₁ a) (hb : KEnv K s₂ b) :
    ∀ r ∈ [Reg.s8, .s9, .s10, .s11], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.s8, hb.s8]; exact two.a2
  · rw [ha.s9, hb.s9]; exact two.a1
  · rw [ha.s10, hb.s10]; exact two.a0
  · rw [ha.ctx.s11, hb.ctx.s11, two.lay]

theorem Two.sub {rs : List Reg} (hs : ∀ r ∈ rs, r ∈ [Reg.s8, .s9, .s10, .s11]) {a b : State}
    (ha : KEnv K s₁ a) (hb : KEnv K s₂ b) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
  fun r hr => two.regs ha hb r (hs r hr)

theorem Two.spE {a b : State} (ha : KEnv K s₁ a) (hb : KEnv K s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

/-! ## The rows of `t̂` -/

theorem kgRow_ct {i : Nat} (hi : i < K.k) :
    RelCT isa (fun a b => KRow K s₁ i a ∧ KRow K s₂ i b) K.kgRowBody fun a b =>
      (KRow K s₁ (i + 1) a ∧ (a.gpr .t0 != 0) = decide (i + 1 ≠ K.k)) ∧
      (KRow K s₂ (i + 1) b ∧ (b.gpr .t0 != 0) = decide (i + 1 ≠ K.k)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have py : RowPre K (lay s₁ K) (ρ₀ K s₁) (sK K s₂) i (okK K s₂ i) y := by
    have := hy.rowPre hp₂ hi; rwa [two.lay, ← two.rho] at this
  -- `RowSum`
  refine RelCT.seq (R := fun (a b : State) =>
      RowInv K (lay s₁ K) false (ρ₀ K s₁) (sK K s₁) i (okK K s₁ i) x K.k a ∧
      RowInv K (lay s₂ K) false (ρ₀ K s₂) (sK K s₂) i (okK K s₂ i) y K.k b)
    (relct_wp (rowSum_ct hp₁.calls (hx.rowPre hp₁ hi) py) fun a b hab =>
      ⟨by rw [hab.1]; exact rowSum_ok (hx.rowPre hp₁ hi),
        by rw [hab.2]; exact rowSum_ok (hy.rowPre hp₂ hi)⟩) ?_
  -- `t̂[i] += ê[i]`
  refine RelCT.seq (R := fun (a b : State) => KR2 K s₁ i x a ∧ KR2 K s₂ i y b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨kr2_ok hp₁ hi hx hab.1, kr2_ok hp₂ hi hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KR3 K s₁ i x a ∧ KR3 K s₂ i y b)
    (relct_wp (RelCT.callT addT (regs2 fun a b hab =>
      ⟨by rw [hab.1.kx.sp, hab.2.kx.sp, hx.env.sp, hy.env.sp, two.sp],
        by rw [hab.1.a0, hab.2.a0, two.lay], by rw [hab.1.a1, hab.2.a1, two.lay]⟩))
      fun a b hab => ⟨kr3_ok hp₁ hi hx hab.1, kr3_ok hp₂ hi hy hab.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b : State) => KR4 K s₁ i x a ∧ KR4 K s₂ i y b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨kr4_ok hp₁ hx hab.1, kr4_ok hp₂ hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KR5 K s₁ i x a ∧ KR5 K s₂ i y b)
    (relct_wp (RelCT.callT encode12T (regs2 fun a b hab =>
      ⟨by rw [hab.1.a0.kx.sp, hab.2.a0.kx.sp, hx.env.sp, hy.env.sp, two.sp],
        by rw [hab.1.a3, hab.2.a3, two.lay], by rw [hab.1.a4, hab.2.a4, two.lay]⟩))
      fun a b hab => ⟨kr5_ok hp₁ hi hx hab.1, kr5_ok hp₂ hi hy hab.2⟩) ?_
  exact relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨kr6_ok hp₁ hi hx hab.1, kr6_ok hp₂ hi hy hab.2⟩

/-! ## `ŝ` into `dk` -/

theorem kgS_ct {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => KS K s₁ j a ∧ KS K s₂ j b) K.kgSBody fun a b =>
      (KS K s₁ (j + 1) a ∧ (a.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) ∧
      (KS K s₂ (j + 1) b ∧ (b.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  refine RelCT.seq (R := fun (a b : State) => KS1 K s₁ j x a ∧ KS1 K s₂ j y b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨by rw [hab.1]; exact ks1_ok hp₁ hj hx,
      by rw [hab.2]; exact ks1_ok hp₂ hj hy⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KS2 K s₁ j x a ∧ KS2 K s₂ j y b)
    (relct_wp (RelCT.callT encode12T (regs2 fun a b hab =>
      ⟨by rw [hab.1.o.sp, hab.2.o.sp, hx.env.sp, hy.env.sp, two.sp],
        by rw [hab.1.a3, hab.2.a3, two.lay], by rw [hab.1.a4, hab.2.a4, two.lay]⟩))
      fun a b hab => ⟨ks2_ok hp₁ hj hx hab.1, ks2_ok hp₂ hj hy hab.2⟩) ?_
  exact relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨ks3_ok hp₁ hj hx hab.1, ks3_ok hp₂ hj hy hab.2⟩

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.keygen fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ a.mem ((lay s₁ K).A 0 oK) = BitVec.ofNat 8 K.k) ∧
      (KEnv K s₂ b ∧ b.mem ((lay s₂ K).A 0 oK) = BitVec.ofNat 8 K.k))
    (relct_wp (hp₁.calls.kgSetupT.relct (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact two.a0
        · exact two.a1
        · exact two.a2
        · exact two.a3))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `G(d ‖ k)`
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₁) ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₁)) ∧
      (KEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₂) ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₂)))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := kidx) VG.Proof.MlKem.rate72 (by decide)
      (List.cons_ne_nil _ _) fun a b hab => ⟨⟨hab.1.1.ctx, g_ins hp₁ hab.1.1, g_outs hp₁ hab.1.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.1.ctx, g_ins hp₂ hab.2.1, g_outs hp₂ hab.2.1⟩,
        two.spE hab.1.1 hab.2.1⟩)
      fun a b hab => ⟨g_ok hp₁ hab.1.1 hab.1.2, g_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `ρ`
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₁) ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₁)) ∧
      (KEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₂) ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₂)))
    (relct_wp (taint_prog [.s11] (fun a b hab => two.spE hab.1.1 hab.2.1)
      (fun a b hab => two.sub (by simp) hab.1.1 hab.2.1) (by taint_decide))
      fun a b hab => ⟨rho_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2,
        rho_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the `PRF`s
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₁) ∧
        ∀ N < 2 * K.k, PolyIs a.mem ((lay s₁ K).A 0 (oPoly (K.k + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₁)) N))) ∧
      (KEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₂) ∧
        ∀ N < 2 * K.k, PolyIs b.mem ((lay s₂ K).A 0 (oPoly (K.k + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₂)) N))))
    (relct_wp (RelCT.pointwise fun x y hxy =>
      prfLoop_ct hK (L := lay s₁ K) true (by have := hK.k1; omega_using [this]) (by omega_using []) hxy.1.1.ctx
        (by rw [← two.lay]; exact hxy.2.1.ctx) rfl rfl)
      fun a b hab => ⟨prf_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2,
        prf_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the rows of `t̂`
  refine RelCT.seq (R := fun (a b : State) => KRow K s₁ 0 a ∧ KRow K s₂ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨rows_init hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, rows_init hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KRow K s₁ K.k a ∧ KRow K s₂ K.k b)
    (relct_loop_nz (N := K.k) hK.k1 fun i hi => kgRow_ct two hi) ?_
  -- `ŝ` into `dk`
  refine RelCT.seq (R := fun (a b : State) => KS K s₁ 0 a ∧ KS K s₂ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨s_init hp₁ hab.1, s_init hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (RelCT.mono (relct_loop_nz (N := K.k) hK.k1 fun j hj => kgS_ct two hj) (fun _ _ h => h)
      fun _ _ h => ⟨h.1.env, h.2.env⟩) ?_
  -- the end
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hp₁.calls.rhoT.relct (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨cpRho_env hp₁ hab.1, cpRho_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hp₁.calls.ekT.relct (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨cpEk_env hp₁ hab.1, cpEk_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hash_ct (L := lay s₁ K) (idx := kidx) VG.Proof.MlKem.rate136 (by decide)
      (List.cons_ne_nil _ _) fun a b hab => ⟨⟨hab.1.ctx, h_ins hp₁ hab.1, h_outs hp₁ hab.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.ctx, h_ins hp₂ hab.2, h_outs hp₂ hab.2⟩,
        two.spE hab.1 hab.2⟩)
      fun a b hab => ⟨hashH_env hp₁ hab.1, hashH_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hp₁.calls.zT.relct (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨cpZ_env hp₁ hab.1, cpZ_env hp₂ hab.2⟩) ?_
  exact taint_block [.s11] (fun a b hab => two.spE hab.1 hab.2)
    (fun a b hab => two.sub (by simp) hab.1 hab.2) (by taint_decide)

end

/-! ## The outcome -/

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem sample_some {K : KemLay} {s₀ : State} (hk : okK K s₀ K.k = true) :
    ∀ i < K.k, ∀ j < K.k,
      sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.KPke.kgRho K.p (D s₀)) i j) =
        some (aK K s₀ i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk i (List.mem_range.mpr hi)
  have h₂ := List.all_eq_true.mp h₁ j (List.mem_range.mpr hj)
  simp only [rowSeed, Bool.false_eq_true, ite_false] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [aK, effA, rowSeed, Bool.false_eq_true, ite_false, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem sample_none {K : KemLay} {s₀ : State} (hk : okK K s₀ K.k = false) :
    ∃ i < K.k, ∃ j < K.k,
      sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.KPke.kgRho K.p (D s₀)) i j) = none := by
  rw [okK, List.all_eq_false] at hk
  obtain ⟨i, hi, h₁⟩ := hk
  rw [Bool.not_eq_true, okRow, List.all_eq_false] at h₁
  obtain ⟨j, hj, h₂⟩ := h₁
  simp only [rowSeed, Bool.false_eq_true, ite_false] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

/-- What key generation returns and writes is the outcome of
`ML-KEM.KeyGen_internal(d, z)`. -/
theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => keyGenInternal K.p iters (D s₀) (Z s₀)) (if okK K s₀ K.k then 1 else 0)
      (EK K s₀, DK K s₀) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okK K s₀ K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := sample_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.keyGenInternal_eq, VG.Proof.MlKem.KPke.kpkeKeyGen_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.keyGenInternal_eq,
      VG.Proof.MlKem.KPke.kpkeKeyGen_some hK.η₁ (sample_some hk)]
    rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.keyGenBodyContract RISCV64.abi 1168).pre s) : Pre kl768 s := by
  sig_pre [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩ := h
  exact ⟨kl768_wf, kl768_calls, al, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩

theorem post_of {s₀ s : State} (h3 : s.gpr .a0 = if okK kl768 s₀ kl768.k then 1 else 0)
    (hek : bytesAt s.mem (pEk s₀) 1184 = EK kl768 s₀)
    (hdk : bytesAt s.mem (pDk s₀) 2400 = DK kl768 s₀) :
    (Proof.MlKem.Scrubbed.keyGenBodyContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32 (if okK kl768 s₀ kl768.k then (1 : BitVec 64) else 0) =
      if okK kl768 s₀ kl768.k then 1 else 0 := by
    cases okK kl768 s₀ kl768.k <;> rfl
  rw [h3, hek, hdk, e]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem.RISCV64.keygen (Proof.MlKem.Scrubbed.keyGenBodyContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hek hdk⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρ₀ kl768 s₁ = ρ₀ kl768 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.RISCV64.KeyGen

end

end

/-! ### `MlKem1024.RISCV64.KeyGenCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on RISC-V: `vg_mlkem1024_keygen`, `Verified`

The function of `Proof/MlKem/RISCV64/CallWipe.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.RISCV64.KeyGen

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64 VG.Impl.MlKem1024.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.RISCV64 VG.Proof.MlKem1024.RISCV64
open VG.Proof.MlKem.RISCV64.Enc
open VG.Proof.MlKem.RISCV64.KeyGen hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.keyGen1024BodyContract RISCV64.abi 1168).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, al, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩

theorem post_of {s₀ s : State} (h3 : s.gpr .a0 = if okK kl1024 s₀ kl1024.k then 1 else 0)
    (hek : bytesAt s.mem (pEk s₀) 1568 = EK kl1024 s₀)
    (hdk : bytesAt s.mem (pDk s₀) 3168 = DK kl1024 s₀) :
    (Proof.MlKem.Scrubbed.keyGen1024BodyContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32 (if okK kl1024 s₀ kl1024.k then (1 : BitVec 64) else 0) =
      if okK kl1024 s₀ kl1024.k then 1 else 0 := by
    cases okK kl1024 s₀ kl1024.k <;> rfl
  rw [h3, hek, hdk, e]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem1024.RISCV64.keygen1024 (Proof.MlKem.Scrubbed.keyGen1024BodyContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hek hdk⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρ₀ kl1024 s₁ = ρ₀ kl1024 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.RISCV64.KeyGen

end

end

/-! ### `MlKem1024.RISCV64.EncapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on RISC-V: `vg_mlkem1024_encaps`, `Verified`

The function of `Proof/MlKem/RISCV64/EncapsCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.RISCV64.Encaps

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64 VG.Impl.MlKem1024.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.RISCV64 VG.Proof.MlKem1024.RISCV64
open VG.Proof.MlKem.RISCV64.Enc
open VG.Proof.MlKem.RISCV64.Encaps hiding pre_of post_of satState verified pre_ofH post_ofH verifiedH

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.encaps1024BodyContract RISCV64.abi 1168).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5, alS⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, al, h0, by rw [h1]; exact .head _, by rw [h1]; exact .tail _ (.head _), h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4,
    b5, f1, f2, f3, f4, f5, alS⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .a0 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 = KK kl1024 s₀)
    (hct : bytesAt s.mem (pCt s₀) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 s₀)) (RR kl1024 s₀)) (EK kl1024 s₀) (M kl1024 s₀) (RR kl1024 s₀)) :
    (Proof.MlKem.Scrubbed.encaps1024BodyContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .a0) 1568 = EK kl1024 s₀ := (EK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .a1) 32 = M kl1024 s₀ := (M_eq kl1024 s₀).symm
  rw [h3, e, hkey, hct, e0, e1]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | .a4 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem1024.RISCV64.encaps1024 (Proof.MlKem.Scrubbed.encaps1024BodyContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey hct⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 s₁) = ekRho kl1024.p (EK kl1024 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, g7, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

/-! ## `encapsH` -/

theorem pre_ofH {s : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract RISCV64.abi 1168).pre s) : PreH kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, dh1, dh2, dh3, d4, d5, d6, d7, d8, d9, b1, bh, b2, b3, b4, b5,
    f1, fh, f2, f3, f4, f5, hh, alS⟩ := h
  have r : (args s).rd = _ := h1
  exact ⟨⟨kl1024_wf, kl1024_calls, al, h0, by rw [r]; exact .head _, by rw [r]; exact .tail _ (.tail _ (.head _)),
    h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5, alS⟩,
    by rw [h1]; exact .tail _ (.head _), dh3, bh, fh, by rw [EK_eq]; exact hh⟩

/-- `post_of` for `encapsH`, whose arguments after `ek` are one register later. -/
theorem post_ofH {s₀ s : State}
    (h3 : s.gpr .a0 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey (args s₀)) 32 = KK kl1024 (args s₀))
    (hct : bytesAt s.mem (pCt (args s₀)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 (args s₀))) (RR kl1024 (args s₀))) (EK kl1024 (args s₀)) (M kl1024 (args s₀))
      (RR kl1024 (args s₀))) :
    (Proof.MlKem.Scrubbed.encapsH1024BodyContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
    RISCV64.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ekRho kl1024.p (EK kl1024 (args s₀))) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .a0) 1568 = EK kl1024 (args s₀) := (EK_eq kl1024 (args s₀)).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .a2) 32 = M kl1024 (args s₀) := (M_eq kl1024 (args s₀)).symm
  have hkey' : bytesAt s.mem (s₀.gpr .a3) 32 = KK kl1024 (args s₀) := hkey
  have hct' : bytesAt s.mem (s₀.gpr .a4) 1568 = _ := hct
  rw [h3, e, hkey', hct', e0, e1]
  exact outcome kl1024_wf (args s₀)

theorem verifiedH :
    Verified RISCV64.target Impl.MlKem1024.RISCV64.encapsH1024 (Proof.MlKem.Scrubbed.encapsH1024BodyContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correctH (pre_ofH hs)
    exact ⟨t, s', he, ⟨fun r hr => (hpres r hr).trans (args_preserved s r hr), hsp, hlr⟩, post_ofH h3 hkey hct⟩
  · have hq₁ := pre_ofH h₁
    have hq₂ := pre_ofH h₂
    sig_pub [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
      RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7, g8⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 (args s₁)) = ekRho kl1024.p (EK kl1024 (args s₂)) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ctH ⟨hq₁, hq₂, hsp, g3, g4, g5, g6, g7, g8, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlKem.RISCV64.Encaps.satStateH 1568 1568 49152, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | exact VG.Proof.MlKem.hMem_h (by decide)
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.RISCV64.Encaps

end

end

/-! ### `MlKem1024.RISCV64.DecapsCT`, which only this module used -/

section

/-!
# ML-KEM-1024 on RISC-V: `vg_mlkem1024_decaps`, `Verified`

The function of `Proof/MlKem/RISCV64/DecapsCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.RISCV64.Decaps

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64 VG.Impl.MlKem1024.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.RISCV64 VG.Proof.MlKem1024.RISCV64
open VG.Proof.MlKem.RISCV64.Enc
open VG.Proof.MlKem.RISCV64.Decaps hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.decaps1024BodyContract RISCV64.abi 1168).pre s) : Pre kl1024 s := by
  sig_pre [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, al, h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .a0 = if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 =
      if CT kl1024 s₀ = C2 kl1024 s₀ then K1 kl1024 s₀ else KB kl1024 s₀) :
    (Proof.MlKem.Scrubbed.decaps1024BodyContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then (1 : BitVec 64) else 0) =
      if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0 := by
    cases okEnc kl1024.k (ρD kl1024 s₀) kl1024.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .a0) 3168 = DK kl1024 s₀ := (DK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .a1) 1568 = CT kl1024 s₀ := (CT_eq kl1024 s₀).symm
  rw [h3, e, hkey, e0, e1]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem1024.RISCV64.decaps1024 (Proof.MlKem.Scrubbed.decaps1024BodyContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρD kl1024 s₁ = ρD kl1024 s₂ := by
      rw [rhoD_eq, rhoD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.RISCV64.Decaps

end

end


/-!
# ML-KEM on RISC-V: the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/RISCV64.lean`) of its code, which zeroes all of
`scratch` with `vg_zeroize` once that code returns, and is verified against
the same contract with 32 more bytes of stack and `scratch` left scrubbed
(`Verified.callWipe'`; `*_scrubbed`, the contracts of
`Proof/MlKem/Scrubbed.lean`), since every byte of it is zero
(`Scrubbed.keyGen_wiped`, …). `*_verified` state them as the contracts of
`Spec/MlKem/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Wipe

open VG VG.RISCV64

/-- `vg_zeroize` has no frames. -/
theorem zeroize_sdepth : sdepth Impl.Zeroize.RISCV64.zeroize ≤ 0 := by decide

/-! ## What the contracts read of the memory -/

/-- Memories agreeing on the region of `k` bytes at `p` agree on the `n`
bytes at offset `o` within it. -/
theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {o n : Nat} (hn : o + n ≤ k) :
    Spec.Sha3.bytesAt m₁ (p + BitVec.ofNat 64 o) n = Spec.Sha3.bytesAt m₂ (p + BitVec.ofNat 64 o) n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [Offset.add_add]
  exact h _ (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hk, hn, hi]))

/-- `bytesAt_agree` at offset 0. -/
theorem bytesAt_agree0 {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {n : Nat} (hn : n ≤ k) :
    Spec.Sha3.bytesAt m₁ p n = Spec.Sha3.bytesAt m₂ p n := by
  have := bytesAt_agree h hk (o := 0) (n := n) (by omega_using [hn])
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- Two buffers of a contract, one of them writable, lie apart. -/
theorem pw_disj {l : List (Region × Bool)} (h : l.Pairwise (fun a b => (a.2 || b.2) = true → a.1.Disjoint b.1))
    {i j : Nat} (hij : i < j) (hj : j < l.length) (hw : (l[i].2 || l[j].2) = true) : l[i].1.Disjoint l[j].1 :=
  List.pairwise_iff_getElem.mp h i j (by omega_using [hij, hj]) hj hij hw

/-! ## The functions, with any code verified against their contracts -/

/-- `vg_mlkem768_keygen`. -/
theorem keyGen_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGenBodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a3 32768 "vg_mlkem768_keygen" body) (Scrubbed.keyGenContract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1184) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 2400) (by decide)]
      exact h)
    (Scrubbed.keyGen_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsHBodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a5 32768 "vg_mlkem768_encaps_h" body) (Scrubbed.encapsHContract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encapsH_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_encaps`. -/
theorem encaps_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsBodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a4 32768 "vg_mlkem768_encaps" body) (Scrubbed.encapsContract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_decaps`. -/
theorem decaps_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decapsBodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a3 32768 "vg_mlkem768_decaps" body) (Scrubbed.decapsContract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1088) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a3 49152 "vg_mlkem1024_keygen" body) (Scrubbed.keyGen1024Contract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 3168) (by decide)]
      exact h)
    (Scrubbed.keyGen1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a5 49152 "vg_mlkem1024_encaps_h" body) (Scrubbed.encapsH1024Contract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encapsH1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encaps1024BodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a4 49152 "vg_mlkem1024_encaps" body) (Scrubbed.encaps1024Contract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_wipe {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decaps1024BodyContract abi st)) (hd : sdepth body ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi (st + 32)).pre s) :
    Verified target (Impl.MlKem.RISCV64.Wipe.wiped .a3 49152 "vg_mlkem1024_decaps" body) (Scrubbed.decaps1024Contract abi (st + 32)) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h Proof.Zeroize.RISCV64.verified (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd zeroize_sdepth (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])

/-! ## The stack the functions use: that of `vg_mlkem_sample_ntt`'s frame -/

theorem keyGen_sdepth : sdepth Impl.MlKem.RISCV64.keygen ≤ 1168 := by lit_decide
theorem encapsH_sdepth : sdepth Impl.MlKem.RISCV64.encapsH ≤ 1168 := by lit_decide
theorem encaps_sdepth : sdepth Impl.MlKem.RISCV64.encaps ≤ 1168 := by lit_decide
theorem decaps_sdepth : sdepth Impl.MlKem.RISCV64.decaps ≤ 1168 := by lit_decide
theorem keyGen1024_sdepth : sdepth Impl.MlKem1024.RISCV64.keygen1024 ≤ 1168 := by lit_decide
theorem encapsH1024_sdepth : sdepth Impl.MlKem1024.RISCV64.encapsH1024 ≤ 1168 := by lit_decide
theorem encaps1024_sdepth : sdepth Impl.MlKem1024.RISCV64.encaps1024 ≤ 1168 := by lit_decide
theorem decaps1024_sdepth : sdepth Impl.MlKem1024.RISCV64.decaps1024 ≤ 1168 := by lit_decide

/-! ## The states satisfying the preconditions, with the frame's 32 more bytes of stack -/

/-- A state satisfying a precondition built with `Sig.contract`, after
`sig_apply_check`. -/
macro "wipe_sat " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (sig_apply_check
   · decide +kernel
   · sig_reduce [$ls,*]
     sig_and_intros
     all_goals first
       | exact VG.Proof.MlKem.hMem_h (by decide)
       | trivial
       | decide +kernel))

theorem keyGen_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem.RISCV64.KeyGen.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, RISCV64.abi, RISCV64.argRegs]

theorem encaps_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem.RISCV64.Encaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs]

theorem encapsH_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem.RISCV64.Encaps.satStateH 1184 1088 32768, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
    RISCV64.argRegs]

theorem decaps_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem.RISCV64.Decaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, RISCV64.abi, RISCV64.argRegs]

theorem keyGen1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem1024.RISCV64.KeyGen.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs]

theorem encaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem1024.RISCV64.Encaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, RISCV64.abi, RISCV64.argRegs]

theorem encapsH1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem.RISCV64.Encaps.satStateH 1568 1568 49152, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
    RISCV64.argRegs]

theorem decaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 1200).pre s := by
  refine ⟨Proof.MlKem1024.RISCV64.Decaps.satState, ?_⟩
  wipe_sat [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, RISCV64.abi, RISCV64.argRegs]

/-! ## The functions, with 1200 bytes of stack -/

theorem keyGen_scrubbed : Verified target Impl.MlKem.RISCV64.Wipe.keyGen (Scrubbed.keyGenContract abi 1200) :=
  keyGen_wipe Proof.MlKem.RISCV64.KeyGen.verified keyGen_sdepth keyGen_sat

theorem keyGen_verified : Verified target Impl.MlKem.RISCV64.Wipe.keyGen (Spec.MlKem.keyGenContract abi 1200) :=
  keyGen_scrubbed

theorem encapsH_scrubbed : Verified target Impl.MlKem.RISCV64.Wipe.encapsH (Scrubbed.encapsHContract abi 1200) :=
  encapsH_wipe Proof.MlKem.RISCV64.Encaps.verifiedH encapsH_sdepth encapsH_sat

theorem encapsH_verified : Verified target Impl.MlKem.RISCV64.Wipe.encapsH (Spec.MlKem.encapsHContract abi 1200) :=
  encapsH_scrubbed

theorem encaps_scrubbed : Verified target Impl.MlKem.RISCV64.Wipe.encaps (Scrubbed.encapsContract abi 1200) :=
  encaps_wipe Proof.MlKem.RISCV64.Encaps.verified encaps_sdepth encaps_sat

theorem encaps_verified : Verified target Impl.MlKem.RISCV64.Wipe.encaps (Spec.MlKem.encapsContract abi 1200) :=
  encaps_scrubbed

theorem decaps_scrubbed : Verified target Impl.MlKem.RISCV64.Wipe.decaps (Scrubbed.decapsContract abi 1200) :=
  decaps_wipe Proof.MlKem.RISCV64.Decaps.verified decaps_sdepth decaps_sat

theorem decaps_verified : Verified target Impl.MlKem.RISCV64.Wipe.decaps (Spec.MlKem.decapsContract abi 1200) :=
  decaps_scrubbed

theorem keyGen1024_scrubbed :
    Verified target Impl.MlKem.RISCV64.Wipe.keyGen1024 (Scrubbed.keyGen1024Contract abi 1200) :=
  keyGen1024_wipe Proof.MlKem1024.RISCV64.KeyGen.verified keyGen1024_sdepth keyGen1024_sat

theorem keyGen1024_verified :
    Verified target Impl.MlKem.RISCV64.Wipe.keyGen1024 (Spec.MlKem1024.keyGenContract abi 1200) :=
  keyGen1024_scrubbed

theorem encapsH1024_scrubbed :
    Verified target Impl.MlKem.RISCV64.Wipe.encapsH1024 (Scrubbed.encapsH1024Contract abi 1200) :=
  encapsH1024_wipe Proof.MlKem1024.RISCV64.Encaps.verifiedH encapsH1024_sdepth encapsH1024_sat

theorem encapsH1024_verified :
    Verified target Impl.MlKem.RISCV64.Wipe.encapsH1024 (Spec.MlKem1024.encapsHContract abi 1200) :=
  encapsH1024_scrubbed

theorem encaps1024_scrubbed :
    Verified target Impl.MlKem.RISCV64.Wipe.encaps1024 (Scrubbed.encaps1024Contract abi 1200) :=
  encaps1024_wipe Proof.MlKem1024.RISCV64.Encaps.verified encaps1024_sdepth encaps1024_sat

theorem encaps1024_verified :
    Verified target Impl.MlKem.RISCV64.Wipe.encaps1024 (Spec.MlKem1024.encapsContract abi 1200) :=
  encaps1024_scrubbed

theorem decaps1024_scrubbed :
    Verified target Impl.MlKem.RISCV64.Wipe.decaps1024 (Scrubbed.decaps1024Contract abi 1200) :=
  decaps1024_wipe Proof.MlKem1024.RISCV64.Decaps.verified decaps1024_sdepth decaps1024_sat

theorem decaps1024_verified :
    Verified target Impl.MlKem.RISCV64.Wipe.decaps1024 (Spec.MlKem1024.decapsContract abi 1200) :=
  decaps1024_scrubbed

end VG.Proof.MlKem.RISCV64.Wipe
