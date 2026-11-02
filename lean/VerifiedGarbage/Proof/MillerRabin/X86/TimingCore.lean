module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingCoreState
import VerifiedGarbage.Proof.MillerRabin.X86.TimingTable
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.MillerRabin.X86.TimingMarker
import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquareLoop
import VerifiedGarbage.Proof.MillerRabin.X86.TimingAttach
import VerifiedGarbage.Proof.MillerRabin.X86.TimingSequences
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The complete prepared round has a trace determined by public geometry -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem prepareRun_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (CoreStart g capacity p))
      (.seq (table name code) (.seq (copy aY aOne) (.block initWindows))) (Two g (CoreRun g capacity p)) := by
  refine private_attach ?_ (fun _ _ H => H.prepare verified noSp stack v length) (fun _ _ H => H.1.data.context)
  refine RelCT.seq ((table_relCT (p := p) verified noSp stack v length).mono ?_ (fun _ _ H => H.1))
    (RelCT.seq (copy_relCT v aY aOne (by decide) (by decide))
      (initWindows_trace.mono (fun _ _ H => H.2.2) (fun _ _ H => H)))
  intro s t ⟨P, ⟨σ, S, mathS, _⟩, ⟨ρ, T, mathT, _⟩⟩
  exact ⟨P, ⟨⟨σ.c, σ.A, σ.V, []⟩, S, mathS.1, mathS.2.1⟩,
    ⟨⟨ρ.c, ρ.A, ρ.V, []⟩, T, mathT.1, mathT.2.1⟩⟩

theorem coreWords_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (CoreRun g capacity p)) (.loop (wordStep name code) .ne) (Two g (CoreWords g capacity p)) := by
  refine private_attach ((wordLoop_relCT (p := p) verified noSp stack v length
    (by have := v.minWidth; unfold Geometry.words; omega : 0 < g.words)).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.wordInput, H.2.2.choose_spec.wordInput⟩) (fun _ _ H => H.2.2))
    (fun _ _ H => H.words verified noSp stack v length) (fun _ _ H => H.1.data.context)

theorem coreMarker_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (CoreWords g capacity p)) (.block lastSquares) (Two g (CoreFinal g capacity p)) :=
  private_attach ((lastSquares_trace v).mono (fun _ _ H => H.1) (fun _ _ H => H))
    (fun _ _ H => H.marker v) (fun _ _ H => H.1.data.context)

theorem core_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (CoreStart g capacity p)) (core name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (seqs ([table name code, copy aY aOne, .block initWindows] ++
    [.loop (wordStep name code) .ne, .block lastSquares, squareLoop name code,
      .block [.mov .eax (.mem (slot sFlag))]])) _
  refine seqs_append_relCT _ _ (prepareRun_relCT verified noSp stack v length)
    (RelCT.seq (coreWords_relCT verified noSp stack v length) (RelCT.seq (coreMarker_relCT v) ?_))
  exact RelCT.seq ((squareLoop_relCT (p := p) verified noSp stack v length (by decide : 0 < 3)).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.squareInput, H.2.2.choose_spec.squareInput⟩) (fun _ _ H => H))
    ((checkedBlockInvariant rfl rfl).mono (fun _ _ H => H.2.2) (fun _ _ H => H))

end VG.Proof.MillerRabin.X86
