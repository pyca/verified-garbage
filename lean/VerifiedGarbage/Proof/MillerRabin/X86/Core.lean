module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RunView
public import VerifiedGarbage.Proof.MillerRabin.X86.ExponentState
public import VerifiedGarbage.Proof.MillerRabin.X86.SquareState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.PrepareRun
import VerifiedGarbage.Proof.MillerRabin.X86.WordLoop
import VerifiedGarbage.Proof.MillerRabin.X86.StageLastSquares
import VerifiedGarbage.Proof.MillerRabin.X86.SquareLoop
import VerifiedGarbage.Proof.MillerRabin.X86.RoundMarker
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.Sequences

/-! # The complete prepared round computes the native fixed-window test -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def finishedState (A : Nat → Nat) (c w N k : Nat) : Nat × Bool :=
  squareState (exponentValues (runValues A c w) c w N false N) c w
    (4 - VG.Proof.RsaKeyGen.sigOf k) 3 (exponentState (runValues A c w) c w N false N).2 3

theorem core_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c k : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A initialArrays V [] s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Xlt : A aX < c) (Olt : A aOne < c) (marker : k < 64)
    (lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32))
    (hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) :
    WP isa (core name code) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (finishedState A c g.w g.words k).2.toNat ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  change WP isa (seqs ([table name code, copy aY aOne, .block initWindows] ++
    [.loop (wordStep name code) .ne, .block lastSquares, squareLoop name code,
      .block [.mov .eax (.mem (slot sFlag))]])) s _
  rw [seqs_append_iff]
  refine WP.mono (prepareRun_ok verified noSp stack v S length odd Xlt) fun a ⟨Sa, Oa, Ka⟩ => ?_
  change WP isa (.seq (.loop (wordStep name code) .ne) (.seq (.block lastSquares)
    (.seq (squareLoop name code) (.block [.mov .eax (.mem (slot sFlag))])))) a _
  have startLt : runValues A c g.w aY < c := by rw [runValues_y]; exact Olt
  have powersLt : ∀ j < 16, runValues A c g.w (aTable + j) < c := by
    intro j digit
    rw [runValues_power A c g.w digit]
    exact Word32.tp_lt (by omega : 0 < c) Xlt Olt j
  have tableOne : runValues A c g.w aTable = runValues A c g.w aOne := by
    rw [← runValues_identity, runValues_y, runValues_one]
  refine WP.seq (WP.mono (wordLoop_ok verified noSp stack v Sa length odd startLt runArrays_y runArrays_one
    runArrays_minus runArrays_exp runArrays_notX (fun _ digit => runArrays_power digit)
    tableOne powersLt false rfl rfl) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  have loB : b.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32) := by
    have R := roundFrame_marker32 v (Oa.trans Ob) (extra := 0) (Or.inl rfl)
    rw [Nat.add_zero] at R
    exact R.trans lo
  have hiB : b.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32) :=
    (roundFrame_marker32 v (Oa.trans Ob) (extra := 4) (Or.inr rfl)).trans hi
  refine WP.seq (WP.mono (Sb.lastSquares v marker loB hiB) fun d ⟨Sd, Od, Kd⟩ => ?_)
  have yBound : exponentValues (runValues A c g.w) c g.w g.words false g.words aY < c := by
    rw [exponentValues, setAt_self]
    exact exponentState_lt (runValues A c g.w) (by omega : 0 < c) g.w g.words false startLt g.words
  refine WP.seq (WP.mono (squareLoop_ok verified noSp stack v Sd length odd yBound runArrays_y runArrays_minus
    (by decide : 0 < 3) (by decide : 3 < 2 ^ 31) (by omega : 4 - VG.Proof.RsaKeyGen.sigOf k < 2 ^ 31)
    (exponentState (runValues A c g.w) c g.w g.words false g.words).2
    (by intro e mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl <;> decide) (by decide) rfl rfl rfl)
    fun e ⟨Se, Oe, Ke⟩ => ?_)
  refine wp_movS (Se.data.context.readScalar sFlag (by have := v.headerFit; unfold sFlag; omega))
    fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, (((Ka.trans Kb).trans Kd).trans Ke).widen T.keeps⟩
  · rw [T.gpr, (Se.data.slotValues sFlag (by decide)).2]
    rfl
  · rw [T.mem]
    exact ((Oa.trans Ob).trans Od).trans Oe

end VG.Proof.MillerRabin.X86
