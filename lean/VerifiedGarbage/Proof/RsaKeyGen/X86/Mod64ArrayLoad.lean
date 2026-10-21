module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.MillerRabin.ExponentWords32

/-! # Load the next high-to-low candidate word through its public frame pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem ArrayState.loadWord {g : ArrayGeometry} (v : g.Valid) {candidate exponent i : Nat} {s : State}
    (S : ArrayState g candidate exponent i s) (index : i < g.n) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.Mod64.loadWord) s fun t =>
      ArrayState g candidate exponent i t ∧
      t.gpr .esi = VG.Proof.MillerRabin.exponentWord candidate (g.n - 1 - i) ∧
      t.mem = s.mem ∧ Keeps [.eax, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Mod64.loadWord
  refine wp_movS (S.context.stack.read 0 (by decide)) fun a A _ => ?_
  have address : a.ea ⟨.eax, 0⟩ = off g.base (g.src + 4 * (g.n - 1 - i)) := by
    change addr (a.gpr .eax) 0 = _
    rw [A.gpr, S.pointer, ArrayGeometry.pointer_eq index]
    have H := S.context.scratch.ea (d := g.src + 4 * (g.n - 1 - i)) (by have := v.sourceFit; omega)
    change addr (s.gpr .edi) (g.src + 4 * (g.n - 1 - i)) = _ at H
    rw [S.context.workspace] at H
    simpa only [addr, BitVec.add_zero] using H
  have access := (S.context.scratch.of_keeps A.keeps (by decide)).read
    (d := g.src + 4 * (g.n - 1 - i)) (n := 4) (by have := v.sourceFit; omega)
  have read : readSrc a (.mem ⟨.eax, 0⟩) =
      some (s.mem.readW (off g.base (g.src + 4 * (g.n - 1 - i))) 32) := by
    change a.load32 (a.ea ⟨.eax, 0⟩) = _
    rw [address, State.load32, ite_eq_left_iff.mpr (fun bad => absurd access bad), A.mem]
  refine wp_movS read fun t T _ => WP.block_nil ?_
  have K : Keeps [.eax, .esi] s t := (A.keeps.mono (by decide)).widen T.keeps
  have M : t.mem = s.mem := T.mem.trans A.mem
  refine ⟨⟨S.context.keepReadonly K (by decide) (by decide) M, ?_, ?_, ?_, ?_⟩, ?_, M, K⟩
  · rw [M]
    exact S.pointer
  · rw [M]
    exact S.count
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide)]
    exact S.value
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide)]
    exact S.bound
  · rw [T.gpr]
    exact VG.Proof.MillerRabin.read_exponentWord S.context.candidateValue (by omega)

end VG.Proof.RsaKeyGen.X86.Mod64
