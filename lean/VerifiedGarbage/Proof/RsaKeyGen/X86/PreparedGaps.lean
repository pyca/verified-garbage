module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame

/-! # The header gap can hold secret preparation data without changing public metadata -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepared
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Mont.X86.Rt

theorem keepGaps {g : Geometry} (v : g.Valid) {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs)
    {ranges : List (Nat × Nat)} (O : Outs g.W ranges s.mem t.mem)
    (header : ∀ r ∈ ranges, (128 ≤ r.1 ∧ r.1 + r.2 ≤ 224) ∨ 256 ≤ r.1) : Context g t := by
  have F := WorkspaceFrame.of_outs C.ws.nowrap O
  have read {d : Nat} (fit : d + 4 ≤ 256)
      (apart : ∀ r ∈ ranges, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) : w32 t.mem g.W d = w32 s.mem g.W d :=
    congrArg BitVec.toNat (F.read32 (Nat.le_trans fit v.headerFit) apart)
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, K.1 .edi base]; exact C.base
  · rw [read (by decide) (fun r mem => by have := header r mem; omega)]
    exact C.width
  · rw [read (by decide) (fun r mem => by have := header r mem; omega)]
    exact C.stride
  · intro j index
    rw [read (by omega) (fun r mem => by have := header r mem; omega)]
    exact C.pointers j index

end VG.Proof.RsaKeyGen.X86.Prepared
