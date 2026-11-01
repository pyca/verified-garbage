module
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument

import VerifiedGarbage.Proof.Dsa.X86.OpenScratch
import VerifiedGarbage.Proof.Dsa.X86.SaveArguments
import VerifiedGarbage.Proof.Dsa.X86.EntryFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer

/-! # Complete cdecl argument installation and packed-key pointer expansion -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem installArguments_precise (args : List (Nat × Field)) {s : State} {base : Addr}
    {size scratchArg keyArg pLenArg qLenArg : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (Entry.argument scratchArg)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 8272 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size)
    (distinct : (args.map Prod.snd).Nodup)
    (inputs : ∀ a ∈ args, StackArgument s base size a.1)
    (fields : ∀ a ∈ args, a.2 ∉ [.q, .g, .y, .x])
    (keyMem : (keyArg, .p) ∈ args) (pLenMem : (pLenArg, .pLen) ∈ args) (qLenMem : (qLenArg, .qLen) ∈ args) :
    WP isa (.block (Entry.openScratch scratchArg ++ Entry.saveArguments args ++ Entry.keyPointers)) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr Entry.savedRegisters ∧
      (∀ a ∈ args, pointerValue base t (.input a.2) = stackValue s a.1) ∧
      pointerValue base t (.input .q) = stackValue s keyArg + stackValue s pLenArg ∧
      pointerValue base t (.input .g) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg ∧
      pointerValue base t (.input .y) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg ∧
      pointerValue base t (.input .x) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg + stackValue s pLenArg ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 8272 s.mem t.mem := by
  have savedSize : Layout.saved ≤ size := by change 8256 ≤ size; omega
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (openScratch_precise read hb hf hz hw stk) fun s1 ⟨Sc1, S1, K1, O1⟩ => ?_)
  refine WP.block_append (WP.mono (saveArguments_ok args Sc1 savedSize distinct
    (fun a ha => (inputs a ha).keep K1 (by decide))) fun s2 ⟨Values, _, K2, O2⟩ => ?_)
  have Sc2 := Sc1.of_keeps K2 (by decide)
  have Original (a : Nat × Field) (ha : a ∈ args) : pointerValue base s2 (.input a.2) = stackValue s a.1 :=
    (Values a ha).trans ((inputs a ha).value_keep K1 (by decide) (O1.mono (Nat.le_refl _) (by omega)))
  refine WP.mono (keyPointers_ok (key := stackValue s keyArg) (plen := stackValue s pLenArg) (qlen := stackValue s qLenArg)
    Sc2 savedSize (Original (keyArg, .p) keyMem) (Original (pLenArg, .pLen) pLenMem) (Original (qLenArg, .qLen) qLenMem))
    fun t ⟨Q, G, Y, X, K3, O3⟩ => ?_
  have Oheader := keyPointerFrame_header O3
  refine ⟨Sc2.of_keeps K3 (by decide), saved_header Oheader (saved_header O2 S1), ?_, Q, G, Y, X,
    K1.trans ((K2.trans K3).mono (by decide)), ?_⟩
  · intro a ha
    exact (keyPointerFrame_field O3 (fields a ha)).trans (Original a ha)
  · exact O1.trans ((O2.trans Oheader).mono (by omega) (by omega))

theorem installArguments_ok (args : List (Nat × Field)) {s : State} {base : Addr}
    {size scratchArg keyArg pLenArg qLenArg : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (Entry.argument scratchArg)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 8272 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size)
    (distinct : (args.map Prod.snd).Nodup)
    (inputs : ∀ a ∈ args, StackArgument s base size a.1)
    (fields : ∀ a ∈ args, a.2 ∉ [.q, .g, .y, .x])
    (keyMem : (keyArg, .p) ∈ args) (pLenMem : (pLenArg, .pLen) ∈ args) (qLenMem : (qLenArg, .qLen) ∈ args) :
    WP isa (.block (Entry.openScratch scratchArg ++ Entry.saveArguments args ++ Entry.keyPointers)) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr Entry.savedRegisters ∧
      (∀ a ∈ args, pointerValue base t (.input a.2) = stackValue s a.1) ∧
      pointerValue base t (.input .q) = stackValue s keyArg + stackValue s pLenArg ∧
      pointerValue base t (.input .g) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg ∧
      pointerValue base t (.input .y) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg ∧
      pointerValue base t (.input .x) = stackValue s keyArg + stackValue s pLenArg + stackValue s qLenArg + stackValue s pLenArg + stackValue s pLenArg ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem :=
  WP.mono (installArguments_precise args read hb hf hz hw stk distinct inputs fields keyMem pLenMem qLenMem)
    fun _ ⟨S,V,A,Q,G,Y,X,K,O⟩ => ⟨S,V,A,Q,G,Y,X,K,O.mono (Nat.le_refl _) (by omega)⟩

end VG.Proof.Dsa.X86
