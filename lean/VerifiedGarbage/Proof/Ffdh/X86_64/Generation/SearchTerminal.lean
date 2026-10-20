module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Native terminal policy transitions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (14, (BitVec.ofNat 32 status).setWidth 64)]

theorem terminal_ok {s : State} {B : Addr} (scr : Scr s B 128) (hb : s.gpr .r12 = B)
    (status : Nat) :
    WP isa (.block (terminal status)) s fun t =>
      t.gpr .rax = (BitVec.ofNat 32 status).setWidth 64 ∧
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.rax] s t := by
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions s.wr B 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = (BitVec.ofNat 32 status).setWidth 64 ∧
    t.mem = writeController s.mem B (terminalValues status)) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold terminal writeController terminalValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, hb, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    hs0, hs 24 (by decide), hs 112 (by decide)]
  rfl

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

end VG.Proof.Ffdh.X86_64.Generation
