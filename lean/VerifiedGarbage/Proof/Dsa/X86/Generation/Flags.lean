module

import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The search's state words: compared with constants, and set -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation (cmpF stImm)

section
variable {is : List Instr} {s : State} {Q : State → Prop} {base : Addr} {size : Nat}

/-- The word at `o`, `w`, compared with `v`: ZF is `w = v`. -/
theorem cmpF_ok {o v w : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (hw : s.mem.readW (off base o) 32 = BitVec.ofNat 32 w) (hwl : w < 2 ^ 32) (hv : v < 2 ^ 32)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → isa.eval .e s' = some (decide (w = v)) → WP isa (.block is) s' Q) :
    WP isa (.block (cmpF o v ++ is)) s Q := by
  simp only [cmpF, List.cons_append, List.nil_append]
  refine ld_ok hs ho fun s₁ u₁ => wp_cmpi fun s₂ f₂ _ z₂ => k s₂ (fun r hr => by rw [f₂.gpr, u₁.other r hr])
    (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd]) (by rw [f₂.wr, u₁.wr]) (by rw [f₂.syms, u₁.syms]) ?_
  show s₂.zf = _
  rw [z₂, u₁.gpr, hw, sub_beq hwl hv]

/-- The word at `o` := `v`. -/
theorem stImm_ok {o v : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem.writeW (off base o) (BitVec.ofNat 32 v) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (stImm o v ++ is)) s Q := by
  simp only [stImm, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => st_ok (Scr.of_eq hs (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) ho
    fun s₂ M₂ => k s₂ (fun r hr => by rw [M₂.gpr, u₁.other r hr]) (by rw [M₂.mem, u₁.mem, u₁.gpr])
      (by rw [M₂.rd, u₁.rd]) (by rw [M₂.wr, u₁.wr]) (by rw [M₂.syms, u₁.syms])

/-- `cmpF` ending a block. -/
theorem cmpF_end {o v w : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (hw : s.mem.readW (off base o) 32 = BitVec.ofNat 32 w) (hwl : w < 2 ^ 32) (hv : v < 2 ^ 32)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → isa.eval .e s' = some (decide (w = v)) → Q s') :
    WP isa (.block (cmpF o v)) s Q := by
  rw [← List.append_nil (cmpF o v)]
  exact cmpF_ok hs ho hw hwl hv fun s' a b c d e f => WP.block_nil (k s' a b c d e f)

/-- `stImm` ending a block. -/
theorem stImm_end {o v : Nat} (hs : Scr s base size) (ho : o + 4 ≤ size)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem.writeW (off base o) (BitVec.ofNat 32 v) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Q s') :
    WP isa (.block (stImm o v)) s Q := by
  rw [← List.append_nil (stImm o v)]
  exact stImm_ok hs ho fun s' a b c d e => WP.block_nil (k s' a b c d e)

end

end VG.Proof.Dsa.X86.Generation
