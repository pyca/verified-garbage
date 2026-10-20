module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminal
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout

/-! # Record final candidate consumption and finish native parameter search -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem accept_prefix {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block [
      .mov .rax (.mem (field 7)), .mov .rcx (.mem { base := .rax }),
      .mov .rax (.mem (field 12)), .alu .add .rax (.reg .rcx), .store (field 12) .rax]) s fun t =>
      t.mem = writeController s.mem p.control [(12, BitVec.ofNat 64 used + consumed)] ∧
      Keep [.rax, .rcx] s t := by
  have scr := h.input.control_scr h.wr
  have hs : InRegions s.wr (p.control + BitVec.ofNat 64 96) 8 := scr.st (by decide)
  have hl7 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 56) 8 := scr.ld (by decide)
  have hl12 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 96) 8 := scr.ld (by decide)
  have hup : InRegions (s.rd ++ s.wr) p.c.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_memory h.wr).ld (d := 0) (by decide)
  have hv7 : s.mem.readW (p.control + BitVec.ofNat 64 56) 64 = p.c.up :=
    h.headers (7, p.c.up) (by simp [SearchPublic.headers])
  have hv12 : s.mem.readW (p.control + BitVec.ofNat 64 96) 64 = BitVec.ofNat 64 used :=
    h.headers (12, BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeController
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, h.r12, hs, hl7, hl12, hup, hu, hv7, hv12,
    BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero]

theorem accept_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block accept) s fun t =>
      t.gpr .rax = 1 ∧
      t.mem = writeController s.mem p.control
        ([(12, BitVec.ofNat 64 used + consumed)] ++ terminalValues 1) ∧ Keep [.rax, .rcx] s t := by
  rw [accept, WP.block_append_iff]
  refine WP.mono (accept_prefix h consumed hu) fun u ⟨hm, k⟩ => ?_
  refine WP.mono (terminal_ok (h.input.control_scr (k.2.2.trans h.wr))
    ((k.gpr (by decide)).trans h.r12) 1) fun t ⟨hr, ht, kt⟩ => ?_
  exact ⟨hr, by rw [ht, hm, writeController_append], (k.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
