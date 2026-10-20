module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Restore the candidate ABI in a private outgoing frame -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def searchCallValues (p : SearchPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(1, BitVec.ofNat 64 (p.c.rand.length - used)), (2, p.c.B), (3, BitVec.ofNat 64 (p.c.Z / 8))]

def SearchArgs (p : SearchPublic) (used : Nat) (s : State) : Prop :=
  s.gpr .rdi = p.c.op ∧ s.gpr .rsi = BitVec.ofNat 64 p.c.k ∧
  s.gpr .rdx = p.c.up ∧ s.gpr .rcx = BitVec.ofNat 64 p.c.bits ∧
  s.gpr .r8 = BitVec.ofNat 64 p.c.gen ∧ s.gpr .r9 = off p.c.rp used

theorem search_arguments_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block arguments) (allocated 32 s) fun t =>
      SearchArgs p used t ∧
      t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 32 s) t := by
  have scr : Scr (allocated 32 s) p.control 128 := by
    have sc := h.input.control_scr (s := s) h.wr
    obtain ⟨B, o, L, hm, hb, hL, hl⟩ := sc.wr
    exact ⟨⟨B, o, L, List.mem_cons_of_mem _ hm, hb, hL, hl⟩, sc.nowrap⟩
  have hs : ∀ d, d + 8 ≤ 128 → InRegions ((allocated 32 s).rd ++ (allocated 32 s).wr)
      (p.control + BitVec.ofNat 64 d) 8 := fun _ hd => scr.ld hd
  have hw : ∀ d, d + 8 ≤ 32 → InRegions (allocated 32 s).wr
      ((s.gpr .rsp - BitVec.ofNat 64 32) + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨⟨s.gpr .rsp - BitVec.ofNat 64 32, 32⟩, List.mem_cons_self ..,
      Offset.contains_base (s.gpr .rsp - BitVec.ofNat 64 32)
        (n := 8) (d := d) (k := 32) hd (by omega_using [hd])⟩
  simp only [allocated, State.setReg] at hs hw
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used remaining) :
      s.mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv5 := hv 5 p.c.op (by simp [SearchPublic.headers])
  have hv6 := hv 6 (BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
  have hv7 := hv 7 p.c.up (by simp [SearchPublic.headers])
  have hv8 := hv 8 (BitVec.ofNat 64 p.c.bits) (by simp [SearchPublic.headers])
  have hv9 := hv 9 (BitVec.ofNat 64 p.c.gen) (by simp [SearchPublic.headers])
  have hv10 := hv 10 (off p.c.rp used) (by simp [SearchPublic.headers])
  have hv11 := hv 11 (BitVec.ofNat 64 (p.c.rand.length - used)) (by simp [SearchPublic.headers])
  have hv13 := hv 13 p.c.B (by simp [SearchPublic.headers])
  have hv15 := hv 15 (BitVec.ofNat 64 (p.c.Z / 8)) (by simp [SearchPublic.headers])
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (Q := fun t =>
    SearchArgs p used t ∧ t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold arguments SearchArgs writeController searchCallValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, allocated, State.setReg, BitVec.ofInt_ofNat, BitVec.ofInt_natCast,
    Nat.reduceMul, h.r12, hs 40 (by decide), hs 48 (by decide), hs 56 (by decide),
    hs 64 (by decide), hs 72 (by decide), hs 80 (by decide), hs 88 (by decide),
    hs 104 (by decide), hs 120 (by decide), hw 8 (by decide), hw 16 (by decide), hw 24 (by decide),
    hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv13, hv15]
  rfl

end VG.Proof.Ffdh.X86_64.Generation
