module

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The attempt's arguments -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- The attempt's stack arguments, in the order the code stores them: `p_len`
twice (as the width and as `rand_len`), the tape's current pointer,
`scratch` and `scratch_len`. -/
def callValues (p : KeyPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.len), (2, BitVec.ofNat 64 p.len), (1, p.rp + BitVec.ofNat 64 used),
    (3, p.B), (4, BitVec.ofNat 64 (p.Z / 8))]

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (t : State) : Prop :=
  t.gpr .rdi = p.xp ∧ t.gpr .rsi = BitVec.ofNat 64 p.len ∧
  t.gpr .rdx = p.yp ∧ t.gpr .rcx = BitVec.ofNat 64 p.len ∧
  t.gpr .r8 = p.dp ∧ t.gpr .r9 = BitVec.ofNat 64 p.dlen

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block arguments) (allocated 40 s) fun t =>
      KeyArgs p t ∧ t.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 40 s) t := by
  have scr : Scr (allocated 40 s) p.control 128 := by
    have sc := h.input.control_scr (t := s) h.wr
    obtain ⟨B, o, L, hm, hb, hL, hl⟩ := sc.wr
    exact ⟨⟨B, o, L, List.mem_cons_of_mem _ hm, hb, hL, hl⟩, sc.nowrap⟩
  have hs : ∀ d, d + 8 ≤ 128 → InRegions ((allocated 40 s).rd ++ (allocated 40 s).wr)
      (p.control + BitVec.ofNat 64 d) 8 := fun _ hd => scr.ld hd
  have hw : ∀ d, d + 8 ≤ 40 → InRegions (allocated 40 s).wr
      ((s.gpr .rsp - BitVec.ofNat 64 40) + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨⟨s.gpr .rsp - BitVec.ofNat 64 40, 40⟩, List.mem_cons_self ..,
      Offset.contains_base (s.gpr .rsp - BitVec.ofNat 64 40)
        (n := 8) (d := d) (k := 40) hd (by omega_using [hd])⟩
  have hw0 : InRegions (allocated 40 s).wr (s.gpr .rsp - BitVec.ofNat 64 40) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  simp only [allocated, State.setReg] at hs hw hw0
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := h.header (j := 5) (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := h.header (j := 6) (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := h.header (j := 7) (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := h.header (j := 8) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := h.header (j := 12) (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := h.header (j := 13) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (Q := fun t =>
    KeyArgs p t ∧ t.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold arguments KeyArgs writeController callValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, allocated, State.setReg, BitVec.ofInt_ofNat, BitVec.ofInt_natCast,
    Nat.reduceMul, BitVec.add_zero, h.r12, hs 16 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 96 (by decide), hs 104 (by decide),
    hw0, hw 8 (by decide), hw 16 (by decide), hw 24 (by decide), hw 32 (by decide),
    hv2, hv5, hv6, hv7, hv8, hv9, hv12, hv13]
  rfl

end VG.Proof.Ffdh.X86_64.KeyGeneration
