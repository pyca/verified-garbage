module

import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Entry
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Data
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The attempt's arguments -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- The attempt's stack arguments, in the order the code stores them: `p_len`
twice (as the width and as `rand_len`), the tape's current pointer,
`scratch` and `scratch_len`, then the context and its length. -/
def callValues (p : KeyPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.len), (2, BitVec.ofNat 64 p.len), (1, p.rp + BitVec.ofNat 64 used),
    (3, p.B), (4, BitVec.ofNat 64 (p.Z / 8)), (5, p.ctx), (6, BitVec.ofNat 64 p.ctxLen)]

private theorem readW_writeW_off64 (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat}
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 < 2 ^ 63) (he : e + 8 < 2 ^ 63) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  VG.X86_64.readW_writeW_off m p v (n := 8) hd he h

private theorem readW_writeW_base64 (m : Mem) (p : Addr) (v : BitVec 64) {d : Nat}
    (h : 8 ≤ d) (hd : d + 8 < 2 ^ 63) :
    (m.writeW p v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 := by
  have := readW_writeW_off64 m p v (d := d) (e := 0) (.inr (by omega)) hd (by decide)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (t : State) : Prop :=
  t.gpr .rdi = p.xp ∧ t.gpr .rsi = BitVec.ofNat 64 p.len ∧
  t.gpr .rdx = p.yp ∧ t.gpr .rcx = BitVec.ofNat 64 p.len ∧
  t.gpr .r8 = p.dp ∧ t.gpr .r9 = BitVec.ofNat 64 p.dlen

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Cached.Search.cachedArguments) (allocated 56 s) fun t =>
      KeyArgs p t ∧ t.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 56 s) t := by
  have scr : Scr (allocated 56 s) p.control 128 := by
    have sc := h.input.control_scr (t := s) h.wr
    obtain ⟨B, o, L, hm, hb, hL, hl⟩ := sc.wr
    exact ⟨⟨B, o, L, List.mem_cons_of_mem _ hm, hb, hL, hl⟩, sc.nowrap⟩
  have hs : ∀ d, d + 8 ≤ 128 → InRegions ((allocated 56 s).rd ++ (allocated 56 s).wr)
      (p.control + BitVec.ofNat 64 d) 8 := fun _ hd => scr.ld hd
  have hw : ∀ d, d + 8 ≤ 56 → InRegions (allocated 56 s).wr
      ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨⟨s.gpr .rsp - BitVec.ofNat 64 56, 56⟩, List.mem_cons_self ..,
      Offset.contains_base (s.gpr .rsp - BitVec.ofNat 64 56)
        (n := 8) (d := d) (k := 56) hd (by omega_using [hd])⟩
  have hw0 : InRegions (allocated 56 s).wr (s.gpr .rsp - BitVec.ofNat 64 56) 8 := by
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
  have hsp : s.gpr .rsp = original.gpr .rsp := h.rsp.trans (congrArg KeyPublic.sp h.input.2).symm
  have ha7 : (s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 120 = stackArgAddr original 7 := by
    rw [hsp, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ha8 : (s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 128 = stackArgAddr original 8 := by
    rw [hsp, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hr7 : InRegions ((allocated 56 s).rd ++ (allocated 56 s).wr)
      ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 120) 8 := by
    rw [ha7]
    obtain ⟨r, hr, hc⟩ := input_args h.input 7 (by decide)
    refine ⟨r, ?_, hc⟩
    change r ∈ s.rd ++ (_ :: s.wr)
    rw [h.rd, h.wr]
    simp only [List.mem_append, List.mem_cons] at hr ⊢
    rcases hr with hr | hr
    exacts [.inl hr, .inr (.inr hr)]
  have hr8 : InRegions ((allocated 56 s).rd ++ (allocated 56 s).wr)
      ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 128) 8 := by
    rw [ha8]
    obtain ⟨r, hr, hc⟩ := input_args h.input 8 (by decide)
    refine ⟨r, ?_, hc⟩
    change r ∈ s.rd ++ (_ :: s.wr)
    rw [h.rd, h.wr]
    simp only [List.mem_append, List.mem_cons] at hr ⊢
    rcases hr with hr | hr
    exacts [.inl hr, .inr (.inr hr)]
  have hc7 : s.mem.readW ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 120) 64 = p.ctx := by
    rw [ha7, h.args 7 (by decide), ← h.input.2]; rfl
  have hc8 : s.mem.readW ((s.gpr .rsp - BitVec.ofNat 64 56) + BitVec.ofNat 64 128) 64 =
      BitVec.ofNat 64 p.ctxLen := by
    rw [ha8, h.args 8 (by decide), ← h.input.2]; simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  simp only [allocated, State.setReg] at hr7 hr8
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (Q := fun t =>
    KeyArgs p t ∧ t.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold VG.Impl.Ffdh.X86_64.Cached.Search.cachedArguments arguments KeyArgs writeController callValues
  simp only [List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append]
  xrun [State.ea, field, off, allocated, State.setReg, BitVec.ofInt_ofNat, BitVec.ofInt_natCast,
    Nat.reduceMul, BitVec.add_zero, h.r12, hs 16 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 96 (by decide), hs 104 (by decide),
    hw0, hw 8 (by decide), hw 16 (by decide), hw 24 (by decide), hw 32 (by decide),
    hw 40 (by decide), hw 48 (by decide), hr7, hr8, hc7, hc8,
    hv2, hv5, hv6, hv7, hv8, hv9, hv12, hv13]
  simp (disch := decide) only [readW_writeW_off64, readW_writeW_base64]
  rw [hc7, hc8]
  rfl

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
