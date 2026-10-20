module
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues

/-! # The key-generation controller's writes of its own words -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_word controllerValue
  shift_ofNat)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (1, 0), (3, 0), (14, (BitVec.ofNat 32 status).setWidth 64)]

theorem key_terminal_ok {s : State} {B : Addr} (scr : Scr s B 128) (hb : s.gpr .r12 = B)
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
    hs0, hs 8 (by decide), hs 24 (by decide), hs 112 (by decide)]
  rfl

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The octets consumed by an attempt. -/
def advanceValues (p : KeyPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(9, p.rp + BitVec.ofNat 64 (used + p.len)), (10, BitVec.ofNat 64 (p.randLen - (used + p.len))),
    (11, BitVec.ofNat 64 (used + p.len))]

theorem advanceValues_bound (p : KeyPublic) (used : Nat) : ∀ e ∈ advanceValues p used, e.1 < 16 := by
  simp only [advanceValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_advance_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (.block advance) s fun t =>
      t.mem = writeController s.mem p.control (advanceValues p used) ∧
        Keep [.rcx, .rdx, .rsi, .r8] s t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv2 hv9 hv10 hv11
  have hlen : p.randLen < 2 ^ 64 := by
    rw [← h.input.2]; exact BitVec.isLt _
  have e9 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = p.rp + BitVec.ofNat 64 (used + p.len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e10 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 p.len =
      BitVec.ofNat 64 (p.randLen - (used + p.len)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have e11 : BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = BitVec.ofNat 64 (used + p.len) := by
    rw [← BitVec.ofNat_add]
  refine WP.keep [.rcx, .rdx, .rsi, .r8] ?_ rfl
  unfold advance writeController advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, Nat.reduceMul, hv2, hv9, hv10, hv11,
    hl 16 (by decide), hl 72 (by decide), hl 80 (by decide), hl 88 (by decide),
    hs 72 (by decide), hs 80 (by decide), hs 88 (by decide), e9, e10, e11]

end VG.Proof.Ffdh.X86_64.KeyGeneration
