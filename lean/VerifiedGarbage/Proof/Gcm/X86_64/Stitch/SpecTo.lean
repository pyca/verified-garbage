import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

/-!
# Interleaved counter mode and GHASH out of place: what the loops need and do

Untrusted: everything here is checked by Lean. Interleaved encryption loops
that read the plaintext from one buffer and write the ciphertext to another
(for `vg_aes_gcm_encrypt_blocks_to`) start from a state `s₀` whose registers
hold the key context (`rdi`), the number of rounds (`rsi`), the counter
(`rdx`), `Y` (`rcx`), the plaintext (`r8`), the number of blocks (`r9`, a
multiple of 16), the output (`r10`) and the working space (`r11`).
`SPreTo s₀` is what they need of it, and `EPostTo` what they do
(`StitchToOkM`): `SPre`/`EPost` (`Stitch/Spec.lean`), with the plaintext
read from `r8`, which nothing writes, and the ciphertext written to `r10`.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom)

section
variable (s₀ : State)

/-- The plaintext, and the output. -/
abbrev sp : Addr := s₀.gpr .r8
abbrev op : Addr := s₀.gpr .r10
abbrev sR : Region := ⟨sp s₀, 16 * nb s₀⟩
abbrev oR : Region := ⟨op s₀, 16 * nb s₀⟩

end

structure SPreTo (M : CtxMode) (s₀ : State) : Prop where
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14
  nb16 : 16 ≤ nb s₀
  nbm : nb s₀ % 16 = 0
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) M.len
  c_in : InRegions s₀.wr (cp s₀) 16
  y_in : InRegions s₀.wr (yp s₀) 16
  s_in : InRegions (s₀.rd ++ s₀.wr) (sp s₀) (16 * nb s₀)
  o_in : InRegions s₀.wr (op s₀) (16 * nb s₀)
  p_in : InRegions s₀.wr (pp s₀) 1024
  /-- What is written is disjoint from what is read, and each from the others. -/
  k_c : (⟨kp s₀, M.len⟩ : Region).Disjoint (cR s₀)
  k_y : (⟨kp s₀, M.len⟩ : Region).Disjoint (yR s₀)
  k_o : (⟨kp s₀, M.len⟩ : Region).Disjoint (oR s₀)
  k_p : (⟨kp s₀, M.len⟩ : Region).Disjoint (pR s₀)
  s_c : (sR s₀).Disjoint (cR s₀)
  s_y : (sR s₀).Disjoint (yR s₀)
  s_o : (sR s₀).Disjoint (oR s₀)
  s_p : (sR s₀).Disjoint (pR s₀)
  o_c : (oR s₀).Disjoint (cR s₀)
  o_y : (oR s₀).Disjoint (yR s₀)
  o_p : (oR s₀).Disjoint (pR s₀)
  p_c : (pR s₀).Disjoint (cR s₀)
  p_y : (pR s₀).Disjoint (yR s₀)
  c_y : (cR s₀).Disjoint (yR s₀)
  wrap_s : (sp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrap_o : (op s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrap_k : (kp s₀).toNat + M.len ≤ 2 ^ 64
  wrap_p : (pp s₀).toNat + 1024 ≤ 2 ^ 64
  /-- What the key context holds, as its kind says. -/
  ok : M.ok s₀.mem (kp s₀)

/-- What the encryption leaves: the plaintext's encryption in the output,
the counter advanced, `Y` continued over the ciphertext, nothing else
written but the working space. -/
structure EPostTo (s₀ s : State) : Prop where
  data : blocksAt s.mem (op s₀) (nb s₀) =
    Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (sp s₀) (nb s₀))
  ctr : blockAt s.mem (cp s₀) = Nat.repeat inc32 (nb s₀) (cb s₀)
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s.mem (op s₀) (nb s₀))
  frame : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- An out-of-place interleaved encryption loop `enc`, for a key context of
kind `M`, meets these contracts. -/
def StitchToOkM (M : CtxMode) (enc : Prog isa) : Prop :=
  ∀ s₀, SPreTo M s₀ → WP isa enc s₀ (EPostTo s₀)

end VG.Proof.Gcm.X86_64.Stitch
