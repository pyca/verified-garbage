module

public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Spec.GcmSiv
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM-SIV's interleaved loop: what it needs and does

Untrusted: everything here is checked by Lean. The interleaved loop of
`vg_aes_gcm_siv_open` (`Impl.AesGcmSiv.X86_64Stitch.dec`) starts from a
state `s₀` whose registers hold the key schedule (`rdi`), the number of
rounds (`rsi`), the counter block (`rdx`), `Y` (`rcx`) and `H` (`r8`), both
in GHASH's order, the working space (`r11`), the data (`r12`) and its number
of blocks (`r9`, a multiple of 16, at least 16). `SPre s₀` is what it needs
of it, and `DPost` what it does: the data deciphered in counter mode
(RFC 8452 §4, from the counter block as it is), the counter block advanced,
and `Y` continued over the plaintext's blocks, each the field element of its
16 bytes as they are (`Spec.GcmSiv.ofBytes`), with GHASH and the key `H`
(`Proof.GcmSiv.polyvalFrom_eq` relates POLYVAL to it).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

section
variable (s₀ : State)

abbrev kp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev cp : Addr := s₀.gpr .rdx
abbrev yp : Addr := s₀.gpr .rcx
abbrev hp : Addr := s₀.gpr .r8
/-- The working space: the powers (256 bytes). -/
abbrev pp : Addr := s₀.gpr .r11
abbrev dp : Addr := s₀.gpr .r12
abbrev nb : Nat := (s₀.gpr .r9).toNat
abbrev kR : Region := ⟨kp s₀, 240⟩
abbrev cR : Region := ⟨cp s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev pR : Region := ⟨pp s₀, 256⟩
/-- The key schedule, and `CIPH_K`. -/
abbrev sch : List Byte := bytesAt s₀.mem (kp s₀) (16 * (nr s₀ + 1))
abbrev ciph : Spec.GcmSiv.Cipher := Spec.GcmSiv.aesWith (nr s₀) (sch s₀)
/-- The counter block. -/
abbrev icb : List Byte := bytesAt s₀.mem (cp s₀) 16
/-- `H`, and `Y`. -/
abbrev hk : Block := blockAt s₀.mem (hp s₀)
abbrev y₀ : Block := blockAt s₀.mem (yp s₀)
/-- Block `k` of the data, where it starts, and deciphered. -/
abbrev bAddr (k : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : List Byte := bytesAt s₀.mem (bAddr s₀ k) 16
abbrev ctb (k : Nat) : List Byte := Spec.Cmac.xor (blk s₀ k) (ciph s₀ (Spec.GcmSiv.counterBlock (icb s₀) k))

end

structure SPre (s₀ : State) : Prop where
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14
  nb16 : 16 ≤ nb s₀
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 240
  h_in : InRegions (s₀.rd ++ s₀.wr) (hp s₀) 16
  c_in : InRegions s₀.wr (cp s₀) 16
  y_in : InRegions s₀.wr (yp s₀) 16
  d_in : InRegions s₀.wr (dp s₀) (16 * nb s₀)
  p_in : InRegions s₀.wr (pp s₀) 256
  d_k : (dR s₀).Disjoint (kR s₀)
  d_c : (dR s₀).Disjoint (cR s₀)
  d_y : (dR s₀).Disjoint (yR s₀)
  d_p : (dR s₀).Disjoint (pR s₀)
  p_k : (pR s₀).Disjoint (kR s₀)
  p_c : (pR s₀).Disjoint (cR s₀)
  p_y : (pR s₀).Disjoint (yR s₀)
  c_y : (cR s₀).Disjoint (yR s₀)
  c_k : (cR s₀).Disjoint (kR s₀)
  y_k : (yR s₀).Disjoint (kR s₀)
  wrap_d : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrap_k : (kp s₀).toNat + 240 ≤ 2 ^ 64
  wrap_p : (pp s₀).toNat + 256 ≤ 2 ^ 64

/-- What the loop leaves: the data deciphered, the counter block advanced,
`Y` continued over the plaintext, nothing else written but the working
space. -/
structure DPost (s₀ s : State) : Prop where
  data : ∀ k < nb s₀, bytesAt s.mem (bAddr s₀ k) 16 = ctb s₀ k
  ctr : bytesAt s.mem (cp s₀) 16 = Spec.GcmSiv.counterBlock (icb s₀) (nb s₀)
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀)
    ((List.range (nb s₀)).map fun k => Spec.GcmSiv.ofBytes (ctb s₀ k))
  frame : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

end VG.Proof.AesGcmSiv.X86_64.Stitch
