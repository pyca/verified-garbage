module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Interleaved counter mode and GHASH on AArch64: what the loops need and do

Untrusted: everything here is checked by Lean. `Impl.Gcm.AArch64.Stitch`'s
`enc` and `dec` run inline in AES-GCM's path for TLS records, from a state
`s₀` whose registers hold the working space `W` (`x19`), the streaming state
(`x20`: `Y` at `+ 16` and the counter block at `+ 48`), the key context
(`x21`: the schedule, and the hash subkey at `+ 240`), the number of rounds
(`x22`), the text (`x23`) and its length (`x26`). `KPre s₀` is what they
need, with the table of keys at `W + 512` (`TblOk`), and `EPost`, `DPost`
what they do to the first `128 ⌊len / 128⌋` bytes (`nb` batches of eight
blocks), as `vg_aes_ctr32` and `vg_ghash` would; `KPreM` and `DPostT` the
same for the decryption that stores the plaintext to `op s₀ to`, over the
text or, out of place, to a destination at `x15`. This module states them
without the algebra of their proofs.
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)

section
variable (s₀ : State)

abbrev wp : Addr := s₀.gpr .x19
abbrev stp : Addr := s₀.gpr .x20
abbrev kc : Addr := s₀.gpr .x21
abbrev rounds : Nat := (s₀.gpr .x22).toNat
abbrev dp : Addr := s₀.gpr .x23
/-- The batches of eight blocks. -/
abbrev nb : Nat := (s₀.gpr .x26).toNat / 128
abbrev yR : Region := ⟨stp s₀ + BitVec.ofNat 64 16, 16⟩
abbrev cR : Region := ⟨stp s₀ + BitVec.ofNat 64 48, 16⟩
abbrev kR : Region := ⟨kc s₀, 256⟩
abbrev dR : Region := ⟨dp s₀, 128 * nb s₀⟩
abbrev tR : Region := ⟨wp s₀ + BitVec.ofNat 64 512, 192⟩
/-- The key schedule, and `CIPH_K`. -/
abbrev ksch : List Byte := Spec.Aes.bytesAt s₀.mem (kc s₀) (16 * (rounds s₀ + 1))
abbrev ciph : Block → Block := aesWith (rounds s₀) (ksch s₀)
abbrev icb : Block := blockAt s₀.mem (stp s₀ + BitVec.ofNat 64 48)
abbrev hk : Block := blockAt s₀.mem (kc s₀ + BitVec.ofNat 64 240)
abbrev y₀ : Block := blockAt s₀.mem (stp s₀ + BitVec.ofNat 64 16)

end

structure KPre (s₀ : State) : Prop where
  rounds : rounds s₀ = 10 ∨ rounds s₀ = 12 ∨ rounds s₀ = 14
  nb1 : 1 ≤ nb s₀
  k_in : InRegions (s₀.rd ++ s₀.wr) (kc s₀) 256
  y_in : InRegions s₀.wr (stp s₀ + BitVec.ofNat 64 16) 16
  c_in : InRegions s₀.wr (stp s₀ + BitVec.ofNat 64 48) 16
  d_in : InRegions s₀.wr (dp s₀) (128 * nb s₀)
  t_in : InRegions (s₀.rd ++ s₀.wr) (wp s₀ + BitVec.ofNat 64 512) 192
  d_k : (dR s₀).Disjoint (kR s₀)
  d_y : (dR s₀).Disjoint (yR s₀)
  d_c : (dR s₀).Disjoint (cR s₀)
  d_t : (dR s₀).Disjoint (tR s₀)
  y_c : (yR s₀).Disjoint (cR s₀)
  wrap_d : (dp s₀).toNat + 128 * nb s₀ ≤ 2 ^ 64
  wrap_k : (kc s₀).toNat + 256 ≤ 2 ^ 64
  wrap_t : (wp s₀).toNat + 704 ≤ 2 ^ 64
  wrap_s : (stp s₀).toNat + 64 ≤ 2 ^ 64
  tbl : TblOk s₀.mem (wp s₀) (hk s₀)

/-- The registers the loops write. -/
abbrev kRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

section
variable (s₀ : State)

/-- Where the decryption stores the plaintext: over the text, or, out of
place (`to`), to the destination at `x15`. -/
abbrev op (to : Bool) : Addr := cond to (s₀.gpr .x15) (dp s₀)
abbrev oR (to : Bool) : Region := ⟨op s₀ to, 128 * nb s₀⟩

theorem op_false : op s₀ false = dp s₀ := rfl

end

/-- The registers the decryption writes: out of place, `x15` too. -/
abbrev kRegsT (to : Bool) : List Reg := cond to (.x15 :: kRegs) kRegs

/-- `KPre` for the decryption that stores to `op s₀ to`: the text only read,
the output written, apart from the key, `Y`, the counter block, the table
and (out of place) the text. -/
structure KPreM (s₀ : State) (to : Bool) : Prop where
  rounds : rounds s₀ = 10 ∨ rounds s₀ = 12 ∨ rounds s₀ = 14
  nb1 : 1 ≤ nb s₀
  k_in : InRegions (s₀.rd ++ s₀.wr) (kc s₀) 256
  y_in : InRegions s₀.wr (stp s₀ + BitVec.ofNat 64 16) 16
  c_in : InRegions s₀.wr (stp s₀ + BitVec.ofNat 64 48) 16
  d_in : InRegions (s₀.rd ++ s₀.wr) (dp s₀) (128 * nb s₀)
  o_in : InRegions s₀.wr (op s₀ to) (128 * nb s₀)
  t_in : InRegions (s₀.rd ++ s₀.wr) (wp s₀ + BitVec.ofNat 64 512) 192
  d_k : (dR s₀).Disjoint (kR s₀)
  o_k : (oR s₀ to).Disjoint (kR s₀)
  o_y : (oR s₀ to).Disjoint (yR s₀)
  o_c : (oR s₀ to).Disjoint (cR s₀)
  o_t : (oR s₀ to).Disjoint (tR s₀)
  d_o : to = true → (dR s₀).Disjoint (oR s₀ to)
  y_c : (yR s₀).Disjoint (cR s₀)
  wrap_d : (dp s₀).toNat + 128 * nb s₀ ≤ 2 ^ 64
  wrap_o : (op s₀ to).toNat + 128 * nb s₀ ≤ 2 ^ 64
  wrap_k : (kc s₀).toNat + 256 ≤ 2 ^ 64
  wrap_t : (wp s₀).toNat + 704 ≤ 2 ^ 64
  wrap_s : (stp s₀).toNat + 64 ≤ 2 ^ 64
  tbl : TblOk s₀.mem (wp s₀) (hk s₀)

/-- What the encryption leaves: the batches encrypted, the counter advanced,
`Y` continued over the ciphertext, and nothing else written. -/
structure EPost (s₀ s : State) : Prop where
  data : blocksAt s.mem (dp s₀) (8 * nb s₀) = ctr32 (ciph s₀) (icb s₀) (blocksAt s₀.mem (dp s₀) (8 * nb s₀))
  ctr : blockAt s.mem (stp s₀ + BitVec.ofNat 64 48) = Nat.repeat inc32 (8 * nb s₀) (icb s₀)
  y : blockAt s.mem (stp s₀ + BitVec.ofNat 64 16) =
    ghashFrom (hk s₀) (y₀ s₀) (blocksAt s.mem (dp s₀) (8 * nb s₀))
  frame : Frame [yR s₀, cR s₀, dR s₀] s₀.mem s.mem
  gpr : ∀ r, r ∉ kRegs → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the decryption leaves: the batches decrypted, the counter advanced,
`Y` continued over the batches as they were, and nothing else written. -/
structure DPost (s₀ s : State) : Prop where
  data : blocksAt s.mem (dp s₀) (8 * nb s₀) = ctr32 (ciph s₀) (icb s₀) (blocksAt s₀.mem (dp s₀) (8 * nb s₀))
  ctr : blockAt s.mem (stp s₀ + BitVec.ofNat 64 48) = Nat.repeat inc32 (8 * nb s₀) (icb s₀)
  y : blockAt s.mem (stp s₀ + BitVec.ofNat 64 16) =
    ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (8 * nb s₀))
  frame : Frame [yR s₀, cR s₀, dR s₀] s₀.mem s.mem
  gpr : ∀ r, r ∉ kRegs → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the decryption to `op s₀ to` leaves: `DPost`, with the plaintext
at the output. -/
structure DPostT (s₀ : State) (to : Bool) (s : State) : Prop where
  data : blocksAt s.mem (op s₀ to) (8 * nb s₀) =
    ctr32 (ciph s₀) (icb s₀) (blocksAt s₀.mem (dp s₀) (8 * nb s₀))
  ctr : blockAt s.mem (stp s₀ + BitVec.ofNat 64 48) = Nat.repeat inc32 (8 * nb s₀) (icb s₀)
  y : blockAt s.mem (stp s₀ + BitVec.ofNat 64 16) =
    ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (8 * nb s₀))
  frame : Frame [yR s₀, cR s₀, oR s₀ to] s₀.mem s.mem
  gpr : ∀ r, r ∉ kRegsT to → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

end VG.Proof.Gcm.AArch64.Stitch
