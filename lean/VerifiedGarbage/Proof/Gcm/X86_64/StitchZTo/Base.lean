module

public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The out-of-place AVX-512 loop: the setting, and the data

Untrusted: everything here is checked by Lean. The out-of-place loop
(`Impl.Gcm.X86_64.StitchZTo`) starts from a state `s₀` meeting
`Stitch.SPreTo`. `dst s₀` is `s₀` with the output in `r8`, where the in-place
loops find their data: it meets `SPre` (`SPreTo.toD`), so that the lemmas of
the in-place proofs about the output, the working space and the GHASH
(stated for any state, through `dp`, `pp`, `bAddr`, …) apply to it. The
plaintext is block `k` at `sAddr s₀ k` (`pblk`), its ciphertext `ctbT`.

`xorDataZTo_ok`: `xorDataZTo t base idx regs j` XORs the lanes of the
registers into the blocks loaded from `base + idx + 64 (j + i)` and stores
them to `base + 64 (j + i)`, for a source and a destination in disjoint
regions, as `VaesZ.xorDataZ_ok` does in place.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreP SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane zmm_lane blockAt_writeW_lane)
open VG.Proof.Aes.X86_64.AesNi (ofInt_natCast inRegions_wr blockAt_frame)
open VG.Proof.Gcm.X86_64 (blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-! ## The in-place view -/

/-- `s₀` with the output in `r8`. -/
def dst (s₀ : State) : State := s₀.setReg .r8 (s₀.gpr .r10)

theorem dst_mem (s₀ : State) : (dst s₀).mem = s₀.mem := rfl
theorem dst_gpr_ne (s₀ : State) {r : Reg} (h : r ≠ .r8) : (dst s₀).gpr r = s₀.gpr r := by
  simp [dst, State.setReg, h]
theorem nb_dst (s₀ : State) : nb (dst s₀) = nb s₀ := rfl
theorem inRegions_prefix {rs : List Region} {a : Addr} {n L : Nat} (h : InRegions rs a L) (hn : n ≤ L) :
    InRegions rs a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, by unfold Region.Contains at *; omega⟩

/-- The in-place loops' view of the out-of-place one's start. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.SPreTo.toD {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) : SPre (dst s₀) where
  rounds := hp.rounds
  nb16 := hp.nb16
  k_in := inRegions_prefix hp.k_in M.ge
  c_in := hp.c_in
  y_in := hp.y_in
  d_in := hp.o_in
  p_in := hp.p_in
  d_k := hp.k_o.symm.sub_right (Region.sub_prefix M.ge)
  d_c := hp.o_c
  d_y := hp.o_y
  d_p := hp.o_p
  p_k := hp.k_p.symm.sub_right (Region.sub_prefix M.ge)
  p_c := hp.p_c
  p_y := hp.p_y
  c_y := hp.c_y
  c_k := hp.k_c.symm.sub_right (Region.sub_prefix M.ge)
  y_k := hp.k_y.symm.sub_right (Region.sub_prefix M.ge)
  wrap_d := hp.wrap_o
  wrap_k := by
    have := hp.wrap_k; have := M.ge
    show (kp s₀).toNat + 256 ≤ 2 ^ 64; omega
  wrap_p := hp.wrap_p

/-- The same, with the powers in the key context. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.SPreTo.toP {s₀ : State} (hp : SPreTo CtxMode.powers s₀) : SPreP (dst s₀) :=
  ⟨hp.toD, hp.k_in, hp.wrap_k, hp.k_o.symm, hp.k_p.symm, hp.ok⟩

/-! ## The plaintext and the ciphertext -/

section
variable (s₀ : State)

/-- Block `k` of the plaintext, where it starts, and encrypted; where block
`k` of the output starts. -/
abbrev sAddr (k : Nat) : Addr := sp s₀ + BitVec.ofNat 64 (16 * k)
abbrev pblk (k : Nat) : Block := blockAt s₀.mem (sAddr s₀ k)
abbrev ctbT (k : Nat) : Block := pblk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀))
abbrev oAddr (k : Nat) : Addr := op s₀ + BitVec.ofNat 64 (16 * k)

end

/-- The source address of the output address `r + x`, `r8` holding
`src - dst`. -/
theorem src_addr {r o s : Addr} {x y : Nat} (h : r + BitVec.ofNat 64 x = o + BitVec.ofNat 64 y) :
    r + (s - o) + BitVec.ofNat 64 x = s + BitVec.ofNat 64 y := by
  rw [BitVec.add_assoc, BitVec.add_comm (s - o), ← BitVec.add_assoc, h, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 y), ← BitVec.add_assoc, BitVec.add_comm o (s - o), BitVec.sub_add_cancel]

/-! ## The data -/

theorem ea_atIx (s : State) (b i : Reg) (d : Nat) :
    s.ea (atIx b i d) = s.gpr b + s.gpr i + BitVec.ofInt 64 (d : Int) := by
  show s.gpr b + s.gpr i * BitVec.ofNat 64 1 + BitVec.ofInt 64 (d : Int) = _
  rw [BitVec.mul_one]

/-- A block disjoint from a region written is kept. -/
theorem blockAt_writeW_out {m : Mem} {p : Addr} {R : Region} {w : Nat} {v : BitVec w}
    (hd : Region.Disjoint ⟨p, 16⟩ R) (hw : w / 8 = R.len) : blockAt (m.writeW R.base v) p = blockAt m p :=
  Stitch.blockAt_writeW_sep' hd hw

end VG.Proof.Gcm.X86_64.StitchZTo
