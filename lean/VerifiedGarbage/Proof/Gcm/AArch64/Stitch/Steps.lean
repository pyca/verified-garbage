module

import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Gcm.AArch64.Stitch.Base`, which this module and modules that import it used -/

section

/-! ### `Gcm.AArch64.Stitch.Spec`, which this module and modules that import it used -/

section

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

/-- `KPre` for the decryption that stores to `op s₀ to`: the text only read
(it may overlap the key), the output written, apart from the key, `Y`, the counter block, the table
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

end

end

/-!
# Interleaved counter mode and GHASH on AArch64: the invariant of the loops

Untrusted: everything here is checked by Lean. After `c` batches encrypted
and `h` hashed, `LInv` holds: the first `8 c` blocks XORed with the keystream
(`DataInv`, as for `vg_aes_ctr32_aes`), `Y` (in `v16`, as loaded) GHASH of
the first `8 h` blocks `hb` (the ciphertext's for `seal`, `blockC`, the
text's as it was for `open`, `blockO`), and the pointer, the counter and the
count. `aesStep` and `ghStep` say what each part does to it, and `stores_ok`
what storing the eight blocks does.
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv DataInvM dataInvM_self dataInvM_frame dataInvM_store1 ctr32_of_dataInvM keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

section
variable (s₀ : State)

/-- The keystream, byte by byte. -/
abbrev kst : Nat → Byte := keyStream (rounds s₀) (ksch s₀) (icb s₀)
/-- The counter of the first counter block. -/
abbrev ctr0 : BitVec 32 := (icb s₀).extractLsb' 0 32
/-- Block `i` of the text as it was, and encrypted. -/
abbrev blockO (i : Nat) : Block := blockAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * i))
abbrev blockC (i : Nat) : Block := blockO s₀ i ^^^ ciph s₀ (Nat.repeat inc32 i (icb s₀))
/-- GHASH of the first `n` blocks of `hb`. -/
abbrev yh (hb : Nat → Block) (n : Nat) : Block := ghashFrom (hk s₀) (y₀ s₀) ((List.range n).map hb)

end

/-- The invariant of the loops, after `c` batches encrypted and `h` hashed,
the output at `op s₀ to` (`to` only for the decryption). -/
structure LInv (s₀ : State) (to : Bool) (hb : Nat → Block) (c h : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  x9 : s.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * h)
  x10 : s.read .w .x10 = ctr0 s₀ + BitVec.ofNat 32 (8 * c)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (nb s₀ - c)
  xo : to = true → s.gpr .x15 = s₀.gpr .x15 + BitVec.ofNat 64 (128 * c)
  gpr : ∀ r, r ∉ kRegsT to → s.gpr r = s₀.gpr r
  y : s.v Y = ext8 (yh s₀ hb (8 * h)) (yh s₀ hb (8 * h))
  cr : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly
  data : DataInvM s₀.mem s.mem (dp s₀) (op s₀ to) (8 * nb s₀) (8 * c) (kst s₀)
  frame : Frame [oR s₀ to] s₀.mem s.mem
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- A register the decryption keeps, in either mode. -/
theorem notMem_kRegsT {r : Reg} (to : Bool) (h : r ∉ Reg.x15 :: kRegs) : r ∉ kRegsT to := by
  cases to with
  | false => exact fun h' => h (List.mem_cons_of_mem _ h')
  | true => exact h

theorem kRegsT_not {r : Reg} {to : Bool} (h : r ∉ kRegsT to) : r ∉ kRegs ∧ (to = true → r ≠ .x15) := by
  cases to with
  | false => exact ⟨h, nofun⟩
  | true => exact ⟨fun h' => h (List.mem_cons_of_mem _ h'), fun _ e => h (e ▸ List.mem_cons_self ..)⟩

/-! ## Memory -/

theorem read_eq_readW (m : Mem) (p : Addr) : m.read p 16 = m.readW p 128 := by
  simp [Mem.readW]

/-- The in-place precondition, as the decryption's to the text. -/
theorem KPre.toM {s₀ : State} (hp : KPre s₀) : KPreM s₀ false where
  rounds := hp.rounds
  nb1 := hp.nb1
  k_in := hp.k_in
  y_in := hp.y_in
  c_in := hp.c_in
  d_in := Proof.Aes.AArch64.Aese.inRegions_wr hp.d_in
  o_in := hp.d_in
  t_in := hp.t_in
  o_k := hp.d_k
  o_y := hp.d_y
  o_c := hp.d_c
  o_t := hp.d_t
  d_o := nofun
  y_c := hp.y_c
  wrap_d := hp.wrap_d
  wrap_o := hp.wrap_d
  wrap_k := hp.wrap_k
  wrap_t := hp.wrap_t
  wrap_s := hp.wrap_s
  tbl := hp.tbl

/-- The decryption's precondition over the text is `KPre`. -/
theorem KPreM.toKPre {s₀ : State} (hp : KPreM s₀ false) : KPre s₀ where
  rounds := hp.rounds
  nb1 := hp.nb1
  k_in := hp.k_in
  y_in := hp.y_in
  c_in := hp.c_in
  d_in := hp.o_in
  t_in := hp.t_in
  d_k := hp.o_k
  d_y := hp.o_y
  d_c := hp.o_c
  d_t := hp.o_t
  y_c := hp.y_c
  wrap_d := hp.wrap_d
  wrap_k := hp.wrap_k
  wrap_t := hp.wrap_t
  wrap_s := hp.wrap_s
  tbl := hp.tbl

namespace KPreM
variable {s₀ : State} {to : Bool} (hp : KPreM s₀ to)
include hp

theorem n16 : 128 * nb s₀ < 2 ^ 64 := by
  have := hp.wrap_o
  have h1 := hp.nb1
  rcases Nat.lt_or_ge (128 * nb s₀) (2 ^ 64) with h | h
  · exact h
  · exfalso
    have := hp.o_k (kc s₀) (by
      simp only [Region.Contains]
      have := (kc s₀ - op s₀ to).isLt
      omega_using [h]) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat]; omega_using [])
    exact this

theorem c_frame {m : Mem} (hf : Frame [oR s₀ to] s₀.mem m) :
    blockAt m (stp s₀ + BitVec.ofNat 64 48) = icb s₀ :=
  Proof.Gcm.blockAt_congr fun _ hk => hf.bytes (R := cR s₀)
    (by simp only [List.mem_singleton, forall_eq]; exact hp.o_c.symm) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem t_frame {m : Mem} (hf : Frame [oR s₀ to] s₀.mem m) {o : Nat} (ho : o + 16 ≤ 192) :
    m.readW (wp s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 o) 128 =
      s₀.mem.readW (wp s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 o) 128 :=
  hf.readW (r := tR s₀) (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho]))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.o_t.symm) (by decide)

theorem sch_frame {m : Mem} (hf : Frame [oR s₀ to] s₀.mem m) :
    Spec.Aes.bytesAt m (kc s₀) (16 * (Stitch.rounds s₀ + 1)) = ksch s₀ := by
  have hR := hp.rounds
  exact Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.o_k.symm.sub_left (Region.sub_prefix (by omega_using [hR]))) (by omega_using [hR])

end KPreM

/-- The text from batch `c` on, as it was: in place, not yet written; out of
place, never written. -/
theorem LInv.src {s₀ : State} {to : Bool} (hp : KPreM s₀ to) {hb : Nat → Block} {c h : Nat} {s : State}
    (hI : LInv s₀ to hb c h s) {i : Nat} (hc : 16 * (8 * c) ≤ i) (hi : i < 16 * (8 * nb s₀)) :
    s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  cases to with
  | false =>
    have := hI.data i hi
    rw [ite_eq_right (by omega_using [hc])] at this
    exact this
  | true =>
    have hn := hp.n16
    exact hI.frame.bytes (R := ⟨dp s₀, 16 * (8 * nb s₀)⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.d_o rfl).sub_left (Region.sub_prefix (by omega_using []))) (by simp only; omega_using [hn]) hi

/-! ## The blocks -/

/-- A block XORed with the keystream, by `DataInv`. -/
theorem blockAt_of_dataInv {m₀ m : Mem} {D : Addr} {n k R : Nat} {w : List Byte} {icb : Block}
    (h : DataInv m₀ m D n k (keyStream R w icb)) {i : Nat} (hi : i < k) (hk : k ≤ n) :
    blockAt m (D + BitVec.ofNat 64 (16 * i)) =
      blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) ^^^ aesWith R w (Nat.repeat inc32 i icb) := by
  refine Proof.Aes.block_ext fun t ht => ?_
  rw [Proof.Aes.toBytes_xor _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht,
    BitVec.add_assoc, ← BitVec.ofNat_add, h _ (by omega_using [hi, hk, ht]), ite_eq_left (by omega_using [hi, ht])]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [Proof.Aes.toBytes_ofBytes (by simp) ht, keyStream, show (16 * i + t) / 16 = i by omega_using [ht],
    show (16 * i + t) % 16 = t by omega_using [ht], Proof.Aes.getD_eq _ ht, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem ht, Option.getD_some]
  rfl

/-- A block not yet XORed. -/
theorem blockAt_of_dataInv' {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte}
    (h : DataInv m₀ m D n k ks) {i : Nat} (hi : k ≤ i) (hn : i < n) :
    blockAt m (D + BitVec.ofNat 64 (16 * i)) = blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) := by
  refine Proof.Aes.block_ext fun t ht => ?_
  rw [Proof.Aes.toBytes_blockAt _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add,
    h _ (by omega_using [hn, ht]), ite_eq_right (by omega_using [hi])]
  exact BitVec.xor_zero

/-- The blocks of `ctr32`. -/
theorem ctr32_eq_map (ciph : Block → Block) (icb : Block) (m : Mem) (D : Addr) (n : Nat) :
    ctr32 ciph icb (blocksAt m D n) =
      (List.range n).map fun i => blockAt m (D + BitVec.ofNat 64 (16 * i)) ^^^ ciph (Nat.repeat inc32 i icb) := by
  apply List.ext_getElem (by simp [ctr32, Spec.Gcm.keystream, blocksAt])
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₂
  have h := Proof.Gcm.ctr32_getD ciph icb (blocksAt m D n) (q := i) (by rw [Proof.Gcm.length_blocksAt]; exact h₂)
  rw [Proof.Gcm.blocksAt_getD _ _ _ h₂] at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some] at h
  rw [h]; simp

theorem ghashFrom_append (H y : Block) (a b : List Block) :
    ghashFrom H y (a ++ b) = ghashFrom H (ghashFrom H y a) b := by
  simp only [ghashFrom, List.foldl_append]

theorem range_map_add (f : Nat → Block) (n : Nat) :
    (List.range (n + 8)).map f = (List.range n).map f ++ (List.range 8).map fun j => f (n + j) := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

/-- `ghPart` from the eight blocks `hb (n + j)` and the table. -/
theorem gh8V_congr {y y' : BitVec 128} {b b' S S' KP KP' : Nat → BitVec 128} (hy : y = y')
    (hb : ∀ j < 8, b j = b' j) (hS : ∀ k, 1 ≤ k → k ≤ 8 → S k = S' k) (hK : ∀ p < 4, KP p = KP' p) :
    gh8V y b S KP = gh8V y' b' S' KP' := by
  subst hy
  simp only [gh8V, pa, pb, pk, pl]
  rw [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hS 1 (by decide) (by decide),
    hS 2 (by decide) (by decide), hS 3 (by decide) (by decide), hS 4 (by decide) (by decide),
    hS 5 (by decide) (by decide), hS 6 (by decide) (by decide), hS 7 (by decide) (by decide),
    hS 8 (by decide) (by decide), hK 0 (by decide), hK 1 (by decide), hK 2 (by decide), hK 3 (by decide)]

end VG.Proof.Gcm.AArch64.Stitch

end

end

/-! ### `Gcm.AArch64.Stitch.GhBits`, which this module and modules that import it used -/

section

/-!
# Interleaved counter mode and GHASH on AArch64: GHASH's instructions

Untrusted: everything here is checked by Lean. `ghPart_ok`: `ghPart`
(`Impl.Gcm.AArch64.Stitch`) leaves in `Y` (`v16`) the `gh8V` of `Y`, the eight
blocks at `x9` as loaded, and the powers and keys of the table at `x19`
(`Ops.lean`), writing only `v16` and `v18`–`v29`: a pair of blocks and its products
(`pair_ok`), added (`addFirst_ok`, `addNext_ok`), and the reduction
(`reduce_ok`), each as bits.
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.Proof.Gcm.AArch64.Pmull (Prod reduce ext8 VOnly v_setV gpr_setV mem_setV rd_setV wr_setV sp_setV
  exec_pmull0 exec_pmull1 exec_eor exec_ext8 eor_ok loadRev_ok vdword_xor vdword_append_0 vdword_append_1)
open VG.Impl.Gcm.AArch64.Stitch

/-- The registers `ghPart` writes. -/
abbrev ghV : List VReg :=
  [.v16, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29]

/-- The product registers. -/
def prodS (s : State) : Prod := ⟨s.v LO, s.v MID, s.v HI⟩

theorem exec_eor3 (d n m a : VReg) (s : State) :
    exec (.vop (.eor3 d n m a)) s = some (s.setV d (s.v n ^^^ s.v m ^^^ s.v a)) := rfl

theorem exec_trn (op : VPermOp) (d n m : VReg) (s : State) :
    exec (.vop (.perm op .d2 d n m)) s = some (s.setV d (op.eval .d2 (s.v n) (s.v m))) := rfl

theorem trn_sum (a b : BitVec 128) :
    VPermOp.eval .trn1 .d2 a b ^^^ VPermOp.eval .trn2 .d2 a b =
      ofVDwords (vdword a 0 ^^^ vdword a 1) (vdword b 0 ^^^ vdword b 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VG.AArch64.ofVDwords, VG.AArch64.vdword, VPermOp.eval, VArr.lanes, VArr.ofLanes, VG.Proof.Gcm.Clmul.ofVDwords, VG.Proof.Gcm.Clmul.vdword, BitVec.getLsbD_xor,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64 <;> simp [h, hi, List.getD] <;> omega

/-! ## A pair of blocks -/

theorem vdword_ofVDwords0 (a b : BitVec 64) : vdword (ofVDwords a b) 0 = a := vdword_append_0 _ _
theorem vdword_ofVDwords1 (a b : BitVec 64) : vdword (ofVDwords a b) 1 = b := vdword_append_1 _ _

/-- Block `j` of the eight at `x9`, as loaded. -/
def blkV (s : State) (j : Nat) : BitVec 128 :=
  VRevOp.eval .rev64b (s.mem.read (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16)

/-- The table's value at `x19 + o`. -/
def tblV (s : State) (o : Nat) : BitVec 128 := s.mem.read (s.gpr .x19 + BitVec.ofNat 64 o) 16

/-- The rest of a pair: the keys loaded, the sums of the blocks' halves
packed, and the six products. -/
theorem pairTail_ok (p k l : Nat) (s : State) (hk : sOff k % 16 = 0 ∧ sOff k < 4096 * 16)
    (hl : sOff l % 16 = 0 ∧ sOff l < 4096 * 16) (hp : kOff p % 16 = 0 ∧ kOff p < 4096 * 16)
    (hink : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff k)) 16)
    (hinl : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff l)) 16)
    (hinp : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (kOff p)) 16) :
    WP isa (.block [.ldrq S₁ .x19 (sOff k), .ldrq S₂ .x19 (sOff l), .ldrq KP .x19 (kOff p),
      .vop (.perm .trn1 .d2 T A₁ A₂), .vop (.perm .trn2 .d2 U A₁ A₂), .vop (.logic .eor T T U),
      .vop (.pmull false X₁ A₁ S₁), .vop (.pmull true A₁ A₁ S₁),
      .vop (.pmull false X₂ A₂ S₂), .vop (.pmull true A₂ A₂ S₂),
      .vop (.pmull false U T KP), .vop (.pmull true T T KP)]) s fun s' =>
      s'.v X₁ = polyMul (vdword (s.v A₁) 0) (vdword (tblV s (sOff k)) 0) ∧
      s'.v A₁ = polyMul (vdword (s.v A₁) 1) (vdword (tblV s (sOff k)) 1) ∧
      s'.v X₂ = polyMul (vdword (s.v A₂) 0) (vdword (tblV s (sOff l)) 0) ∧
      s'.v A₂ = polyMul (vdword (s.v A₂) 1) (vdword (tblV s (sOff l)) 1) ∧
      s'.v U = polyMul (vdword (s.v A₁) 0 ^^^ vdword (s.v A₁) 1) (vdword (tblV s (kOff p)) 0) ∧
      s'.v T = polyMul (vdword (s.v A₂) 0 ^^^ vdword (s.v A₂) 1) (vdword (tblV s (kOff p)) 1) ∧
      VOnly [S₁, S₂, KP, T, U, X₁, A₁, X₂, A₂] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_ldrq hk.1 hk.2 hink, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_ldrq hl.1 hl.2 (by simpa only [gpr_setV, rd_setV, wr_setV] using hinl), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_ldrq hp.1 hp.2 (by simpa only [gpr_setV, rd_setV, wr_setV] using hinp), ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_trn, exec_eor, exec_pmull0, exec_pmull1,
    Option.some.injEq, exists_eq_left', v_setV, gpr_setV, mem_setV, ite_true, ite_false, reduceCtorEq, tblV,
    trn_sum, vdword_ofVDwords0, vdword_ofVDwords1]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, by simp only [gpr_setV],
    by simp only [mem_setV], by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-- `Y` added to `A₂` if `y`. -/
theorem addY_ok (y : Bool) (s : State) :
    WP isa (.block (if y then [.vop (.logic .eor A₂ A₂ Y)] else [])) s fun s' =>
      s'.v A₂ = s.v A₂ ^^^ (if y then s.v Y else 0) ∧ VOnly [A₂] s s' := by
  cases y
  · exact WP.block_nil ⟨by simp, VOnly.refl _ _⟩
  · exact WP.mono (eor_ok A₂ A₂ Y s) fun s' ⟨h, o⟩ => ⟨by rw [h]; rfl, o⟩

/-- The table's offsets. -/
theorem sOff_ok (k : Nat) (hk : k ≤ 8) : sOff k % 16 = 0 ∧ sOff k < 4096 * 16 := by
  unfold sOff tbl; omega_using [hk]
theorem kOff_ok (p : Nat) (hp : p < 4) : kOff p % 16 = 0 ∧ kOff p < 4096 * 16 := by
  unfold kOff tbl; omega_using [hp]

/-- What `ghPart` reads. -/
structure GhIn (s : State) : Prop where
  blk : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (16 * j)) 16
  sw : ∀ k, 1 ≤ k → k ≤ 8 → InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (sOff k)) 16
  key : ∀ p < 4, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (kOff p)) 16

theorem GhIn.of {s s' : State} (h : GhIn s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    GhIn s' :=
  ⟨fun j hj => by rw [hg, hrd, hwr]; exact h.blk j hj, fun k a b => by rw [hg, hrd, hwr]; exact h.sw k a b,
    fun p hp => by rw [hg, hrd, hwr]; exact h.key p hp⟩

theorem ld_eq (a : VReg) (j : Nat) : ld a j = Impl.Gcm.AArch64.Pmull.loadRev a .x9 (16 * j) := rfl

/-- Pair `p` of blocks `a` and `b`, by the powers `k` and `l`. -/
theorem pair_ok (p a k b l : Nat) (y : Bool) (s : State) (hin : GhIn s) (hp : p < 4) (ha : a < 8)
    (hb : b < 8) (hk : 1 ≤ k ∧ k ≤ 8) (hl : 1 ≤ l ∧ l ≤ 8) :
    WP isa (.block (pair p a k b l y)) s fun s' =>
      s'.v X₁ = polyMul (vdword (blkV s a) 0) (vdword (tblV s (sOff k)) 0) ∧
      s'.v A₁ = polyMul (vdword (blkV s a) 1) (vdword (tblV s (sOff k)) 1) ∧
      s'.v X₂ = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 0) (vdword (tblV s (sOff l)) 0) ∧
      s'.v A₂ = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 1) (vdword (tblV s (sOff l)) 1) ∧
      s'.v U = polyMul (vdword (blkV s a) 0 ^^^ vdword (blkV s a) 1) (vdword (tblV s (kOff p)) 0) ∧
      s'.v T = polyMul (vdword (blkV s b ^^^ (if y then s.v Y else 0)) 0 ^^^
        vdword (blkV s b ^^^ (if y then s.v Y else 0)) 1) (vdword (tblV s (kOff p)) 1) ∧
      VOnly [A₁, A₂, S₁, S₂, KP, T, U, X₁, X₂] s s' := by
  unfold pair
  simp only [List.append_assoc]
  rw [ld_eq, ld_eq, WP.block_append_iff]
  refine WP.mono (loadRev_ok A₁ .x9 (16 * a) s (Nat.mul_mod_right 16 _) (by omega_using [ha]) (hin.blk a ha))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A₂ .x9 (16 * b) s₁ (Nat.mul_mod_right 16 _) (by omega_using [hb])
    (by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hin.blk b hb)) fun s₂ ⟨l₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addY_ok y s₂) fun s₃ ⟨e₃, o₃⟩ => ?_
  have o₁₃ := o₁.trans (o₂.trans o₃)
  have hin₃ := hin.of o₁₃.gpr o₁₃.rd o₁₃.wr
  refine WP.mono (pairTail_ok p k l s₃ (sOff_ok k hk.2) (sOff_ok l hl.2) (kOff_ok p hp)
    (hin₃.sw k hk.1 hk.2) (hin₃.sw l hl.1 hl.2) (hin₃.key p hp))
    fun s' ⟨h1, h2, h3, h4, h5, h6, o⟩ => ?_
  have hA₁ : s₃.v A₁ = blkV s a := by
    rw [o₃.v A₁ (by decide), o₂.v A₁ (by decide), l₁]; rfl
  have hA₂ : s₃.v A₂ = blkV s b ^^^ (if y then s.v Y else 0) := by
    rw [e₃, l₂, o₁.mem, o₁.gpr, o₂.v Y (by decide), o₁.v Y (by decide)]; rfl
  have ht : ∀ o, tblV s₃ o = tblV s o := fun o => by simp only [tblV, o₁₃.mem, o₁₃.gpr]
  rw [hA₁] at h1 h2 h5
  rw [hA₂] at h3 h4 h6
  simp only [ht] at h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6, (o₁₃.trans o).weaken⟩

/-- A pair's products, the first: their sums. -/
theorem addFirst_ok (s : State) :
    WP isa (.block addFirst) s fun s' =>
      prodS s' = ⟨s.v A₁ ^^^ s.v A₂, s.v U ^^^ s.v T, s.v X₁ ^^^ s.v X₂⟩ ∧ VOnly [HI, LO, MID] s s' := by
  apply WP.of_runBlock
  simp only [addFirst, runBlock_cons, runStep_some, runBlock_nil, exec_eor, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prodS, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A pair's products added. -/
theorem addNext_ok (s : State) :
    WP isa (.block addNext) s fun s' =>
      prodS s' = ⟨s.v LO ^^^ s.v A₁ ^^^ s.v A₂, s.v MID ^^^ s.v U ^^^ s.v T, s.v HI ^^^ s.v X₁ ^^^ s.v X₂⟩ ∧
        VOnly [HI, LO, MID] s s' := by
  apply WP.of_runBlock
  simp only [addNext, runBlock_cons, runStep_some, runBlock_nil, exec_eor3, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prodS, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The reduction of `fix` of the product, into `Y`. -/
theorem reduce_ok (s : State) (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (.block Impl.Gcm.AArch64.Stitch.reduce) s fun s' =>
      s'.v Y = Pmull.reduce (fix (prodS s)) ∧ VOnly [T, U, MID, HI, Y] s s' := by
  have hc0 : vdword (ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) 0 =
    Impl.Gcm.AArch64.Pmull.poly := vdword_append_0 _ _
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Stitch.reduce, runBlock_cons, runStep_some, runBlock_nil, exec_pmull0, exec_ext8,
    exec_eor3, Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false, reduceCtorEq, hc]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [hc0, Pmull.reduce, fix, prodS]
    have e : s.v MID ^^^ (ext8 (s.v LO) (s.v LO) ^^^ s.v LO ^^^ s.v HI) ^^^
        polyMul (vdword (s.v LO) 0) Impl.Gcm.AArch64.Pmull.poly =
        s.v MID ^^^ s.v HI ^^^ s.v LO ^^^ ext8 (s.v LO) (s.v LO) ^^^
          polyMul (vdword (s.v LO) 0) Impl.Gcm.AArch64.Pmull.poly := by
      ac_rfl
    rw [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The part -/

/-- The products of pair `p`, added to `pv`. -/
def pairP (s : State) (pv : Prod) (p : Nat) : Prod :=
  kpair pv (blkV s (pa p)) (tblV s (sOff (pk p))) (blkV s (pb p) ^^^ (if p = 3 then s.v Y else 0))
    (tblV s (sOff (pl p))) (tblV s (kOff p))

/-- The registers a pair and its sums write. -/
abbrev pairV : List VReg := [.v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29]

theorem pairAdd_ok (p : Nat) (hp : p < 4) (first : Bool) (s₀ s : State) (hin : GhIn s₀)
    (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hy : s.v Y = s₀.v Y) :
    WP isa (.block (pair p (pa p) (pk p) (pb p) (pl p) (decide (p = 3)) ++ (if first then addFirst else addNext)))
      s fun s' => prodS s' = pairP s₀ (if first then ⟨0, 0, 0⟩ else prodS s) p ∧ VOnly pairV s s' := by
  have hin' := hin.of hg hrd hwr
  rw [WP.block_append_iff]
  have hpa : pa p < 8 := by unfold pa; split <;> omega_using []
  have hpb : pb p < 8 := by unfold pb; split <;> omega_using []
  have hpk : 1 ≤ pk p ∧ pk p ≤ 8 := by unfold pk; split <;> omega_using []
  have hpl : 1 ≤ pl p ∧ pl p ≤ 8 := by unfold pl; split <;> omega_using []
  refine WP.mono (pair_ok p (pa p) (pk p) (pb p) (pl p) (decide (p = 3)) s hin' hp hpa hpb hpk hpl)
    fun s₁ ⟨h1, h2, h3, h4, h5, h6, o₁⟩ => ?_
  have eb : ∀ j, blkV s j = blkV s₀ j := fun j => by simp only [blkV, hm, hg]
  have et : ∀ o, tblV s o = tblV s₀ o := fun o => by simp only [tblV, hm, hg]
  cases first
  · refine WP.mono (addNext_ok s₁) fun s' ⟨e, o⟩ => ⟨?_, (o₁.trans o).weaken⟩
    rw [e, h1, h2, h3, h4, h5, h6, o₁.v LO (by decide), o₁.v MID (by decide), o₁.v HI (by decide)]
    simp only [pairP, kpair, kadd, prodS, decide_eq_true_eq, hy, eb, et, Bool.false_eq_true, ite_false]
  · refine WP.mono (addFirst_ok s₁) fun s' ⟨e, o⟩ => ⟨?_, (o₁.trans o).weaken⟩
    rw [e, h1, h2, h3, h4, h5, h6]
    simp only [pairP, kpair, kadd, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, ite_true, decide_eq_true_eq, hy, eb, et]

theorem ghPart_eq : ghPart =
    (pair 0 (pa 0) (pk 0) (pb 0) (pl 0) (decide (0 = 3)) ++ (if true then addFirst else addNext)) ++
    ((pair 1 (pa 1) (pk 1) (pb 1) (pl 1) (decide (1 = 3)) ++ (if false then addFirst else addNext)) ++
    ((pair 2 (pa 2) (pk 2) (pb 2) (pl 2) (decide (2 = 3)) ++ (if false then addFirst else addNext)) ++
    ((pair 3 (pa 3) (pk 3) (pb 3) (pl 3) (decide (3 = 3)) ++ (if false then addFirst else addNext)) ++
    Impl.Gcm.AArch64.Stitch.reduce))) := by
  simp only [ghPart, List.append_assoc]; rfl

theorem ghPart_ok (s : State) (hin : GhIn s)
    (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (.block ghPart) s fun s' =>
      s'.v Y = gh8V (s.v Y) (blkV s) (fun k => tblV s (sOff k)) (fun p => tblV s (kOff p)) ∧
        VOnly ghV s s' := by
  rw [ghPart_eq, WP.block_append_iff]
  refine WP.mono (pairAdd_ok 0 (by decide) true s s hin rfl rfl rfl rfl rfl) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok 1 (by decide) false s s₁ hin o₁.gpr o₁.mem o₁.rd o₁.wr (o₁.v Y (by decide)))
    fun s₂ ⟨p₂, o₂⟩ => ?_
  have O₂ := (o₁.trans o₂).weaken (rs' := pairV)
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok 2 (by decide) false s s₂ hin O₂.gpr O₂.mem O₂.rd O₂.wr (O₂.v Y (by decide)))
    fun s₃ ⟨p₃, o₃⟩ => ?_
  have O₃ := (O₂.trans o₃).weaken (rs' := pairV)
  rw [WP.block_append_iff]
  refine WP.mono (pairAdd_ok 3 (by decide) false s s₃ hin O₃.gpr O₃.mem O₃.rd O₃.wr (O₃.v Y (by decide)))
    fun s₄ ⟨p₄, o₄⟩ => ?_
  have O₄ := (O₃.trans o₄).weaken (rs' := pairV)
  refine WP.mono (reduce_ok s₄ (by rw [O₄.v C (by decide), hc])) fun s' ⟨e, o⟩ => ⟨?_, (O₄.trans o).weaken⟩
  rw [e, p₄, p₃, p₂, p₁]
  simp only [ite_true, Bool.false_eq_true, ite_false, gh8V, pairP]

end VG.Proof.Gcm.AArch64.Stitch

end

end

/-! ### `Gcm.AArch64.Stitch.Aes`, which this module and modules that import it used -/

section

/-!
# Interleaved counter mode and GHASH on AArch64: the counter mode

Untrusted: everything here is checked by Lean. `aesPart_ok`: `aesPart nr o`
(`Impl.Gcm.AArch64.Stitch`) leaves in `v0`–`v7` the eight text blocks at
`x9 + o` XORed with the keystream of the counter blocks `k … k + 7`, where
`w10` is the counter of the counter block at `x20 + 48` plus `k`: byte `t` of
`breg j` is byte `16 (k + j) + t` of the keystream (`keyStream`, as for
`vg_aes_ctr32_aes`) XORed with the text's. Each round loads its round key
into `v30` (`round_st`, `last_st` of `Proof/Aes/AArch64/Aese/Rounds.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.Impl.Gcm.AArch64.Stitch
open VG.Proof.Aes.AArch64.Aese (st KeyIs rnds round_st last_st keyIs_readW getD_st exec_ldrq ctrVec_st
  vbyte_xor vbyte_readW setV_v_self setV_v_of_ne setV_setV Fr exec_addImm_w sw32)
open VG.Proof.Aes.AArch64 (keyStream)
open VG.Spec.Aes (roundKey cipher addRoundKey)
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV v_write gpr_write_self
  gpr_write_of_ne mem_write rd_write wr_write sp_write)

/-! ## Registers -/

theorem breg_inj : ∀ i < 8, ∀ j < 8, breg i = breg j → i = j := by decide

theorem breg_ne_K (j : Nat) : breg j ≠ K := by unfold breg; split <;> decide
theorem breg_ne_P (j : Nat) : breg j ≠ P := by unfold breg; split <;> decide

/-- The registers `aesPart` writes. -/
abbrev aesV : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, K, P]

theorem breg_mem (j : Nat) : breg j ∈ aesV := by unfold breg; split <;> decide

/-! ## What the part needs -/

section
variable (s : State)

abbrev kp : Addr := s.gpr .x21
abbrev cbA : Addr := s.gpr .x20 + BitVec.ofNat 64 48
/-- The counter block, and its counter. -/
abbrev cbk : Spec.Gcm.Block := Spec.Gcm.blockAt s.mem (cbA s)
abbrev c0 : BitVec 32 := (cbk s).extractLsb' 0 32
end

/-- `aesPart nr o` can run from `s`, the counter in `w10` being the
counter block's plus `k`. -/
structure APre (nr o k : Nat) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  o_le : o ≤ 128
  keys : ∀ r ≤ nr, InRegions (s.rd ++ s.wr) (kp s + BitVec.ofNat 64 (16 * r)) 16
  ctr : InRegions (s.rd ++ s.wr) (cbA s + BitVec.ofNat 64 0) 16
  data : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16
  x10 : s.read .w .x10 = c0 s + BitVec.ofNat 32 k

/-- The key schedule of `nr` rounds at `x21`. -/
abbrev sch (nr : Nat) (s : State) : List Byte := Spec.Aes.bytesAt s.mem (kp s) (16 * (nr + 1))

/-- What it leaves: the blocks, and only `x10`, `x12` and `aesV` written. -/
structure APost (nr o k : Nat) (s s' : State) : Prop where
  out : ∀ j < 8, ∀ t < 16, vbyte (s'.v (breg j)) t =
    keyStream nr (sch nr s) (cbk s) (16 * (k + j) + t) ^^^
      s.mem (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) + BitVec.ofNat 64 t)
  x10 : s'.read .w .x10 = c0 s + BitVec.ofNat 32 (k + 8)
  fr : Fr [.x10, .x12] aesV s s'

/-! ## The counter blocks -/

/-- `ctr1 j`: counter block `k + j` into `breg j`. -/
theorem ctr1_ok (j : Nat) (hj : j < 8) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 48) 16) :
    WP isa (.block (ctr1 j)) s fun s' =>
      s'.v (breg j) = setLane (s.mem.readW (s.gpr .x20 + BitVec.ofNat 64 48) 128) 32 3
        (rev32 (s.read .w .x10 + BitVec.ofNat 32 j)) ∧ Fr [.x12] [breg j] s s' := by
  rw [ctr1, WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (by omega_arith), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (off := 48) (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp [State.setV, State.write, State.read, sw32]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]

/-- The counter block `k + j`, as `ctr1` builds it. -/
abbrev cvec (s : State) (k j : Nat) : BitVec 128 :=
  setLane (s.mem.readW (s.gpr .x20 + BitVec.ofNat 64 48) 128) 32 3
    (rev32 (c0 s + BitVec.ofNat 32 k + BitVec.ofNat 32 j))

theorem ctrs_ok {nr o k : Nat} {s : State} (hp : APre nr o k s) :
    WP isa (.block ((List.range 8).flatMap ctr1)) s fun s' =>
      (∀ j < 8, s'.v (breg j) = cvec s k j) ∧ Fr [.x12] aesV s s' := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 48) 16 := by
    have := hp.ctr; rwa [cbA, BitVec.add_zero] at this
  refine wp_range_flatMap (M := isa) (fun i s' => (∀ j < i, s'.v (breg j) = cvec s k j) ∧
      Fr [.x12] aesV s s') (fun i s₁ hi ⟨e₁, f₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), Fr.refl _ _ _⟩
  refine WP.mono (ctr1_ok i hi s₁ (by rw [f₁.rd, f₁.wr, f₁.gpr _ (by decide)]; exact hin))
    fun s' ⟨e, f⟩ => ⟨fun j hj => ?_, f₁.trans (f.mono (fun r h => h)
      (fun r h => by simp only [List.mem_singleton] at h; subst h; exact breg_mem i))⟩
  by_cases hji : j = i
  · subst hji
    have hx := hp.x10
    simp only [State.read] at hx
    rw [e, f₁.mem]
    simp only [State.read, f₁.gpr _ (by decide : Reg.x20 ∉ [Reg.x12]), f₁.gpr _ (by decide : Reg.x10 ∉ [Reg.x12])]
    rw [hx]
  · rw [f.v _ (by simp only [List.mem_singleton]; exact fun h => hji (breg_inj j (by omega_arith) i hi h)),
      e₁ j (by omega_arith)]

/-! ## The rounds -/

theorem fr_setV {gs : List Reg} {vs : List VReg} (s : State) {r : VReg} (x : BitVec 128) (h : r ∈ vs) :
    Fr gs vs s (s.setV r x) :=
  ⟨fun _ _ => rfl, fun _ hr' => setV_v_of_ne _ _ fun e => hr' (e ▸ h), rfl, rfl, rfl, rfl⟩

theorem fr_widen {vs : List VReg} {s s' : State} (h : Fr [] vs s s') (gs : List Reg) : Fr gs vs s s' :=
  h.mono (fun _ h => by simp at h) fun _ h => h

/-- The block registers hold the states before the `AddRoundKey` of round key `r`. -/
def RI (w : List Byte) (x : Nat → Spec.Aes.State) (r : Nat) (s : State) : Prop :=
  ∀ j < 8, addRoundKey (st (s.v (breg j))) (roundKey w r) = rnds w (x j) r

theorem aesround_run (j : Nat) (s : State) :
    runBlock isa [.vop (.aese (breg j) K), .vop (.aesmc (breg j) (breg j))] s =
      some (s.setV (breg j) (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K))))) :=
  Proof.Aes.AArch64.Aese.rnd_run K (breg j) s

/-- The eight states through a full round with the key in `v30`. -/
theorem rnd8_ok {w : List Byte} {x : Nat → Spec.Aes.State} {r : Nat} {s : State}
    (hk : KeyIs (s.v K) (roundKey w r)) (hI : RI w x r s) :
    WP isa (.block ((List.range 8).flatMap fun j =>
        [.vop (.aese (breg j) K), .vop (.aesmc (breg j) (breg j))])) s fun s' =>
      RI w x (r + 1) s' ∧ Fr [] aesV s s' ∧ s'.v K = s.v K := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, addRoundKey (st (s'.v (breg j))) (roundKey w (r + 1)) = rnds w (x j) (r + 1)) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, hK⟩ => ⟨e, f, hK⟩
  refine WP.of_runBlock ⟨_, aesround_run i s₁, ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [setV_v_self]
      refine round_st (k := s₁.v K) (by rw [k₁]; exact hk) ?_
      rw [u₁ j (Nat.le_refl _) hi]; exact hI j hi
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i)
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, k₁]

/-- Round key `r` into `v30`, and the eight states through the round. -/
theorem rnd_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {r : Nat}
    (hr : r + 1 ≤ nr) {s : State} (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x r s) :
    WP isa (.block (rnd r)) s fun s' => RI (sch nr s₀) x (r + 1) s' ∧ Fr [.x12] aesV s₀ s' := by
  have hR := hp.rounds
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hf.rd, hf.wr, hf.gpr _ (by decide)]; exact hp.keys r (by omega_arith)
  rw [rnd, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_arith) hin, ?_⟩
  have hk : KeyIs ((s.setV K (s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 128)).v K)
      (roundKey (sch nr s₀) r) := by
    rw [setV_v_self, hf.mem, hf.gpr _ (by decide)]
    exact keyIs_readW _ _ (by omega_arith)
  have hI' : RI (sch nr s₀) x r (s.setV K (s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 128)) :=
    fun j hj => by rw [setV_v_of_ne _ _ (breg_ne_K j)]; exact hI j hj
  exact WP.mono (rnd8_ok hk hI') fun s' ⟨e, f, _⟩ =>
    ⟨e, (hf.trans (fr_setV _ _ (by decide))).trans (fr_widen f _)⟩

theorem rnds_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {s : State}
    (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x 0 s) :
    ∀ n, n + 1 ≤ nr → WP isa (.block ((List.range n).flatMap rnd)) s fun s' =>
      RI (sch nr s₀) x n s' ∧ Fr [.x12] aesV s₀ s' := by
  intro n hn
  refine wp_range_flatMap (M := isa) (fun r s' => RI (sch nr s₀) x r s' ∧ Fr [.x12] aesV s₀ s')
    (fun r s₁ hr ⟨e₁, f₁⟩ => rnd_ok hp (by omega_arith) f₁ e₁) n (Nat.le_refl _) s ⟨hI, hf⟩

/-! ## The last round and the text -/

theorem aese_run (j : Nat) (s : State) :
    runBlock isa [.vop (.aese (breg j) K)] s =
      some (s.setV (breg j) (aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K)))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]

/-- `aese` of the eight states with the key in `v30`. -/
theorem aese8_ok (s : State) :
    WP isa (.block ((List.range 8).flatMap fun j => [.vop (.aese (breg j) K)])) s fun s' =>
      (∀ j < 8, s'.v (breg j) = aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K))) ∧
      Fr [] aesV s s' ∧ s'.v K = s.v K := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, s'.v (breg j) = aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K))) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, hK⟩ => ⟨e, f, hK⟩
  refine WP.of_runBlock ⟨_, aese_run i s₁, ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; rw [setV_v_self, u₁ j (Nat.le_refl _) hi, k₁]
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i)
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, k₁]

theorem eor3_run (j o : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho : o + 16 * j < 65536) (ho' : (o + 16 * j) % 16 = 0) :
    runBlock isa [.ldrq P .x9 (o + 16 * j), .vop (.eor3 (breg j) (breg j) P K)] s =
      some ((s.setV P (s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128)).setV (breg j)
        (s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K)) := by
  rw [runBlock_cons]
  rw [exec_ldrq ⟨ho', ho⟩ hin, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (breg_ne_P j), setV_v_of_ne _ _ (by decide : K ≠ P)]

/-- The text blocks at `x9 + o` added to the states and the last round key (in `v30`). -/
theorem fin8_ok {o : Nat} (ho : o ≤ 128) (s : State)
    (hin : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho16 : o % 16 = 0) :
    WP isa (.block ((List.range 8).flatMap fun j =>
        [.ldrq P .x9 (o + 16 * j), .vop (.eor3 (breg j) (breg j) P K)])) s fun s' =>
      (∀ j < 8, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      Fr [] aesV s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, _⟩ => ⟨e, f⟩
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * i)) 16 := by
    rw [f₁.rd, f₁.wr, f₁.gpr _ (by decide)]; exact hin i hi
  refine WP.of_runBlock ⟨_, eor3_run i o s₁ hin₁ (by omega_arith) (by omega_arith), ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; rw [setV_v_self, u₁ j (Nat.le_refl _) hi, k₁, f₁.mem, f₁.gpr _ (by decide)]
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji), setV_v_of_ne _ _ (breg_ne_P j)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), setV_v_of_ne _ _ (breg_ne_P j), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    rw [setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i), setV_v_of_ne _ _ fun h => hr (by rw [h]; decide)]
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, setV_v_of_ne _ _ (by decide : K ≠ P), k₁]

/-! ## The part -/

theorem keyStream_byte {nr k j t : Nat} {w : List Byte} {icb : Spec.Gcm.Block} (ht : t < 16) :
    keyStream nr w icb (16 * (k + j) + t) = (cipher nr w (Proof.Aes.ctrState icb (k + j))).getD t 0 := by
  rw [keyStream, show (16 * (k + j) + t) / 16 = k + j by omega_arith, show (16 * (k + j) + t) % 16 = t by omega_arith]

theorem aesPart_ok {nr o k : Nat} {s : State} (hp : APre nr o k s) (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart nr o)) s (APost nr o k s) := by
  have hR := hp.rounds
  unfold aesPart
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ctrs_ok hp) fun s₁ ⟨e₁, f₁⟩ => ?_
  -- The counter blocks, as AES states.
  let x : Nat → Spec.Aes.State := fun j => Proof.Aes.ctrState (cbk s) (k + j)
  have hx : ∀ j < 8, st (cvec s k j) = x j := fun j _ => by
    show _ = Proof.Aes.ctrState _ _
    rw [cvec, BitVec.add_assoc, ← BitVec.ofNat_add, c0, cbk, cbA, ← ctrVec_st, BitVec.add_zero]
  have hI₁ : RI (sch nr s) x 0 s₁ := fun j hj => by rw [e₁ j hj, hx j hj]; rfl
  refine WP.mono (rnds_ok hp f₁ hI₁ (nr - 1) (by omega_arith)) fun s₂ ⟨e₂, f₂⟩ => ?_
  -- The last round.
  have g₂ : s₂.gpr .x21 = s.gpr .x21 := f₂.gpr _ (by decide)
  have hin : ∀ r ≤ nr, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16 :=
    fun r hr => by rw [f₂.rd, f₂.wr, g₂]; exact hp.keys r hr
  unfold lastRnd
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_arith) (hin (nr - 1) (by omega_arith)), ?_⟩
  generalize hK₁ : s₂.mem.readW (s₂.gpr .x21 + BitVec.ofNat 64 (16 * (nr - 1))) 128 = K₁
  refine WP.mono (aese8_ok _) fun s₃ ⟨e₃, f₃, _⟩ => ?_
  rw [WP.block_cons_iff]
  have hin₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 16 := by
    rw [f₃.rd, f₃.wr, f₃.gpr _ (by decide), rd_setV, wr_setV, gpr_setV]
    exact hin nr (Nat.le_refl _)
  refine ⟨_, exec_ldrq (by omega_arith) hin₃, ?_⟩
  generalize hK₂ : s₃.mem.readW (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 128 = K₂
  have g₃ : ∀ r, s₃.gpr r = s₂.gpr r := fun r => by rw [f₃.gpr r (by simp)]; rfl
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, mem_setV, f₂.mem]
  have hin₄ : ∀ j < 8, InRegions ((s₃.setV K K₂).rd ++ (s₃.setV K K₂).wr)
      ((s₃.setV K K₂).gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16 := fun j hj => by
    rw [rd_setV, wr_setV, gpr_setV, f₃.rd, f₃.wr, g₃, rd_setV, wr_setV, f₂.rd,
      f₂.wr, f₂.gpr _ (by decide)]
    exact hp.data j hj
  refine WP.mono (fin8_ok hp.o_le _ hin₄ ho16) fun s₄ ⟨e₄, f₄⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (imm := 8) (by decide), WP.block_nil ?_⟩
  -- The keys, and the last round of each block.
  have hk₁ : KeyIs K₁ (roundKey (sch nr s) (nr - 1)) := by
    rw [← hK₁, f₂.mem, g₂]; exact keyIs_readW _ _ (by omega_arith)
  have hk₂ : KeyIs K₂ (roundKey (sch nr s) nr) := by
    rw [← hK₂, m₃, g₃, g₂]; exact keyIs_readW _ _ (by omega_arith)
  have g₉ : s₃.gpr .x9 = s.gpr .x9 := by rw [g₃, f₂.gpr _ (by decide)]
  refine ⟨fun j hj t ht => ?_, ?_, ?_⟩
  · rw [v_write, e₄ j hj, v_setV_of_ne _ _ (breg_ne_K j), e₃ j hj, v_setV_of_ne _ _ (breg_ne_K j),
      v_setV_self, v_setV_self, mem_setV, gpr_setV, m₃, g₉,
      show ∀ A M C : BitVec 128, A ^^^ M ^^^ C = (A ^^^ C) ^^^ M from fun A M C => by ac_rfl, vbyte_xor,
      vbyte_readW _ _ ht, keyStream_byte ht, ← getD_st _ ht,
      last_st hk₁ hk₂ (e₂ j hj)]
  · have hx := hp.x10
    have g₁₀ : s₄.gpr .x10 = s.gpr .x10 := by
      rw [f₄.gpr _ (by simp), gpr_setV, g₃, f₂.gpr _ (by decide)]
    simp only [State.read] at hx ⊢
    rw [gpr_write_self, sw32, g₁₀, hx, BitVec.add_assoc, ← BitVec.ofNat_add]
  · have f₄' : Fr [] aesV s₃ s₄ := (fr_setV _ _ (by decide)).trans f₄
    have f₃' : Fr [] aesV s₂ s₃ := (fr_setV _ _ (by decide)).trans f₃
    refine ((f₂.trans (fr_widen (f₃'.trans f₄') _)).mono (fun r h => List.mem_cons_of_mem _ h)
      (fun _ h => h)).trans ⟨fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact gpr_write_of_ne _ _ _ hr.1

end VG.Proof.Gcm.AArch64.Stitch

end

end

/-!
# Interleaved counter mode and GHASH on AArch64: one batch

Untrusted: everything here is checked by Lean. From the loops' invariant
(`LInv`): `aesStep`, the counter mode of batch `c` (the text blocks at
`x9 + o`); `stores_ok`, the eight blocks it computes stored to the output
(over them, or out of place); and
`ghStep`, GHASH of the eight blocks at `x9`, the blocks `hb (8 h + j)`, for
any `ghPart` that is GHASH (`Gh8Ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv DataInvM dataInvM_self dataInvM_frame dataInvM_store1 ctr32_of_dataInvM keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

/-! ## Storing a batch -/

/-- A block of the text XORed with the keystream, stored over it. -/
theorem dataInv_store1 {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 128}
    (hn : 16 * n < 2 ^ 64) (hk : k < n) (h : DataInv m₀ m D n k ks)
    (hv : ∀ t < 16, vbyte v t = ks (16 * k + t) ^^^ m₀ (D + BitVec.ofNat 64 (16 * k + t))) :
    DataInv m₀ (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) :=
  have h' := dataInvM_store1 hn hk (dataInvM_self.mpr h) hv
  ⟨dataInvM_self.mp h'.1, h'.2⟩

/-- The eight blocks of batch `c` stored at `p + o`, the output's batch `c`. -/
theorem stores_ok {s₀ : State} {to : Bool} (hp : KPreM s₀ to) {c o : Nat} (hc : c < nb s₀) (ho : o ≤ 128)
    (ho16 : o % 16 = 0) (u : State) (p : Reg)
    (hx9 : u.gpr p + BitVec.ofNat 64 o = op s₀ to + BitVec.ofNat 64 (128 * c))
    (hdata : DataInvM s₀.mem u.mem (dp s₀) (op s₀ to) (8 * nb s₀) (8 * c) (kst s₀)) (hwr : u.wr = s₀.wr)
    (hv : ∀ j < 8, ∀ t < 16, vbyte (u.v (breg j)) t =
      kst s₀ (16 * (8 * c + j) + t) ^^^ s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j) + t))) :
    WP isa (.block (storesAt p o)) u fun u' =>
      DataInvM s₀.mem u'.mem (dp s₀) (op s₀ to) (8 * nb s₀) (8 * (c + 1)) (kst s₀) ∧
        Frame [oR s₀ to] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := hp.n16
  refine WP.mono (wp_range_flatMap (M := isa) (fun j u' =>
      DataInvM s₀.mem u'.mem (dp s₀) (op s₀ to) (8 * nb s₀) (8 * c + j) (kst s₀) ∧
        Frame [oR s₀ to] u.mem u'.mem ∧
        u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr)
    (fun j u₁ hj ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_) 8 (Nat.le_refl _) u
    ⟨hdata, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩) fun u' ⟨d, f, g, v, sp, rd, wr⟩ =>
      ⟨by rw [show 8 * (c + 1) = 8 * c + 8 by omega_arith]; exact d, f, g, v, sp, rd, wr⟩
  have ha : u₁.gpr p + BitVec.ofNat 64 (o + 16 * j) = op s₀ to + BitVec.ofNat 64 (16 * (8 * c + j)) := by
    rw [g₁, ← Offset.add_add, hx9, Offset.add_add_eq _ (show 128 * c + 16 * j = 16 * (8 * c + j) by omega_arith)]
  have hw : InRegions u₁.wr (u₁.gpr p + BitVec.ofNat 64 (o + 16 * j)) 16 := by
    rw [ha, wr₁, hwr]
    exact CallLay.inRegions_sub hp.o_in (by omega_arith) (by omega_arith)
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by omega_arith) hw, WP.block_nil ?_⟩
  rw [ha]
  have hst := dataInvM_store1 (v := u₁.v (breg j)) (by omega_arith) (by omega_arith) d₁ fun t ht => by
    rw [v₁, hv j hj t ht]
  refine ⟨hst.1, f₁.trans ?_, g₁, v₁, sp₁, rd₁, wr₁⟩
  exact hst.2.sub fun r hr => ⟨oR s₀ to, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)⟩

/-! ## Counter mode -/

/-- Counter mode of batch `c`, from the text at `x9 + o`. -/
theorem aesStep {s₀ : State} {to : Bool} (hp : KPreM s₀ to) {hb : Nat → Block} {c h o : Nat} {s : State}
    (hI : LInv s₀ to hb c h s) (hc : c < nb s₀) (ho : 128 * h + o = 128 * c) (ho' : o ≤ 128) (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart (rounds s₀) o)) s fun t =>
      (∀ j < 8, ∀ tt < 16, vbyte (t.v (breg j)) tt =
        kst s₀ (16 * (8 * c + j) + tt) ^^^ s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j) + tt))) ∧
      t.read .w .x10 = ctr0 s₀ + BitVec.ofNat 32 (8 * (c + 1)) ∧ Fr [.x10, .x12] aesV s t := by
  have hn := hp.n16
  have hR := hp.rounds
  have g21 : s.gpr .x21 = kc s₀ := hI.gpr _ (notMem_kRegsT _ (by decide))
  have g20 : s.gpr .x20 = stp s₀ := hI.gpr _ (notMem_kRegsT _ (by decide))
  have rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hI.rd, hI.wr]
  have hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j)) :=
    fun j => by rw [hI.x9, Offset.add_add_eq _ (show 128 * h + (o + 16 * j) = 16 * (8 * c + j) by omega_arith)]
  have hcb : cbk s = icb s₀ := by rw [cbk, cbA, g20]; exact hp.c_frame hI.frame
  have hA : APre (rounds s₀) o (8 * c) s := {
    rounds := hR
    o_le := ho'
    keys := fun r hr => by
      rw [rdwr, kp, g21]; exact CallLay.inRegions_sub hp.k_in (by omega_arith) (by omega_arith)
    ctr := by
      rw [rdwr, cbA, g20, BitVec.add_zero]
      exact inRegions_wr hp.c_in
    data := fun j hj => by
      rw [rdwr, hx9]
      exact CallLay.inRegions_sub hp.d_in (by omega_arith) (by omega_arith)
    x10 := by rw [hI.x10, c0, hcb] }
  refine WP.mono (aesPart_ok hA ho16) fun t ⟨out, x10, fr⟩ => ⟨fun j hj tt htt => ?_, ?_, fr⟩
  · rw [out j hj tt htt, sch, kp, g21, hp.sch_frame hI.frame, hcb, hx9, Offset.add_add,
      hI.src hp (by omega_arith) (by omega_arith)]
  · rw [x10, c0, hcb, show 8 * c + 8 = 8 * (c + 1) by omega_arith]

/-! ## GHASH -/

/-- GHASH of the eight blocks at `x9`, the blocks `hb (8 h + j)`. -/
theorem ghStep {s₀ : State} {to : Bool} (hp : KPreM s₀ to) (gh : Gh8Ok) {hb : Nat → Block} {h : Nat} {t : State}
    (hy : t.v Y = ext8 (yh s₀ hb (8 * h)) (yh s₀ hb (8 * h)))
    (hc : t.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly)
    (hx9 : t.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * h)) (hh : h < nb s₀)
    (hx19 : t.gpr .x19 = wp s₀) (hrdwr : t.rd ++ t.wr = s₀.rd ++ s₀.wr)
    (hf : Frame [oR s₀ to] s₀.mem t.mem)
    (hb' : ∀ j < 8, blockAt t.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * h + j))) = hb (8 * h + j)) :
    WP isa (.block ghPart) t fun u =>
      u.v Y = ext8 (yh s₀ hb (8 * (h + 1))) (yh s₀ hb (8 * (h + 1))) ∧ VOnly ghV t u := by
  have hn := hp.n16
  have ha : ∀ j, t.gpr .x9 + BitVec.ofNat 64 (16 * j) = dp s₀ + BitVec.ofNat 64 (16 * (8 * h + j)) :=
    fun j => by rw [hx9, Offset.add_add_eq _ (show 128 * h + 16 * j = 16 * (8 * h + j) by omega_arith)]
  have ht : ∀ o, o + 16 ≤ 192 → t.gpr .x19 + BitVec.ofNat 64 (512 + o) =
      wp s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 o := fun o _ => by rw [hx19, Offset.add_add]
  have hin : GhIn t := {
    blk := fun j hj => by
      rw [hrdwr, ha]; exact CallLay.inRegions_sub hp.d_in (by omega_arith) (by omega_arith)
    sw := fun k hk1 hk8 => by
      rw [hrdwr, show sOff k = 512 + 16 * (k - 1) from rfl, ht _ (by omega_arith)]
      exact CallLay.inRegions_sub hp.t_in (by omega_arith) (by omega_arith)
    key := fun p hp' => by
      rw [hrdwr, show kOff p = 512 + (128 + 16 * p) by unfold kOff tbl; omega_arith, ht _ (by omega_arith)]
      exact CallLay.inRegions_sub hp.t_in (by omega_arith) (by omega_arith) }
  refine WP.mono (ghPart_ok t hin hc) fun u ⟨e, o⟩ => ⟨?_, o⟩
  rw [e, hy, gh8V_congr rfl (b' := fun j => ext8 (hb (8 * h + j)) (hb (8 * h + j)))
    (S' := fun k => ext8 (Pmull.pp (hk s₀) k) (Pmull.pp (hk s₀) k))
    (KP' := fun p => kpack (hk s₀) (pk p) (pl p))
    (fun j hj => by rw [blkV, ha, rev64b_read, hb' j hj])
    (fun k hk1 hk8 => by
      rw [tblV, read_eq_readW, show sOff k = 512 + 16 * (k - 1) from rfl, ht _ (by omega_arith), hp.t_frame hf (by omega_arith),
        Offset.add_add, show 512 + 16 * (k - 1) = sOff k from rfl]
      exact hp.tbl.sw k hk1 hk8)
    (fun p hp' => by
      rw [tblV, read_eq_readW, show kOff p = 512 + (128 + 16 * p) by unfold kOff tbl; omega_arith, ht _ (by omega_arith), hp.t_frame hf (by omega_arith),
        Offset.add_add, show 512 + (128 + 16 * p) = kOff p by unfold kOff tbl; omega_arith]
      exact hp.tbl.key p hp'), gh, yh, yh, show 8 * (h + 1) = 8 * h + 8 by omega_arith, range_map_add hb (8 * h),
    ghashFrom_append]

end VG.Proof.Gcm.AArch64.Stitch
