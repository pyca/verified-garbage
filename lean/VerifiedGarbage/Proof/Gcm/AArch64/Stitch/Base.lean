module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Spec
public import VerifiedGarbage.Proof.Aes.AArch64.Group
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32


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
open VG.Proof.Aes.AArch64 (DataInv keyStream)
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

/-- The bytes at `O`: the `16 k` first, the `16 k` at `D` XORed with the
keystream; the rest, as they were. With `O = D`, `DataInv` (`dataInvM_self`). -/
def DataInvM (m₀ m : Mem) (D O : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (O + BitVec.ofNat 64 i) =
    if i < 16 * k then m₀ (D + BitVec.ofNat 64 i) ^^^ ks i else m₀ (O + BitVec.ofNat 64 i)

theorem dataInvM_self {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} :
    DataInvM m₀ m D D n k ks ↔ DataInv m₀ m D n k ks := by
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩ <;> rw [h i hi] <;> by_cases hk : i < 16 * k
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]; exact BitVec.xor_zero.symm
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]; exact BitVec.xor_zero

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

theorem dataInvM_frame {m₀ m m' : Mem} {D O : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨O, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInvM m₀ m D O n k ks) : DataInvM m₀ m' D O n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨O, 16 * n⟩) hd (by simp only; omega) hi

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
      omega) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat]; omega)
    exact this

theorem c_frame {m : Mem} (hf : Frame [oR s₀ to] s₀.mem m) :
    blockAt m (stp s₀ + BitVec.ofNat 64 48) = icb s₀ :=
  Proof.Gcm.blockAt_congr fun _ hk => hf.bytes (R := cR s₀)
    (by simp only [List.mem_singleton, forall_eq]; exact hp.o_c.symm) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem t_frame {m : Mem} (hf : Frame [oR s₀ to] s₀.mem m) {o : Nat} (ho : o + 16 ≤ 192) :
    m.readW (wp s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 o) 128 =
      s₀.mem.readW (wp s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 o) 128 :=
  hf.readW (r := tR s₀) (Offset.contains_base _ (by omega) (by omega))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.o_t.symm) (by decide)

theorem sch_frame {m : Mem} (hf : Frame [oR s₀ to] s₀.mem m) :
    Spec.Aes.bytesAt m (kc s₀) (16 * (Stitch.rounds s₀ + 1)) = ksch s₀ := by
  have hR := hp.rounds
  exact Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.o_k.symm.sub_left (Region.sub_prefix (by omega))) (by omega)

end KPreM

/-- The text from batch `c` on, as it was: in place, not yet written; out of
place, never written. -/
theorem LInv.src {s₀ : State} {to : Bool} (hp : KPreM s₀ to) {hb : Nat → Block} {c h : Nat} {s : State}
    (hI : LInv s₀ to hb c h s) {i : Nat} (hc : 16 * (8 * c) ≤ i) (hi : i < 16 * (8 * nb s₀)) :
    s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  cases to with
  | false =>
    have := hI.data i hi
    rw [ite_eq_right (by omega)] at this
    exact this
  | true =>
    have hn := hp.n16
    exact hI.frame.bytes (R := ⟨dp s₀, 16 * (8 * nb s₀)⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.d_o rfl).sub_left (Region.sub_prefix (by omega))) (by simp only; omega) hi

/-! ## The blocks -/

/-- A block XORed with the keystream, by `DataInv`. -/
theorem blockAt_of_dataInv {m₀ m : Mem} {D : Addr} {n k R : Nat} {w : List Byte} {icb : Block}
    (h : DataInv m₀ m D n k (keyStream R w icb)) {i : Nat} (hi : i < k) (hk : k ≤ n) :
    blockAt m (D + BitVec.ofNat 64 (16 * i)) =
      blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) ^^^ aesWith R w (Nat.repeat inc32 i icb) := by
  refine Proof.Aes.block_ext fun t ht => ?_
  rw [Proof.Aes.toBytes_xor _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht,
    BitVec.add_assoc, ← BitVec.ofNat_add, h _ (by omega), ite_eq_left (by omega)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [Proof.Aes.toBytes_ofBytes (by simp) ht, keyStream, show (16 * i + t) / 16 = i by omega,
    show (16 * i + t) % 16 = t by omega, Proof.Aes.getD_eq _ ht, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem ht, Option.getD_some]
  rfl

/-- A block not yet XORed. -/
theorem blockAt_of_dataInv' {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte}
    (h : DataInv m₀ m D n k ks) {i : Nat} (hi : k ≤ i) (hn : i < n) :
    blockAt m (D + BitVec.ofNat 64 (16 * i)) = blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) := by
  refine Proof.Aes.block_ext fun t ht => ?_
  rw [Proof.Aes.toBytes_blockAt _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add,
    h _ (by omega), ite_eq_right (by omega)]
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
