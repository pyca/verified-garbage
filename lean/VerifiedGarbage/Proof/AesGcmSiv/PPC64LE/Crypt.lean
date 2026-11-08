module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Tag
public import VerifiedGarbage.Proof.GcmSiv.Ctr
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Callee
import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-GCM-SIV on PPC64LE: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/AesGcmSiv/RISCV64/Crypt.lean`): `cryptHead` writes the initial
counter block from the tag at `W + 96`; up to 64 counter blocks at a time
are written to `W + 496` (`ctrBuild_wp`), encrypted by one call of
`vg_aes_encrypt_blocks` and XORed into the data a doubleword at a time
(`xorDLoop_ok`, `cryptChunk_wp`, `blocks_wp`); the last bytes are XORed
with a keystream block computed at `W + 240` (`cryptTail_wp`): RFC 8452's
counter mode (`crypt_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_ld wp_std wp_lsl wp_lsr wp_lwz wp_stw wp_subi
  wp_or wp_xor wp_sub)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.AesGcm.PPC64LE (CtrCall CtrPost ctr_call LoopPre LoopOut xorLoop_ok xorBytes)
open VG.WriteBytes (writeBytes_nil)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

theorem inc32_word (x : BitVec 32) : ((x.setWidth 64 + BitVec.ofNat 64 1).setWidth 32 : BitVec 32) = x + 1#32 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, Offset.add_add, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega_arith) (by omega_arith)) hc

/-- What counter mode writes: the counter block and its copy, the block at
`W + 240`, the counter blocks, the callees' working space and the data. -/
abbrev cryR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 496, 1024⟩,
    ⟨W + BitVec.ofNat 64 1776, 2048⟩, ⟨D, n⟩]

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {c : Cx} (L : Lay c) :
    ∀ r ∈ cryR c.W c.D c.n, (⟨c.W + BitVec.ofNat 64 256, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

theorem ciph_cryR {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (cryR c.W c.D c.n) m m') :
    Spec.GcmSiv.ctxCiph m' (c.W + BitVec.ofNat 64 256) c.R = Spec.GcmSiv.ctxCiph m (c.W + BitVec.ofNat 64 256) c.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega_arith)]

/-- The counter block, after writes apart from it. -/
theorem CtrSt.of_frame {W : Addr} {icb : List Byte} {j : Nat} {m m' : Mem} (C : CtrSt W icb j m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 96, 16⟩ : Region).Disjoint r) : CtrSt W icb j m' :=
  ⟨by rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by decide)]; exact C.word,
    by rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left
      (by rw [show W + BitVec.ofNat 64 100 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 4 by rw [Offset.add_add]]
          exact Offset.sub_base _ (by decide))) (by decide)]; exact C.rest⟩

/-- A run of blocks the XOR loop wrote: each the XOR of the old one with the
block of the source at the same offset. -/
theorem xorBytes_block (m : Mem) (D S : Addr) {k l : Nat} (hl : l < k) (hk : 16 * k < 2 ^ 64) :
    bytesAt (writeBytes m D (xorBytes m D S (16 * k))) (D + BitVec.ofNat 64 (16 * l)) 16 =
      Spec.Cmac.xor (bytesAt m (D + BitVec.ofNat 64 (16 * l)) 16) (bytesAt m (S + BitVec.ofNat 64 (16 * l)) 16) := by
  apply List.ext_getElem (by simp [bytesAt, Spec.Cmac.xor])
  intro i h₁ h₂
  have hi : i < 16 := by simpa [bytesAt] using h₁
  have hp : 16 * l + i < 16 * k := by omega
  have hl' : (xorBytes m D S (16 * k)).length = 16 * k := Proof.AesGcm.PPC64LE.length_xorBytes _ _ _ _
  simp only [bytesAt, Spec.Cmac.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith, writeBytes,
    Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 16 * l + i < 2 ^ 64 by omega), hl', hp, ite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl']; exact hp), Option.getD_some]
  simp [xorBytes, bytesAt]

/-! ## The doubleword XOR -/

theorem le8_xor (a b : BitVec 64) :
    Proof.Cmac.le8 (a ^^^ b) = List.zipWith (· ^^^ ·) (Proof.Cmac.le8 a) (Proof.Cmac.le8 b) := by
  apply List.ext_getElem (by simp [Proof.Cmac.le8])
  intro i h₁ h₂
  simp [Proof.Cmac.le8, BitVec.extractLsb'_xor]

/-- What `xorDLoop` needs: `k` (at least 1) doublewords at `D` (`r4`) XORed
with those at `S` (`r3`, apart from `D`). -/
structure XorDPre (s : State) (S D : Addr) (k : Nat) : Prop where
  r3 : s.gpr .r3 = S
  r4 : s.gpr .r4 = D
  r5 : s.gpr .r5 = BitVec.ofNat 64 k
  pos : 1 ≤ k
  lt : 8 * k < 2 ^ 64
  rd : Covers [⟨S, 8 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 8 * k⟩] s.wr
  disj : (⟨S, 8 * k⟩ : Region).Disjoint ⟨D, 8 * k⟩

/-- `xorDLoop`: the `8 k` bytes at `D` XORed with those at `S`, as
`xorLoop` leaves them. -/
theorem xorDLoop_ok (s : State) {S D : Addr} {k : Nat} (h : XorDPre s S D k) :
    WP isa xorDLoop s fun s' =>
      s'.mem = writeBytes s.mem D (xorBytes s.mem D S (8 * k)) ∧ LoopOut s S D (8 * k) s' := by
  have hk := h.lt
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ t.gpr .r3 = S + BitVec.ofNat 64 (8 * i) ∧
      t.gpr .r4 = D + BitVec.ofNat 64 (8 * i) ∧ t.gpr .r5 = BitVec.ofNat 64 (k - i) ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t.gpr r = s.gpr r) ∧
      (t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr) ∧
      t.mem = writeBytes s.mem D (xorBytes s.mem D S (8 * i))) ?_ (k - 0) s
    ⟨0, rfl, by have := h.pos; omega, by rw [h.r3]; exact (BitVec.add_zero _).symm,
      by rw [h.r4]; exact (BitVec.add_zero _).symm, by rw [h.r5, Nat.sub_zero], fun _ _ _ _ _ _ => rfl,
      ⟨rfl, rfl, rfl, rfl⟩, by simp [xorBytes, bytesAt, writeBytes_nil]⟩
  rintro w t ⟨i, rfl, hi, r3, r4, r5, oth, ⟨rd, wr, sp, lr⟩, mem⟩
  have hin : 8 * i + 8 ≤ 8 * k := by omega
  refine wp_ld (a := D + BitVec.ofNat 64 (8 * i)) (by decide) (by decide) (by rw [r4]; exact BitVec.add_zero _)
    (by rw [rd, wr]; exact VG.Proof.Gather.PPC64LE.in_off (Covers.right h.wr) hin (by omega)) fun t₁ u₁ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 (8 * i)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), r3]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr, rd, wr]; exact VG.Proof.Gather.PPC64LE.in_off h.rd hin (by omega)) fun t₂ u₂ => ?_
  refine wp_xor fun t₃ u₃ => ?_
  refine wp_std (a := D + BitVec.ofNat 64 (8 * i)) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r4]; exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr, wr]; exact VG.Proof.Gather.PPC64LE.in_off h.wr hin (by omega)) fun t₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₅ u₅ => wp_addi (by decide) (by decide) fun t₆ u₆ =>
    wp_subi (by decide) (by decide) fun t₇ u₇ => WP.block_nil ?_
  have hlen : (xorBytes s.mem D S (8 * i)).length = 8 * i := Proof.AesGcm.PPC64LE.length_xorBytes _ _ _ _
  have past := bytesAt_writeBytes_past s.mem D (xorBytes s.mem D S (8 * i)) 8 (by rw [hlen]; omega)
  rw [hlen] at past
  have dS : ∀ r ∈ [(⟨D, (xorBytes s.mem D S (8 * i)).length⟩ : Region)],
      (⟨S + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [hlen]
    exact (h.disj.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
  have srcS : Spec.Aes.bytesAt t.mem (S + BitVec.ofNat 64 (8 * i)) 8 =
      Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [mem]
    exact Proof.Cmac.bytesAt_frame (VG.WriteBytes.writeBytes_frame _ _ _ (Region.contains_self _ _)) dS (by decide)
  have app := VG.WriteBytes.writeBytes_append s.mem D (xorBytes s.mem D S (8 * i))
    (List.zipWith (· ^^^ ·) (Spec.Aes.bytesAt s.mem (D + BitVec.ofNat 64 (8 * i)) 8)
      (Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 (8 * i)) 8))
    (by rw [hlen, List.length_zipWith, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]; omega)
  rw [hlen] at app
  have hmem : t₇.mem = writeBytes s.mem D (xorBytes s.mem D S (8 * (i + 1))) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₂.gpr, u₂.other .r0 (by decide), u₁.gpr, u₃.mem, u₂.mem, u₁.mem,
      VG.Proof.AesCcm.writeW64_eq, le8_xor, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, srcS, mem, past, app,
      show 8 * (i + 1) = 8 * i + 8 by omega, xorBytes, xorBytes, Proof.Cmac.Stream.bytesAt_append,
      Proof.Cmac.Stream.bytesAt_append, List.zipWith_append (by rw [Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length])]
  have hstep : ∀ P : Addr, P + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 = P + BitVec.ofNat 64 (8 * (i + 1)) :=
    fun P => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * i + 8 = 8 * (i + 1) by omega]
  have r3' : t₇.gpr .r3 = S + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
  have r4' : t₇.gpr .r4 = D + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), r4, hstep]
  have r5' : t₇.gpr .r5 = BitVec.ofNat 64 (k - (i + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), r5, VG.Proof.Gather.PPC64LE.ofNat_sub_one (by omega),
      Nat.sub_sub]
  have oth' : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t₇.gpr r = s.gpr r :=
    fun r h0 h3 h4 h5 h6 => by
      rw [u₇.other _ h5, u₆.other _ h4, u₅.other _ h3, u₄.gpr, u₃.other _ h0, u₂.other _ h6, u₁.other _ h0,
        oth r h0 h3 h4 h5 h6]
  have keep : t₇.rd = s.rd ∧ t₇.wr = s.wr ∧ t₇.sp = s.sp ∧ t₇.lr = s.lr :=
    ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr,
      u₁.wr, wr], by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, sp],
      by rw [u₇.lr, u₆.lr, u₅.lr, u₄.lr, u₃.lr, u₂.lr, u₁.lr, lr]⟩
  have ev := VG.Proof.Gather.PPC64LE.eval_nonzero (r := .r5) (a := k - (i + 1)) r5' (by omega)
  by_cases he : i + 1 = k
  · left
    subst he
    refine ⟨by rw [ev]; simp, hmem, r3', r4', by rw [r5', Nat.sub_self]; rfl, oth', keep⟩
  · right
    exact ⟨by rw [ev]; simp; omega, k - (i + 1), by omega, i + 1, rfl, by omega, r3', r4', r5', oth', keep, hmem⟩

/-! ## The counter blocks -/

/-- The memory after the counter block is copied to `P`. -/
def cpyMem (m : Mem) (W P : Addr) : Mem :=
  (m.writeW P (m.readW (W + BitVec.ofNat 64 96) 64)).writeW (P + BitVec.ofNat 64 8)
    (m.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64)

theorem cpyMem_bytes (m : Mem) (W P : Addr) : bytesAt (cpyMem m W P) P 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [cpyMem, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.bytesAt_split]

/-- After `l` of the `k` counter blocks of a chunk from block `j`, from `t₀`. -/
structure GInv (c : Cx) (icb : List Byte) (j k l : Nat) (t₀ t : State) : Prop where
  env : Env c t
  pk : PK t₀ t
  r23 : t.gpr .r23 = t₀.gpr .r23
  r24 : t.gpr .r24 = t₀.gpr .r24
  r25 : t.gpr .r25 = BitVec.ofNat 64 k
  r4 : t.gpr .r4 = c.W + BitVec.ofNat 64 (496 + 16 * l)
  r3 : t.gpr .r3 = BitVec.ofNat 64 (k - l)
  le : l ≤ k
  ctr : CtrSt c.W icb (j + l) t.mem
  frame : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩, ⟨c.W + BitVec.ofNat 64 496, 1024⟩] t₀.mem t.mem
  blk : ∀ q < l, bytesAt t.mem (c.W + BitVec.ofNat 64 (496 + 16 * q)) 16 = Spec.GcmSiv.counterBlock icb (j + q)

theorem ctr0_wp {c : Cx} {t : State} (E : Env c t) {icb : List Byte} {j k : Nat} (C : CtrSt c.W icb j t.mem)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 k) :
    WP isa (.block [.addi .r4 .r14 revO, Impl.AesGcm.PPC64LE.mov .r3 .r25]) t (GInv c icb j k 0 t) := by
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ => WP.block_nil ?_
  have pk : PK t t₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  refine ⟨E.of_pk pk, pk, by rw [u₂.other _ (by decide), u₁.other _ (by decide)],
    by rw [u₂.other _ (by decide), u₁.other _ (by decide)], by rw [u₂.other _ (by decide), u₁.other _ (by decide), h25],
    by rw [u₂.other _ (by decide), u₁.gpr, E.r14]; rfl, by rw [u₂.gpr, u₁.other _ (by decide), h25, Nat.sub_zero],
    Nat.zero_le _, by rw [u₂.mem, u₁.mem, Nat.add_zero]; exact C, by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A counter block of a chunk. -/
theorem ctrStep_wp {c : Cx} (L : Lay c) {icb : List Byte} {j k l : Nat} (hk : k ≤ 64) (hl : l < k)
    {t₀ t : State} (G : GInv c icb j k l t₀ t) : WP isa (.block ctrBody) t (GInv c icb j k (l + 1) t₀) := by
  have hw := L.ww
  have E := G.env
  unfold ctrBody
  refine wp_ld (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide) (by rw [E.r14]; rfl)
    (E.perm.wR (by decide)) fun t₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14, Offset.add_add]; rfl)
    (by rw [u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by decide)) fun t₂ u₂ => ?_
  have r4₂ : t₂.gpr .r4 = c.W + BitVec.ofNat 64 (496 + 16 * l) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), G.r4]
  have wr₂ : t₂.wr = t.wr := by rw [u₂.wr, u₁.wr]
  refine wp_std (a := c.W + BitVec.ofNat 64 (496 + 16 * l)) (by decide) (by decide) (by rw [r4₂, BitVec.add_zero])
    (by rw [wr₂]; exact E.perm.wW (by omega)) fun t₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 (496 + 16 * l) + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.gpr, r4₂])
    (by rw [u₃.wr, wr₂, Offset.add_add]; exact E.perm.wW (by omega)) fun t₄ u₄ => ?_
  have m₄ : t₄.mem = cpyMem t.mem c.W (c.W + BitVec.ofNat 64 (496 + 16 * l)) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other .r5 (by decide), u₁.gpr, u₂.mem, u₁.mem]; rfl
  have f₄ : Frame [⟨c.W + BitVec.ofNat 64 (496 + 16 * l), 16⟩] t.mem t₄.mem := by
    rw [m₄]; exact Proof.Cmac.frame_store2 _ _ _
  refine wp_lwz (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, wr₂, u₁.rd]; exact E.perm.wR (by decide))
    fun t₅ u₅ => ?_
  refine wp_addi (by decide) (by decide) fun t₆ u₆ => ?_
  refine wp_stw (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]; exact E.perm.wW (by decide))
    fun t₇ u₇ => ?_
  refine wp_addi (by decide) (by decide) fun t₈ u₈ => wp_subi (by decide) (by decide) fun t₉ u₉ => WP.block_nil ?_
  have pk : PK t t₉ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofMupd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  have g₆ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t₉.gpr r = t.gpr r :=
    fun r h3 h4 h5 h6 => by
      rw [u₉.other _ h3, u₈.other _ h4, u₇.gpr, u₆.other _ h5, u₅.other _ h5, u₄.gpr, u₃.gpr, u₂.other _ h6,
        u₁.other _ h5]
  have hm : t₉.mem = t₄.mem.writeW (c.W + BitVec.ofNat 64 96) (t₄.mem.readW (c.W + BitVec.ofNat 64 96) 32 + 1#32) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₅.gpr, u₆.mem, u₅.mem, inc32_word]
  have fw : Frame [⟨c.W + BitVec.ofNat 64 96, 4⟩] t₄.mem t₉.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dP : (⟨c.W + BitVec.ofNat 64 96, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 (496 + 16 * l), 16⟩ :=
    L.w_w (.inl (by omega)) (by decide) (by omega)
  have C₄ : CtrSt c.W icb (j + l) t₄.mem := G.ctr.of_frame f₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP
  refine ⟨E.of_pk pk, G.pk.trans pk, by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), G.r23],
    by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), G.r24],
    by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), G.r25], ?_, ?_, by omega, ⟨?_, ?_⟩, ?_,
    fun q hq => ?_⟩
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), G.r4, Offset.add_add,
      show 496 + 16 * l + 16 = 496 + 16 * (l + 1) by omega]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), G.r3, ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [hm, Mem.readW_writeW_self32, C₄.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hm, Proof.Cmac.bytesAt_frame (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), C₄.rest]
  · refine G.frame.trans ((f₄.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  · have fw' : Frame [⟨c.W + BitVec.ofNat 64 96, 4⟩] t₄.mem t₉.mem := fw
    rw [Proof.Cmac.bytesAt_frame fw' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)]
    by_cases e : q = l
    · subst e; rw [m₄, cpyMem_bytes, G.ctr.block]
    · rw [Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact G.blk q (by omega)

/-- `ctrBuild`: the `k` counter blocks from block `j`. -/
theorem ctrBuild_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {icb : List Byte} {j k : Nat} (hk1 : 1 ≤ k)
    (hk : k ≤ 64) (C : CtrSt c.W icb j t.mem) (h25 : t.gpr .r25 = BitVec.ofNat 64 k) :
    WP isa ctrBuild t (GInv c icb j k k t) := by
  unfold ctrBuild
  refine WP.seq (WP.mono (ctr0_wp E C h25) fun t₀ G₀ => ?_)
  refine WP.loop (M := isa) (fun m t' => ∃ l, m = k - l ∧ l < k ∧ GInv c icb j k l t t') ?_
    (k - 0) _ ⟨0, rfl, by omega, G₀⟩
  rintro m t' ⟨l, rfl, hl, G⟩
  refine WP.mono (ctrStep_wp L hk hl G) fun t'' G' => ?_
  have ev := VG.Proof.Gather.PPC64LE.eval_nonzero G'.r3 (by omega)
  by_cases he : l + 1 = k
  · left; exact ⟨ev.trans (by simp; omega), he ▸ G'⟩
  · right; exact ⟨ev.trans (by simp; omega), k - (l + 1), by omega, l + 1, rfl, by omega, G'⟩

/-! ## A chunk -/

/-- The arguments of `vg_aes_encrypt_blocks`: the encryption key's schedule,
`k` blocks at `W + 496` and the working space at `W + 1776`. -/
theorem bargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {k : Nat} (hk : k ≤ 64)
    (r3 : s.gpr .r3 = c.W + BitVec.ofNat 64 256) (r4 : s.gpr .r4 = BitVec.ofNat 64 c.R)
    (r5 : s.gpr .r5 = c.W + BitVec.ofNat 64 496) (r6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (r7 : s.gpr .r7 = c.W + BitVec.ofNat 64 1776) :
    Proof.AesOcb.PPC64LE.BCall s (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 496)
      (c.W + BitVec.ofNat 64 1776) c.R k where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  rounds := by rcases L.rounds with h | h <;> simp [h]
  wrap := by rw [L.wrapW (by decide)]; have := L.ww; omega
  kd := L.w_w (.inl (by omega)) (by decide) (by omega)
  ks := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := L.w_w (.inl (by omega)) (by omega) (by decide)
  reads := Covers.append_left (Covers.cons (E.perm.wCR (by decide)) Covers.nil)
    (Covers.cons (E.perm.wCR (by omega)) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega)) (Covers.cons (E.perm.wC (by decide)) Covers.nil)

/-- A block `vg_aes_encrypt_blocks` replaced: the cipher of the old one. -/
theorem bytesAt_cipher {m m' : Mem} {D : Addr} {k : Nat} {R : Nat} {w : List Byte}
    (h : Spec.Aes.statesAt m' D k = (Spec.Aes.statesAt m D k).map (Spec.Aes.cipher R w)) {l : Nat} (hl : l < k) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * l)) 16 =
      Spec.GcmSiv.aesWith R w (bytesAt m (D + BitVec.ofNat 64 (16 * l)) 16) := by
  have e : Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * l)) =
      Vector.ofFn fun i => (bytesAt m (D + BitVec.ofNat 64 (16 * l)) 16).getD i.1 0 := by
    apply Vector.ext
    intro i hi
    simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD]
  rw [Proof.Ocb.bytesAt_toList, Proof.Ocb.stateAt_of_statesAt h hl, e]
  rfl

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (c : Cx) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  pk : PK t t'
  r23 : t'.gpr .r23 = c.D + BitVec.ofNat 64 (16 * b)
  r24 : t'.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * b)
  ctr : CtrSt c.W icb b t'.mem
  data : bytesAt t'.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem

/-- The arguments of the call of a chunk. -/
theorem encArgs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {k : Nat} (hk : k ≤ 64)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 k) :
    WP isa (.block chunkEncArgs) t fun t₅ => PK t t₅ ∧ t₅.mem = t.mem ∧
      (∀ r ∈ [Reg.r23, .r24, .r25], t₅.gpr r = t.gpr r) ∧
      Proof.AesOcb.PPC64LE.BCall t₅ (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 496)
        (c.W + BitVec.ofNat 64 1776) c.R k := by
  unfold chunkEncArgs
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_addi (by decide) (by decide)
    fun t₃ u₃ => wp_mv fun t₄ u₄ => wp_addi (by decide) (by decide) fun t₅ u₅ => WP.block_nil ?_
  have pk : PK t t₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  have E₅ := E.of_pk pk
  refine ⟨pk, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], fun r hr => ?_, bargs L E₅ hk ?_ ?_ ?_ ?_ ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      E.r14]; rfl
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      E.r17]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      E.r14]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h25]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.r14]; rfl

/-- The arguments of the XOR of a chunk's keystream into the data. -/
theorem ksArgs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {j k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 64)
    (hjk : 16 * (j + k) ≤ c.n) (h23 : t.gpr .r23 = c.D + BitVec.ofNat 64 (16 * j))
    (h25 : t.gpr .r25 = BitVec.ofNat 64 k) :
    WP isa (.block ksArgs) t fun t₃ => PK t t₃ ∧ t₃.mem = t.mem ∧ (∀ r ∈ [Reg.r23, .r24, .r25], t₃.gpr r = t.gpr r) ∧
      XorDPre t₃ (c.W + BitVec.ofNat 64 496) (c.D + BitVec.ofNat 64 (16 * j)) (2 * k) := by
  have hn := L.n_lt
  have hdw := L.dw
  unfold ksArgs
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_lsl (by decide) fun t₃ u₃ =>
    WP.block_nil ?_
  have pk : PK t t₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  have E₃ := E.of_pk pk
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * j), 16 * k⟩ : Region).Disjoint ⟨c.W, 3824⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  refine ⟨pk, by rw [u₃.mem, u₂.mem, u₁.mem], fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have e8 : 8 * (2 * k) = 16 * k := by omega
  exact { r3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.r14]; rfl
          r4 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h23]
          r5 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h25, ofNat_shl, Nat.pow_one]
          pos := by omega
          lt := by omega
          rd := by
            rw [e8]
            exact VG.Proof.Gather.PPC64LE.covers_prefix (E₃.perm.wCR (show 496 + 1024 ≤ 3824 by decide)) (by omega)
          wr := by rw [e8]; exact VG.Proof.Gather.PPC64LE.covers_off E₃.perm.d (by omega) (by omega)
          disj := by
            rw [e8]
            exact (dQ.sub_right (Lay.wSub (show 496 + 1024 ≤ 3824 by decide))).symm.sub_left
              (Region.sub_prefix (by omega)) }

/-- After the XOR: `r23` and `r24` past the chunk, and `r11` zero if no
whole block is left. -/
theorem chunkNext_wp {c : Cx} (L : Lay c) {t : State} {j k : Nat} (hjk : 16 * (j + k) ≤ c.n)
    (hr4 : t.gpr .r4 = c.D + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (8 * (2 * k)))
    (h24 : t.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * j)) (h25 : t.gpr .r25 = BitVec.ofNat 64 k) :
    WP isa (.block chunkNext) t fun t' => PK t t' ∧ t'.mem = t.mem ∧
      t'.gpr .r23 = c.D + BitVec.ofNat 64 (16 * (j + k)) ∧ t'.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * (j + k)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 ((c.n - 16 * (j + k)) / 16) := by
  have hn := L.n_lt
  unfold chunkNext wholeLeft
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ u₁ => wp_lsl (by decide) fun t₂ u₂ => wp_sub fun t₃ u₃ => wp_lsr (by decide) fun t₄ u₄ =>
    WP.block_nil ?_
  have r24' : t₃.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * (j + k)) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h24, u₂.gpr, u₁.other _ (by decide), h25,
      ofNat_shl, ofNat_sub (by omega) (by omega)]
    congr 1; omega
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄))),
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_, by rw [u₄.other _ (by decide), r24'], ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hr4, Offset.add_add,
      show 16 * j + 8 * (2 * k) = 16 * (j + k) by omega]
  · rw [u₄.gpr, r24', ofNat_lsr 4 (by omega)]

theorem cryptChunk_wp {c : Cx} (L : Lay c) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n)
    {j : Nat} (hj : j < c.n / 16) {t t' : State} (E : Env c t') (P : BlocksPost c ciph icb x j t t')
    (hc : Spec.GcmSiv.ctxCiph t'.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa cryptChunk t' fun t'' => BlocksPost c ciph icb x (j + min ((c.n - 16 * j) / 16) 64) t t'' ∧
      t''.gpr .r11 = BitVec.ofNat 64 ((c.n - 16 * (j + min ((c.n - 16 * j) / 16) 64)) / 16) := by
  have hn := L.n_lt
  have hw := L.ww
  have hdw := L.dw
  generalize hkd : min ((c.n - 16 * j) / 16) 64 = k
  have hk1 : 1 ≤ k := by omega
  have hk : k ≤ 64 := by omega
  have hjk : 16 * (j + k) ≤ c.n := by omega
  have hk16 : ∀ i, (GcmSiv.ksBlock ciph icb i).length = 16 := fun i => by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  unfold cryptChunk
  refine WP.seq (WP.mono (chunkLen_wp (m := c.n - 16 * j) (by omega) P.r24) fun t₁ u₁ => ?_)
  rw [hkd] at u₁
  have E₁ := E.of_pk (PK.ofUpd u₁)
  have C₁ : CtrSt c.W icb j t₁.mem := by rw [u₁.mem]; exact P.ctr
  refine WP.seq (WP.mono (ctrBuild_wp L E₁ hk1 hk C₁ u₁.gpr) fun t₂ G => ?_)
  refine WP.seq (WP.mono (encArgs_wp L G.env hk G.r25) fun t₃ ⟨pk₃, m₃, k₃, bc⟩ => ?_)
  refine WP.seq (WP.mono (Proof.AesOcb.PPC64LE.blk_call Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.AesOcb.PPC64LE.encryptBlocks_noFrames bc) fun t₄ B => ?_)
  have pk₄ : PK t₃ t₄ := PK.ofSaved B.rd B.wr B.sp B.saved
  have E₄ := G.env.of_pk (pk₃.trans pk₄)
  have g₄ : ∀ r ∈ [Reg.r23, .r24, .r25], t₄.gpr r = t₂.gpr r := fun r hr => by
    rw [B.saved r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide), k₃ r hr]
  have r23₄ : t₄.gpr .r23 = c.D + BitVec.ofNat 64 (16 * j) := by
    rw [g₄ _ (by simp), G.r23, u₁.other _ (by decide), P.r23]
  have r24₄ : t₄.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * j) := by
    rw [g₄ _ (by simp), G.r24, u₁.other _ (by decide), P.r24]
  have r25₄ : t₄.gpr .r25 = BitVec.ofNat 64 k := by rw [g₄ _ (by simp), G.r25]
  -- The schedule and the keystream.
  have fG : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩, ⟨c.W + BitVec.ofNat 64 496, 1024⟩] t'.mem t₂.mem := by
    rw [← u₁.mem]; exact G.frame
  have hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (c.W + BitVec.ofNat 64 256) c.R = ciph := by
    rw [m₃, ← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.Cmac.bytesAt_frame fG (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb)
      · exact (L.w_w (.inl (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb))
      (by have := L.rb; omega)]
  have hks : ∀ q < k, bytesAt t₄.mem (c.W + BitVec.ofNat 64 496 + BitVec.ofNat 64 (16 * q)) 16 =
      GcmSiv.ksBlock ciph icb (j + q) := fun q hq => by
    rw [bytesAt_cipher B.out hq, Offset.add_add, m₃, G.blk q hq, ← m₃, ← hc₃]
    rfl
  -- The XOR.
  refine WP.seq (WP.mono (ksArgs_wp L E₄ hk1 hk hjk r23₄ r25₄) fun t₅ ⟨pk₅, m₅, k₅, lp⟩ => ?_)
  refine WP.seq (WP.mono (xorDLoop_ok t₅ lp) fun t₆ ⟨hm₆, O⟩ => ?_)
  have k₆ : ∀ r ∈ [Reg.r23, .r24, .r25], t₆.gpr r = t₄.gpr r := fun r hr => by
    have h' : r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
    rw [O.other r h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1 h'.2.2.2.2, k₅ r hr]
  refine WP.mono (chunkNext_wp L hjk O.r4 (by rw [k₆ _ (by simp), r24₄]) (by rw [k₆ _ (by simp), r25₄]))
    fun t₇ ⟨pk₇, m₇, r23₇, r24₇, r11₇⟩ => ?_
  have e16 : 8 * (2 * k) = 16 * k := by omega
  rw [e16] at hm₆
  -- What the call and the XOR wrote.
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * j), 16 * k⟩ : Region).Disjoint ⟨c.W, 3824⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have fX : Frame [⟨c.D + BitVec.ofNat 64 (16 * j), 16 * k⟩] t₄.mem t₇.mem := by
    rw [m₇, hm₆, m₅]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [Proof.AesGcm.PPC64LE.length_xorBytes]; exact Region.contains_self _ _)
  have fB : Frame [⟨c.W + BitVec.ofNat 64 496, 1024⟩, ⟨c.W + BitVec.ofNat 64 1776, 2048⟩] t₃.mem t₄.mem :=
    B.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨⟨?_, r23₇, r24₇, ?_, ?_, ?_⟩, r11₇⟩
  · exact P.pk.trans ((PK.ofUpd u₁).trans (G.pk.trans (pk₃.trans (pk₄.trans (pk₅.trans ((PK.ofLoop O).trans pk₇))))))
  · -- The counter block.
    refine ((G.ctr.of_frame (by rw [m₃] at fB; exact fB) fun r hr => ?_).of_frame fX fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dQ.sub_right (Lay.wSub (by decide))).symm
  · -- The data.
    have hD₄ : bytesAt t₄.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
      rw [Proof.Cmac.bytesAt_frame fB (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact L.d_w' (by decide)) (by omega), m₃,
        Proof.Cmac.bytesAt_frame fG (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact L.d_w' (by decide)) (by omega), P.data]
    rw [← hxl] at hD₄ ⊢
    refine GcmSiv.ctrPart_stepN ciph icb x c.D (fun l _ => hk16 _) hD₄ ?_ fun l hl => ?_
    · rw [hxl]
      intro p hp ho
      refine frame_outside fX (len := c.n) (a := 16 * j) (n := 16 * k) (fun q hq => ?_) (by omega) (by omega) p hp
        (by omega)
      simp only [List.mem_singleton] at hq
      exact .inl hq
    · rw [m₇, hm₆, m₅, show c.D + BitVec.ofNat 64 (16 * (j + l)) =
          c.D + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (16 * l) by rw [Offset.add_add, Nat.mul_add],
        xorBytes_block _ _ _ hl (by omega), ← hks l hl]
  · -- The frame.
    refine P.frame.trans ((?_ : Frame (cryR c.W c.D c.n) t'.mem t₂.mem).trans
      ((?_ : Frame (cryR c.W c.D c.n) t₂.mem t₄.mem).trans (?_ : Frame (cryR c.W c.D c.n) t₄.mem t₇.mem)))
    · exact fG.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    · rw [← m₃]; exact fB.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    · exact fX.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base _ (by omega)⟩

theorem blocks_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n) (hb1 : 1 ≤ c.n / 16)
    (h23 : t.gpr .r23 = c.D) (h24 : t.gpr .r24 = BitVec.ofNat 64 c.n)
    (C : CtrSt c.W icb 0 t.mem) (hx : bytesAt t.mem c.D c.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa (.loop cryptChunk (.nonzero .d .r11)) t (BlocksPost c ciph icb x (c.n / 16) t) := by
  have hn := L.n_lt
  refine WP.loop (M := isa)
    (fun (m : Nat) (t' : State) => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧ BlocksPost c ciph icb x j t t') ?_
    (c.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨PK.refl _, by rw [h23, Nat.mul_zero, BitVec.add_zero], by rw [h24, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro m t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (c.W + BitVec.ofNat 64 256) c.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptChunk_wp L hxl hj (E.of_pk P.pk) P hc') fun t'' ⟨Q, r11⟩ => ?_
  have ev := VG.Proof.Gather.PPC64LE.eval_nonzero r11 (by omega)
  by_cases he : j + min ((c.n - 16 * j) / 16) 64 = c.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ Q⟩
  · right
    exact ⟨ev.trans (by simp; omega), c.n / 16 - (j + min ((c.n - 16 * j) / 16) 64), by omega,
      j + min ((c.n - 16 * j) / 16) 64, rfl, by omega, Q⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (c : Cx) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  pk : PK t t'
  data : bytesAt t'.mem c.D c.n = GcmSiv.ctrPart ciph icb x c.n
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem

theorem cryptTail_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n) {b r : Nat}
    (hn : c.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h23 : t.gpr .r23 = c.D + BitVec.ofNat 64 (16 * b))
    (h24 : t.gpr .r24 = BitVec.ofNat 64 r) (C : CtrSt c.W icb b t.mem)
    (hx : bytesAt t.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa cryptTail t (TailPost c ciph icb x t) := by
  have hn' := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  unfold cryptTail
  refine WP.seq (WP.mono (tag_wp L E (o := 240) (by decide)) fun t₂ T => ?_)
  have E₂ := E.of_pk T.pk
  have dT : ∀ q ∈ tagR c.W 240, (⟨c.D, c.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact L.d_w' (by decide)
  have hx₂ : bytesAt t₂.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.Cmac.bytesAt_frame T.frame dT (by omega_arith), hx]
  have hks : bytesAt t₂.mem (c.W + BitVec.ofNat 64 240) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  refine WP.seq (wp_addi (by decide) (by decide) fun t₃ u₃ => wp_mv fun t₄ u₄ => wp_mv fun t₅ u₅ => WP.block_nil ?_)
  have pk₅ : PK t₂ t₅ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans (PK.ofUpd u₅))
  have E₅ := E₂.of_pk pk₅
  have m₅ : t₅.mem = t₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨c.W, 3824⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  have lp : LoopPre t₅ (c.W + BitVec.ofNat 64 240) (c.D + BitVec.ofNat 64 (16 * b)) r :=
    { r3 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, E₂.r14] <;> rfl
      r4 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), T.r23, h23]
      r5 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), T.r24, h24]
      pos := hr1
      lt := by omega_arith
      rd := VG.Proof.Gather.PPC64LE.covers_prefix (E₅.perm.wCR (show 240 + 16 ≤ 3824 by decide)) (by omega_arith)
      wr := VG.Proof.Gather.PPC64LE.covers_off E₅.perm.d (by omega_arith) (by omega_arith)
      disj := ((dQ.sub_right (Lay.wSub (show 240 + 16 ≤ 3824 by decide))).sub_right
        (Region.sub_prefix (by omega_arith))).symm }
  refine WP.mono (xorLoop_ok t₅ lp) fun t₆ ⟨hm₆, O⟩ => ?_
  rw [m₅] at hm₆
  have hl : (xorBytes t₂.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 240) r).length = r := by
    simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw : Frame [⟨c.D + BitVec.ofNat 64 (16 * b), r⟩] t₂.mem t₆.mem := by
    rw [hm₆]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.pk.trans (pk₅.trans (PK.ofLoop O)), ?_, ?_⟩
  · have hb' : bytesAt t₆.mem (c.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (c.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.PPC64LE.bytesAt_writeBytes_self t₂.mem (c.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 240) r) (by omega_arith)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (c.W + BitVec.ofNat 64 240) r (16 - r)
      rw [show r + (16 - r) = 16 by omega_arith, hks] at hs
      rw [hm₆, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega_arith) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega_arith) (by omega_arith)) hb'
    rwa [hxl, ← hn] at this
  · refine (T.frame.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (c : Cx) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem
  data : bytesAt t'.mem c.D c.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) (bytesAt t.mem c.D c.n)

/-- The memory `cryptHead` leaves: the counter block from the tag. -/
def headMem (m : Mem) (W : Addr) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 96) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
    (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (m.readW (W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) 64 |||
      1#64 <<< 63)

/-- What `cryptHead` leaves: the counter block from the tag, and the data as
the bytes to encrypt. -/
structure HeadPost (c : Cx) (t t₁ : State) : Prop where
  pk : PK t t₁
  r23 : t₁.gpr .r23 = c.D
  r24 : t₁.gpr .r24 = BitVec.ofNat 64 c.n
  r11 : t₁.gpr .r11 = BitVec.ofNat 64 (c.n / 16)
  frame : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem
  ctr : CtrSt c.W (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) 0 t₁.mem
  data : bytesAt t₁.mem c.D c.n = bytesAt t.mem c.D c.n
  ciph : Spec.GcmSiv.ctxCiph t₁.mem (c.W + BitVec.ofNat 64 256) c.R =
    Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R

theorem cryptHead_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) : WP isa (.block cryptHead) t (HeadPost c t) := by
  have hw := L.ww
  have hn := L.n_lt
  unfold cryptHead wholeLeft
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ u₁ => wp_mv fun t₂ u₂ => ?_
  have g₂ : ∀ r, r ≠ .r23 → r ≠ .r24 → t₂.gpr r = t.gpr r := fun r h3 h4 => by rw [u₂.other _ h4, u₁.other _ h3]
  have rd₂ : t₂.rd ++ t₂.wr = t.rd ++ t.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_ld (a := c.W + BitVec.ofNat 64 0) (by decide) (by decide) (by rw [g₂ _ (by decide) (by decide), E.r14] <;> rfl)
    (by rw [rd₂]; exact E.perm.wR (by decide)) fun t₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), g₂ _ (by decide) (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, Offset.add_add]; exact E.perm.wR (by decide)) fun t₄ u₄ => ?_
  refine wp_li (by decide) fun t₅ u₅ => wp_lsl (by decide) fun t₆ u₆ => wp_or fun t₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r23 → r ≠ .r24 → t₇.gpr r = t.gpr r :=
    fun r h3 h4 h5 h23 h24 => by
      rw [u₇.other _ h4, u₆.other _ h5, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3, g₂ _ h23 h24]
  have wr₇ : t₇.wr = t.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_std (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide)
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r14] <;> rfl)
    (by rw [wr₇]; exact E.perm.wW (by decide)) fun t₈ u₈ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₈.gpr, g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₈.wr, wr₇, Offset.add_add]; exact E.perm.wW (by decide)) fun t₉ u₉ => ?_
  refine wp_lsr (by decide) fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₁ : PK t t₁₀ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofMupd u₈).trans ((PK.ofMupd u₉).trans
    (PK.ofUpd u₁₀)))))))))
  have E₁ := E.of_pk pk₁
  have hm₁ : t₁₀.mem = headMem t.mem c.W := by
    rw [u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, u₇.gpr, u₇.other .r3 (by decide), u₇.mem, u₆.gpr, u₆.other .r3 (by decide),
      u₆.other .r4 (by decide), u₆.mem, u₅.gpr, u₅.other .r3 (by decide), u₅.other .r4 (by decide), u₅.mem, u₄.gpr,
      u₄.other .r3 (by decide), u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem]
    rfl
  have r23₁ : t₁₀.gpr .r23 = c.D := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.r20]
  have r24₁ : t₁₀.gpr .r24 = BitVec.ofNat 64 c.n := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r21]
  have r11₁ : t₁₀.gpr .r11 = BitVec.ofNat 64 (c.n / 16) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r21, ofNat_lsr 4 hn]
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁₀.mem := by
    rw [hm₁, headMem]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨c.D, c.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁₀.mem c.D c.n = bytesAt t.mem c.D c.n :=
    Proof.Cmac.bytesAt_frame f₁ dD (by omega_arith)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁₀.mem (c.W + BitVec.ofNat 64 256) c.R =
      Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.Cmac.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb))
      (by have := L.rb; omega_arith)]
  have hicb : bytesAt t₁₀.mem (c.W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16) := by
    rw [hm₁, headMem, Proof.Cmac.bytesAt_store2, show (1#64 <<< 63 : BitVec 64) = 0x8000000000000000#64 by decide,
      ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split,
      BitVec.add_zero]
  have h4 := Proof.Cmac.bytesAt_add t₁₀.mem (c.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, Offset.add_add] at h4
  have C₀ : CtrSt c.W (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) 0 t₁₀.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  exact ⟨pk₁, r23₁, r24₁, r11₁, f₁, C₀, hx₁, hc₁⟩

theorem crypt_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) : WP isa crypt t (CryptPost c t) := by
  have hw := L.ww
  have hn := L.n_lt
  unfold crypt
  refine WP.seq (WP.mono (cryptHead_wp L E) fun t₁₀ Hd => ?_)
  have pk₁ := Hd.pk
  have E₁ := E.of_pk pk₁
  have r23₁ := Hd.r23
  have r24₁ := Hd.r24
  have r11₁ := Hd.r11
  have f₁ := Hd.frame
  have C₀ := Hd.ctr
  have hx₁ := Hd.data
  have hc₁ := Hd.ciph
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem c.D c.n).length = c.n := Proof.Cmac.bytesAt_length _ _ _
  have fC : ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ cryR c.W c.D c.n, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨c.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  -- The whole blocks.
  have hmid : WP isa (.ite (.zero .d .r11) (.block []) (.loop cryptChunk (.nonzero .d .r11))) t₁₀
      (BlocksPost c (Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) (bytesAt t.mem c.D c.n) (c.n / 16) t₁₀) := by
    refine WP.ite (decide (c.n / 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero r11₁ (by omega_arith)) (fun ht => ?_)
      (fun hf => ?_)
    · have h0 : c.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨PK.refl _, by rw [r23₁, Nat.mul_zero, BitVec.add_zero], by rw [r24₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : c.n / 16 ≠ 0 := by simpa using hf
      exact blocks_wp L E₁ hxl (by omega_arith) r23₁ r24₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have r24₂ : t₂.gpr .r24 = BitVec.ofNat 64 (c.n % 16) := by rw [B.r24]; congr 1; omega_arith
  refine WP.ite (decide (c.n % 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero r24₂ (by omega_arith)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨pk₁.trans B.pk, (f₁.sub fC).trans B.frame, ?_⟩
    rw [B.data, show 16 * (c.n / 16) = c.n by omega_arith, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : c.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (c.W + BitVec.ofNat 64 256) c.R =
        Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R := by
      rw [ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_wp L (E₁.of_pk B.pk) hxl (b := c.n / 16) (r := c.n % 16) (by omega_arith)
      (by omega_arith) (by omega_arith) B.r23 r24₂ B.ctr B.data hc₂) fun t₃ T => ?_
    refine ⟨pk₁.trans (B.pk.trans T.pk), ((f₁.sub fC).trans B.frame).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.PPC64LE
