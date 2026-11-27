module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.AesGcmSiv.Arm
public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
public import VerifiedGarbage.Proof.AesGcmSiv.Arm.Env
public import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesGcm.Arm.Args
import VerifiedGarbage.Proof.AesGcmSiv.Arm.Polyval
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.GcmSiv.Ctr
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.GcmSiv.Words32

/-! ### `AesGcmSiv.Arm.Crypt`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.Arm.Tag`, which only this module used -/

section

/-!
# AES-GCM-SIV on ARMv7: a block encrypted with the encryption key (`tag`)

Untrusted: everything here is checked by Lean. `tag o` copies the block at
`W + 96` to `W + 112` (`copyMem`), zeroes the block at `W + o`, and calls
`vg_aes_ctr32` on that one block with the copy as the counter block: the
encryption of the block at `W + 96` with the encryption key's schedule at
`W + 192` (`tag_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below covers_cons covers_nil covers_append' add_ofNat_assoc
  add_ofNat_zero mem_store gpr_store sp_store rd_store wr_store z_store)

theorem blockAt_zero4 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero4 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 32)
    (m.readW (W + BitVec.ofNat 64 100) 32) (m.readW (W + BitVec.ofNat 64 104) 32)
    (m.readW (W + BitVec.ofNat 64 108) 32)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (copyMem m W) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]
  simp only [add_ofNat_assoc, Nat.reduceAdd]

/-- What `tag o` writes. -/
abbrev tagR (W : Addr) (SP : BitVec 32) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 1712, 2048⟩, below SP]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : Prm) (o : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = t.gpr .r4
  r5 : t'.gpr .r5 = t.gpr .r5
  frame : Frame (tagR (State.addr p.W) p.SP o) t.mem t'.mem
  out : bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R
      (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 96) 16)

/-- The arguments of `tag o`'s call. -/
theorem tagArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : o = 0 ∨ o = 176) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
        ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 (copyMem t.mem (State.addr p.W)) (State.addr p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .r0 = p.W + BitVec.ofNat 32 192 ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .r3 = p.W + BitVec.ofNat 32 o ∧
      t₁.gpr .r12 = BitVec.ofNat 32 1 ∧ t₁.gpr .lr = p.W + BitVec.ofNat 32 1712 ∧
      Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  obtain r₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  obtain r₁ := E.perm.wR (show 100 + 4 ≤ 3760 by decide)
  obtain r₂ := E.perm.wR (show 104 + 4 ≤ 3760 by decide)
  obtain r₃ := E.perm.wR (show 108 + 4 ≤ 3760 by decide)
  obtain w₀ := E.perm.wW (show 112 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wW (show 116 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wW (show 120 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wW (show 124 + 4 ≤ 3760 by decide)
  obtain z₀ := E.perm.wW (show o + 4 ≤ 3760 by omega_arith)
  obtain z₁ := E.perm.wW (show o + 4 + 4 ≤ 3760 by omega_arith)
  obtain z₂ := E.perm.wW (show o + 8 + 4 ≤ 3760 by omega_arith)
  obtain z₃ := E.perm.wW (show o + 12 + 4 ≤ 3760 by omega_arith)
  obtain o₁ : o < 3760 := by omega_arith
  obtain o₂ : o + 4 < 3760 := by omega_arith
  obtain o₃ : o + 8 < 3760 := by omega_arith
  obtain o₄ : o + 12 < 3760 := by omega_arith
  obtain i₁ : o < 4096 := by omega_arith
  obtain i₂ : o + 4 < 4096 := by omega_arith
  obtain i₃ : o + 8 < 4096 := by omega_arith
  obtain i₄ : o + 12 < 4096 := by omega_arith
  obtain oe : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  refine ⟨_, by simp only [copy16, Impl.AesGcm.Arm.zero16, ctrArgs]; srun [E.r8, E.r11, L.wA, r₀, r₁, r₂, r₃,
    w₀, w₁, w₂, w₃, z₀, z₁, z₂, z₃, o₁, o₂, o₃, o₄, i₁, i₂, i₃, i₄, oe], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, by rfl,
    by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.zero4,
      Proof.Cmac.store4, copyMem, add_ofNat_assoc, Nat.reduceAdd]
    rfl
  all_goals simp [gpr_setReg, E.r8, E.r11]

/-- The arguments of `tag o`'s call, as `vg_aes_ctr32` needs them. -/
theorem tagCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) {o : Nat} (ho : o = 0 ∨ o = 176)
    (r0 : t₁.gpr .r0 = p.W + BitVec.ofNat 32 192) (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R)
    (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112) (r3 : t₁.gpr .r3 = p.W + BitVec.ofNat 32 o)
    (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1) (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 o)
      (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have hw := L.ww
  obtain o₁ : o < 3760 := by omega_arith
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, by rw [L.wN (by decide)]; omega_arith,
    by rw [L.wN (by decide)]; omega_arith, by rw [L.wN o₁]; omega_arith, by rw [L.wN (by decide)]; omega_arith,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.wA o₁,
      L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one]
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega_arith)) (by decide) (by omega_arith)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.w_w (by omega_arith) (by omega_arith) (by decide) :
      (⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by omega_arith)
  · exact L.bw' (by decide)
  · exact E₁.perm.wCR (by decide)
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by omega_arith))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))

theorem tag_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : o = 0 ∨ o = 176) :
    WP isa (tag o) t (TagPost p o t) := by
  have hw := L.ww
  obtain o₁ : o < 3760 := by omega_arith
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := tagArgs_ok L E ho
  obtain E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  obtain dO : (⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega_arith) (by omega_arith) (by decide)
  obtain cc := tagCall L E₁ ho r0 r1 r2 r3 r12 lr
  obtain fZ := Proof.Cmac.frame_store4 (m := copyMem t.mem (State.addr p.W)) (State.addr p.W + BitVec.ofNat 64 o) 0 0 0 0
  obtain f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩]
      t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero4]
    exact ((copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  obtain hb₁ : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero4, Proof.AesGcm.Arm.bytesAt_frame fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), copyMem_bytes]
  obtain hz₁ : Spec.Gcm.blockAt t₁.mem (State.addr p.W + BitVec.ofNat 64 o) = 0 := by
    rw [hm₁]; exact blockAt_zero4 _ _
  obtain ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (L.w_w (.inr (by omega_arith)) (by decide) (by omega_arith)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_arith)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (ctr_call cc) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.wA o₁,
    L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one] at fc hout
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [P.rd, rd₁], by rw [P.wr, wr₁],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 192) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.Arm

end

end


/-!
# AES-GCM-SIV on ARMv7: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 176` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below covers_cons covers_nil covers_append' covers_off
  covers_left covers_prefix add_ofNat_assoc add_ofNat_zero add32_ofNat_assoc eval_eq' eval_ne' z_cmp ofNat_sub32
  ofNat_add32 toNat32 mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags
  sp_subFlags rd_subFlags wr_subFlags LoopPre LoopOut xorLoop_ok xorBytes length_bytesAt)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega_arith) (by omega_arith)) hc

/-- What counter mode writes: the counter block, its copy, the block at
`W + 176`, `vg_aes_ctr32`'s working space, the data and the stack below
`SP`. -/
abbrev cryR (W D : Addr) (n : Nat) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 176, 16⟩, ⟨W + BitVec.ofNat 64 1712, 2048⟩, ⟨D, n⟩, below SP]

/-- Block `j` of the data, as a 64-bit address. -/
theorem Lay.dA {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) :
    State.addr (p.D + BitVec.ofNat 32 j) = State.addr p.D + BitVec.ofNat 64 j :=
  addr_add (by have := L.dw; omega_arith)

theorem Lay.dN {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) : (p.D + BitVec.ofNat 32 j).toNat = p.D.toNat + j := by
  have := L.dw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (j + 1))
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * (j + 1))
  z : t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0)
  ctr : CtrSt (State.addr p.W) icb (j + 1) t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat}
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr)) t = some t₁ ∧
      t₁.mem = copyMem t.mem (State.addr p.W) ∧
      t₁.gpr .r0 = p.W + BitVec.ofNat 32 192 ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .r3 = p.D + BitVec.ofNat 32 (16 * j) ∧
      t₁.gpr .r12 = BitVec.ofNat 32 1 ∧ t₁.gpr .lr = p.W + BitVec.ofNat 32 1712 ∧
      Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  obtain r₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  obtain r₁ := E.perm.wR (show 100 + 4 ≤ 3760 by decide)
  obtain r₂ := E.perm.wR (show 104 + 4 ≤ 3760 by decide)
  obtain r₃ := E.perm.wR (show 108 + 4 ≤ 3760 by decide)
  obtain w₀ := E.perm.wW (show 112 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wW (show 116 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wW (show 120 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wW (show 124 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [copy16, ctrArgs]; srun [E.r8, E.r11, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.store4, copyMem,
      add_ofNat_assoc, Nat.reduceAdd]
  all_goals simp [gpr_setReg, E.r8, E.r11, h4]

/-- The arguments of a block's call, as `vg_aes_ctr32` needs them. -/
theorem blkCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (r0 : t₁.gpr .r0 = p.W + BitVec.ofNat 32 192) (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R)
    (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112) (r3 : t₁.gpr .r3 = p.D + BitVec.ofNat 32 (16 * j))
    (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1) (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.D + BitVec.ofNat 32 (16 * j))
      (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have hn := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  obtain dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, by rw [L.wN (by decide)]; omega_arith,
    by rw [L.wN (by decide)]; omega_arith, by rw [L.dN (by omega_arith)]; omega_arith, by rw [L.wN (by decide)]; omega_arith,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.dA (show 16 * j < p.n by omega_arith),
      L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one]
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact (dQ.sub_right (Lay.wSub (show 192 + 240 ≤ 3760 by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (dQ.sub_right (Lay.wSub (show 112 + 16 ≤ 3760 by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact dQ.sub_right (Lay.wSub (by decide))
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bd.sub_right (Offset.sub_base _ (by omega_arith))
  · exact L.bw' (by decide)
  · exact E₁.perm.wCR (by decide)
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (covers_off E₁.perm.d (by omega_arith) (by omega_arith))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))

/-- The code after a block's call. -/
theorem blkPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)) (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)) :
    ∃ t' : State, runBlock isa blockNext t = some t' ∧
      t'.mem = t.mem.writeW (State.addr p.W + BitVec.ofNat 64 96)
        (t.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 + BitVec.ofNat 32 1) ∧
      t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (j + 1)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) ∧
      t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0) ∧ Others [.r0, .r4, .r5, .r12] t t' ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hn := L.n_lt
  obtain c₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  obtain c₁ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  obtain e5 : BitVec.ofNat 32 (p.n - 16 * j) - BitVec.ofNat 32 16 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) := by
    rw [ofNat_sub32 (by omega_arith) (by omega_arith), show p.n - 16 * j - 16 = p.n - 16 * (j + 1) by omega_arith]
  refine ⟨_, by simp only [blockNext, wholeLeft]; srun [E.r11, L.wA, h4, h5, c₀, c₁], ?_, ?_, ?_, ?_, by others_tac,
    by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags]
  · simp [gpr_setReg, add32_ofNat_assoc, Nat.mul_succ]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, e5]
  · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, e5, ofNat_lsr32 (show p.n - 16 * (j + 1) < 2 ^ 32 by omega_arith)]
    rw [z_cmp (by omega_arith) (by decide)]

theorem cryptBlock_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)) (C : CtrSt (State.addr p.W) icb j t.mem)
    (hx : bytesAt t.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa cryptBlock t (BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn := L.n_lt
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok L E h4
  obtain E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  obtain dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  obtain cc := blkCall L E₁ hj r0 r1 r2 r3 r12 lr
  -- What the copy changed.
  obtain f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact copyMem_frame _ _
  obtain dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ : Region)],
      (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  obtain hcb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, copyMem_bytes, C.block]
  obtain hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_arith)]
  obtain hx₁ : bytesAt t₁.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ dD (by omega_arith), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (ctr_call cc) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.dA (show 16 * j < p.n by omega_arith),
    L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one] at fc hout
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    ctr32_single, List.cons.injEq, and_true] at hout
  obtain hb₂ : bytesAt t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 192) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R from rfl, hc₁, hcb]
  obtain hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  obtain hx₂ : bytesAt t₂.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x _ (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega_arith)])
    rw [hxl]
    refine frame_outside fc (fun q hq => ?_) (by omega_arith) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inr L.bd.symm
  obtain E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  obtain h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h4]
  obtain h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h5]
  -- What the first two pieces changed.
  obtain f₂' : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 1712, 2048⟩, below p.SP] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  obtain f₂ : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 1712, 2048⟩, below p.SP],
        (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega_arith))).symm
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (L.bw' (by omega_arith)).symm
  obtain w₂ : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (Nat.le_refl _) (by decide)) (by decide)
  obtain r₂ : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 100) 12 =
      bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.Arm.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  obtain fw : ∀ v : BitVec 32, Frame [⟨State.addr p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem
      (t₂.mem.writeW (State.addr p.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨t₃, run₃, hm₃, r4₃, r5₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := blkPost_ok L E₂ hj h4₂ h5₂
  refine WP.of_runBlock ⟨t₃, run₃, E₂.of_others ho₃ sp₃ rd₃ wr₃, by rw [rd₃, P.rd, rd₁], by rw [wr₃, P.wr, wr₁],
    r4₃, r5₃, z₃, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hm₃, Mem.readW_writeW_self32, w₂, C.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  · rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), r₂, C.rest]
  · rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)) (Nat.le_of_lt (by omega_arith)), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega_arith]
  · rw [hm₃]
    exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains _ (Nat.le_refl _) (by decide) (by decide))


/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : Prm} (L : Lay p) :
    ∀ r ∈ cryR (State.addr p.W) (State.addr p.D) p.n p.SP,
      (⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm
  · exact (L.bw' (by decide)).symm

theorem ciph_cryR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) m m') :
    Spec.GcmSiv.ctxCiph m' (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph m (State.addr p.W + BitVec.ofNat 64 192) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.Arm.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega_arith)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b)
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * b)
  ctr : CtrSt (State.addr p.W) icb b t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

theorem blocks_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (h4 : t.gpr .r4 = p.D) (h5 : t.gpr .r5 = BitVec.ofNat 32 p.n)
    (C : CtrSt (State.addr p.W) icb 0 t.mem) (hx : bytesAt t.mem (State.addr p.D) p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa (.loop cryptBlock .ne) t (BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h5, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  obtain hc' : Spec.GcmSiv.ctxCiph t'.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_ok L P.env hxl (j := j) (by omega_arith) P.r4 P.r5 P.ctr P.data hc') fun t'' Q => ?_
  obtain P' : BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.r4, Q.r5, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  obtain ev := eval_ne' Q.z
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega_arith), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), p.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

theorem cryptTail_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) (C : CtrSt (State.addr p.W) icb b t.mem)
    (hx : bytesAt t.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa cryptTail t (TailPost p ciph icb x t) := by
  have hn' := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  refine WP.seq (WP.mono (tag_ok L E (o := 176) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  obtain dT : ∀ q ∈ tagR (State.addr p.W) p.SP 176, (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  obtain hx₂ : bytesAt t₂.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.Arm.bytesAt_frame fT dT (by omega_arith), hx]
  obtain hks : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  obtain h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b) := by rw [T.r4, h4]
  obtain h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 r := by rw [T.r5, h5]
  obtain ⟨t₃, run₃, r1₃, r2₃, r3₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [Impl.AesGcm.Arm.addI .r1 .r11 bO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)] t₂ = some t₃ ∧
      t₃.gpr .r1 = p.W + BitVec.ofNat 32 176 ∧ t₃.gpr .r2 = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .r3 = BitVec.ofNat 32 r ∧ Others [.r1, .r2, .r3] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, T.env.r11]
    · simp [gpr_setReg, h4₂]
    · simp [gpr_setReg, h5₂]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain eD := L.dA (j := 16 * b) (by omega_arith)
  obtain dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  obtain lp : LoopPre t₃ (p.W + BitVec.ofNat 32 176) (p.D + BitVec.ofNat 32 (16 * b)) r := by
    refine ⟨r1₃, r2₃, r3₃, by omega_arith, by omega_arith, by rw [L.wN (by decide)]; omega_arith, by rw [L.dN (by omega_arith)]; omega_arith,
      ?_, ?_, ?_⟩
    · rw [rd₃, wr₃, L.wA (by decide)]
      exact covers_prefix (T.env.perm.wCR (show 176 + 16 ≤ 3760 by decide)) (by omega_arith)
    · rw [wr₃, eD]; exact covers_off T.env.perm.d (by omega_arith) (by omega_arith)
    · rw [eD, L.wA (by decide)]
      exact ((dQ.sub_right (Lay.wSub (show 176 + 16 ≤ 3760 by decide))).sub_right (Region.sub_prefix (by omega_arith))).symm
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, O⟩ => ?_
  rw [m₃, eD, L.wA (by decide)] at hm₄
  obtain hl : (xorBytes t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) (State.addr p.W + BitVec.ofNat 64 176) r).length
      = r := by simp [xorBytes, Proof.Cmac.bytesAt_length]
  obtain fw := Proof.AesGcm.Arm.writeBytes_frame' t₂.mem (q := State.addr p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  obtain hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.env.keep (fun q hq => by
      obtain h1 : q ≠ .r1 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      obtain h2 : q ≠ .r2 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      obtain h3 : q ≠ .r3 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      obtain h0 : q ≠ .r0 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      obtain h12 : q ≠ .r12 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [O.other q h0 h1 h2 h3 h12, ho₃ q (by simp [h1, h2, h3])])
      (by rw [O.sp, sp₃]) (by rw [O.rd, rd₃]) (by rw [O.wr, wr₃]),
    by rw [O.rd, rd₃, T.rd], by rw [O.wr, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      obtain e := Proof.AesGcm.Arm.bytesAt_writeBytes_self t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) (State.addr p.W + BitVec.ofNat 64 176) r)
        (by omega_arith)
      rw [hl] at e
      obtain hs := Proof.Cmac.bytesAt_add t₂.mem (State.addr p.W + BitVec.ofNat 64 176) r (16 - r)
      rw [show r + (16 - r) = 16 by omega_arith, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega_arith) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega_arith) (by omega_arith)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) (bytesAt t.mem (State.addr p.D) p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag. -/
def headMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96) (m.readW W 32) (m.readW (W + BitVec.ofNat 64 4) 32)
    (m.readW (W + BitVec.ofNat 64 8) 32) (m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = headMem t.mem (State.addr p.W) ∧
      t₁.gpr .r4 = p.D ∧ t₁.gpr .r5 = BitVec.ofNat 32 p.n ∧ t₁.z = decide (p.n / 16 = 0) ∧
      Others [.r0, .r1, .r2, .r3, .r4, .r5, .r12] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  obtain rT₀ : InRegions (t.rd ++ t.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  obtain rT₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  obtain rT₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  obtain rT₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  obtain w₀ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wW (show 100 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wW (show 104 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wW (show 108 + 4 ≤ 3760 by decide)
  obtain a₄ := E.perm.argR' L (k := 4) (by decide)
  obtain a₈ := E.perm.argR' L (k := 8) (by decide)
  refine ⟨_, by simp only [cryptHead, wholeLeft]; srun [E.r11, E.sp, add_ofNat_zero, L.wA, rT₀, rT₁, rT₂, rT₃, w₀,
    w₁, w₂, w₃, a₄, a₈, A.a4, A.a8], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, headMem,
      Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ofNat_lsr32 L.n_lt]
    rw [z_cmp (by have := L.n_lt; omega_arith) (by decide)]

theorem crypt_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    WP isa crypt t (CryptPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, r4₁, r5₁, z₁, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E A
  obtain hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  obtain hxl : (bytesAt t.mem (State.addr p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  obtain f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, headMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  obtain hx₁ : bytesAt t₁.mem (State.addr p.D) p.n = bytesAt t.mem (State.addr p.D) p.n :=
    Proof.AesGcm.Arm.bytesAt_frame f₁ dD (by omega_arith)
  obtain hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_arith)]
  obtain hicb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16) := by
    rw [hm₁, headMem, Proof.Cmac.bytesAt_store4, ← GcmSiv.Words32.initialCounter_words, Proof.Cmac.le4_readW,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]
  obtain h4 := Proof.Cmac.bytesAt_add t₁.mem (State.addr p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  obtain C₀ : CtrSt (State.addr p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  obtain E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  obtain fC : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      ∃ q' ∈ cryR (State.addr p.W) (State.addr p.D) p.n p.SP, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  obtain hmid : WP isa (.ite .eq (.block []) (.loop cryptBlock .ne)) t₁
      (BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) (bytesAt t.mem (State.addr p.D) p.n)
        (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [r4₁, Nat.mul_zero, add_ofNat_zero], by rw [r5₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok L E₁ hxl (by omega_arith) r4₁ r5₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  obtain r5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [B.r5]; congr 1; omega_arith
  obtain ⟨t₃, run₃, z₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa [.cmp .r5 (Impl.AesGcm.Arm.imm 0)] t₂ = some t₃ ∧
      t₃.z = decide (p.n % 16 = 0) ∧ Others [] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [r5₂], ?_, fun r _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
    simp only [z_subFlags]
    rw [z_cmp (by omega_arith) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain E₃ : Env p t₃ := B.env.of_others ho₃ sp₃ rd₃ wr₃
  refine WP.ite (decide (p.n % 16 = 0)) (eval_eq' z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [rd₃, B.rd, rd₁], by rw [wr₃, B.wr, wr₁], by rw [m₃]; exact (f₁.sub fC).trans B.frame, ?_⟩
    rw [m₃, B.data, show 16 * (p.n / 16) = p.n by omega_arith, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    obtain hc₂ : Spec.GcmSiv.ctxCiph t₃.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
        Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
      rw [m₃, ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_ok L E₃ hxl (b := p.n / 16) (r := p.n % 16) (by omega_arith) (by omega_arith) (by omega_arith)
      (by rw [ho₃ _ (by simp), B.r4]) (by rw [ho₃ _ (by simp), r5₂]) (m₃ ▸ B.ctr) (by rw [m₃]; exact B.data) hc₂)
      fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, rd₃, B.rd, rd₁], by rw [T.wr, wr₃, B.wr, wr₁],
      ((f₁.sub fC).trans (m₃ ▸ B.frame)).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.Arm

end

end

/-!
# AES-GCM-SIV on ARMv7: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp` sets `r0` to 1 if the
tags at `W` and `W + 176` are equal and 0 if not, without a branch, as
AES-GCM's `cmpTail` does (`Proof.AesGcm.Arm.cmp_value`) (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − r0`: it keeps the data if `r0` is 1
and zeroes it if `r0` is 0 (`mask_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.Arm (add_ofNat_assoc add_ofNat_zero eval_eq' eval_ne' z_cmp ofNat_sub32 ofNat_add32
  mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags rd_subFlags
  wr_subFlags length_bytesAt in_of_covers cmp_value words_eq_iff bytes_words)

theorem cmp_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.gpr .r0 = (if bytesAt t.mem (State.addr p.W) 16 =
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 176) 16 then 1 else 0) ∧
      Others [.r0, .r1, .r2] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain r₀ : InRegions (t.rd ++ t.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  obtain r₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  obtain r₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  obtain r₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  obtain q₀ := E.perm.wR (show 176 + 4 ≤ 3760 by decide)
  obtain q₁ := E.perm.wR (show 180 + 4 ≤ 3760 by decide)
  obtain q₂ := E.perm.wR (show 184 + 4 ≤ 3760 by decide)
  obtain q₃ := E.perm.wR (show 188 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [cmp, xorW]; srun [E.r11, add_ofNat_zero, L.wA, r₀, r₁, r₂, r₃, q₀, q₁, q₂, q₃], ?_,
    by others_tac, by rfl, by rfl, by rfl, by rfl⟩
  simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  rw [cmp_value, bytes_words, bytes_words]
  simp only [add_ofNat_assoc, add_ofNat_zero, Nat.reduceAdd]
  congr 1
  exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm

/-! ## The mask -/

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, Impl.AesGcm.Arm.addI .r4 .r4 1,
    .subs .r5 .r5 (Impl.AesGcm.Arm.imm 1)]

theorem byte_and (a : Byte) (k : BitVec 32) : (a.setWidth 32 &&& k).setWidth 8 = a &&& k.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 32 by omega_arith, hi, decide_true, Bool.true_and]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept' {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : BitVec 32} {n : Nat} (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    (hn1 : 1 ≤ n) (hn : n < 2 ^ 32) (hf : D.toNat + n ≤ 2 ^ 32) (hw : Covers [⟨State.addr D, n⟩] s.wr) :
    WP isa (.loop (.block maskBody) .ne) s fun s' =>
      s'.mem = writeBytes s.mem (State.addr D) (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) n) ∧
      Others [.r4, .r5, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r4 = D + BitVec.ofNat 32 i ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (State.addr D) (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) i) ∧
      Others [.r4, .r5, .r12] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, by omega_arith, by rw [h4, add_ofNat_zero], by rw [h5, Nat.sub_zero],
      by simp [maskBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r4, r5, mem, g, sp, rd, wr⟩
  obtain ea : State.addr (D + BitVec.ofNat 32 i) = State.addr D + BitVec.ofNat 64 i := addr_add (by omega_arith)
  obtain w₁ : InRegions t.wr (State.addr D + BitVec.ofNat 64 i) 1 := by rw [wr]; exact in_of_covers hw hi (by omega_arith)
  obtain w₂ : InRegions (t.rd ++ t.wr) (State.addr D + BitVec.ofNat 64 i) 1 := Proof.AesGcm.Arm.in_left w₁
  obtain h1 : t.gpr .r1 = s.gpr .r1 := g _ (by decide)
  obtain ⟨t', run', mem', r4', r5', z', g', sp', rd', wr'⟩ : ∃ t', runBlock isa maskBody t = some t' ∧
      t'.mem = t.mem.writeW (State.addr D + BitVec.ofNat 64 i)
        (t.mem (State.addr D + BitVec.ofNat 64 i) &&& (s.gpr .r1).setWidth 8) ∧
      t'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ t'.gpr .r5 = BitVec.ofNat 32 (n - (i + 1)) ∧
      t'.z = decide (n - (i + 1) = 0) ∧ Others [.r4, .r5, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
    refine ⟨_, by srun [r4, r5, add_ofNat_zero, ea, w₁, w₂], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, byte_and, h1]
    · simp [gpr_setReg, r4, Proof.AesGcm.Arm.add32_ofNat_assoc]
    · simp only [gpr_setReg, gpr_subFlags, ite_true, r5]
      rw [ofNat_sub32 (by omega_arith) (by omega_arith)]; rfl
    · simp only [z_setReg, z_subFlags]
      rw [z_cmp (by omega_arith) (by decide)]
      congr 1; apply propext; omega_arith
  refine WP.of_runBlock ⟨t', run', ?_⟩
  obtain hlen : (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) i).length = i := by
    simp [maskBytes, length_bytesAt]
  obtain hmem : t'.mem = writeBytes s.mem (State.addr D) (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) (i + 1)) := by
    rw [mem', mem, dst_kept' (by omega_arith) _ hlen]
    simp only [maskBytes]
    rw [Proof.AesGcm.Arm.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      writeBytes_snoc s.mem _ _ _ (by rw [List.length_map, length_bytesAt]; omega_arith),
      List.length_map, length_bytesAt]
  obtain ev := eval_ne' z'
  obtain gg : Others [.r4, .r5, .r12] s t' := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r4', r5', hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#32 - BitVec.ofNat 32 1 : BitVec 32).setWidth 8) = xs := by
  rw [show (0#32 - BitVec.ofNat 32 1 : BitVec 32).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#32 - BitVec.ofNat 32 0 : BitVec 32).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#32 - BitVec.ofNat 32 0 : BitVec 32).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `r0` is whether `c` holds. -/
structure MaskPost (p : Prm) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : Env p t'
  r0 : t'.gpr .r0 = t.gpr .r0
  frame : Frame [⟨State.addr p.D, p.n⟩] t.mem t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = if c then bytesAt t.mem (State.addr p.D) p.n else Spec.GcmSiv.zeros p.n

theorem mask_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) {c : Prop} [Decidable c]
    (hok : t.gpr .r0 = BitVec.ofNat 32 (if c then 1 else 0)) :
    WP isa mask t (MaskPost p c t) := by
  have hn := L.n_lt
  obtain a₄ := E.perm.argR' L (k := 4) (by decide)
  obtain a₈ := E.perm.argR' L (k := 8) (by decide)
  obtain ⟨t₁, run₁, r1₁, r4₁, r5₁, z₁, ho₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      [.ldrSp .r4 4, .ldrSp .r5 8, .mov .r1 (Impl.AesGcm.Arm.imm 0), .dp .sub .r1 .r1 (.reg .r0),
        .cmp .r5 (Impl.AesGcm.Arm.imm 0)] t = some t₁ ∧
      t₁.gpr .r1 = 0#32 - t.gpr .r0 ∧ t₁.gpr .r4 = p.D ∧ t₁.gpr .r5 = BitVec.ofNat 32 p.n ∧
      t₁.z = decide (p.n = 0) ∧ Others [.r1, .r4, .r5] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by srun [E.sp, a₄, a₈, A.a4, A.a8], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
      rw [z_cmp hn (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  obtain r0₁ : t₁.gpr .r0 = t.gpr .r0 := ho₁ _ (by decide)
  refine WP.ite (decide (p.n = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n = 0 := by simpa using ht
    refine WP.block_nil ⟨E₁, r0₁, by rw [hm₁]; exact Frame.refl _ _, ?_⟩
    rw [h0]; split <;> simp [bytesAt, Spec.GcmSiv.zeros]
  · have h0 : p.n ≠ 0 := by simpa using hf
    refine WP.mono (maskLoop_ok t₁ r4₁ r5₁ (by omega_arith) hn L.dw E₁.perm.d) fun t₂ ⟨hm₂, ho₂, sp₂, rd₂, wr₂⟩ => ?_
    obtain hl : (maskBytes t₁.mem (State.addr p.D) ((t₁.gpr .r1).setWidth 8) p.n).length = p.n := by
      simp [maskBytes, length_bytesAt]
    refine ⟨E₁.of_others ho₂ sp₂ rd₂ wr₂, by rw [ho₂ _ (by decide), r0₁],
      by rw [hm₂, ← hm₁]; exact Proof.AesGcm.Arm.writeBytes_frame' _ hl, ?_⟩
    obtain e := Proof.AesGcm.Arm.bytesAt_writeBytes_self t₁.mem (State.addr p.D)
      (maskBytes t₁.mem (State.addr p.D) ((t₁.gpr .r1).setWidth 8) p.n) (by omega_arith)
    rw [hl] at e
    rw [hm₂, e, r1₁, hok, hm₁]
    simp only [maskBytes]
    split
    · exact map_and_ff _
    · rw [map_and_zero, length_bytesAt]

end VG.Proof.AesGcmSiv.Arm

/-!
## The arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`),
what the state may access (`args_of_seal`, `args_of_open`) and the stack
arguments (`args_of`). `recv` and `tagOut` copy the tag, whose address they
read from the stack (`recv_ok`, `tagOut_ok`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, and keeps the arguments in `r7`–`r11` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (arg args bel covers_of_mem covers_left covers_prefix SavedAt savedR argAddr_zero stackArg_eq
  in_off add_ofNat_zero mem_store)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .r0
  W := arg s 4
  N := s.gpr .r2
  A := s.gpr .r3
  D := arg s 1
  T := arg s 3
  SP := s.sp
  R := (s.gpr .r1).toNat
  al := (arg s 0).toNat
  n := (arg s 2).toNat

theorem args_eq (s : State) : args s 5 = argR s.sp := by
  simp only [args, argAddr_zero]

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  sig_split h
  rename_i sd sw nd nw ad aw td tw dw da wa bs bn ba bd bt bw fK fN fA fD fT fW sp8 spf
  have hR := h
  clear h
  rw [args_eq] at da wa
  exact ⟨fK, fW, fN, fA, fD, BitVec.isLt _, BitVec.isLt _, sp8, spf, fT, sw, sd, nw, nd, aw, ad, dw, tw, td, da, wa,
    bs, bn, ba, bd, bw, hR⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨State.addr (s.gpr .r0), 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨State.addr (s.gpr .r2), 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨State.addr (arg s 1), (arg s 2).toNat⟩] s.wr) (hW : Covers [⟨State.addr (arg s 4), 3760⟩] s.wr)
    (ha : Covers [args s 5] (s.rd ++ s.wr)) (hT : Covers [⟨State.addr (arg s 3), 16⟩] (s.rd ++ s.wr))
    (hw : ∀ r ∈ s.wr, (args s 5).Disjoint r) : Perm (prmOf s) s := by
  rw [args_eq] at ha hw
  exact ⟨hk, hN, hA, hD, hW, ha, hw, hT⟩

/-- `seal`'s layout and permissions, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [⟨State.addr (arg s 3), 16⟩] s.wr := by
  obtain ⟨hrd, hwr, ta, hl⟩ := h
  obtain mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  obtain mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 3), 16⟩,
      ⟨State.addr (arg s 4), 3760⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (covers_left (mwr _ (by simp))) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact da.symm
      · exact ta.symm
      · exact wa.symm), mwr _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) : Lay (prmOf s) ∧ Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  obtain mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, ⟨State.addr (arg s 3), 16⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  obtain mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 4), 3760⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact da.symm
      · exact wa.symm)⟩

theorem args_of (s : State) : Args (prmOf s) s.mem :=
  ⟨by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq],
    by simp [prmOf, arg, stackArg_eq]⟩

/-- What the entry leaves. -/
structure Entered (s s₁ : State) : Prop where
  env : Env (prmOf s) s₁
  saved : SavedAt s₁.mem (prmOf s).W s
  frame : Frame [savedR (prmOf s).W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- `entry`. -/
theorem entry_ok {s : State} (L : Lay (prmOf s)) (P : Perm (prmOf s) s) : WP isa (.block entry) s (Entered s) := by
  have hw := L.ww
  obtain ha : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4 := P.argR' L (k := 16) (by decide)
  obtain e16 : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = (prmOf s).W := by simp [prmOf, arg, stackArg_eq]
  refine Proof.AesGcm.Arm.entry_ok (off := 16) (by decide) ha (by rw [e16]; omega_arith)
    (by rw [e16]; exact P.w2560) fun s₁ g16 g rd wr sp sv fr => ?_
  rw [e16] at g16 sv fr
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by simp only [sp_setReg]; rw [sp]; rfl,
    P.of_eq (by simp only [rd_setReg]; exact rd) (by simp only [wr_setReg]; exact wr)⟩, by simpa [mem_setReg] using sv,
    by simpa [mem_setReg] using fr, by simp only [rd_setReg]; exact rd, by simp only [wr_setReg]; exact wr⟩
  all_goals simp [gpr_setReg, g, g16, prmOf]

/-! ## The tag's copies -/

/-- `tag`'s address, read from the stack. -/
theorem tagArg {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 12)) 32 = p.T ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 12)) 4 := by
  rw [E.sp]; exact ⟨A.a12, E.perm.argR' L (k := 12) (by decide)⟩

/-- A 16-byte block copied by words, all loaded first. -/
theorem bytesAt_copy4 (m : Mem) (S T : Addr) :
    bytesAt (Proof.Cmac.store4 m T (m.readW S 32) (m.readW (S + BitVec.ofNat 64 4) 32)
      (m.readW (S + BitVec.ofNat 64 8) 32) (m.readW (S + BitVec.ofNat 64 12) 32)) T 16 = bytesAt m S 16 := by
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨State.addr p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.T) 16 ∧
      Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := tagArg L E A
  have tw := L.tw
  obtain eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega_arith)
  obtain t₀ : InRegions (s.rd ++ s.wr) (State.addr p.T) 4 := by
    simpa using in_off (d := 0) (n := 4) E.perm.t (by decide) (by decide)
  obtain t₁ := in_off (d := 4) (n := 4) E.perm.t (by decide) (by decide)
  obtain t₂ := in_off (d := 8) (n := 4) E.perm.t (by decide) (by decide)
  obtain t₃ := in_off (d := 12) (n := 4) E.perm.t (by decide) (by decide)
  obtain w₀ : InRegions s.wr (State.addr p.W) 4 := by simpa using E.perm.wW (show 0 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wW (show 4 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wW (show 8 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wW (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [recv]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact bytesAt_copy4 _ _ _

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem)
    (hTw : Covers [⟨State.addr p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨State.addr p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.T) 16 = bytesAt s.mem (State.addr p.W) 16 ∧
      Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := tagArg L E A
  have tw := L.tw
  obtain eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega_arith)
  obtain t₀ : InRegions s.wr (State.addr p.T) 4 := by simpa using in_off (d := 0) (n := 4) hTw (by decide) (by decide)
  obtain t₁ := in_off (d := 4) (n := 4) hTw (by decide) (by decide)
  obtain t₂ := in_off (d := 8) (n := 4) hTw (by decide) (by decide)
  obtain t₃ := in_off (d := 12) (n := 4) hTw (by decide) (by decide)
  obtain w₀ : InRegions (s.rd ++ s.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [tagOut]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact bytesAt_copy4 _ _ _

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, the stack below `SP`, or the key schedule. -/
tactic_template "disj_tac" L:term : tactic => `(tactic| (
                   simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
                   repeat' apply And.intro
                   all_goals first
                     | (with_reducible refine Lay.w_w $L (.inl ?_) ?_ ?_) <;> decide
                     | (with_reducible refine Lay.w_w $L (.inr ?_) ?_ ?_) <;> decide
                     | (with_reducible refine Lay.d_w' $L ?_) <;> decide
                     | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide
                     | (with_reducible refine Lay.k_w' $L ?_) <;> decide
                     | (with_reducible refine Lay.n_w' $L ?_) <;> decide
                     | (with_reducible refine Lay.a_w' $L ?_) <;> decide
                     | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
                     | (with_reducible refine Lay.args_w' $L ?_) <;> decide
                     | with_reducible exact Lay.k_d $L
                     | with_reducible exact Lay.n_d $L
                     | with_reducible exact Lay.a_d $L
                     | (with_reducible refine Lay.t_w' $L ?_) <;> decide
                     | with_reducible exact Lay.t_d $L
                     | with_reducible exact (Lay.t_d $L).symm
                     | with_reducible exact (Lay.d_w $L).symm
                     | with_reducible exact (Lay.bk $L).symm
                     | with_reducible exact (Lay.bn $L).symm
                     | with_reducible exact (Lay.ba $L).symm
                     | with_reducible exact (Lay.bd $L).symm
                     | with_reducible exact Lay.args_below $L
                     | with_reducible exact (Lay.d_args $L).symm))

end VG.Proof.AesGcmSiv.Arm

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, and
the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR restore_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.Arm.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega_arith)]

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : Prm} (L : Lay p) {s₀ t : State} (E : Env p t) (hsp : p.SP = s₀.sp)
    (hs : SavedAt t.mem p.W s₀) :
    WP isa (.block Impl.AesGcm.Arm.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .r0 = t.gpr .r0 :=
  WP.mono (restore_ok E.r11 (by have := L.ww; omega_arith) (covers_left (covers_prefix E.perm.w (by decide))) hs
    (by rw [E.sp, hsp])) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩
where
  covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := Proof.AesGcm.Arm.covers_left h
  covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
      Covers [⟨p, n⟩] rs := Proof.AesGcm.Arm.covers_prefix h hn

/-- A run, which keeps the permissions. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨t, s', e, hq, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp [VG.Proof.Gcm.Arm.GhashLaw] (hti : TagInputEq) {s : State} (h : sealPre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' := by
  obtain ⟨L, P, hTw⟩ := args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  obtain A₀ := args_of s
  refine WP.seq (WP.mono (WP.rdwr (entry_ok L P)) fun s₁ ⟨En, _, w₁⟩ => ?_)
  obtain A₁ : Args (prmOf s) s₁.mem := A₀.frame L En.frame (by disj_tac L)
  -- The keys.
  refine WP.seq (WP.mono (WP.rdwr (keys_ok L En.env)) fun s₂ ⟨Ky, _, w₂⟩ => ?_)
  obtain A₂ : Args (prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok L Ky.env A₂ Ky.hkey Ky.acc) fun s₃ Po => ?_)
  obtain A₃ : Args (prmOf s) s₃.mem := A₂.frame L Po.frame (by disj_tac L)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  obtain A₄ : Args (prmOf s) s₄.mem := A₃.frame L Tg.frame (by disj_tac L)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok L Tg.env A₄) fun s₅ Cr => ?_)
  obtain A₅ : Args (prmOf s) s₅.mem := A₄.frame L Cr.frame (by disj_tac L)
  -- The copy of the tag, and `restore`.
  obtain w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, w₂, w₁]
  obtain ⟨s₆, run₆, fT, hT₆, ho₆, sp₆, rd₆, wr₆⟩ := tagOut_ok L Cr.env A₅ (by rw [w₅]; exact hTw)
  obtain E₆ : Env (prmOf s) s₆ := Cr.env.of_others ho₆ sp₆ rd₆ wr₆
  obtain sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (((((En.saved.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame
      (by disj_tac L)).frame Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 36 ≤ 3760 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (exit_ok L E₆ rfl sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
      (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12)
      (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al) =
    (bytesAt s'.mem (State.addr (prmOf s).D) (prmOf s).n, bytesAt s'.mem (State.addr (prmOf s).T) 16)
  rw [hm, hT₆, bytesAt_keep fT (by disj_tac L) (by omega_arith)]
  -- What the pieces read.
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (prmOf s).K) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R :=
    ciph_keep En.frame (by disj_tac L) hRb
  obtain n₁ : bytesAt s₁.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 :=
    bytesAt_keep En.frame (by disj_tac L) (by decide)
  obtain n₂ : bytesAt s₂.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  obtain a₂ : bytesAt s₂.mem (State.addr (prmOf s).A) (prmOf s).al = bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega_arith),
      bytesAt_keep En.frame (by disj_tac L) (by have := L.al_lt; omega_arith)]
  obtain d₂ : bytesAt s₂.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega_arith), bytesAt_keep En.frame (by disj_tac L) (by omega_arith)]
  obtain d₄ : bytesAt s₄.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by omega_arith), bytesAt_keep Po.frame (by disj_tac L) (by omega_arith), d₂]
  obtain key₃ : Spec.GcmSiv.ctxCiph s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  obtain key₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R := by
    rw [ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  obtain t₅ : bytesAt s₅.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  rw [BitVec.add_zero] at t₅
  have tg := Tg.out
  rw [BitVec.add_zero] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.Arm

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 176`, the comparison, the mask and the restore
compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

theorem ite_ofNat (c : Prop) [Decidable c] :
    (if c then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (if c then 1 else 0) := by
  split <;> rfl

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp [VG.Proof.Gcm.Arm.GhashLaw] (hti : TagInputEq) {s : State} (h : openPre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' := by
  obtain ⟨L, P⟩ := args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  obtain A₀ := args_of s
  refine WP.seq (WP.mono (entry_ok L P) fun s₀ En₀ => ?_)
  obtain A₀' : Args (prmOf s) s₀.mem := A₀.frame L En₀.frame (by disj_tac L)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, ho₁, sp₁, rd₁, wr₁⟩ := recv_ok L En₀.env A₀'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain fR' : Frame [⟨State.addr (prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by
    rw [BitVec.add_zero]; exact fR
  obtain E₁ : Env (prmOf s) s₁ := En₀.env.of_others ho₁ sp₁ rd₁ wr₁
  obtain sv₁ : SavedAt s₁.mem (prmOf s).W s := En₀.saved.frame fR' (by disj_tac L)
  obtain f₁ : Frame [savedR (prmOf s).W, ⟨State.addr (prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (En₀.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  obtain A₁ : Args (prmOf s) s₁.mem := A₀'.frame L fR' (by disj_tac L)
  obtain hT₁ : bytesAt s₁.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [BitVec.add_zero, hR₁, bytesAt_keep En₀.frame (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (keys_ok L E₁) fun s₂ Ky => ?_)
  obtain A₂ : Args (prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok L Ky.env A₂) fun s₃ Cr => ?_)
  obtain A₃ : Args (prmOf s) s₃.mem := A₂.frame L Cr.frame (by disj_tac L)
  obtain a₃ : bytesAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16 =
      bytesAt s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  obtain hG₃ : Spec.Gcm.blockAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.hkey, a₃]
  obtain hY₃ : Spec.Gcm.blockAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok L Cr.env A₃ hG₃ hY₃) fun s₄ Po => ?_)
  obtain A₄ : Args (prmOf s) s₄.mem := A₃.frame L Po.frame (by disj_tac L)
  -- Its tag at `W + 176`.
  refine WP.seq (WP.mono (tag_ok L Po.env (o := 176) (by decide)) fun s₅ Tg => ?_)
  obtain A₅ : Args (prmOf s) s₅.mem := A₄.frame L Tg.frame (by disj_tac L)
  -- The comparison.
  obtain ⟨s₆, run₆, r0₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env (prmOf s) s₆ := Tg.env.of_others ho₆ sp₆ rd₆ wr₆
  rw [ite_ofNat] at r0₆
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ (hm₆ ▸ A₅) r0₆) fun s₇ Mk => ?_)
  -- The restore.
  obtain sv₇ : SavedAt s₇.mem (prmOf s).W s := by
    have := ((((sv₁.frame Ky.frame (by disj_tac L)).frame Cr.frame (by disj_tac L)).frame Po.frame
      (by disj_tac L)).frame Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok L Mk.env rfl sv₇) fun s' ⟨ga, hm, hr0⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (prmOf s).K) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  obtain n₁ : bytesAt s₁.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 :=
    bytesAt_keep f₁ (by disj_tac L) (by decide)
  obtain n₃ : bytesAt s₃.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by decide), bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  obtain a₃' : bytesAt s₃.mem (State.addr (prmOf s).A) (prmOf s).al =
      bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by have := L.al_lt; omega_arith),
      bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega_arith),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega_arith)]
  obtain d₂ : bytesAt s₂.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega_arith), bytesAt_keep f₁ (by disj_tac L) (by omega_arith)]
  obtain tag₂ : bytesAt s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), hT₁]
  obtain tag₅ : bytesAt s₅.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by decide), bytesAt_keep Po.frame (by disj_tac L) (by decide),
      bytesAt_keep Cr.frame (by disj_tac L) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  obtain ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R := by
    rw [ciph_keep Po.frame (by disj_tac L) hRb, ciph_cryR L Cr.frame]
  obtain d₆ : bytesAt s₆.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s₃.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [hm₆, bytesAt_keep Tg.frame (by disj_tac L) (by omega_arith), bytesAt_keep Po.frame (by disj_tac L) (by omega_arith)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.data
  rw [hm₆, tg, tag₅] at md
  rw [← hm₆, d₆, pt₃] at md
  obtain ax : s'.gpr .r0 = s₆.gpr .r0 := by rw [hr0, Mk.r0]
  rw [r0₆, tg, tag₅] at ax
  show openPost (openResult s) s' (State.addr (prmOf s).D) (prmOf s).n
  obtain hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
            (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) =
          bytesAt s.mem (State.addr (prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
          (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
        (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) =
      bytesAt s.mem (State.addr (prmOf s).T) 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (State.addr (prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (State.addr (prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
          (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) :=
      Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.Arm
