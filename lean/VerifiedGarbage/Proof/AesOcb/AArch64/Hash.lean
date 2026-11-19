module

public import VerifiedGarbage.Proof.AesOcb.AArch64.LNtz
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesOcb.AArch64.Env
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesOcb.AArch64.Args

/-! ### `AesOcb.AArch64.HashChunk`, which this module and modules that import it used -/

section

/-! ### `AesOcb.AArch64.HashFill`, which only this module used -/

section

/-!
# AES-OCB on AArch64: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xor16_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x23, .x25, .x27]

/-- What one `hashFill` leaves. -/
structure FillPost (W A : Addr) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
    blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  x23 : t'.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i + 1))
  x25 : t'.gpr .x25 = BitVec.ofNat 64 (j + i + 2)
  x27 : t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * (i + 1))
  x15 : t'.gpr .x15 = BitVec.ofNat 64 (c - (i + 1))
  gpr : ∀ r, r ∉ fillRegs → t'.gpr r = t.gpr r
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {T : Nat} {K W : Addr} (L : Lay T K W) {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] t.wr)
    {A : Addr} {l : Block} {j i c : Nat} (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 61)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 (j + i + 1)) (h23 : t.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i)))
    (h27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i)) (h15 : t.gpr .x15 = BitVec.ofNat 64 (c - i))
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr))
    (hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, T⟩) :
    WP isa hashFill t (FillPost W A l j i c t) := by
  obtain hT := L.hT
  unfold hashFill
  refine WP.seq (WP.mono (lNtz_ok (i := j + i + 1) h19 hw (by omega_using []) (by omega_using [hj]) h25 hl0) fun t₁ P₁ => ?_)
  obtain h19₁ : t₁.gpr .x19 = W := by rw [P₁.gpr _ (by decide), h19]
  obtain ww : ∀ {d : Nat}, d + 8 ≤ 512 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [P₁.wr]; exact in_off hw h (by decide)
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .x19) (a := lO) (d := ohO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (in_left (ww (by decide))) (in_left (ww (by decide)))
    (ww (by decide)) (ww (by decide))
  obtain oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [B₂.val, P₁.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)), hoh]
    rfl
  obtain g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      P₁.gpr r hr]
  obtain h23₂ : t₂.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i)) := by rw [g₂ _ (by decide), h23]
  obtain h27₂ : t₂.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i) := by rw [g₂ _ (by decide), h27]
  obtain h19₂ : t₂.gpr .x19 = W := by rw [g₂ _ (by decide), h19]
  obtain h25₂ : t₂.gpr .x25 = BitVec.ofNat 64 (j + i + 1) := by rw [g₂ _ (by decide), h25]
  obtain h15₂ : t₂.gpr .x15 = BitVec.ofNat 64 (c - i) := by rw [g₂ _ (by decide), h15]
  obtain rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  obtain wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  obtain fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  obtain eA : blockAtMem t₂.mem (A + BitVec.ofNat 64 (16 * (j + i))) = blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) :=
    blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hAW.sub_right (Lay.wSub (by have := ocbOffs; omega))
  obtain rA₀ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i))) 8 := by
    rw [rd₂, wr₂]; simpa using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  obtain rA₈ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i)) + BitVec.ofNat 64 8) 8 := by
    rw [rd₂, wr₂]; exact in_off (d := 8) (n := 8) hA (by decide) (by decide)
  obtain rO₀ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 144) 8 := by
    rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide))
  obtain rO₈ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 152) 8 := by
    rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide))
  obtain wS₀ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i)) 8 := by rw [wr₂]; exact in_off hw (by omega_using [hi, hc]) (by decide)
  obtain wS₈ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 8) 8 := by
    rw [wr₂, Offset.add_add]; exact in_off hw (by omega_using [hi, hc]) (by decide)
  refine WP.of_runBlock ⟨_, by rw [runBlock_append, run₂, Option.bind_some]; orun [h23₂, h27₂, h19₂, h25₂, h15₂,
    rA₀, rA₈, rO₀, rO₈, wS₀, wS₈], ?_⟩
  obtain fs : ∀ (M : Mem) (v₀ v₁ : BitVec 64), Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 (384 + 16 * i)) v₀).writeW (W + BitVec.ofNat 64 (384 + 16 * i) + 8#64) v₁) :=
    fun M v₀ v₁ => Proof.Cmac.frame_store2 _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ <;> try dsimp only
  · simp only [mem_write]
    exact (fr₂.mono (by simp)).trans ((fs _ _ _).mono (by simp))
  · simp only [mem_write]
    rw [blockAtMem_frame (fs _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 144) (n := 16) (d := 384 + 16 * i) (k := 16) (.inl (by omega_using [])) (by have := ocbOffs; omega) (by omega)), oh₂]
  · simp only [mem_write]
    rw [blockAtMem_store2, show W + 152#64 = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 from (addr8 W 144).symm,
      blockAtMem_xor_words, eA, show W + BitVec.ofNat 64 144 = W + BitVec.ofNat 64 ohO from rfl, oh₂]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h23₂, Offset.add_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega_using []]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h25₂, ← BitVec.ofNat_add]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, Offset.add_add]
    rw [show 384 + 16 * i + 16 = 384 + 16 * (i + 1) by omega_using []]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15₂]
    rw [Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  · simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2, ite_false]
    exact g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1])
  · simp only [sp_write]; rw [B₂.sp, P₁.sp]
  · simp only [rd_write]; exact rd₂
  · simp only [wr_write]; exact wr₂

end VG.Proof.AesOcb.AArch64

end

end


/-!
# AES-OCB on AArch64: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`x23` points at block `j`, `x25` is `j + 1` and `x26` is `m − j`.
`hashChunk` takes `c = min(8, m − j)` blocks (`chunkHead_ok`): fills the
buffer with each block XORed with its offset (`fill_ok`), enciphers the
buffer, adds it to the sum (`hashSum_ok`), and leaves `HInv` at `j + c`
(`hashChunk_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_zero eval_nonzero toNat_ofNat_of_lt)

/-- What `HASH` writes: the sum, `[96, 160)` (`L_{ntz(i)}`, the blocks of
one call and the offset), and the buffer and the working space of the
functions called. -/
abbrev hashR (T : Nat) (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 64⟩, ⟨W + BitVec.ofNat 64 384, T - 384⟩]

theorem hashR_mut {T : Nat} {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (hashR T W) m m')
    (hT : 384 ≤ T := by omega) :
    Frame (mutR T W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by have := ocbOffs; omega)

/-- What holds of `HASH` of `a` (at `A`) after `j` of its whole blocks, from
the state `s₀` at its start. -/
structure HInv (T : Nat) (K W D : Addr) (R n : Nat) (SP : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ s : State) (j : Nat) : Prop where
  env : Env T K W D R n SP s
  frame : Frame (hashR T W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ a.length / 16
  sum : blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l j
  x23 : s.gpr .x23 = A + BitVec.ofNat 64 (16 * j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (j + 1)
  x26 : s.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j)
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

/-- What a chunk of `HASH` needs of its start, `s₀`: the key context's
cipher and `L_*`, the associated data (apart from `W` and the data at `D`). -/
structure HCtx (T : Nat) (K W D : Addr) (n R : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) : Prop where
  lay : Lay T K W
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ciph : ctxCiph s₀.mem K R = ciph
  lstar : ctxLstar s₀.mem K = l
  buf : Buf T W s₀ A a.length
  aad : bytesAt s₀.mem A a.length = a
  ad : (⟨A, a.length⟩ : Region).Disjoint ⟨D, n⟩
  kd : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, T⟩

namespace HCtx

variable {T : Nat} {K W D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}
  (C : HCtx T K W D n R ciph l A a s₀)
include C

theorem short : a.length < 2 ^ 64 := C.buf.lt

/-- The associated data misses the parts the pieces write. -/
theorem a_mut : ∀ r ∈ mutR T W D n, (⟨A, a.length⟩ : Region).Disjoint r := by
  obtain hT := C.lay.hT
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact C.buf.w.sub_right (Region.sub_prefix (by have := ocbOffs; omega))
  · exact C.buf.w.sub_right (Lay.wSub (by have := ocbOffs; omega))
  · exact C.ad

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (mutR T W D n) s₀.mem m) {i : Nat} (hi : i < a.length / 16) :
    blockAtMem m (A + BitVec.ofNat 64 (16 * i)) = blockAt a i := by
  rw [← C.aad, Proof.Ocb.blockAt_bytesAt _ _ (by omega_arith), blockAtMem_frame h fun r hr =>
    (C.a_mut r hr).sub_left (Offset.sub_base A (by omega_arith))]

theorem ciph' {m : Mem} (h : Frame (mutR T W D n) s₀.mem m) : ctxCiph m K R = ciph := by
  rw [ctxCiph_mut C.lay C.kd h C.rounds, C.ciph]

theorem lstar' {m : Mem} (h : Frame (mutR T W D n) s₀.mem m) : ctxLstar m K = l := by
  rw [ctxLstar_mut C.lay C.kd h, C.lstar]

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (T : Nat) (K W D : Addr) (R n : Nat) (SP : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env T K W D R n SP t
  frame : Frame (hashR T W) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  x23 : t.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i))
  x25 : t.gpr .x25 = BitVec.ofNat 64 (j + i + 1)
  x27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i)
  x15 : t.gpr .x15 = BitVec.ofNat 64 (c - i)
  x24 : t.gpr .x24 = BitVec.ofNat 64 c
  x26 : t.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j)
  oh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) {j c : Nat} (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    {t : State} {i : Nat} (hi : i < c) (F : FillInv T K W D R n SP ciph l A a s₀ j c t i) :
    WP isa hashFill t fun t' => FillInv T K W D R n SP ciph l A a s₀ j c t' (i + 1) := by
  obtain hT := C.lay.hT
  have L := C.lay
  have hs := C.short
  obtain hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr) := by
    rw [F.rd, F.wr]; exact (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega_arith)).rd
  obtain hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, T⟩ :=
    (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega_arith)).w
  refine WP.mono (hashFill_ok L F.env.x19 (F.env.perm.w5 L) hi hc (by omega_arith) F.x25 F.x23 F.x27 F.x15 F.l0 F.oh hA hAW)
    fun t' P => ?_
  obtain hfr : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩], ∃ r' ∈ hashR T W, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        Offset.sub W (by omega_arith) (by omega_arith)⟩
  obtain keepB : ∀ {d : Nat}, (d + 16 ≤ 96 ∨ (112 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 384 + 16 * i) ∨
      384 + 16 * (i + 1) ≤ d) → d + 16 ≤ T →
      blockAtMem t'.mem (W + BitVec.ofNat 64 d) = blockAtMem t.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega_arith) h₂ (by have := ocbOffs; omega)
      · exact L.w_w (a := _) (d := 144) (k := 16) (by omega_arith) h₂ (by have := ocbOffs; omega)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega_arith) h₂ (by omega_arith)
  obtain hg : ∀ r ∈ envRegs, t'.gpr r = t.gpr r := fun r hr => P.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine
    { env := F.env.keep hg P.sp P.rd P.wr
      frame := F.frame.trans (P.frame.sub hfr)
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      x23 := by rw [P.x23, show j + i + 1 = j + (i + 1) by omega_arith]
      x25 := by rw [P.x25, show j + i + 2 = j + (i + 1) + 1 by omega_arith]
      x27 := P.x27
      x15 := P.x15
      x24 := by rw [P.gpr _ (by decide), F.x24]
      x26 := by rw [P.gpr _ (by decide), F.x26]
      oh := by rw [P.oh]; rfl
      buf := fun k hk => ?_
      sum := by rw [keepB (by simp only [sumO]; omega_arith) (by have := ocbOffs; omega), F.sum]
      l0 := by rw [keepB (by simp only [l0O]; omega_arith) (by have := ocbOffs; omega), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by omega_arith) (by omega_arith), F.buf k hk']
  · obtain rfl : k = i := by omega_arith
    rw [P.buf, C.blk (hashR_mut F.frame) (by omega_arith)]

theorem fill_ok {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8)
    (hjc : j + c ≤ a.length / 16) {t : State} (F : FillInv T K W D R n SP ciph l A a s₀ j c t 0) :
    WP isa (.loop hashFill (.nonzero .x .x15)) t fun t' => FillInv T K W D R n SP ciph l A a s₀ j c t' c := by
  obtain hT := C.lay.hT
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ FillInv T K W D R n SP ciph l A a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (fill_step C hc hjc hi F) fun u' F' => ?_
  obtain ev := eval_nonzero F'.x15 (by omega_arith)
  by_cases he : i + 1 = c
  · left; exact ⟨ev.trans (by simp; omega_arith), he ▸ F'⟩
  · right; exact ⟨ev.trans (by simp; omega_arith), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, F'⟩

/-! ## Adding the buffer to the sum -/

theorem bufStart_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) {c : Nat} (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ∃ t', runBlock isa bufStart t = some t' ∧ t'.gpr .x15 = BitVec.ofNat 64 (c - 0) ∧
      t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * 0) ∧
      (∀ r, r ≠ .x15 → r ≠ .x27 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  refine ⟨_, by orun [bufStart, h19], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h24]
  · simp [gpr_write, h19]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

/-- The sum loop after `k` of the `c` blocks of the buffer. -/
theorem sumStep_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] t.wr) {k c : Nat}
    (hk : k < c) (hc : c ≤ 8) (h27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * k))
    (h15 : t.gpr .x15 = BitVec.ofNat 64 (c - k)) :
    ∃ t', runBlock isa (xor16 .x27 0 sumO ++ [Impl.AesGcm.AArch64.ptr .x27 .x27 16, .subImm .x .x15 .x15 1]) t =
        some t' ∧
      BlkStep W sumO (blockAtMem t.mem (W + BitVec.ofNat 64 sumO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k))) [.x9, .x10, .x11, .x12, .x15, .x27] t t' ∧
      t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * (k + 1)) ∧ t'.gpr .x15 = BitVec.ofNat 64 (c - (k + 1)) := by
  obtain e0 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * k) :=
    BitVec.add_zero _
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .x27) (a := 0) (d := sumO) (by decide) (by decide) h19 h27
    (by decide) (by decide) (by decide) (by rw [e0]; exact in_left (in_off hw (by omega_arith) (by decide)))
    (by rw [Offset.add_add]; exact in_left (in_off hw (by omega_arith) (by decide)))
    (in_off hw (by decide) (by decide)) (in_off hw (by decide) (by decide))
  rw [e0] at B₁
  obtain h27₁ : t₁.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * k) := by rw [B₁.gpr _ (by decide), h27]
  obtain h15₁ : t₁.gpr .x15 = BitVec.ofNat 64 (c - k) := by rw [B₁.gpr _ (by decide), h15]
  refine ⟨_, by rw [runBlock_append, run₁, Option.bind_some]; orun [h27₁, h15₁], ?_, ?_, ?_⟩
  · refine ⟨B₁.frame, B₁.val, fun r hr => ?_, B₁.sp, B₁.rd, B₁.wr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    exact B₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₁, Offset.add_add]
    rw [show 384 + 16 * k + 16 = 384 + 16 * (k + 1) by omega_arith]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15₁]
    rw [Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]

theorem hashSum_ok {T : Nat} {K W : Addr} (L : Lay T K W) {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] t.wr)
    {c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (h24 : t.gpr .x24 = BitVec.ofNat 64 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  obtain hT := L.hT
  obtain ⟨t₁, run₁, x15₁, x27₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := bufStart_ok h19 h24
  unfold hashSum
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧
      u.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i) ∧ u.gpr .x15 = BitVec.ofNat 64 (c - i) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → u.gpr r = t.gpr r) ∧ u.sp = t.sp ∧ u.rd = t.rd ∧
      u.wr = t.wr) ?_ (c - 0) _
    ⟨0, rfl, hc0, x27₁, x15₁, by rw [m₁]; exact Frame.refl _ _, by rw [m₁]; rfl, fun r hr => g₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2.2.2.1)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2.2.2.2), sp₁, rd₁,
      wr₁⟩
  rintro k u ⟨i, rfl, hi, x27, x15, fr, sum, gu, sp, rd, wr⟩
  obtain ⟨u', run', B, x27', x15'⟩ := sumStep_ok (by rw [gu _ (by decide), h19]) (by rw [wr]; exact hw) hi hc x27 x15
  refine WP.of_runBlock ⟨u', run', ?_⟩
  obtain hbuf : blockAtMem u.mem (W + BitVec.ofNat 64 (384 + 16 * i)) = g i := by
    rw [blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 384 + 16 * i) (n := 16) (d := 48) (k := 16) (.inr (by omega_arith)) (by omega_arith) (by have := ocbOffs; omega),
      hg i hi]
  obtain fr' : Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u'.mem := fr.trans B.frame
  obtain sum' : blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [B.val, sum, hbuf]; rfl
  obtain gu' : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → u'.gpr r = t.gpr r := fun r hr => by
    rw [B.gpr r hr, gu r hr]
  obtain ev := eval_nonzero x15' (by omega_arith)
  by_cases he : i + 1 = c
  · left
    exact ⟨ev.trans (by simp; omega_arith), fr', he ▸ sum', gu', by rw [B.sp, sp], by rw [B.rd, rd], by rw [B.wr, wr]⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, x27', x15', fr',
      sum', gu', by rw [B.sp, sp], by rw [B.rd, rd], by rw [B.wr, wr]⟩

/-! ## A chunk -/

/-- `x9 ← (x26 − 8) ⋙ 63`: 1 if fewer than 8 blocks are left. -/
theorem lt8 {L : Nat} (hL : L < 2 ^ 63) :
    (BitVec.ofNat 64 L - 8#64) >>> 63 = BitVec.ofNat 64 (if L < 8 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega_arith

/-- The number of blocks of a chunk: `x24 ← min(8, x26)`. -/
theorem chunkHead_ok {t : State} {L : Nat} (hL : L < 2 ^ 63) (h26 : t.gpr .x26 = BitVec.ofNat 64 L) :
    WP isa (.seq (.block [.subImm .x .x9 .x26 8, .lsr .x .x9 .x9 63, Impl.AesGcm.AArch64.mov .x24 .x26])
      (.ite (.zero .x .x9) (.block [Impl.AesGcm.AArch64.imm .x24 8]) (.block []))) t fun t' =>
      t'.gpr .x24 = BitVec.ofNat 64 (min 8 L) ∧ (∀ r, r ≠ .x9 → r ≠ .x24 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, x9₁, x24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.subImm .x .x9 .x26 8, .lsr .x .x9 .x9 63, Impl.AesGcm.AArch64.mov .x24 .x26] t = some t₁ ∧
      t₁.gpr .x9 = BitVec.ofNat 64 (if L < 8 then 1 else 0) ∧ t₁.gpr .x24 = BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x9 → r ≠ .x24 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by orun [h26], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h26, lt8 hL]
    · simp [gpr_write, h26]
    · simp [gpr_write, h1, h2]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  by_cases h8 : L < 8
  · simp only [h8, ↓reduceIte] at x9₁
    refine WP.ite false (by rw [eval_zero x9₁ (by decide)]; rfl) (fun h => by cases h) (fun _ => ?_)
    exact WP.block_nil ⟨by rw [x24₁, Nat.min_eq_right (by omega_arith)], g₁, m₁, sp₁, rd₁, wr₁⟩
  · simp only [h8, ↓reduceIte] at x9₁
    refine WP.ite true (by rw [eval_zero x9₁ (by decide)]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = t₁.write .x .x24 (BitVec.ofNat 64 8)) ⟨_, by orun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨by simp [gpr_write, Nat.min_eq_left (show 8 ≤ L by omega_arith)], fun r h1 h2 => ?_, m₁, sp₁, rd₁, wr₁⟩
    simp only [gpr_write, h2, ite_false]; exact g₁ r h1 h2

/-- The `c` blocks of the buffer. -/
theorem bufArgs_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) {c : Nat} (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ArgsOk [Impl.AesGcm.AArch64.ptr .x2 .x19 bufO, Impl.AesGcm.AArch64.mov .x3 .x24] t (W + BitVec.ofNat 64 384) c := by
  refine ⟨_, by orun [h19, h24], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19]
  · simp [gpr_write, h24]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- `bufStart`: the fill loop before its first block. -/
theorem bufStart_inv {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} {t : State} {j c : Nat}
    (H : HInv T K W D R n SP ciph l A a s₀ t j) (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ∃ t₁, runBlock isa bufStart t = some t₁ ∧ FillInv T K W D R n SP ciph l A a s₀ j c t₁ 0 := by
  obtain ⟨t₁, run₁, x15₁, x27₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := bufStart_ok H.env.x19 h24
  exact ⟨t₁, run₁,
    { env := H.env.others (rs := [.x15, .x27]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact g₁ r hr.1 hr.2) sp₁ rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      x23 := by rw [g₁ _ (by decide) (by decide), H.x23]; rfl
      x25 := by rw [g₁ _ (by decide) (by decide), H.x25]
      x27 := x27₁
      x15 := x15₁
      x24 := by rw [g₁ _ (by decide) (by decide), h24]
      x26 := by rw [g₁ _ (by decide) (by decide), H.x26]
      oh := by rw [m₁, H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [m₁, H.sum]
      l0 := by rw [m₁, H.l0] }⟩

/-- A chunk from `bufStart` on, with its `c` blocks in `x24`. -/
theorem chunkRest_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) {t : State} {j c : Nat}
    (H : HInv T K W D R n SP ciph l A a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 c)
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (.seq (.block bufStart) (.seq (.loop hashFill (.nonzero .x .x15))
        (.seq (callBlocks (callees v).enc [Impl.AesGcm.AArch64.ptr .x2 .x19 bufO, Impl.AesGcm.AArch64.mov .x3 .x24])
          (.seq hashSum (.block [.sub .x .x26 .x26 .x24]))))) t
      fun t' => HInv T K W D R n SP ciph l A a s₀ t' (j + c) := by
  obtain hT := C.lay.hT
  have L := C.lay
  have hs := C.short
  obtain ⟨t₁, run₁, F₀⟩ := bufStart_inv H h24
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOkW v.encNoFrames hv L F.env
    C.rounds (bufArgs_ok F.env.x19 F.x24) (dstW L F.env.perm (d := 384) (n := c) (by omega_arith)))
    fun t₃ P₃ => ?_)
  obtain E₃ := F.env.of_saved P₃.saved P₃.sp P₃.rd P₃.wr
  obtain F₃ : Frame (hashR T W) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := T - 384) (by decide) (by omega_arith)⟩
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := T - 384) (by decide) (by have := ocbOffs; omega)⟩
  obtain k₃ : ∀ {d : Nat}, d + 16 ≤ 384 → blockAtMem t₃.mem (W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (W + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by have := ocbOffs; omega)
  obtain hg : ∀ k < c, blockAtMem t₃.mem (W + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [Offset.add_add] at this
    rw [this, F.buf k hk]
    exact congrFun (C.ciph' (hashR_mut F.frame)) _
  obtain h24₃ : t₃.gpr .x24 = BitVec.ofNat 64 c := by rw [P₃.saved _ (by decide) (by decide), F.x24]
  refine WP.seq (WP.mono (hashSum_ok L E₃.x19 (E₃.perm.w5 L) hc0 hc h24₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
  obtain E₄ := E₃.others g₄ sp₄ rd₄ wr₄
  obtain k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ 64 ≤ d) → d + 16 ≤ T →
      blockAtMem t₄.mem (W + BitVec.ofNat 64 d) = blockAtMem t₃.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega_arith) h₂ (by have := ocbOffs; omega)
  obtain h24₄ : t₄.gpr .x24 = BitVec.ofNat 64 c := by rw [g₄ _ (by decide), h24₃]
  obtain h26₄ : t₄.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j) := by
    rw [g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x26]
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = t₄.write .x .x26 (t₄.gpr .x26 - t₄.gpr .x24)) ⟨_, by orun [], rfl⟩ fun t' ht' => ?_
  subst ht'
  refine
    { env := E₄.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl
      frame := F.frame.trans (F₃.trans (fr₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., fun _ h => h⟩))
      rd := by rw [rd_write, rd₄, P₃.rd, F.rd]
      wr := by rw [wr_write, wr₄, P₃.wr, F.wr]
      le := by omega_arith
      sum := by rw [mem_write, sum₄, k₃ (by decide), F.sum, hsum_add]
      oh := by rw [mem_write, k₄ (by simp only [ohO]; omega_arith) (by have := ocbOffs; omega), k₃ (by decide), F.oh]
      x23 := by
        rw [gpr_write_of_ne _ _ _ (by decide), g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x23]
      x25 := by
        rw [gpr_write_of_ne _ _ _ (by decide), g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x25]
      x26 := by
        rw [gpr_write_self, h26₄, h24₄, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
      l0 := by rw [mem_write, k₄ (by simp only [l0O]; omega_arith) (by have := ocbOffs; omega), k₃ (by decide), F.l0] }

/-- `HInv` after `chunkHead`, which writes only `x9` and `x24`. -/
theorem HInv.head {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} {t t₁ : State} {j : Nat}
    (H : HInv T K W D R n SP ciph l A a s₀ t j) (g₁ : ∀ r, r ≠ .x9 → r ≠ .x24 → t₁.gpr r = t.gpr r)
    (m₁ : t₁.mem = t.mem) (sp₁ : t₁.sp = t.sp) (rd₁ : t₁.rd = t.rd) (wr₁ : t₁.wr = t.wr) :
    HInv T K W D R n SP ciph l A a s₀ t₁ j :=
  { H with
    env := H.env.others (rs := [.x9, .x24]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact g₁ r hr.1 hr.2) sp₁ rd₁ wr₁
    frame := by rw [m₁]; exact H.frame
    rd := by rw [rd₁, H.rd]
    wr := by rw [wr₁, H.wr]
    sum := by rw [m₁, H.sum]
    oh := by rw [m₁, H.oh]
    x23 := by rw [g₁ _ (by decide) (by decide), H.x23]
    x25 := by rw [g₁ _ (by decide) (by decide), H.x25]
    x26 := by rw [g₁ _ (by decide) (by decide), H.x26]
    l0 := by rw [m₁, H.l0] }

theorem hashChunk_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) {t : State} {j : Nat}
    (H : HInv T K W D R n SP ciph l A a s₀ t j) (hj : j < a.length / 16)
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (hashChunk (callees v)) t fun t' =>
      HInv T K W D R n SP ciph l A a s₀ t' (j + min 8 (a.length / 16 - j)) := by
  obtain hT := C.lay.hT
  have hs := C.short
  unfold hashChunk
  refine WP.assoc (WP.seq (WP.mono (chunkHead_ok (L := a.length / 16 - j) (by omega_arith) H.x26)
    fun t₁ ⟨h24, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_))
  exact chunkRest_ok v C (H.head g₁ m₁ sp₁ rd₁ wr₁) (by omega_arith) (by omega_arith) (by omega_arith) h24

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, loads the associated data and its length from `W`, takes the whole
blocks a chunk at a time (`hashChunk_ok`), and the rest, padded, XORed with
`Offset_m ⊕ L_*` and enciphered (`hashRest_ok`): the sum is §4.1's
`HASH(K, A)` (`hash_ok`, `Proof.Ocb.hash_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_zero eval_nonzero toNat_ofNat_of_lt lsr_ofNat and15)

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) {t : State}
    (H : HInv T K W D R n SP ciph l A a s₀ t (a.length / 16)) (hr : 0 < a.length % 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 (a.length % 16))
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (hashRest (callees v)) t fun t' => Env T K W D R n SP t' ∧ Frame (hashR T W) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  obtain hT := C.lay.hT
  have L := C.lay
  have E := H.env
  have hs := C.short
  generalize hm : a.length / 16 = m at H
  obtain hrest : a.length - 16 * m = a.length % 16 := by omega_using [hm]
  -- `Offset_m ⊕ L_*`
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .x20) (a := 240) (d := ohO) (by decide) (by decide) E.x19 E.x20
    (by decide) (by decide) (by decide) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by have := ocbOffs; omega))
    (E.perm.wW (by have := ocbOffs; omega))
  obtain E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  obtain oh₁ : blockAtMem t₁.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [B₁.val, H.oh, ← C.lstar' (hashR_mut H.frame)]; rfl
  obtain fr₁ : Frame (hashR T W) s₀.mem t₁.mem := H.frame.trans (B₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩)
  -- `pad(A_*)`
  obtain hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega_using [hm])
  obtain hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  obtain hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by have := ocbOffs; omega))
  obtain hrestb : bytesAt t₁.mem (A + BitVec.ofNat 64 (16 * m)) (a.length % 16) = a.drop (16 * m) := by
    obtain hd := Proof.Ocb.bytesAt_drop s₀.mem A (a := 16 * m) (n := a.length) (by omega_using [hm])
    rw [C.aad, hrest] at hd
    rw [Proof.Cmac.bytesAt_frame (hashR_mut (D := D) (n := n) fr₁) (fun r hr =>
      (C.a_mut r hr).sub_left (Offset.sub_base A (by omega_using [hm]))) (by omega_using []), hd]
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (padTo_ok E₁.x19 (E₁.perm.w5 L) hr (by omega_using []) (by decide)
    (by rw [B₁.gpr _ (by decide), H.x23]) (by rw [B₁.gpr _ (by decide), h24]) hS hSD)
    fun t₂ ⟨fr₂, pad₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  rw [hrestb] at pad₂
  obtain E₂ := E₁.others g₂ sp₂ rd₂ wr₂
  obtain oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega), oh₁]
  -- XORed with the offset
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .x19) (a := ohO) (d := bufO) (by decide) (by decide) E₂.x19
    E₂.x19 (by decide) (by decide) (by decide) (E₂.perm.wR (by have := ocbOffs; omega)) (E₂.perm.wR (by have := ocbOffs; omega))
    (E₂.perm.wW (by have := ocbOffs; omega)) (E₂.perm.wW (by have := ocbOffs; omega))
  obtain E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  obtain buf₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 bufO) = pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l) := by
    rw [B₃.val, pad₂, oh₂]
  obtain fr₃ : Frame (hashR T W) s₀.mem t₃.mem := fr₁.trans ((fr₂.trans B₃.frame).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, Offset.sub W (e := 384) (k := T - 384) (by decide) (by have := ocbOffs; omega)⟩)
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOkW v.encNoFrames hv L E₃
    C.rounds (oneBlock_ok E₃.x19 bufO (by decide)) (dstW L E₃.perm (d := bufO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  obtain E₄ := E₃.of_saved P₄.saved P₄.sp P₄.rd P₄.wr
  obtain buf₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 bufO) = ciph (pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l)) := by
    rw [P₄.enc0, buf₃]
    exact congrFun (C.ciph' (hashR_mut fr₃)) _
  obtain fr₄ : Frame (hashR T W) s₀.mem t₄.mem := fr₃.trans (P₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := T - 384) (by decide) (by have := ocbOffs; omega)⟩
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := T - 384) (by decide) (by have := ocbOffs; omega)⟩)
  obtain kSum : ∀ {u u' : State}, Frame [⟨W + BitVec.ofNat 64 bufO, 16⟩] u.mem u'.mem →
      blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (W + BitVec.ofNat 64 sumO) := fun h =>
    blockAtMem_frame h fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)
  obtain sum₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)
      · exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)),
      kSum B₃.frame, kSum fr₂, blockAtMem_frame B₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)), H.sum]
  -- added to the sum
  obtain ⟨t₅, run₅, B₅⟩ := xor16_ok (s := t₄) (b := .x19) (a := bufO) (d := sumO) (by decide) (by decide) E₄.x19
    E₄.x19 (by decide) (by decide) (by decide) (E₄.perm.wR (by have := ocbOffs; omega)) (E₄.perm.wR (by have := ocbOffs; omega))
    (E₄.perm.wW (by have := ocbOffs; omega)) (E₄.perm.wW (by have := ocbOffs; omega))
  refine WP.of_runBlock ⟨t₅, run₅, E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr, fr₄.trans (B₅.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩), ?_,
    by rw [B₅.rd, P₄.rd, B₃.rd, rd₂, B₁.rd, H.rd], by rw [B₅.wr, P₄.wr, B₃.wr, wr₂, B₁.wr, H.wr]⟩
  rw [B₅.val, sum₄, buf₄, Proof.Ocb.hash_eq]
  obtain hlen : (a.drop (16 * m)).length = a.length % 16 := by simp; omega_using [hm]
  simp only [hlen, show a.length % 16 > 0 from hr, ↓reduceIte, hm]

/-- The first block of `hash`: the sum and the offset zeroed, the associated
data and its length loaded. -/
theorem hashHead1_ok {T : Nat} {K W : Addr} (L : Lay T K W) {s₀ : State} (h19 : s₀.gpr .x19 = W)
    (hw : Covers [⟨W, 512⟩] s₀.wr) {A : Addr} {al : Nat}
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al) :
    ∃ s, runBlock isa (zero16 sumO ++ zero16 ohO ++ [ld .x23 .x19 aadO, ld .x26 .x19 alenO]) s₀ = some s ∧
      s.gpr .x23 = A ∧ s.gpr .x26 = BitVec.ofNat 64 al ∧ (∀ r, r ∉ [.x9, .x23, .x26] → s.gpr r = s₀.gpr r) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] s₀.mem s.mem ∧
      blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = 0 ∧ blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = 0 ∧
      s.sp = s₀.sp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain hT := L.hT
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s₀) (d := sumO) (by decide) h19 (in_off hw (by decide) (by decide))
    (in_off hw (by decide) (by decide))
  obtain h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
  obtain ⟨s₂, run₂, B₂⟩ := zero16_ok (s := s₁) (d := ohO) (by decide) h19₁ (by rw [B₁.wr]; exact in_off hw (by decide) (by decide))
    (by rw [B₁.wr]; exact in_off hw (by decide) (by decide))
  obtain h19₂ : s₂.gpr .x19 = W := by rw [B₂.gpr _ (by decide), h19₁]
  obtain kA : ∀ {d : Nat}, (d + 8 ≤ 48 ∨ (64 ≤ d ∧ d + 8 ≤ 144) ∨ 160 ≤ d) → d + 8 ≤ T →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₀.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [B₂.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 144) (k := 16) (by omega_using [h₁]) h₂ (by have := ocbOffs; omega)) (by decide),
      B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 48) (k := 16) (by omega_using [h₁]) h₂ (by have := ocbOffs; omega)) (by decide)]
  obtain haad₂ := (kA (d := aadO) (by decide) (by have := ocbOffs; omega)).trans haad
  obtain halen₂ := (kA (d := alenO) (by decide) (by have := ocbOffs; omega)).trans halen
  obtain r₁ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 aadO) 8 := by
    rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (in_off hw (by decide) (by decide))
  obtain r₂ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 alenO) 8 := by
    rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (in_off hw (by decide) (by decide))
  simp only [aadO, alenO] at haad₂ halen₂ r₁ r₂
  refine ⟨_, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]; orun [h19₂,
    r₁, r₂], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, haad₂]
  · simp [gpr_write, halen₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.2.1, hr.2.2, ite_false]
    rw [B₂.gpr r (by simp [hr.1]), B₁.gpr r (by simp [hr.1])]
  · exact (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  · simp only [mem_write]
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)), B₁.val]
  · simp only [mem_write]; exact B₂.val
  · simp only [sp_write]; rw [B₂.sp, B₁.sp]
  · simp only [rd_write]; rw [B₂.rd, B₁.rd]
  · simp only [wr_write]; rw [B₂.wr, B₁.wr]

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W`: `HInv` at 0. -/
theorem hashHead_ok {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) (E : Env T K W D R n SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.seq (.block (zero16 sumO ++ zero16 ohO ++ [ld .x23 .x19 aadO, ld .x26 .x19 alenO]))
      (.block [.lsr .x .x26 .x26 4, Impl.AesGcm.AArch64.imm .x25 1])) s₀ fun s =>
      HInv T K W D R n SP ciph l A a s₀ s 0 := by
  obtain hT := C.lay.hT
  have L := C.lay
  have hs := C.short
  obtain ⟨s₁, run₁, x23₁, x26₁, g₁, f₁, sum₁, oh₁, sp₁, rd₁, wr₁⟩ := hashHead1_ok L E.x19 (E.perm.w5 L) haad halen
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine Proof.AesGcm.AArch64.WP.run (Q := fun s => s = (s₁.write .x .x26 (s₁.gpr .x26 >>> 4)).write .x .x25
    (BitVec.ofNat 64 1)) ⟨_, by orun [], rfl⟩ fun s hs' => ?_
  subst hs'
  refine
    { env := E.others (rs := [.x9, .x23, .x25, .x26]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [gpr_write, hr.2.2.1, hr.2.2.2, ite_false]; exact g₁ r (by simp [hr.1, hr.2.1, hr.2.2.2]))
        (by simp only [sp_write]; exact sp₁) (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)
      frame := by
        simp only [mem_write]
        exact f₁.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
      rd := by simp only [rd_write]; exact rd₁
      wr := by simp only [wr_write]; exact wr₁
      le := Nat.zero_le _
      sum := by simp only [mem_write]; rw [sum₁]; rfl
      oh := by simp only [mem_write]; rw [oh₁]; rfl
      x23 := by simp [gpr_write, x23₁]
      x25 := by simp [gpr_write]
      x26 := by simp [gpr_write, x26₁, lsr_ofNat _ _ hs]
      l0 := by
        simp only [mem_write]
        rw [blockAtMem_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact L.w_w (.inr (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)
          · exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)), hl0] }

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) {t : State}
    (H₀ : HInv T K W D R n SP ciph l A a s₀ t 0) (hm : 0 < a.length / 16)
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (.loop (hashChunk (callees v)) (.nonzero .x .x26)) t fun u =>
      HInv T K W D R n SP ciph l A a s₀ u (a.length / 16) := by
  obtain hT := C.lay.hT
  have hs := C.short
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ j, k = a.length / 16 - j ∧ j < a.length / 16 ∧
      HInv T K W D R n SP ciph l A a s₀ u j) ?_ (a.length / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (hashChunk_ok v C H hj) fun u' H' => ?_
  obtain ev := eval_nonzero H'.x26 (by omega_using [hs])
  by_cases he : a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0
  · left
    obtain hje : j + min 8 (a.length / 16 - j) = a.length / 16 := by omega_using [hj, he]
    exact ⟨ev.trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨ev.trans (by simp [he]), a.length / 16 - (j + min 8 (a.length / 16 - j)), by omega_using [hj],
      j + min 8 (a.length / 16 - j), rfl, by omega_using [he], H'⟩

/-- The length of the rest of the associated data. -/
theorem tailHead_ok {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) {t : State}
    (H : HInv T K W D R n SP ciph l A a s₀ t (a.length / 16)) :
    WP isa (.block [ld .x24 .x19 alenO, Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x24 .x10]) t
      fun t₁ => HInv T K W D R n SP ciph l A a s₀ t₁ (a.length / 16) ∧
        t₁.gpr .x24 = BitVec.ofNat 64 (a.length % 16) := by
  obtain hT := C.lay.hT
  have hs := C.short
  obtain r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 alenO) 8 := H.env.perm.wR (by have := ocbOffs; omega)
  obtain al : t.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length := by
    rw [kept_read C.lay C.dw (hashR_mut H.frame) (by decide), halen]
  simp only [alenO] at r₁ al
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t₁ => t₁ = ((t.write .x .x24 (BitVec.ofNat 64 a.length)).write .x .x10
    (BitVec.ofNat 64 15)).write .x .x24 (BitVec.ofNat 64 a.length &&& BitVec.ofNat 64 15))
    ⟨_, by orun [H.env.x19, r₁, al], rfl⟩ fun t₁ ht₁ => ?_
  subst ht₁
  refine ⟨{ H with
      env := H.env.others (rs := [.x10, .x24]) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr.1, hr.2])
        rfl rfl rfl
      frame := H.frame
      x23 := by simp [gpr_write, H.x23]
      x25 := by simp [gpr_write, H.x25]
      x26 := by simp [gpr_write, H.x26] }, ?_⟩
  simp [gpr_write, and15, toNat_ofNat_of_lt hs]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) {t : State}
    (H : HInv T K W D R n SP ciph l A a s₀ t (a.length / 16))
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (.seq (.block [ld .x24 .x19 alenO, Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x24 .x10])
      (.ite (.zero .x .x24) (.block []) (hashRest (callees v)))) t fun t' => Env T K W D R n SP t' ∧
        Frame (hashR T W) s₀.mem t'.mem ∧
        blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  obtain hT := C.lay.hT
  have hs := C.short
  refine WP.seq (WP.mono (tailHead_ok C halen H) fun t₁ ⟨H₁, h24⟩ => ?_)
  refine WP.ite (decide (a.length % 16 = 0)) (eval_zero h24 (by omega_using [])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : a.length % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq]
    obtain hlen : (a.drop (16 * (a.length / 16))).length = 0 := by simp; omega_using [h0]
    simp [hlen]
  · exact hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega_using [this]) h24

/-- The chunks, if any. -/
theorem hashBody_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) {t : State}
    (H₀ : HInv T K W D R n SP ciph l A a s₀ t 0)
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (.ite (.zero .x .x26) (.block []) (.loop (hashChunk (callees v)) (.nonzero .x .x26))) t fun u =>
      HInv T K W D R n SP ciph l A a s₀ u (a.length / 16) := by
  obtain hT := C.lay.hT
  have hs := C.short
  refine WP.ite (decide (a.length / 16 = 0)) (eval_zero H₀.x26 (by omega_using [hs])) (fun hb => WP.block_nil ?_)
    (fun hb => hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb)))
  exact (of_decide_eq_true hb) ▸ H₀

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W + aadO` and
`W + alenO`. -/
theorem hash_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx T K W D n R ciph l A a s₀) (E : Env T K W D R n SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (Impl.AesOcb.AArch64.hash (callees v)) s₀ fun t' => Env T K W D R n SP t' ∧
      Frame (hashR T W) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  obtain hT := C.lay.hT
  unfold Impl.AesOcb.AArch64.hash
  refine WP.assoc (WP.seq (WP.mono (hashHead_ok C E haad halen hl0) fun s₃ H₀ => ?_))
  exact WP.seq (WP.mono (hashBody_ok v C H₀) fun u H => hashTail_ok v C halen H)

end VG.Proof.AesOcb.AArch64
