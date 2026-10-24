module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
public import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE

/-!
# AES-GCM-SIV on PPC64LE: POLYVAL's whole blocks (`chunk`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcmSiv/Arm/Absorb.lean`): `revLoop` copies blocks to `W + 496`,
each with its bytes reversed (`ldbrx`), so that GHASH reads POLYVAL's field
elements of them (`revMem_block`); `chunk` absorbs up to 64 of them by a
call of `vg_ghash` (`chunk_wp`), and a loop of chunks the whole blocks of a
string (`chunks_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_ld wp_std wp_lsl wp_lsr wp_sub wp_subi)
open VG.Proof.AesCcm.PPC64LE (wp_mv wp_ldbrx)
open VG.Proof.AesGcm.PPC64LE (GhCall GhPost gh_call)
open VG.Spec.Aes (bytesAt)

/-! ## Reversing blocks -/

/-- What one step of `revLoop` stores: the doublewords of the block at `S` in
the other order, each reversed. -/
def revMem (m : Mem) (S P : Addr) : Mem :=
  (m.writeW P (rev64 (m.readW (S + BitVec.ofNat 64 8) 64))).writeW (P + BitVec.ofNat 64 8) (rev64 (m.readW S 64))

theorem revMem_frame (m : Mem) (S P : Addr) : Frame [⟨P, 16⟩] m (revMem m S P) :=
  Proof.Cmac.frame_store2 _ _ _

/-- The block `revMem` stores, as GHASH reads it: POLYVAL's field element of
the source. -/
theorem revMem_block (m : Mem) (S P : Addr) :
    Spec.Gcm.blockAt (revMem m S P) P = Spec.GcmSiv.ofBytes (bytesAt m S 16) := by
  have hs : Mem.Sep P (64 / 8) (P + BitVec.ofNat 64 8) (64 / 8) := by
    simpa using Offset.sep P (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
  rw [revMem, ← Proof.Gcm.PPC64LE.blockAt_rev, BitVec.add_zero, Mem.readW_writeW_sep hs (by decide),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64, Proof.Gcm.PPC64LE.rev64_rev64,
    Proof.Gcm.PPC64LE.rev64_rev64, GcmSiv.ofBytes_bytesAt]

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (c : Cx) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  lt : k < 2 ^ 64
  wrap : Q.toNat + k ≤ 2 ^ 64
  y : (⟨Q, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 80, 16⟩
  rev : (⟨Q, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 496, 1280⟩

namespace Src

variable {c : Cx} {s : State} {Q : Addr} {n : Nat} (h : Src c s Q n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src c s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 64 j).toNat = Q.toNat + j := by
  have := h.wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src c s Q k where
  rd := VG.Proof.Gather.PPC64LE.covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : Src c s (Q + BitVec.ofNat 64 a) k := by
  have hs : Region.Sub ⟨Q + BitVec.ofNat 64 a, k⟩ ⟨Q, n⟩ := Offset.sub_base _ hk
  exact ⟨VG.Proof.Gather.PPC64LE.covers_off h.rd hk h.lt, by have := h.lt; omega,
    by rw [h.toNat_add ha]; have := h.wrap; omega, h.y.sub_left hs, h.rev.sub_left hs⟩

end Src

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (c : Cx) (Q : Addr) (k j : Nat) (t₀ t : State) : Prop where
  r23 : t.gpr .r23 = Q + BitVec.ofNat 64 (16 * j)
  r4 : t.gpr .r4 = c.W + BitVec.ofNat 64 (496 + 16 * j)
  r3 : t.gpr .r3 = BitVec.ofNat 64 (k - j)
  frame : Frame [⟨c.W + BitVec.ofNat 64 496, 16 * k⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (c.W + BitVec.ofNat 64 496) j = elemsAt t₀.mem Q j
  keep : Keep [.r3, .r4, .r5, .r6, .r23] t₀ t
  sp : t.sp = t₀.sp

/-- `revLoop`: `k` blocks at `Q` copied to `W + 496`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_wp {c : Cx} (L : Lay c) {t₀ : State} (E : Env c t₀) {Q : Addr} {k : Nat}
    (hk1 : 1 ≤ k) (hk : k ≤ 64) (hQ : Src c t₀ Q (16 * k)) (h23 : t₀.gpr .r23 = Q)
    (h4 : t₀.gpr .r4 = c.W + BitVec.ofNat 64 496) (h3 : t₀.gpr .r3 = BitVec.ofNat 64 k)
    (h9 : t₀.gpr .r9 = BitVec.ofNat 64 8) (h10 : t₀.gpr .r10 = BitVec.ofNat 64 0) :
    WP isa revLoop t₀ fun t => Frame [⟨c.W + BitVec.ofNat 64 496, 16 * k⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (c.W + BitVec.ofNat 64 496) k = elemsAt t₀.mem Q k ∧
      t.gpr .r23 = Q + BitVec.ofNat 64 (16 * k) ∧ Keep [.r3, .r4, .r5, .r6, .r23] t₀ t ∧ t.sp = t₀.sp := by
  have hw := L.ww
  have I₀ : RInv c Q k 0 t₀ t₀ := ⟨by rw [h23, Nat.mul_zero, BitVec.add_zero], by rw [h4],
    by rw [h3, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    Keep.refl _ _, rfl⟩
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ j, w = k - j ∧ j < k ∧ RInv c Q k j t₀ t) ?_ (k - 0) t₀ ⟨0, rfl, hk1, I₀⟩
  rintro w t ⟨j, rfl, hj, I⟩
  have hS := hQ.toNat_add (j := 16 * j) (by omega)
  have r9 : t.gpr .r9 = BitVec.ofNat 64 8 := by rw [I.keep.gpr (by decide), h9]
  have r10 : t.gpr .r10 = BitVec.ofNat 64 0 := by rw [I.keep.gpr (by decide), h10]
  have hr : Covers [⟨Q + BitVec.ofNat 64 (16 * j), 16⟩] (t.rd ++ t.wr) := by
    rw [I.keep.2.1, I.keep.2.2]; exact VG.Proof.Gather.PPC64LE.covers_off hQ.rd (by omega) hQ.lt
  have hwr : Covers [⟨c.W + BitVec.ofNat 64 (496 + 16 * j), 16⟩] t.wr := by
    rw [I.keep.2.2]; exact E.perm.wC (by omega)
  have in8 (P : Addr) {rs : List Region} (h : Covers [⟨P, 16⟩] rs) (d : Nat) (hd : d + 8 ≤ 16) :
      InRegions rs (P + BitVec.ofNat 64 d) 8 := VG.Proof.Gather.PPC64LE.in_off h hd (by decide)
  refine wp_ldbrx (ea := Q + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 8) (by decide) (by rw [I.r23, r9])
    (in8 _ hr 8 (by decide)) fun t₁ u₁ => ?_
  refine wp_ldbrx (ea := Q + BitVec.ofNat 64 (16 * j)) (by decide)
    (by rw [u₁.other _ (by decide), u₁.other _ (by decide), I.r23, r10]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr]; simpa using in8 _ hr 0 (by decide)) fun t₂ u₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 (496 + 16 * j)) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), I.r4]; exact BitVec.add_zero _)
    (by rw [u₂.wr, u₁.wr]; simpa using in8 _ hwr 0 (by decide)) fun t₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 (496 + 16 * j) + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), I.r4])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact in8 _ hwr 8 (by decide)) fun t₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₅ u₅ => wp_addi (by decide) (by decide) fun t₆ u₆ =>
    wp_subi (by decide) (by decide) fun t₇ u₇ => WP.block_nil ?_
  have hm : t₇.mem = revMem t.mem (Q + BitVec.ofNat 64 (16 * j)) (c.W + BitVec.ofNat 64 (496 + 16 * j)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other .r5 (by decide), u₁.gpr,
      u₂.mem, u₁.mem]
    rfl
  -- The source is outside the copies.
  have src : bytesAt t.mem (Q + BitVec.ofNat 64 (16 * j)) 16 = bytesAt t₀.mem (Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.Cmac.bytesAt_frame16 I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub _ (by omega) (by omega)))
  have fr : Frame [⟨c.W + BitVec.ofNat 64 (496 + 16 * j), 16⟩] t.mem t₇.mem := by
    rw [hm]; exact revMem_frame _ _ _
  have kp : Keep [.r3, .r4, .r5, .r6, .r23] t t₇ :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₇.other _ hr.1, u₆.other _ hr.2.1, u₅.other _ hr.2.2.2.2, u₄.gpr, u₃.gpr, u₂.other _ hr.2.2.2.1,
        u₁.other _ hr.2.2.1],
      by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  have r3' : t₇.gpr .r3 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), I.r3, ofNat_sub (by omega) (by omega), Nat.sub_sub]
  have I' : RInv c Q k (j + 1) t₀ t₇ := by
    refine ⟨?_, ?_, r3', ?_, ?_, (I.keep.trans kp).mono (by decide), ?_⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), I.r23, Offset.add_add, Nat.mul_succ]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), I.r4, Offset.add_add, Nat.mul_succ, Nat.add_assoc]
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩)
    · rw [blocksAt_succ, blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [Offset.add_add, hm, revMem_block, src]
    · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, I.sp]
  have ev := VG.Proof.Gather.PPC64LE.eval_nonzero r3' (by omega)
  by_cases he : j + 1 = k
  · left
    refine ⟨ev.trans (by simp [he]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.r23, I'.keep, I'.sp⟩
  · right
    exact ⟨ev.trans (by simp; omega), k - (j + 1), by omega, j + 1, rfl, by omega, I'⟩

/-! ## A chunk -/

/-- `chunkLen`: the number of blocks of the chunk, `min (m / 16) 64`. -/
theorem chunkLen_wp {t : State} {m : Nat} (hm : m < 2 ^ 64) (h24 : t.gpr .r24 = BitVec.ofNat 64 m) :
    WP isa chunkLen t fun t' => Proof.ChaCha20Poly1305.PPC64LE.Upd t t' .r25 (BitVec.ofNat 64 (min (m / 16) 64)) := by
  unfold chunkLen
  refine WP.seq (wp_lsr (by decide) fun t₁ u₁ => WP.block_nil ?_)
  have e1 : t₁.gpr .r25 = BitVec.ofNat 64 (m / 1024) := by rw [u₁.gpr, h24, ofNat_lsr 10 hm]
  refine WP.ite (decide (m / 1024 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero e1 (by omega)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine wp_lsr (by decide) fun t₂ u₂ => WP.block_nil (upd2 u₁ u₂ ?_)
    rw [u₁.other _ (by decide), h24, ofNat_lsr 4 hm]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine wp_li (by decide) fun t₂ u₂ => WP.block_nil (upd2 u₁ u₂ ?_)
    exact congrArg (BitVec.ofNat 64) (by omega)

/-- A chunk up to its call: up to 64 blocks reversed at `W + 496`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (c : Cx) (Q : Addr) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 496)
    (c.W + BitVec.ofNat 64 1520) k
  pk : PK t t₅
  r23 : t₅.gpr .r23 = Q + BitVec.ofNat 64 (16 * k)
  r24 : t₅.gpr .r24 = BitVec.ofNat 64 (m - 16 * k)
  frame : Frame [⟨c.W + BitVec.ofNat 64 496, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (c.W + BitVec.ofNat 64 496) k = elemsAt t.mem Q k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ : Src c t Q (16 * (m / 16))) (h23 : t.gpr .r23 = Q) (h24 : t.gpr .r24 = BitVec.ofNat 64 m) :
    WP isa chunkPre t (ChunkPre c Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  unfold chunkPre
  refine WP.seq (WP.mono (chunkLen_wp hm h24) fun t₁ u₁ => ?_)
  refine WP.seq (wp_addi (by decide) (by decide) fun t₂ u₂ => wp_mv fun t₃ u₃ => wp_li (by decide) fun t₄ u₄ =>
    wp_li (by decide) fun t₅ u₅ => WP.block_nil ?_)
  have pk₅ : PK t t₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  have E₅ := E.of_pk pk₅
  have hQ₅ : Src c t₅ Q (16 * min (m / 16) 64) := (hQ.take (by omega)).of_eq pk₅.rd pk₅.wr
  have m₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (revLoop_wp L E₅ hk1 (by omega) hQ₅
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h23])
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      E.r14] <;> rfl)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₅.other _ (by decide), u₄.gpr]) u₅.gpr)
    fun t₆ ⟨fr₆, out₆, r23₆, kp₆, sp₆⟩ => ?_)
  have pk₆ : PK t₅ t₆ := PK.ofKeep kp₆ sp₆
  have E₆ := E₅.of_pk pk₆
  have r25₆ : t₆.gpr .r25 = BitVec.ofNat 64 (min (m / 16) 64) := by
    rw [kp₆.gpr (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  have r24₆ : t₆.gpr .r24 = BitVec.ofNat 64 m := by
    rw [kp₆.gpr (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h24]
  rw [m₅] at fr₆ out₆
  unfold chunkArgs
  refine wp_lsl (by decide) fun t₇ u₇ => wp_sub fun t₈ u₈ => wp_addi (by decide) (by decide) fun t₉ u₉ =>
    wp_addi (by decide) (by decide) fun t₁₀ u₁₀ => wp_addi (by decide) (by decide) fun t₁₁ u₁₁ =>
    wp_mv fun t₁₂ u₁₂ => wp_addi (by decide) (by decide) fun t₁₃ u₁₃ => WP.block_nil ?_
  have pk₁₃ : PK t₆ t₁₃ := (PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans
    ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans (PK.ofUpd u₁₃))))))
  have E₁₃ := E₆.of_pk pk₁₃
  have w14 : ∀ {s : State}, Env c s → s.gpr .r14 = c.W := fun h => h.r14
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, pk₅.trans (pk₆.trans pk₁₃), ?_, ?_,
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]; exact fr₆,
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]; exact out₆⟩
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), E₆.r14] <;> rfl
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), E₆.r14] <;> rfl
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), E₆.r14] <;> rfl
  · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), r25₆]
  · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), E₆.r14] <;> rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by omega)) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Covers.append_left (Covers.cons (E₁₃.perm.wCR (by decide)) (Covers.cons (E₁₃.perm.wCR (by omega))
      Covers.nil)) (Covers.cons (E₁₃.perm.wCR (by decide)) (Covers.cons (E₁₃.perm.wCR (by decide)) Covers.nil))
  · exact Covers.cons (E₁₃.perm.wC (by decide)) (Covers.cons (E₁₃.perm.wC (by decide)) Covers.nil)
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), r23₆]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₇.other _ (by decide), r24₆, r25₆, ofNat_shl,
      ofNat_sub (by omega) hm]

/-- What a chunk writes: GHASH's accumulator, the reversed blocks and
`vg_ghash`'s working space. -/
abbrev absR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 496, 1280⟩]

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (c : Cx) (Q : Addr) (m k : Nat) (t t' : State) : Prop where
  pk : PK t t'
  r23 : t'.gpr .r23 = Q + BitVec.ofNat 64 (16 * k)
  r24 : t'.gpr .r24 = BitVec.ofNat 64 (m - 16 * k)
  r11 : t'.gpr .r11 = BitVec.ofNat 64 ((m - 16 * k) / 16)
  frame : Frame (absR c.W) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (c.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80)) (elemsAt t.mem Q k)

theorem chunk_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src c t Q (16 * (m / 16))) (h23 : t.gpr .r23 = Q)
    (h24 : t.gpr .r24 = BitVec.ofNat 64 m) :
    WP isa chunk t (ChunkPost c Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega
  unfold chunk
  refine WP.seq (WP.mono (chunkPre_wp L E hm h16 hQ h23 h24) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call Pr.call) fun t₆ P => ?_)
  have pk₆ : PK t₅ t₆ := PK.ofSaved P.rd P.wr P.sp P.saved
  have r24₆ : t₆.gpr .r24 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide), Pr.r24]
  have dH : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 496, 16 * min (m / 16) 64⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 496, 16 * min (m / 16) 64⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have out₆ := P.out
  rw [blockAt_frame Pr.frame dH, blockAt_frame Pr.frame dY, Pr.out] at out₆
  unfold wholeLeft
  refine wp_lsr (by decide) fun t₇ u₇ => WP.block_nil ⟨Pr.pk.trans (pk₆.trans (PK.ofUpd u₇)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), P.saved _ (by decide), Pr.r23]
  · rw [u₇.other _ (by decide), r24₆]
  · rw [u₇.gpr, r24₆, ofNat_lsr 4 (by omega)]
  · rw [u₇.mem]
    refine (Pr.frame.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  · rw [u₇.mem]; exact out₆

/-! ## Absorbing -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    elemsAt m Q (d + k) = elemsAt m Q d ++ elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, Offset.add_add, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : elemsAt m' Q k = elemsAt m Q k := by
  unfold elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.Cmac.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 240`. -/
abbrev absorbR (W : Addr) : List Region := ⟨W + BitVec.ofNat 64 240, 16⟩ :: absR W

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (c : Cx) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (c.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80)) xs

theorem absorbR_H {c : Cx} (L : Lay c) :
    ∀ r ∈ absorbR c.W, (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem absR_H {c : Cx} (L : Lay c) : ∀ r ∈ absR c.W, (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => absorbR_H L r (List.mem_cons_of_mem _ hr)

/-- A buffer apart from `W` misses what absorbing writes. -/
theorem absorbR_buf {c : Cx} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨c.W, 3824⟩) :
    ∀ r ∈ absorbR c.W, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hd.sub_right (Lay.wSub (by decide))

theorem absR_sub (W : Addr) : ∀ r ∈ absR W, ∃ r' ∈ absorbR W, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {c : Cx} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : Absorbed c rs xs t t₁) (h₂ : Absorbed c rs ys t₁ t₂) : Absorbed c rs (xs ++ ys) t t₂ := by
  refine ⟨h₁.pk.trans h₂.pk, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {c : Cx} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : Absorbed c rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Absorbed c rs' xs t t' :=
  ⟨h.pk, h.frame.sub hs, h.out⟩

theorem Absorbed.of_chunk {c : Cx} {Q : Addr} {m k : Nat} {t t' : State}
    (h : ChunkPost c Q m k t t') : Absorbed c (absR c.W) (elemsAt t.mem Q k) t t' :=
  ⟨h.pk, h.frame, h.out⟩

theorem Absorbed.of_eq {c : Cx} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : Absorbed c rs xs t₁ t₂) (pk : PK t t₁) (hm : t₁.mem = t.mem) : Absorbed c rs xs t t₂ :=
  ⟨pk.trans h.pk, hm ▸ h.frame, by rw [h.out, hm]⟩

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (c : Cx) (σ : State) (Q : Addr) (m d : Nat) (t : State) : Prop where
  abs : Absorbed c (absR c.W) (elemsAt σ.mem Q d) σ t
  r23 : t.gpr .r23 = Q + BitVec.ofNat 64 (16 * d)
  r24 : t.gpr .r24 = BitVec.ofNat 64 (m - 16 * d)

/-- A chunk, in the chunks. -/
theorem CInv.step {c : Cx} (L : Lay c) {σ t t' : State} {Q : Addr} {m d : Nat}
    (hQ : Src c σ Q (16 * (m / 16))) (hd : d < m / 16) (I : CInv c σ Q m d t)
    (C : ChunkPost c (Q + BitVec.ofNat 64 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    CInv c σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.gpr .r11 = BitVec.ofNat 64 (m / 16 - (d + min (m / 16 - d) 64)) := by
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega) (by omega)
  have C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.y
      · exact hs.rev) (by omega)] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.r23, Offset.add_add, Nat.mul_add],
    by rw [C.r24]; congr 1; omega⟩, by rw [C.r11]; congr 1; omega⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src c t Q (16 * (m / 16))) (h23 : t.gpr .r23 = Q)
    (h24 : t.gpr .r24 = BitVec.ofNat 64 m) :
    WP isa (.loop chunk (.nonzero .d .r11)) t fun t' =>
      Absorbed c (absR c.W) (elemsAt t.mem Q (m / 16)) t t' ∧
      t'.gpr .r23 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t'.gpr .r24 = BitVec.ofNat 64 (m % 16) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv c t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega, ⟨⟨PK.refl _, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h23, Nat.mul_zero, BitVec.add_zero], by rw [h24, Nat.mul_zero, Nat.sub_zero]⟩⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_wp L (E.of_pk I.abs.pk) (by omega) (by omega)
    ((hQ.slice (by omega) (by omega)).of_eq I.abs.pk.rd I.abs.pk.wr) I.r23 I.r24) fun t'' C => ?_
  obtain ⟨I', r11⟩ := I.step L hQ hd C
  have ev := VG.Proof.Gather.PPC64LE.eval_nonzero r11 (by omega)
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega), he ▸ I'.abs, by rw [I'.r23, he], by rw [I'.r24, he]; congr 1; omega⟩
  · right
    exact ⟨ev.trans (by simp; omega), m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.PPC64LE
