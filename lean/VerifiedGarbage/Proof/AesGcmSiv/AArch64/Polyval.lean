module

public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.GcmSiv.Words
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `AesGcmSiv.AArch64.Absorb`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on AArch64: POLYVAL (`chunk`, `absorb`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 480` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); `absorb` absorbs the padded string so, its last
bytes padded with zeros in the block at `W + 224` (`absorb_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.AArch64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off toNat_ofNat_of_lt covers_off
  covers_left covers_cons covers_nil covers_append ofNat_sub lsr_ofNat lsl4_ofNat eval_zero eval_nonzero
  add_ofNat_assoc Others in_of_covers)

/-! ## Reversing blocks -/

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.ldr .x .x12 .x11 0, .ldr .x .x13 .x11 8, .rev .x12 .x12, .rev .x13 .x13,
    .str .x .x13 .x14 0, .str .x .x12 .x14 8, Impl.AesGcm.AArch64.ptr .x11 .x11 16,
    Impl.AesGcm.AArch64.ptr .x14 .x14 16, .subImm .x .x15 .x15 1]

/-- The registers `revLoop` writes. -/
abbrev revRegs : List Reg := [.x11, .x12, .x13, .x14, .x15]

theorem revStep_ok {t : State} {S P : Addr} {j : Nat} (hj : j < 2 ^ 63)
    (h11 : t.gpr .x11 = S) (h14 : t.gpr .x14 = P) (h15 : t.gpr .x15 = BitVec.ofNat 64 (j + 1))
    (hr₀ : InRegions (t.rd ++ t.wr) S 8) (hr₈ : InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 8) 8)
    (hw₀ : InRegions t.wr P 8) (hw₈ : InRegions t.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ t' : State, runBlock isa revBody t = some t' ∧
      t'.mem = Proof.Gcm.AArch64.storeMem t.mem P (t.mem.readW (S + BitVec.ofNat 64 8) 64) (t.mem.readW S 64) ∧
      t'.gpr .x11 = S + BitVec.ofNat 64 16 ∧ t'.gpr .x14 = P + BitVec.ofNat 64 16 ∧
      t'.gpr .x15 = BitVec.ofNat 64 j ∧ Others revRegs t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [h11, h14, BitVec.add_zero, hr₀, hr₈, hw₀, hw₈], ?_⟩
  refine ⟨?_, by simp [gpr_write, h11], by simp [gpr_write, h14], ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Proof.Gcm.AArch64.storeMem, Mem.writeW,
      BitVec.setWidth_eq, BitVec.add_zero, read8_readW]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15]
    rw [show (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 1) = BitVec.ofNat 64 j from by
      rw [ofNat_sub (by omega_arith) (by omega_arith)]; rfl]

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (W : Addr) (Q : Addr) (c j : Nat) (t₀ t : State) : Prop where
  x11 : t.gpr .x11 = Q + BitVec.ofNat 64 (16 * j)
  x14 : t.gpr .x14 = W + BitVec.ofNat 64 (480 + 16 * j)
  x15 : t.gpr .x15 = BitVec.ofNat 64 (c - j)
  frame : Frame [⟨W + BitVec.ofNat 64 480, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (W + BitVec.ofNat 64 480) j = elemsAt t₀.mem Q j
  others : Others revRegs t₀ t
  sp : t.sp = t₀.sp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (p : Prm) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  lt : k < 2 ^ 64
  wrap : Q.toNat + k ≤ 2 ^ 64
  y : (⟨Q, k⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 80, 16⟩
  rev : (⟨Q, k⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 480, 1280⟩

namespace Src

variable {p : Prm} {s : State} {Q : Addr} {n : Nat} (h : Src p s Q n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : Src p s (Q + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega_arith) h.lt
  lt := by have := h.lt; omega_arith
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega_arith)]
    have := Nat.mod_le (Q.toNat + k) (2 ^ 64)
    omega_arith
  y := h.y.sub_left (Offset.sub_base Q (by omega_arith))
  rev := h.rev.sub_left (Offset.sub_base Q (by omega_arith))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src p s Q k where
  rd := Proof.AesGcm.AArch64.covers_prefix h.rd hk
  lt := by have := h.lt; omega_arith
  wrap := by have := h.wrap; omega_arith
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : Src p s (Q + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega_arith)).take (by omega_arith)

end Src

/-- A buffer apart from `W`. -/
theorem Src.ofW {p : Prm} (_L : Lay p) {s : State} {Q : Addr} {n : Nat} (hc : Covers [⟨Q, n⟩] (s.rd ++ s.wr))
    (hlt : n < 2 ^ 64) (hw : Q.toNat + n ≤ 2 ^ 64) (hd : (⟨Q, n⟩ : Region).Disjoint ⟨p.W, p.Wn⟩) : Src p s Q n :=
  ⟨hc, hlt, hw, hd.sub_right (Lay.wSub (by have := _L.hWn; omega)), hd.sub_right (Lay.wSub (by have := _L.hWn; omega))⟩

/-- `revLoop`: `c` blocks at `Q` copied to `W + 480`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : Prm} (L : Lay p) {t₀ : State} (E : Env p t₀) {Q : Addr} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : Src p t₀ Q (16 * c)) (h11 : t₀.gpr .x11 = Q)
    (h14 : t₀.gpr .x14 = p.W + BitVec.ofNat 64 480) (h15 : t₀.gpr .x15 = BitVec.ofNat 64 c) :
    WP isa revLoop t₀ fun t => Frame [⟨p.W + BitVec.ofNat 64 480, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (p.W + BitVec.ofNat 64 480) c = elemsAt t₀.mem Q c ∧
      Others revRegs t₀ t ∧ t.sp = t₀.sp ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  obtain hWn := L.hWn
  obtain I₀ : RInv p.W Q c 0 t₀ t₀ := ⟨by rw [h11, Nat.mul_zero, BitVec.add_zero], by rw [h14],
    by rw [h15, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    fun _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block revBody) (c := .nonzero .x .x15)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ RInv p.W Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have hw := L.ww
  obtain rq₀ := in_off (d := 16 * j) (n := 8) hQ.rd (by omega_arith) hQ.lt
  obtain rq₈ := in_off (d := 16 * j + 8) (n := 8) hQ.rd (by omega_arith) hQ.lt
  rw [← add_ofNat_assoc] at rq₈
  obtain ww₀ := E.perm.wW (d := 480 + 16 * j) (n := 8) (by omega_arith)
  obtain ww₈ := E.perm.wW (d := 480 + 16 * j + 8) (n := 8) (by omega_arith)
  rw [← add_ofNat_assoc] at ww₈
  rw [← I.rd, ← I.wr] at rq₀ rq₈
  rw [← I.wr] at ww₀ ww₈
  obtain ⟨t', run', hm', x11', x14', x15', ho', sp', rd', wr'⟩ :=
    revStep_ok (j := c - j - 1) (by omega_arith) I.x11 I.x14 (by rw [I.x15]; congr 1; omega_arith) rq₀ rq₈ ww₀ ww₈
  refine WP.of_runBlock ⟨t', run', ?_⟩
  -- The source is outside the copies.
  obtain src : ∀ d, d + 8 ≤ 16 * c → t.mem.readW (Q + BitVec.ofNat 64 d) 64 = t₀.mem.readW (Q + BitVec.ofNat 64 d) 64 :=
    fun d hd => I.frame.readW (r := ⟨Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base Q (by omega_arith))).sub_right (Offset.sub p.W (by omega_arith) (by omega_arith)))
      (by decide)
  obtain c₁ : (⟨p.W + BitVec.ofNat 64 480, 16 * c⟩ : Region).Contains (p.W + BitVec.ofNat 64 (480 + 16 * j)) (64 / 8) :=
    Offset.contains p.W (by omega_arith) (by omega_arith) (by omega_arith)
  obtain c₂ : (⟨p.W + BitVec.ofNat 64 480, 16 * c⟩ : Region).Contains
      (p.W + BitVec.ofNat 64 (480 + 16 * j) + BitVec.ofNat 64 8) (64 / 8) := by
    rw [add_ofNat_assoc]; exact Offset.contains p.W (by omega_arith) (by omega_arith) (by omega_arith)
  obtain fr : Frame [⟨p.W + BitVec.ofNat 64 (480 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', Proof.Gcm.AArch64.storeMem, BitVec.add_zero]; exact Proof.Cmac.frame_store2 _ _ _
  obtain I' : RInv p.W Q c (j + 1) t₀ t' := by
    refine ⟨by rw [x11', add_ofNat_assoc]; congr 2, by rw [x14', add_ofNat_assoc]; congr 2,
      by rw [x15', Nat.sub_sub], ?_, ?_, fun r hr => by rw [ho' r hr, I.others r hr],
      by rw [sp', I.sp], by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · rw [hm', Proof.Gcm.AArch64.storeMem, BitVec.add_zero]
      exact (I.frame.writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂
    · have s₈ := src (16 * j + 8) (by omega_arith)
      rw [← add_ofNat_assoc] at s₈
      rw [blocksAt_succ, Proof.AesGcm.AArch64.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint p.W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', Proof.Gcm.AArch64.blockAt_storeMem,
        GcmSiv.ofBytes_bytesAt, src (16 * j) (by omega_arith), s₈]
  obtain ev := eval_nonzero x15' (show c - j - 1 < 2 ^ 64 by omega_arith)
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega_arith]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, I'.others, I'.sp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩

/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the reversed blocks and
`vg_ghash`'s working space. -/
abbrev absR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 480, 1280⟩]

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (p : Prm) (Q : Addr) (m k : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = Q + BitVec.ofNat 64 (16 * k)
  x28 : t'.gpr .x28 = BitVec.ofNat 64 (m - 16 * k)
  x9 : t'.gpr .x9 = BitVec.ofNat 64 ((m - 16 * k) / 16)
  frame : Frame (absR p.W) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80)) (elemsAt t.mem Q k)

/-- `chunkLen`: the number of blocks of the chunk. -/
theorem chunkLen_ok {t : State} {m : Nat} (hm : m < 2 ^ 64) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa chunkLen t fun t' => t'.gpr .x10 = BitVec.ofNat 64 (min (m / 16) 64) ∧
      Others [.x10] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, x10₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.lsr .x .x10 .x28 10] t = some t₁ ∧
      t₁.gpr .x10 = BitVec.ofNat 64 (m / 1024) ∧ Others [.x10] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [], ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    simp [gpr_write, h28, lsr_ofNat _ _ hm]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (m / 1024 = 0)) (eval_zero x10₁ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine WP.run ⟨_, by grun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, ho₁ .x28 (by decide), h28, lsr_ofNat _ _ hm]
      congr 1; omega_arith
    · simp only [List.mem_singleton] at hr; simp only [gpr_write, hr, ite_false]; exact ho₁ r (by simpa using hr)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine WP.run ⟨_, by grun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, movz_lit (show 64 < 2 ^ 16 by decide)]
      congr 1; omega_arith
    · simp only [List.mem_singleton] at hr; simp only [gpr_write, hr, ite_false]; exact ho₁ r (by simpa using hr)

/-- A chunk up to its call: up to 64 blocks reversed at `W + 480`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : Prm) (Q : Addr) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (p.W + BitVec.ofNat 64 64) (p.W + BitVec.ofNat 64 80) (p.W + BitVec.ofNat 64 480)
    (p.W + BitVec.ofNat 64 1504) k
  env : Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  x27 : t₅.gpr .x27 = Q + BitVec.ofNat 64 (16 * k)
  x28 : t₅.gpr .x28 = BitVec.ofNat 64 (m - 16 * k)
  frame : Frame [⟨p.W + BitVec.ofNat 64 480, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (p.W + BitVec.ofNat 64 480) k = elemsAt t.mem Q k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa chunkPre t (ChunkPre p Q m (min (m / 16) 64) t) := by
  obtain hWn := L.hWn
  have hw := L.ww
  refine WP.seq (WP.mono (chunkLen_ok hm h28) fun t₁ ⟨x10₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨t₂, run₂, x11₂, x14₂, x15₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x11 .x27, Impl.AesGcm.AArch64.ptr .x14 .x19 revO, Impl.AesGcm.AArch64.mov .x15 .x10]
        t₁ = some t₂ ∧
      t₂.gpr .x11 = Q ∧ t₂.gpr .x14 = p.W + BitVec.ofNat 64 480 ∧
      t₂.gpr .x15 = BitVec.ofNat 64 (min (m / 16) 64) ∧ Others [.x11, .x14, .x15] t₁ t₂ ∧ t₂.mem = t₁.mem ∧
      t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    · simp [gpr_write, ho₁ .x27 (by decide), h27]
    · simp [gpr_write, ho₁ .x19 (by decide), E.x19]
    · simp [gpr_write, x10₁]
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  obtain E₂ : Env p t₂ := E.keep (fun r hr => by
      rw [ho₂ r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ho₁ r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)])
    (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  obtain hk1 : 1 ≤ min (m / 16) 64 := by omega_arith
  obtain hQ₂ : Src p t₂ Q (16 * min (m / 16) 64) := (hQ.take (by omega_arith)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (revLoop_ok L E₂ hk1 (by omega_arith) hQ₂ x11₂ x14₂ x15₂)
    fun t₃ ⟨fr₃, out₃, ho₃, sp₃, rd₃, wr₃⟩ => ?_)
  obtain E₃ : Env p t₃ := E₂.keep (fun r hr => ho₃ r (by
    simp only [envRegs, revRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  obtain x10₃ : t₃.gpr .x10 = BitVec.ofNat 64 (min (m / 16) 64) := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), x10₁]
  obtain x27₃ : t₃.gpr .x27 = Q := by rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h27]
  obtain x28₃ : t₃.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h28]
  obtain m₂₁ : t₂.mem = t.mem := by rw [m₂, m₁]
  rw [m₂₁] at fr₃ out₃
  refine WP.run ⟨_, by simp only [chunkArgs, ghArgs]; grun [], rfl⟩ fun t₄ ht₄ => ?_
  subst ht₄
  refine ⟨⟨?x0, ?x1, ?x2, ?x3, ?x4, ?n_lt, ?hy, ?hs, ?yd, ?ys, ?ds, ?reads, ?writes⟩,
    E₃.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by simp only [rd_write]; rw [rd₃, rd₂, rd₁], by simp only [wr_write]; rw [wr₃, wr₂, wr₁], ?_, ?_,
    by simp only [mem_write]; exact fr₃, by simp only [mem_write]; exact out₃⟩
  case regs =>
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  case x0 => simp [gpr_write, E₃.x19]
  case x1 => simp [gpr_write, E₃.x19]
  case x2 => simp [gpr_write, E₃.x19]
  case x3 => simp [gpr_write, x10₃]
  case x4 => simp [gpr_write, E₃.x19]
  case n_lt => omega_arith
  case hy => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case hs => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case yd => exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  case ys => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case ds => exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  case reads =>
    exact covers_append (covers_cons (E₃.perm.wCR (by decide)) (covers_cons (E₃.perm.wCR (by omega_arith)) covers_nil))
      (covers_cons (E₃.perm.wCR (by decide)) (covers_cons (E₃.perm.wCR (by decide)) covers_nil))
  case writes => exact covers_cons (E₃.perm.wC (by decide)) (covers_cons (E₃.perm.wC (by decide)) covers_nil)
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x27₃, x10₃, ofNat_lsl,
      add_ofNat_assoc]
    congr 2; omega_arith
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x28₃, x10₃, ofNat_lsl]
    rw [ofNat_sub (by omega_arith) hm]; congr 2; omega_arith

theorem chunk_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q)
    (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (chunk v.callees) t (ChunkPost p Q m (min (m / 16) 64) t) := by
  obtain hWn := L.hWn
  have hw := L.ww
  obtain hk : 16 * min (m / 16) 64 ≤ 1024 := by omega_arith
  refine WP.seq (WP.mono (chunkPre_ok L E hm h16 hQ h27 h28) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call v.gh Pr.call) fun t₆ P => ?_)
  obtain E₆ : Env p t₆ := Pr.env.of_saved P.saved P.sp P.rd P.wr
  obtain x28₆ : t₆.gpr .x28 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide) (by decide), Pr.x28]
  obtain dH : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 480, 16 * min (m / 16) 64⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  obtain dY : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 480, 16 * min (m / 16) 64⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  have out₆ := P.out
  rw [Proof.AesGcm.AArch64.blockAt_frame Pr.frame dH, Proof.AesGcm.AArch64.blockAt_frame Pr.frame dY, Pr.out]
    at out₆
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₇ ht₇ => ?_
  subst ht₇
  refine ⟨E₆.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
    by simp only [rd_write]; rw [P.rd, Pr.rd], by simp only [wr_write]; rw [P.wr, Pr.wr], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [P.saved _ (by decide) (by decide), Pr.x27]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; exact x28₆
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x28₆]
    rw [lsr_ofNat _ _ (by omega_arith)]
  · simp only [mem_write]
    refine (Pr.frame.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub p.W (by decide) (by decide)⟩
  · simp only [mem_write]; exact out₆

/-! ## Absorbing a string -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    elemsAt m Q (d + k) = elemsAt m Q d ++ elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, add_ofNat_assoc, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : elemsAt m' Q k = elemsAt m Q k := by
  unfold elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.AArch64.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 224`. -/
abbrev absorbR (W : Addr) : List Region := ⟨W + BitVec.ofNat 64 224, 16⟩ :: absR W

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (p : Prm) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80)) xs

/-- What absorbing a string leaves. -/
abbrev AbsPost (p : Prm) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop := Absorbed p (absorbR p.W) xs t t'

theorem absorbR_H {p : Prm} (L : Lay p) : ∀ r ∈ absorbR p.W, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  obtain hWn := L.hWn
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- A buffer apart from `W` misses what absorbing writes. -/
theorem absorbR_buf {p : Prm} {Q : Addr} {k : Nat} (hd : (⟨Q, k⟩ : Region).Disjoint ⟨p.W, p.Wn⟩)
    (hWn : 1760 ≤ p.Wn := by omega) :
    ∀ r ∈ absorbR p.W, (⟨Q, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hd.sub_right (Lay.wSub (by omega))

theorem absR_sub (W : Addr) : ∀ r ∈ absR W, ∃ r' ∈ absorbR W, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : Absorbed p rs xs t t₁) (h₂ : Absorbed p rs ys t₁ t₂) : Absorbed p rs (xs ++ ys) t t₂ := by
  obtain hWn := h₁.env.perm.hWn
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.AArch64.blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {p : Prm} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : Absorbed p rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Absorbed p rs' xs t t' :=
  ⟨h.env, h.rd, h.wr, h.frame.sub hs, h.out⟩

theorem AbsPost.trans {p : Prm} (L : Lay p) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : AbsPost p xs t t₁) (h₂ : AbsPost p ys t₁ t₂) : AbsPost p (xs ++ ys) t t₂ :=
  Absorbed.trans (absorbR_H L) h₁ h₂

theorem Absorbed.of_chunk {p : Prm} {Q : Addr} {m k : Nat} {t t' : State}
    (h : ChunkPost p Q m k t t') : Absorbed p (absR p.W) (elemsAt t.mem Q k) t t' :=
  ⟨h.env, h.rd, h.wr, h.frame, h.out⟩

theorem Absorbed.of_eq {p : Prm} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : Absorbed p rs xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    Absorbed p rs xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absR_H {p : Prm} (L : Lay p) : ∀ r ∈ absR p.W, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => absorbR_H L r (List.mem_cons_of_mem _ hr)

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (p : Prm) (σ : State) (Q : Addr) (m d : Nat) (t : State) : Prop where
  abs : Absorbed p (absR p.W) (elemsAt σ.mem Q d) σ t
  x27 : t.gpr .x27 = Q + BitVec.ofNat 64 (16 * d)
  x28 : t.gpr .x28 = BitVec.ofNat 64 (m - 16 * d)

theorem CInv.src {p : Prm} {σ t : State} {Q : Addr} {m d : Nat} (I : CInv p σ Q m d t)
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) :
    Src p t (Q + BitVec.ofNat 64 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
  (hQ.slice (by omega_arith)).of_eq I.abs.rd I.abs.wr

theorem CInv.zero {p : Prm} {σ : State} (E : Env p σ) {Q : Addr} {m : Nat} (h27 : σ.gpr .x27 = Q)
    (h28 : σ.gpr .x28 = BitVec.ofNat 64 m) : CInv p σ Q m 0 σ :=
  ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
    by rw [h27, Nat.mul_zero, BitVec.add_zero], by rw [h28, Nat.mul_zero, Nat.sub_zero]⟩

/-- A chunk, in the chunks. -/
theorem CInv.step {p : Prm} (L : Lay p) {σ t t' : State} {Q : Addr} {m d : Nat} (_hm : m < 2 ^ 64)
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) (I : CInv p σ Q m d t)
    (C : ChunkPost p (Q + BitVec.ofNat 64 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    CInv p σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 (m / 16 - (d + min (m / 16 - d) 64)) := by
  obtain hWn := L.hWn
  obtain hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega_arith
  rw [hk] at C
  obtain hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega_arith)
  obtain C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.y
      · exact hs.rev) (by omega_arith)] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.x27, add_ofNat_assoc, Nat.mul_add],
    by rw [C.x28]; congr 1; omega_arith⟩, by rw [C.x9]; congr 1; omega_arith⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q)
    (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (.loop (chunk v.callees) (.nonzero .x .x9)) t fun t' =>
      Absorbed p (absR p.W) (elemsAt t.mem Q (m / 16)) t t' ∧
      t'.gpr .x27 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t'.gpr .x28 = BitVec.ofNat 64 (m % 16) := by
  obtain hWn := L.hWn
  refine WP.loop (M := isa) (body := chunk v.callees) (c := .nonzero .x .x9)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega_arith, CInv.zero E h27 h28⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_ok v L I.abs.env (by omega_arith) (by omega_arith) (I.src hQ hd) I.x27 I.x28) fun t'' C => ?_
  obtain ⟨I', x9⟩ := I.step L hm hQ hd C
  obtain ev := eval_nonzero x9 (by omega_arith)
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega_arith), he ▸ I'.abs, by rw [I'.x27, he], by rw [I'.x28, he]; congr 1; omega_arith⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), m / 16 - (d + min (m / 16 - d) 64), by omega_arith, d + min (m / 16 - d) 64, rfl,
      by omega_arith, I'⟩

end VG.Proof.AesGcmSiv.AArch64

end

end

/-!
# AES-GCM-SIV on AArch64: POLYVAL and the tag input (`polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 224` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`); `tagIn` turns POLYVAL's result into the tag input
(`tagIn_ok`). `polyval_ok`: the tag input of RFC 8452 §4, with POLYVAL as
GHASH with the key `H · x` (`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl ofNat_add_ofNat in_off toNat_ofNat_of_lt covers_off covers_left
  ofNat_sub lsr_ofNat eval_zero add_ofNat_assoc Others LoopPre copyLoop_ok loopRegs length_bytesAt)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero2 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  have hz := Proof.Cmac.zero2_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega_arith, Proof.AesGcm.AArch64.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega_arith, Proof.AesGcm.AArch64.bytesAt_add,
    Proof.AesGcm.AArch64.bytesAt_writeBytes_self _ _ _ (by omega_arith),
    Proof.AesGcm.AArch64.bytesAt_frame (Proof.AesGcm.AArch64.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega_arith)) (by omega_arith)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

theorem zero2_eq (m : Mem) (W : Addr) :
    (m.writeW (W + BitVec.ofNat 64 224) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 232) (0 : BitVec 64) =
      Proof.Cmac.zero2 m (W + BitVec.ofNat 64 224) := by
  rw [Proof.Cmac.zero2, add_ofNat_assoc]

/-- The block at `W + 224` as a chunk's source. -/
theorem srcB {p : Prm} (L : Lay p) {s : State} (P : Perm p s) : Src p s (p.W + BitVec.ofNat 64 224) 16 where
  rd := P.wCR (by decide)
  lt := by decide
  wrap := by rw [L.toNat_W (by have := L.hWn; omega)]; have := L.ww; have := L.hWn; omega_arith
  y := L.w_w (.inr (by decide)) (by decide) (by decide)
  rev := L.w_w (.inl (by decide)) (by decide) (by decide)

/-- One chunk of the 16 bytes at `W + 224`: their field element absorbed. -/
theorem chunkB_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (h27 : t.gpr .x27 = p.W + BitVec.ofNat 64 224) (h28 : t.gpr .x28 = BitVec.ofNat 64 16) :
    WP isa (chunk v.callees) t (Absorbed p (absR p.W)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 224) 16)] t) :=
  WP.mono (chunk_ok v L E (m := 16) (by decide) (by decide) (srcB L E.perm) h27 h28) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [elemsAt] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 224`, as the
bytes to absorb. -/
structure TailPre (p : Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  x27 : t₃.gpr .x27 = p.W + BitVec.ofNat 64 224
  x28 : t₃.gpr .x28 = BitVec.ofNat 64 16
  frame : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨p.W, p.Wn⟩) (h27 : t.gpr .x27 = P) (h28 : t.gpr .x28 = BitVec.ofNat 64 r) :
    WP isa absTailPre t (TailPre p P r t) := by
  obtain hWn := L.hWn
  have hw := L.ww
  have w₀ := E.perm.wW (show 224 + 8 ≤ 1760 by decide)
  have w₈ := E.perm.wW (show 232 + 8 ≤ 1760 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, x11₁, x12₁, x13₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State,
      runBlock isa (zero16 bO ++ [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27,
        Impl.AesGcm.AArch64.mov .x13 .x28]) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (p.W + BitVec.ofNat 64 224) ∧ t₁.gpr .x11 = p.W + BitVec.ofNat 64 224 ∧
      t₁.gpr .x12 = P ∧ t₁.gpr .x13 = BitVec.ofNat 64 r ∧ Others [.x9, .x11, .x12, .x13] t t₁ ∧
      t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [zero16]; grun [E.x19, w₀, w₈], ?_, ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl)⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, movz0, ← zero2_eq]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h27]
    · simp [gpr_write, h28]
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dB : (⟨P, r⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 224, r⟩ :=
    (hd.sub_right (Lay.wSub (show 224 + 16 ≤ p.Wn by omega))).sub_right (Region.sub_prefix (by omega_arith))
  have lp : LoopPre t₁ P (p.W + BitVec.ofNat 64 224) r :=
    ⟨by omega_arith, by rw [rd₁, wr₁]; exact hc, Proof.AesGcm.AArch64.covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 1760 by decide))
      (by omega_arith), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ x12₁ x11₁ x13₁ (by omega_arith) lp) fun t₂ ⟨hm₂, _, _, ho₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env p t₂ := E₁.keep (fun q hq => ho₂ q (by
    simp only [envRegs, loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁]
    exact Proof.AesGcm.AArch64.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by omega)))
      (by omega_arith)
  have hb₂ : bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := length_bytesAt t.mem P r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega_arith), hl]
  have f₂ : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact (Proof.Cmac.frame_store2 _ _ _).trans
      ((Proof.AesGcm.AArch64.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  exact ⟨E₂.keep (fun q hq => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
    by simp only [rd_write]; rw [rd₂, rd₁], by simp only [wr_write]; rw [wr₂, wr₁],
    by simp [gpr_write, E₂.x19], by simp [gpr_write, movz_lit (show 16 < 2 ^ 16 by decide)],
    by simp only [mem_write]; exact f₂, by simp only [mem_write]; exact hb₂⟩

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨p.W, p.Wn⟩) (h27 : t.gpr .x27 = P) (h28 : t.gpr .x28 = BitVec.ofNat 64 r) :
    WP isa (absTail v.callees) t
      (AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  obtain hWn := L.hWn
  have hw := L.ww
  refine WP.seq (WP.mono (absTailPre_ok L E hr1 hr hc hd h27 h28) fun t₃ T => ?_)
  refine WP.mono (chunkB_ok v L T.env T.x27 T.x28) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region)], ∀ d, d + 16 ≤ 224 →
      (⟨p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega_arith) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.AArch64.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
    Proof.AesGcm.AArch64.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]

/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.AesGcm.AArch64.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at hs
  have hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `x9` holds their number. -/
theorem absMid_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (hQ : Src p t Q m) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 (m / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (chunk v.callees) (.nonzero .x .x9))) t fun t₂ =>
      Absorbed p (absR p.W) (elemsAt t.mem Q (m / 16)) t t₂ ∧
        t₂.gpr .x27 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t₂.gpr .x28 = BitVec.ofNat 64 (m % 16) := by
  obtain hWn := L.hWn
  refine WP.ite (decide (m / 16 = 0)) (eval_zero h9 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h27, h0, Nat.mul_zero, BitVec.add_zero], by rw [h28]; congr 1; omega_arith⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_ok v L E hm (by omega_arith) (hQ.take (by omega_arith)) h27 h28

/-- `absorb`'s first block. -/
theorem absHead_ok {t : State} {m : Nat} (hm : m < 2 ^ 64) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (.block [.lsr .x .x9 .x28 4]) t fun t₁ => t₁.gpr .x9 = BitVec.ofNat 64 (m / 16) ∧
      Others [.x9] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
  WP.run ⟨_, by grun [], rfl⟩ fun t₁ ht₁ => by
    subst ht₁
    exact ⟨by simp [gpr_write, h28, lsr_ofNat _ _ hm], by others_tac, rfl, rfl, rfl, rfl⟩

theorem absorb_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hc : Covers [⟨Q, m⟩] (t.rd ++ t.wr)) (hm : m < 2 ^ 64) (hw : Q.toNat + m ≤ 2 ^ 64)
    (hd : (⟨Q, m⟩ : Region).Disjoint ⟨p.W, p.Wn⟩) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (absorb v.callees) t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q m))) t) := by
  obtain hWn := L.hWn
  have hQ : Src p t Q m := Src.ofW L hc hm hw hd
  refine WP.seq (WP.mono (absHead_ok hm h28) fun t₁ ⟨x9₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (absMid_ok v L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [ho₁ _ (by decide), h27])
    (by rw [ho₁ _ (by decide), h28]) x9₁) fun t₂ ⟨P₂, x27₂, x28₂⟩ => ?_)
  rw [m₁] at P₂
  have P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [elems_pad16_bytesAt]
  refine WP.ite (decide (m % 16 = 0)) (eval_zero x28₂ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₂'.sub (absR_sub p.W))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith)
    have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨p.W, p.Wn⟩ :=
      hd.sub_left (Offset.sub_base Q (by omega_arith))
    refine WP.mono (absTail_ok v L P₂'.env (by omega_arith) (by omega_arith) (by rw [P₂'.rd, P₂'.wr]; exact hs.rd) dT x27₂ x28₂)
      fun t₃ T => ?_
    have e := Proof.AesGcm.AArch64.bytesAt_frame P₂'.frame (fun r hr => dT.sub_right ?_) (by omega_arith)
    · rw [e] at T
      exact AbsPost.trans L (P₂'.sub (absR_sub p.W)) T
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.wSub (by omega)

/-! ## The lengths, and the tag input -/

theorem le64_word (x : Nat) : Spec.GcmSiv.le64 x = Proof.Cmac.le8 (BitVec.ofNat 64 x) := GcmSiv.le64_le8 x

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (lens v.callees) t (AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  obtain hWn := L.hWn
  have w₀ := E.perm.wW (show 224 + 8 ≤ 1760 by decide)
  have w₈ := E.perm.wW (show 232 + 8 ≤ 1760 by decide)
  obtain ⟨t₁, run₁, hm₁, x27₁, x28₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = (t.mem.writeW (p.W + BitVec.ofNat 64 224) (BitVec.ofNat 64 (8 * p.al))).writeW
        (p.W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8) (BitVec.ofNat 64 (8 * p.n)) ∧
      t₁.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t₁.gpr .x28 = BitVec.ofNat 64 16 ∧
      Others [.x9, .x27, .x28] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl),
      (by rfl)⟩
    · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, BitVec.setWidth_eq,
        add_ofNat_assoc, ofNat_lsl, E.x24, E.x26]
      rw [Nat.mul_comm p.al, Nat.mul_comm p.n]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, movz_lit (show 16 < 2 ^ 16 by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  refine WP.mono (chunkB_ok v L E₁ x27₁ x28₁) fun t₂ C => ?_
  have hb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 224) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, le64_word, le64_word]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 224 → ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega_arith) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁],
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.AArch64.blockAt_frame f₁ (dHY 64 (by decide)),
    Proof.AesGcm.AArch64.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  let lo := rev64 (m.readW (W + BitVec.ofNat 64 88) 64) ^^^ m.readW N 64
  let hi := ((rev64 (m.readW (W + BitVec.ofNat 64 80) 64) ^^^ (m.readW (N + BitVec.ofNat 64 8) 32).setWidth 64)
    <<< 1) >>> 1
  (m.writeW (W + BitVec.ofNat 64 96) lo).writeW (W + BitVec.ofNat 64 104) hi

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  rw [tagInMem, show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    Proof.Cmac.bytesAt_store2, ← Proof.Gcm.AArch64.blockAt_rev, BitVec.add_zero, add_ofNat_assoc,
    GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words, GcmSiv.Words.shl_shr_one]

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (tagInMem m W N) := by
  rw [tagInMem, show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact Proof.Cmac.frame_store2 _ _ _

theorem tagIn_ok {p : Prm} {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = tagInMem t.mem p.W p.N ∧
      Others [.x9, .x10, .x11] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain hWn := E.perm.hWn
  have r₀ := E.perm.wR (show 80 + 8 ≤ 1760 by decide)
  have r₈ := E.perm.wR (show 88 + 8 ≤ 1760 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 1760 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 1760 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) p.N 8 := by simpa using E.perm.nR (d := 0) (k := 8) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn]; grun [E.x19, E.x20, BitVec.add_zero, r₀, r₈, w₀, w₈, n₀, n₈], ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, tagInMem, Mem.writeW, BitVec.setWidth_eq,
    read8_readW, read4_readW]

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W : Addr) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: absorbR W

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (polyR p.W) t.mem t'.mem
  out : bytesAt t'.mem (p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem p.N 12) (bytesAt t.mem p.D p.n)
      (bytesAt t.mem p.A p.al)

theorem polyval_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (PolyPost p t) := by
  obtain hWn := L.hWn
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((E.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact E.perm.aad) L.al_lt L.aw L.a_w
    (by simp [gpr_write, E.x23]) (by simp [gpr_write, E.x24])) fun t₂ P₂ => ?_)
  simp only [mem_write] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  -- The data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((P₂.env.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact covers_left P₂.env.perm.d)
    L.n_lt L.dw L.d_w (by simp [gpr_write, P₂.env.x25]) (by simp [gpr_write, P₂.env.x26])) fun t₄ P₄ => ?_)
  simp only [mem_write] at P₄
  rw [Proof.AesGcm.AArch64.bytesAt_frame P₂.frame (absorbR_buf L.d_w) (by have := L.n_lt; omega_arith)] at P₄
  have P₂₄ := AbsPost.trans L P₂' (P₄.of_eq rfl rfl rfl)
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.keep (fun q hq => ho₆ q (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆,
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
    have nN : bytesAt t₅.mem p.N 12 = bytesAt t.mem p.N 12 :=
      Proof.AesGcm.AArch64.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_write]

end VG.Proof.AesGcmSiv.AArch64
