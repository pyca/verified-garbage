import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# AES-GCM-SIV on AArch64: POLYVAL (`chunk`, `absorb`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 768` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); `absorb` absorbs the padded string so, its last
bytes padded with zeros in the block at `W + 224` (`absorb_ok`).
-/

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
      rw [ofNat_sub (by omega) (by omega)]; rfl]

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (W : Addr) (Q : Addr) (c j : Nat) (t₀ t : State) : Prop where
  x11 : t.gpr .x11 = Q + BitVec.ofNat 64 (16 * j)
  x14 : t.gpr .x14 = W + BitVec.ofNat 64 (768 + 16 * j)
  x15 : t.gpr .x15 = BitVec.ofNat 64 (c - j)
  frame : Frame [⟨W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (W + BitVec.ofNat 64 768) j = elemsAt t₀.mem Q j
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
  rev : (⟨Q, k⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 768, 1280⟩

namespace Src

variable {p : Prm} {s : State} {Q : Addr} {n : Nat} (h : Src p s Q n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : Src p s (Q + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (Q.toNat + k) (2 ^ 64)
    omega
  y := h.y.sub_left (Offset.sub_base Q (by omega))
  rev := h.rev.sub_left (Offset.sub_base Q (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src p s Q k where
  rd := Proof.AesGcm.AArch64.covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : Src p s (Q + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Src

/-- A buffer apart from `W`. -/
theorem Src.ofW {p : Prm} (_L : Lay p) {s : State} {Q : Addr} {n : Nat} (hc : Covers [⟨Q, n⟩] (s.rd ++ s.wr))
    (hlt : n < 2 ^ 64) (hw : Q.toNat + n ≤ 2 ^ 64) (hd : (⟨Q, n⟩ : Region).Disjoint ⟨p.W, 4096⟩) : Src p s Q n :=
  ⟨hc, hlt, hw, hd.sub_right (Lay.wSub (by decide)), hd.sub_right (Lay.wSub (by decide))⟩

/-- `revLoop`: `c` blocks at `Q` copied to `W + 768`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : Prm} (L : Lay p) {t₀ : State} (E : Env p t₀) {Q : Addr} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : Src p t₀ Q (16 * c)) (h11 : t₀.gpr .x11 = Q)
    (h14 : t₀.gpr .x14 = p.W + BitVec.ofNat 64 768) (h15 : t₀.gpr .x15 = BitVec.ofNat 64 c) :
    WP isa revLoop t₀ fun t => Frame [⟨p.W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (p.W + BitVec.ofNat 64 768) c = elemsAt t₀.mem Q c ∧
      Others revRegs t₀ t ∧ t.sp = t₀.sp ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  have I₀ : RInv p.W Q c 0 t₀ t₀ := ⟨by rw [h11, Nat.mul_zero, BitVec.add_zero], by rw [h14],
    by rw [h15, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    fun _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block revBody) (c := .nonzero .x .x15)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ RInv p.W Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have hw := L.ww
  have rq₀ := in_off (d := 16 * j) (n := 8) hQ.rd (by omega) hQ.lt
  have rq₈ := in_off (d := 16 * j + 8) (n := 8) hQ.rd (by omega) hQ.lt
  rw [← add_ofNat_assoc] at rq₈
  have ww₀ := E.perm.wW (d := 768 + 16 * j) (n := 8) (by omega)
  have ww₈ := E.perm.wW (d := 768 + 16 * j + 8) (n := 8) (by omega)
  rw [← add_ofNat_assoc] at ww₈
  rw [← I.rd, ← I.wr] at rq₀ rq₈
  rw [← I.wr] at ww₀ ww₈
  obtain ⟨t', run', hm', x11', x14', x15', ho', sp', rd', wr'⟩ :=
    revStep_ok (j := c - j - 1) (by omega) I.x11 I.x14 (by rw [I.x15]; congr 1; omega) rq₀ rq₈ ww₀ ww₈
  refine WP.of_runBlock ⟨t', run', ?_⟩
  -- The source is outside the copies.
  have src : ∀ d, d + 8 ≤ 16 * c → t.mem.readW (Q + BitVec.ofNat 64 d) 64 = t₀.mem.readW (Q + BitVec.ofNat 64 d) 64 :=
    fun d hd => I.frame.readW (r := ⟨Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base Q (by omega))).sub_right (Offset.sub p.W (by omega) (by omega)))
      (by decide)
  have c₁ : (⟨p.W + BitVec.ofNat 64 768, 16 * c⟩ : Region).Contains (p.W + BitVec.ofNat 64 (768 + 16 * j)) (64 / 8) :=
    Offset.contains p.W (by omega) (by omega) (by omega)
  have c₂ : (⟨p.W + BitVec.ofNat 64 768, 16 * c⟩ : Region).Contains
      (p.W + BitVec.ofNat 64 (768 + 16 * j) + BitVec.ofNat 64 8) (64 / 8) := by
    rw [add_ofNat_assoc]; exact Offset.contains p.W (by omega) (by omega) (by omega)
  have fr : Frame [⟨p.W + BitVec.ofNat 64 (768 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', Proof.Gcm.AArch64.storeMem, BitVec.add_zero]; exact Proof.Cmac.frame_store2 _ _ _
  have I' : RInv p.W Q c (j + 1) t₀ t' := by
    refine ⟨by rw [x11', add_ofNat_assoc]; congr 2, by rw [x14', add_ofNat_assoc]; congr 2,
      by rw [x15', Nat.sub_sub], ?_, ?_, fun r hr => by rw [ho' r hr, I.others r hr],
      by rw [sp', I.sp], by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · rw [hm', Proof.Gcm.AArch64.storeMem, BitVec.add_zero]
      exact (I.frame.writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂
    · have s₈ := src (16 * j + 8) (by omega)
      rw [← add_ofNat_assoc] at s₈
      rw [blocksAt_succ, Proof.AesGcm.AArch64.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint p.W (.inl (by omega)) (by omega) (by omega)) (by omega), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', Proof.Gcm.AArch64.blockAt_storeMem,
        GcmSiv.ofBytes_bytesAt, src (16 * j) (by omega), s₈]
  have ev := eval_nonzero x15' (show c - j - 1 < 2 ^ 64 by omega)
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, I'.others, I'.sp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (j + 1), by omega, j + 1, rfl, by omega, I'⟩

/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the reversed blocks and
`vg_ghash`'s working space. -/
abbrev absR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 768, 1280⟩]

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
  refine WP.ite (decide (m / 1024 = 0)) (eval_zero x10₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine WP.run ⟨_, by grun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, ho₁ .x28 (by decide), h28, lsr_ofNat _ _ hm]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_write, hr, ite_false]; exact ho₁ r (by simpa using hr)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine WP.run ⟨_, by grun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, movz_lit (show 64 < 2 ^ 16 by decide)]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_write, hr, ite_false]; exact ho₁ r (by simpa using hr)

/-- A chunk up to its call: up to 64 blocks reversed at `W + 768`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : Prm) (Q : Addr) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (p.W + BitVec.ofNat 64 64) (p.W + BitVec.ofNat 64 80) (p.W + BitVec.ofNat 64 768)
    (p.W + BitVec.ofNat 64 1792) k
  env : Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  x27 : t₅.gpr .x27 = Q + BitVec.ofNat 64 (16 * k)
  x28 : t₅.gpr .x28 = BitVec.ofNat 64 (m - 16 * k)
  frame : Frame [⟨p.W + BitVec.ofNat 64 768, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (p.W + BitVec.ofNat 64 768) k = elemsAt t.mem Q k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa chunkPre t (ChunkPre p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (chunkLen_ok hm h28) fun t₁ ⟨x10₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨t₂, run₂, x11₂, x14₂, x15₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x11 .x27, Impl.AesGcm.AArch64.ptr .x14 .x19 revO, Impl.AesGcm.AArch64.mov .x15 .x10]
        t₁ = some t₂ ∧
      t₂.gpr .x11 = Q ∧ t₂.gpr .x14 = p.W + BitVec.ofNat 64 768 ∧
      t₂.gpr .x15 = BitVec.ofNat 64 (min (m / 16) 64) ∧ Others [.x11, .x14, .x15] t₁ t₂ ∧ t₂.mem = t₁.mem ∧
      t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    · simp [gpr_write, ho₁ .x27 (by decide), h27]
    · simp [gpr_write, ho₁ .x19 (by decide), E.x19]
    · simp [gpr_write, x10₁]
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  have E₂ : Env p t₂ := E.keep (fun r hr => by
      rw [ho₂ r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ho₁ r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)])
    (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  have hQ₂ : Src p t₂ Q (16 * min (m / 16) 64) := (hQ.take (by omega)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (revLoop_ok L E₂ hk1 (by omega) hQ₂ x11₂ x14₂ x15₂)
    fun t₃ ⟨fr₃, out₃, ho₃, sp₃, rd₃, wr₃⟩ => ?_)
  have E₃ : Env p t₃ := E₂.keep (fun r hr => ho₃ r (by
    simp only [envRegs, revRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have x10₃ : t₃.gpr .x10 = BitVec.ofNat 64 (min (m / 16) 64) := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), x10₁]
  have x27₃ : t₃.gpr .x27 = Q := by rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h27]
  have x28₃ : t₃.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h28]
  have m₂₁ : t₂.mem = t.mem := by rw [m₂, m₁]
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
  case n_lt => omega
  case hy => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case hs => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case yd => exact L.w_w (.inl (by omega)) (by decide) (by omega)
  case ys => exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case ds => exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case reads =>
    exact covers_append (covers_cons (E₃.perm.wCR (by decide)) (covers_cons (E₃.perm.wCR (by omega)) covers_nil))
      (covers_cons (E₃.perm.wCR (by decide)) (covers_cons (E₃.perm.wCR (by decide)) covers_nil))
  case writes => exact covers_cons (E₃.perm.wC (by decide)) (covers_cons (E₃.perm.wC (by decide)) covers_nil)
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x27₃, x10₃, ofNat_lsl,
      add_ofNat_assoc]
    congr 2; omega
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x28₃, x10₃, ofNat_lsl]
    rw [ofNat_sub (by omega) hm]; congr 2; omega

theorem chunk_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q)
    (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (chunk v.callees) t (ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega
  refine WP.seq (WP.mono (chunkPre_ok L E hm h16 hQ h27 h28) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call v.gh Pr.call) fun t₆ P => ?_)
  have E₆ : Env p t₆ := Pr.env.of_saved P.saved P.sp P.rd P.wr
  have x28₆ : t₆.gpr .x28 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide) (by decide), Pr.x28]
  have dH : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 768, 16 * min (m / 16) 64⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨p.W + BitVec.ofNat 64 768, 16 * min (m / 16) 64⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
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
    rw [lsr_ofNat _ _ (by omega)]
  · simp only [mem_write]
    refine (Pr.frame.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
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
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- A buffer apart from `W` misses what absorbing writes. -/
theorem absorbR_buf {p : Prm} {Q : Addr} {k : Nat} (hd : (⟨Q, k⟩ : Region).Disjoint ⟨p.W, 4096⟩) :
    ∀ r ∈ absorbR p.W, (⟨Q, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hd.sub_right (Lay.wSub (by decide))

theorem absR_sub (W : Addr) : ∀ r ∈ absR W, ∃ r' ∈ absorbR W, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : Absorbed p rs xs t t₁) (h₂ : Absorbed p rs ys t₁ t₂) : Absorbed p rs (xs ++ ys) t t₂ := by
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
  (hQ.slice (by omega)).of_eq I.abs.rd I.abs.wr

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
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega)
  have C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.y
      · exact hs.rev) (by omega)] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.x27, add_ofNat_assoc, Nat.mul_add],
    by rw [C.x28]; congr 1; omega⟩, by rw [C.x9]; congr 1; omega⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h27 : t.gpr .x27 = Q)
    (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (.loop (chunk v.callees) (.nonzero .x .x9)) t fun t' =>
      Absorbed p (absR p.W) (elemsAt t.mem Q (m / 16)) t t' ∧
      t'.gpr .x27 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t'.gpr .x28 = BitVec.ofNat 64 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk v.callees) (c := .nonzero .x .x9)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega, CInv.zero E h27 h28⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_ok v L I.abs.env (by omega) (by omega) (I.src hQ hd) I.x27 I.x28) fun t'' C => ?_
  obtain ⟨I', x9⟩ := I.step L hm hQ hd C
  have ev := eval_nonzero x9 (by omega)
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega), he ▸ I'.abs, by rw [I'.x27, he], by rw [I'.x28, he]; congr 1; omega⟩
  · right
    exact ⟨ev.trans (by simp; omega), m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.AArch64
