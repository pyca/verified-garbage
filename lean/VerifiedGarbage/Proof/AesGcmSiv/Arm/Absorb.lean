import VerifiedGarbage.Proof.AesGcmSiv.Arm.Keys
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# AES-GCM-SIV on ARMv7: POLYVAL (`chunk`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 432` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); chunks follow each other until fewer than 16
bytes are left (`chunks_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (GhCall GhPost gh_call below add_ofNat_zero add_ofNat_assoc add32_ofNat_assoc covers_cons
  covers_nil covers_append' covers_off covers_prefix eval_ne' eval_eq' z_cmp ofNat_sub32 ofNat_add32 toNat32
  mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags
  rd_subFlags wr_subFlags)

/-! ## Reversing blocks -/

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.ldr .r0 .r4 12, .ldr .r1 .r4 8, .ldr .r12 .r4 4, .ldr .lr .r4 0, .rev .r0 .r0, .rev .r1 .r1,
    .rev .r12 .r12, .rev .lr .lr, .str .r0 .r2 0, .str .r1 .r2 4, .str .r12 .r2 8, .str .lr .r2 12,
    Impl.AesGcm.Arm.addI .r4 .r4 16, Impl.AesGcm.Arm.addI .r2 .r2 16, .subs .r3 .r3 (Impl.AesGcm.Arm.imm 1)]

/-- The registers `revLoop` writes. -/
abbrev revRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r12, .lr]

/-- What one step of `revLoop` stores: the words of the block at `S` in the
other order, each reversed. -/
def revMem (m : Mem) (S P : Addr) : Mem :=
  Proof.Cmac.store4 m P (rev (m.readW (S + BitVec.ofNat 64 12) 32)) (rev (m.readW (S + BitVec.ofNat 64 8) 32))
    (rev (m.readW (S + BitVec.ofNat 64 4) 32)) (rev (m.readW S 32))

theorem revStep_ok {t : State} {S P : BitVec 32} {j : Nat} (hj : j + 1 < 2 ^ 32)
    (hS : ∀ o, o < 16 → State.addr (S + BitVec.ofNat 32 o) = State.addr S + BitVec.ofNat 64 o)
    (hP : ∀ o, o < 16 → State.addr (P + BitVec.ofNat 32 o) = State.addr P + BitVec.ofNat 64 o)
    (h4 : t.gpr .r4 = S) (h2 : t.gpr .r2 = P) (h3 : t.gpr .r3 = BitVec.ofNat 32 (j + 1))
    (hr : Covers [⟨State.addr S, 16⟩] (t.rd ++ t.wr)) (hw : Covers [⟨State.addr P, 16⟩] t.wr) :
    ∃ t' : State, runBlock isa revBody t = some t' ∧ t'.mem = revMem t.mem (State.addr S) (State.addr P) ∧
      t'.gpr .r4 = S + BitVec.ofNat 32 16 ∧ t'.gpr .r2 = P + BitVec.ofNat 32 16 ∧
      t'.gpr .r3 = BitVec.ofNat 32 j ∧ t'.z = decide (j = 0) ∧ Others revRegs t t' ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ : InRegions (t.rd ++ t.wr) (State.addr S) 4 := by simpa using in_off hr (d := 0) (n := 4) (by decide) (by decide)
  have r₄ := in_off hr (d := 4) (n := 4) (by decide) (by decide)
  have r₈ := in_off hr (d := 8) (n := 4) (by decide) (by decide)
  have r₁₂ := in_off hr (d := 12) (n := 4) (by decide) (by decide)
  have w₀ : InRegions t.wr (State.addr P) 4 := by simpa using in_off hw (d := 0) (n := 4) (by decide) (by decide)
  have w₄ := in_off hw (d := 4) (n := 4) (by decide) (by decide)
  have w₈ := in_off hw (d := 8) (n := 4) (by decide) (by decide)
  have w₁₂ := in_off hw (d := 12) (n := 4) (by decide) (by decide)
  refine ⟨_, by srun [h4, h2, h3, add_ofNat_zero, hS, hP, r₀, r₄, r₈, r₁₂, w₀, w₄, w₈, w₁₂], ?_⟩
  refine ⟨?_, by simp [gpr_setReg, h4], by simp [gpr_setReg, h2], ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, revMem,
      Proof.Cmac.store4]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h3]
    rw [ofNat_sub32 (by omega) (by omega)]; rfl
  · simp only [z_setReg, z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h3]
    rw [z_cmp (by omega) (by decide)]
    congr 1; apply propext; omega
where
  in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k) (hk : k < 2 ^ 64) :
      InRegions rs (p + BitVec.ofNat 64 d) n := Proof.AesGcm.Arm.in_off h hd hk

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- The block `revMem` stores, as GHASH reads it: POLYVAL's field element of
the source. -/
theorem revMem_block (m : Mem) (S P : Addr) :
    Spec.Gcm.blockAt (revMem m S P) P = Spec.GcmSiv.ofBytes (bytesAt m S 16) := by
  rw [revMem, blockAt_store4, rev_rev, rev_rev, rev_rev, rev_rev, Proof.Gcm.Arm.w4, GcmSiv.Words32.ofBytes_bytesAt]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (p : Prm) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨State.addr Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  y : (⟨State.addr Q, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 80, 16⟩
  rev : (⟨State.addr Q, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 432, 1280⟩
  stk : (below p.SP).Disjoint ⟨State.addr Q, k⟩

namespace Src

variable {p : Prm} {s : State} {Q : BitVec 32} {n : Nat} (h : Src p s Q n)
include h

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem addr {j : Nat} (hj : j < n) : State.addr (Q + BitVec.ofNat 32 j) = State.addr Q + BitVec.ofNat 64 j :=
  addr_add (by have := h.wrap; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 32 j).toNat = Q.toNat + j := by
  have := h.wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src p s Q k where
  rd := covers_prefix h.rd hk
  wrap := by have := h.wrap; omega
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : Src p s (Q + BitVec.ofNat 32 a) k := by
  have e := h.addr ha
  have hs : Region.Sub ⟨State.addr Q + BitVec.ofNat 64 a, k⟩ ⟨State.addr Q, n⟩ := Offset.sub_base _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact covers_off h.rd hk h.lt
  · rw [h.toNat_add ha]; have := h.wrap; omega
  · rw [e]; exact h.y.sub_left hs
  · rw [e]; exact h.rev.sub_left hs
  · rw [e]; exact h.stk.sub_right hs

end Src

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (p : Prm) (Q : BitVec 32) (c j : Nat) (t₀ t : State) : Prop where
  r4 : t.gpr .r4 = Q + BitVec.ofNat 32 (16 * j)
  r2 : t.gpr .r2 = p.W + BitVec.ofNat 32 (432 + 16 * j)
  r3 : t.gpr .r3 = BitVec.ofNat 32 (c - j)
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (State.addr p.W + BitVec.ofNat 64 432) j = elemsAt t₀.mem (State.addr Q) j
  others : Others revRegs t₀ t
  sp : t.sp = t₀.sp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

/-- `revLoop`: `c` blocks at `Q` copied to `W + 432`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : Prm} (L : Lay p) {t₀ : State} (E : Env p t₀) {Q : BitVec 32} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : Src p t₀ Q (16 * c)) (h4 : t₀.gpr .r4 = Q)
    (h2 : t₀.gpr .r2 = p.W + BitVec.ofNat 32 432) (h3 : t₀.gpr .r3 = BitVec.ofNat 32 c) :
    WP isa revLoop t₀ fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (State.addr p.W + BitVec.ofNat 64 432) c = elemsAt t₀.mem (State.addr Q) c ∧
      t.gpr .r4 = Q + BitVec.ofNat 32 (16 * c) ∧
      Others revRegs t₀ t ∧ t.sp = t₀.sp ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  have hw := L.ww
  have I₀ : RInv p Q c 0 t₀ t₀ := ⟨by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h2],
    by rw [h3, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    fun _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ RInv p Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have eS : State.addr (Q + BitVec.ofNat 32 (16 * j)) = State.addr Q + BitVec.ofNat 64 (16 * j) :=
    hQ.addr (by omega)
  have hS : ∀ o, o < 16 → State.addr (Q + BitVec.ofNat 32 (16 * j) + BitVec.ofNat 32 o) =
      State.addr (Q + BitVec.ofNat 32 (16 * j)) + BitVec.ofNat 64 o := fun o ho => by
    rw [add32_ofNat_assoc, hQ.addr (by omega), eS, add_ofNat_assoc]
  have hP : ∀ o, o < 16 → State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j) + BitVec.ofNat 32 o) =
      State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j)) + BitVec.ofNat 64 o := fun o ho => by
    rw [add32_ofNat_assoc, L.wA (by omega), L.wA (by omega), add_ofNat_assoc]
  have hr : Covers [⟨State.addr (Q + BitVec.ofNat 32 (16 * j)), 16⟩] (t.rd ++ t.wr) := by
    rw [I.rd, I.wr, eS]; exact covers_off hQ.rd (by omega) hQ.lt
  have hwr : Covers [⟨State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j)), 16⟩] t.wr := by
    rw [I.wr, L.wA (by omega)]; exact E.perm.wC (by omega)
  obtain ⟨t', run', hm', r4', r2', r3', z', ho', sp', rd', wr'⟩ :=
    revStep_ok (j := c - j - 1) (by omega) hS hP I.r4 I.r2 (by rw [I.r3]; congr 1; omega) hr hwr
  refine WP.of_runBlock ⟨t', run', ?_⟩
  rw [eS, L.wA (by omega)] at hm'
  -- The source is outside the copies.
  have src : bytesAt t.mem (State.addr Q + BitVec.ofNat 64 (16 * j)) 16 =
      bytesAt t₀.mem (State.addr Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.AesGcm.Arm.bytesAt_frame I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub _ (by omega) (by omega)))
      (by decide)
  have fr : Frame [⟨State.addr p.W + BitVec.ofNat 64 (432 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', revMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have I' : RInv p Q c (j + 1) t₀ t' := by
    refine ⟨by rw [r4', add32_ofNat_assoc, Nat.mul_succ], by rw [r2', add32_ofNat_assoc, Nat.mul_succ, Nat.add_assoc],
      by rw [r3', Nat.sub_sub], ?_, ?_, fun r hr => by rw [ho' r hr, I.others r hr],
      by rw [sp', I.sp], by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩)
    · rw [blocksAt_succ, Proof.AesGcm.Arm.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', revMem_block, src]
  have ev := eval_ne' z'
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.r4, I'.others, I'.sp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (j + 1), by omega, j + 1, rfl, by omega, I'⟩


/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the reversed blocks,
`vg_ghash`'s working space and the stack below `SP`. -/
abbrev absR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 432, 1280⟩, below SP]

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (p : Prm) (Q : BitVec 32) (m k : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = Q + BitVec.ofNat 32 (16 * k)
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (m - 16 * k)
  z : t'.z = decide ((m - 16 * k) / 16 = 0)
  frame : Frame (absR (State.addr p.W) p.SP) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (State.addr p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80)) (elemsAt t.mem (State.addr Q) k)

/-- `chunkLen`: the number of blocks of the chunk. -/
theorem chunkLen_ok {t : State} {m : Nat} (hm : m < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunkLen t fun t' => t'.gpr .r6 = BitVec.ofNat 32 (min (m / 16) 64) ∧
      Others [.r6] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, r6₁, z₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.mov .r6 (.shifted .r5 .lsr 10), .cmp .r6 (Impl.AesGcm.Arm.imm 0)] t = some t₁ ∧
      t₁.gpr .r6 = BitVec.ofNat 32 (m / 1024) ∧ t₁.z = decide (m / 1024 = 0) ∧ Others [.r6] t t₁ ∧
      t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h5], ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, ofNat_lsr32 hm]
    · simp only [z_subFlags, gpr_setReg, ite_true, ofNat_lsr32 hm]
      rw [z_cmp (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (m / 1024 = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_setReg, ite_true, ho₁ .r5 (by decide), h5, ofNat_lsr32 hm]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false]; exact ho₁ r (by simpa using hr)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_setReg, ite_true]
      congr 1; omega
    · simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false]; exact ho₁ r (by simpa using hr)

/-- A chunk up to its call: up to 64 blocks reversed at `W + 432`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : Prm) (Q : BitVec 32) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (p.W + BitVec.ofNat 32 64) (p.W + BitVec.ofNat 32 80) (p.W + BitVec.ofNat 32 432)
    (p.W + BitVec.ofNat 32 1456) k
  env : Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  r4 : t₅.gpr .r4 = Q + BitVec.ofNat 32 (16 * k)
  r5 : t₅.gpr .r5 = BitVec.ofNat 32 (m - 16 * k)
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (State.addr p.W + BitVec.ofNat 64 432) k = elemsAt t.mem (State.addr Q) k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q) (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunkPre t (ChunkPre p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (chunkLen_ok hm h5) fun t₁ ⟨r6₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨t₂, run₂, r2₂, r3₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [Impl.AesGcm.Arm.addI .r2 .r11 revO, .mov .r3 (.reg .r6)] t₁ = some t₂ ∧
      t₂.gpr .r2 = p.W + BitVec.ofNat 32 432 ∧ t₂.gpr .r3 = BitVec.ofNat 32 (min (m / 16) 64) ∧
      Others [.r2, .r3] t₁ t₂ ∧ t₂.mem = t₁.mem ∧ t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by srun [], ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, ho₁ .r11 (by decide), E.r11]
    · simp [gpr_setReg, r6₁]
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  have E₂ : Env p t₂ := (E.of_others ho₁ sp₁ rd₁ wr₁).of_others ho₂ sp₂ rd₂ wr₂
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  have hQ₂ : Src p t₂ Q (16 * min (m / 16) 64) :=
    (hQ.take (by omega)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have h4₂ : t₂.gpr .r4 = Q := by rw [ho₂ _ (by decide), ho₁ _ (by decide), h4]
  refine WP.seq (WP.mono (revLoop_ok L E₂ hk1 (by omega) hQ₂ h4₂ r2₂ r3₂)
    fun t₃ ⟨fr₃, out₃, r4₃, ho₃, sp₃, rd₃, wr₃⟩ => ?_)
  have E₃ : Env p t₃ := E₂.of_others ho₃ sp₃ rd₃ wr₃
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (min (m / 16) 64) := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), r6₁]
  have r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 m := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h5]
  have m₂₁ : t₂.mem = t.mem := by rw [m₂, m₁]
  rw [m₂₁] at fr₃ out₃
  refine Proof.AesGcm.Arm.WP.run ⟨_, by simp only [chunkArgs]; srun [], rfl⟩ fun t₄ ht₄ => ?_
  subst ht₄
  refine ⟨⟨?r0, ?r1, ?r2, ?r3, ?r12, ?hsp, ?fH, ?fY, ?fD, ?fS, ?hy, ?hs, ?yd, ?ys, ?ds, ?bh, ?bY, ?bd, ?bs,
      ?reads, ?writes⟩,
    E₃.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by simp only [rd_setReg]; rw [rd₃, rd₂, rd₁],
    by simp only [wr_setReg]; rw [wr₃, wr₂, wr₁], ?_, ?_, by simp only [mem_setReg]; exact fr₃,
    by simp only [mem_setReg]; exact out₃⟩
  case regs =>
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  case r0 => simp [gpr_setReg, E₃.r11]
  case r1 => simp [gpr_setReg, E₃.r11]
  case r2 => simp [gpr_setReg, E₃.r11]
  case r3 => simp [gpr_setReg, r6₃]
  case r12 => simp [gpr_setReg, E₃.r11]
  case hsp => simp only [sp_setReg]; rw [E₃.sp]; exact L.sp8
  case fH => rw [L.wN (by decide)]; omega
  case fY => rw [L.wN (by decide)]; omega
  case fD => rw [L.wN (by decide)]; omega
  case fS => rw [L.wN (by decide)]; omega
  case hy => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case hs => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case yd => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  case ys => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case ds => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  case bh => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case bY => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case bd => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by omega)
  case bs => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case reads =>
    simp only [rd_setReg, wr_setReg]
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_append' (covers_cons (E₃.perm.wCR (by decide)) covers_nil)
      (covers_cons (E₃.perm.wCR (by omega)) covers_nil)
  case writes =>
    simp only [wr_setReg]
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_cons (E₃.perm.wC (by decide)) (covers_cons (E₃.perm.wC (by decide)) covers_nil)
  · simp [gpr_setReg, r4₃]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, r5₃, r6₃, ofNat_lsl32]
    rw [ofNat_sub32 (by omega) hm]; congr 2; omega


/-- `wholeLeft`: `Z` set iff fewer than 16 of the `r` bytes are left. -/
theorem wholeLeft_ok {t : State} {r : Nat} (hr : r < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa wholeLeft t = some t' ∧ t'.z = decide (r / 16 = 0) ∧ Others [.r12] t t' ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by simp only [wholeLeft]; srun [h5], ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
  simp only [z_subFlags, gpr_setReg, ite_true, ofNat_lsr32 hr]
  rw [z_cmp (by omega) (by decide)]

theorem chunk_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunk t (ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : 16 * min (m / 16) 64 ≤ 1024 := by omega
  refine WP.seq (WP.mono (chunkPre_ok L E hm h16 hQ h4 h5) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call Pr.call) fun t₆ P => ?_)
  have E₆ : Env p t₆ := Pr.env.of_saved P.saved P.sp P.rd P.wr
  have r5₆ : t₆.gpr .r5 = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide) (by decide), Pr.r5]
  have fr := P.frame
  have out₆ := P.out
  simp only [L.wA (show 64 < 3760 by decide), L.wA (show 80 < 3760 by decide),
    L.wA (show 432 < 3760 by decide), L.wA (show 1456 < 3760 by decide), Pr.env.sp] at fr out₆
  have dH : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 432, 16 * min (m / 16) 64⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 432, 16 * min (m / 16) 64⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  rw [Proof.AesGcm.Arm.blockAt_frame Pr.frame dH, Proof.AesGcm.Arm.blockAt_frame Pr.frame dY, Pr.out] at out₆
  obtain ⟨t₇, run₇, z₇, ho₇, m₇, sp₇, rd₇, wr₇⟩ := wholeLeft_ok (by omega) r5₆
  refine WP.of_runBlock ⟨t₇, run₇, E₆.of_others ho₇ sp₇ rd₇ wr₇, by rw [rd₇, P.rd, Pr.rd],
    by rw [wr₇, P.wr, Pr.wr], ?_, by rw [ho₇ _ (by decide), r5₆], z₇, ?_, by rw [m₇]; exact out₆⟩
  · rw [ho₇ _ (by decide), P.saved _ (by decide) (by decide), Pr.r4]
  · rw [m₇]
    refine (Pr.frame.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-! ## Absorbing -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    elemsAt m Q (d + k) = elemsAt m Q d ++ elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, add_ofNat_assoc, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : elemsAt m' Q k = elemsAt m Q k := by
  unfold elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.Arm.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 176`. -/
abbrev absorbR (W : Addr) (SP : BitVec 32) : List Region := ⟨W + BitVec.ofNat 64 176, 16⟩ :: absR W SP

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (p : Prm) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (State.addr p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80)) xs

/-- What absorbing a string leaves. -/
abbrev AbsPost (p : Prm) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop :=
  Absorbed p (absorbR (State.addr p.W) p.SP) xs t t'

theorem absorbR_H {p : Prm} (L : Lay p) :
    ∀ r ∈ absorbR (State.addr p.W) p.SP, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm

/-- A buffer apart from `W` and the stack below `SP` misses what absorbing writes. -/
theorem absorbR_buf {p : Prm} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩)
    (hb : (below p.SP).Disjoint ⟨P, k⟩) : ∀ r ∈ absorbR (State.addr p.W) p.SP, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hb.symm

theorem absR_sub (W : Addr) (SP : BitVec 32) : ∀ r ∈ absR W SP, ∃ r' ∈ absorbR W SP, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : Absorbed p rs xs t t₁) (h₂ : Absorbed p rs ys t₁ t₂) : Absorbed p rs (xs ++ ys) t t₂ := by
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.Arm.blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {p : Prm} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : Absorbed p rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Absorbed p rs' xs t t' :=
  ⟨h.env, h.rd, h.wr, h.frame.sub hs, h.out⟩

theorem AbsPost.trans {p : Prm} (L : Lay p) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : AbsPost p xs t t₁) (h₂ : AbsPost p ys t₁ t₂) : AbsPost p (xs ++ ys) t t₂ :=
  Absorbed.trans (absorbR_H L) h₁ h₂

theorem Absorbed.of_chunk {p : Prm} {Q : BitVec 32} {m k : Nat} {t t' : State}
    (h : ChunkPost p Q m k t t') : Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) k) t t' :=
  ⟨h.env, h.rd, h.wr, h.frame, h.out⟩

theorem Absorbed.of_eq {p : Prm} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : Absorbed p rs xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    Absorbed p rs xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absR_H {p : Prm} (L : Lay p) :
    ∀ r ∈ absR (State.addr p.W) p.SP, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => absorbR_H L r (List.mem_cons_of_mem _ hr)

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (p : Prm) (σ : State) (Q : BitVec 32) (m d : Nat) (t : State) : Prop where
  abs : Absorbed p (absR (State.addr p.W) p.SP) (elemsAt σ.mem (State.addr Q) d) σ t
  r4 : t.gpr .r4 = Q + BitVec.ofNat 32 (16 * d)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (m - 16 * d)

theorem CInv.src {p : Prm} {σ t : State} {Q : BitVec 32} {m d : Nat} (I : CInv p σ Q m d t)
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) :
    Src p t (Q + BitVec.ofNat 32 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
  (hQ.slice (by omega) (by omega)).of_eq I.abs.rd I.abs.wr

theorem CInv.zero {p : Prm} {σ : State} (E : Env p σ) {Q : BitVec 32} {m : Nat} (h4 : σ.gpr .r4 = Q)
    (h5 : σ.gpr .r5 = BitVec.ofNat 32 m) : CInv p σ Q m 0 σ :=
  ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
    by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h5, Nat.mul_zero, Nat.sub_zero]⟩

/-- A chunk, in the chunks. -/
theorem CInv.step {p : Prm} (L : Lay p) {σ t t' : State} {Q : BitVec 32} {m d : Nat}
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) (I : CInv p σ Q m d t)
    (C : ChunkPost p (Q + BitVec.ofNat 32 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    CInv p σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.z = decide (m / 16 - (d + min (m / 16 - d) 64) = 0) := by
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega) (by omega)
  have ea := hQ.addr (j := 16 * d) (by omega)
  have C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.y
      · exact hs.rev
      · exact hs.stk.symm) (by omega), ea] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.r4, add32_ofNat_assoc, Nat.mul_add],
    by rw [C.r5]; congr 1; omega⟩, by rw [C.z]; congr 1; apply propext; omega⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa (.loop chunk .ne) t fun t' =>
      Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) (m / 16)) t t' ∧
      t'.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega, CInv.zero E h4 h5⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_ok L I.abs.env (by omega) (by omega) (I.src hQ hd) I.r4 I.r5) fun t'' C => ?_
  obtain ⟨I', z⟩ := I.step L hQ hd C
  have ev := eval_ne' z
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega), he ▸ I'.abs, by rw [I'.r4, he], by rw [I'.r5, he]; congr 1; omega⟩
  · right
    exact ⟨ev.trans (by simp; omega), m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.Arm
