import VerifiedGarbage.Proof.AesGcmSiv.X86.Keys
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# AES-GCM-SIV on x86: POLYVAL (`chunk`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 768` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); chunks follow each other until fewer than 16
bytes are left (`chunks_ok`). The pointer is in `esi`, the number of bytes
left at `W + nO` and the number of blocks of the chunk at `W + iO`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add slotv slotv_eq GcmImpl readW_writeW_off covers_off
  in_off covers_cons covers_nil sub_beq32)

/-! ## Reversing blocks -/

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 12)), .bswap .eax, .store (at_ .edx 0) .eax,
    .mov .eax (.mem (at_ .esi 8)), .bswap .eax, .store (at_ .edx 4) .eax, .mov .eax (.mem (at_ .esi 4)),
    .bswap .eax, .store (at_ .edx 8) .eax, .mov .eax (.mem (at_ .esi 0)), .bswap .eax, .store (at_ .edx 12) .eax,
    .alu .add .esi (imm 16), .alu .add .edx (imm 16), .alu .sub .ecx (imm 1)]

/-- What one step of `revLoop` stores: the words of the block at `S` in the
other order, each byte-reversed. -/
def revMem (m : Mem) (S P : Addr) : Mem :=
  Proof.Cmac.store4 m P (bswap (m.readW (S + BitVec.ofNat 64 12) 32)) (bswap (m.readW (S + BitVec.ofNat 64 8) 32))
    (bswap (m.readW (S + BitVec.ofNat 64 4) 32)) (bswap (m.readW (S + BitVec.ofNat 64 0) 32))

theorem ofNat_sub1 {j : Nat} (hj : j + 1 < 2 ^ 32) :
    BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 1 = BitVec.ofNat 32 j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 hj, toNat_ofNat32 (by decide), toNat_ofNat32 (by omega)]
  omega

theorem revStep_ok {t : State} {S P : BitVec 32} {j : Nat} (hj : j + 1 < 2 ^ 32)
    (fS : S.toNat + 16 ≤ 2 ^ 32) (fP : P.toNat + 16 ≤ 2 ^ 32)
    (hsp : (⟨w64 S, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩)
    (hsi : t.gpr .esi = S) (hdx : t.gpr .edx = P) (hcx : t.gpr .ecx = BitVec.ofNat 32 (j + 1))
    (hr : Covers [⟨w64 S, 16⟩] (t.rd ++ t.wr)) (hw : Covers [⟨w64 P, 16⟩] t.wr) :
    ∃ t' : State, runBlock isa revBody t = some t' ∧ t'.mem = revMem t.mem (w64 S) (w64 P) ∧
      t'.gpr .esi = S + BitVec.ofNat 32 16 ∧ t'.gpr .edx = P + BitVec.ofNat 32 16 ∧
      t'.gpr .ecx = BitVec.ofNat 32 j ∧ t'.zf = some (decide (j = 0)) ∧ t'.gpr .ebp = t.gpr .ebp ∧
      t'.gpr .esp = t.gpr .esp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have aS : ∀ {o}, o < 16 → w64 (S + BitVec.ofNat 32 o) = w64 S + BitVec.ofNat 64 o := fun ho => w64_add (by omega)
  have aP : ∀ {o}, o < 16 → w64 (P + BitVec.ofNat 32 o) = w64 P + BitVec.ofNat 64 o := fun ho => w64_add (by omega)
  have rS : ∀ {o}, o + 4 ≤ 16 → InRegions (t.rd ++ t.wr) (w64 S + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hr ho (by decide)
  have wP : ∀ {o}, o + 4 ≤ 16 → InRegions t.wr (w64 P + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hw ho (by decide)
  have sep : ∀ (m : Mem) (v : BitVec 32) {a b : Nat}, a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (w64 P + BitVec.ofNat 64 a) v).readW (w64 S + BitVec.ofNat 64 b) 32 =
        m.readW (w64 S + BitVec.ofNat 64 b) 32 := fun m v a b ha hb =>
    Proof.Cmac.readW_writeW_disj _ (hsp.symm.sub_left (Offset.sub_base _ ha) |>.sub_right (Offset.sub_base _ hb))
  refine ⟨_, by grun [hsi, hdx, hcx, aS, aP, rS, wP, sep], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hsi, hdx, sep, revMem, Proof.Cmac.store4, BitVec.add_zero]
  · gregs [hsi]
  · gregs [hdx]
  · gregs [hcx, ofNat_sub1 hj]
  · gmems [hcx, ofNat_sub1 hj]
    rw [show BitVec.ofNat 32 j = BitVec.ofNat 32 j - BitVec.ofNat 32 0 by simp, sub_beq32 (by omega) (by decide)]
  · gregs []
  · gregs []
  all_goals rfl

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- The block `revMem` stores, as GHASH reads it: POLYVAL's field element of
the source. -/
theorem revMem_block (m : Mem) (S P : Addr) :
    Spec.Gcm.blockAt (revMem m S P) P = Spec.GcmSiv.ofBytes (bytesAt m S 16) := by
  have b := blockAt_bswap (revMem m S P) P 0
  rw [BitVec.add_zero] at b
  rw [b, revMem, Proof.Cmac.store4]
  simp (disch := decide) only [Nat.reduceAdd, BitVec.add_zero, Mem.readW_writeW_self32, readW_writeW_off,
    bswap_bswap]
  have dj : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 →
      (⟨P + BitVec.ofNat 64 x, 4⟩ : Region).Disjoint ⟨P + BitVec.ofNat 64 y, 4⟩ :=
    fun h hx hy => Offset.disjoint P h (by omega) (by omega)
  have d₀ : ∀ y, 4 ≤ y → y + 4 ≤ 16 → (⟨P, 4⟩ : Region).Disjoint ⟨P + BitVec.ofNat 64 y, 4⟩ := fun y h₁ h₂ => by
    simpa using dj (x := 0) (y := y) (.inl h₁) (by decide) h₂
  simp only [Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 8) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 8) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (d₀ 4 (by decide) (by decide)).symm,
    Proof.Cmac.readW_writeW_disj _ (d₀ 8 (by decide) (by decide)).symm,
    Proof.Cmac.readW_writeW_disj _ (d₀ 12 (by decide) (by decide)).symm, Mem.readW_writeW_self32, bswap_bswap,
    BitVec.add_zero]
  rw [GcmSiv.Words32.ofBytes_bytesAt]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (p : Prm) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  y : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 80, 16⟩
  v : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩
  rev : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩
  stk : (stk p).Disjoint ⟨w64 Q, k⟩

namespace Src

variable {p : Prm} {s : State} {Q : BitVec 32} {n : Nat} (h : Src p s Q n)
include h

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem addr {j : Nat} (hj : j < n) : w64 (Q + BitVec.ofNat 32 j) = w64 Q + BitVec.ofNat 64 j :=
  w64_add (by have := h.wrap; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 32 j).toNat = Q.toNat + j :=
  toNat_add32 (by have := h.wrap; omega)

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src p s Q k where
  rd := covers_prefix h.rd hk
  wrap := by have := h.wrap; omega
  y := h.y.sub_left (Region.sub_prefix hk)
  v := h.v.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : Src p s (Q + BitVec.ofNat 32 a) k := by
  have e := h.addr ha
  have hs : Region.Sub ⟨w64 Q + BitVec.ofNat 64 a, k⟩ ⟨w64 Q, n⟩ := Offset.sub_base _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact covers_off h.rd hk h.lt
  · rw [h.toNat_add ha]; have := h.wrap; omega
  · rw [e]; exact h.y.sub_left hs
  · rw [e]; exact h.v.sub_left hs
  · rw [e]; exact h.rev.sub_left hs
  · rw [e]; exact h.stk.sub_right hs

end Src

/-- The block at `W + 224` as a chunk's source. -/
theorem srcB {p : Prm} {s : State} (L : Lay p) (P : Perm p s) : Src p s (p.W + BitVec.ofNat 32 224) 16 where
  rd := by rw [L.aW (by decide)]; exact P.wCR (by decide)
  wrap := by rw [L.nW (by decide)]; have := L.ww; omega
  y := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  v := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  rev := by rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  stk := by rw [L.aW (by decide)]; exact L.bw' (by decide)

/-- A buffer apart from `W` and the stack as a chunk's source. -/
theorem srcBuf {p : Prm} {s : State} {Q : BitVec 32} {k : Nat} (hr : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr))
    (hwrap : Q.toNat + k ≤ 2 ^ 32) (hw : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩)
    (hb : (stk p).Disjoint ⟨w64 Q, k⟩) : Src p s Q k :=
  ⟨hr, hwrap, hw.sub_right (Lay.wSub (by decide)), hw.sub_right (Lay.wSub (by decide)),
    hw.sub_right (Lay.wSub (by decide)), hb⟩

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (p : Prm) (Q : BitVec 32) (c j : Nat) (t₀ t : State) : Prop where
  esi : t.gpr .esi = Q + BitVec.ofNat 32 (16 * j)
  edx : t.gpr .edx = p.W + BitVec.ofNat 32 (768 + 16 * j)
  ecx : t.gpr .ecx = BitVec.ofNat 32 (c - j)
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (w64 p.W + BitVec.ofNat 64 768) j = elemsAt t₀.mem (w64 Q) j
  ebp : t.gpr .ebp = t₀.gpr .ebp
  esp : t.gpr .esp = t₀.gpr .esp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

theorem add32_ofNat_assoc (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `revLoop`: `c` blocks at `Q` copied to `W + 768`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : Prm} (L : Lay p) {t₀ : State} (E : Env p t₀) {Q : BitVec 32} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : Src p t₀ Q (16 * c)) (hsi : t₀.gpr .esi = Q)
    (hdx : t₀.gpr .edx = p.W + BitVec.ofNat 32 768) (hcx : t₀.gpr .ecx = BitVec.ofNat 32 c) :
    WP isa revLoop t₀ fun t => Frame [⟨w64 p.W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (w64 p.W + BitVec.ofNat 64 768) c = elemsAt t₀.mem (w64 Q) c ∧
      t.gpr .esi = Q + BitVec.ofNat 32 (16 * c) ∧ t.gpr .ebp = t₀.gpr .ebp ∧ t.gpr .esp = t₀.gpr .esp ∧
      t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  have hw := L.ww
  have I₀ : RInv p Q c 0 t₀ t₀ := ⟨by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hdx],
    by rw [hcx, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ RInv p Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have eS : w64 (Q + BitVec.ofNat 32 (16 * j)) = w64 Q + BitVec.ofNat 64 (16 * j) := hQ.addr (by omega)
  have eP : w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)) = w64 p.W + BitVec.ofNat 64 (768 + 16 * j) :=
    L.aW (by omega)
  have hr : Covers [⟨w64 (Q + BitVec.ofNat 32 (16 * j)), 16⟩] (t.rd ++ t.wr) := by
    rw [I.rd, I.wr, eS]; exact covers_off hQ.rd (by omega) hQ.lt
  have hwr : Covers [⟨w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)), 16⟩] t.wr := by
    rw [I.wr, eP]; exact E.perm.wC (by omega)
  have hsep : (⟨w64 (Q + BitVec.ofNat 32 (16 * j)), 16⟩ : Region).Disjoint
      ⟨w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)), 16⟩ := by
    rw [eS, eP]
    exact (hQ.rev.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub _ (by omega) (by omega))
  obtain ⟨t', run', hm', si', dx', cx', z', bp', sp', rd', wr'⟩ :=
    revStep_ok (j := c - j - 1) (by omega) (by rw [hQ.toNat_add (by omega)]; have := hQ.wrap; omega)
      (by rw [L.nW (by omega)]; omega) hsep I.esi I.edx (by rw [I.ecx]; congr 1; omega) hr hwr
  refine WP.of_runBlock ⟨t', run', ?_⟩
  rw [eS, eP] at hm'
  -- The source is outside the copies.
  have src : bytesAt t.mem (w64 Q + BitVec.ofNat 64 (16 * j)) 16 =
      bytesAt t₀.mem (w64 Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.AesGcm.X86.bytesAt_frame I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub _ (by omega) (by omega)))
      (by decide)
  have fr : Frame [⟨w64 p.W + BitVec.ofNat 64 (768 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', revMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have I' : RInv p Q c (j + 1) t₀ t' := by
    refine ⟨by rw [si', add32_ofNat_assoc, Nat.mul_succ], by rw [dx', add32_ofNat_assoc, Nat.mul_succ,
      Nat.add_assoc], by rw [cx', Nat.sub_sub], ?_, ?_, by rw [bp', I.ebp], by rw [sp', I.esp], by rw [rd', I.rd],
      by rw [wr', I.wr]⟩
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩)
    · rw [blocksAt_succ, Proof.AesGcm.X86.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', revMem_block, src]
  have ev := eval_ne z'
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.esi, I'.ebp, I'.esp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (j + 1), by omega, j + 1, rfl, by omega, I'⟩


/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the variables, the reversed
blocks and `vg_ghash`'s working space, and the stack below `SP`. -/
abbrev absR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 80, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩,
    stk p]

theorem inMut_absR (p : Prm) : InMut p (absR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_stk p

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (p : Prm) (Q : BitVec 32) (m k : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = Q + BitVec.ofNat 32 (16 * k)
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (m - 16 * k)
  z : t'.zf = some (decide ((m - 16 * k) / 16 = 0))
  frame : Frame (absR p) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (w64 p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80)) (elemsAt t.mem (w64 Q) k)

/-- `chunkLen`'s first block: `nO / 16` compared with 64. -/
theorem chunkLen1_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {m : Nat} (hm : m < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    ∃ t₁, runBlock isa [.mov .ecx (slot nO), .shift .shr .ecx 4, .alu .cmp .ecx (imm 64)] t = some t₁ ∧
      t₁.gpr .ecx = BitVec.ofNat 32 (m / 16) ∧ t₁.cf = some (decide (m / 16 < 64)) ∧ t₁.gpr .ebp = p.W ∧
      t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ t₁.mem = t.mem := by
  simp only [slotv_eq, nO] at hn
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gregs [hn, ofNat_lsr32 hm]
  · gmems [hn, ofNat_lsr32 hm]
    rw [toNat_ofNat32 (by omega), toNat_ofNat32 (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals gmems []

/-- `chunkLen`: the number of blocks of the chunk, in `ecx` and at `W + iO`. -/
theorem chunkLen_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {m : Nat} (hm : m < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa chunkLen t fun t' => Env p t' ∧ t'.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) ∧
      slotv t'.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 m ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t.mem t'.mem := by
  obtain ⟨t₁, run₁, cx₁, cf₁, bp₁, sp₁, si₁, rd₁, wr₁, m₁⟩ := chunkLen1_ok L E hm hn
  simp only [slotv_eq, nO] at hn
  have E₁ : Env p t₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁ m₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- `ecx := min (m / 16, 64)`, by the branch.
  have hk : ∀ t₂ : State, t₂.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) → Env p t₂ → t₂.gpr .esi = t.gpr .esi →
      t₂.rd = t.rd → t₂.wr = t.wr → t₂.mem = t.mem →
      WP isa (.block [.store (at_ .ebp iO) .ecx]) t₂ fun t' => Env p t' ∧
        t'.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) ∧
        slotv t'.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 m ∧
        t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
        Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t.mem t'.mem := by
    intro t₂ cx₂ E₂ si₂ rd₂ wr₂ m₂
    have f : Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t₂.mem
        (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 180) (BitVec.ofNat 32 (min (m / 16) 64))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have fm := frame_toMut f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
    refine WP.of_runBlock ⟨_, by grun [E₂.ebp, L.aW, E₂.perm.wW, cx₂], ?_⟩
    refine ⟨E₂.mut L (by gregs [E₂.ebp]) (by gregs [E₂.esp]) (by gmems []) (by gmems []) (by gmems []; exact fm),
      by gregs [cx₂], by gmems [slotv_eq], by gmems [slotv_eq, m₂, hn], by gregs [si₂], by gmems [rd₂],
      by gmems [wr₂], by gmems []; rw [← m₂]; exact f⟩
  refine WP.seq (WP.ite (decide (m / 16 < 64)) (eval_b cf₁) (fun ht => ?_) (fun hf => ?_))
  · refine WP.of_runBlock ⟨t₁, rfl, ?_⟩
    have h : m / 16 < 64 := by simpa using ht
    exact hk t₁ (by rw [cx₁]; congr 1; omega) E₁ si₁ rd₁ wr₁ m₁
  · have h : ¬ m / 16 < 64 := by simpa using hf
    obtain ⟨t₂, run₂, cx₂, bp₂, sp₂, si₂, rd₂, wr₂, m₂⟩ : ∃ t₂, runBlock isa [.mov .ecx (imm 64)] t₁ = some t₂ ∧
        t₂.gpr .ecx = BitVec.ofNat 32 64 ∧ t₂.gpr .ebp = p.W ∧ t₂.gpr .esp = p.SP ∧ t₂.gpr .esi = t₁.gpr .esi ∧
        t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr ∧ t₂.mem = t₁.mem :=
      ⟨_, by grun [], by gregs [], by gregs [bp₁], by gregs [sp₁], by gregs [], by gmems [], by gmems [], by gmems []⟩
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    exact hk t₂ (by rw [cx₂]; congr 1; omega) (E₁.keep (by rw [bp₂, bp₁]) (by rw [sp₂, sp₁]) rd₂ wr₂ m₂)
      (by rw [si₂, si₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [m₂, m₁])

/-- Four doublings. -/
theorem dbl4 (k : Nat) : BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k)) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k))) = BitVec.ofNat 32 (16 * k) := by
  simp only [ofNat_add32]; congr 1; omega

theorem ofNat_sub32 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 ha, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  omega

/-- A chunk up to its call: up to 64 blocks reversed at `W + 768`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : Prm) (Q : BitVec 32) (m k : Nat) (t t₅ : State) : Prop where
  env : Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  eax : t₅.gpr .eax = p.W + BitVec.ofNat 32 64
  edx : t₅.gpr .edx = p.W + BitVec.ofNat 32 80
  ebx : t₅.gpr .ebx = p.W + BitVec.ofNat 32 768
  edi : t₅.gpr .edi = BitVec.ofNat 32 k
  esi : t₅.gpr .esi = Q + BitVec.ofNat 32 (16 * k)
  n : slotv t₅.mem p.W nO = BitVec.ofNat 32 (m - 16 * k)
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (w64 p.W + BitVec.ofNat 64 768) k = elemsAt t.mem (w64 Q) k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa chunkPre t (ChunkPre p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (chunkLen_ok L E hm hn) fun t₁ ⟨E₁, cx₁, ix₁, n₁, si₁, rd₁, wr₁, f₁⟩ => ?_)
  obtain ⟨t₂, run₂, dx₂, cx₂, si₂, bp₂, sp₂, rd₂, wr₂, m₂⟩ : ∃ t₂, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm revO)] t₁ = some t₂ ∧
      t₂.gpr .edx = p.W + BitVec.ofNat 32 768 ∧ t₂.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) ∧
      t₂.gpr .esi = Q ∧ t₂.gpr .ebp = p.W ∧ t₂.gpr .esp = p.SP ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr ∧ t₂.mem = t₁.mem :=
    ⟨_, by grun [], by gregs [E₁.ebp], by gregs [cx₁], by gregs [si₁, hsi], by gregs [E₁.ebp], by gregs [E₁.esp],
      by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  have E₂ : Env p t₂ := E₁.keep (by rw [bp₂, E₁.ebp]) (by rw [sp₂, E₁.esp]) rd₂ wr₂ m₂
  have hk1 : 1 ≤ min (m / 16) 64 := by omega
  have hd₁ : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 180, 4⟩ : Region)],
      (⟨w64 Q, 16 * min (m / 16) 64⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hQ.v.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub _ (by decide) (by decide))
  have hQ₂ : Src p t₂ Q (16 * min (m / 16) 64) :=
    (hQ.take (by omega)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (revLoop_ok L E₂ hk1 (by omega) hQ₂ si₂ dx₂ cx₂)
    fun t₃ ⟨fr₃, out₃, si₃, bp₃, sp₃, rd₃, wr₃⟩ => ?_)
  have dV : ∀ {d k : Nat}, 176 ≤ d → d + k ≤ 184 →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 768, 16 * min (m / 16) 64⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by omega)
  have E₃ : Env p t₃ := E₂.mut L (by rw [bp₃, bp₂]) (by rw [sp₃, sp₂]) rd₃ wr₃ (frame_toMut fr₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact inMut_w p (.inr (.inr (.inr ⟨by decide, by omega⟩))))
  have ix₃ : slotv t₃.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) := by
    rw [← ix₁, ← m₂]
    exact fr₃.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (dV (by decide) (by decide))
      (by decide)
  have n₃ : slotv t₃.mem p.W nO = BitVec.ofNat 32 m := by
    rw [← n₁, ← m₂]
    exact fr₃.readW (r := ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩) (Region.contains_self _ _) (dV (by decide) (by decide))
      (by decide)
  simp only [slotv_eq, iO, nO] at ix₃ n₃
  rw [m₂] at fr₃ out₃
  have eQ : elemsAt t₁.mem (w64 Q) (min (m / 16) 64) = elemsAt t.mem (w64 Q) (min (m / 16) 64) := by
    unfold elemsAt
    rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.X86.bytesAt_frame f₁ hd₁ (by omega)]
  have f4 : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₃.mem
      (t₃.mem.writeW (w64 p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 (m - 16 * min (m / 16) 64))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨_, by simp only [chunkArgs]; grun [E₃.ebp, L.aW, E₃.perm.wW, E₃.perm.wR, ix₃, n₃], ?_⟩
  have fm4 := frame_toMut f4 fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine ⟨E₃.mut L (by gregs [E₃.ebp]) (by gregs [E₃.esp]) (by gmems []) (by gmems [])
      (by gmems [dbl4, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]; exact fm4),
    by gmems [rd₃, rd₂, rd₁], by gmems [wr₃, wr₂, wr₁], by gregs [E₃.ebp], by gregs [E₃.ebp], by gregs [E₃.ebp],
    by gregs [ix₃], by gregs [si₃], ?_, ?_, ?_⟩
  · gmems [slotv_eq, dbl4, n₃, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]
  · gmems [dbl4, n₃, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]
    refine ((f₁.sub fun r hr => ?_).trans (fr₃.sub fun r hr => ?_)).trans (f4.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  · gmems [dbl4, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega) hm]
    rw [Proof.AesGcm.X86.blocksAt_frame f4 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (a := 768) (n := 16 * min (m / 16) 64) (.inr (by decide)) (by omega) (by decide)) (by omega),
      out₃, eQ]

/-- `wholeLeft`: ZF set iff fewer than 16 of the `r` bytes are left. -/
theorem wholeLeft_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {r : Nat} (hr : r < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa wholeLeft t = some t' ∧ t'.zf = some (decide (r / 16 = 0)) ∧ Env p t' ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [slotv_eq, nO] at hn
  refine ⟨_, by simp only [wholeLeft]; grun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, by gregs [], by gmems [],
    by gmems [], by gmems []⟩
  · gmems [hn, ofNat_lsr32 hr]
    rw [BitVec.and_self, show BitVec.ofNat 32 (r / 16) = BitVec.ofNat 32 (r / 16) - BitVec.ofNat 32 0 by simp,
      sub_beq32 (by omega) (by decide)]
  · exact E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems [])

theorem chunk_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (chunk v.callees) t (ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  have hk : min (m / 16) 64 ≤ 64 := by omega
  refine WP.seq (WP.mono (chunkPre_ok L E hm h16 hQ hsi hn) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (callGh_ok v L Pr.env hk Pr.eax Pr.edx Pr.ebx Pr.edi) fun t₆ P => ?_)
  have dH : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 768,
      16 * min (m / 16) 64⟩], (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 768,
      16 * min (m / 16) 64⟩], (⟨w64 p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
  have out₆ := P.out
  rw [Proof.AesGcm.X86.blockAt_frame Pr.frame dH, Proof.AesGcm.X86.blockAt_frame Pr.frame dY, Pr.out] at out₆
  have n₆ : slotv t₆.mem p.W nO = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) := by
    rw [← Pr.n]
    exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  obtain ⟨t₇, run₇, z₇, E₇, si₇, m₇, rd₇, wr₇⟩ := wholeLeft_ok L P.env (by omega) n₆
  refine WP.of_runBlock ⟨t₇, run₇, E₇, by rw [rd₇, P.rd, Pr.rd], by rw [wr₇, P.wr, Pr.wr], ?_,
    by rw [slotv_eq, m₇]; exact n₆, z₇, ?_, by rw [m₇]; exact out₆⟩
  · rw [si₇, P.saved _ (by decide), Pr.esi]
  · rw [m₇]
    refine (Pr.frame.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩, by simp, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
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
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.X86.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 224`. -/
abbrev absorbR (p : Prm) : List Region := ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ :: absR p

theorem inMut_absorbR (p : Prm) : InMut p (absorbR p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_absR p r hr

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (p : Prm) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (w64 p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80)) xs

/-- What absorbing a string leaves. -/
abbrev AbsPost (p : Prm) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop := Absorbed p (absorbR p) xs t t'

theorem absorbR_H {p : Prm} (L : Lay p) :
    ∀ r ∈ absorbR p, (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm

theorem absR_sub (p : Prm) : ∀ r ∈ absR p, ∃ r' ∈ absorbR p, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : Absorbed p rs xs t t₁) (h₂ : Absorbed p rs ys t₁ t₂) : Absorbed p rs (xs ++ ys) t t₂ := by
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.X86.blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {p : Prm} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : Absorbed p rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Absorbed p rs' xs t t' :=
  ⟨h.env, h.rd, h.wr, h.frame.sub hs, h.out⟩

theorem Absorbed.of_chunk {p : Prm} {Q : BitVec 32} {m k : Nat} {t t' : State}
    (h : ChunkPost p Q m k t t') : Absorbed p (absR p) (elemsAt t.mem (w64 Q) k) t t' :=
  ⟨h.env, h.rd, h.wr, h.frame, h.out⟩

theorem Absorbed.of_eq {p : Prm} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : Absorbed p rs xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    Absorbed p rs xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absR_H {p : Prm} (L : Lay p) :
    ∀ r ∈ absR p, (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => absorbR_H L r (List.mem_cons_of_mem _ hr)

theorem AbsPost.trans {p : Prm} (L : Lay p) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : AbsPost p xs t t₁) (h₂ : AbsPost p ys t₁ t₂) : AbsPost p (xs ++ ys) t t₂ :=
  Absorbed.trans (absorbR_H L) h₁ h₂

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (p : Prm) (σ : State) (Q : BitVec 32) (m d : Nat) (t : State) : Prop where
  abs : Absorbed p (absR p) (elemsAt σ.mem (w64 Q) d) σ t
  esi : t.gpr .esi = Q + BitVec.ofNat 32 (16 * d)
  n : slotv t.mem p.W nO = BitVec.ofNat 32 (m - 16 * d)

theorem CInv.src {p : Prm} {σ t : State} {Q : BitVec 32} {m d : Nat} (I : CInv p σ Q m d t)
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) :
    Src p t (Q + BitVec.ofNat 32 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
  (hQ.slice (by omega) (by omega)).of_eq I.abs.rd I.abs.wr

theorem CInv.zero {p : Prm} {σ : State} (E : Env p σ) {Q : BitVec 32} {m : Nat} (hsi : σ.gpr .esi = Q)
    (hn : slotv σ.mem p.W nO = BitVec.ofNat 32 m) : CInv p σ Q m 0 σ :=
  ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
    by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hn, Nat.mul_zero, Nat.sub_zero]⟩

/-- A chunk, in the chunks. -/
theorem CInv.step {p : Prm} (L : Lay p) {σ t t' : State} {Q : BitVec 32} {m d : Nat}
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) (I : CInv p σ Q m d t)
    (C : ChunkPost p (Q + BitVec.ofNat 32 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    CInv p σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.zf = some (decide (m / 16 - (d + min (m / 16 - d) 64) = 0)) := by
  have hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega
  rw [hk] at C
  have hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega) (by omega)
  have ea := hQ.addr (j := 16 * d) (by omega)
  have C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.y
      · exact hs.v
      · exact hs.rev
      · exact hs.stk.symm) (by omega), ea] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.esi, add32_ofNat_assoc, Nat.mul_add],
    by rw [C.n]; congr 1; omega⟩, by rw [C.z]; congr 2; apply propext; omega⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (.loop (chunk v.callees) .ne) t fun t' =>
      Absorbed p (absR p) (elemsAt t.mem (w64 Q) (m / 16)) t t' ∧
      t'.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk v.callees) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega, CInv.zero E hsi hn⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_ok v L I.abs.env (by omega) (by omega) (I.src hQ hd) I.esi I.n) fun t'' C => ?_
  obtain ⟨I', z⟩ := I.step L hQ hd C
  have ev := eval_ne z
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega), he ▸ I'.abs, by rw [I'.esi, he], by rw [I'.n, he]; congr 1; omega⟩
  · right
    exact ⟨ev.trans (by simp; omega), m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.X86
