module

public import VerifiedGarbage.Proof.Cmac.Block32
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.AesGcmSiv.X86.Keys
import VerifiedGarbage.Proof.GcmSiv.Words32
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesGcmSiv.X86.Derive

/-! ### `AesGcmSiv.X86.Absorb`, which this module and modules that import it used -/

section

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

@[expose] public section

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
  rw [BitVec.toNat_sub, toNat_ofNat32 hj, toNat_ofNat32 (by decide), toNat_ofNat32 (by omega_arith)]
  omega_arith

theorem revStep_ok {t : State} {S P : BitVec 32} {j : Nat} (hj : j + 1 < 2 ^ 32)
    (fS : S.toNat + 16 ≤ 2 ^ 32) (fP : P.toNat + 16 ≤ 2 ^ 32)
    (hsp : (⟨w64 S, 16⟩ : Region).Disjoint ⟨w64 P, 16⟩)
    (hsi : t.gpr .esi = S) (hdx : t.gpr .edx = P) (hcx : t.gpr .ecx = BitVec.ofNat 32 (j + 1))
    (hr : Covers [⟨w64 S, 16⟩] (t.rd ++ t.wr)) (hw : Covers [⟨w64 P, 16⟩] t.wr) :
    ∃ t' : State, runBlock isa revBody t = some t' ∧ t'.mem = revMem t.mem (w64 S) (w64 P) ∧
      t'.gpr .esi = S + BitVec.ofNat 32 16 ∧ t'.gpr .edx = P + BitVec.ofNat 32 16 ∧
      t'.gpr .ecx = BitVec.ofNat 32 j ∧ t'.zf = some (decide (j = 0)) ∧ t'.gpr .ebp = t.gpr .ebp ∧
      t'.gpr .esp = t.gpr .esp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain aS : ∀ {o}, o < 16 → w64 (S + BitVec.ofNat 32 o) = w64 S + BitVec.ofNat 64 o := fun ho => w64_add (by omega_arith)
  obtain aP : ∀ {o}, o < 16 → w64 (P + BitVec.ofNat 32 o) = w64 P + BitVec.ofNat 64 o := fun ho => w64_add (by omega_arith)
  obtain rS : ∀ {o}, o + 4 ≤ 16 → InRegions (t.rd ++ t.wr) (w64 S + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hr ho (by decide)
  obtain wP : ∀ {o}, o + 4 ≤ 16 → InRegions t.wr (w64 P + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hw ho (by decide)
  obtain sep : ∀ (m : Mem) (v : BitVec 32) {a b : Nat}, a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (w64 P + BitVec.ofNat 64 a) v).readW (w64 S + BitVec.ofNat 64 b) 32 =
        m.readW (w64 S + BitVec.ofNat 64 b) 32 := fun m v a b ha hb =>
    Proof.Cmac.readW_writeW_disj _ (hsp.symm.sub_left (Offset.sub_base _ ha) |>.sub_right (Offset.sub_base _ hb))
  refine ⟨_, by grun [hsi, hdx, hcx, aS, aP, rS, wP, sep], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hsi, hdx, sep, revMem, Proof.Cmac.store4, BitVec.add_zero]
  · gregs [hsi]
  · gregs [hdx]
  · gregs [hcx, ofNat_sub1 hj]
  · gmems [hcx, ofNat_sub1 hj]
    rw [show BitVec.ofNat 32 j = BitVec.ofNat 32 j - BitVec.ofNat 32 0 by simp, sub_beq32 (by omega_arith) (by decide)]
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
  obtain b := blockAt_bswap (revMem m S P) P 0
  rw [BitVec.add_zero] at b
  rw [b, revMem, Proof.Cmac.store4]
  simp (disch := decide) only [Nat.reduceAdd, BitVec.add_zero, Mem.readW_writeW_self32, readW_writeW_off,
    bswap_bswap]
  obtain dj : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 →
      (⟨P + BitVec.ofNat 64 x, 4⟩ : Region).Disjoint ⟨P + BitVec.ofNat 64 y, 4⟩ :=
    fun h hx hy => Offset.disjoint P h (by omega_arith) (by omega_arith)
  obtain d₀ : ∀ y, 4 ≤ y → y + 4 ≤ 16 → (⟨P, 4⟩ : Region).Disjoint ⟨P + BitVec.ofNat 64 y, 4⟩ := fun y h₁ h₂ => by
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

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega_arith

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem addr {j : Nat} (hj : j < n) : w64 (Q + BitVec.ofNat 32 j) = w64 Q + BitVec.ofNat 64 j :=
  w64_add (by have := h.wrap; omega_arith)

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 32 j).toNat = Q.toNat + j :=
  toNat_add32 (by have := h.wrap; omega_arith)

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src p s Q k where
  rd := covers_prefix h.rd hk
  wrap := by have := h.wrap; omega_arith
  y := h.y.sub_left (Region.sub_prefix hk)
  v := h.v.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : Src p s (Q + BitVec.ofNat 32 a) k := by
  obtain e := h.addr ha
  obtain hs : Region.Sub ⟨w64 Q + BitVec.ofNat 64 a, k⟩ ⟨w64 Q, n⟩ := Offset.sub_base _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact covers_off h.rd hk h.lt
  · rw [h.toNat_add ha]; have := h.wrap; omega_arith
  · rw [e]; exact h.y.sub_left hs
  · rw [e]; exact h.v.sub_left hs
  · rw [e]; exact h.rev.sub_left hs
  · rw [e]; exact h.stk.sub_right hs

end Src

/-- The block at `W + 224` as a chunk's source. -/
theorem srcB {p : Prm} {s : State} (L : Lay p) (P : Perm p s) : Src p s (p.W + BitVec.ofNat 32 224) 16 where
  rd := by rw [L.aW (by decide)]; exact P.wCR (by decide)
  wrap := by rw [L.nW (by decide)]; have := L.ww; omega_arith
  y := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  v := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  rev := by rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  stk := by rw [L.aW (by decide)]; exact L.bw' (by decide)

/-- A buffer apart from `W` and the stack as a chunk's source. -/
theorem srcBuf {p : Prm} {s : State} {Q : BitVec 32} {k : Nat} (hr : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr))
    (hwrap : Q.toNat + k ≤ 2 ^ 32) (hw : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩)
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
  obtain I₀ : RInv p Q c 0 t₀ t₀ := ⟨by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hdx],
    by rw [hcx, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ RInv p Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  obtain eS : w64 (Q + BitVec.ofNat 32 (16 * j)) = w64 Q + BitVec.ofNat 64 (16 * j) := hQ.addr (by omega_arith)
  obtain eP : w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)) = w64 p.W + BitVec.ofNat 64 (768 + 16 * j) :=
    L.aW (by omega_arith)
  obtain hr : Covers [⟨w64 (Q + BitVec.ofNat 32 (16 * j)), 16⟩] (t.rd ++ t.wr) := by
    rw [I.rd, I.wr, eS]; exact covers_off hQ.rd (by omega_arith) hQ.lt
  obtain hwr : Covers [⟨w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)), 16⟩] t.wr := by
    rw [I.wr, eP]; exact E.perm.wC (by omega_arith)
  obtain hsep : (⟨w64 (Q + BitVec.ofNat 32 (16 * j)), 16⟩ : Region).Disjoint
      ⟨w64 (p.W + BitVec.ofNat 32 (768 + 16 * j)), 16⟩ := by
    rw [eS, eP]
    exact (hQ.rev.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub _ (by omega_arith) (by omega_arith))
  obtain ⟨t', run', hm', si', dx', cx', z', bp', sp', rd', wr'⟩ :=
    revStep_ok (j := c - j - 1) (by omega_arith) (by rw [hQ.toNat_add (by omega_arith)]; have := hQ.wrap; omega_arith)
      (by rw [L.nW (by omega_arith)]; omega_arith) hsep I.esi I.edx (by rw [I.ecx]; congr 1; omega_arith) hr hwr
  refine WP.of_runBlock ⟨t', run', ?_⟩
  rw [eS, eP] at hm'
  -- The source is outside the copies.
  obtain src : bytesAt t.mem (w64 Q + BitVec.ofNat 64 (16 * j)) 16 =
      bytesAt t₀.mem (w64 Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.AesGcm.X86.bytesAt_frame I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub _ (by omega_arith) (by omega_arith)))
      (by decide)
  obtain fr : Frame [⟨w64 p.W + BitVec.ofNat 64 (768 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', revMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain I' : RInv p Q c (j + 1) t₀ t' := by
    refine ⟨by rw [si', add32_ofNat_assoc, Nat.mul_succ], by rw [dx', add32_ofNat_assoc, Nat.mul_succ,
      Nat.add_assoc], by rw [cx', Nat.sub_sub], ?_, ?_, by rw [bp', I.ebp], by rw [sp', I.esp], by rw [rd', I.rd],
      by rw [wr', I.wr]⟩
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩)
    · rw [blocksAt_succ, Proof.AesGcm.X86.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', revMem_block, src]
  obtain ev := eval_ne z'
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega_arith]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.esi, I'.ebp, I'.esp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩


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
    rw [toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by decide)]
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
  obtain E₁ : Env p t₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁ m₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- `ecx := min (m / 16, 64)`, by the branch.
  obtain hk : ∀ t₂ : State, t₂.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) → Env p t₂ → t₂.gpr .esi = t.gpr .esi →
      t₂.rd = t.rd → t₂.wr = t.wr → t₂.mem = t.mem →
      WP isa (.block [.store (at_ .ebp iO) .ecx]) t₂ fun t' => Env p t' ∧
        t'.gpr .ecx = BitVec.ofNat 32 (min (m / 16) 64) ∧
        slotv t'.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 m ∧
        t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
        Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t.mem t'.mem := by
    intro t₂ cx₂ E₂ si₂ rd₂ wr₂ m₂
    obtain f : Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t₂.mem
        (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 180) (BitVec.ofNat 32 (min (m / 16) 64))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain fm := frame_toMut f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
    refine WP.of_runBlock ⟨_, by grun [E₂.ebp, L.aW, E₂.perm.wW, cx₂], ?_⟩
    refine ⟨E₂.mut L (by gregs [E₂.ebp]) (by gregs [E₂.esp]) (by gmems []) (by gmems []) (by gmems []; exact fm),
      by gregs [cx₂], by gmems [slotv_eq], by gmems [slotv_eq, m₂, hn], by gregs [si₂], by gmems [rd₂],
      by gmems [wr₂], by gmems []; rw [← m₂]; exact f⟩
  refine WP.seq (WP.ite (decide (m / 16 < 64)) (eval_b cf₁) (fun ht => ?_) (fun hf => ?_))
  · refine WP.of_runBlock ⟨t₁, rfl, ?_⟩
    obtain h : m / 16 < 64 := by simpa using ht
    exact hk t₁ (by rw [cx₁]; congr 1; omega_arith) E₁ si₁ rd₁ wr₁ m₁
  · have h : ¬ m / 16 < 64 := by simpa using hf
    obtain ⟨t₂, run₂, cx₂, bp₂, sp₂, si₂, rd₂, wr₂, m₂⟩ : ∃ t₂, runBlock isa [.mov .ecx (imm 64)] t₁ = some t₂ ∧
        t₂.gpr .ecx = BitVec.ofNat 32 64 ∧ t₂.gpr .ebp = p.W ∧ t₂.gpr .esp = p.SP ∧ t₂.gpr .esi = t₁.gpr .esi ∧
        t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr ∧ t₂.mem = t₁.mem :=
      ⟨_, by grun [], by gregs [], by gregs [bp₁], by gregs [sp₁], by gregs [], by gmems [], by gmems [], by gmems []⟩
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    exact hk t₂ (by rw [cx₂]; congr 1; omega_arith) (E₁.keep (by rw [bp₂, bp₁]) (by rw [sp₂, sp₁]) rd₂ wr₂ m₂)
      (by rw [si₂, si₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [m₂, m₁])

/-- Four doublings. -/
theorem dbl4 (k : Nat) : BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k)) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k) +
    (BitVec.ofNat 32 k + BitVec.ofNat 32 k + (BitVec.ofNat 32 k + BitVec.ofNat 32 k))) = BitVec.ofNat 32 (16 * k) := by
  simp only [ofNat_add32]; congr 1; omega_arith

theorem ofNat_sub32 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat32 ha, toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)]
  omega_arith

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
  obtain E₂ : Env p t₂ := E₁.keep (by rw [bp₂, E₁.ebp]) (by rw [sp₂, E₁.esp]) rd₂ wr₂ m₂
  obtain hk1 : 1 ≤ min (m / 16) 64 := by omega_arith
  obtain hd₁ : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 180, 4⟩ : Region)],
      (⟨w64 Q, 16 * min (m / 16) 64⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hQ.v.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub _ (by decide) (by decide))
  obtain hQ₂ : Src p t₂ Q (16 * min (m / 16) 64) :=
    (hQ.take (by omega_arith)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (revLoop_ok L E₂ hk1 (by omega_arith) hQ₂ si₂ dx₂ cx₂)
    fun t₃ ⟨fr₃, out₃, si₃, bp₃, sp₃, rd₃, wr₃⟩ => ?_)
  obtain dV : ∀ {d k : Nat}, 176 ≤ d → d + k ≤ 184 →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 768, 16 * min (m / 16) 64⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain E₃ : Env p t₃ := E₂.mut L (by rw [bp₃, bp₂]) (by rw [sp₃, sp₂]) rd₃ wr₃ (frame_toMut fr₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact inMut_w p (.inr (.inr (.inr ⟨by decide, by omega_arith⟩))))
  obtain ix₃ : slotv t₃.mem p.W iO = BitVec.ofNat 32 (min (m / 16) 64) := by
    rw [← ix₁, ← m₂]
    exact fr₃.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (dV (by decide) (by decide))
      (by decide)
  obtain n₃ : slotv t₃.mem p.W nO = BitVec.ofNat 32 m := by
    rw [← n₁, ← m₂]
    exact fr₃.readW (r := ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩) (Region.contains_self _ _) (dV (by decide) (by decide))
      (by decide)
  simp only [slotv_eq, iO, nO] at ix₃ n₃
  rw [m₂] at fr₃ out₃
  obtain eQ : elemsAt t₁.mem (w64 Q) (min (m / 16) 64) = elemsAt t.mem (w64 Q) (min (m / 16) 64) := by
    unfold elemsAt
    rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.X86.bytesAt_frame f₁ hd₁ (by omega_arith)]
  obtain f4 : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₃.mem
      (t₃.mem.writeW (w64 p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 (m - 16 * min (m / 16) 64))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨_, by simp only [chunkArgs]; grun [E₃.ebp, L.aW, E₃.perm.wW, E₃.perm.wR, ix₃, n₃], ?_⟩
  obtain fm4 := frame_toMut f4 fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine ⟨E₃.mut L (by gregs [E₃.ebp]) (by gregs [E₃.esp]) (by gmems []) (by gmems [])
      (by gmems [dbl4, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega_arith) hm]; exact fm4),
    by gmems [rd₃, rd₂, rd₁], by gmems [wr₃, wr₂, wr₁], by gregs [E₃.ebp], by gregs [E₃.ebp], by gregs [E₃.ebp],
    by gregs [ix₃], by gregs [si₃], ?_, ?_, ?_⟩
  · gmems [slotv_eq, dbl4, n₃, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega_arith) hm]
  · gmems [dbl4, n₃, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega_arith) hm]
    refine ((f₁.sub fun r hr => ?_).trans (fr₃.sub fun r hr => ?_)).trans (f4.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  · gmems [dbl4, ofNat_sub32 (show 16 * min (m / 16) 64 ≤ m by omega_arith) hm]
    rw [Proof.AesGcm.X86.blocksAt_frame f4 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (a := 768) (n := 16 * min (m / 16) 64) (.inr (by decide)) (by omega_arith) (by decide)) (by omega_arith),
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
      sub_beq32 (by omega_arith) (by decide)]
  · exact E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems [])

theorem chunk_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (chunk v.callees) t (ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  obtain hk : min (m / 16) 64 ≤ 64 := by omega_arith
  refine WP.seq (WP.mono (chunkPre_ok L E hm h16 hQ hsi hn) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (callGh_ok v L Pr.env hk Pr.eax Pr.edx Pr.ebx Pr.edi) fun t₆ P => ?_)
  obtain dH : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 768,
      16 * min (m / 16) 64⟩], (⟨w64 p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  obtain dY : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 8⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 768,
      16 * min (m / 16) 64⟩], (⟨w64 p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  have out₆ := P.out
  rw [Proof.AesGcm.X86.blockAt_frame Pr.frame dH, Proof.AesGcm.X86.blockAt_frame Pr.frame dY, Pr.out] at out₆
  obtain n₆ : slotv t₆.mem p.W nO = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) := by
    rw [← Pr.n]
    exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  obtain ⟨t₇, run₇, z₇, E₇, si₇, m₇, rd₇, wr₇⟩ := wholeLeft_ok L P.env (by omega_arith) n₆
  refine WP.of_runBlock ⟨t₇, run₇, E₇, by rw [rd₇, P.rd, Pr.rd], by rw [wr₇, P.wr, Pr.wr], ?_,
    by rw [slotv_eq, m₇]; exact n₆, z₇, ?_, by rw [m₇]; exact out₆⟩
  · rw [si₇, P.saved _ (by decide), Pr.esi]
  · rw [m₇]
    refine (Pr.frame.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 768, 1280⟩, by simp, Region.sub_prefix (by omega_arith)⟩
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
  (hQ.slice (by omega_arith) (by omega_arith)).of_eq I.abs.rd I.abs.wr

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
  obtain hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega_arith
  rw [hk] at C
  obtain hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega_arith) (by omega_arith)
  obtain ea := hQ.addr (j := 16 * d) (by omega_arith)
  obtain C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.y
      · exact hs.v
      · exact hs.rev
      · exact hs.stk.symm) (by omega_arith), ea] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.esi, add32_ofNat_assoc, Nat.mul_add],
    by rw [C.n]; congr 1; omega_arith⟩, by rw [C.z]; congr 2; apply propext; omega_arith⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (hsi : t.gpr .esi = Q)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (.loop (chunk v.callees) .ne) t fun t' =>
      Absorbed p (absR p) (elemsAt t.mem (w64 Q) (m / 16)) t t' ∧
      t'.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv t'.mem p.W nO = BitVec.ofNat 32 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk v.callees) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega_arith, CInv.zero E hsi hn⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_ok v L I.abs.env (by omega_arith) (by omega_arith) (I.src hQ hd) I.esi I.n) fun t'' C => ?_
  obtain ⟨I', z⟩ := I.step L hQ hd C
  obtain ev := eval_ne z
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega_arith), he ▸ I'.abs, by rw [I'.esi, he], by rw [I'.n, he]; congr 1; omega_arith⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), m / 16 - (d + min (m / 16 - d) 64), by omega_arith, d + min (m / 16 - d) 64, rfl,
      by omega_arith, I'⟩

end VG.Proof.AesGcmSiv.X86

end

end

/-!
# AES-GCM-SIV on x86: POLYVAL and the tag input (`absorb`, `polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 224` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`), from the slots `alenO` and `lenO`; `tagIn` turns POLYVAL's
result into the tag input (`tagIn_ok`). `polyval_ok`: the tag input of
RFC 8452 §4, with POLYVAL as GHASH with the key `H · x`
(`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.Cmac (le4)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv slotv_eq GcmImpl readW_writeW_off covers_left covers_off
  zero4_fold LoopPre CopyPost copyLoop_ok length_bytesAt sub_beq32)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero4 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  obtain hz := Proof.Cmac.zero4_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega_arith, Proof.AesGcm.X86.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega_arith, Proof.AesGcm.X86.bytesAt_add,
    Proof.AesGcm.X86.bytesAt_writeBytes_self _ _ _ (by omega_arith),
    Proof.AesGcm.X86.bytesAt_frame (Proof.AesGcm.X86.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega_arith)) (by omega_arith)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- One chunk of the 16 bytes at `W + 224`: their field element absorbed. -/
theorem chunkB_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hsi : t.gpr .esi = p.W + BitVec.ofNat 32 224) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 16) :
    WP isa (chunk v.callees) t (Absorbed p (absR p)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 224) 16)] t) :=
  WP.mono (chunk_ok v L E (m := 16) (by decide) (by decide) (srcB L E.perm) hsi hn) fun t' C => by
    obtain A := Absorbed.of_chunk C
    simpa [elemsAt, L.aW (show 224 < 2816 by decide)] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 224`, as the
bytes to absorb. -/
structure TailPre (p : Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  esi : t₃.gpr .esi = p.W + BitVec.ofNat 32 224
  n : slotv t₃.mem p.W nO = BitVec.ofNat 32 16
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`'s first block: the block zeroed, and the copy's arguments. -/
theorem absTail1_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hsi : t.gpr .esi = P) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    ∃ t₁ : State, runBlock isa (zero4 bO ++ ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm bO),
        .mov .ecx (slot nO)] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 t.mem (w64 p.W + BitVec.ofNat 64 224) ∧ t₁.gpr .edi = P ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₁.gpr .ecx = BitVec.ofNat 32 r ∧ t₁.gpr .ebp = p.W ∧
      t₁.gpr .esp = p.SP ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  simp only [slotv_eq, nO] at hn
  obtain hz := zero4_fold t.mem p.W 224
  simp only [Nat.reduceAdd] at hz
  obtain rn : (Proof.Cmac.zero4 t.mem (w64 p.W + BitVec.ofNat 64 224)).readW (w64 p.W + BitVec.ofNat 64 176) 32 =
      t.mem.readW (w64 p.W + BitVec.ofNat 64 176) 32 := by
    rw [← hz]; simp (disch := decide) only [readW_writeW_off]
  refine ⟨_, by simp only [zero4]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hn, hz, rn], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · gmems [hz]
  · gregs [hsi]
  · gregs [E.ebp]
  · gmems [hz, rn, hn]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨w64 P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩) (hsi : t.gpr .esi = P)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    WP isa absTailPre t (TailPre p (w64 P) r t) := by
  have hw := L.ww
  obtain ⟨t₁, run₁, hm₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ := absTail1_ok L E hsi hn
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain dB : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 (p.W + BitVec.ofNat 32 224), r⟩ := by
    rw [L.aW (by decide)]
    exact (hd.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right (Region.sub_prefix (by omega_arith))
  obtain lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r :=
    ⟨di₁, dx₁, cx₁, by omega_arith, by omega_arith, hf, by rw [L.nW (by decide)]; omega_arith, by rw [rd₁, wr₁]; exact hc,
      by rw [L.aW (by decide)]; exact covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 2816 by decide)) (by omega_arith), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ lp) fun t₂ O => ?_)
  have hm₂ := O.mem
  rw [L.aW (by decide)] at hm₂
  -- The data is outside the zeroed block.
  obtain hd₁ : bytesAt t₁.mem (w64 P) r = bytesAt t.mem (w64 P) r :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide))) (by omega_arith)
  obtain hb₂ : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
      bytesAt t.mem (w64 P) r ++ Spec.GcmSiv.zeros (16 - r) := by
    obtain hl := length_bytesAt t.mem (w64 P) r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega_arith), hl]
  obtain f₂' : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t₁.mem t₂.mem := by
    rw [hm₂]
    exact (Proof.AesGcm.X86.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
  obtain f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₂.mem := f₁.trans f₂'
  obtain bp₂ : t₂.gpr .ebp = p.W := by rw [O.other _ (by decide) (by decide) (by decide) (by decide), bp₁]
  obtain sp₂ : t₂.gpr .esp = p.SP := by rw [O.other _ (by decide) (by decide) (by decide) (by decide), sp₁]
  obtain E₂ : Env p t₂ := E₁.mut L bp₂ sp₂ O.rd O.wr (frame_toMut f₂' fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem
      (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 16)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fm₃ := frame_toMut f₃ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine WP.of_runBlock ⟨_, by grun [E₂.ebp, L.aW, E₂.perm.wW], ?_⟩
  refine ⟨E₂.mut L (by gregs [E₂.ebp]) (by gregs [E₂.esp]) (by gmems []) (by gmems []) (by gmems []; exact fm₃),
    by gmems [O.rd, rd₁], by gmems [O.wr, wr₁], by gregs [E₂.ebp], by gmems [slotv_eq], ?_, ?_⟩
  · gmems []
    exact (f₂.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (f₃.mono fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_of_mem _ List.mem_cons_self)
  · gmems []
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), hb₂]

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨w64 P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩) (hsi : t.gpr .esi = P)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    WP isa (absTail v.callees) t
      (AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 P) r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (absTailPre_ok L E hr1 hr hc hf hd hsi hn) fun t₃ T => ?_)
  refine WP.mono (chunkB_ok v L T.env T.esi T.n) fun t₄ C => ?_
  rw [T.bytes] at C
  obtain dHY : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩], ∀ d,
      d + 16 ≤ 176 → (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.sub fun q hq => ?_).trans (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · rw [C.out, Proof.AesGcm.X86.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
      Proof.AesGcm.X86.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]

/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  obtain hs := Proof.AesGcm.X86.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at hs
  obtain hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once ZF says whether there are any. -/
theorem absMid_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : Src p t Q m) (hsi : t.gpr .esi = Q) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m)
    (hz : t.zf = some (decide (m / 16 = 0))) :
    WP isa (.ite .e (.block []) (.loop (chunk v.callees) .ne)) t fun t₂ =>
      Absorbed p (absR p) (elemsAt t.mem (w64 Q) (m / 16)) t t₂ ∧
        t₂.gpr .esi = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ slotv t₂.mem p.W nO = BitVec.ofNat 32 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (eval_e hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [hsi, h0, Nat.mul_zero, BitVec.add_zero], by rw [hn]; congr 1; omega_arith⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_ok v L E hm (by omega_arith) (hQ.take (by omega_arith)) hsi hn

/-- `anyLeft`: ZF set iff no byte is left. -/
theorem anyLeft_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {r : Nat} (hr : r < 2 ^ 32)
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa anyLeft t = some t' ∧ t'.zf = some (decide (r = 0)) ∧ Env p t' ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [slotv_eq, nO] at hn
  refine ⟨_, by simp only [anyLeft]; grun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, by gregs [], by gmems [],
    by gmems [], by gmems []⟩
  · gmems [hn]
    rw [BitVec.and_self, show BitVec.ofNat 32 r = BitVec.ofNat 32 r - BitVec.ofNat 32 0 by simp,
      sub_beq32 hr (by decide)]
  · exact E.keep (by gregs []) (by gregs []) (by gmems []) (by gmems []) (by gmems [])

theorem absorb_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : Src p t Q m) (hd : (⟨w64 Q, m⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩)
    (hsi : t.gpr .esi = Q) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 m) :
    WP isa (absorb v.callees) t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem (w64 Q) m))) t) := by
  obtain ⟨t₁, run₁, z₁, E₁, si₁, m₁, rd₁, wr₁⟩ := wholeLeft_ok L E hm hn
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (absMid_ok v L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [si₁, hsi]) (by rw [slotv_eq, m₁]; exact hn)
    z₁) fun t₂ ⟨P₂, si₂, n₂⟩ => ?_)
  rw [m₁] at P₂
  obtain P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [elems_pad16_bytesAt]
  obtain ⟨t₃, run₃, z₃, E₃, si₃, m₃, rd₃, wr₃⟩ := anyLeft_ok L P₂'.env (by omega_arith) n₂
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain P₃ : Absorbed p (absR p) (elemsAt t.mem (w64 Q) (m / 16)) t t₃ :=
    ⟨E₃, rd₃.trans P₂'.rd, wr₃.trans P₂'.wr, m₃ ▸ P₂'.frame, by rw [m₃]; exact P₂'.out⟩
  refine WP.ite (decide (m % 16 = 0)) (eval_e z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₃.sub (absR_sub p))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    obtain hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith) (by omega_arith)
    obtain ea := hQ.addr (j := 16 * (m / 16)) (by omega_arith)
    obtain dT : (⟨w64 (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ := by
      rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega_arith))
    refine WP.mono (absTail_ok v L P₃.env (by omega_arith) (by omega_arith) (by rw [P₃.rd, P₃.wr]; exact hs.rd) hs.wrap dT
      (by rw [si₃, si₂]) (by rw [slotv_eq, m₃]; exact n₂)) fun t₄ T => ?_
    obtain e := Proof.AesGcm.X86.bytesAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact hs.stk.symm) (by omega_arith)
    rw [e, ea] at T
    exact AbsPost.trans L (P₃.sub (absR_sub p)) T

/-! ## The lengths, and the tag input -/

/-- The memory `lensBlock` leaves. -/
def lensMem (m : Mem) (W : Addr) (al n : Nat) : Mem :=
  (Proof.Cmac.store4 m (W + BitVec.ofNat 64 224) (BitVec.ofNat 32 al <<< 3) (BitVec.ofNat 32 al >>> 29)
    (BitVec.ofNat 32 n <<< 3) (BitVec.ofNat 32 n >>> 29)).writeW (W + BitVec.ofNat 64 176) (BitVec.ofNat 32 16)

/-- `lensBlock`: the lengths block at `W + 224`, as the bytes to absorb. -/
theorem lensBlock_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = lensMem t.mem (w64 p.W) p.al p.n ∧ t₁.gpr .esi = p.W + BitVec.ofNat 32 224 ∧
      t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have ha := E.slots.alen
  have hn := E.slots.len
  simp only [slotv_eq, alenO, lenO] at ha hn
  refine ⟨_, by simp only [lensBlock, le64At]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, ha, hn], ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · gmems [ha, hn, add_self32_3, lensMem, Proof.Cmac.store4, add_ofNat_assoc]
  · gregs [E.ebp]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (lens v.callees) t (AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  obtain ⟨t₁, run₁, hm₁, si₁, bp₁, sp₁, rd₁, wr₁⟩ := lensBlock_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
    rw [hm₁, lensMem]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  obtain E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  refine WP.mono (chunkB_ok v L E₁ si₁ (by rw [slotv_eq, hm₁, lensMem, Mem.readW_writeW_self32])) fun t₂ C => ?_
  obtain hb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    obtain ea := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.al)
    obtain en := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.n)
    rw [toNat_ofNat32 L.al32] at ea
    rw [toNat_ofNat32 L.n32] at en
    rw [hm₁, lensMem, Proof.AesGcm.X86.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide),
      Proof.Cmac.bytesAt_store4, ea, en, List.append_assoc]
  rw [hb] at C
  obtain dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 224, 16⟩ : Region),
      ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩], (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁], (f₁.sub fun q hq => ?_).trans
    (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · rw [C.out, Proof.AesGcm.X86.blockAt_frame f₁ (dHY 64 (by decide)),
      Proof.AesGcm.X86.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96)
    (bswap (m.readW (W + BitVec.ofNat 64 92) 32) ^^^ m.readW (N + BitVec.ofNat 64 0) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 88) 32) ^^^ m.readW (N + BitVec.ofNat 64 4) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 84) 32) ^^^ m.readW (N + BitVec.ofNat 64 8) 32)
    (bswap (m.readW (W + BitVec.ofNat 64 80) 32) &&& 0x7FFFFFFF#32)

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  obtain e := GcmSiv.Words32.tagOf_words (bswap (m.readW (W + BitVec.ofNat 64 92) 32))
    (bswap (m.readW (W + BitVec.ofNat 64 88) 32)) (bswap (m.readW (W + BitVec.ofNat 64 84) 32))
    (bswap (m.readW (W + BitVec.ofNat 64 80) 32)) (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32)
    (m.readW (N + BitVec.ofNat 64 8) 32)
  rw [GcmSiv.Words32.shl_shr_one] at e
  rw [tagInMem, Proof.Cmac.bytesAt_store4, blockAt_bswap, GcmSiv.Words32.toBytes_append4,
    show (12 : Nat) = 4 + 4 + 4 from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW]
  simp only [add_ofNat_assoc, Nat.reduceAdd, BitVec.add_zero]
  rw [e]

theorem tagIn_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = tagInMem t.mem (w64 p.W) (w64 p.N) ∧
      t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hN := E.slots.nonce
  simp only [slotv_eq, nonceO] at hN
  obtain n₀ := E.perm.nR (d := 0) (k := 4) (by decide)
  obtain n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  obtain n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn, tagInW]; grun [E.ebp, L.aW, L.aN, E.perm.wW, E.perm.wR, hN, n₀, n₄, n₈], ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [hN, tagInMem, Proof.Cmac.store4, add_ofNat_assoc]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (tagInMem m W N) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (p : Prm) : List Region := ⟨w64 p.W + BitVec.ofNat 64 96, 16⟩ :: absorbR p

theorem inMut_polyR (p : Prm) : InMut p (polyR p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact inMut_w p (.inl (by decide))
  · exact inMut_absorbR p r hr

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (polyR p) t.mem t'.mem
  out : bytesAt t'.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem (w64 p.N) 12)
      (bytesAt t.mem (w64 p.D) p.n) (bytesAt t.mem (w64 p.A) p.al)

/-- A buffer apart from `W` and the stack below `SP` misses what absorbing writes. -/
theorem absorbR_buf {p : Prm} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩)
    (hb : (stk p).Disjoint ⟨P, k⟩) : ∀ r ∈ absorbR p, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hb.symm

/-- `onStr s l`: the string at `W + s` (`W + l` bytes) to absorb. -/
theorem onStr_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {s l : Nat} {Q : BitVec 32} {k : Nat}
    (hs : s + 4 ≤ 176 ∧ 128 ≤ s) (hl : l + 4 ≤ 176 ∧ 128 ≤ l) (hQ : slotv t.mem p.W s = Q)
    (hk : slotv t.mem p.W l = BitVec.ofNat 32 k) :
    ∃ t₁ : State, runBlock isa (onStr s l) t = some t₁ ∧ Env p t₁ ∧ t₁.gpr .esi = Q ∧
      slotv t₁.mem p.W nO = BitVec.ofNat 32 k ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
  simp only [slotv_eq] at hQ hk
  obtain f : Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem (t.mem.writeW (w64 p.W + BitVec.ofNat 64 176)
      (BitVec.ofNat 32 k)) := (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fm := frame_toMut f fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  refine ⟨_, by simp only [onStr]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hQ, hk], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E.mut L (by gregs [E.ebp]) (by gregs [E.esp]) (by gmems []) (by gmems []) (by gmems [hQ, hk]; exact fm)
  · gregs [hQ]
  · gmems [slotv_eq, hk]
  · gmems []
  · gmems []
  · gmems [hk]; exact f

theorem polyval_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (w64 p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (PolyPost p t) := by
  have hw := L.ww
  -- The additional data.
  obtain ⟨t₁, run₁, E₁, si₁, n₁, rd₁, wr₁, f₁⟩ := onStr_ok L E (s := aadO) (l := alenO) (by decide) (by decide)
    E.slots.aad E.slots.alen
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain d176 : ∀ {P : Addr} {k : Nat}, (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)], (⟨P, k⟩ : Region).Disjoint q := fun hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide))
  obtain eA₁ : bytesAt t₁.mem (w64 p.A) p.al = bytesAt t.mem (w64 p.A) p.al :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (d176 L.a_w) (by have := L.aw; omega_arith)
  refine WP.seq (WP.mono (absorb_ok v L E₁ (Q := p.A) (m := p.al) L.al32
    (srcBuf E₁.perm.aad L.aw L.a_w L.ba) L.a_w si₁ n₁) fun t₂ P₂ => ?_)
  rw [eA₁] at P₂
  -- The data.
  obtain ⟨t₃, run₃, E₃, si₃, n₃, rd₃, wr₃, f₃⟩ := onStr_ok L P₂.env (s := dataO) (l := lenO) (by decide) (by decide)
    P₂.env.slots.data P₂.env.slots.len
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain eD₃ : bytesAt t₃.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (d176 L.d_w) (by have := L.dw; omega_arith),
      Proof.AesGcm.X86.bytesAt_frame P₂.frame (absorbR_buf L.d_w L.bd) (by have := L.dw; omega_arith),
      Proof.AesGcm.X86.bytesAt_frame f₁ (d176 L.d_w) (by have := L.dw; omega_arith)]
  refine WP.seq (WP.mono (absorb_ok v L E₃ (Q := p.D) (m := p.n) L.n32
    (srcBuf (covers_left E₃.perm.d) L.dw L.d_w L.bd) L.d_w si₃ n₃) fun t₄ P₄ => ?_)
  rw [eD₃] at P₄
  -- From `t`: the writes of `onStr` are in `absorbR`, apart from GHASH's key and accumulator.
  obtain dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain sub176 : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 176, 4⟩ : Region)], ∃ q' ∈ absorbR p, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  obtain pre : ∀ {xs : List Spec.GcmSiv.Elem} {u u₁ u₂ : State},
      Frame [⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] u.mem u₁.mem → u₁.rd = u.rd → u₁.wr = u.wr →
      AbsPost p xs u₁ u₂ → AbsPost p xs u u₂ := fun f hrd hwr P =>
    ⟨P.env, P.rd.trans hrd, P.wr.trans hwr, (f.sub sub176).trans P.frame, by
      rw [P.out, Proof.AesGcm.X86.blockAt_frame f (dHY 64 (by decide)),
        Proof.AesGcm.X86.blockAt_frame f (dHY 80 (by decide))]⟩
  obtain P₂₄ := AbsPost.trans L (pre f₁ rd₁ wr₁ P₂) (pre f₃ rd₃ wr₃ P₄)
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  obtain P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := tagIn_ok L P₂₅.env
  obtain f₆ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 16⟩] t₅.mem t₆.mem := by rw [hm₆]; exact tagInMem_frame _ _ _
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.mut L bp₆ sp₆ rd₆ wr₆ (frame_toMut f₆ fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inl (by decide))),
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    exact f₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
    obtain nN : bytesAt t₅.mem (w64 p.N) 12 = bytesAt t.mem (w64 p.N) 12 :=
      Proof.AesGcm.X86.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w L.bn) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]

end VG.Proof.AesGcmSiv.X86
