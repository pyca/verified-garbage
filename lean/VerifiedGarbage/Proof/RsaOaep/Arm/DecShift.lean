module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecScan
import VerifiedGarbage.Proof.RsaPss.Arm.VfShift
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaPss.Arm.VfPass
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP decryption on ARMv7: the shift

`T`, copied to the 2048-byte buffer at `oBuf` with zeros after it
(`buf_vp`), shifted left by `a = idx + 1` bytes in ten passes: pass `p`
moves each of the buffer's first 1024 bytes by `2^p` if bit `p` of `a` is
set (`onePass_vp`), so that after `p` passes byte `j` is byte
`j + a mod 2^p` of `T`, zeros after its end (`SH`); after ten, `a < 2^10`
(`shift_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sAcc sPos sA sD sPc countLoop passBody passNext
  shInit)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h g : OHash)

/-- What the copy and the shift keep. -/
abbrev Zk (P : EP) (σ : State) (m : Mem) : Prop :=
  X1 h P σ m ∧ (∃ a : BitVec 32, m.readW (P.lay.fr sAcc) 32 = a ∧ a.toNat < 256 ∧ (a = 0 ↔ allOk h g P σ)) ∧
    m.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ)

/-- What misses those. -/
abbrev Away (P : EP) (r : Region) : Prop :=
  (slotR P.lay sRes).Disjoint r ∧ (slotR P.lay sAcc).Disjoint r ∧ (slotR P.lay sPos).Disjoint r ∧
    (sR P.scr oLh h.H.D).Disjoint r ∧ (sR P.scr 0 1).Disjoint r

theorem Zk.keep {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hz : Zk h g P σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, Away h P r) : Zk h g P σ m' := by
  obtain ⟨⟨hk, hl, h0⟩, ⟨a, ha', hb, he⟩, hp⟩ := hz
  have := h.D_le
  refine ⟨⟨hk.keep h hf fun r hr => (ha r hr).1, hl.keep h hf fun r hr => (ha r hr).2.2.2.1, ?_⟩,
    ⟨a, slot_keep hf (fun r hr => (ha r hr).2.1) ha', hb, he⟩, slot_keep hf (fun r hr => (ha r hr).2.2.1) hp⟩
  rw [← h0]
  exact em_keep (n := 1) hf (fun r hr => (ha r hr).2.2.2.2) (by decide)
    (f := fun _ => m (sa P.scr 0)) (fun i hi => by rw [show i = 0 by omega]) 0 (by decide)

theorem away_buf {P : EP} (hg : Geo P.lay P.scr) {o n : Nat} (ho : oBuf ≤ o) (hn : o + n ≤ oSt) :
    Away h P (sR P.scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  have := h.D_le
  exact ⟨hg.slot ok (by oomega) (by rw [hg.F]; decide), hg.slot ok (by oomega) (by rw [hg.F]; decide),
    hg.slot ok (by oomega) (by rw [hg.F]; decide), Geo.sep (by oomega) (by oomega) (by oomega),
    Geo.sep (by oomega) (by oomega) (by oomega)⟩

theorem away_slot {P : EP} (hg : Geo P.lay P.scr) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sRes ∨ sRes + 4 ≤ d) (h₂ : d + 4 ≤ sAcc ∨ sAcc + 4 ≤ d) (h₃ : d + 4 ≤ sPos ∨ sPos + 4 ≤ d) :
    Away h P (slotR P.lay d) := by
  obtain ⟨σ', ok⟩ := hg.ok
  have := h.D_le
  exact ⟨slotSep (by decide) hd h₁.symm, slotSep (by decide) hd h₂.symm, slotSep (by decide) hd h₃.symm,
    (hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)).symm,
    (hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)).symm⟩

/-- Byte `i` of `T`, zero after its end. -/
abbrev Bp (P : EP) (σ : State) (i : Nat) : Byte := if i < tN h P then T h g P σ i else 0

/-- The shift's distance. -/
abbrev aV (P : EP) (σ : State) : Nat := idx h g P σ + 1

theorem idx_lt {P : EP} {σ : State} (ht : 0 < tN h P) : idx h g P σ < tN h P := by
  have := lzS_le (tN h P) (T h g P σ)
  simp only [idx, pzS]; split <;> omega

/-! ## `T` to the buffer -/

/-- The buffer holds `T`, zeros after it. -/
abbrev BF (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp h g P σ j

theorem buf_vp (P : EP) :
    VP (A2 h g P)
      (.seq (.block clrBuf) (.seq Impl.Bignum.Arm.maskBytes (.seq (.block (tSet h.H)) Impl.Bignum.Arm.copyBytes)))
      (BF h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1.1, hs.2.1.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  -- The buffer's 2048 bytes, zeros.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ (Zk h g P σ s.mem ∧
      ∀ x < P.K, s.mem (sa P.scr x) = V5 h g P σ x)) ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .r2 = 0 ∧
      s.gpr .lr = BitVec.ofNat 32 2048)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
      fun σ s ⟨hc, hy, ha, hp⟩ => ?_) ?_
  · have hw : WP isa (.block clrBuf) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧ t.gpr .r2 = 0 ∧ t.gpr .lr = BitVec.ofNat 32 2048 := by
      prun [clrBuf, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oBuf < 2 ^ 16 by decide), movw_val (show 2048 < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2, lr⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ ⟨⟨hy.1, ha, hp⟩, hy.2⟩⟩, r0, r2, lr⟩
  have aB : State.addr (P.scr + BitVec.ofNat 32 oBuf) = sa P.scr oBuf := hg.addr (by oomega)
  refine VP.seq ((zero_vp (hg.wbuf (o := oBuf) (n := 2048) (by oomega) (by decide)) (by decide)
    (Inv := fun σ m => Zk h g P σ m ∧ ∀ x < P.K, m (sa P.scr x) = V5 h g P σ x) fun σ m m' ⟨hz, he⟩ hf => by
      rw [aB] at hf
      exact ⟨hz.keep h g hf fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away_buf h hg (by oomega) (by oomega),
        em_keep hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by oomega) (by oomega) (by oomega))
          (by omega) he⟩).mono
    (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩) fun _ _ h => h) ?_
  -- `T` to the buffer.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ (Zk h g P σ s.mem ∧
      ∀ j < 2048, tN h P ≤ j → s.mem (sa P.scr (oBuf + j)) = 0)) ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
      s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D) ∧ s.gpr .lr = BitVec.ofNat 32 (tN h P) ∧
      ∀ i < tN h P, s.mem (byteAt (P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D)) i) = T h g P σ i)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
      fun σ s ⟨hc, ⟨hz, he⟩, hb⟩ => ?_) ?_
  · have hi := hz.1.1.1
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block (tSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D) ∧
        t.gpr .lr = BitVec.ofNat 32 (tN h P) := by
      prun [tSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a4, r4, v4, arg_lt,
        movw_val (show oBuf < 2 ^ 16 by decide), movw_val (show oEm + 1 + 2 * h.H.D < 2 ^ 16 by oomega),
        movw_val (show 2 * h.H.D + 1 < 2 ^ 16 by omega), Offset.ofNat_sub_ofNat (show 2 * h.H.D + 1 ≤ P.K by omega)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ =>
      ⟨⟨hc.regs rd wr sp m, ?_, fun j hj _ => ?_⟩, r0, r1, lr, fun i hi => ?_⟩
    · rw [m]; exact hz
    · rw [m, ← hg.byteAt_scr (by oomega)]; exact hb j hj
    · rw [m, hg.byteAt_scr (by oomega), show oEm + 1 + 2 * h.H.D + i = 1 + 2 * h.H.D + i by oomega]
      exact he _ (by omega)
  have aE : State.addr (P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D)) = sa P.scr (oEm + 1 + 2 * h.H.D) :=
    hg.addr (by oomega)
  refine (copy_vp (hg.wbuf (o := oBuf) (n := tN h P) (by oomega) (by omega))
    (hg.rbuf (o := oEm + 1 + 2 * h.H.D) (n := tN h P) (by oomega) (by omega))
    (by rw [aB, aE]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by omega)
    (Inv := fun σ m => Zk h g P σ m ∧ ∀ j < 2048, tN h P ≤ j → m (sa P.scr (oBuf + j)) = 0)
    (f := T h g P) fun σ m m' ⟨hz, hb⟩ hf => by
      rw [aB] at hf
      refine ⟨hz.keep h g hf fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away_buf h hg (by oomega) (by oomega),
        fun j hj hj' => ?_⟩
      rw [← hb j hj hj']
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega) (by oomega) (by oomega) _
          (Region.contains_self _ _)).mono
    (fun σ s ⟨⟨hc, hm⟩, r0, r1, lr, hf⟩ => ⟨hc, hm, r0, r1, lr, hf⟩)
    fun σ s ⟨hc, ⟨hz, hb⟩, ht⟩ => ⟨hc, hz, fun j hj => ?_⟩
  by_cases e : j < tN h P
  · rw [Bp, ite_eq_left e, ← ht j e, hg.byteAt_scr (by oomega)]
  · rw [Bp, ite_eq_right e]; exact hb j hj (by omega)

/-! ## The shift -/

/-- After `p` passes. -/
abbrev SH (P : EP) (σ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW (P.lay.fr sA) 32 = BitVec.ofNat 32 (aV h g P σ / 2 ^ p) ∧
    m.readW (P.lay.fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW (P.lay.fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2048, m (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ % 2 ^ p)

/-- The bounds a pass needs. -/
theorem shB {P : EP} {σ : State} {m : Mem} (hk : Zk h g P σ m) : 1 ≤ tN h P ∧ tN h P ≤ 1021 ∧ aV h g P σ < 1024 := by
  have hi := hk.1.1.1
  have hfit := hk.1.1.2.1
  have hK := hi.k1024
  have hD := h.D_pos
  have ht : 1 ≤ tN h P := by show 1 ≤ P.K - (2 * h.H.D + 1); omega
  have ht' : tN h P ≤ 1021 := by show P.K - (2 * h.H.D + 1) ≤ 1021; omega
  have := idx_lt h g (P := P) (σ := σ) (by omega)
  exact ⟨ht, ht', by show idx h g P σ + 1 < 1024; omega⟩

/-- A pass's registers. -/
theorem passSet_vp (P : EP) {p : Nat} (hp : p < 10) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) (.block passSet)
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 1024 ∧
        s.gpr .r2 = maskOf (aV h g P σ / 2 ^ p % 2 = 1)) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hs⟩ => ?_
  have hg := hk.1.1.1.geo
  obtain ⟨-, -, haV⟩ := shB h g hk
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
  have hav : aV h g P σ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hw : WP isa (.block passSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
      t.gpr .r1 = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ t.gpr .lr = BitVec.ofNat 32 1024 ∧
      t.gpr .r2 = 0 - (BitVec.ofNat 32 (aV h g P σ / 2 ^ p) &&& 1) := by
    prun [passSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hs.1, hs.2.1,
      movw_val (show oBuf < 2 ^ 16 by decide), movw_val (show 1024 < 2 ^ 16 by decide),
      movw_val (show 0 < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat, dpVal]
    rfl
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ =>
    ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hs⟩, r0, r1, lr, by rw [r2, Vf.mask_bit hav]⟩

/-- Between a pass's bytes and its next stage. -/
abbrev SM (P : EP) (σ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW (P.lay.fr sA) 32 = BitVec.ofNat 32 (aV h g P σ / 2 ^ p) ∧
    m.readW (P.lay.fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW (P.lay.fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2048, m (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ % 2 ^ (p + 1))

/-- A pass's bytes. -/
theorem passMid_vp (P : EP) (hP : ∃ σ, In P σ) {p : Nat} (hp : p < 10) :
    VP (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 1024 ∧
        s.gpr .r2 = maskOf (aV h g P σ / 2 ^ p % 2 = 1))
      (countLoop passBody)
      (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SM h g P σ p s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have e2 : oRsa = 8192 := rfl
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
  have hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  refine (pass_vp hg (o := oBuf) (d := 2 ^ p) (n := 1024) (by decide) hp0 (by oomega)
    (c := fun σ => aV h g P σ / 2 ^ p % 2 = 1) (X := fun σ m => Zk h g P σ m ∧ SH h g P σ p m)).mono
    (fun σ s ⟨⟨hc, hk, hs⟩, r0, r1, lr, r2⟩ => ⟨hc, ⟨hk, hs⟩, r0, r1, lr, r2⟩)
    fun σ s ⟨hc, m₀, ⟨hk, hs⟩, fr, hsel⟩ => ?_
  obtain ⟨ht1, ht, haV⟩ := shB h g hk
  have ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW (P.lay.fr d) 32 = m₀.readW (P.lay.fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW (P.lay.fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by oomega) (by rw [hg.F]; omega)) rfl
  refine ⟨hc, hk.keep h g fr fun r hr => ?_, by rw [ks _ (by decide)]; exact hs.1,
    by rw [ks _ (by decide)]; exact hs.2.1, by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact away_buf h hg (by oomega) (by oomega)
  have ms := Vf.mod_succ (aV h g P σ) p
  by_cases e : j < 1024
  · rw [hsel j e]
    by_cases hc' : aV h g P σ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oBuf + 2 ^ p + j = oBuf + (2 ^ p + j) by omega, hs.2.2.2 _ (by omega)]
      congr 1; rw [ms, hc']; omega
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show aV h g P σ / 2 ^ p % 2 = 0 by omega]; omega
  · have hm : s.mem (sa P.scr (oBuf + j)) = m₀ (sa P.scr (oBuf + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj]; unfold Bp; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp (P : EP) {p : Nat} (hp : p < 10) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SM h g P σ p s.mem) (.block passNext)
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ (p + 1) s.mem) ∧
        s.z = decide (10 - (p + 1) = 0)) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hs⟩ => ?_
  have hi := hk.1.1.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨-, -, haV⟩ := shB h g hk
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
  have ea : BitVec.ofNat 32 (aV h g P σ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (aV h g P σ / 2 ^ (p + 1)) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)), Nat.div_div_eq_div_mul,
      Nat.pow_one, ← Nat.pow_succ]
  have ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega
  have ec : BitVec.ofNat 32 (10 - p) - 1 = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [show 10 - p = (10 - (p + 1)) + 1 by omega]; exact sub_one_ofNat (by omega)
  have hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
  have w1 : ∀ v, (s.mem.writeW (P.lay.fr sA) v).readW (P.lay.fr sD) 32 = BitVec.ofNat 32 (2 ^ p) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hs.2.1
  have w2 : ∀ v v', ((s.mem.writeW (P.lay.fr sA) v).writeW (P.lay.fr sD) v').readW
      (P.lay.fr sPc) 32 = BitVec.ofNat 32 (10 - p) := fun v v' => by
    rw [slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide)]
    exact hs.2.2.1
  have hw : WP isa (.block passNext) s fun t =>
      t.mem = ((s.mem.writeW (P.lay.fr sA) (BitVec.ofNat 32 (aV h g P σ / 2 ^ (p + 1)))).writeW
        (P.lay.fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW (P.lay.fr sPc)
          (BitVec.ofNat 32 (10 - (p + 1))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = decide (10 - (p + 1) = 0) := by
    prun [passNext, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hs.1, hs.2.1, hs.2.2.1,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide), ea, ed, ec, hz0, w1, w2,
      VG.Proof.X25519.Arm.ofNat_beq_zero (show 10 - (p + 1) < 2 ^ 32 by omega), dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  have fr : Frame [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  have aw : ∀ r ∈ [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc], Away h P r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact away_slot h hg (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h g fr aw, ?_, ?_, ?_,
    sbytes_keep fr (fun r hr => ?_) (by oomega) hs.2.2.2⟩, z⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

/-- A pass. -/
theorem onePass_vp (P : EP) (hP : ∃ σ, In P σ) {p : Nat} (hp : p < 10) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) passOne
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ (p + 1) s.mem) ∧
        s.z = decide (10 - (p + 1) = 0)) :=
  (passSet_vp h g P hp).seq ((passMid_vp h g P hP hp).seq (passNext_vp h g P hp))

/-- The shift's distance, its first pass's, and its passes. -/
theorem shInit_vp (P : EP) :
    VP (BF h g P) (.block shInit) (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ 0 s.mem) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hw : WP isa (.block shInit) s fun t =>
      t.mem = ((s.mem.writeW (P.lay.fr sA) (BitVec.ofNat 32 (aV h g P σ))).writeW
        (P.lay.fr sD) (BitVec.ofNat 32 1)).writeW (P.lay.fr sPc) (BitVec.ofNat 32 10) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [shInit, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.2.2,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide),
      movw_val (show 1 < 2 ^ 16 by decide), movw_val (show 10 < 2 ^ 16 by decide),
      VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  have aw : ∀ r ∈ [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc], Away h P r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact away_slot h hg (by decide) (by decide) (by decide) (by decide)
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h g fr aw, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Nat.pow_zero, Nat.div_one]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [Nat.pow_zero, Nat.mod_one, Nat.add_zero]
    refine (sbytes_keep fr (fun r hr => ?_) (by oomega) hy) j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

/-- After the shift: the buffer holds `T` from byte `idx + 1` on, zeros after it. -/
abbrev SF (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ)

/-- `T` shifted left by `idx + 1` bytes. -/
theorem shift_vp (P : EP) : VP (BF h g P) shift (SF h g P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1.1⟩
  refine (shInit_vp h g P).seq ?_
  let I : Nat → State → State → Prop := fun k σ s => k ≤ 10 ∧ Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧
    SH h g P σ (10 - k) s.mem
  refine (VP.loop (I := I) (fun k => ?_) 9).mono (fun σ s ⟨hc, hk, hs⟩ => ⟨by omega, hc, hk, hs⟩) fun _ _ h => h
  by_cases hk : k ≤ 9
  swap
  · exact VP.empty fun σ s h' => hk (by have := h'.1; omega)
  refine (onePass_vp h g P hP (p := 9 - k) (by omega)).mono
    (fun σ s ⟨_, hc, hq, hs⟩ => ⟨hc, hq, by rw [show 9 - k = 10 - (k + 1) by omega]; exact hs⟩)
    fun σ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩, fun hpos => ⟨by omega, hc, hq, ?_⟩⟩
  · rw [VG.Proof.X25519.Arm.eval_ne, z, show 10 - (9 - k + 1) = k by omega]; cases k <;> simp
  · subst h0
    obtain ⟨-, -, haV⟩ := shB h g hq
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show aV h g P σ < 2 ^ (9 - 0 + 1) by
      show aV h g P σ < 1024; omega)]
  · rw [show 10 - k = 9 - k + 1 by omega]; exact hs

end VG.Proof.RsaOaep.Arm.Dec
