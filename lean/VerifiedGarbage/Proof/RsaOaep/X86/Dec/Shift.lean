module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Scan
public import VerifiedGarbage.Proof.RsaPss.X86.VfPass
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86: `T` shifted to the start of the buffer

As on ARMv7 (`Proof/RsaOaep/Arm/DecShift.lean`): the buffer of 2048 bytes
at `oBuf` cleared and `T` copied to its start (`buf_vp`); then shifted left
by `idx + 1` bytes in ten passes (`shift_vp`, with the passes of RSASSA-PSS,
`Proof/RsaPss/X86/VfPass.lean`), pass `p` by `2^p` bytes if bit `p` of the
distance is set, so that no address depends on `idx`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi addSlot sAcc sPos sA sD sPc countLoop passBody
  passNext shInit zeroLoop clrArgs)

variable (h g : OHash)

/-- What the copy and the shift keep. -/
abbrev Zk (P : EP) (σ : State) (m : Mem) : Prop :=
  X1 h P σ m ∧ (∃ a : BitVec 32, m.readW (P.lay.fr sAcc) 32 = a ∧ (a = 0 ↔ allOk h g P σ)) ∧
    m.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ)

/-- What misses those. -/
abbrev Away (P : EP) (r : Region) : Prop :=
  (slotR P.lay sRes).Disjoint r ∧ (slotR P.lay sAcc).Disjoint r ∧ (slotR P.lay sPos).Disjoint r ∧
    (sR P.scr oLh h.H.D).Disjoint r ∧ (sR P.scr oEm 1).Disjoint r

theorem Zk.keep {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hz : Zk h g P σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, Away h P r) : Zk h g P σ m' := by
  obtain ⟨⟨hk, hl, h0⟩, ⟨a, ha', he⟩, hp⟩ := hz
  have := h.D_le
  refine ⟨⟨hk.keep h hf fun r hr => (ha r hr).1, hl.keep h hf fun r hr => (ha r hr).2.2.2.1, ?_⟩,
    ⟨a, slot_keep hf (fun r hr => (ha r hr).2.1) ha', he⟩, slot_keep hf (fun r hr => (ha r hr).2.2.1) hp⟩
  rw [← h0]
  exact sbytes_keep (o := oEm) (n := 1) hf (fun r hr => (ha r hr).2.2.2.2) (by oomega)
    (f := fun _ => m (sa P.scr (oEm + 0))) (fun i hi => by rw [show i = 0 by omega_arith]) 0 (by decide)

theorem away_buf {P : EP} (hg : Geo P.lay P.scr) {o n : Nat} (ho : oBuf ≤ o) (hn : o + n ≤ oRsa) :
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
    (hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_arith)).symm,
    (hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_arith)).symm⟩

/-- Byte `i` of `T`, zero after its end. -/
abbrev Bp (P : EP) (σ : State) (i : Nat) : Byte := if i < tN h P then T h g P σ i else 0

/-- The shift's distance. -/
abbrev aV (P : EP) (σ : State) : Nat := idx h g P σ + 1

theorem idx_lt {P : EP} {σ : State} (ht : 0 < tN h P) : idx h g P σ < tN h P := by
  have := lzS_le (tN h P) (T h g P σ)
  simp only [idx, pzS]; split <;> omega_arith

/-! ## `T` to the buffer -/

/-- The buffer holds `T`, zeros after it. -/
abbrev BF (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp h g P σ j

theorem buf_vp (P : EP) {c : Prog isa} {Q : State → State → Prop} (k : VP (BF h g P) c Q) :
    VP (A2 h g P)
      (.seq (.block (clrArgs oBuf 2048)) (.seq zeroLoop (.seq (.block (tSet h.H)) (.seq Impl.Bignum.X86.copyBytes c))))
      Q := by
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
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ (Zk h g P σ s.mem ∧ EMv P s.mem (V5 h g P σ))) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧ s.gpr .ecx = BitVec.ofNat 32 2048 ∧ s.gpr .eax = 0)
    (VP.taint [.esp, .ebp] clrBuf_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hy, ha, hp⟩ => ?_) ?_
  · simp only [clrArgs, atS, addi, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
      (by decide)).upd u4 (by decide) (by decide), m4 ▸ ⟨⟨hy.1, ha, hp⟩, hy.2⟩⟩, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u4.other _ (by decide), u3.gpr]
    · rw [u4.gpr]; rfl
  have aB : (P.scr + BitVec.ofNat 32 oBuf).setWidth 64 = sa P.scr oBuf := hg.scrA (by oomega)
  have aE : (P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D)).setWidth 64 = sa P.scr (oEm + 1 + 2 * h.H.D) :=
    hg.scrA (by oomega)
  refine VP.seq ((zero_vp (scr := P.scr) (hg.wbuf (o := oBuf) (n := 2048) (by oomega) (by decide)) (by decide)
    (Inv := fun σ m => Zk h g P σ m ∧ EMv P m (V5 h g P σ)) fun σ m m' ⟨hz, he⟩ hf => by
      rw [aB] at hf
      exact ⟨hz.keep h g hf fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away_buf h hg (by oomega) (by oomega),
        he.keep hf hK fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by oomega) (by oomega) (by oomega)⟩).mono
    (fun σ s ⟨⟨hc, hm⟩, si, cx, ax⟩ => ⟨hc, hm, si, cx, ax⟩) fun _ _ h => h) ?_
  -- `T` to the buffer.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ (Zk h g P σ s.mem ∧
      ∀ j < 2048, tN h P ≤ j → s.mem (sa P.scr (oBuf + j)) = 0)) ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 oBuf ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D) ∧ s.gpr .ecx = BitVec.ofNat 32 (tN h P) ∧
      ∀ i < tN h P, s.mem (byteAt (P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D)) i) = T h g P σ i)
    (VP.taint [.esp, .ebp] h.certs.tSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hz, he⟩, hb⟩ => ?_) ?_
  · simp only [tSet, atS, addi, ld, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
    have c4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
      (by decide)).upd u4 (by decide) (by decide)
    refine c4.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t5 c5 u5 =>
      wp_subi fun t6 u6 _ _ => WP.block_nil ?_
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c5.upd u6 (by decide) (by decide), ?_, fun j hj _ => ?_⟩, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [m6]; exact hz
    · rw [m6, ← hg.byteAt_scr (by oomega)]; exact hb j hj
    · simp (disch := decide) only [u6.other, u5.other, u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u6.gpr, u5.gpr]
      show BitVec.ofNat 32 P.K - BitVec.ofNat 32 (2 * h.H.D + 1) = _
      rw [sub_ofNat (by omega_arith)]
    · rw [m6, hg.byteAt_scr (by oomega), show oEm + 1 + 2 * h.H.D + i = oEm + (1 + 2 * h.H.D + i) by omega_arith]
      exact he _ (by omega_arith)
  refine VP.seq ((copy_vp (scr := P.scr) (hg.wbuf (o := oBuf) (n := tN h P) (by oomega) (by omega_arith))
    (hg.rbuf (o := oEm + 1 + 2 * h.H.D) (n := tN h P) (by oomega) (by omega_arith))
    (by rw [aB, aE]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by omega_arith)
    (Inv := fun σ m => Zk h g P σ m ∧ ∀ j < 2048, tN h P ≤ j → m (sa P.scr (oBuf + j)) = 0)
    (f := T h g P) fun σ m m' ⟨hz, hb⟩ hf => by
      rw [aB] at hf
      refine ⟨hz.keep h g hf fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away_buf h hg (by oomega) (by oomega),
        fun j hj hj' => ?_⟩
      rw [← hb j hj hj']
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega_arith) (by oomega) (by oomega) _
          (Region.contains_self _ _)).mono
    (fun σ s ⟨⟨hc, hm⟩, bx, si, cx, hf⟩ => ⟨hc, hm, bx, si, cx, hf⟩)
    fun σ s ⟨hc, ⟨hz, hb⟩, ht⟩ => ⟨hc, hz, fun j hj => ?_⟩) k
  by_cases e : j < tN h P
  · rw [Bp, ite_eq_left e, ← ht j e, hg.byteAt_scr (by oomega)]
  · rw [Bp, ite_eq_right e]; exact hb j hj (by omega_arith)

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
  have ht : 1 ≤ tN h P := by show 1 ≤ P.K - (2 * h.H.D + 1); omega_arith
  have ht' : tN h P ≤ 1021 := by show P.K - (2 * h.H.D + 1) ≤ 1021; omega_arith
  have := idx_lt h g (P := P) (σ := σ) (by omega_arith)
  exact ⟨ht, ht', by show idx h g P σ + 1 < 1024; omega_arith⟩

theorem mask_bit {v : Nat} (hv : v < 2 ^ 32) : 0 - (BitVec.ofNat 32 v &&& 1) = maskOf (v % 2 = 1) := by
  have e : BitVec.ofNat 32 v &&& 1 = BitVec.ofNat 32 (v % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    rw [show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]; omega_arith
  rw [e]; unfold maskOf
  rcases Nat.mod_two_eq_zero_or_one v with e' | e' <;> rw [e'] <;> decide

theorem mod_succ (a p : Nat) : a % 2 ^ (p + 1) = a % 2 ^ p + 2 ^ p * (a / 2 ^ p % 2) := by
  rw [Nat.pow_succ, Nat.mod_mul]

/-- A pass's registers. -/
theorem passSet_vp (P : EP) {p : Nat} (hp : p < 10) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) (.block passSet)
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) ∧
        s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 1024 ∧
        s.gpr .edx = maskOf (aV h g P σ / 2 ^ p % 2 = 1)) := by
  refine VP.taint [.esp, .ebp] passSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hs⟩ => ?_
  have hg := hk.1.1.1.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨-, -, haV⟩ := shB h g hk
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hav : aV h g P σ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)
  simp only [passSet, atS, addSlot, addi, ld, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => ?_
  have c3 : Ctx P.lay P.scr σ t3 :=
    ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
  refine wp_addm (B := P.lay.B) (by rw [c3.st.sp])
    (by rw [hg.aFr ok sD (by decide)]; exact c3.rFr hg sD (by decide)) fun t4 u4 => ?_
  have c4 : Ctx P.lay P.scr σ t4 := c3.upd u4 (by decide) (by decide)
  refine c4.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_andi fun t6 u6 => wp_movi fun t7 u7 => wp_sub fun t8 u8 _ => wp_movi fun t9 u9 => WP.block_nil ?_
  have c9 : Ctx P.lay P.scr σ t9 :=
    (((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)).upd u9
      (by decide) (by decide)
  have m9 : t9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have esi2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 oBuf := by rw [u2.gpr, u1.gpr, hc.ebp]
  refine ⟨⟨c9, m9 ▸ hk, m9 ▸ hs⟩, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, esi2]
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.gpr, u3.gpr, esi2]
    rw [u3.mem, u2.mem, u1.mem, hg.aFr ok sD (by decide), hs.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [u9.gpr]
  · simp (disch := decide) only [u9.other, u8.gpr, u7.gpr, u7.other, u6.gpr, u5.gpr]
    rw [u4.mem, u3.mem, u2.mem, u1.mem, hs.1]
    exact mask_bit hav

/-- Between a pass's bytes and its next stage. -/
abbrev SM (P : EP) (σ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW (P.lay.fr sA) 32 = BitVec.ofNat 32 (aV h g P σ / 2 ^ p) ∧
    m.readW (P.lay.fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW (P.lay.fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2048, m (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ % 2 ^ (p + 1))

/-- A pass's bytes. -/
theorem passMid_vp (P : EP) (hP : ∃ σ, In P σ) {p : Nat} (hp : p < 10) :
    VP (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) ∧
        s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oBuf + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 1024 ∧
        s.gpr .edx = maskOf (aV h g P σ / 2 ^ p % 2 = 1))
      (countLoop passBody)
      (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SM h g P σ p s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  refine (pass_vp hg (o := oBuf) (d := 2 ^ p) (n := 1024) (by decide) hp0 (by oomega)
    (c := fun σ => aV h g P σ / 2 ^ p % 2 = 1) (X := fun σ m => Zk h g P σ m ∧ SH h g P σ p m)).mono
    (fun σ s ⟨⟨hc, hk, hs⟩, si, di, cx, dx⟩ => ⟨hc, ⟨hk, hs⟩, si, di, cx, dx⟩)
    fun σ s ⟨hc, m₀, ⟨hk, hs⟩, fr, hsel⟩ => ?_
  obtain ⟨ht1, ht, haV⟩ := shB h g hk
  have ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW (P.lay.fr d) 32 = m₀.readW (P.lay.fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW (P.lay.fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_arith)) rfl
  refine ⟨hc, hk.keep h g fr fun r hr => ?_, by rw [ks _ (by decide)]; exact hs.1,
    by rw [ks _ (by decide)]; exact hs.2.1, by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact away_buf h hg (by oomega) (by oomega)
  have ms := mod_succ (aV h g P σ) p
  by_cases e : j < 1024
  · rw [hsel j e]
    by_cases hc' : aV h g P σ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oBuf + 2 ^ p + j = oBuf + (2 ^ p + j) by omega_arith, hs.2.2.2 _ (by oomega)]
      congr 1; rw [ms, hc']; omega_arith
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show aV h g P σ / 2 ^ p % 2 = 0 by omega_arith]; omega_arith
  · have hm : s.mem (sa P.scr (oBuf + j)) = m₀ (sa P.scr (oBuf + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oBuf + j) (n := 1) (by omega_arith) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj]; unfold Bp; rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

/-- Three words stored in the slots of the shift. -/
theorem fr3 (L : Lay) (m : Mem) (a b c : BitVec 32) :
    Frame [slotR L sA, slotR L sD, slotR L sPc] m (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c) :=
  ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
    ((slot_frame _ _ _ _).mono (by simp))

/-- The words of the three slots after the stores. -/
theorem rd3 (L : Lay) (m : Mem) (a b c : BitVec 32) :
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sA) 32 = a ∧
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sD) 32 = b ∧
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sPc) 32 = c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- What the shift's slots keep. -/
theorem keep3 (P : EP) (hg : Geo P.lay P.scr) {σ : State} {m m' : Mem}
    (hf : Frame [slotR P.lay sA, slotR P.lay sD, slotR P.lay sPc] m m') (hk : Zk h g P σ m)
    {f : Nat → Byte} (hy : ∀ j < 2048, m (sa P.scr (oBuf + j)) = f j) :
    Zk h g P σ m' ∧ ∀ j < 2048, m' (sa P.scr (oBuf + j)) = f j := by
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hk.keep h g hf fun r hr => ?_, sbytes_keep hf (fun r hr => ?_) (by oomega) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact away_slot h hg (by decide) (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp (P : EP) {p : Nat} (hp : p < 10) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SM h g P σ p s.mem) (.block passNext)
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ (p + 1) s.mem) ∧
        s.zf = some (decide (10 - (p + 1) = 0))) := by
  refine VP.taint [.esp, .ebp] passNext_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hs⟩ => ?_
  have hg := hk.1.1.1.geo
  obtain ⟨-, -, haV⟩ := shB h g hk
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have ea : BitVec.ofNat 32 (aV h g P σ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (aV h g P σ / 2 ^ (p + 1)) := by
    rw [ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)), Nat.div_div_eq_div_mul,
      Nat.pow_one, ← Nat.pow_succ]
  have ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega_arith
  have ec : BitVec.ofNat 32 (10 - p) - 1 = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [ofNat_pred (by omega_arith), Nat.sub_sub]
  simp only [passNext, ld, st]
  refine hc.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_shr (by decide) fun t2 u2 _ => ?_
  refine (c1.upd u2 (by decide) (by decide)).wp_st hg (d := sA) (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_slot hg (d := sD) (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_add fun t5 u5 _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t6 c6 m6 => ?_
  refine c6.wp_slot hg (d := sPc) (by decide) (by decide) (by decide) fun t7 c7 u7 => ?_
  refine wp_subi fun t8 u8 _ z8 => (c7.upd u8 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t9 c9 m9 => WP.block_nil ?_
  have va : t2.gpr .eax = BitVec.ofNat 32 (aV h g P σ / 2 ^ (p + 1)) := by rw [u2.gpr, u1.gpr, hs.1, ea]
  have m3' : t3.mem = s.mem.writeW (P.lay.fr sA) (BitVec.ofNat 32 (aV h g P σ / 2 ^ (p + 1))) := by
    rw [m3.mem, va, u2.mem, u1.mem]
  have vd : t5.gpr .eax = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [u5.gpr, u4.gpr, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.1, ed]
  have vc : t8.gpr .eax = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [u8.gpr, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec]
  have mm : t9.mem = ((s.mem.writeW (P.lay.fr sA) (BitVec.ofNat 32 (aV h g P σ / 2 ^ (p + 1)))).writeW
      (P.lay.fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW (P.lay.fr sPc)
        (BitVec.ofNat 32 (10 - (p + 1))) := by
    rw [m9.mem, vc, u8.mem, u7.mem, m6.mem, vd, u5.mem, u4.mem, m3']
  obtain ⟨hk', hy'⟩ := keep3 h g P hg (mm ▸ fr3 _ _ _ _ _) hk hs.2.2.2
  obtain ⟨r1, r2, r3⟩ := rd3 P.lay s.mem (BitVec.ofNat 32 (aV h g P σ / 2 ^ (p + 1)))
    (BitVec.ofNat 32 (2 ^ (p + 1))) (BitVec.ofNat 32 (10 - (p + 1)))
  rw [← mm] at r1 r2 r3
  refine ⟨⟨c9, hk', r1, r2, r3, hy'⟩, ?_⟩
  rw [m9.zf, z8, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
    Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec, ofNat_beq_zero (by omega_arith)]

/-- A pass. -/
theorem onePass_vp (P : EP) (hP : ∃ σ, In P σ) {p : Nat} (hp : p < 10) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ p s.mem) passOne
      (fun σ s => (Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ (p + 1) s.mem) ∧
        s.zf = some (decide (10 - (p + 1) = 0))) :=
  (passSet_vp h g P hp).seq ((passMid_vp h g P hP hp).seq (passNext_vp h g P hp))

/-- The shift's distance, its first pass's, and its passes. -/
theorem shInit_vp (P : EP) :
    VP (BF h g P) (.block shInit) (fun σ s => Ctx P.lay P.scr σ s ∧ Zk h g P σ s.mem ∧ SH h g P σ 0 s.mem) := by
  refine VP.taint [.esp, .ebp] shInit_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hy⟩ => ?_
  have hg := hk.1.1.1.geo
  simp only [shInit, ld, st, mi, addi]
  refine hc.wp_slot hg (d := sPos) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_addi fun t2 u2 => (c1.upd u2 (by decide) (by decide)).wp_st hg (d := sA) (by decide)
    fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t5 c5 m5 => ?_
  refine wp_movi fun t6 u6 => (c5.upd u6 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t7 c7 m7 => WP.block_nil ?_
  have mm : t7.mem = ((s.mem.writeW (P.lay.fr sA) (BitVec.ofNat 32 (aV h g P σ))).writeW
      (P.lay.fr sD) (BitVec.ofNat 32 1)).writeW (P.lay.fr sPc) (BitVec.ofNat 32 10) := by
    rw [m7.mem, u6.gpr, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, u2.gpr, u1.gpr, u2.mem, u1.mem, hk.2.2,
      BitVec.ofNat_add_ofNat]
  obtain ⟨hk', hy'⟩ := keep3 h g P hg (mm ▸ fr3 _ _ _ _ _) hk hy
  obtain ⟨r1, r2, r3⟩ := rd3 P.lay s.mem (BitVec.ofNat 32 (aV h g P σ)) (BitVec.ofNat 32 1) (BitVec.ofNat 32 10)
  rw [← mm] at r1 r2 r3
  refine ⟨c7, hk', ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [r1, Nat.pow_zero, Nat.div_one]
  · rw [r2]
  · rw [r3]
  · rw [hy' j hj, Nat.pow_zero, Nat.mod_one, Nat.add_zero]

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
  refine (VP.loop (I := I) (fun k => ?_) 9).mono (fun σ s ⟨hc, hk, hs⟩ => ⟨by omega_arith, hc, hk, hs⟩) fun _ _ h => h
  by_cases hk : k ≤ 9
  swap
  · exact VP.empty fun σ s h' => hk (by have := h'.1; omega_arith)
  refine (onePass_vp h g P hP (p := 9 - k) (by omega_arith)).mono
    (fun σ s ⟨_, hc, hq, hs⟩ => ⟨hc, hq, by rw [show 9 - k = 10 - (k + 1) by omega_arith]; exact hs⟩)
    fun σ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩, fun hpos => ⟨by omega_arith, hc, hq, ?_⟩⟩
  · show eval .ne s = _
    simp only [eval, z, show 10 - (9 - k + 1) = k by omega_arith]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega_arith
  · subst h0
    obtain ⟨-, -, haV⟩ := shB h g hq
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show aV h g P σ < 2 ^ (9 - 0 + 1) by
      show aV h g P σ < 1024; omega_arith)]
  · rw [show 10 - k = 9 - k + 1 by omega_arith]; exact hs

end VG.Proof.RsaOaep.X86.Dec
