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
import VerifiedGarbage.Proof.RsaOaep.X86.Instr
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT

/-! ### `RsaOaep.X86.Dec.End`, which only this module used -/

section

/-! ### `RsaOaep.X86.Dec.Out`, which only this module used -/

section

/-! ### `RsaOaep.X86.Dec.Shift`, which only this module used -/

section

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

end

end


/-!
# RSAES-OAEP decryption on x86: the output

As on ARMv7 (`Proof/RsaOaep/Arm/DecOut.lean`): `ok` (all ones exactly when
the private-key operation succeeded and every check passed) to its slot
(`okMask_vp`); then `out` from the buffer, each byte ANDed with `ok`
(`outLoop_vp`): the message after `T`'s padding, zeros after it, or zeros.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sAcc sPos countLoop)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## A masked copy -/

section
variable {L : Lay} {scr : BitVec 32}

theorem and8 (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 :=
  BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi, show i < 32 by omega_using [hi]]

/-- After `j` bytes of the masked copy. -/
structure OI (src dst : BitVec 32) (n : Nat) (f : Nat → Byte) (w : BitVec 32) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = src + BitVec.ofNat 32 j
  edi : s.gpr .edi = dst + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  edx : s.gpr .edx = w
  out : ∀ i < j, s.mem (byteAt dst i) = f i &&& w.setWidth 8

/-- The `n` bytes at `src`, ANDed with the low byte of `w σ`, to `dst`. -/
theorem outLoop_vp {src dst : BitVec 32} {n : Nat} (hd : WBuf L dst n) (hs : RBuf L src n)
    (hn : 0 < n) {X : State → Mem → Prop} (hX : ∀ σ m m', X σ m → Frame [⟨dst.setWidth 64, n⟩] m m' → X σ m')
    {f : State → Nat → Byte} (hf : ∀ σ m, X σ m → ∀ i < n, m (byteAt src i) = f σ i) {w : State → BitVec 32} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .esi = src ∧ s.gpr .edi = dst ∧
        s.gpr .ecx = BitVec.ofNat 32 n ∧ s.gpr .edx = w σ)
      (countLoop outBody)
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ ∀ i < n, s.mem (byteAt dst i) = f σ i &&& (w σ).setWidth 8) := by
  have fit := hd.fit
  have fis := hs.fit
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧ X σ s.mem ∧
    OI src dst n (f σ) (w σ) (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, si, di, cx, dx⟩ => ⟨by omega_using [hn], hc, hx,
    ⟨by rw [si, show n - (n - 1 + 1) = 0 by omega_using [], BitVec.add_zero],
      by rw [di, show n - (n - 1 + 1) = 0 by omega_using [], BitVec.add_zero],
      by rw [cx, show n - (n - 1 + 1) = 0 by omega_using []]; rfl, dx, fun i hi => by omega⟩⟩) fun _ _ h => h
  refine VP.taint _ outBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, hx, hp⟩ => ?_
  · obtain ⟨-, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : n - (k + 1) = j at hp
  have hjn : j < n := by omega_using [hn, hj]
  have az : ∀ x : BitVec 32, addr x 0 = x.setWidth 64 := fun x => by simp [addr]
  simp only [outBody, addi, Impl.RsaPkcs1Sig.X86.at_]
  refine wp_movzx8 (a := byteAt src j) (by rw [ea_at, hp.esi, az, byte32 fis hjn]) (hs.inR hc.st hjn)
    fun t1 u1 => wp_and fun t2 u2 => ?_
  have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_store8 (a := byteAt dst j)
    (by rw [ea_at, u2.other _ (by decide), u1.other _ (by decide), hp.edi, az, byte32 fit hjn])
    (by rw [u2.wr, u1.wr]; exact hd.inW hc.st hjn) fun t3 m3 => ?_
  refine wp_addi fun t4 u4 => wp_addi fun t5 u5 => wp_subi fun t6 u6 _ z6 => WP.block_nil ?_
  have v2 : t2.gpr .eax = (f σ j).setWidth 32 &&& w σ := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), hp.edx, hf σ s.mem hx j hjn]
  have mm : t6.mem = s.mem.writeW (byteAt dst j) (f σ j &&& (w σ).setWidth 8) := by
    rw [u6.mem, u5.mem, u4.mem, m3.mem]
    show t2.mem.writeW _ ((t2.gpr .eax).setWidth 8) = _
    rw [v2, and8, u2.mem, u1.mem]
  have fr : Frame [⟨dst.setWidth 64, n⟩] s.mem t6.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_byte (Region.contains_self _ _) fit hjn)
  have g6 : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ecx → r ≠ .eax → t6.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u6.other _ h3, u5.other _ h2, u4.other _ h1, m3.gpr, u2.other _ h4, u1.other _ h4]
  have c6 : Ctx L scr σ t6 := hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.sub)
    (by rw [u6.rd, u5.rd, u4.rd, m3.rd, u2.rd, u1.rd]) (by rw [u6.wr, u5.wr, u4.wr, m3.wr, u2.wr, u1.wr])
    (g6 _ (by decide) (by decide) (by decide) (by decide)) (g6 _ (by decide) (by decide) (by decide) (by decide))
  have c5 : t5.gpr .ecx = BitVec.ofNat 32 (n - j) := by
    rw [u5.other _ (by decide), u4.other _ (by decide), m3.gpr, u2.other _ (by decide), u1.other _ (by decide), hp.ecx]
  have sk : OI src dst n (f σ) (w σ) (j + 1) t6 := by
    refine ⟨?_, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, m3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), hp.esi, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), m3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), hp.edi, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u6.gpr, c5, ofNat_pred (by omega_using [hn, hj]), Nat.sub_sub]
    · rw [g6 _ (by decide) (by decide) (by decide) (by decide), hp.edx]
    · rw [mm, VG.WriteBytes.writeW8_apply]
      by_cases e : i = j
      · subst e; simp
      · rw [ite_eq_right fun h' => e (byteAt_inj fit (by omega_using [hn, hj, hi]) hjn h')]
        exact hp.out i (by omega_using [hi, e])
  rw [c5, ofNat_pred (by omega_using [hn, hj]), Nat.sub_sub, ofNat_beq_zero (by omega_using [fit]), show n - (j + 1) = k by omega_using [hk, hj]] at z6
  refine ⟨?_, fun h0 => ⟨c6, hX σ _ _ hx fr, fun i hi => sk.out i (by omega_using [hj, h0, hi])⟩,
    fun hpos => ⟨by omega_using [hk], c6, hX σ _ _ hx fr, by rw [show n - k = j + 1 by omega_using [hk, hj]]; exact sk⟩⟩
  show eval .ne t6 = _
  simp only [eval, z6]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega_using [h0]

end

theorem and_maskOf (b : Byte) (c : Prop) [Decidable c] : b &&& (maskOf c).setWidth 8 = if c then b else 0 := by
  unfold maskOf
  by_cases hc : c
  · rw [ifp hc, ifp hc]; exact BitVec.and_allOnes
  · rw [ifn hc, ifn hc]; exact BitVec.and_zero

theorem maskOf_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : maskOf p = maskOf q := by
  unfold maskOf
  by_cases hp : p
  · rw [ifp hp, ifp (h.mp hp)]
  · rw [ifn hp, ifn fun hq => hp (h.mpr hq)]

theorem lt_one_iff (x : BitVec 32) : x.toNat < (1 : BitVec 32).toNat ↔ x = 0 := by
  constructor
  · intro h
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [e1] at h
    apply BitVec.eq_of_toNat_eq
    show x.toNat = 0
    omega_using [h]
  · rintro rfl; decide

/-- `ok`, as `okMask` computes it: the borrow of `((r ⊕ 1) ∨ acc) - 1`. -/
theorem okBit (o : Spec.Rsa.Outcome) (a : BitVec 32) :
    (if decide (((rOf o ^^^ 1) ||| a).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32 else 0) =
      maskOf (rOf o = 1 ∧ a = 0) := by
  have hx : (rOf o ^^^ 1) ||| a = 0 ↔ rOf o = 1 ∧ a = 0 := by
    rw [or_eq_zero32]
    cases o <;> simp only [rOf] <;> exact and_congr_left fun _ => by decide
  unfold maskOf
  by_cases hc : rOf o = 1 ∧ a = 0
  · rw [ifp hc, decide_eq_true ((lt_one_iff _).mpr (hx.mpr hc))]; rfl
  · rw [ifn hc, decide_eq_false fun h' => hc (hx.mp ((lt_one_iff _).mp h'))]; rfl

variable (h g : OHash)

/-- Every check passed, and the operation succeeded. -/
abbrev okP (P : EP) (σ : State) : Prop := rV P σ = 1 ∧ allOk h g P σ
abbrev okW (P : EP) (σ : State) : BitVec 32 := maskOf (okP h g P σ)

/-- The message's length, or zero. -/
abbrev mlV (P : EP) (σ : State) : Nat := if okP h g P σ then P.K - (2 * h.H.D + 2) - idx h g P σ else 0

/-- What the output keeps: `K0`, `idx` and `ok` in their slots. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  K0 h P σ m ∧ m.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ) ∧
    m.readW (P.lay.fr sOk) 32 = okW h g P σ

theorem Ko.keep {P : EP} {σ : State} {rs : List Region} {m m' : Mem} (hk : Ko h g P σ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, (slotR P.lay sRes).Disjoint r ∧ (slotR P.lay sPos).Disjoint r ∧ (slotR P.lay sOk).Disjoint r) :
    Ko h g P σ m' :=
  ⟨hk.1.keep h hf fun r hr => (ha r hr).1, slot_keep hf (fun r hr => (ha r hr).2.1) hk.2.1,
    slot_keep hf (fun r hr => (ha r hr).2.2) hk.2.2⟩

/-- After `ok`: `out` from the buffer. -/
abbrev O1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧ ∀ j < 2048, s.mem (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ)

theorem okMask_vp (P : EP) : VP (SF h g P) (.block okMask) (O1 h g P) := by
  refine VP.taint [.esp, .ebp] okMask_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hx, ⟨a, ha, hae⟩, hp⟩, hb⟩ => ?_
  have hi := hx.1.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  simp only [okMask, ld, st, Impl.RsaPkcs1Sig.X86.stk]
  refine hc.wp_slot hg (d := sRes) (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_xorI fun t2 u2 => ?_
  have c2 := c1.upd u2 (by decide) (by decide)
  refine wp_orm (B := P.lay.B) (by rw [c2.st.sp]) (by rw [hg.aFr ok sAcc (by decide)]; exact c2.rFr hg sAcc (by decide))
    fun t3 u3 => wp_cmpi fun t4 f4 cf4 _ => wp_sbb_self cf4 fun t5 u5 => ?_
  have c5 := ((c2.upd u3 (by decide) (by decide)).fupd f4).upd u5 (by decide) (by decide)
  refine c5.wp_st hg (d := sOk) (by decide) fun t6 c6 m6 => WP.block_nil ?_
  have m5 : t5.mem = s.mem := by rw [u5.mem, f4.mem, u3.mem, u2.mem, u1.mem]
  have v5 : t5.gpr .eax = okW h g P σ := by
    rw [u5.gpr, u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hg.aFr ok sAcc (by decide), hx.1.2.2.1, ha, okBit]
    exact maskOf_congr (and_congr_right fun _ => hae)
  have fr : Frame [slotR P.lay sOk] s.mem t6.mem := by rw [m6.mem, m5, v5]; exact slot_frame _ _ _ _
  refine ⟨c6, ⟨hx.1.keep h fr fun r hr => ?_, slot_keep fr (fun r hr => ?_) hp,
    by rw [m6.mem, m5, v5, Mem.readW_writeW_self32]⟩, sbytes_keep fr (fun r hr => ?_) (by oomega) hb⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

/-- After the output: `out` holds the message, or zeros. -/
abbrev O3 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧
    ∀ i < P.K, s.mem (byteAt P.out i) = if okP h g P σ then Bp h g P σ (i + aV h g P σ) else 0

theorem out_vp (P : EP) : VP (O1 h g P) (.seq (.block outSet) (countLoop outBody)) (O3 h g P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hK' := hi₀.k64
  let X : State → Mem → Prop := fun σ m => Ko h g P σ m ∧
    ∀ j < 2048, m (sa P.scr (oBuf + j)) = Bp h g P σ (j + aV h g P σ)
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ X σ s.mem ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oBuf ∧
      s.gpr .edi = P.out ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .edx = okW h g P σ)
    (VP.taint [.esp, .ebp] outSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hb⟩ => ?_) ?_
  · simp only [outSet, atS, addi, ld, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine c2.wp_arg hg (dec_arg (j := 0) (by decide)) (by decide) (by decide) fun t3 c3 u3 =>
      c3.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t4 c4 u4 =>
      c4.wp_slot hg (d := sOk) (by decide) (by decide) (by decide) fun t5 c5 u5 => WP.block_nil ?_
    have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨c5, m5 ▸ ⟨hk, hb⟩, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
    · rw [u5.other _ (by decide), u4.gpr]; rfl
    · rw [u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem, hk.2.2]
  have hf := ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega_using [])] at hf
  have wb : WBuf P.lay P.out P.K := ⟨hf, by omega_using [hK], ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩
  have sO : ∀ {o n : Nat}, o + n ≤ oRsa → (sR P.scr o n).Disjoint P.OUT := by
    intro o n hon
    have hs := hi₀.slK
    unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
    have d : P.OUT.Disjoint P.SCR := by
      have := ok.wrw
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at this
      exact this.1.2
    have hf' := ok.fits P.SCR (by simp)
    simp only [BitVec.toNat_setWidth] at hf'
    exact (d.sub_right (Offset.sub_base _ (by unfold oRsa at hon; omega_using [hon, hs]))).symm
  have ko : ∀ σ m m', X σ m → Frame [⟨P.out.setWidth 64, P.K⟩] m m' → X σ m' := fun σ m m' ⟨hk, hb⟩ hf' =>
    ⟨hk.keep h g hf' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨out_slot hk.1.1 (by decide), out_slot hk.1.1 (by decide), out_slot hk.1.1 (by decide)⟩,
     fun j hj => by
      rw [← hb j hj]
      exact hf' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sO (o := oBuf + j) (n := 1) (by oomega) _ (Region.contains_self _ _)⟩
  refine (outLoop_vp wb (hg.rbuf (o := oBuf) (n := P.K) (by oomega) (by omega_using [hK'])) (by omega_using [hK']) (X := X) ko
    (f := fun σ i => Bp h g P σ (i + aV h g P σ))
    (fun σ m hx i hi => by rw [hg.byteAt_scr (by oomega)]; exact hx.2 i (by omega_using [hK, hi])) (w := okW h g P)).mono
    (fun σ s hh => hh) fun σ s ⟨hc, ⟨hk, _⟩, hb⟩ => ⟨hc, hk, fun i hi => by rw [hb i hi, and_maskOf]⟩

end VG.Proof.RsaOaep.X86.Dec

end

end

/-! ### `RsaOaep.X86.Dec.Spec`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on x86: what the decoding returns

As on ARMv7 (`Proof/RsaOaep/Arm/DecSpec.lean`): `decOut_eq`: when
`k ≥ 2 hLen + 2`, decryption returns the message after `T`'s padding if
every check passes (`allOk`), the error otherwise, or the private-key
operation's own error, all in the terms the code computes (`EM`'s bytes `V`,
`EM` unmasked `V5`, `T`, `idx`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

variable (h g : OHash)

theorem take1_map_range (f : Nat → Byte) {n : Nat} (hn : 0 < n) : ((List.range n).map f).take 1 = [f 0] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_using [hn]⟩
  simp [List.range_succ_eq_map]

theorem lhB_length (P : EP) (σ : State) : (lhB h P σ).length = h.H.D := by
  rw [lhB, h.valid.2, h.glen]

/-- `lHash' = lHash`, as lists. -/
theorem lh_iff (P : EP) (σ : State) :
    srcB (V5 h g P σ) (1 + h.H.D) h.H.D = h.G.hash (labB P σ) ↔
      ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0 := by
  constructor
  · intro e i hi
    rw [← srcB_getD (V5 h g P σ) (1 + h.H.D) hi]; exact congrArg (fun l => l.getD i 0) e
  · intro e
    exact Proof.RsaOaep.srcB_eq (lhB_length h P σ) e

/-- `decode`, in the code's terms. -/
theorem decode_eq' (P : EP) (σ : State) (hfit : 2 * h.H.D + 2 ≤ P.K) :
    Spec.RsaOaep.decode h.G g.G (labB P σ) ((List.range P.K).map (V P σ)) =
      if allOk h g P σ then some ((sL (tN h P) (T h g P σ)).drop (idx h g P σ + 1)) else none := by
  have hD := h.D_pos
  have h5 := Proof.RsaOaep.chain_eq (G := g.G) (V := V P σ) (V1 := V P σ) (V3 := V3 h g P σ)
    (V5 := V5 h g P σ) hfit (fun _ _ => rfl) (fun x _ => by rw [Nat.sub_add_eq])
    (fun x _ => by rw [Nat.sub_add_eq])
  rw [Proof.RsaOaep.decode_eq g.valid (labB P σ) hfit h.glen h5,
    show srcB (V5 h g P σ) (1 + 2 * h.H.D) (P.K - (2 * h.H.D + 1)) = sL (tN h P) (T h g P σ) from rfl,
    RsaPss.dropWhile_lz, take1_map_range _ (by omega_using [hfit])]
  have hc : ([V P σ 0] = [0x00] ∧ srcB (V5 h g P σ) (1 + h.H.D) h.H.D = h.G.hash (labB P σ)) ↔ hdOk h g P σ := by
    simp only [lh_iff h g P σ, List.cons.injEq, and_true]
  have hl : RsaPss.lz (sL (tN h P) (T h g P σ)) ≤ tN h P := lzS_le (tN h P) (T h g P σ)
  by_cases hf : lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1
  · have e : (sL (tN h P) (T h g P σ)).drop (lzS (tN h P) (T h g P σ)) =
        0x01 :: (sL (tN h P) (T h g P σ)).drop (idx h g P σ + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [sL_length]; exact hf.1)]
      simp only [sL, List.getElem_map, List.getElem_range, idx, pzS, ite_eq_left hf.1, hf.2]
    rw [e]
    split
    · rename_i m heq
      obtain ⟨-, rfl⟩ := List.cons.inj heq
      by_cases ho : hdOk h g P σ
      · rw [ifp (hc.mpr ho), ifp ⟨ho, hf⟩]
      · rw [ifn (fun h' => ho (hc.mp h')), ifn (fun h' => ho h'.1)]
    · rename_i hne; exact (hne _ rfl).elim
  · rw [ifn (fun h' => hf h'.2)]
    by_cases hlt : lzS (tN h P) (T h g P σ) < tN h P
    · rw [List.drop_eq_getElem_cons (by rw [sL_length]; exact hlt)]
      have hne : (sL (tN h P) (T h g P σ))[lzS (tN h P) (T h g P σ)]'(by rw [sL_length]; exact hlt) ≠ 0x01 := by
        simp only [sL, List.getElem_map, List.getElem_range]; exact fun e => hf ⟨hlt, e⟩
      split
      · rename_i heq; exact absurd (List.cons.inj heq).1 hne
      · rfl
    · rw [List.drop_eq_nil_of_le (by rw [sL_length]; show tN h P ≤ lzS (tN h P) (T h g P σ); omega_using [hlt])]

/-- What decryption returns, when `k ≥ 2 hLen + 2`. -/
theorem decOut_eq (P : EP) (σ : State) (hfit : 2 * h.H.D + 2 ≤ P.K) (hk : OcK P σ) :
    Proof.RsaOaep.decOut h.G g.G (labB P σ) (oc P σ) =
      if rV P σ = 1 then
        (if allOk h g P σ then .ok ((sL (tN h P) (T h g P σ)).drop (idx h g P σ + 1)) else .invalid)
      else if rV P σ = 2 then .fault else .invalid := by
  have hd := decode_eq' h g P σ hfit
  show _ = if rOf (oc P σ) = 1 then _ else if rOf (oc P σ) = 2 then _ else _
  have hV : ∀ i, V P σ i = (emL P.K (oc P σ)).getD i 0 := fun _ => rfl
  cases e : oc P σ with
  | invalid => simp [Proof.RsaOaep.decOut, rOf]
  | fault => simp [Proof.RsaOaep.decOut, rOf]
  | ok y =>
    have hem : (List.range P.K).map (V P σ) = y :=
      Proof.RsaOaep.range_ext (hk y e) fun i _ => by rw [hV, e]; rfl
    rw [hem] at hd
    simp only [Proof.RsaOaep.decOut, hd, rOf]
    rw [ifp trivial]
    by_cases ha : allOk h g P σ
    · rw [ifp ha, ifp ha]
    · rw [ifn ha, ifn ha]

end VG.Proof.RsaOaep.X86.Dec

end

end


/-!
# RSAES-OAEP decryption on x86: `*msg_len` and the result

As on ARMv7 (`Proof/RsaOaep/Arm/DecEnd.lean`): the message's length ANDed
with `ok` to `*msg_len` as a 64-bit word, and the result
`(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)` (`end_vp`): what `decrypt` says
(`Proof.RsaOaep.decrypt_eq`, `decOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi sPos)
open VG.Proof.Mont.X86 (wp_storeS)
open VG.Proof.Mgf1 (ifp ifn)

variable (h g : OHash)

theorem mlV_eq {P : EP} {σ : State} (ht : 0 < tN h P) :
    (BitVec.ofNat 32 P.K - BitVec.ofNat 32 (2 * h.H.D + 2) - BitVec.ofNat 32 (idx h g P σ)) &&& okW h g P σ =
      BitVec.ofNat 32 (mlV h g P σ) := by
  have hl := idx_lt h g (P := P) (σ := σ) ht
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  unfold mlV okW maskOf
  by_cases hc : okP h g P σ
  · rw [ifp hc, ifp hc, BitVec.and_allOnes, Offset.ofNat_sub_ofNat (w := 32) (by omega),
      Offset.ofNat_sub_ofNat (w := 32) (by omega_using [hl, htN])]
  · rw [ifn hc, ifn hc]; exact BitVec.and_zero

theorem okW_one (P : EP) (σ : State) : okW h g P σ &&& 1 = if okP h g P σ then 1 else 0 := by
  unfold okW maskOf
  by_cases hc : okP h g P σ
  · rw [ifp hc, ifp hc]; decide
  · rw [ifn hc, ifn hc]; decide

theorem faultV_r (o : Spec.Rsa.Outcome) : faultV (rOf o) = if rOf o = 2 then 2 else 0 := by
  rw [faultV_rOf]; cases o <;> simp [rOf]

theorem Bp_getD (P : EP) (σ : State) (j : Nat) : Bp h g P σ j = (sL (tN h P) (T h g P σ)).getD j 0 := by
  unfold Bp
  by_cases e : j < tN h P
  · rw [ifp e, sL_getD e]
  · rw [ifn e, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sL_length]; omega_using [e])]; rfl

theorem mlV_lt (P : EP) (σ : State) (hK : P.K ≤ 1024) : mlV h g P σ < 2 ^ 32 := by
  unfold mlV; split <;> omega_arith

/-- `msg_len` in `esi`, the length in `eax`. -/
abbrev O4 (P : EP) (σ s : State) : Prop :=
  O3 h g P σ s ∧ s.gpr .esi = P.ml ∧ s.gpr .eax = BitVec.ofNat 32 (mlV h g P σ)

/-- After `*msg_len`. -/
abbrev O5 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Ko h g P σ s.mem ∧
    (∀ i < P.K, s.mem (byteAt P.out i) = if okP h g P σ then Bp h g P σ (i + aV h g P σ) else 0) ∧
    s.mem.readW (P.ml.setWidth 64) 64 = BitVec.ofNat 64 (mlV h g P σ)

theorem mlHead_vp (P : EP) : VP (O3 h g P) (.block ((mlSet h.H).take 5)) (O4 h g P) := by
  refine VP.taint [.esp] h.certs.mlHead (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp])
    fun σ s ⟨hc, hk, hb⟩ => ?_
  have hi := hk.1.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hD := h.D_le
  have hK := hi.k1024
  have hfit := hk.1.2.1
  simp only [mlSet, ld, Impl.RsaPkcs1Sig.X86.stk, List.take_succ_cons, List.take_zero]
  refine hc.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
    wp_subi fun t2 u2 _ _ => ?_
  have c2 := c1.upd u2 (by decide) (by decide)
  refine wp_subm (B := P.lay.B) (by rw [c2.st.sp]) (by rw [hg.aFr ok sPos (by decide)]; exact c2.rFr hg sPos (by decide))
    fun t3 u3 => ?_
  have c3 := c2.upd u3 (by decide) (by decide)
  refine wp_andm (B := P.lay.B) (by rw [c3.st.sp]) (by rw [hg.aFr ok sOk (by decide)]; exact c3.rFr hg sOk (by decide))
    fun t4 u4 => ?_
  have c4 := c3.upd u4 (by decide) (by decide)
  refine c4.wp_arg hg (dec_arg (j := 2) (by decide)) (by decide) (by decide) fun t5 c5 u5 => WP.block_nil ?_
  have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨c5, m5 ▸ hk, m5 ▸ hb⟩, by rw [u5.gpr]; rfl, ?_⟩
  rw [u5.other _ (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr, u3.mem, u2.mem, u1.mem,
    hg.aFr ok sPos (by decide), hg.aFr ok sOk (by decide), hk.2.1, hk.2.2]
  show BitVec.ofNat 32 P.K - _ - _ &&& _ = _
  exact mlV_eq h g (show 0 < tN h P by show 0 < P.K - (2 * h.H.D + 1); omega_using [hfit])

theorem mlRest_vp (P : EP) : VP (O4 h g P) (.block ((mlSet h.H).drop 5)) (O5 h g P) := by
  refine VP.taint [.esp, .esi] mlRest_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
      · rw [h₁.2.1, h₂.2.1]) fun σ s ⟨⟨hc, hk, hb⟩, si, ax⟩ => ?_
  have hi := hk.1.1
  have fit := ml_fit hi
  have hK := hi.k1024
  have win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (P.ml.setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨P.ML, hc.st.inRw (by simp), Offset.contains_base _ hd (by omega_using [hd])⟩
  simp only [mlSet, mi, List.drop_succ_cons, List.drop_zero]
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 0)
    (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si]; exact addr_eq (by omega_using [])) (win 0 (by decide)) fun t1 m1 => ?_
  refine wp_movi fun t2 u2 => ?_
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 4)
    (by show t2.ea ⟨.esi, 4⟩ = _; rw [ea_at, u2.other _ (by decide), m1.gpr, si]; exact addr_eq (by omega_using [fit]))
    (by rw [u2.wr, m1.wr]; exact win 4 (by decide)) fun t3 m3 => WP.block_nil ?_
  have mm : t3.mem = (s.mem.writeW (P.ml.setWidth 64 + BitVec.ofNat 64 0) (BitVec.ofNat 32 (mlV h g P σ))).writeW
      (P.ml.setWidth 64 + BitVec.ofNat 64 4) (BitVec.ofNat 32 0) := by
    rw [m3.mem, u2.gpr, u2.mem, m1.mem, ax]
  have fr : Frame [P.ML] s.mem t3.mem := by
    rw [mm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
    (by rw [m3.rd, u2.rd, m1.rd]) (by rw [m3.wr, u2.wr, m1.wr])
    (by rw [m3.gpr, u2.other _ (by decide), m1.gpr]) (by rw [m3.gpr, u2.other _ (by decide), m1.gpr]),
    hk.keep h g fr fun r hr => ?_, fun i hi' => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ml_slot hi (by decide), ml_slot hi (by decide), ml_slot hi (by decide)⟩
  · rw [← hb i hi']
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact out_ml hi _ (contains_byte (Region.contains_self _ _) (out_wbuf hi).fit hi')
  · rw [mm, BitVec.add_zero]
    exact readW_pair s.mem (P.ml.setWidth 64) (mlV_lt h g P σ hK)

theorem end_vp (P : EP) : VP (O3 h g P) (.seq (.block (mlSet h.H)) (.block decRet)) (Fin h.G g.G P) := by
  have e : (mlSet h.H) = (mlSet h.H).take 5 ++ (mlSet h.H).drop 5 := (List.take_append_drop _ _).symm
  rw [e]
  refine VP.seq ((mlHead_vp h g P).block_append (mlRest_vp h g P)) ?_
  refine VP.taint [.esp, .ebp] decRet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hb, hml⟩ => ?_
  have hi := hk.1.1
  have hg := hi.geo
  have hfit := hk.1.2.1
  have hK := hi.k1024
  refine fault_wp hc hi hk.1.2.2.1 fun t ct m r0 => ?_
  simp only [ld]
  refine ct.wp_slot hg (d := sOk) (by decide) (by decide) (by decide) fun t1 c1 u1 =>
    wp_andi fun t2 u2 => wp_or fun t3 u3 => WP.block_nil ?_
  have c3 := (c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
  refine ⟨⟨hi, c3.st⟩, ?_⟩
  have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem, m]
  have v3 : t3.gpr .eax = faultV (rV P σ) ||| (okW h g P σ &&& 1) := by
    rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide), r0, m, hk.2.2]
  rw [m3, v3, okW_one]
  have ec : (ctB P σ).length = P.nB.length := by rw [ctB_length, nB_length hi]
  have hfv : faultV (rV P σ) = if rV P σ = 2 then 2 else 0 := faultV_r (oc P σ)
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  have ht : 0 < tN h P := by omega_using [hfit, htN]
  have hil := idx_lt h g (P := P) (σ := σ) ht
  rw [Res, Proof.RsaOaep.decrypt_eq ec, decOut_eq h g P σ hfit hk.1.2.2.2, hfv]
  have hz : ¬ okP h g P σ → Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = Spec.RsaOaep.zeros P.K :=
    fun hn => Proof.RsaOaep.out_zero fun i hi' => by rw [hb i hi', ifn hn]
  have hm0 : ¬ okP h g P σ → s.mem.readW (P.ml.setWidth 64) 64 = 0 := fun hn => by
    rw [hml, mlV, ifn hn]; rfl
  by_cases h1 : rV P σ = 1
  · have h2 : ¬ rV P σ = 2 := by rw [h1]; decide
    rw [ifp h1, ifn h2]
    by_cases ha : allOk h g P σ
    · have hc : okP h g P σ := ⟨h1, ha⟩
      rw [ifp ha, ifp hc]
      refine ⟨by decide, ?_, ?_⟩
      · refine Proof.RsaOaep.out_list (T := sL (tN h P) (T h g P σ)) (idx := idx h g P σ)
          (by rw [sL_length]; omega_using [htN]) (by rw [sL_length]; exact hil) fun i hi' => ?_
        rw [hb i hi', ifp hc, Bp_getD]
      · rw [hml, mlV, ifp hc, List.length_drop, sL_length]
        congr 1; show P.K - (2 * h.H.D + 2) - idx h g P σ = P.K - (2 * h.H.D + 1) - (idx h g P σ + 1); omega_using []
    · have hn : ¬ okP h g P σ := fun e => ha e.2
      rw [ifn ha, ifn hn]
      exact ⟨by decide, hz hn, hm0 hn⟩
  · have hn : ¬ okP h g P σ := fun e => h1 e.1
    rw [ifn h1, ifn hn]
    by_cases h2 : rV P σ = 2
    · rw [ifp h2, ifp h2]; exact ⟨by decide, hz hn, hm0 hn⟩
    · rw [ifn h2, ifn h2]; exact ⟨by decide, hz hn, hm0 hn⟩

end VG.Proof.RsaOaep.X86.Dec

end

end


/-!
# RSAES-OAEP decryption on x86: verified

As on ARMv7 (`Proof/RsaOaep/Arm/DecVerified.lean`): the private-key
operation and the check of `k` (`pa_vp`, `call_vp`, `chk_vp`), then zeros if
`k` is too short (`fail_vp`) or the decoding (`main_vp`): `body_vp`. The body
writes `esp` only through the frames of its calls (`body_noSp`); the frames
around it (`wrap_ok`, `wrap_ct`) and the result as the shared contract states
it, for MGF1's hash function the variant `w` whose table the argument 23 is
(`tabFacts_entered`): `vg_rsa_oaep_<H>_mgf1_decrypt`, calling
`vg_rsa_private_checked` over `v`, with MGF1's hash function any of the
tables of `vs`, is verified, given a state that meets the contract
(`Dec/Sat.lean`): `dec_verified`. Every stage keeps the addresses of the
statics (`VP.syms`), which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes seqs countLoop zeroLoop clrArgs)
open VG.Proof.HashTable.X86 (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered
  fnsOf_noSp)

section
variable {F G H : State → State → Prop} {a b c d e r : Prog isa}

theorem relCT_assoc' {Q R : State → State → Prop} (h : RelCT isa Q (.seq a (.seq b c)) R) :
    RelCT isa Q (.seq (.seq a b) c) R := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem vpAssoc (h : VP F (.seq (.seq a b) c) G) : VP F (.seq a (.seq b c)) G :=
  ⟨fun σ s hs => WP.assoc (h.wp σ s hs), RelCT.assoc h.ct⟩

theorem vpAssoc' (h : VP F (.seq a (.seq b c)) G) : VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_assoc' h.ct⟩

/-- A piece of `n` steps, then the rest. -/
theorem VP.cont2 (h : VP F (.seq a b) G) (h₂ : VP G r H) : VP F (.seq a (.seq b r)) H := vpAssoc (h.seq h₂)

theorem VP.cont3 (h : VP F (.seq a (.seq b c)) G) (h₂ : VP G r H) : VP F (.seq a (.seq b (.seq c r))) H :=
  vpAssoc (VP.cont2 (vpAssoc' h) h₂)

theorem VP.cont4 (h : VP F (.seq a (.seq b (.seq c d))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d r)))) H :=
  vpAssoc (VP.cont3 (vpAssoc' h) h₂)

end

variable (h : OHash)

/-- A stage, with what follows it, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- The decoding, when `k ≥ 2 hLen + 2`, with the label's hash function `h`
and MGF1's `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => Sy (C2 h.H.D P) σ s ∧ isa.eval .b s = some false) (decMain h.H f) (Sy (Fin h.G g.G P)) := by
  show VP _ (.seq (.block (tabSlot 23)) (.seq (hashLabelT f 17 oLh) (.seq (.block (seedArgs h.H 4))
    (.seq (mgfXor f 24) (.seq (.block (dbArgs h.H 4)) (.seq (mgfXor f 24) (.seq (.block (cmpSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.cmpBody) (.seq (.block accPut) (.seq (.block (scanSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.scanBody) (.seq (.block scanEnd) (.seq (.block (clrArgs oBuf 2048))
    (.seq zeroLoop (.seq (.block (tSet h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq shift (.seq (.block okMask)
    (.seq (.block outSet) (.seq (countLoop outBody) (.seq (.block (mlSet h.H)) (.block decRet))))))))))))))))))))))
    _
  exact VP.cont2 ((labT_vp h P hTL fne).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (VP.cont4 (unmask_vp h g P hT fne) (VP.syms (VP.cont3 (acc_vp h g P) (VP.cont3 (tscan_vp h g P)
      (buf_vp h g P ((shift_vp h g P).seq ((okMask_vp h g P).seq (VP.cont2 (out_vp h g P) (end_vp h g P)))))))))

/-- The digest length of the label's hash function's table to `edx`. -/
theorem len_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ) :
    VP (R2 P) (.block (lenLoad 23)) (fun σ s => R2 P σ s ∧ s.gpr .edx = BitVec.ofNat 32 h.H.D) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨tR, tRo, tC⟩ := tblL_of hi₀
  show VP _ (.block ([Impl.RsaPss.X86.ld .edx (Impl.RsaPss.X86.arg 23)] ++
    [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 24))])) _
  refine VP.block_append (G := fun σ s => R2 P σ s ∧ s.gpr .edx = P.tabL)
    (VP.taint [.esp] lenArg23_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] lenWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp]
  · obtain ⟨hc, hi, he, hr0, hk⟩ := hs
    simp only [Impl.RsaPss.X86.ld]
    refine hc.wp_arg hg (j := 23) (by simp) (by decide) (by decide) fun t1 c1 u1 => WP.block_nil
      ⟨⟨c1, hi, by rw [u1.mem]; exact he, by rw [u1.other _ (by decide)]; exact hr0, hk⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨hc, hi, he, hr0, hk⟩, hdx⟩ := hs
    have T := hTL σ hi.tabTL
    have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabL 24) 4 := ⟨tR, hc.st.inRo tRo, tC 24 (by decide)⟩
    refine wp_ldm (B := P.tabL) hdx hin fun t2 u2 => WP.block_nil
      ⟨⟨hc.upd u2 (by decide) (by decide), hi, by rw [u2.mem]; exact he, by rw [u2.other _ (by decide)]; exact hr0,
        hk⟩, ?_⟩
    rw [u2.gpr, St_roW hc.st tRo (tC 24 (by decide)), T.d]

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Impl.Pbkdf2.Stream.X86.Hash} (hD : G.D = G'.D) (f : Fns) :
    decTail G f = decTail G' f := by
  simp only [decTail, decMain, decChk, seedArgs, dbArgs, cmpSet, scanSet, tSet, mlSet, hD]

theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (Sy (S P)) (decBody f (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (Sy (Fin h.G g.G P)) := by
  show VP _ (.seq (.block (decStart ++ privArgs)) (.seq (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v))
    (.seq (.block (lenLoad 23)) (byLen (fun d => decTail (ofLen d) f) lens)))) _
  refine VP.cont3 (VP.syms ((pa_vp P).seq ((call_vp P v).seq (len_vp h P hTL)))) (byLen_vp (D := h.H.D)
    (by have := h.D_le; omega_using [this]) (fun _ _ hs => hs.1.2)
    (fun σ s t ⟨⟨⟨hc, hi, he, hr0, hk⟩, dx⟩, sy⟩ fu sy' =>
      ⟨⟨⟨hc.fupd fu, hi, by rw [fu.mem]; exact he, by rw [fu.gpr]; exact hr0, hk⟩, by rw [fu.gpr]; exact dx⟩,
        sy'.trans sy⟩) ?_ h.lens cmpLens_taint)
  show VP _ (decTail (ofLen h.H.D) f) _
  rw [decTail_D (G := ofLen h.H.D) (G' := h.H) rfl f]
  show VP _ (.seq (.block (decChk h.H)) (.ite .b decFail (decMain h.H f))) _
  exact VP.seq ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨r2, _⟩, sy⟩ => ⟨r2, sy⟩) fun _ _ x => x) (VP.ite
    (fun σ s hs => ⟨decide (P.K < 2 * h.H.D + 2), by simp only [eval, hs.1.2.2.2.2.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (main_vp h P g hT hTL fne))

/-! ## The stack -/

theorem tail_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (c : OCerts G) {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2)
    (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2) : NoSp (decTail G f) := by
  obtain ⟨-, p2, -, p4, -, -, -, p8, p9, p10, p11, p12⟩ := c.parts
  have hm := mgfX_noSp hi hu hf (j := 24) (NoSp.of_all (by decide +kernel))
  have hl := hashLabelT_noSp hi hu hf (j := 17) (o := oLh) (NoSp.of_all (by decide +kernel))
    (NoSp.of_all (by decide +kernel))
  simp only [decTail, decMain, decFail, shift, passOne, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply RsaPss.X86.noSp_ite | with_reducible apply noSp_loop
    | exact hm | exact hl | exact p2 | exact p4 | exact p8 | exact p9 | exact p10 | exact p11 | exact p12
    | exact NoSp.of_all (by decide +kernel))

theorem body_noSp {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2)
    (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    NoSp (decBody f (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) := by
  have hc := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  have hb := byLen_noSp (b := fun d => decTail (ofLen d) f) (ds := lens) fun d hd => tail_noSp _ (lens_certs hd) hi hu hf
  simp only [decBody, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_call
    | exact hc | exact hb
    | exact NoSp.of_all (by decide +kernel))

/-! ## The entry -/

variable (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked` over `v`, with both hash
functions any of the tables of `vs`. -/
abbrev decCode (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : Prog isa :=
  decrypt (fnsOf vs) (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev dspec : Contract isa := spec (tables vs)

variable {vs}

/-- The public parameters for MGF1's table of `w` and the label's hash
function's of `w₁`, with their functions where `s` has them. -/
abbrev epw (s : State) (w w₁ : TVar) : EP :=
  ep s (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (arg s 24) (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN))
    (s.syms w₁.g.H.initN) (s.syms w₁.g.H.updN) (s.syms w₁.g.H.finN)
    (TabFacts w₁.g.H (fnsOf vs) (arg s 23) (s.syms w₁.g.H.initN) (s.syms w₁.g.H.updN) (s.syms w₁.g.H.finN))

theorem spec_sp {s : State} (hs : (dspec vs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  dec_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega_using [hsa]⟩

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the tables of `w` at the argument 24 and `w₁` at
23, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (dspec vs).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem ((arg s 24).setWidth 64) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S (ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s 24) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
      (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
      (TabFacts w₁.g.H (fnsOf vs) (arg s 23) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN)
        (s'.syms w₁.g.H.finN))))
      (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tab hs
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  have ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs trivial trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.HashTable.X86.mem_names hw
  have hnL := Proof.HashTable.X86.mem_names hw₁
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 fun _ => True
  have tf := tabFacts_entered (argv := e0.argv) (ro := e0.ro) (rw := e0.rw) (C := 3448) hsp ok (p := arg s 24)
    (by simp [e0, ep]) hfit hc hpw' hw hh
  have tfL := tabFacts_entered (argv := e0.argv) (ro := e0.ro) (rw := e0.rw) (C := 3448) hsp ok (p := arg s 23)
    (by simp [e0, ep]) hfitL hc hpw' hw₁ hhL
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  rw [hsy _ hnL.1, hsy _ hnL.2.1, hsy _ hnL.2.2] at tfL
  have hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs tf tfL
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) {s : State} (hs : (dspec vs).pre s) :
    WP isa (decCode vs v) s fun t => abiPreserved s t ∧ (dspec vs).post s t := by
  obtain ⟨⟨T₁, hT₁, hhL⟩, ⟨T, hT, hh⟩, -, hfitL, hfit⟩ := spec_tab hs
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have hidxL := (held_tableOf hfitL hhL).2.1
  have he := entered_state hc hs hw hw₁ hh hhL (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  have hb := (body_vp w₁.g (epw (vs := vs) s w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) v).wp _ _ he
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp ni nu nf v) hsp hfit4
    (W := (epw (vs := vs) s w w₁).lay.W)
    (Q := fun r m => Res w₁.g.G w.g.G (epw (vs := vs) s w w₁) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (epw (vs := vs) s w w₁).argv) (ro := (epw (vs := vs) s w w₁).ro)
        (rw := (epw (vs := vs) s w w₁).rw) (C := 3448) hsp,
      ret_eq (argv := (epw (vs := vs) s w w₁).argv) (ro := (epw (vs := vs) s w w₁).ro)
        (rw := (epw (vs := vs) s w w₁).rw) (C := 3448) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw (vs := vs) s w w₁).ro) => entered_ro hsp ok hR
    sig_post [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes]
    intro H G hH hG
    rw [hashAt_tableOf hfitL hidxL, Option.some.injEq] at hH
    rw [hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    have hP : pB (epw (vs := vs) s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat :=
      ro (R := (epw (vs := vs) s w w₁).PP) (by simp)
    have hQ : qB (epw (vs := vs) s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat :=
      ro (R := (epw (vs := vs) s w w₁).QQ) (by simp)
    have hDP : dpB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 11).setWidth 64)
        (arg s 8).toNat := ro (R := (epw (vs := vs) s w w₁).DP) (by simp)
    have hDQ : dqB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 13).setWidth 64)
        (arg s 10).toNat := ro (R := (epw (vs := vs) s w w₁).DQ) (by simp)
    have hQI : qiB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 15).setWidth 64)
        (arg s 8).toNat := ro (R := (epw (vs := vs) s w w₁).QI) (by simp)
    have hL : labB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 17).setWidth 64)
        (arg s 18).toNat := ro (R := (epw (vs := vs) s w w₁).LAB) (by simp)
    have hC : ctB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 19).setWidth 64)
        (arg s 4).toNat := ro (R := (epw (vs := vs) s w w₁).CT) (by simp)
    rw [hP, hQ, hDP, hDQ, hQI, hL, hC] at res
    rw [BitVec.setWidth_append_eq_right]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    ConstantTime isa (dspec vs).pre (dspec vs).pub (decCode vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23, a24⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  have hep : epw (vs := vs) s₁ w w₁ = ep s₂ (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s₂ 24) (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN))
      (s₁.syms w₁.g.H.initN) (s₁.syms w₁.g.H.updN) (s₁.syms w₁.g.H.finN)
      (TabFacts w₁.g.H (fnsOf vs) (arg s₂ 23) (s₁.syms w₁.g.H.initN) (s₁.syms w₁.g.H.updN)
        (s₁.syms w₁.g.H.finN)) := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.bytesAt_len, a4])
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a17, a18, a19, a21, a22, a23, a24]
    rw [a3, a4] at hn
    rw [a5, a6] at he
    rw [hn, he]
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  refine (wrap_ct (F := frameBytes) (body_noSp ni nu nf v) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w₁.g (epw (vs := vs) s₁ w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy'⟩

theorem code_noSp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : NoSp (decCode vs v) :=
  have n := fnsOf_noSp vs
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp n.1 n.2.1 n.2.2 v)) restore_noSp)

theorem code_sp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : (decCode vs v).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp v)

/-- `vg_rsa_oaep_decrypt`, calling `vg_rsa_private_checked` over `v`, with
both hash functions any of the tables of `vs`, meets the shared contract
(satisfiable, `Dec/Sat.lean`). -/
theorem dec_verified (hc : Coh vs) (hsat : ∃ s, (dspec vs).pre s) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (decCode vs v) (dspec vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc v, hsat⟩

end VG.Proof.RsaOaep.X86.Dec
