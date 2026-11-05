module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCTBody
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptImplies
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCTBody
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptImplies
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: constant time, and verified

The front loads the working space's and the context's addresses from the
stack and runs without a branch; p's load and check are as
`vg_ffdh_generate_key`'s, from `Base` alone (r9 holds `p_len`, not g's
address, here); then the body (`body_rel`) or the status 0, and the
registers' restore. Runs with the same public arguments and leakage have
the same public data (`cgOf_eq`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gcOf gxOf GD)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_ite' two_mono)

/-! ## The front -/

def T0 (q : CG) (s : State) : Prop := cgContract.pre s ∧ cgOf s = q

/-- After the front: `Base`, and p's load and check to come. -/
def A3 (q : CG) (s : State) : Prop := Base q.c s ∧ WP isa loadP s (A4 q)

/-- The front after the two loads. -/
abbrev frontRest : List Instr :=
  save .r11 ++ ctxHdr ++ ([.store .d .r3 .r23 64, .store .d .r4 .r23 72, .store .d .r5 .r23 80,
    .store .d .r10 .r23 88, .addi .r3 .r7 0, .addi .r4 .r8 0, .addi .r5 .r9 0] : List Instr) ++ setup

theorem front_eq : front = ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr) ++
    (([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr) ++ frontRest) := by
  simp only [front, frontRest, List.append_assoc]

/-- After the working space's address. -/
def T1 (q : CG) (s : State) : Prop :=
  (∃ s₀, T0 q s₀ ∧ s.gpr .r11 = stackArg s₀ 1 ∧ s.mem = s₀.mem ∧ Keep [.r11] s₀ s) ∧
    WP isa (.block (([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr) ++ frontRest)) s (A3 q)

/-- After the context's address. -/
def T2 (q : CG) (s : State) : Prop :=
  (s.gpr .r11 = q.c.S ∧ s.gpr .r12 = q.C) ∧ WP isa (.block frontRest) s (A3 q)

theorem pins_T0 : Pins T0 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_T1 : Pins T1 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_T2 : Pins T2 [.r11, .r12] := by
  rintro q s₁ s₂ ⟨⟨a11, a12⟩, -⟩ ⟨⟨b11, b12⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a12, b12]

theorem stackArg_rd {s : State} (h : cgContract.pre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := by
  refine ⟨cgStack s, List.mem_append_left _ (by rw [h.2.1]; simp), ?_⟩
  rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
    simp only [stackArgAddr, Offset.add_add]; congr 2; omega]
  exact Offset.contains_base _ (by have := h.1; omega) (by omega)

theorem T0_T1 {q : CG} {s : State} (h : T0 q s) :
    WP isa (.block ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr)) s (T1 q) := by
  obtain ⟨hpre, rfl⟩ := h
  have hf := cg_toBI hpre
  rw [front_eq, WP.block_append_iff] at hf
  exact WP.mono (WP.and (loadS1_ok s (stackArg_rd hpre (by decide))) hf)
    fun t ⟨⟨⟨a11, m⟩, k⟩, hw⟩ => ⟨⟨s, ⟨hpre, rfl⟩, a11, m, k⟩, WP.mono hw fun _ h => h⟩

theorem T1_T2 {q : CG} {s : State} (h : T1 q s) :
    WP isa (.block ([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr)) s (T2 q) := by
  obtain ⟨⟨s₀, ⟨hpre, rfl⟩, a11, m, k⟩, hw⟩ := h
  rw [WP.block_append_iff] at hw
  have hrd : InRegions (s.rd ++ s.wr) (stackArgAddr s 3) 8 := by
    rw [k.rd, k.wr, show stackArgAddr s 3 = stackArgAddr s₀ 3 by simp only [stackArgAddr, k.sp]]
    exact stackArg_rd hpre (by decide)
  exact WP.mono (WP.and (loadC_ok s hrd) hw) fun t ⟨⟨⟨a12, _⟩, kt⟩, hw'⟩ =>
    ⟨⟨(kt.gpr .r11 (by decide)).trans a11, a12.trans (show stackArg s 3 = stackArg s₀ 3 by simp only [stackArg, stackArgAddr, m, k.sp])⟩, hw'⟩

/-! ## p's load and check, from `Base` -/

/-- With `loadN`'s arguments. -/
def Y1 (c : CD) (s : State) : Prop := Base c s ∧ s.gpr .r12 = off c.D 0 ∧ s.gpr .r6 = BitVec.ofNat 64 c.k

/-- After `check1`. -/
def Y3 (c : CD) (s : State) : Prop :=
  Base c s ∧ arr s.mem c.S c.w 0 = c.p ∧ s.gpr .r6 = BitVec.ofNat 64 c.k ∧
    s.gpr .r15 = BitVec.ofNat 64 ((c.db.take c.k).getD 0 0).toNat ∧ s.gpr .r18 = 1 ∧
    (s.gpr .r0 = 0 ↔ ((c.db.take c.k).getD (c.k - 1) 0).toNat % 2 = 1)

theorem YA {c : CD} {s : State} (h : Base c s) : WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (Y1 c) := by
  refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off c.D 0 ∧ t.gpr .r6 = BitVec.ofNat 64 c.k ∧
    t.mem = s.mem) (by prun [h.r21, h.r28, BitVec.add_zero]) (by decide)) fun t ⟨⟨a12, a6, m⟩, k⟩ =>
      ⟨h.same k m, a12, a6⟩

theorem YL {c : CD} {s : State} (h : Y1 c s) :
    WP isa Precompute.loadN s fun t => Y1 c t ∧ arr t.mem c.S c.w 0 = c.p := by
  obtain ⟨hb, h12, h6⟩ := h
  have hwd : c.w = (c.k + 7) / 8 := rfl
  have hZ := hb.env.hZ
  have hk := hb.k64
  have hk' := hb.k1024
  have e28 := Domain.slot_eq c.w 28
  refine WP.mono (loadN_ok (dA := slot c.w 0) hb.env.hs hb.env.h10 h12 h6 hb.env.h11 (by omega_arith) (by omega_arith)
    (by omega_arith) (by rw [Domain.slot_eq]; omega_arith) (by rw [Domain.slot_eq] at hZ ⊢; omega_arith)
    (fun i hi => hb.rdD i (by rcases hb.hL with h | h <;> omega_arith))
    (fun i hi => hb.sepD i (by rcases hb.hL with h | h <;> omega_arith))) fun t ⟨hv, out, k⟩ => ?_
  have hm : Body c.S c.w s.mem t.mem := Body.of out (Nat.le_refl _) (by rw [Domain.slot_eq] at hZ ⊢; omega_arith)
  refine ⟨⟨hb.keep k hm, (k.gpr .r12 (by decide)).trans h12, (k.gpr .r6 (by decide)).trans h6⟩, ?_⟩
  rw [arr, hv, ← Proof.Ffdh.take_bytesAt _ _ (show c.k ≤ c.L by rcases hb.hL with h | h <;> omega_arith), hb.bD]

theorem YC1 {c : CD} {s : State} (h : Y1 c s ∧ arr s.mem c.S c.w 0 = c.p) :
    WP isa (.block Precompute.check1) s (Y3 c) := by
  obtain ⟨⟨hb, h12, h6⟩, hp⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := c.D) (nb := c.db.take c.k) h12 h6 hk hl
    (fun i hi => hb.rdD i (by have := hb.kL; omega_arith)) fun i hi => hb.take_byte hi)
    fun t ⟨⟨i0, i15, i18, im⟩, k⟩ => ⟨hb.same k im, by rw [arr, im]; exact hp,
      (k.gpr .r6 (by decide)).trans h6, by rw [i15, getD_of_lt' (by omega_arith)], i18,
      by rw [i0, getD_of_lt' (by omega_arith)]⟩

/-- With `loadN`'s arguments, and p's load and check to come. -/
def P1 (q : CG) (s : State) : Prop := Y1 q.c s ∧ WP isa (.seq Precompute.loadN Precompute.check) s (A4 q)

def P2 (q : CG) (s : State) : Prop := (Y1 q.c s ∧ arr s.mem q.c.S q.c.w 0 = q.c.p) ∧ WP isa Precompute.check s (A4 q)

def P3 (q : CG) (s : State) : Prop := Y3 q.c s ∧ WP isa Precompute.check2 s (A4 q)

theorem pins_A3 : Pins A3 baseRegs := fun _ _ _ h₁ h₂ => h₁.1.pins h₂.1

theorem pins_Y1 {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → Y1 q.c s) :
    Pins Φ (baseRegs ++ ([.r12, .r6] : List Reg)) := by
  intro q s₁ s₂ h₁ h₂ r hr
  have h₁ := h _ _ h₁
  have h₂ := h _ _ h₂
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.pins h₂.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

theorem pins_P3 : Pins P3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := by
  intro q s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1]
    · rw [h₁.1.2.2.2.2.1, h₂.1.2.2.2.2.1]

theorem pins_A4 {Φ : CG → State → Prop} (h : ∀ q s, Φ q s → A4 q s) : Pins Φ [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr
  rw [(h _ _ h₁).1.2, (h _ _ h₂).1.2]

theorem pins_CF : Pins (fun (q : CG) s => CF q.c s) [.r23] := by
  intro q s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr
  exact h₁.trans h₂.symm

/-! ## Constant time -/

theorem cg_rel : RelCT isa (Two T0) Generate.code fun _ _ => True := by
  unfold Generate.code
  rw [front_eq]
  refine RelCT.seq (R := Two A3) (RelCT.block_append (RelCT.seq (R := Two T1)
      (two_post (two_taint _ pins_T0 (by taint_decide)) fun _ _ h => T0_T1 h)
      (RelCT.block_append (RelCT.seq (R := Two T2)
        (two_post (two_taint _ pins_T1 (by taint_decide)) fun _ _ h => T1_T2 h)
        (two_post (two_taint _ pins_T2 (by taint_decide)) fun _ _ h => h.2)))))
    (RelCT.seq (R := Two A4) ?_
      (RelCT.seq (R := Two fun (q : CG) s => CF q.c s) ?_ (two_taint _ pins_CF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (R := Two P1)
      (two_post (two_taint _ pins_A3 (by taint_decide)) fun _ _ h => Derive.wp_split (YA h.1) h.2)
      (RelCT.seq (R := Two P2) (two_post (two_taint _ (pins_Y1 fun _ _ h => h.1) (by taint_decide))
          fun _ _ h => Derive.wp_split (YL h.1) h.2)
        (RelCT.seq (R := Two P3) (two_post (two_taint _ (pins_Y1 fun _ _ h => h.1.1) (by taint_decide))
            fun _ _ h => Derive.wp_split (YC1 h.1) h.2)
          (two_post (two_taint _ pins_P3 (by taint_decide)) fun _ _ h => h.2)))
  · refine two_ite' (fun q : CG => Spec.Rsa.modulusValid q.c.p q.c.k) (fun q s h => by
        rw [eval_zero]; congr 1
        cases hv : Spec.Rsa.modulusValid q.c.p q.c.k
        · exact beq_false_of_ne fun e => by simpa [hv] using h.1.1.mp e
        · exact beq_iff_eq.mpr (h.1.1.mpr hv)) ?_ ?_
    · exact two_mono (fun q s ⟨h, hv⟩ => h.2 (h.1.1.mpr hv)) body_rel
    · exact two_post (two_taint _ (pins_A4 fun _ _ h => h.1) (by taint_decide)) fun _ _ ⟨h, _⟩ =>
        WP.mono (li_ok _ 0 (by decide)) fun t ⟨_, kt⟩ => (kt.gpr .r23 (by decide)).trans h.1.2

/-! ## The public data -/

/-- The attempt's scalar, as the code cuts it. -/
theorem cgScalar_eq {s : State} (h : cgContract.pre s) :
    cgScalar s = cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrl, -, hdv, -⟩ := h
  have hb := genBits_facts hdv
  unfold cgScalar
  rw [Spec.Ffdh.vettedScalarOfOctets, hrl, cgX, scalarC_value (VG.Proof.Bignum.bytesAt_length _ _ _) hb.1 hb.2]

/-- Runs with the same public arguments and leakage have the same public
data. -/
theorem cgOf_eq {s t : State} (hs : cgContract.pre s) (ht : cgContract.pre t) (h3 : s.gpr .r3 = t.gpr .r3)
    (h5 : s.gpr .r5 = t.gpr .r5) (h7 : s.gpr .r7 = t.gpr .r7) (h8 : s.gpr .r8 = t.gpr .r8)
    (h9 : s.gpr .r9 = t.gpr .r9) (h10 : s.gpr .r10 = t.gpr .r10) (a1 : stackArg s 1 = stackArg t 1)
    (a2 : stackArg s 2 = stackArg t 2) (a3 : stackArg s 3 = stackArg t 3) (hl : cgLeak s = cgLeak t) :
    cgOf s = cgOf t := by
  have hsc := cgScalar_eq hs
  have htc := cgScalar_eq ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := hs
  simp only [Spec.Ffdh.domainLenValid] at hL
  simp only [cgLeak] at hl
  obtain ⟨e1, e2⟩ := List.append_inj hl (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h8])
  have ed : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r8).toNat := by
    have := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
    simp only [cgDom] at this
    rw [← h7, ← h8] at this; exact this
  have sl : ∀ o, o + (s.gpr .r9).toNat ≤ (s.gpr .r8).toNat →
      Spec.Rsa.bytesAt s.mem (s.gpr .r7 + BitVec.ofNat 64 o) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r7 + BitVec.ofNat 64 o) (s.gpr .r9).toNat := fun o ho => by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem _ ho, ← VG.Proof.Dsa.bytesAt_slice t.mem _ ho, ed]
  have hgx : gxOf s = gxOf t := by
    have e1 : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat =
        Spec.Rsa.bytesAt t.mem (t.gpr .r7) (t.gpr .r8).toNat := by rw [← h7, ← h8]; exact ed
    have e2 : Spec.Rsa.bytesAt s.mem (off (s.gpr .r7) (s.gpr .r9).toNat) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt t.mem (off (t.gpr .r7) (t.gpr .r9).toNat) (t.gpr .r9).toNat := by
      rw [← h7, ← h9]; exact sl _ (by omega)
    unfold gxOf gcOf
    rw [e1, e2, h3, h5, h7, h8, h9, a1, a2]
  have hp : ∀ m : Mem, Spec.Rsa.os2ip ((Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r8).toNat).take (s.gpr .r9).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r9).toNat) := fun m => by
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega)]
  have hbT : ∀ P, Derive.bnd t.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat P =
      Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat P := fun P =>
    Derive.bnd_congr fun hq => (sl _ (by omega)).symm
  have hpT : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r9).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by rw [← hp, ← hp, ed]
  have hA : cgA t = cgA s := by
    show Spec.Ffdh.domainOf (t.gpr .r9).toNat (Spec.Rsa.bytesAt t.mem (t.gpr .r7) (t.gpr .r8).toNat) =
      Spec.Ffdh.domainOf (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
    rw [← h7, ← h8, ← h9, ← ed]
  have e3 := (Derive.keyStatus_two _ _).symm.trans
    ((iff_of_eq (congrArg (· = 2) (List.cons.inj e2).1)).trans (Derive.keyStatus_two _ _))
  rw [hsc, htc, hA] at e3
  simp only [cgA, cgDom, ← h9, ← h10] at e3
  rw [Derive.privateValid_dom (by omega) (by omega), Derive.privateValid_dom (by omega) (by omega)] at e3
  have hv := Derive.bool_eq_of_false_iff e3
  have hgp : (gcOf t).p = (gcOf s).p := congrArg (fun x : XD => x.c.p) hgx.symm
  have ep : (gcOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := hp s.mem
  simp only [cgOf, CG.mk.injEq, GD.mk.injEq, Derive.DD.mk.injEq]
  refine ⟨⟨⟨hgx, ?_, ?_⟩, h10⟩, a3, by rw [hA]⟩
  · rw [← h7, ← h8, ← h9, hgp, hbT]
  · rw [hA, ← h7, ← h8, ← h9, ← h10, hgp, hbT, ep]
    simp only [cgA, cgDom] at hv ⊢
    exact hv

theorem cg_ct : ConstantTime isa cgContract.pre cgContract.pub Generate.code :=
  RelCT.constantTime (cg_rel.mono (fun s _ ⟨hs, ht, hsp, hl, h3, _, h5, _, h7, h8, h9, h10, _, a1, a2, a3, _⟩ =>
    ⟨cgOf s, ⟨hs, rfl⟩, ⟨ht, (cgOf_eq hs ht h3 h5 h7 h8 h9 h10 a1 a2 a3 hl).symm⟩, hsp⟩) fun _ _ h => h)

/-- `vg_ffdh_generate_key_cached`. -/
theorem cg_verified : Verified target Generate.code (Spec.Ffdh.cachedGenerateKeyContract abi) :=
  Verified.of_correct cg_correct cg_ct cg_implies

end VG.Proof.Ffdh.PPC64LE.Cached
