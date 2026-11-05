module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcMain
public import VerifiedGarbage.Impl.Ffdh.VettedGroups
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # FFDH's context on PPC64LE: with p valid

`main_ok`: from p checked and the recognized width in the header, the width
and the metadata, `R² mod p`, the prefix rows and the table: the context's
words are `generationValues`. -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Precompute
open VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)
open VG.Spec.RsaKeyGen (bitLength)

/-! ## The width's facts -/

theorem recognized_le {a : Spec.Ffdh.Parameters} {b : Nat} (h : Spec.Ffdh.vettedExponentBits a = some b) :
    b ≤ 400 := by
  unfold Spec.Ffdh.vettedExponentBits at h
  repeat' split at h
  all_goals cases h
  all_goals decide

/-- The width the code computes is the spec's. -/
theorem width_eq {k : Nat} {dom : List Byte} (hk : 0 < k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hn : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (dom.take k)) :
    widthOf (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom)
        (bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))) =
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) := by
  rw [VG.Proof.Ffdh.VettedGroupFacts.recognize_spec hk hd hn]
  unfold Spec.Ffdh.generationScalarBits
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simp [widthOf]
  | some b =>
    have := recognized_nonzero he
    simp only [Option.getD_some, widthOf]
    by_cases hb : b < bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))
    · rw [ite_eq_left ⟨this, hb⟩]; exact (Nat.min_eq_left (by omega)).symm
    · rw [ite_eq_right (fun h => hb h.2)]; exact (Nat.min_eq_right (by omega)).symm

theorem recognize_lt {k : Nat} {dom : List Byte} (hk : 0 < k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hn : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (dom.take k)) :
    VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom ≤ 400 := by
  rw [VG.Proof.Ffdh.VettedGroupFacts.recognize_spec hk hd hn]
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simp
  | some b => exact recognized_le he

/-- The bound's first significant octet is not zero. -/
theorem lead_ne {k : Nat} {dom : List Byte} (hk : 1 ≤ k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hv : Spec.Ffdh.domainValid k dom = true) :
    leadOct (VG.Proof.Ffdh.KeyScalar.bnd k dom) ≠ 0 := by
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  have hpf := VG.Proof.Ffdh.PPC64LE.Domain.modulus_facts hv'.1
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length hd
  have hne : VG.Proof.Ffdh.KeyScalar.bnd k dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  have hld := VG.Proof.Ffdh.lead_lt hne
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := k) (dom := dom) hk hd (fun _ => ⟨hpf.2, by
    have : (Spec.Ffdh.domainOf k dom).p = Spec.Rsa.os2ip (dom.take k) := rfl; omega⟩)
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  unfold leadOct
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hld, Option.getD_some]
  intro hb0
  by_cases hlast : VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k dom) + 1 <
      (VG.Proof.Ffdh.KeyScalar.bnd k dom).length
  · exact VG.Proof.Ffdh.lead_nonzero hne hlast (BitVec.eq_of_toNat_eq (by simpa using hb0))
  · rw [hb0] at hbits
    have : bitLength 0 = 0 := rfl
    rw [this] at hbits
    have hpos := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega)).2
    rw [hbits] at hpos
    rw [hbl] at hlast hld
    have : k - VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k dom) - 1 = 0 := by omega
    rw [this] at hpos
    omega

/-- `storePrefix`: p and `R² mod p` to the context's rows 0 and 1. -/
theorem storePrefix_ok {B C : Addr} {Z w P : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) :
    WP isa storePrefix s fun t =>
      (rowv t.mem C w 0 = arr s.mem B w 0 ∧ rowv t.mem C w 1 = arr s.mem B w 1 ∧
        Outside C (rowOff w 0) (16 * w) s.mem t.mem ∧ Outside B Z (2 ^ 64) s.mem t.mem ∧ TS B C Z w P M t) ∧
      Keep ([.r3] ++ rowRegs) s t := by
  have hCn := h.hc.nowrap
  unfold storePrefix
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 0 ∧ u.mem = s.mem)
    (by prun) (by decide)) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have ts1 := h.keep k1 (by decide) fun x _ => by rw [m1]
  refine WP.seq (WP.mono (ts1.store (j := 0) (a := 0) (by decide) a3 (by decide)) fun t₂ ⟨⟨r0, o2, b2, ts2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 1 ∧ u.mem = t₂.mem)
    (by prun) (by decide)) fun t₃ ⟨⟨a3', m3⟩, k3⟩ => ?_)
  have ts3 := ts2.keep k3 (by decide) fun x _ => by rw [m3]
  refine WP.mono (ts3.store (j := 1) (a := 1) (by decide) a3' (by decide)) fun t ⟨⟨r1, o4, b4, ts4⟩, k4⟩ => ?_
  have hZ := h.env.hZ
  have hnw := h.fit
  have a1 : slot w 1 + 8 * (w + 2) ≤ Z := Env.arr h.env (by decide)
  have fit0 : rowOff w 0 + 4 * (2 * w) ≤ rowOff w 1 := by unfold rowOff; omega
  refine ⟨⟨?_, ?_, ?_, fun y hy => by rw [b4 y hy, m3, b2 y hy, m1], ts4⟩, (((k1.trans k2).trans k3).trans k4).mono (by decide)⟩
  · rw [rowv, Outside.val32 o4 (Or.inl fit0) (by unfold rowOff ctxWords at *; omega), m3]
    exact r0.trans (by rw [arr, arr, m1])
  · exact r1.trans (by
      rw [arr, arr, m3, b2.val32 (Or.inl (by omega)) (by omega), m1])
  · intro y hy
    rw [o4 y (by unfold rowOff at *; omega), m3, o2 y (by unfold rowOff at *; omega), m1]

/-! ## With p valid -/

/-- At `main`: the working space, the domain, the context's address in the
header, writable and apart, the recognized width in the header, p in array 0. -/
structure MP (S D C : Addr) (Z k L : Nat) (s : State) : Prop where
  env : Env s S Z ((k + 7) / 8)
  h23 : s.gpr .r23 = S
  h21 : s.gpr .r21 = D
  h27 : s.gpr .r27 = BitVec.ofNat 64 L
  h28 : s.gpr .r28 = BitVec.ofNat 64 k
  hk : 64 ≤ k
  hk' : k ≤ 1024
  hL : L = 2 * k ∨ L = 3 * k
  rdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1
  sepD : ∀ i < L, ∀ x, ofs S x < Z → off D i ≠ x
  sepDC : ∀ i < L, ∀ x, ofs C x < 8 * ctxWords ((k + 7) / 8) → off D i ≠ x
  hc : Scr s C (8 * ctxWords ((k + 7) / 8))
  sepCB : ∀ x, ofs C x < 8 * ctxWords ((k + 7) / 8) → Z ≤ ofs S x
  sepBC : ∀ x, ofs S x < Z → 8 * ctxWords ((k + 7) / 8) ≤ ofs C x
  hC : s.mem.readW (off S hCtx) 64 = C
  hcap : s.mem.readW (off S hCap) 64 =
    BitVec.ofNat 64 (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k
      (Spec.Rsa.bytesAt s.mem D L))
  hP : arr s.mem S ((k + 7) / 8) 0 = (Spec.Ffdh.domainOf k (Spec.Rsa.bytesAt s.mem D L)).p
  hdv : Spec.Ffdh.domainValid k (Spec.Rsa.bytesAt s.mem D L) = true

/-- The registers `main` writes. -/
def mainRegs : List Reg :=
  bbRegs ++ [.r8, .r9, .r16] ++ [.r0, .r17, .r18, .r19, .r24, .r30] ++
    [.r0, .r3, .r4, .r5, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r20] ++ ([.r3] ++ rowRegs) ++ tabRegs ++ [.r3]

theorem main_ok {S D C : Addr} {Z k L : Nat} {s : State} (h : MP S D C Z k L s) :
    WP isa main s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 1 ∧
        Spec.Rsa.wordsAt t.mem C (3 + 34 * ((k + 7) / 8)) = VG.Proof.Ffdh.generationValues k (Spec.Rsa.bytesAt s.mem D L) ∧
        (∀ x, ofs S x < slot ((k + 7) / 8) 1 → t.mem x = s.mem x)) ∧ Keep mainRegs s t := by
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hw := h.env.hw; have hw' := h.env.hw'
  have hk := h.hk; have hk' := h.hk'
  have hCn := h.hc.nowrap
  have hdl : (Spec.Rsa.bytesAt s.mem D L).length = L := by simp [Spec.Rsa.bytesAt]
  have hd : (Spec.Rsa.bytesAt s.mem D L).length = 2 * k ∨ (Spec.Rsa.bytesAt s.mem D L).length = 3 * k := by
    rw [hdl]; exact h.hL
  generalize hdom : Spec.Rsa.bytesAt s.mem D L = dom at hd hdl ⊢
  have hcap := h.hcap; rw [hdom] at hcap
  have hP := h.hP; rw [hdom] at hP
  have hdv := h.hdv; rw [hdom] at hdv
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hdv
  have hpf := VG.Proof.Ffdh.PPC64LE.Domain.modulus_facts hv'.1
  generalize hpd : (Spec.Ffdh.domainOf k dom).p = p at hP hpf hv'
  have hpe : Spec.Rsa.os2ip (dom.take k) = p := hpd
  have hmv := hv'.1
  have hnorm : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (dom.take k) := by
    rw [hpe]
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmv
    refine Nat.le_trans ?_ hmv.2
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpw : p < 2 ^ (64 * ((k + 7) / 8)) := by
    have := VG.Proof.Bignum.os2ip_lt (dom.take k)
    rw [hpe, List.length_take] at this
    refine Nat.lt_of_lt_of_le this ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  -- The bound's bits.
  have hbb := VG.Proof.Ffdh.KeyScalar.bound_bits (k := k) (dom := dom) (by omega) hd (fun _ => ⟨by rw [hpe]; exact hpf.2,
    by rw [hpe]; omega⟩)
  generalize hbl : bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) = bl at hbb
  have hbl8 : bl ≤ 8192 := by
    have hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) < 2 ^ 8192 := by
      unfold Spec.Ffdh.scalarBound
      have hp8 : p < 2 ^ 8192 := by
        simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmv; omega
      cases hq : (Spec.Ffdh.domainOf k dom).q with
      | none => simp only [Option.getD_none]; rw [hpd]; omega
      | some q => have := (hv'.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega
    rw [← hbl]; exact bitLength_le_of_lt hle
  have hlead := lead_ne (by omega) hd hdv
  unfold main
  simp only [seqs]
  refine WP.seq (WP.mono (boundBits_ok h.h21 h.h27 h.h28 h.hL (by omega) (by omega) h.rdD (by rw [hdom]; exact hlead))
    fun t₁ ⟨⟨a16, m1⟩, k1⟩ => ?_)
  rw [hdom] at a16
  have e16 : t₁.gpr .r16 = BitVec.ofNat 64 bl := by
    rw [a16, hbb]; congr 2
    unfold leadOct; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
  -- The width.
  have hcap' := recognize_lt (by omega) hd hnorm
  refine WP.seq (WP.mono (width_ok (cap := VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom)
    (h.env.hs.congr k1.wr) (Nat.le_trans (by simp only [slot]; omega) hZ)
    ((k1.gpr .r23 (by decide)).trans h.h23) (by rw [m1]; exact hcap) e16 (by omega) (by omega))
    fun t₂ ⟨⟨a16', m2⟩, k2⟩ => ?_)
  rw [← hbl, width_eq (by omega) hd hnorm] at a16'
  generalize hbits : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) = bits at a16'
  have hgb := genBits_facts (k := k) (dom := dom) hdv
  rw [hbits] at hgb
  have hb8 : bits ≤ 8192 := by omega
  have k12 := k1.trans k2
  have m12 : t₂.mem = s.mem := by rw [m2, m1]
  -- The metadata.
  have hc24 : Scr t₂ C 24 := ⟨let ⟨B₀, o, L', hm, hb, hL, hL'⟩ := (h.hc.congr k12.wr).wr
    ⟨B₀, o, L', hm, hb, by unfold ctxWords at hL; omega, hL'⟩, by unfold ctxWords at hCn; omega⟩
  refine WP.seq (WP.mono (metadata_ok (h.env.hs.congr k12.wr) (by simp only [slot] at hZ; omega)
    ((k12.gpr .r23 (by decide)).trans h.h23) (by rw [m12]; exact h.hC) hc24 a16' hgb.1 hb8)
    fun t₃ ⟨⟨a30, a24, w0, w8, w16, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have bS3 : ∀ x, ofs S x < Z → t₃.mem x = s.mem x := fun x hx => by
    rw [o3 x (Or.inr (by have := h.sepBC x hx; unfold ctxWords at this; omega)), m12]
  have hp3 : arr t₃.mem S ((k + 7) / 8) 0 = p := by
    rw [arr, val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => bS3 _ (by
      rw [ofs_off S (by have := Env.arr h.env (j := 0) (by decide); simp only [slot] at *; omega)]
      have := Env.arr h.env (j := 0) (by decide); simp only [slot] at *; omega)), ← arr]
    exact hP
  have e3 : Env t₃ S Z ((k + 7) / 8) := h.env.keep k13 (by decide)
  have hlow3 : (word t₃.mem S (slot ((k + 7) / 8) 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 t₃.mem S (slot ((k + 7) / 8) 0)
    have h2 : val32 t₃.mem S (slot ((k + 7) / 8) 0) (2 * ((k + 7) / 8) - 1 + 1) =
        w32 t₃.mem S (slot ((k + 7) / 8) 0) + 2 ^ 32 * val32 t₃.mem S (slot ((k + 7) / 8) 0 + 4) (2 * ((k + 7) / 8) - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * ((k + 7) / 8))] at h2
    have := hpf.2
    have hp' := hp3
    rw [arr] at hp'
    omega
  -- `R² mod p`.
  refine WP.seq (WP.mono (montgomery_ok e3 hp3 hpf.1 hlow3) fun t₄ ⟨⟨r1, r12a, r12b, o4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  have hp4 : arr t₄.mem S ((k + 7) / 8) 0 = p := by
    rw [arr, Outside.val32 o4 (Or.inl (by simp only [slot, hdrBytes]; omega)) (by simp only [slot, hdrBytes] at hZ ⊢; omega),
      ← arr]; exact hp3
  have ts4 : TS S C Z ((k + 7) / 8) p t₄.mem t₄ := ⟨h.env.keep k14 (by decide), (k4.gpr .r30 (by decide)).trans a30,
    h.hc.congr k14.wr, h.sepCB, h.sepBC, r12a, r12b, hp4, hpf.2, by omega, fun _ _ => rfl⟩
  -- The prefix.
  refine WP.seq (WP.mono (storePrefix_ok ts4) fun t₅ ⟨⟨row0, row1, o5, b5, ts5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have ts5' : TS S C Z ((k + 7) / 8) p t₅.mem t₅ := { ts5 with low := fun _ _ => rfl }
  have tt5 : TT S C Z ((k + 7) / 8) p (Spec.Rsa.FixedBaseComb.rows bits) t₅ t₅ :=
    ⟨ts5', by rw [k5.gpr .r24 (by decide), k4.gpr .r24 (by decide), a24], (k15.gpr .r23 (by decide)).trans h.h23,
      CtxKeep.refl _ _ _, Keep.refl _ _⟩
  -- g's octets are as in `s`.
  have ws5 : WsOnly S C Z (8 * ctxWords ((k + 7) / 8)) s.mem t₅.mem :=
    (((WsOnly.of_eq m12).trans (WsOnly.of_ctx o3 (by unfold ctxWords; omega))).trans
      (WsOnly.of_ws o4 (by simp only [slot, hdrBytes] at hZ ⊢; omega))).trans
      (WsOnly.of_ctx o5 (by unfold rowOff ctxWords; omega))
  have hgL : 2 * k ≤ L := by rcases h.hL with e | e <;> omega
  have hG : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₅.mem (off D k) k) = (Spec.Ffdh.domainOf k dom).g := by
    rw [ws5.bytes (fun i hi x hx => by rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact h.sepD _ (by omega) x hx)
      (fun i hi x hx => by rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact h.sepDC _ (by omega) x hx), ← hdom,
      VG.Proof.Ffdh.domainOf_g _ _ hgL]
  have h1 : arr t₅.mem S ((k + 7) / 8) 1 = 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % p := by
    rw [arr, b5.val32 (Or.inl (by have := Env.arr h.env (j := 1) (by decide); omega)) (by
      have := Env.arr h.env (j := 1) (by decide); omega), ← arr, r1, ← Nat.pow_add]
    congr 2; omega
  have hrows := VG.Proof.Rsa.FixedBaseComb.rows_small (show bits ≤ 8192 from hb8)
  refine WP.seq (WP.mono (table_ok (bits := bits) tt5 (by
      simp only [Spec.Rsa.FixedBaseComb.rows, Spec.Rsa.FixedBaseComb.teeth]; omega) (by omega) h1
      ((k15.gpr .r21 (by decide)).trans h.h21) ((k15.gpr .r28 (by decide)).trans h.h28) (by omega) (by omega)
      (fun i hi => by rw [k15.rd, k15.wr, VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact h.rdD _ (by omega))
      (fun i hi x hx => by rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact h.sepD _ (by omega) x hx)
      (fun i hi x hx => by rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact h.sepDC _ (by omega) x hx) hG
      (by have := hv'.2.1.2; omega)) fun t₆ ⟨tt6, e6⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 1 ∧ u.mem = t₆.mem)
    (by prun) (by decide)) fun t ⟨⟨u3, mu⟩, ku⟩ => ?_
  -- The context's words.
  have c56 : ∀ y, ofs C y < rowOff ((k + 7) / 8) 2 → t.mem y = t₅.mem y := fun y hy => by
    rw [mu]; exact tt6.keep y hy
  have c35 : ∀ y, ofs C y < 24 → t₅.mem y = t₃.mem y := fun y hy => by
    rw [o5 y (Or.inl (by unfold rowOff; omega))]
    exact o4 y (Or.inr (by have := h.sepCB y (by unfold ctxWords; omega); simp only [slot] at hZ ⊢; omega))
  have cw : ∀ d, d + 8 ≤ 24 → t.mem.readW (C + BitVec.ofNat 64 d) 64 = word t₃.mem C d := fun d hd =>
    Mem.readW_congr fun i hi => by
      have hy : ofs C (off C d + BitVec.ofNat 64 i) < 24 := by rw [ofs_off C (by omega)]; omega
      exact (c56 _ (Nat.lt_of_lt_of_le hy (by unfold rowOff; omega))).trans (c35 _ hy)
  have rw0 : rowv t.mem C ((k + 7) / 8) 0 = p := by
    rw [rowv, val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => c56 _ (by
      rw [ofs_off C (by unfold rowOff ctxWords at *; omega)]; unfold rowOff at *; omega)), ← rowv, row0, arr]
    rw [← arr]; exact hp4
  have rw1 : rowv t.mem C ((k + 7) / 8) 1 = 2 ^ (128 * ((k + 7) / 8)) % p := by
    rw [rowv, val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => c56 _ (by
      rw [ofs_off C (by unfold rowOff ctxWords at *; omega)]; unfold rowOff at *; omega)), ← rowv, row1]
    exact r1
  refine ⟨⟨u3, ctx_words (k := k) (dom := dom) (by omega) (by rw [cw 0 (by decide), hbits]; exact w0)
      (by rw [cw 8 (by decide), hbits]; exact w8) (by rw [cw 16 (by decide), hbits]; exact w16)
      (by rw [hpd]; exact rw0) (by rw [hpd]; exact rw1)
      (by rw [hbits, hpd]; intro a ha; show ent t.mem C _ a = _; rw [ent, mu, ← ent]; exact e6 a ha), ?_⟩,
    (k15.trans tt6.kr).trans ku⟩
  intro x hx
  have hxZ : ofs S x < Z := by simp only [slot] at hx hZ; omega
  rw [mu, tt6.ts.low x hx, b5 x (Or.inl hxZ), o4 x (Or.inl hx), bS3 x hxZ]


end VG.Proof.Ffdh.PPC64LE.Cached
