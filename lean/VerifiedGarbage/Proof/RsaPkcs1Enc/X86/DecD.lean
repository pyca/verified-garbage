module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecPriv
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
public import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecMem

/-!
# RSAES-PKCS1-v1_5 decryption on x86: `D = I2OSP(d, k)`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecD.lean`): from here on the call's
result stays in `out` and in its slot (`Base`), as long as memory changes
only in `scratch`, the frame's other words and the stack below
(`Base.frame`). `D`, `k` bytes in `scratch`: zeros (`dZero_vp`,
`zero_vp`), then `d` copied to its end (`dCopy_vp`, `copy_vp`): `d` after
`k - d_len` zeros (`Dfull`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86 VG.WriteBytes
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_addS wp_subS)

variable {P : EP}

/-- The call's result, in `out` and in its slot. -/
def Base (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ ∃ rc, Priv P σ s.mem rc ∧ s.mem.readW (P.lay.fr oR) 32 = rc

/-- What the frame's slots and the stack below may change. -/
def Safe (P : EP) (r : Region) : Prop := P.OUT.Disjoint r ∧ Region.Disjoint ⟨P.lay.fr oR, 4⟩ r

theorem writtenOutcome_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.writtenOutcome m a K r o) :
    Spec.Rsa.writtenOutcome m' a K r o := by
  cases o with
  | ok y => exact ⟨h.1, hb.trans h.2⟩
  | invalid => exact ⟨h.1, hb.trans h.2⟩
  | fault => exact ⟨h.1, hb.trans h.2⟩

theorem Base.frame {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hs : ∀ r ∈ rs, Safe P r) : Base P σ t := by
  obtain ⟨hS, rc, pr, sl⟩ := h
  have hK := hS.1.k1024
  refine ⟨⟨hS.1, st⟩, rc, writtenOutcome_congr (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hs r hr).1)
    (by omega)) pr, ?_⟩
  rw [hf.readW (r := ⟨P.lay.fr oR, 4⟩) (Region.contains_self _ _) (fun r hr => (hs r hr).2) (by decide)]
  exact sl

/-! ## Safe regions -/

namespace In

variable {σ : State} (h : In P σ)
include h

theorem safe_sc {o n : Nat} (hn : o + n ≤ 8448) : Safe P (sc P o n) :=
  ⟨(h.sc_out hn).symm, h.fr_sc (by simp only [oR, frameBytes]; omega) hn⟩

theorem safe_low : Safe P P.lay.LOW :=
  ⟨(h.ok.low_buf (R := P.OUT) (.inr (by simp))).symm, Lay.fr_low (by simp only [oR]; omega)
    (by show (3448 : Nat) ≤ 2 ^ 32; decide)⟩

theorem safe_fr {d n : Nat} (hd : d + n ≤ frameBytes) (ho : d + n ≤ oR ∨ oR + 4 ≤ d) :
    Safe P ⟨P.lay.fr d, n⟩ :=
  ⟨(h.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + n ≤ frameBytes + 16; omega)).symm,
    Lay.fr_sep (by omega) (by simp only [oR]; omega) (by simp only [frameBytes] at hd; omega)⟩

end In

/-! ## The stages -/

/-- `D = I2OSP(d, k)`: `d` after zeros. -/
abbrev Dfull (P : EP) (σ : State) : List Byte := List.replicate (P.K - P.dl) 0 ++ dB P σ

/-- Before the zeros of `D`. -/
def D1 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sD ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

/-- `D` zeros. -/
def D2 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sD P.K).base P.K = List.replicate P.K 0

/-- Before the copy of `d`. -/
def D3 (P : EP) (σ s : State) : Prop :=
  D2 P σ s ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl)) ∧ s.gpr .esi = P.d ∧
    s.gpr .ecx = BitVec.ofNat 32 P.dl

/-- `D` built. -/
def D4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sD P.K).base P.K = Dfull P σ

theorem dZero_wp {σ s : State} (h : R2 P σ s) : WP isa (.block (saveR ++ dZero)) s (D1 P σ) := by
  obtain ⟨hs, pr⟩ := h
  have hK := hs.1.k1024
  simp only [saveR, dZero, scr, movI, List.cons_append, List.nil_append]
  refine hs.2.wp_strFr (d := oR) (by simp only [oR, frameBytes]; omega) fun t1 s1 m1 => ?_
  refine s1.wp_arg (j := 21) (r := .esi) (by simp) (by decide) fun t2 s2 u2 => ?_
  refine wp_addi fun t3 u3 => ?_
  have s3 := s2.upd u3 (by decide)
  refine s3.wp_arg (j := 4) (r := .ecx) (by simp) (by decide) fun t4 s4 u4 => ?_
  refine wp_movi fun t5 u5 => WP.block_nil ?_
  have s4' := s4.upd u5 (by decide)
  have mm : t5.mem = s.mem.writeW (P.lay.fr oR) (s.gpr .eax) := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem, m1.mem]
  refine ⟨⟨⟨hs.1, s4'⟩, s.gpr .eax, ?_, ?_⟩, ?_, ?_, u5.gpr⟩
  · rw [Priv, mm]
    refine writtenOutcome_congr (Proof.RsaPkcs1Sig.bytesAt_frame
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => ?_)
      (by omega)) pr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oR, frameBytes]; omega)).symm
  · rw [mm, Mem.readW_writeW_self32]
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.gpr]; rfl

theorem zero_wp {σ s : State} (h : D1 P σ s) : WP isa zeroLoop s (D2 P σ) := by
  obtain ⟨hb, esi, ecx, eax⟩ := h
  have hs := hb.1
  have hK := hs.1.k1024
  have hsD : (P.scr + BitVec.ofNat 32 sD).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 sD :=
    hs.1.scrA (by decide)
  have fit := hs.1.scr_fit
  have sl8 := hs.1.sl8
  refine WP.mono (zero_ok (p := P.scr + BitVec.ofNat 32 sD) (n := P.K) (by have := hs.1.k64; omega) (by omega)
    (by rw [hs.1.scr_toNat (by decide)]; simp only [sD]; omega) esi ecx eax
    (by rw [hsD]; exact St.sc_w hs (by simp only [sD]; omega))) fun t ht => ?_
  have fr : Frame [sc P sD P.K] s.mem t.mem := by
    rw [ht.mem, hsD]
    have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 sD) (List.replicate P.K 0)
    simpa using this
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.SCR, by simp, hs.1.sc_sub (by simp only [sD]; omega)⟩) ht.rd ht.wr
    (ht.other _ (by decide) (by decide))
  refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_sc (by simp only [sD]; omega)
  · rw [ht.mem, hsD]
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 sD)
      (List.replicate P.K 0) (by simp; omega)
    simpa using this

theorem dCopy_wp {σ s : State} (h : D2 P σ s) : WP isa (.block dCopy) s (D3 P σ) := by
  have hs := h.1.1
  have hdl := hs.1.dlK
  have hK := hs.1.k1024
  simp only [dCopy, scr, List.cons_append, List.nil_append]
  refine hs.2.wp_arg (j := 21) (r := .ebx) (by simp) (by decide) fun t1 s1 u1 => ?_
  refine wp_addi fun t2 u2 => ?_
  have s2 := s1.upd u2 (by decide)
  refine wp_addS (s2.readArg (j := 4) (by simp)) fun t3 u3 _ => ?_
  have s3 := s2.upd u3 (by decide)
  refine wp_subS (s3.readArg (j := 8) (by simp)) fun t4 u4 _ => ?_
  have s4 := s3.upd u4 (by decide)
  refine s4.wp_arg (j := 7) (r := .esi) (by simp) (by decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 8) (r := .ecx) (by simp) (by decide) fun t6 s6 u6 => WP.block_nil ?_
  have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨⟨⟨hs.1, s6⟩, ?_⟩, by rw [mm]; exact h.2⟩, ?_, ?_, ?_⟩
  · obtain ⟨rc, pr, sl⟩ := h.1.2
    exact ⟨rc, by rw [Priv, mm]; exact pr, by rw [mm]; exact sl⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr]
    simp only [EP.argv, List.getD_cons_succ, List.getD_cons_zero]
    rw [show BitVec.ofNat 32 P.K = BitVec.ofNat 32 (P.K - P.dl) + BitVec.ofNat 32 P.dl by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hdl], ← BitVec.add_assoc, BitVec.add_sub_cancel,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · rw [u6.gpr]; rfl

theorem copy_wp {σ s : State} (h : D3 P σ s) : WP isa Impl.Bignum.X86.copyBytes s (D4 P σ) := by
  obtain ⟨⟨hb, hz⟩, ebx, esi, ecx⟩ := h
  have hs := hb.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have hdl := hs.1.dlK
  have hfd := ok.fits P.D (by simp)
  have fit := hs.1.scr_fit
  have sl8 := hs.1.sl8
  simp only [BitVec.toNat_setWidth] at hfd
  rw [Nat.mod_eq_of_lt (by have := P.d.isLt; omega)] at hfd
  have hdst : (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl))).setWidth 64 =
      P.scr.setWidth 64 + BitVec.ofNat 64 (sD + (P.K - P.dl)) := hs.1.scrA (by simp only [sD]; omega)
  have ctx := Proof.Bignum.X86.copyCtx_of_regions s P.d (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl))) (n := P.dl)
    (by omega) hfd (by rw [hs.1.scr_toNat (by simp only [sD]; omega)]; simp only [sD]; omega)
    ⟨P.D, hs.2.inRo (by simp), Region.contains_self _ _⟩
    (by simp only [Proof.Bignum.X86.byteAddr]; rw [hdst]; exact St.sc_w hs (by simp only [sD]; omega))
    (by simp only [Proof.Bignum.X86.byteAddr]; rw [hdst]
        exact (hs.1.sc_ro (by simp only [sD]; omega) (R := P.D) (by simp)).symm)
  refine WP.mono (Proof.Bignum.X86.copyBytes_ok s ctx (by have := hs.1.dl1; omega) esi ebx ecx) fun t ht => ?_
  have fr := ht.frame (by rw [hs.1.scr_toNat (by simp only [sD]; omega)]; simp only [sD]; omega)
  simp only [Proof.Bignum.X86.byteAddr] at fr
  rw [hdst] at fr
  have hsub : Region.Sub (sc P (sD + (P.K - P.dl)) P.dl) P.SCR := hs.1.sc_sub (by simp only [sD]; omega)
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hsub⟩) ht.rest.2.1 ht.rest.2.2
    (ht.rest.1 .esp (by decide))
  refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_sc (by simp only [sD]; omega)
  · have hl : (Dfull P σ).length = P.K := by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega
    show Spec.Rsa.bytesAt t.mem (P.scr.setWidth 64 + BitVec.ofNat 64 sD) P.K = Dfull P σ
    have e := Proof.RsaPkcs1Sig.bytesAt_eq (m := t.mem) (p := P.scr.setWidth 64 + BitVec.ofNat 64 sD)
      (xs := Dfull P σ) fun i hi => ?_
    · rw [hl] at e; exact e
    rw [hl] at hi
    have scrN := hs.1.scr_toNat (o := sD + i) (by simp only [sD]; omega)
    rw [Offset.add_ofNat_add_ofNat]
    have bA : ∀ j < P.dl, Proof.Bignum.X86.byteAddr (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl)) + BitVec.ofNat 32 j) =
        P.scr.setWidth 64 + BitVec.ofNat 64 (sD + (P.K - P.dl) + j) := by
      intro j hj
      simp only [Proof.Bignum.X86.byteAddr]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sD]; omega)]
    rcases (by omega : i < P.K - P.dl ∨ P.K - P.dl ≤ i) with hi' | hi'
    · -- One of the zeros.
      have o := ht.outside (P.scr.setWidth 64 + BitVec.ofNat 64 (sD + i)) fun j hj he => by
        rw [bA j hj] at he
        exact Offset.add_ofNat_ne _ (by simp only [sD]; omega) (by simp only [sD]; omega) (by omega) he
      have z := congrArg (fun l => l.getD i 0) hz
      simp only at z
      rw [Proof.RsaPkcs1Sig.bytesAt_getD (by omega), Offset.add_ofNat_add_ofNat] at z
      rw [o, z, Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, hi', show i < P.K by omega]
    · -- A byte of `d`.
      obtain ⟨j, rfl⟩ : ∃ j, i = P.K - P.dl + j := ⟨i - (P.K - P.dl), by omega⟩
      have hj : j < P.dl := by omega
      have c := ht.copied j hj
      rw [bA j hj] at c
      rw [show sD + (P.K - P.dl + j) = sD + (P.K - P.dl) + j by omega, c,
        Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp), List.length_replicate, Nat.add_sub_cancel_left,
        Proof.RsaPkcs1Sig.bytesAt_getD hj]
      have ro := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.D) (by simp))
      simp only at ro
      rw [Proof.RsaPkcs1Sig.bytesAt_getD hj, Proof.RsaPkcs1Sig.bytesAt_getD hj] at ro
      simp only [Proof.Bignum.X86.byteAddr]
      rw [show (P.d + BitVec.ofNat 32 j).setWidth 64 = P.d.setWidth 64 + BitVec.ofNat 64 j from addr_eq (by omega)]
      exact ro

end VG.Proof.RsaPkcs1Enc.X86.Dec
