module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.PSat
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.PVerified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Base
public import VerifiedGarbage.Proof.RsaOaep.X86.Base
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtHash
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.RsaOaep.X86.Mgf
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaOaep.X86.MgfSlots
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PubCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-! ### `RsaOaep.X86.Enc.Verified`, which only this module used -/

section

/-! ### `RsaOaep.X86.Enc.Call`, which only this module used -/

section

/-! ### `RsaOaep.X86.Enc.Mask`, which only this module used -/

section

/-! ### `RsaOaep.X86.Enc.Em`, which only this module used -/

section

/-! ### `RsaOaep.X86.Enc.Chk`, which only this module used -/

section

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: the checks

As on ARMv7 (`Proof/RsaOaep/Arm/EncChk.lean`): `chk_vp`: `scratch` into
`ebp`, and the flags of whether the message fits (`fits`), from the lengths
alone. `fail_vp`: when it does not, zeros to `out` and 0 returned, as
`encrypt` (`Proof.RsaOaep.encrypt_none`) says.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa arg ld mi zeroLoop)

variable (h g : OHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.H.D P σ ∧ (P.lay h.H.D).St σ s

/-- The label, the message and the seed, as they are in the run from `σ`. -/
abbrev labB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.lab.setWidth 64) P.ll
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.msg.setWidth 64) P.ml
abbrev seedB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.seed.setWidth 64) h.H.D

/-- Whether the message fits. -/
abbrev fits (P : EP) : Prop := 2 * h.H.D + 2 + P.ml ≤ P.K

/-- What the function writes to `out` and returns. -/
abbrev Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (P.out.setWidth 64) P.K r (Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ)
      (seedB h P σ))

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h g P σ s.mem (s.gpr .eax)

theorem enc_arg {j : Nat} (hj : j < 18) {D : Nat} {P : EP} : j < ((P.lay D).argv).length := by simp; omega_using [hj]

/-- An argument's place may be read. -/
theorem argR {D : Nat} {P : EP} {σ t : State} (hg : Geo (P.lay D) P.scr) (ct : Ctx (P.lay D) P.scr σ t) {j : Nat}
    (hj : j < 18) : InRegions (t.rd ++ t.wr) (VG.X86.addr (P.lay D).B (Impl.RsaPkcs1Sig.X86.argOff frameBytes j)) 4 := by
  rw [hg.aArg ct.st.ok j (enc_arg hj), ct.st.rd, ct.st.wr]; exact ct.st.ok.arg_read (enc_arg hj)

/-- The flags of the checks: zero exactly when `c + ml ≤ K`. -/
theorem chk_z {K c ml : Nat} (hK : K < 2 ^ 32) (hc : c < 2 ^ 32) (hml : ml < 2 ^ 32) :
    let x := (if decide ((BitVec.ofNat 32 K).toNat < (BitVec.ofNat 32 c).toNat) = true then BitVec.allOnes 32 else 0) |||
      (if decide ((BitVec.ofNat 32 K - BitVec.ofNat 32 c).toNat < (BitVec.ofNat 32 ml).toNat) = true then
        BitVec.allOnes 32 else 0)
    (x &&& x == 0) = decide (c + ml ≤ K) := by
  intro x
  rw [BitVec.and_self]
  simp only [x, toNat_ofNat_lt hK, toNat_ofNat_lt hc, toNat_ofNat_lt hml]
  by_cases hcK : K < c
  · have h1 : decide (c + ml ≤ K) = false := decide_eq_false (by omega_using [hcK])
    rw [decide_eq_true hcK, h1]
    simp
  · rw [decide_eq_false hcK, sub_ofNat (by omega_using [hcK]), toNat_ofNat_lt (by omega_using [hK])]
    by_cases e : K - c < ml
    · rw [decide_eq_true e, decide_eq_false (by omega_using [e])]; simp
    · rw [decide_eq_false e, decide_eq_true (by omega_using [hcK, e])]; simp

/-! ## The checks -/

/-- After `encChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ s.zf = some (decide (fits h P))

theorem chk_vp (P : EP) : VP (S h P) (.block (encChk h.H)) (C0 h P) := by
  refine VP.taint [.esp] h.certs.encChk (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]) fun σ s ⟨hi, hs⟩ => ?_
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hD := h.D_le
  have hK := hi.k1024
  simp only [encChk, ld, Impl.RsaPkcs1Sig.X86.stk]
  refine hs.wp_arg (enc_arg (j := 12) (by decide)) (by decide) fun t1 s1 u1 => ?_
  obtain c1 : Ctx (P.lay h.H.D) P.scr σ t1 := ⟨s1, by rw [u1.gpr]; rfl⟩
  refine c1.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t2 c2 u2 => ?_
  refine wp_subi fun t3 u3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => ?_
  obtain c4 : Ctx (P.lay h.H.D) P.scr σ t4 := (c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
  refine wp_cmpm (B := (P.lay h.H.D).B) (by rw [c4.st.sp])
    (by rw [hg.aArg ok 9 (enc_arg (by decide)), c4.st.rd, c4.st.wr]; exact c4.st.ok.arg_read (enc_arg (by decide)))
    fun t5 f5 cf5 _ => wp_sbb_self cf5 fun t6 u6 => ?_
  refine wp_or fun t7 u7 => wp_test fun t8 f8 z8 => WP.block_nil ⟨Ctx.fupd (((c4.fupd f5).upd u6 (by decide)
    (by decide)).upd u7 (by decide) (by decide)) f8, hi, ?_⟩
  rw [z8]
  obtain e2 : t2.gpr .eax = BitVec.ofNat 32 P.K := by rw [u2.gpr]; rfl
  obtain e3 : t3.gpr .eax = BitVec.ofNat 32 P.K - BitVec.ofNat 32 (2 * h.H.D + 2) := by rw [u3.gpr, e2]
  obtain m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  rw [u4.other _ (by decide), e3, m4, hg.aArg ok 9 (enc_arg (by decide)), hs.arg (enc_arg (by decide))] at u6
  rw [u7.gpr, u6.other _ (by decide), u6.gpr, f5.gpr, u4.gpr, e2]
  exact congrArg some (chk_z (by omega_using [hK]) (by omega_using [hD]) hi.ml32)

/-! ## A message that does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.bytesAt_len]

theorem msgB_length (P : EP) (σ : State) : (msgB P σ).length = P.ml := RsaPkcs1Sig.bytesAt_len _ _ _

/-- `out` zeros and 0, the specification's result. -/
abbrev F1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ ¬ fits h P ∧ s.gpr .esi = P.out ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

abbrev F2 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ ¬ fits h P ∧
    Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = List.replicate P.K 0

theorem fail_vp (P : EP) : VP (fun σ s => C0 h P σ s ∧ isa.eval .ne s = some true) encFail (Fin h g P) := by
  show VP _ (.seq (.block [ld .esi (arg 0), ld .ecx (arg 3), mi .eax 0]) (.seq zeroLoop (.block [mi .eax 0]))) _
  refine VP.seq (G := F1 h P) (VP.taint [.esp] encFailArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.st.sp, h₂.1.1.st.sp])
    fun σ s ⟨⟨hc, hi, z⟩, e⟩ => ?_) (VP.seq (G := F2 h P) ?_ ?_)
  · have hf : ¬ fits h P := fun hfits => by
      simp only [eval, z, decide_eq_true hfits] at e
      exact absurd e (by decide)
    have hg := hi.geo
    simp only [ld, mi]
    refine hc.wp_arg hg (enc_arg (j := 0) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      c1.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t2 c2 u2 => wp_movi fun t3 u3 =>
        WP.block_nil ⟨c2.upd u3 (by decide) (by decide), hi, hf, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u3.other, u2.other, u1.gpr]; rfl
    · simp (disch := decide) only [u3.other, u2.gpr]; rfl
    · rw [u3.gpr]; rfl
  · by_cases hP : ∃ σ, In h.H.D P σ
    swap
    · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
    obtain ⟨σ₀, hi₀⟩ := hP
    have hK := hi₀.k1024
    obtain hfo := hi₀.ok.fits P.OUT (by simp)
    simp only [BitVec.toNat_setWidth] at hfo
    rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega_using [])] at hfo
    obtain wb : WBuf (P.lay h.H.D) P.out P.K := ⟨hfo, by omega_using [hK], ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩
    refine (zero_vp (scr := P.scr) wb (by have := hi₀.k64; omega_using [this])
      (Inv := fun σ _ => In h.H.D P σ ∧ ¬ fits h P) fun _ _ _ hi _ => hi).mono
      (fun σ s ⟨hc, hi, hf, si, cx, ax⟩ => ⟨hc, ⟨hi, hf⟩, si, cx, ax⟩) fun σ s ⟨hc, ⟨hi, hf⟩, hz⟩ => ?_
    refine ⟨hc, hi, hf, ?_⟩
    apply List.ext_getElem (by simp [RsaPkcs1Sig.bytesAt_len])
    intro i h₁ h₂
    rw [RsaPkcs1Sig.bytesAt_len] at h₁
    rw [List.getElem_replicate, ← hz i h₁, ← RsaPkcs1Sig.bytesAt_getD (m := s.mem) (p := P.out.setWidth 64) h₁ 0,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [RsaPkcs1Sig.bytesAt_len]; exact h₁)]; rfl
  · refine VP.taint [.esp] ret0_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp]) fun σ s ⟨hc, hi, hf, hz⟩ => ?_
    simp only [mi]
    refine wp_movi fun t u => WP.block_nil ⟨⟨hi, hc.st.upd u (by decide)⟩, fun _ => ?_⟩
    obtain en : Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ) (seedB h P σ) = none :=
      Proof.RsaOaep.encrypt_none (by rw [nB_length hi, msgB_length, h.glen]; simp only [fits] at hf; omega_using [hf])
    rw [en, u.gpr, u.mem]
    exact ⟨rfl, hz⟩

end VG.Proof.RsaOaep.X86.Enc

end

end


/-!
# RSAES-OAEP encryption with a precomputed public key on x86: `EM` before masking

As on ARMv7 (`Proof/RsaOaep/Arm/EncEm.lean`): when the message fits, `EM`'s
`k` bytes at `scratch + oEm` cleared, the seed after its first byte, the
label's hash (`labelT_vp`, with the table `hash`) after the seed, `0x01`
before the message and the message at its end: `EM = 0x00 ‖ seed ‖ lHash ‖ 0… ‖ 0x01 ‖ M`
(`Proof.RsaOaep.EmAt`, `em_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oCW oSt oDig oEm arg ld mi atS addi addSlot zeroLoop)
open VG.Proof.RsaPss.X86.Sg (vpAssoc)

variable (h : OHash)

/-- A state of the body when the message fits. -/
abbrev E0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ fits h P

/-- `EM`'s bytes, from the memory. -/
abbrev emV (scr : BitVec 32) (m : Mem) (o : Nat) : Byte := m (sa scr (oEm + o))

/-- The label's hash. -/
abbrev lhB (P : EP) (σ : State) : List Byte := h.G.hash (labB P σ)

/-- The facts that do not change in the body. -/
abbrev K0 (P : EP) (σ : State) : Prop := In h.H.D P σ ∧ fits h P

/-! ## The pieces -/

/-- `EM` cleared. -/
abbrev Z1 (P : EP) (m : Mem) : Prop := ∀ i < P.K, emV P.scr m i = 0

theorem em1_vp (P : EP) :
    VP (E0 h P) (.seq (.block clrEm) zeroLoop) (fun σ s => E0 h P σ s ∧ Z1 P s.mem) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ K0 h P σ) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 oEm ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0)
    (VP.taint [.esp, .ebp] clrEm_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hf⟩ => ?_)
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by oomega) (by omega_using [hK0])) (by omega_using [hK0]) (Inv := fun σ _ => K0 h P σ)
      fun σ m m' hm _ => hm).mono (fun σ s ⟨⟨hc, hm⟩, si, cx, ax⟩ => ⟨hc, hm, si, cx, ax⟩)
      fun σ s ⟨hc, hm, hz⟩ => ⟨⟨hc, hm⟩, fun i hi => by rw [emV, ← hg.byteAt_scr (by oomega)]; exact hz i hi⟩)
  simp only [clrEm, atS, addi, ld, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  obtain c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine c2.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 =>
    WP.block_nil ⟨⟨c3.upd u4 (by decide) (by decide), hi, hf⟩, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u4.other _ (by decide), u3.gpr]; rfl
  · rw [u4.gpr]; rfl

/-- The seed after `EM`'s first byte, zeros elsewhere. -/
abbrev Z2 (P : EP) (sd : List Byte) (m : Mem) : Prop :=
  emV P.scr m 0 = 0 ∧ (∀ i < h.H.D, emV P.scr m (1 + i) = sd.getD i 0) ∧
    ∀ i, 1 + h.H.D ≤ i → i < P.K → emV P.scr m i = 0

/-- A buffer only read, byte by byte, in a state of the body. -/
theorem ro_byte {D : Nat} {P : EP} {σ s : State} (hs : (P.lay D).St σ s) {R : Region} (hR : R ∈ (P.lay D).ro)
    {i : Nat} (hi : i < R.len) : s.mem (R.base + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem R.base R.len).getD i 0 := by
  obtain e := congrArg (fun l => l.getD i 0) (hs.ro hR)
  simp only [RsaPkcs1Sig.bytesAt_getD hi] at e
  rw [e, RsaPkcs1Sig.bytesAt_getD hi]

theorem em2_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Z1 P s.mem) (.seq (.block (seedSet h.H)) Impl.Bignum.X86.copyBytes)
      (fun σ s => E0 h P σ s ∧ Z2 h P (seedB h P σ) s.mem) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hsd : RBuf (P.lay h.H.D) P.seed h.H.D := by
    obtain hf := hi₀.ok.fits (P.SEED h.H.D) (by simp)
    simp only [BitVec.toNat_setWidth] at hf
    rw [Nat.mod_eq_of_lt (by have := P.seed.isLt; omega_using [])] at hf
    exact ⟨hf, by omega_using [hD], ⟨P.SEED h.H.D, by simp, Region.contains_self _ _⟩⟩
  obtain sep : Region.Disjoint ⟨P.seed.setWidth 64, h.H.D⟩ ⟨(P.scr + BitVec.ofNat 32 (oEm + 1)).setWidth 64, h.H.D⟩ := by
    rw [hg.scrA (by oomega)]
    exact (hg.ro ok (o := oEm + 1) (n := h.H.D) (by oomega) (R := P.SEED h.H.D) (by simp)).symm
  -- What the copy keeps: `EM`'s other bytes, zero.
  let X : State → Mem → Prop := fun σ m => K0 h P σ ∧ emV P.scr m 0 = 0 ∧
    ∀ i, 1 + h.H.D ≤ i → i < P.K → emV P.scr m i = 0
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ X σ s.mem) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + 1) ∧ s.gpr .esi = P.seed ∧ s.gpr .ecx = BitVec.ofNat 32 h.H.D ∧
      ∀ i < h.H.D, s.mem (byteAt P.seed i) = (seedB h P σ).getD i 0)
    (VP.taint [.esp, .ebp] h.certs.seedSet (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hi, hf⟩, hz⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + 1) (n := h.H.D) (by oomega) hD0) hsd sep hD0 (Inv := X)
      (f := fun σ i => (seedB h P σ).getD i 0) fun σ m m' ⟨k, z0, zr⟩ hf => ?_).mono
      (fun σ s ⟨⟨hc, hm⟩, bx, si, cx, hb⟩ => ⟨hc, hm, bx, si, cx, hb⟩)
      fun σ s ⟨hc, ⟨k, z0, zr⟩, hb⟩ => ⟨⟨hc, k⟩, z0, fun i hi => ?_, zr⟩)
  · simp only [seedSet, atS, addi, ld, mi, List.cons_append, List.nil_append]
    refine hc.wp_arg hg (enc_arg (j := 10) (by decide)) (by decide) (by decide) fun t1 c1 u1 => ?_
    refine wp_mov fun t2 u2 => wp_addi fun t3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
    obtain m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨((c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide),
      ⟨hi, hf⟩, ?_, fun i h1 h2 => ?_⟩, ?_, ?_, ?_, fun i hi' => ?_⟩
    · rw [emV, m4]; exact hz 0 (by omega)
    · rw [emV, m4]; exact hz i h2
    · simp (disch := decide) only [u4.other, u3.gpr, u2.gpr, c1.ebp]
    · simp (disch := decide) only [u4.other, u3.other, u2.other, u1.gpr]; rfl
    · rw [u4.gpr]
    · rw [m4]; exact ro_byte hc.st (R := P.SEED h.H.D) (by simp) hi'
  · rw [hg.scrA (by oomega)] at hf
    refine ⟨k, ?_, fun i h1 h2 => ?_⟩
    · rw [emV, ← z0]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oEm + 0) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    · rw [emV, ← zr i h1 h2]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
  · rw [emV, show oEm + (1 + i) = oEm + 1 + i by oomega, ← hg.byteAt_scr (by oomega)]
    exact hb i hi

/-! ## `EM`'s bytes as functions -/

/-- `EM`'s first `k` bytes are `f`. -/
abbrev EMv (P : EP) (m : Mem) (f : Nat → Byte) : Prop := ∀ i < P.K, emV P.scr m i = f i

/-- `EM` with the seed. -/
abbrev e2 (P : EP) (σ : State) (i : Nat) : Byte :=
  if 1 ≤ i ∧ i < 1 + h.H.D then (seedB h P σ).getD (i - 1) 0 else 0

/-- `EM` with the seed and `lHash`. -/
abbrev e3 (P : EP) (σ : State) (i : Nat) : Byte :=
  if 1 + h.H.D ≤ i ∧ i < 1 + 2 * h.H.D then (lhB h P σ).getD (i - (1 + h.H.D)) 0 else e2 h P σ i

/-- `EM` with `0x01`. -/
abbrev e4 (P : EP) (σ : State) (i : Nat) : Byte := if i = P.K - P.ml - 1 then 1 else e3 h P σ i

/-- `EM` before masking. -/
abbrev e5 (P : EP) (σ : State) (i : Nat) : Byte :=
  if P.K - P.ml ≤ i ∧ i < P.K then (msgB P σ).getD (i - (P.K - P.ml)) 0 else e4 h P σ i

theorem z2_emv {P : EP} {σ : State} {m : Mem} (hz : Z2 h P (seedB h P σ) m) : EMv P m (e2 h P σ) := by
  intro i hi
  obtain ⟨z0, sd, zr⟩ := hz
  simp only [e2]
  by_cases h1 : 1 ≤ i ∧ i < 1 + h.H.D
  · rw [ite_eq_left h1, show i = 1 + (i - 1) by omega_using [h1], sd _ (by omega_using [h1]), Nat.add_sub_cancel_left]
  · rw [ite_eq_right h1]
    by_cases h0 : i = 0
    · subst h0; exact z0
    · exact zr i (by omega_using [h1, h0]) hi

theorem add_ofNat_sub {x : BitVec 32} {a b : Nat} (hb : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  have : BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel hb]
  rw [this, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `EM`'s bytes, kept by a write before `EM` in our part of `scratch`. -/
theorem emv_keep {P : EP} (hg : Geo (P.lay h.H.D) P.scr) (hK : P.K ≤ 1024) {m m' : Mem} {f : Nat → Byte}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (∃ o n, o + n ≤ oEm ∧ r = sR P.scr o n) ∨
      r = (P.lay h.H.D).LOW) (he : EMv P m f) : EMv P m' f := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro i hi
  rw [emV, ← he i hi]
  refine hf _ fun r hr => ?_
  rcases hd r hr with ⟨o, n, h2, rfl⟩ | rfl
  · exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _ (Region.contains_self _ _)
  · exact hg.low ok (o := oEm + i) (n := 1) (by oomega) _ (Region.contains_self _ _)

/-- The label's hash function's table, the argument 16, in a buffer only read. -/
theorem tblL_of {D : Nat} {P : EP} {σ : State} (hi : In D P σ) :
    ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (VG.X86.addr P.tabL o) 4 := by
  obtain hf := hi.ok.fits P.TABL (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tabL.isLt; omega_using [])] at hf
  refine ⟨P.TABL, by simp, fun o ho => ?_⟩
  show (⟨P.tabL.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tabL o) 4
  rw [addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- What the label's hash keeps, with its table's address in its slot. -/
abbrev L0 (P : EP) (σ : State) (m : Mem) : Prop :=
  (K0 h P σ ∧ EMv P m (e2 h P σ)) ∧ m.readW ((P.lay h.H.D).fr sTab) 32 = P.tabL

/-- The label's hash function's table's address to its slot, and the label's
hash at `oDig`, with that table's hash function `h`. -/
theorem em3_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => (E0 h P σ s ∧ Z2 h P (seedB h P σ) s.mem) ∧ s.syms = σ.syms)
      (.seq (.block (tabSlot 16)) (hashLabelT f 6 oDig))
      (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e2 h P σ) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oDig + i)) = (lhB h P σ).getD i 0) ∧ s.syms = σ.syms) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hl := hi₀.ok.fits P.LAB (by simp)
  simp only [BitVec.toNat_setWidth] at hl
  rw [Nat.mod_eq_of_lt (by have := P.lab.isLt; omega_using [])] at hl
  obtain hlab : RBuf (P.lay h.H.D) P.lab P.ll := ⟨hl, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  obtain dS : ∀ {o n : Nat}, o + n ≤ oRsa → Region.Disjoint ⟨P.lab.setWidth 64, P.ll⟩ (sR P.scr o n) :=
    fun hon => (hg.ro ok hon (R := P.LAB) (by simp)).symm
  -- The table's address to its slot.
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ L0 h P σ s.mem) ∧ s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] tabSlot16_taint (sp_bp fun _ _ h => h.1.1)
      fun σ s ⟨⟨hc, hi, hf⟩, hz⟩ => ?_)) ?_
  · simp only [tabSlot, ld, Impl.RsaPss.X86.st]
    refine hc.wp_arg hg (j := 16) (by simp) (by decide) (by decide) fun t1 c1 u1 =>
      c1.wp_st hg (d := sTab) (by decide) fun t2 c2 m2 => WP.block_nil ?_
    obtain fr : Frame [slotR (P.lay h.H.D) sTab] s.mem t2.mem := by
      rw [m2.mem, u1.mem]; exact slot_frame _ _ _ _
    refine ⟨c2, ⟨⟨hi, hf⟩, fun i hi' => ?_⟩, ?_⟩
    · rw [emV, ← z2_emv h hz i hi']
      refine fr _ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (by oomega) (by rw [hg.F]; decide)).symm _
        (Region.contains_self _ _)
    · rw [m2.mem, Mem.readW_writeW_self32, u1.gpr]; rfl
  -- The label's hash.
  refine (labelT_vp hg h (f := f) (p := P.tabL) (ai := P.aiL) (au := P.auL) (af := P.afL) (tblL_of hi₀) fne
    (j := 6) (o := oDig) (ll := P.ll) (lab := P.lab) (by simp) updLab6_taint finLab6_taint
    rfl rfl hlab (dS (by oomega)) (dS (by oomega)) (ok.low_buf (R := P.LAB) (.inl (by simp))).symm (by oomega)
    (by oomega) (labB := labB P) (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := L0 h P) ?_ (fun _ _ hm => hm.2) (fun σ _ hm => hTL σ hm.1.1.1.tabTL)).mono
    (fun _ _ hh => hh) fun σ s ⟨⟨hc, ⟨⟨⟨hi, hf⟩, he⟩, _⟩, hd⟩, sy⟩ => ⟨⟨⟨hc, hi, hf⟩, he, hd⟩, sy⟩
  intro σ m m' ⟨⟨k, he⟩, hs⟩ hf
  refine ⟨⟨k, emv_keep h hg hK hf ?_ he⟩, slot_keep hf (fun r hr => ?_) hs⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨oSt, h.H.S, by oomega, rfl⟩
    · exact .inl ⟨oCW, h.ok.Wb, by oomega, rfl⟩
    · exact .inr rfl
    · exact .inl ⟨oDig, h.H.F, by oomega, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
    · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
    · exact Lay.fr_low (by decide) (by show (100 : Nat) ≤ 2 ^ 32; decide)
    · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)

/-- `lHash` after the seed. -/
theorem em4_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ EMv P s.mem (e2 h P σ) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oDig + i)) = (lhB h P σ).getD i 0)
      (.seq (.block (lhSet h.H)) Impl.Bignum.X86.copyBytes)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  let X : State → Mem → Prop := fun σ m => K0 h P σ ∧
    ∀ i < P.K, (i < 1 + h.H.D ∨ 1 + 2 * h.H.D ≤ i) → emV P.scr m i = e2 h P σ i
  obtain sp4 : Region.Disjoint ⟨(P.scr + BitVec.ofNat 32 oDig).setWidth 64, h.H.D⟩
      ⟨(P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D)).setWidth 64, h.H.D⟩ := by
    rw [hg.scrA (by oomega), hg.scrA (by oomega)]
    exact Geo.sep (by oomega) (by oomega) (by oomega)
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ X σ s.mem) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oDig ∧
      s.gpr .ecx = BitVec.ofNat 32 h.H.D ∧
      ∀ i < h.H.D, s.mem (byteAt (P.scr + BitVec.ofNat 32 oDig) i) = (lhB h P σ).getD i 0)
    (VP.taint [.esp, .ebp] h.certs.lhSet (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hi, _⟩, he, hd⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + 1 + h.H.D) (n := h.H.D) (by oomega) hD0) (hg.rbuf (o := oDig) (n := h.H.D)
      (by oomega) hD0) sp4 hD0 (Inv := X) (f := fun σ i => (lhB h P σ).getD i 0) fun σ m m' ⟨k, ho⟩ hf' => ?_).mono
      (fun σ s ⟨⟨hc, hm⟩, bx, si, cx, hb⟩ => ⟨hc, hm, bx, si, cx, hb⟩)
      fun σ s ⟨hc, ⟨k, ho⟩, hb⟩ => ⟨⟨hc, k⟩, fun i hi => ?_⟩)
  · simp only [lhSet, atS, addi, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => wp_movi fun t5 u5 =>
      WP.block_nil ?_
    obtain c5 : Ctx (P.lay h.H.D) P.scr σ t5 := ((((hc.upd u1 (by decide) (by decide)).upd u2 (by decide)
      (by decide)).upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)
    obtain m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c5, ⟨hi, hf⟩, fun i hi _ => by rw [emV, m5]; exact he i hi⟩, ?_, ?_, ?_, fun i hi => ?_⟩
    · simp (disch := decide) only [u5.other, u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
    · simp (disch := decide) only [u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u5.gpr]
    · rw [m5, hg.byteAt_scr (by oomega)]; exact hd i hi
  · rw [hg.scrA (by oomega)] at hf'
    refine ⟨k, fun i hi hr => ?_⟩
    rw [emV, ← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
        (Region.contains_self _ _)
  · simp only [e3]
    by_cases hr : 1 + h.H.D ≤ i ∧ i < 1 + 2 * h.H.D
    · rw [ite_eq_left hr, emV, show oEm + i = oEm + 1 + h.H.D + (i - (1 + h.H.D)) by oomega,
        ← hg.byteAt_scr (by oomega)]
      exact hb _ (by omega_using [hr])
    · rw [ite_eq_right hr]; exact ho i hi (by omega_using [hr])

/-- `0x01` before the message's place at the end of `EM`. -/
theorem em5_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) (.seq (.block msgPos) (.block put1))
      (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e4 h P σ)) ∧
        s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml)) ∧ s.gpr .esi = P.msg ∧
        s.gpr .ecx = BitVec.ofNat 32 P.ml ∧ s.zf = some (decide (P.ml = 0))) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine VP.seq (G := fun σ s => (E0 h P σ s ∧ EMv P s.mem (e3 h P σ)) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml - 1)))
    (VP.taint [.esp, .ebp] msgPos_taint (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hi, hf'⟩, he⟩ => ?_)
    (VP.taint [.esp, .ebx] put1_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨hc, hi, hf'⟩, he⟩, bx⟩ => ?_)
  · simp only [msgPos, atS, addi, addSlot, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    obtain c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.H.D).B) (by rw [c2.st.sp]) (argR hg c2 (j := 3) (by decide)) fun t3 u3 => ?_
    obtain c3 := c2.upd u3 (by decide) (by decide)
    refine wp_subm (B := (P.lay h.H.D).B) (by rw [c3.st.sp]) (argR hg c3 (j := 9) (by decide)) fun t4 u4 => ?_
    refine wp_subi fun t5 u5 _ _ => WP.block_nil ⟨⟨⟨(c3.upd u4 (by decide) (by decide)).upd u5 (by decide)
      (by decide), hi, hf'⟩, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact he⟩, ?_⟩
    rw [u5.gpr, u4.gpr, u3.gpr, u3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp, hg.aArg ok 3 (enc_arg (by decide)),
      hg.aArg ok 9 (enc_arg (by decide)), hc.st.arg (enc_arg (by decide)), hc.st.arg (enc_arg (by decide))]
    show P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ml - BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, add_ofNat_sub (by omega_using [hfit]), add_ofNat_sub (by oomega)]
    congr 2; oomega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · simp only [put1, mi, addi, ld, Impl.RsaPkcs1Sig.X86.at_]
    refine wp_movi fun t1 u1 => ?_
    obtain c1 := hc.upd u1 (by decide) (by decide)
    obtain ad : VG.X86.addr (t1.gpr .ebx) 0 = sa P.scr (oEm + (P.K - P.ml - 1)) := by
      rw [u1.other _ (by decide), bx, hg.addrD (by oomega), Nat.add_zero]
    refine wp_store8 (a := sa P.scr (oEm + (P.K - P.ml - 1))) (by rw [ea_at]; exact ad)
      (by rw [u1.wr]; exact hg.wr hc.st (by oomega)) fun t2 m2 => ?_
    obtain m2' : t2.mem = s.mem.writeW (sa P.scr (oEm + (P.K - P.ml - 1))) (1 : Byte) := by
      rw [m2.mem, Reg8.reg, u1.gpr, u1.mem]; rfl
    obtain fr : Frame [sR P.scr (oEm + (P.K - P.ml - 1)) 1] s.mem t2.mem := by
      rw [m2']; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_using []) (by oomega)
    obtain c2 : Ctx (P.lay h.H.D) P.scr σ t2 := ctxW hg hc fr (fun r hr => .inl ⟨oEm + (P.K - P.ml - 1), 1, by oomega,
      by simpa using hr⟩) (by rw [m2.rd, u1.rd]) (by rw [m2.wr, u1.wr])
      (by rw [m2.gpr, u1.other _ (by decide)]) (by rw [m2.gpr, u1.other _ (by decide)])
    refine wp_addi fun t3 u3 => ?_
    obtain c3 := c2.upd u3 (by decide) (by decide)
    refine c3.wp_arg hg (enc_arg (j := 8) (by decide)) (by decide) (by decide) fun t4 c4 u4 =>
      c4.wp_arg hg (enc_arg (j := 9) (by decide)) (by decide) (by decide) fun t5 c5 u5 =>
        wp_test fun t6 f6 z6 => WP.block_nil ⟨⟨⟨c5.fupd f6, hi, hf'⟩, fun i hi' => ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [emV, f6.mem, u5.mem, u4.mem, u3.mem, m2', sa_write P.scr _ _ (by oomega) (by oomega)]
      by_cases e : i = P.K - P.ml - 1
      · rw [ite_eq_left (by omega_using [e])]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega_using [e])]; exact (he i hi').trans (ite_eq_right e).symm
    · rw [f6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.gpr, m2.gpr, u1.other _ (by decide), bx,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, show oEm + (P.K - P.ml - 1) + 1 = oEm + (P.K - P.ml) by oomega]
    · rw [f6.gpr, u5.other _ (by decide), u4.gpr]; rfl
    · rw [f6.gpr, u5.gpr]; rfl
    · rw [z6, u5.gpr, BitVec.and_self]
      exact congrArg some (ofNat_beq_zero hi.ml32)

/-- The message at the end of `EM`, if it is not empty. -/
theorem em6_vp (P : EP) :
    VP (fun σ s => (E0 h P σ s ∧ EMv P s.mem (e4 h P σ)) ∧
        s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + (P.K - P.ml)) ∧ s.gpr .esi = P.msg ∧
        s.gpr .ecx = BitVec.ofNat 32 P.ml ∧ s.zf = some (decide (P.ml = 0)))
      (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e5 h P σ)) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s hs => hf hs.1.1.2.2
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine VP.ite (fun σ s h' => ⟨_, h'.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2])
    (VP.block_nil fun σ s ⟨⟨⟨hc, he⟩, _, _, _, z⟩, e⟩ => ⟨hc, fun i hi => ?_⟩) ?_
  · have h0 : P.ml = 0 := by simp only [eval, z, Option.some.injEq, decide_eq_true_eq] at e; exact e
    rw [he i hi]; exact (ite_eq_right (by omega_using [h0])).symm
  by_cases h0 : P.ml = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
  obtain hm := hi₀.ok.fits P.MSG (by simp)
  simp only [BitVec.toNat_setWidth] at hm
  rw [Nat.mod_eq_of_lt (by have := P.msg.isLt; omega_using [])] at hm
  obtain hmsg : RBuf (P.lay h.H.D) P.msg P.ml := ⟨hm, hi₀.ml32, ⟨P.MSG, by simp, Region.contains_self _ _⟩⟩
  refine (copy_vp (hg.wbuf (o := oEm + (P.K - P.ml)) (n := P.ml) (by oomega) (by omega_using [h0])) hmsg
    (by rw [hg.scrA (by oomega)]; exact (hg.ro ok (by oomega) (R := P.MSG) (by simp)).symm)
    (by omega_using [h0]) (f := fun σ i => (msgB P σ).getD i 0)
    (Inv := fun σ m => K0 h P σ ∧ ∀ i < P.K, i < P.K - P.ml → emV P.scr m i = e4 h P σ i)
    fun σ m m' ⟨k, ho⟩ hf' => ?_).mono
    (fun σ s ⟨⟨⟨⟨hc, hi, hf'⟩, he⟩, bx, si, cx, _⟩, _⟩ => ⟨hc, ⟨⟨hi, hf'⟩, fun i hi _ => he i hi⟩, bx, si, cx,
      fun i hi => ?_⟩) fun σ s ⟨hc, ⟨k, ho⟩, hs⟩ => ⟨⟨hc, k⟩, fun i hi => ?_⟩
  · rw [hg.scrA (by oomega)] at hf'
    refine ⟨k, fun i hi hr => ?_⟩
    rw [emV, ← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by oomega) (by oomega) (by oomega) _
        (Region.contains_self _ _)
  · exact ro_byte hc.st (R := P.MSG) (by simp) hi
  · simp only [e5]
    by_cases hr : P.K - P.ml ≤ i ∧ i < P.K
    · rw [ite_eq_left hr, emV, show oEm + i = oEm + (P.K - P.ml) + (i - (P.K - P.ml)) by oomega,
        ← hg.byteAt_scr (by oomega)]
      exact hs _ (by omega_using [h0, hi])
    · rw [ite_eq_right hr]; exact ho i hi (by omega_using [hi, hr])

/-! ## `EM` -/

theorem e5_emAt {P : EP} {σ : State} (hf : fits h P) {m : Mem} (he : EMv P m (e5 h P σ)) :
    Proof.RsaOaep.EmAt (emV P.scr m) P.K h.H.D (seedB h P σ) (lhB h P σ) (msgB P σ) P.ml := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · rw [he 0 (by omega_using [hfit])]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega_using [hfit]), ite_eq_right (by omega_using [hfit]), ite_eq_right (by omega_using []), ite_eq_right (by omega_using [])]
  · rw [he _ (by omega_using [hfit, hi])]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega_using [hfit, hi]), ite_eq_right (by omega_using [hfit, hi]), ite_eq_right (by omega_using [hi]), ite_eq_left (by omega_using [hi]),
      Nat.add_sub_cancel_left]
  · rw [he _ (by omega_using [hfit, hi])]; simp only [e5, e4, e3]
    rw [ite_eq_right (by omega_using [hfit, hi]), ite_eq_right (by omega_using [hfit, hi]), ite_eq_left (by omega_using [hi]),
      show 1 + h.H.D + i - (1 + h.H.D) = i by omega_using []]
  · rw [he _ (by omega_using [h2])]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega_using [h2]), ite_eq_right (by omega_using [h2]), ite_eq_right (by omega_using [h1]), ite_eq_right (by omega_using [h1])]
  · rw [he _ (by omega_using [hfit])]; simp only [e5, e4]
    rw [ite_eq_right (by omega_using [hfit])]; exact ite_eq_left trivial
  · rw [he _ (by omega_using [hfit, hi])]; simp only [e5]
    rw [ite_eq_left (by omega_using [hfit, hi]), show P.K - P.ml + i - (P.K - P.ml) = i by omega_using []]

/-- `EM` before masking, from the checks' state when the message fits, with
the label's hash function `h`, that of the table `hash`. -/
theorem em_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => E0 h P σ s ∧ s.syms = σ.syms) (encEm h.H f)
      (fun σ s => (E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml) ∧ s.syms = σ.syms) := by
  show VP _ (.seq (.block clrEm) (.seq zeroLoop (.seq (.block (seedSet h.H))
    (.seq Impl.Bignum.X86.copyBytes (.seq (.block (tabSlot 16)) (.seq (hashLabelT f 6 oDig) (.seq (.block (lhSet h.H))
      (.seq Impl.Bignum.X86.copyBytes (.seq (.block msgPos) (.seq (.block put1)
        (.ite .e (.block []) Impl.Bignum.X86.copyBytes))))))))))) _
  exact vpAssoc (VP.seq (VP.syms (em1_vp h P)) (vpAssoc (VP.seq (VP.syms (em2_vp h P))
    (vpAssoc (VP.seq (em3_vp h P hTL fne)
    (vpAssoc (VP.seq (VP.syms (em4_vp h P)) (vpAssoc (VP.seq (VP.syms (em5_vp h P)) ((VP.syms (em6_vp h P)).mono
      (fun _ _ h => h) fun σ s ⟨⟨he0, he⟩, sy⟩ => ⟨⟨he0, e5_emAt h he0.2.2 he⟩, sy⟩))))))))))

end VG.Proof.RsaOaep.X86.Enc

end

end


/-!
# RSAES-OAEP encryption with a precomputed public key on x86: `EM` masked

As on ARMv7 (`Proof/RsaOaep/Arm/EncMask.lean`): `DB` (after the seed)
masked with MGF1 of the seed, then the seed with MGF1 of the masked `DB`
(`mgf_vp`, with the slots that `dbArgs` and `seedArgs` set, `MgfSlots.lean`):
`EM = Proof.RsaOaep.emOf …` (`mask_vp`), with MGF1's hash function the
table that is the argument 15 (`tbl_of`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sCtr sDone)

variable (h g : OHash)

/-! ## The pieces -/

/-- `DB` before masking. -/
abbrev dbB (P : EP) (σ : State) : List Byte :=
  lhB h P σ ++ Spec.RsaOaep.zeros (P.K - P.ml - 2 * h.H.D - 2) ++ 0x01 :: msgB P σ

/-- `DB` masked. -/
abbrev mdbB (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.xorBytes (dbB h P σ) (Spec.Mgf1.mgf1 g.G (seedB h P σ) (P.K - h.H.D - 1))

/-- What the masking keeps: `EM`'s first byte, zero. -/
abbrev X0 (P : EP) (σ : State) (m : Mem) : Prop := K0 h P σ ∧ emV P.scr m 0 = 0

theorem lhB_length (P : EP) (σ : State) : (lhB h P σ).length = h.H.D := by
  rw [lhB, h.valid.2, h.glen]

theorem seedB_length (P : EP) (σ : State) : (seedB h P σ).length = h.H.D := RsaPkcs1Sig.bytesAt_len _ _ _

theorem dbB_length {P : EP} (hf : fits h P) (σ : State) : (dbB h P σ).length = P.K - h.H.D - 1 := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  simp only [dbB, List.length_append, List.length_cons, lhB_length, msgB_length, Spec.RsaOaep.zeros,
    List.length_replicate]
  omega_using [hfit]

theorem mdbB_length {P : EP} (hf : fits h P) (σ : State) : (mdbB h g P σ).length = P.K - h.H.D - 1 := by
  rw [mdbB, Proof.Mgf1.xorBytes_length, dbB_length h hf, Proof.Mgf1.mgf1_length g.valid]; omega_using []

theorem x0_keep {P : EP} (hg : Geo (P.lay h.H.D) P.scr) {dOff dl : Nat} (hfd : dOff + dl ≤ oBuf)
    (h0 : oEm + 1 ≤ dOff) :
    ∀ σ m m', X0 h P σ m → Frame (mgfW g (P.lay h.H.D) P.scr dOff dl) m m' → X0 h P σ m' :=
  fun _ _ _ ⟨k, z⟩ hf => ⟨k, by
    rw [emV, ← z]
    exact hf _ fun r hr => mgfW_byte g hg hfd (o := oEm + 0) (by oomega) (by oomega) (by omega_using [h0]) r hr _
      (Region.contains_self _ _)⟩

/-- Four slots written, and the memory around them. -/
theorem slots4 {P : EP} {σ s t : State} (hc : Ctx (P.lay h.H.D) P.scr σ s) (hg : Geo (P.lay h.H.D) P.scr)
    {v1 v2 v3 v4 : BitVec 32}
    (m : t.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) v1).writeW ((P.lay h.H.D).fr sDstLen) v2).writeW
      ((P.lay h.H.D).fr sSrc) v3).writeW ((P.lay h.H.D).fr sSrcLen) v4)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) :
    Ctx (P.lay h.H.D) P.scr σ t ∧
      Frame [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen, slotR (P.lay h.H.D) sSrc,
        slotR (P.lay h.H.D) sSrcLen] s.mem t.mem ∧
      t.mem.readW ((P.lay h.H.D).fr sSrc) 32 = v3 ∧ t.mem.readW ((P.lay h.H.D).fr sSrcLen) 32 = v4 ∧
      t.mem.readW ((P.lay h.H.D).fr sDst) 32 = v1 ∧ t.mem.readW ((P.lay h.H.D).fr sDstLen) 32 = v2 := by
  obtain fr : Frame [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen, slotR (P.lay h.H.D) sSrc,
      slotR (P.lay h.H.D) sSrcLen] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, fr, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · rw [m, Lay.readW_fr_other (d := sSrc) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDst) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sDstLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDstLen) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDstLen) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]

/-- The slots' frame misses our part of `scratch`. -/
theorem slots4_dis {P : EP} (hg : Geo (P.lay h.H.D) P.scr) :
    ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen,
      slotR (P.lay h.H.D) sSrc, slotR (P.lay h.H.D) sSrcLen], (sR P.scr o n).Disjoint r := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro o n hon r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm

/-- The slots for masking `DB` with the seed. -/
theorem db_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml)
      (.block (dbArgs h.H 3))
      (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = (dbB h P σ).getD i 0) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0) := by
  refine VP.taint [.esp, .ebp] h.certs.dbArgs3 (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hi, hf⟩, em⟩ => ?_
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  simp only [dbArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_subi fun t5 u5 _ _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (by decide) fun t6 c6 m6 => ?_
  refine wp_mov fun t7 u7 => wp_addi fun t8 u8 => ?_
  refine ((c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)).wp_st hg (by decide) fun t9 c9 m9 => ?_
  refine wp_movi fun t10 u10 => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  obtain e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by rw [u2.gpr, u1.gpr, hc.ebp]
  obtain e5 : t5.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u5.gpr, u4.gpr]; show BitVec.ofNat 32 P.K - BitVec.ofNat 32 (h.H.D + 1) = _
    rw [sub_ofNat (by omega_using [hfit]), Nat.sub_add_eq]
  obtain e8 : t8.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by
    rw [u8.gpr, u7.gpr, m6.gpr, u5.other _ (by decide), u4.other _ (by decide), m3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), hc.ebp]
  obtain m11 : t11.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW
      ((P.lay h.H.D).fr sDstLen) (BitVec.ofNat 32 (P.K - h.H.D - 1))).writeW ((P.lay h.H.D).fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW ((P.lay h.H.D).fr sSrcLen) (BitVec.ofNat 32 h.H.D) := by
    rw [m11.mem, u10.gpr, u10.mem, m9.mem, e8, u8.mem, u7.mem, m6.mem, e5, u5.mem, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 h hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  obtain dis := slots4_dis h hg
  obtain db := em.db (lhB_length h P σ) (msgB_length P σ) hfit
  refine ⟨c, ⟨⟨⟨hi, hf⟩, ?_⟩, r1, r2, r3, r4⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · rw [emV, ← em.z0]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm) (n := 1) (f := fun _ => s.mem (sa P.scr oEm))
      (fun i hi => by rw [show i = 0 by omega_using [hi], Nat.add_zero]) 0 (by decide)
  · rw [← db i hi', emV, show oEm + (1 + h.H.D + i) = oEm + 1 + h.H.D + i by oomega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1 + h.H.D) (n := P.K - h.H.D - 1)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + h.H.D + i))) (fun _ _ => rfl) i hi'
  · rw [← em.sd i hi', emV, show oEm + (1 + i) = oEm + 1 + i by oomega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1) (n := h.H.D)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + i))) (fun _ _ => rfl) i hi'

/-- The slots for masking the seed with the masked `DB`. -/
theorem seed_vp (P : EP) :
    VP (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (dbB h P σ).getD i 0 ^^^ (Spec.Mgf1.mgf1 g.G (seedB h P σ) (P.K - h.H.D - 1)).getD i 0) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0)
      (.block (seedArgs h.H 3))
      (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = (mdbB h g P σ).getD i 0) := by
  refine VP.taint [.esp, .ebp] h.certs.seedArgs3 (sp_bp fun _ _ h => h.1)
    fun σ s ⟨hc, ⟨⟨⟨hi, hf⟩, z0⟩, _⟩, hdb, hsd⟩ => ?_
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  simp only [seedArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (by decide) fun t5 c5 m5 => ?_
  refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => ?_
  refine ((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).wp_st hg (by decide) fun t8 c8 m8 => ?_
  refine c8.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t9 c9 u9 => ?_
  refine wp_subi fun t10 u10 _ _ => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  obtain e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by rw [u2.gpr, u1.gpr, hc.ebp]
  obtain e7 : t7.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by
    rw [u7.gpr, u6.gpr, m5.gpr, u4.other _ (by decide), m3.gpr, u2.other _ (by decide), u1.other _ (by decide),
      hc.ebp]
  obtain e10 : t10.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u10.gpr, u9.gpr]; show BitVec.ofNat 32 P.K - BitVec.ofNat 32 (h.H.D + 1) = _
    rw [sub_ofNat (by omega_using [hfit]), Nat.sub_add_eq]
  obtain m11 : t11.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW
      ((P.lay h.H.D).fr sDstLen) (BitVec.ofNat 32 h.H.D)).writeW ((P.lay h.H.D).fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW ((P.lay h.H.D).fr sSrcLen)
          (BitVec.ofNat 32 (P.K - h.H.D - 1)) := by
    rw [m11.mem, e10, u10.mem, u9.mem, m8.mem, e7, u7.mem, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 h hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  obtain dis := slots4_dis h hg
  obtain hdl := dbB_length h hf σ
  obtain hml := Proof.Mgf1.mgf1_length g.valid (seedB h P σ) (P.K - h.H.D - 1)
  refine ⟨c, ⟨⟨⟨hi, hf⟩, ?_⟩, r1, r2, r3, r4⟩, sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hsd, fun i hi' => ?_⟩
  · rw [emV, ← z0]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm) (n := 1) (f := fun _ => s.mem (sa P.scr oEm))
      (fun i hi => by rw [show i = 0 by omega_using [hi], Nat.add_zero]) 0 (by decide)
  · rw [mdbB, Proof.Mgf1.xorBytes_getD (by omega_using [hdl, hi']) (by omega_using [hml, hi'])]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hdb i hi'

/-! ## `EM` masked -/

/-- `EM` masked, as the specification has it. -/
abbrev emB (P : EP) (σ : State) : List Byte :=
  Proof.RsaOaep.emOf g.G h.H.D P.K P.ml (seedB h P σ) (lhB h P σ) (msgB P σ)

/-- A state of the body with `EM` masked at `scratch + oEm`. -/
abbrev E1 (P : EP) (σ s : State) : Prop :=
  E0 h P σ s ∧ ∀ i < P.K, emV P.scr s.mem i = (emB h g P σ).getD i 0

/-- `EM` masked, byte by byte. -/
theorem emB_getD {P : EP} (hf : fits h P) (σ : State) {i : Nat} (hi : i < P.K) :
    (emB h g P σ).getD i 0 = if i = 0 then 0 else if i < 1 + h.H.D then
      (seedB h P σ).getD (i - 1) 0 ^^^ (Spec.Mgf1.mgf1 g.G (mdbB h g P σ) h.H.D).getD (i - 1) 0
      else (mdbB h g P σ).getD (i - 1 - h.H.D) 0 := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  obtain hsl := seedB_length h P σ
  obtain hml := Proof.Mgf1.mgf1_length g.valid (mdbB h g P σ) h.H.D
  show (0 :: (Spec.Mgf1.xorBytes (seedB h P σ) (Spec.Mgf1.mgf1 g.G (mdbB h g P σ) h.H.D) ++ mdbB h g P σ)).getD i 0 = _
  cases i with
  | zero => rfl
  | succ i =>
    rw [List.getD_cons_succ, ite_eq_right (by omega_using []), Proof.Mgf1.getD_append, Proof.Mgf1.xorBytes_length, hsl, hml,
      Nat.min_self, Nat.add_sub_cancel]
    by_cases h1 : i < h.H.D
    · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1]), Proof.Mgf1.xorBytes_getD (by omega_using [hsl, h1]) (by omega_using [hml, h1])]
    · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1])]

/-- MGF1's table, the argument 17, in a buffer only read. -/
theorem tbl_of {D : Nat} {P : EP} {σ : State} (hi : In D P σ) :
    ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (VG.X86.addr ((P.lay D).argv.getD 17 0) o) 4 := by
  obtain hf := hi.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tab.isLt; omega_using [])] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨P.tab.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tab o) 4
  rw [addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- `EM` masked, from `EM` before masking, then `k`, with MGF1's hash
function `g`, whose functions the table reaches (`hT`). -/
theorem mask_vp (P : EP) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) {c : Prog isa} {Q : State → State → Prop}
    (k : VP (fun σ s => E1 h g P σ s ∧ s.syms = σ.syms) c Q) :
    VP (fun σ s => (E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml) ∧ s.syms = σ.syms)
      (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor f 17) (.seq (.block (seedArgs h.H 3)) (.seq (mgfXor f 17) c))))
      Q := by
  by_cases hP : ∃ σ, In h.H.D P σ ∧ fits h P
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1, hs.1.1.2.2⟩
  obtain ⟨σ₀, hi₀, hf⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  obtain tab : ∀ σ m, X0 h P σ m → TabFacts g.H f ((P.lay h.H.D).argv.getD 17 0) P.ai P.au P.af σ :=
    fun σ m hx => hT σ hx.1.1.tabT
  obtain P1 := mpOf g hg (so := oEm + 1) (sl := h.H.D) (dOff := oEm + 1 + h.H.D) (dl := P.K - h.H.D - 1) hD0
    (by omega_using [hfit]) (by oomega) (by oomega) (by oomega) (by oomega) (.inl (Nat.le_refl _)) (seed := seedB h P)
    (seedB_length h P) (x0_keep h g hg (by oomega) (by oomega)) (by simp) (tbl_of hi₀) tabArg17_taint tab fne
  obtain P2 := mpOf g hg (so := oEm + 1 + h.H.D) (sl := P.K - h.H.D - 1) (dOff := oEm + 1) (dl := h.H.D)
    (by omega_using [hfit]) hD0 (by oomega) (by oomega) (by oomega) (by oomega) (.inr (Nat.le_refl _)) (seed := mdbB h g P)
    (mdbB_length h g hf) (x0_keep h g hg (by oomega) (by oomega)) (by simp) (tbl_of hi₀) tabArg17_taint tab fne
  refine VP.seq (VP.syms (db_vp h P)) (VP.seq (mgf_vp g P1 (dstv := fun σ i => (dbB h P σ).getD i 0))
    (VP.seq (VP.syms (seed_vp h g P)) (VP.seq ((mgf_vp g P2 (dstv := fun σ i => (seedB h P σ).getD i 0)).mono
      (fun _ _ hh => hh) fun σ s ⟨⟨hc, ⟨⟨⟨hi, _⟩, z0⟩, _⟩, hsd, hdb⟩, sy⟩ => ⟨⟨⟨hc, hi, hf⟩, fun i hi' => ?_⟩, sy⟩)
      k)))
  rw [emB_getD h g hf σ hi']
  by_cases h0 : i = 0
  · rw [ite_eq_left h0, h0]; exact z0
  rw [ite_eq_right h0]
  by_cases h1 : i < 1 + h.H.D
  · rw [ite_eq_left h1, emV, show oEm + i = oEm + 1 + (i - 1) by oomega]
    exact hsd _ (by omega_using [hD0, h1])
  · rw [ite_eq_right h1, emV, show oEm + i = oEm + 1 + h.H.D + (i - 1 - h.H.D) by oomega]
    exact hdb _ (by omega_using [hfit, hi'])

end VG.Proof.RsaOaep.X86.Enc

end

end


/-!
# RSAES-OAEP encryption with a precomputed public key on x86: the call

As on ARMv7 (`Proof/RsaOaep/Arm/EncCall.lean`): the ten arguments of
`vg_rsa_public_precomputed_checked`, one word of the frame at a time
(`pa_vp`): `out`, `pre`, `e`, `EM` (`k` bytes at `scratch + oEm`) as the
input, and the rest of `scratch` from `oRsa` on; the call (`call_vp`,
correct and constant time: its arguments and the public data it reads are
the same in two runs), which writes the public operation of the masked
`EM`, that is the encryption (`encrypt_some`), to `out`, or zeros.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st atS addi copyArg)

variable (h g : OHash)

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  pubArgv P.out P.pre P.e (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K P.rl P.el (P.scl - 1024)

/-- The first `k` of them in the frame. -/
def Slots (D : Nat) (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW ((P.lay D).fr (4 * i)) 32 = (outv P).getD i 0

/-- During the call's arguments. -/
abbrev A0 (P : EP) (σ s : State) (k : Nat) : Prop := E1 h g P σ s ∧ Slots h.H.D P s.mem k

theorem slots_next {D : Nat} {P : EP} {m : Mem} {i : Nat} (hs : Slots D P m i) (hi : i < 10) (v : BitVec 32)
    (hv : v = (outv P).getD i 0) : Slots D P (m.writeW ((P.lay D).fr (4 * i)) v) (i + 1) := by
  intro k hk
  rcases (by omega_arith : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hs k hki

/-- A word stored in the frame keeps `EM`. -/
theorem keepE1 {P : EP} {σ s t : State} (he : E1 h g P σ s) {i : Nat} {v : BitVec 32} (hi : i < 10)
    (ct : Ctx (P.lay h.H.D) P.scr σ t) (m : t.mem = s.mem.writeW ((P.lay h.H.D).fr (4 * i)) v) :
    E1 h g P σ t := by
  obtain ⟨⟨_, hin, hf⟩, hx⟩ := he
  have hg := hin.geo
  have hK := hin.k1024
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨⟨ct, hin, hf⟩, sbytes_keep (o := oEm) (n := P.K) (by rw [m]; exact slot_frame _ _ _ _) (fun r hr => ?_)
    (by oomega) hx⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact (hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes; omega_arith)).symm

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {P : EP} {σ s : State} {i j : Nat} (ha : A0 h g P σ s i) (hi : i < 10)
    (hj : j < 18) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h g P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  obtain ⟨he, hs⟩ := ha
  have hc := he.1.1
  have hg := he.1.2.1.geo
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine hc.wp_arg hg (enc_arg hj) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega_arith) fun t2 c2 m2 => kk t2 ⟨?_, ?_⟩
  · exact keepE1 h g he hi c2 (by rw [m2.mem, u1.mem])
  · rw [m2.mem, u1.mem, u1.gpr]
    exact slots_next hs hi _ hv

/-- `scratch + o` to the call's argument `i`. -/
theorem scrSlot {P : EP} {σ s : State} {i o : Nat} (ha : A0 h g P σ s i) (hi : i < 10)
    (hv : P.scr + BitVec.ofNat 32 o = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h g P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (atS .eax o ++ [st .eax (4 * i)] ++ is)) s Q := by
  obtain ⟨he, hs⟩ := ha
  have hc := he.1.1
  have hg := he.1.2.1.geo
  simp only [atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (d := 4 * i)
    (by unfold frameBytes; omega_arith) fun t3 c3 m3 => kk t3 ⟨?_, ?_⟩
  · exact keepE1 h g he hi c3 (by rw [m3.mem, u2.mem, u1.mem])
  · rw [m3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp]
    exact slots_next hs hi _ hv

theorem pubArgs_eq : pubArgs = copyArg 0 0 ++ copyArg 3 1 ++ copyArg 14 2 ++ copyArg 15 3 ++ copyArg 4 4 ++
    copyArg 5 5 ++ (atS .eax oEm ++ [st .eax (4 * 6)]) ++ copyArg 3 7 ++ (atS .eax oRsa ++ [st .eax (4 * 8)]) ++
    [ld .eax (arg 13), .alu .sub .eax (.imm 1024), st .eax (4 * 9)] := by
  simp only [pubArgs, List.append_assoc]; rfl

/-- Before the call. -/
abbrev V1 (P : EP) (σ s : State) : Prop :=
  E1 h g P σ s ∧ PubArgs s P.out P.pre P.e (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K P.rl
    P.el (P.scl - 1024)

theorem pa_vp (P : EP) : VP (E1 h g P) (.block pubArgs) (V1 h g P) := by
  refine VP.taint [.esp, .ebp] pubArgs_taint (sp_bp fun _ _ h => h.1.1) fun σ s hm => ?_
  have hi := hm.1.2.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hs1 := hi.pubScr
  rw [pubArgs_eq]
  simp only [List.append_assoc]
  obtain z0 : A0 h g P σ s 0 := ⟨hm, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  refine copySlot h g z0 (by decide) (j := 0) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t1 z1 => ?_
  refine copySlot h g z1 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t2 z2 => ?_
  refine copySlot h g z2 (by decide) (j := 14) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t3 z3 => ?_
  refine copySlot h g z3 (by decide) (j := 15) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t4 z4 => ?_
  refine copySlot h g z4 (by decide) (j := 4) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t5 z5 => ?_
  refine copySlot h g z5 (by decide) (j := 5) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t6 z6 => ?_
  rw [← List.append_assoc (atS .eax oEm)]
  refine scrSlot h g z6 (by decide) (by simp [outv, pubArgv]) fun t7 z7 => ?_
  refine copySlot h g z7 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t8 z8 => ?_
  rw [← List.append_assoc (atS .eax oRsa)]
  refine scrSlot h g z8 (by decide) (by simp [outv, pubArgv]) fun t9 z9 => ?_
  obtain ⟨e9, s9⟩ := z9
  have c9 := e9.1.1
  simp only [ld, st]
  refine c9.wp_arg hg (enc_arg (j := 13) (by decide)) (by decide) (by decide) fun t10 c10 u10 =>
    wp_subi fun t11 u11 _ _ => (c10.upd u11 (by decide) (by decide)).wp_st hg (d := 4 * 9) (by decide)
      fun t12 c12 m12 => WP.block_nil ?_
  obtain v : t11.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u11.gpr, u10.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) (by omega_arith)
  obtain m : t12.mem = t9.mem.writeW ((P.lay h.H.D).fr (4 * 9)) (t11.gpr .eax) := by
    rw [m12.mem, u11.mem, u10.mem]
  obtain sl := slots_next s9 (by decide) _ (v.trans (by simp [outv, pubArgv]))
  rw [← m] at sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨keepE1 h g e9 (i := 9) (by decide) c12 m, fun i hi' => ?_,
    by rw [c12.st.sp]; have : 100 ≤ P.B.toNat := ok.BC; show 100 ≤ P.B.toNat; omega_arith,
    by rw [c12.st.sp]; show P.B.toNat + 40 ≤ _; omega_arith, hi.kv, hi.rlK, hi.el1, hi.elK, hs1.1,
    by have := hi.scl32; omega_arith⟩
  rw [c12.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega_arith)]
  exact sl i hi'

/-! ## The call -/

/-- `EM` and the call's working space, in `scratch`. -/
abbrev emR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oEm).setWidth 64, P.K⟩
abbrev scrR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oRsa).setWidth 64, (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In h.H.D P σ) :
    (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm ∧
    (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa ∧
    Region.Sub (emR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (emR P).Disjoint (scrR P) ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1025 ≤ P.scl ∧ P.K ≤ 1024 := by
  obtain hf := hi.ok.fits P.SCR (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_arith)] at hf
  have hs := hi.pubScr.2
  have hK := hi.k1024
  obtain e1 : (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm :=
    addr_eq (by unfold oEm; omega_arith)
  obtain e2 : (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa :=
    addr_eq (by unfold oRsa; omega_arith)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, hs, hK⟩
  · rw [emR, e1]; exact Offset.sub_base _ (by unfold oEm; omega_arith)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega_arith)
  · rw [emR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega_arith) (by unfold oEm; omega_arith)
      (by unfold oRsa; omega_arith)

theorem eB_at {P : EP} {σ s : State} (hi : In h.H.D P σ) (hs : (P.lay h.H.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- `pre`'s words, in a state of the body. -/
theorem pw_at {P : EP} {σ s : State} (hi : In h.H.D P σ) (hs : (P.lay h.H.D).St σ s) :
    Spec.Rsa.wordsAt s.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hi.ok
  obtain hR : P.PRE ∈ (P.lay h.H.D).ro := by simp
  obtain hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' hs.frame (fun r hr => ?_) (by omega_arith)).trans hi.pw
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    false_or] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (ok.wro P.OUT (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact (ok.wro P.SCR (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- `pre`'s words, in a callee's entry state. -/
theorem callPw {P : EP} {σ s : State} (hi : In h.H.D P σ) (hs : (P.lay h.H.D).St σ s) :
    Spec.Rsa.wordsAt s.callEntry.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hi.ok
  obtain hR : P.PRE ∈ (P.lay h.H.D).ro := by simp
  obtain hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' (hs.callEntry_frame (by show 4 ≤ 100; decide)) (fun r hr => ?_)
    (by omega_arith)).trans (pw_at h hi hs)
  simp only [List.mem_singleton] at hr; subst hr
  exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

theorem emB_length {P : EP} (hf : fits h P) (σ : State) : (emB h g P σ).length = P.K := by
  have hf' : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  obtain hl := lhB_length h P σ
  simp only [emB, Proof.RsaOaep.emOf, List.length_cons, List.length_append, Proof.Mgf1.xorBytes_length,
    Proof.Mgf1.mgf1_length g.valid, hl, Spec.RsaOaep.zeros, List.length_replicate, seedB, RsaPkcs1Sig.bytesAt_len]
  omega_arith

/-- The masked `EM`, as the call reads it. -/
theorem em_bytes {P : EP} {σ s : State} (hr : E1 h g P σ s) :
    Spec.Rsa.bytesAt s.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K = emB h g P σ := by
  obtain ⟨⟨-, hi, hf⟩, he⟩ := hr
  have hg := hi.geo
  have hK := hi.k1024
  obtain hl := emB_length h g hf σ
  rw [← hl]
  refine RsaPkcs1Sig.bytesAt_eq fun i hi' => ?_
  rw [hg.scrA (by oomega), sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact he i (by omega_arith)

/-- The result: the encryption. -/
theorem res_of {P : EP} {σ : State} (hi : In h.H.D P σ) (hf : fits h P) :
    Spec.Rsa.publicOpChecked P.nB P.eB (emB h g P σ) =
      Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ) (seedB h P σ) := by
  have hf' : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  rw [Proof.RsaOaep.encrypt_some (by rw [h.glen]; exact RsaPkcs1Sig.bytesAt_len _ _ _)
    (by rw [h.glen, nB_length hi, msgB_length]; exact hf'), nB_length hi, msgB_length, h.glen]

theorem call_vp (P : EP) (c : Ver.PublicImpl) : VP (V1 h g P) (.call c.name c.code) (Fin h g P) := by
  refine VP.call c.verified.1 c.verified.2.1 c.noSp
    (pubRd P.pre P.e (P.scr + BitVec.ofNat 32 oEm) P.K P.rl P.el)
    (pubWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ s hr => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' hr rd wr cs fr po => ?_)
  · -- The callee's precondition.
    obtain ⟨⟨⟨hc, hi, -⟩, -⟩, pa⟩ := hr
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have fit := ok.fit
    simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at fit
    obtain dOS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
    obtain args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.H.D).fr 0, 40⟩ := by simp
    have hsp := hc.st.sp
    rw [show (P.lay h.H.D).B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    refine pub_pre pa ?_ ?_ ?_ ?_
    · intro w hw r hr
      simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (r := P.PRE) (by simp) (by simp)
      · exact ok.rw_ro (w := P.OUT) (r := P.E) (by simp) (by simp)
      · exact dOS.sub_right sI
      · exact (ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
      · exact dIS.symm
      all_goals rw [args0]
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)).sub_right sI
    · simp only [pubWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨dOS.sub_right sS', ?_⟩, ?_⟩
      · rw [args0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)).symm
      · rw [args0]; exact ⟨((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 40 ≤ frameBytes + 16; decide)).symm).sub_left sS', fun _ h => h.elim⟩
    · intro r hr
      obtain low : Region.Sub (below P.B 100) (P.lay h.H.D).LOW := by
        rw [← ok.low_eq]; exact below_sub (show 100 ≤ 100 by decide) ok.BC
      rw [hsp]
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (ok.low_buf (R := P.OUT) (.inr (by simp))).sub_left low
      · exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS').sub_left low
      · rw [args0]; exact ((Lay.fr_low (by omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)).symm).sub_left low
      · exact (ok.low_buf (R := P.PRE) (.inl (by simp))).sub_left low
      · exact (ok.low_buf (R := P.E) (.inl (by simp))).sub_left low
      · exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI).sub_left low
    · intro r hr
      have hg := hi.geo
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits _ (by simp)
      · show ((P.scr + BitVec.ofNat 32 oRsa).setWidth 64).toNat + (P.scl - 1024) * 8 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega_arith),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega_arith
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 40 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_arith)]
        omega_arith
      · exact ok.fits _ (by simp)
      · exact ok.fits _ (by simp)
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega_arith),
          hg.scr_lt (by decide)]
        unfold oEm; omega_arith
  · -- What the callee is given is ours.
    obtain ⟨⟨⟨hc, hi, -⟩, -⟩, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    obtain hro : ∀ R ∈ (P.lay h.H.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    obtain inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega_arith)⟩
    obtain hA : Covers [⟨P.B.setWidth 64, 40⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 40) (by simp only [frameBytes]; omega_arith)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    obtain hO : Covers [P.OUT] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.inRw (by simp)
    obtain wr : Covers (pubWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      hO.cons ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega_arith)).cons
        (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    exact (hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons
      ((show Covers [emR P] s.wr by rw [emR, e1]; exact inS (by unfold oEm; omega_arith)).right.cons Covers.nil))
  · rw [hr.1.1.1.st.sp]
    have : 100 ≤ P.B.toNat := hr.1.1.2.1.ok.BC
    have := c.stack
    show _ ≤ P.B.toNat
    omega_arith
  · refine pub_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [pw_at h h₁.1.1.2.1 h₁.1.1.1.st, pw_at h h₂.1.1.2.1 h₂.1.1.1.st]
    · rw [eB_at h h₁.1.1.2.1 h₁.1.1.1.st, eB_at h h₂.1.1.2.1 h₂.1.1.1.st]
    · have ok := h₁.1.1.2.1.ok
      rw [h₁.1.1.1.st.sp]
      exact (ok.low_buf (R := P.PRE) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 100 ≤ 100 by decide) ok.BC)
    · have ok := h₁.1.1.2.1.ok
      rw [h₁.1.1.1.st.sp]
      exact (ok.low_buf (R := P.E) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 100 ≤ 100 by decide) ok.BC)
  · -- After the call.
    obtain ⟨he1, pa⟩ := hr
    obtain ⟨⟨hc, hi, hf⟩, he⟩ := he1
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hfit, hs1, hK⟩ := call_geo h hi
    obtain low : Region.Sub (below (s.gpr .esp) (stackUse c.code + 4)) (P.lay h.H.D).LOW := by
      rw [hsp, ← ok.low_eq]
      exact below_sub (by have := c.stack; show _ ≤ 100; omega_arith) ok.BC
    obtain args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.H.D).fr 0, 40⟩ := by simp
    obtain hw : ∀ r ∈ pubWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024) ++
        [below (s.gpr .esp) (stackUse c.code + 4)], ∃ R ∈ (P.lay h.H.D).W, Region.Sub r R := fun r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨(P.lay h.H.D).FR, by simp, ?_⟩
        rw [args0]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨(P.lay h.H.D).LOW, by simp, low⟩
    obtain st : (P.lay h.H.D).St σ s' := hs.write fr hw rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hi, st⟩, fun hp => ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := pub_post pa po P.nB (nB_length hi) (by rw [callPw h hi hs]; exact hp)
    rw [m₂, g₂ .eax (by decide)] at this
    obtain eE : Spec.Rsa.bytesAt s.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
      (hs.callEntry_ro (by show 4 ≤ 100; decide) (R := P.E) (by simp)).trans hi.eB
    obtain eM : Spec.Rsa.bytesAt s.callEntry.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K = emB h g P σ := by
      refine (Proof.RsaPkcs1Sig.bytesAt_frame (hs.callEntry_frame (by show 4 ≤ 100; decide)) (fun r hr => ?_)
        (by omega_arith)).trans (em_bytes h g ⟨⟨hc, hi, hf⟩, he⟩)
      simp only [List.mem_singleton] at hr; subst hr
      exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI).symm
    rw [eE, eM, res_of h g hi hf] at this
    exact this

end VG.Proof.RsaOaep.X86.Enc

end

end


/-!
# RSAES-OAEP encryption with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaOaep/Arm/EncBody.lean`, `EncVerified.lean`): the
checks, then zeros to `out` if the message does not fit (`fail_vp`), or
`EM` (`em_vp`), its masks (`mask_vp`) and the call (`pa_vp`, `call_vp`):
`body_vp`. The body writes `esp` only through the frames of its calls
(`body_noSp`); the frames around it (`wrap_ok`, `wrap_ct`) and the result
as the shared contract states it, for MGF1's hash function the variant `w`
whose table the argument 15 is (`tabFacts_entered`):
`vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, calling a precomputed public
operation `c`, with MGF1's hash function any of the tables of `vs`, is
verified, given a state that meets the contract (`Enc/Sat.lean`):
`encrypt_verified`. Every stage keeps the addresses of the statics
(`VP.syms`), which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes seqs countLoop zeroLoop)
open VG.Proof.HashTable.X86 (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered
  fnsOf_noSp)

variable (h : OHash)

/-- A stage, with what follows it, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- After the checks, when the message fits, with the label's hash function
`h` and MGF1's `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : Ver.PublicImpl) :
    VP (Sy (E0 h P)) (encMain h.H f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (encEm h.H f) (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor f 17) (.seq (.block (seedArgs h.H 3))
    (.seq (mgfXor f 17) (.seq (.block pubArgs) (.call c.name c.code))))))) _
  exact (em_vp h P hTL fne).seq (mask_vp h g P hT fne (VP.syms ((pa_vp h g P).seq (call_vp h g P c))))

/-- The digest length of the label's hash function's table to `edx`. -/
theorem len_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ) :
    VP (S h P) (.block (lenLoad 16)) (fun σ s => S h P σ s ∧ s.gpr .edx = BitVec.ofNat 32 h.H.D) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := tblL_of hi₀
  show VP _ (.block ([Impl.RsaPss.X86.ld .edx (Impl.RsaPss.X86.arg 16)] ++
    [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 24))])) _
  refine VP.block_append (G := fun σ s => S h P σ s ∧ s.gpr .edx = P.tabL)
    (VP.taint [.esp] lenArg16_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] lenWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]
  · obtain ⟨hi, hs⟩ := hs
    simp only [Impl.RsaPss.X86.ld, Impl.RsaPkcs1Sig.X86.stk]
    exact hs.wp_arg (enc_arg (j := 16) (by decide)) (by decide) fun t1 s1 u1 =>
      WP.block_nil ⟨⟨hi, s1⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.2.sp, h₂.1.2.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨hi, hs⟩, hdx⟩ := hs
    obtain T := hTL σ hi.tabTL
    obtain hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabL 24) 4 := ⟨tR, hs.inRo tRo, tC 24 (by decide)⟩
    refine wp_ldm (B := P.tabL) hdx hin fun t2 u2 => WP.block_nil ⟨⟨hi, hs.upd u2 (by decide)⟩, ?_⟩
    rw [u2.gpr, St_roW hs tRo (tC 24 (by decide)), T.d]

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem encTail_D {G G' : Impl.Pbkdf2.Stream.X86.Hash} (hD : G.D = G'.D) (f : Fns) (n : String) (c : Prog isa) :
    encTail G f n c = encTail G' f n c := by
  simp only [encTail, encMain, encEm, encChk, seedSet, lhSet, dbArgs, seedArgs, hD]

/-- The body. -/
theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : Ver.PublicImpl) :
    VP (Sy (S h P)) (encBody f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (.block (lenLoad 16)) (byLen (fun d => encTail (ofLen d) f c.name c.code) lens)) _
  refine (VP.syms (len_vp h P hTL)).seq (byLen_vp (D := h.H.D) (by have := h.D_le; omega_using [this]) (fun _ _ hs => hs.1.2)
    (fun σ s t ⟨⟨⟨hi, st⟩, dx⟩, sy⟩ fu sy' => ⟨⟨⟨hi, st.fupd fu⟩, by rw [fu.gpr]; exact dx⟩, sy'.trans sy⟩) ?_
    h.lens cmpLens_taint)
  show VP _ (encTail (ofLen h.H.D) f c.name c.code) _
  rw [encTail_D (G := ofLen h.H.D) (G' := h.H) rfl]
  show VP _ (.seq (.block (encChk h.H)) (.ite .ne encFail (encMain h.H f c.name c.code))) _
  refine ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨s', _⟩, sy⟩ => ⟨s', sy⟩) fun _ _ x => x).seq (VP.ite
    (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.1.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2, h₂.1.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x) ?_)
  refine (main_vp h P g hT hTL fne c).mono (fun σ s ⟨⟨⟨hc, hi, z⟩, sy⟩, e⟩ => ⟨⟨hc, hi, ?_⟩, sy⟩) fun _ _ hh => hh
  simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
  exact e

/-! ## The stack -/

theorem tail_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (cs : OCerts G) {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2)
    (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2) (c : Ver.PublicImpl) :
    NoSp (encTail G f c.name c.code) := by
  obtain ⟨p1, -, p3, -, p5, p6, p7, -⟩ := cs.parts
  obtain hm := mgfX_noSp hi hu hf (j := 17) (NoSp.of_all (by decide +kernel))
  obtain hl := hashLabelT_noSp hi hu hf (j := 6) (o := Impl.RsaPss.X86.oDig) (NoSp.of_all (by decide +kernel))
    (NoSp.of_all (by decide +kernel))
  have hc := c.noSp
  simp only [encTail, encMain, encEm, encFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply RsaPss.X86.noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | exact hm | exact hl | exact hc | exact p1 | exact p3 | exact p5 | exact p6 | exact p7
    | exact NoSp.of_all (by decide +kernel))

theorem body_noSp {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2)
    (c : Ver.PublicImpl) : NoSp (encBody f c.name c.code) :=
  noSp_seq (NoSp.of_all (by decide +kernel))
    (byLen_noSp fun d hd => tail_noSp (ofLen d) (lens_certs hd) hi hu hf c)

/-! ## The entry -/

variable (vs : List TVar)

/-- The code, calling `c`, with both hash functions any of the tables of `vs`. -/
abbrev encryptCode (c : Ver.PublicImpl) : Prog isa := encryptPrecomputed (fnsOf vs) c.name c.code

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev espec : Contract isa := spec (tables vs)

variable {vs}

/-- The public parameters for MGF1's table of `w` and the label's hash
function's of `w₁`, with their functions where `s'` has them. -/
abbrev epw (s s' : State) (w w₁ : TVar) : EP :=
  ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (arg s 17) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
    (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
    (TabFacts w₁.g.H (fnsOf vs) (arg s 16) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN))

theorem spec_sp {s : State} (hs : (espec vs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  enc_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega_using [hsa]⟩

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the tables of `w` at the argument 17 and `w₁` at
16, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (espec vs).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem ((arg s 17).setWidth 64) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem ((arg s 16).setWidth 64) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S w₁.g (epw (vs := vs) s s' w w₁)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tab hs
  obtain hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  obtain hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  obtain hHa := hashAt_tableOf hfitL (held_tableOf hfitL hhL).2.1
  obtain ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs hHa trivial trivial).ok
  rw [ep_lay] at ok
  obtain hn := Proof.HashTable.X86.mem_names hw
  obtain hnL := Proof.HashTable.X86.mem_names hw₁
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 fun _ => True
  obtain tf := tabFacts_entered (argv := e0.argv) (ro := e0.ro w₁.g.G.len) (rw := e0.rw) (C := 100) hsp ok
    (p := arg s 17) (by simp [e0, ep]) hfit hc hpw' hw hh
  obtain tfL := tabFacts_entered (argv := e0.argv) (ro := e0.ro w₁.g.G.len) (rw := e0.rw) (C := 100) hsp ok
    (p := arg s 16) (by simp [e0, ep]) hfitL hc hpw' hw₁ hhL
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  rw [hsy _ hnL.1, hsy _ hnL.2.1, hsy _ hnL.2.2] at tfL
  obtain hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs hHa tf tfL
  rw [w₁.g.glen] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (c : Ver.PublicImpl) {s : State} (hs : (espec vs).pre s) :
    WP isa (encryptCode vs c) s fun t => abiPreserved s t ∧ (espec vs).post s t := by
  obtain ⟨⟨T₁, hT₁, hhL⟩, ⟨T, hT, hh⟩, -, hfitL, hfit⟩ := spec_tab hs
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain hidx := (held_tableOf hfit hh).2.1
  obtain hidxL := (held_tableOf hfitL hhL).2.1
  obtain he := entered_state hc hs hw hw₁ hh hhL (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  obtain hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  obtain hb := (body_vp w₁.g (epw (vs := vs) s s w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) c).wp _ _ he
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp ni nu nf c) hsp hfit4
    (W := ((epw (vs := vs) s s w w₁).lay w₁.g.H.D).W)
    (Q := fun r m => Res w₁.g w.g (epw (vs := vs) s s w w₁) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩) (fun r m m' fl hres => ?_)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (epw (vs := vs) s s w w₁).argv) (ro := (epw (vs := vs) s s w w₁).ro w₁.g.H.D)
        (rw := (epw (vs := vs) s s w w₁).rw) (C := 100) hsp,
      ret_eq (argv := (epw (vs := vs) s s w w₁).argv) (ro := (epw (vs := vs) s s w w₁).ro w₁.g.H.D)
        (rw := (epw (vs := vs) s s w w₁).rw) (C := 100) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    obtain F' := release_frame (argv := (epw (vs := vs) s s w w₁).argv) (ro := (epw (vs := vs) s s w w₁).ro w₁.g.H.D) (rw := (epw (vs := vs) s s w w₁).rw) (C := 100) fl
    unfold Res at hres ⊢
    exact fun h => VG.Proof.Rsa.written_frame F' (by show (arg s 3).toNat < 2 ^ 64; have := (arg s 3).isLt; omega_using [this])
      (fun q hq => by rw [List.mem_singleton.mp hq]; exact (ok.stk (epw (vs := vs) s s w w₁).OUT (by simp [layOf])).symm) (hres h)
  · have ok := hin.ok
    rw [ep_lay] at ok
    obtain ro := fun {R : Region} (hR : R ∈ (epw (vs := vs) s s w w₁).ro w₁.g.H.D) => entered_ro hsp ok hR
    sig_post [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes]
    intro H G hH hG
    rw [hashAt_tableOf hfitL hidxL, Option.some.injEq] at hH
    rw [hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    obtain hL : labB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).LAB) (by simp)
    obtain hM : msgB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).MSG) (by simp)
    obtain hS : seedB w₁.g (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 10).setWidth 64) w₁.g.H.D :=
      ro (R := (epw (vs := vs) s s w w₁).SEED w₁.g.H.D) (by simp)
    rw [hL, hM, hS] at res
    rw [BitVec.setWidth_append_eq_right, w₁.g.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (c : Ver.PublicImpl) :
    ConstantTime isa (espec vs).pre (espec vs).pub (encryptCode vs c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
    a17⟩ := hp
  obtain hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  obtain hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  obtain hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  obtain hep : epw (vs := vs) s₁ s₁ w w₁ = epw (vs := vs) s₂ s₁ w w₁ := by
    obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.bytesAt_len, a3, a5])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [RsaPkcs1Sig.bytesAt_len, a3])
    obtain hw' := map_toNat_inj hw
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17]
    rw [a2, a3] at hn
    rw [a4, a5] at he
    rw [a14, a15] at hw'
    rw [hn, he, hw']
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  refine (wrap_ct (F := frameBytes) (body_noSp ni nu nf c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w₁.g (epw (vs := vs) s₁ s₁ w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) c).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy'⟩

theorem code_noSp (c : Ver.PublicImpl) : NoSp (encryptCode vs c) :=
  have n := fnsOf_noSp vs
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp n.1 n.2.1 n.2.2 c)) restore_noSp)

theorem code_sp (c : Ver.PublicImpl) : (encryptCode vs c).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp c)

/-- `vg_rsa_oaep_encrypt_precomputed`, calling `c`, with both hash functions
any of the tables of `vs`, meets the shared contract (satisfiable,
`Enc/Sat.lean`). -/
theorem encrypt_verified (hc : Coh vs) (hsat : ∃ s, (espec vs).pre s) (c : Ver.PublicImpl) :
    Verified target (encryptCode vs c) (espec vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc c, hsat⟩

end VG.Proof.RsaOaep.X86.Enc

end

end

/-! ### `RsaOaep.X86.Enc.Sat`, which only this module used -/

section

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: the contract is satisfiable

A state that meets `encryptMdTablesContract` (`encrypt_sat`), with both
hash functions' tables that of any variant `w` of `vs`: a modulus of 64 bytes, `e` of one byte, an empty label and
message, the seed, the working space it needs, the precomputed values' 16
words, the arguments above `esp = 0x20000`, and the table at `0x300000`
(`withTable`), for both.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.HashTable.X86 (TVar tables tableOf names withTable withTable_arg withTable_held held_twL hashAt_tableOf held_tableOf)
open VG.Proof.HashTable (symsOf32_distinct2)

/-- The state, for a seed of `D` bytes, but for the tables. -/
def satState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x10 else if a = 131080 then 0x40 else if a = 131085 then 0x20 else if a = 131088 then 0x40 else if a = 131093 then 0x21 else if a = 131096 then 0x1 else if a = 131101 then 0x30 else if a = 131109 then 0x31 else if a = 131117 then 0x32 else if a = 131120 then BitVec.ofNat 8 D else if a = 131126 then 0x1 else if a = 131128 then 0x20 else if a = 131129 then 0x8 else if a = 131133 then 0x70 else if a = 131136 then 0x10 else if a = 131142 then 0x30 else if a = 131146 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, D⟩, ⟨0x7000, 128⟩, ⟨0x300000, 44⟩,
    ⟨0x300000, 44⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 72⟩]

theorem encrypt_sat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (spec (tables vs)).pre s := by
  obtain hha : ∀ s : State, Spec.MdHashTable.hashAt 32 (withTable s vs w).mem ((0x300000 : BitVec 32).setWidth 64) =
      some w.g.G := fun s => hashAt_tableOf (by decide) (held_tableOf (by decide) (withTable_held s vs w)).2.1
  obtain hl' : w.g.G.len ∈ Impl.RsaOaep.X86.lens := w.g.glen ▸ w.g.lens
  generalize hDd : w.g.G.len = D at hl'
  refine ⟨withTable (satState D) vs w, ?_⟩
  obtain hA : ∀ D ∈ Impl.RsaOaep.X86.lens, ∀ j < 18, (argAddr (satState D) j).toNat + 4 ≤ 0x300000 := by decide
  obtain a0 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 0 = 0x1000 by decide) D hl'
  obtain a1 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 1 = 64 by decide) D hl'
  obtain a2 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 2 = 0x2000 by decide) D hl'
  obtain a3 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 3 = 64 by decide) D hl'
  obtain a4 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 4 = 0x2100 by decide) D hl'
  obtain a5 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 5 = 1 by decide) D hl'
  obtain a6 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 6 = 0x3000 by decide) D hl'
  obtain a7 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 7 = 0 by decide) D hl'
  obtain a8 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 8 = 0x3100 by decide) D hl'
  obtain a9 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 9 = 0 by decide) D hl'
  obtain a10 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 10 = 0x3200 by decide) D hl'
  obtain a11 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 11 = BitVec.ofNat 32 D by decide) D hl'
  obtain a12 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 12 = 0x10000 by decide) D hl'
  obtain a13 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 13 = 0x820 by decide) D hl'
  obtain a14 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 14 = 0x7000 by decide) D hl'
  obtain a15 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 15 = 16 by decide) D hl'
  obtain a16 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 16 = 0x300000 by decide) D hl'
  obtain a17 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 17 = 0x300000 by decide) D hl'
  obtain hA' := hA D hl'
  have e : argAddr (withTable (satState D) vs w) 0 = 0x20004 := rfl
  obtain hha' := hha (satState D)
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argSlots, argVal, argBytes, stackBelow]
  simp only [withTable_arg _ vs w (hA' 0 (by decide)), withTable_arg _ vs w (hA' 1 (by decide)),
    withTable_arg _ vs w (hA' 2 (by decide)), withTable_arg _ vs w (hA' 3 (by decide)),
    withTable_arg _ vs w (hA' 4 (by decide)), withTable_arg _ vs w (hA' 5 (by decide)),
    withTable_arg _ vs w (hA' 6 (by decide)), withTable_arg _ vs w (hA' 7 (by decide)),
    withTable_arg _ vs w (hA' 8 (by decide)), withTable_arg _ vs w (hA' 9 (by decide)),
    withTable_arg _ vs w (hA' 10 (by decide)), withTable_arg _ vs w (hA' 11 (by decide)),
    withTable_arg _ vs w (hA' 12 (by decide)), withTable_arg _ vs w (hA' 13 (by decide)),
    withTable_arg _ vs w (hA' 14 (by decide)), withTable_arg _ vs w (hA' 15 (by decide)),
    withTable_arg _ vs w (hA' 16 (by decide)), withTable_arg _ vs w (hA' 17 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13, a14, a15, a16, a17, e]
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals first
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro H' hH'
       obtain rfl := Option.some.inj (hha'.symm.trans hH')
       rw [hDd]; rfl)
    | (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
    | (simp only [Spec.Rsa.lenValid]; decide)
    -- What mentions the seed's length, for each length.
    | (simp only [Impl.RsaOaep.X86.lens, List.mem_cons, List.not_mem_nil, or_false] at hl'
       rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl <;> first
         | rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)
         | (intro H' hH'
            obtain rfl := Option.some.inj (hha'.symm.trans hH')
            rw [hDd]; rfl))

end VG.Proof.RsaOaep.X86.Enc

end

end


/-!
# RSAES-OAEP on x86: the instances emitted

What the registrations check of the variants whose tables a function takes
(`OK`), and the instances' proofs against the contracts the registrations
state, with both hash functions any of the tables: decryption (`dec_ok`,
and `decP_ok` given `pre`) and encryption (`enc_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86
open VG.Proof.HashTable.X86 (TVar tables names Coh)

/-- What the registrations check of the variants whose tables a function
takes: their functions of the same name have the same code, there are not
too many to give distinct addresses in the witnesses, and there is one. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ []

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List TVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs` and the private-key
operation of `c`. -/
theorem dec_ok (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (Dec.decCode vs c) (Dec.dspec vs) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat hw hok.2.1) c

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs` and the
private-key operation of `c` and `w`, given `pre`. -/
theorem decP_ok (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl)
    (w : Proof.Rsa.X86.PrivChecked.CrtPImpl) :
    Verified target (Dec.decCodeP vs c w) (Dec.dspecP vs) :=
  Dec.decP_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_satP hw hok.2.1) c w

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok (vs : List TVar) (hok : OK vs) :
    Verified target (Enc.encryptCode vs RsaPkcs1Sig.X86.Ver.baseline) (Enc.espec vs) :=
  Enc.encrypt_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Enc.encrypt_sat hw hok.2.1) _

end VG.Proof.RsaOaep.X86
