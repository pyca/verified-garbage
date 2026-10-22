module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Chk
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaOaep.X86.Label
import VerifiedGarbage.Proof.RsaOaep.X86.Calls
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: `EM` before masking

As on ARMv7 (`Proof/RsaOaep/Arm/EncEm.lean`): when the message fits, `EM`'s
`k` bytes at `scratch + oEm` cleared, the seed after its first byte, the
label's hash (`label_vp`) after the seed, `0x01` before the message and the
message at its end: `EM = 0x00 ‖ seed ‖ lHash ‖ 0… ‖ 0x01 ‖ M`
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
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by oomega) (by omega)) (by omega) (Inv := fun σ _ => K0 h P σ)
      fun σ m m' hm _ => hm).mono (fun σ s ⟨⟨hc, hm⟩, si, cx, ax⟩ => ⟨hc, hm, si, cx, ax⟩)
      fun σ s ⟨hc, hm, hz⟩ => ⟨⟨hc, hm⟩, fun i hi => by rw [emV, ← hg.byteAt_scr (by oomega)]; exact hz i hi⟩)
  simp only [clrEm, atS, addi, ld, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
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
  have e := congrArg (fun l => l.getD i 0) (hs.ro hR)
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
  have hsd : RBuf (P.lay h.H.D) P.seed h.H.D := by
    have hf := hi₀.ok.fits (P.SEED h.H.D) (by simp)
    simp only [BitVec.toNat_setWidth] at hf
    rw [Nat.mod_eq_of_lt (by have := P.seed.isLt; omega)] at hf
    exact ⟨hf, by omega, ⟨P.SEED h.H.D, by simp, Region.contains_self _ _⟩⟩
  have sep : Region.Disjoint ⟨P.seed.setWidth 64, h.H.D⟩ ⟨(P.scr + BitVec.ofNat 32 (oEm + 1)).setWidth 64, h.H.D⟩ := by
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
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
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
  · rw [ite_eq_left h1, show i = 1 + (i - 1) by omega, sd _ (by omega), Nat.add_sub_cancel_left]
  · rw [ite_eq_right h1]
    by_cases h0 : i = 0
    · subst h0; exact z0
    · exact zr i (by omega) hi

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

/-- The label's hash at `oDig`. -/
theorem em3_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Z2 h P (seedB h P σ) s.mem) (hashLabel h.H 6 oDig)
      (fun σ s => E0 h P σ s ∧ EMv P s.mem (e2 h P σ) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oDig + i)) = (lhB h P σ).getD i 0) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le
  obtain ⟨σ', ok⟩ := hg.ok
  have hl := hi₀.ok.fits P.LAB (by simp)
  simp only [BitVec.toNat_setWidth] at hl
  rw [Nat.mod_eq_of_lt (by have := P.lab.isLt; omega)] at hl
  have hlab : RBuf (P.lay h.H.D) P.lab P.ll := ⟨hl, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  have dS : ∀ {o n : Nat}, o + n ≤ oRsa → Region.Disjoint ⟨P.lab.setWidth 64, P.ll⟩ (sR P.scr o n) :=
    fun hon => (hg.ro ok hon (R := P.LAB) (by simp)).symm
  refine (label_vp hg h (j := 6) (o := oDig) (ll := P.ll) (lab := P.lab) (by simp) updLab6_taint finLab6_taint
    rfl rfl hlab (dS (by oomega)) (dS (by oomega)) (ok.low_buf (R := P.LAB) (.inl (by simp))).symm (by oomega)
    (by oomega) (labB := labB P) (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := fun σ m => K0 h P σ ∧ EMv P m (e2 h P σ)) fun σ m m' ⟨k, he⟩ hf => ⟨k, emv_keep h hg hK hf ?_ he⟩).mono
    (fun σ s ⟨⟨hc, hi, hf⟩, hz⟩ => ⟨hc, ⟨hi, hf⟩, z2_emv h hz⟩)
    fun σ s ⟨hc, ⟨⟨hi, hf⟩, he⟩, hd⟩ => ⟨⟨hc, hi, hf⟩, he, hd⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl ⟨oSt, h.H.S, by oomega, rfl⟩
  · exact .inl ⟨oCW, h.ok.Wb, by oomega, rfl⟩
  · exact .inr rfl
  · exact .inl ⟨oDig, h.H.F, by oomega, rfl⟩

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
  have sp4 : Region.Disjoint ⟨(P.scr + BitVec.ofNat 32 oDig).setWidth 64, h.H.D⟩
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
    have c5 : Ctx (P.lay h.H.D) P.scr σ t5 := ((((hc.upd u1 (by decide) (by decide)).upd u2 (by decide)
      (by decide)).upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)
    have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
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
      exact hb _ (by omega)
    · rw [ite_eq_right hr]; exact ho i hi (by omega)

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
    have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.H.D).B) (by rw [c2.st.sp]) (argR hg c2 (j := 3) (by decide)) fun t3 u3 => ?_
    have c3 := c2.upd u3 (by decide) (by decide)
    refine wp_subm (B := (P.lay h.H.D).B) (by rw [c3.st.sp]) (argR hg c3 (j := 9) (by decide)) fun t4 u4 => ?_
    refine wp_subi fun t5 u5 _ _ => WP.block_nil ⟨⟨⟨(c3.upd u4 (by decide) (by decide)).upd u5 (by decide)
      (by decide), hi, hf'⟩, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact he⟩, ?_⟩
    rw [u5.gpr, u4.gpr, u3.gpr, u3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp, hg.aArg ok 3 (enc_arg (by decide)),
      hg.aArg ok 9 (enc_arg (by decide)), hc.st.arg (enc_arg (by decide)), hc.st.arg (enc_arg (by decide))]
    show P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ml - BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, add_ofNat_sub (by omega), add_ofNat_sub (by oomega)]
    congr 2; oomega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · simp only [put1, mi, addi, ld, Impl.RsaPkcs1Sig.X86.at_]
    refine wp_movi fun t1 u1 => ?_
    have c1 := hc.upd u1 (by decide) (by decide)
    have ad : VG.X86.addr (t1.gpr .ebx) 0 = sa P.scr (oEm + (P.K - P.ml - 1)) := by
      rw [u1.other _ (by decide), bx, hg.addrD (by oomega), Nat.add_zero]
    refine wp_store8 (a := sa P.scr (oEm + (P.K - P.ml - 1))) (by rw [ea_at]; exact ad)
      (by rw [u1.wr]; exact hg.wr hc.st (by oomega)) fun t2 m2 => ?_
    have m2' : t2.mem = s.mem.writeW (sa P.scr (oEm + (P.K - P.ml - 1))) (1 : Byte) := by
      rw [m2.mem, Reg8.reg, u1.gpr, u1.mem]; rfl
    have fr : Frame [sR P.scr (oEm + (P.K - P.ml - 1)) 1] s.mem t2.mem := by
      rw [m2']; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by oomega)
    have c2 : Ctx (P.lay h.H.D) P.scr σ t2 := ctxW hg hc fr (fun r hr => .inl ⟨oEm + (P.K - P.ml - 1), 1, by oomega,
      by simpa using hr⟩) (by rw [m2.rd, u1.rd]) (by rw [m2.wr, u1.wr])
      (by rw [m2.gpr, u1.other _ (by decide)]) (by rw [m2.gpr, u1.other _ (by decide)])
    refine wp_addi fun t3 u3 => ?_
    have c3 := c2.upd u3 (by decide) (by decide)
    refine c3.wp_arg hg (enc_arg (j := 8) (by decide)) (by decide) (by decide) fun t4 c4 u4 =>
      c4.wp_arg hg (enc_arg (j := 9) (by decide)) (by decide) (by decide) fun t5 c5 u5 =>
        wp_test fun t6 f6 z6 => WP.block_nil ⟨⟨⟨c5.fupd f6, hi, hf'⟩, fun i hi' => ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [emV, f6.mem, u5.mem, u4.mem, u3.mem, m2', sa_write P.scr _ _ (by oomega) (by oomega)]
      by_cases e : i = P.K - P.ml - 1
      · rw [ite_eq_left (by omega)]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega)]; exact (he i hi').trans (ite_eq_right e).symm
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
    rw [he i hi]; exact (ite_eq_right (by omega)).symm
  by_cases h0 : P.ml = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
  have hm := hi₀.ok.fits P.MSG (by simp)
  simp only [BitVec.toNat_setWidth] at hm
  rw [Nat.mod_eq_of_lt (by have := P.msg.isLt; omega)] at hm
  have hmsg : RBuf (P.lay h.H.D) P.msg P.ml := ⟨hm, hi₀.ml32, ⟨P.MSG, by simp, Region.contains_self _ _⟩⟩
  refine (copy_vp (hg.wbuf (o := oEm + (P.K - P.ml)) (n := P.ml) (by oomega) (by omega)) hmsg
    (by rw [hg.scrA (by oomega)]; exact (hg.ro ok (by oomega) (R := P.MSG) (by simp)).symm)
    (by omega) (f := fun σ i => (msgB P σ).getD i 0)
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
      exact hs _ (by omega)
    · rw [ite_eq_right hr]; exact ho i hi (by omega)

/-! ## `EM` -/

theorem e5_emAt {P : EP} {σ : State} (hf : fits h P) {m : Mem} (he : EMv P m (e5 h P σ)) :
    Proof.RsaOaep.EmAt (emV P.scr m) P.K h.H.D (seedB h P σ) (lhB h P σ) (msgB P σ) P.ml := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · rw [he 0 (by omega)]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [he _ (by omega)]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  · rw [he _ (by omega)]; simp only [e5, e4, e3]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show 1 + h.H.D + i - (1 + h.H.D) = i by omega]
  · rw [he _ (by omega)]; simp only [e5, e4, e3, e2]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [he _ (by omega)]; simp only [e5, e4]
    rw [ite_eq_right (by omega)]; exact ite_eq_left trivial
  · rw [he _ (by omega)]; simp only [e5]
    rw [ite_eq_left (by omega), show P.K - P.ml + i - (P.K - P.ml) = i by omega]

/-- `EM` before masking, from the checks' state when the message fits. -/
theorem em_vp (P : EP) :
    VP (E0 h P) (encEm h.H)
      (fun σ s => E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml) := by
  show VP _ (.seq (.block clrEm) (.seq zeroLoop (.seq (.block (seedSet h.H))
    (.seq Impl.Bignum.X86.copyBytes (.seq (hashLabel h.H 6 oDig) (.seq (.block (lhSet h.H))
      (.seq Impl.Bignum.X86.copyBytes (.seq (.block msgPos) (.seq (.block put1)
        (.ite .e (.block []) Impl.Bignum.X86.copyBytes)))))))))) _
  exact vpAssoc (VP.seq (em1_vp h P) (vpAssoc (VP.seq (em2_vp h P) (VP.seq (em3_vp h P)
    (vpAssoc (VP.seq (em4_vp h P) (vpAssoc (VP.seq (em5_vp h P) ((em6_vp h P).mono (fun _ _ h => h)
      fun σ s ⟨he0, he⟩ => ⟨he0, e5_emAt h he0.2.2 he⟩)))))))))

end VG.Proof.RsaOaep.X86.Enc
