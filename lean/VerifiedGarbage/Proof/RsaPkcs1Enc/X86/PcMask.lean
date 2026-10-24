module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcTaint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: the masks

After the call, as on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcCall.lean`): the mask
`keep` (all ones unless `PS` had a zero byte), the result masked with it
(`maskArgs_wp`), `out` masked with it one byte at a time (`maskLoop_vp`),
`EM` overwritten with zeros (`wipeArgs_wp`, `zero_wp`), and the result
returned (`ret_wp`): what the function writes and returns (`Res`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- The mask of the result: all ones unless `PS` has a zero byte. -/
abbrev keep (P : EP) (σ : State) : BitVec 32 := zm (psB P σ) ^^^ BitVec.allOnes 32

/-- What the function writes and returns. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (P.out.setWidth 64) P.K r
      (if zm (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none)

/-- `out` with `k` of its bytes left to mask. -/
def MI (P : EP) (k : Nat) (σ s : State) : Prop :=
  S P σ s ∧ k ≤ P.K ∧ s.gpr .esi = P.out + BitVec.ofNat 32 (P.K - k) ∧ s.gpr .ecx = BitVec.ofNat 32 k ∧
    s.gpr .ebx = keep P σ ∧ ∃ m0 rc, CR P σ m0 rc ∧ s.gpr .edi = rc &&& keep P σ ∧
      ∀ i < P.K, s.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) =
        if i < P.K - k then m0 (P.out.setWidth 64 + BitVec.ofNat 64 i) &&& (keep P σ).setWidth 8
        else m0 (P.out.setWidth 64 + BitVec.ofNat 64 i)

/-- `out` masked. -/
def G10 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .edi)

/-- Before the wipe of `EM`. -/
def G11 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ Res P σ s.mem (s.gpr .edi) ∧ s.gpr .esi = P.B + BitVec.ofNat 32 oEM ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

/-- The end of the body. -/
def G13 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .eax)

theorem zm_cases (bs : List Byte) : zm bs = 0 ∨ zm bs = BitVec.allOnes 32 := by
  unfold zm; split <;> simp

theorem masked {m m' : Mem} {a : Addr} {K : Nat} {r z : BitVec 32} {o : Option (List Byte)}
    (hz : z = 0 ∨ z = BitVec.allOnes 32) (hw : Spec.Rsa.written m a K r o)
    (hb : Spec.Rsa.bytesAt m' a K = (Spec.Rsa.bytesAt m a K).map (· &&& (z ^^^ BitVec.allOnes 32).setWidth 8)) :
    Spec.Rsa.written m' a K (r &&& (z ^^^ BitVec.allOnes 32)) (if z = 0 then o else none) := by
  rcases hz with rfl | rfl
  · simp only [ite_true]
    have e1 : (0 : BitVec 32) ^^^ BitVec.allOnes 32 = BitVec.allOnes 32 := BitVec.zero_xor
    have e8 : (BitVec.allOnes 32).setWidth 8 = BitVec.allOnes 8 := by decide
    have hb' : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K := by
      rw [hb, e1, e8]
      exact (List.map_congr_left (g := id) fun x _ => BitVec.and_allOnes).trans (List.map_id _)
    rw [e1, BitVec.and_allOnes]
    cases o with
    | some y => exact ⟨hw.1, hb'.trans hw.2⟩
    | none => exact ⟨hw.1, hb'.trans hw.2⟩
  · simp only [show BitVec.allOnes 32 = 0 ↔ False by decide, ite_false]
    have e1 : BitVec.allOnes 32 ^^^ BitVec.allOnes 32 = 0 := BitVec.xor_self
    have e0 : r &&& (0 : BitVec 32) = 0 := by simp
    rw [e1, e0]
    refine ⟨rfl, ?_⟩
    rw [hb, e1]
    apply List.ext_getElem (by simp [Proof.RsaPkcs1Sig.bytesAt_len])
    intro i h₁ h₂
    simp

theorem maskArgs_wp {σ s : State} (h : G8 P σ s) : WP isa (.block maskArgs) s (MI P P.K σ) := by
  obtain ⟨hs, zs, cr⟩ := h
  simp only [maskArgs]
  refine hs.2.wp_slot (d := oZ) (r := .ebx) (by show oZ + 4 ≤ frameBytes; decide) (by decide) fun t1 s1 u1 => ?_
  refine wp_xorI fun t2 u2 => ?_
  refine wp_mov fun t3 u3 => ?_
  refine wp_and fun t4 u4 => ?_
  have s4 : P.lay.St σ t4 := ((s1.upd u2 (by decide)).upd u3 (by decide)).upd u4 (by decide)
  refine s4.wp_arg (j := 0) (r := .esi) (by simp) (by decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 3) (r := .ecx) (by simp) (by decide) fun t6 s6 u6 => WP.block_nil ?_
  have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have b2 : t2.gpr .ebx = keep P σ := by rw [u2.gpr, u1.gpr, zs]
  refine ⟨⟨hs.1, s6⟩, Nat.le_refl _, ?_, ?_, ?_, s.mem, s.gpr .eax, cr, ?_, fun i _ => ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, Nat.sub_self]; simp
  · rw [u6.gpr]; rfl
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), b2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), b2,
      u2.other _ (by decide), u1.other _ (by decide)]
  · rw [mm, Nat.sub_self]; simp

theorem maskBody_vp (m : Nat) : VP (MI P (m + 1)) (.block maskBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < m)) ∧ (m = 0 → MI P 0 σ s) ∧ (0 < m → MI P m σ s) := by
  refine VP.taint [.esi, .ecx] maskBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  obtain ⟨hs, hk, si, cx, bx, m0, rc, cr, di, mem⟩ := h
  have hK := hs.1.k1024
  have hfo : P.out.toNat + P.K ≤ 2 ^ 32 := by
    have := hs.1.ok.fits P.OUT (by simp)
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by have := P.out.isLt; omega)] at this
  have hi : P.K - (m + 1) < P.K := by omega
  have ha : ∀ t : State, t.gpr .esi = s.gpr .esi →
      t.ea ⟨.esi, 0⟩ = P.out.setWidth 64 + BitVec.ofNat 64 (P.K - (m + 1)) := fun t e => by
    rw [ea_at, e, si, addr, BitVec.add_zero]; exact addr_eq (by omega)
  have hc : (P.OUT : Region).Contains (P.out.setWidth 64 + BitVec.ofNat 64 (P.K - (m + 1))) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  simp only [maskBody]
  refine wp_movzx8 (ha s rfl) ⟨P.OUT, List.mem_append_right _ (hs.2.inRw (by simp)), hc⟩ fun t1 u1 => ?_
  refine wp_and fun t2 u2 => ?_
  refine wp_store8 (ha t2 (by rw [u2.other _ (by decide), u1.other _ (by decide)]))
    ⟨P.OUT, by rw [u2.wr, u1.wr]; exact hs.2.inRw (by simp), hc⟩ fun t3 u3 => ?_
  refine wp_addi fun t4 u4 => ?_
  refine wp_subi fun t5 u5 _ z5 => WP.block_nil ?_
  have fr : Frame [⟨P.out.setWidth 64 + BitVec.ofNat 64 (P.K - (m + 1)), 1⟩] s.mem t5.mem := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have st : P.lay.St σ t5 := hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨P.OUT, by simp, Offset.sub_base _ (by omega)⟩)
    (by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.other _ (by decide)])
  have cx4 : t4.gpr .ecx = BitVec.ofNat 32 (m + 1) := by
    rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.other _ (by decide), cx]
  have inv : MI P m σ t5 := by
    refine ⟨⟨hs.1, st⟩, by omega, ?_, ?_, ?_, m0, rc, cr, ?_, fun i hi' => ?_⟩
    · rw [u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide), u1.other _ (by decide), si]
      exact off_add _ _ 1 _ (by omega)
    · rw [u5.gpr, cx4]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega)
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), bx]
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), di]
    · rw [u5.mem, u4.mem, u3.mem, WriteBytes.writeW8_apply, u2.mem, u1.mem]
      by_cases e : i = P.K - (m + 1)
      · subst e
        have hm := mem _ hi
        simp only [Nat.lt_irrefl, ↓reduceIte] at hm
        simp only [show P.K - (m + 1) < P.K - m from by omega, ↓reduceIte]
        rw [show Reg8.dl.reg = .edx from rfl, u2.gpr, u1.gpr, u1.other _ (by decide), bx, ← hm,
          BitVec.setWidth_and, setWidth_byte]
      · have hne := Offset.add_ofNat_ne (P.out.setWidth 64) (by omega : i < 2 ^ 64)
          (by omega : P.K - (m + 1) < 2 ^ 64) e
        simp only [hne, ↓reduceIte]
        rw [mem i hi']
        by_cases h1 : i < P.K - (m + 1)
        · simp only [h1, show i < P.K - m from by omega, ↓reduceIte]
        · simp only [h1, show ¬ i < P.K - m from by omega, ↓reduceIte]
  refine ⟨?_, fun h0 => h0 ▸ inv, fun _ => inv⟩
  show eval .ne t5 = _
  rw [cx4, show BitVec.ofNat 32 (m + 1) - 1 = BitVec.ofNat 32 m from
    Offset.ofNat_sub_ofNat (d := 1) (by omega), ofNat_beq_zero (by omega)] at z5
  simp only [eval, z5]
  by_cases h0 : m = 0 <;> simp [h0] <;> omega

theorem maskLoop_vp : VP (MI P P.K) maskLoop (MI P 0) := by
  refine (VP.loop (I := fun m => MI P m) maskBody_vp (P.K - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have := h.1.1.k64
  rw [show P.K - 1 + 1 = P.K by omega]; exact h

theorem masked_g10 {σ s : State} (h : MI P 0 σ s) : G10 P σ s := by
  obtain ⟨hs, -, -, -, -, m0, rc, cr, di, mem⟩ := h
  refine ⟨hs, fun nB hn hp => ?_⟩
  rw [di]
  refine masked (zm_cases _) (cr nB hn hp) ?_
  apply List.ext_getElem (by simp [Proof.RsaPkcs1Sig.bytesAt_len])
  intro i h₁ h₂
  simp only [Proof.RsaPkcs1Sig.bytesAt_len] at h₁
  simp only [List.getElem_map, Spec.Rsa.bytesAt, List.getElem_range]
  rw [mem i h₁]
  simp only [Nat.sub_zero, h₁, ↓reduceIte]
  rfl

theorem wipeArgs_wp {σ s : State} (h : G10 P σ s) : WP isa (.block wipeArgs) s (G11 P σ) := by
  obtain ⟨hs, res⟩ := h
  simp only [wipeArgs]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have s2 : P.lay.St σ t2 := (hs.2.upd u1 (by decide)).upd u2 (by decide)
  refine s2.wp_arg (j := 3) (r := .ecx) (by simp) (by decide) fun t3 s3 u3 => ?_
  refine wp_movi fun t4 u4 => WP.block_nil ⟨⟨hs.1, s3.upd u4 (by decide)⟩, ?_, ?_, ?_, u4.gpr⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide)]
    exact res
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr, hs.2.sp]
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem zero_wp {σ s : State} (h : G11 P σ s) : WP isa zeroLoop s (G10 P σ) := by
  obtain ⟨hs, res, si, cx, ax⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := hs.1.fit
  have em := hs.1.emA
  have hF : oEM + P.K ≤ P.lay.F := by show _ ≤ frameBytes; simp only [oEM, frameBytes]; omega
  have hpt : (P.B + BitVec.ofNat 32 oEM).toNat + P.K ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oEM) (by decide)]
    simp only [oEM, frameBytes] at fit ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  refine WP.mono (zero_ok (p := P.B + BitVec.ofNat 32 oEM) (n := P.K) (by have := hs.1.k64; omega) (by omega)
    hpt si cx ax (by rw [em]; exact hs.2.inFr hF)) fun t ht => ?_
  have fr : Frame [⟨P.lay.fr oEM, P.K⟩] s.mem t.mem := by
    rw [ht.mem, em]
    have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (P.lay.fr oEM) (List.replicate P.K 0)
    simpa using this
  have st : P.lay.St σ t := hs.2.frameW hF fr ht.rd ht.wr (ht.other _ (by decide) (by decide))
  refine ⟨⟨hs.1, st⟩, fun nB hn hp => ?_⟩
  have hd : oEM + P.K ≤ P.lay.F + 16 := by show _ ≤ frameBytes + 16; simp only [oEM, frameBytes]; omega
  have hb : Spec.Rsa.bytesAt t.mem (P.out.setWidth 64) P.K = Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K :=
    Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) hd).symm) (by omega)
  have w := res nB hn hp
  rw [ht.other _ (by decide) (by decide)]
  revert w
  generalize (if zm (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none) = o
  intro w
  cases o with
  | some y => exact ⟨w.1, hb.trans w.2⟩
  | none => exact ⟨w.1, hb.trans w.2⟩

theorem ret_wp {σ s : State} (h : G10 P σ s) : WP isa (.block [.mov .eax (.reg .edi)]) s (G13 P σ) :=
  wp_mov fun t u => WP.block_nil ⟨⟨h.1.1, h.1.2.upd u (by decide)⟩, by
    rw [u.mem, u.gpr]; exact h.2⟩

/-! ## Constant time -/

theorem maskArgs_vp : VP (G8 P) (.block maskArgs) (MI P P.K) :=
  VP.taint [.esp] maskArgs_taint (sp_agree fun _ _ h => h.1) fun _ _ h => maskArgs_wp h

theorem mask_vp : VP (G8 P) (.seq (.block maskArgs) maskLoop) (G10 P) :=
  maskArgs_vp.seq (maskLoop_vp.mono (fun _ _ h => h) fun _ _ h => masked_g10 h)

theorem wipeArgs_vp : VP (G10 P) (.block wipeArgs) (G11 P) :=
  VP.taint [.esp] wipeArgs_taint (sp_agree fun _ _ h => h.1) fun _ _ h => wipeArgs_wp h

theorem zero_vp : VP (G11 P) zeroLoop (G10 P) :=
  VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]) fun _ _ h => zero_wp h

theorem ret_vp : VP (G10 P) (.block [.mov .eax (.reg .edi)]) (G13 P) :=
  VP.taint [.esp] ret_taint (sp_agree fun _ _ h => h.1) fun _ _ h => ret_wp h

end VG.Proof.RsaPkcs1Enc.X86.Pc
