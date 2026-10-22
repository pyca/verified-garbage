module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Call
public import VerifiedGarbage.Proof.RsaOaep.X86.Base
public import VerifiedGarbage.Proof.RsaPss.X86.Prims
public import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaOaep.X86.Instr
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86: the check of `k`, and when it fails

As on ARMv7 (`Proof/RsaOaep/Arm/DecChk.lean`, `Proof/RsaOaep/Arm/DecFail.lean`):
`chk_vp`: the private-key operation's result to its slot, and the flags of
`k < 2 hLen + 2`. `fail_vp`: then zeros to `out` and to `*msg_len`, and the
result `(r = 2) ? 2 : 0`, as `decrypt` says (`Proof.RsaOaep.decOut_short`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi zeroLoop)
open VG.Proof.Mont.X86 (wp_storeS)

/-- A slot of the frame and our part of `scratch` are apart. -/
theorem slot_em {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    ∀ r ∈ [slotR P.lay d], Region.Disjoint (sR P.scr oEm P.K) r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi.k1024
  exact (hg.slot ok (o := oEm) (n := P.K) (by unfold oEm oRsa; omega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega)).symm

/-- After the check. -/
abbrev C2 (D : Nat) (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ In P σ ∧ (∀ i < P.K, s.mem (sa P.scr (oEm + i)) = V P σ i) ∧
    s.mem.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ ∧ s.cf = some (decide (P.K < 2 * D + 2))

theorem chk_vp (h : OHash) (P : EP) : VP (R2 P) (.block (decChk h.H)) (C2 h.H.D P) := by
  refine VP.taint [.esp] h.certs.decChk (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp])
    fun σ s ⟨hc, hi, he, r0, hk⟩ => ?_
  have hg := hi.geo
  have hD := h.D_le
  have hK := hi.k1024
  simp only [decChk, ld, st]
  refine hc.wp_st hg (d := sRes) (by decide) fun t1 c1 m1 => ?_
  refine c1.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t2 c2 u2 => ?_
  refine wp_cmpi fun t3 f3 cf3 _ => WP.block_nil ⟨c2.fupd f3, hi, ?_, ?_, hk, ?_⟩
  · have fr : Frame [slotR P.lay sRes] s.mem t3.mem := by
      rw [f3.mem, u2.mem, m1.mem]; exact slot_frame _ _ _ _
    exact sbytes_keep fr (slot_em hi (by decide)) (by unfold oEm; omega) he
  · rw [f3.mem, u2.mem, m1.mem, Mem.readW_writeW_self32, r0]
  · rw [cf3, u2.gpr]
    show some (decide ((BitVec.ofNat 32 P.K).toNat < (BitVec.ofNat 32 (2 * h.H.D + 2)).toNat)) = _
    rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]

/-! ## When `k` is too short -/

/-- `(r = 2) ? 2 : 0`, as `faultBit` computes it. -/
abbrev faultV (r : BitVec 32) : BitVec 32 :=
  (if decide ((r ^^^ 2).toNat < (1 : BitVec 32).toNat) then BitVec.allOnes 32 else 0) &&& 2

theorem faultV_rOf (o : Spec.Rsa.Outcome) : faultV (rOf o) = if o = .fault then 2 else 0 := by
  cases o <;> simp only [rOf, reduceCtorEq, ite_false, ite_true] <;> decide

/-- `(r = 2) ? 2 : 0` from the result's slot. -/
theorem fault_wp {P : EP} {σ s : State} (hc : Ctx P.lay P.scr σ s) (hi : In P σ)
    (hr : s.mem.readW (P.lay.fr sRes) 32 = rV P σ) {rest : List Instr} {Q : State → Prop}
    (hq : ∀ t, Ctx P.lay P.scr σ t → t.mem = s.mem → t.gpr .eax = faultV (rV P σ) → WP isa (.block rest) t Q) :
    WP isa (.block (faultBit ++ rest)) s Q := by
  have hg := hi.geo
  simp only [faultBit, ld, List.cons_append, List.nil_append]
  refine hc.wp_slot hg (d := sRes) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_xori fun t2 u2 => wp_cmpi fun t3 f3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => wp_andi fun t5 u5 => ?_
  have c5 : Ctx P.lay P.scr σ t5 :=
    (((c1.upd u2 (by decide) (by decide)).fupd f3).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)
  refine hq t5 c5 (by rw [u5.mem, u4.mem, f3.mem, u2.mem, u1.mem]) ?_
  rw [u5.gpr, u4.gpr, u2.gpr, u1.gpr, hr]

/-- What failing keeps. -/
abbrev Xf (D : Nat) (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ P.K < 2 * D + 2 ∧ m.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ

theorem out_slot {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    (slotR P.lay d).Disjoint P.OUT :=
  hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 16; unfold frameBytes at hd ⊢; omega)

theorem ml_slot {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    (slotR P.lay d).Disjoint P.ML :=
  hi.ok.stk_fr (R := P.ML) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 16; unfold frameBytes at hd ⊢; omega)

theorem out_ml {P : EP} {σ : State} (hi : In P σ) : P.OUT.Disjoint P.ML := by
  have := hi.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact this.1.1

theorem ml_fit {P : EP} {σ : State} (hi : In P σ) : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := hi.ok.fits P.ML (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.ml.isLt; omega)] at this

theorem out_wbuf {P : EP} {σ : State} (hi : In P σ) : WBuf P.lay P.out P.K := by
  have hK := hi.k1024
  have hfo := hi.ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at hfo
  rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega)] at hfo
  exact ⟨hfo, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩

theorem nB_length {P : EP} {σ : State} (hi : In P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.bytesAt_len]

theorem ctB_length (P : EP) (σ : State) : (ctB P σ).length = P.K := RsaPkcs1Sig.bytesAt_len _ _ _

/-- The result when `k` is too short. -/
theorem decOut_fail {H G : Spec.Mgf1.Hash} {label : List Byte} {o : Spec.Rsa.Outcome} {K : Nat}
    (hl : ∀ y, o = .ok y → y.length = K) (hk : K < 2 * H.len + 2) {m : Mem} {out ml : Addr}
    (hz : Spec.Rsa.bytesAt m out K = Spec.RsaOaep.zeros K) (hml : m.readW ml 64 = 0) :
    Spec.RsaOaep.writtenDecrypt m out ml K (faultV (rOf o)) (Proof.RsaOaep.decOut H G label o) := by
  rw [faultV_rOf]
  cases o with
  | ok y => rw [Proof.RsaOaep.decOut_short hl hk]; exact ⟨rfl, hz, hml⟩
  | invalid => exact ⟨rfl, hz, hml⟩
  | fault => exact ⟨rfl, hz, hml⟩

/-- `*msg_len := 0`, through `esi = msg_len`, and the result. -/
theorem mlZero_wp {P : EP} {σ s : State} (hc : Ctx P.lay P.scr σ s) (hi : In P σ) (si : s.gpr .esi = P.ml)
    {Q : State → Prop}
    (hq : ∀ t, Ctx P.lay P.scr σ t → Frame [P.ML] s.mem t.mem → t.mem.readW (P.ml.setWidth 64) 64 = 0 →
      t.gpr .eax = faultV (rV P σ) → Q t)
    (hr : s.mem.readW (P.lay.fr sRes) 32 = rV P σ) :
    WP isa (.block ((mlZero ++ faultBit).drop 1)) s Q := by
  have fit := ml_fit hi
  have win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (P.ml.setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨P.ML, hc.st.inRw (by simp), Offset.contains_base _ hd (by omega)⟩
  simp only [mlZero, mi, List.cons_append, List.drop_succ_cons, List.drop_zero]
  refine wp_movi fun t1 u1 => ?_
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 0)
    (by show t1.ea ⟨.esi, 0⟩ = _; rw [ea_at, u1.other _ (by decide), si]; exact addr_eq (by omega))
    (by rw [u1.wr]; exact win 0 (by decide)) fun t2 m2 => ?_
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 4)
    (by show t2.ea ⟨.esi, 4⟩ = _; rw [ea_at, m2.gpr, u1.other _ (by decide), si]; exact addr_eq (by omega))
    (by rw [m2.wr, u1.wr]; exact win 4 (by decide)) fun t3 m3 => ?_
  have mm : t3.mem = (s.mem.writeW (P.ml.setWidth 64 + BitVec.ofNat 64 0) (BitVec.ofNat 32 0)).writeW
      (P.ml.setWidth 64 + BitVec.ofNat 64 4) (BitVec.ofNat 32 0) := by
    rw [m3.mem, m2.gpr, m2.mem, u1.gpr, u1.mem]
  have fr : Frame [P.ML] s.mem t3.mem := by
    rw [mm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have c3 : Ctx P.lay P.scr σ t3 := hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
    (by rw [m3.rd, m2.rd, u1.rd]) (by rw [m3.wr, m2.wr, u1.wr])
    (by rw [m3.gpr, m2.gpr, u1.other _ (by decide)]) (by rw [m3.gpr, m2.gpr, u1.other _ (by decide)])
  have hr3 : t3.mem.readW (P.lay.fr sRes) 32 = rV P σ := by
    rw [slot_keep fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ml_slot hi (by decide)) hr]
  refine fault_wp c3 hi hr3 (rest := []) fun t ct m ax => WP.block_nil (hq t ct (m ▸ fr) ?_ ax)
  rw [m, mm, BitVec.add_zero]
  exact readW_pair s.mem (P.ml.setWidth 64) (L := 0) (by decide)

theorem fail_vp (h g : OHash) (P : EP) :
    VP (fun σ s => C2 h.H.D P σ s ∧ isa.eval .b s = some true) (decFail) (Fin h.G g.G P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hb := out_wbuf hi₀
  have hK := hi₀.k64
  show VP _ (.seq (.block outClr) (.seq zeroLoop (.block (mlZero ++ faultBit)))) _
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ Xf h.H.D P σ s.mem ∧ s.gpr .esi = P.out ∧
      s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0)
    (VP.taint [.esp] outClr_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.st.sp, h₂.1.1.st.sp])
      fun σ s ⟨⟨hc, hi, _, hr, hk, cf⟩, e⟩ => ?_) ?_
  · have nf : P.K < 2 * h.H.D + 2 := by
      by_contra hf
      simp only [eval, cf, decide_eq_false hf] at e
      exact absurd e (by decide)
    have hg := hi.geo
    simp only [outClr, ld, mi]
    refine hc.wp_arg hg (dec_arg (j := 0) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      c1.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t2 c2 u2 => wp_movi fun t3 u3 =>
        WP.block_nil ⟨c2.upd u3 (by decide) (by decide), ⟨hi, nf, ?_, hk⟩, ?_, ?_, ?_⟩
    · rw [u3.mem, u2.mem, u1.mem, hr]
    · simp (disch := decide) only [u3.other, u2.other, u1.gpr]; rfl
    · simp (disch := decide) only [u3.other, u2.gpr]; rfl
    · rw [u3.gpr]; rfl
  refine VP.seq ((zero_vp (scr := P.scr) hb (by omega) (Inv := Xf h.H.D P)
    fun σ m m' hm hf => ⟨hm.1, hm.2.1, slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact out_slot hm.1 (by decide)) hm.2.2.1, hm.2.2.2⟩).mono
    (fun σ s h => h) fun _ _ h => h) ?_
  -- `*msg_len := 0` and the result.
  have e : VP _ (.block ((mlZero ++ faultBit).take 1 ++ (mlZero ++ faultBit).drop 1)) (Fin h.G g.G P) :=
    (VP.taint (F := fun σ s => Ctx P.lay P.scr σ s ∧ Xf h.H.D P σ s.mem ∧
      ∀ i < P.K, s.mem (byteAt P.out i) = 0)
    (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Xf h.H.D P σ s.mem ∧ ∀ i < P.K, s.mem (byteAt P.out i) = 0) ∧
      s.gpr .esi = P.ml)
    [.esp] mlZeroHead_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp])
    fun σ s ⟨hc, hm, hz⟩ => ?_).block_append (VP.taint [.esp, .esi] mlZeroRest_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
      · rw [h₁.2, h₂.2]) fun σ s ⟨⟨hc, hm, hz⟩, si⟩ => ?_)
  · rwa [List.take_append_drop] at e
  · have hg := hm.1.geo
    simp only [mlZero, ld, List.cons_append, List.take_succ_cons, List.take_zero]
    exact hc.wp_arg hg (dec_arg (j := 2) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      WP.block_nil ⟨⟨c1, by rw [u1.mem]; exact hm, by rw [u1.mem]; exact hz⟩, by rw [u1.gpr]; rfl⟩
  · obtain ⟨hi, nf, hr, hk⟩ := hm
    refine mlZero_wp hc hi si (fun t ct fr hml ax => ?_) hr
    refine ⟨⟨hi, ct.st⟩, ?_⟩
    have hz' : ∀ i < P.K, t.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) = 0 := fun i hi' => by
      rw [← hz i hi']
      exact fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact out_ml hi _ (contains_byte (Region.contains_self _ _) (out_wbuf hi).fit hi')
    rw [ax]
    have ec : (ctB P σ).length = P.nB.length := by rw [ctB_length, nB_length hi]
    rw [Res, Proof.RsaOaep.decrypt_eq ec, rV]
    exact decOut_fail hk (by rw [h.glen]; omega) (Proof.RsaOaep.out_zero hz') hml

end VG.Proof.RsaOaep.X86.Dec
