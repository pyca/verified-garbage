module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecChk
public import VerifiedGarbage.Proof.RsaOaep.Decode
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP decryption on ARMv7: when `k` is too short

`fault_vp`: `r0 := (r = 2) ? 2 : 0` from the result's slot. `fail_vp`: when
`k < 2 hLen + 2`, zeros to `out` and to `*msg_len`, and that result, as
`decrypt` says (`Proof.RsaOaep.decOut_short`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- `(r = 2) ? 2 : 0` from the result's slot. -/
theorem fault_wp {P : EP} {σ s : State} (hc : Ctx P.lay P.scr σ s) (hi : In P σ)
    (hr : s.mem.readW (P.lay.fr sRes) 32 = rV P σ) {rest : List Instr} {Q : State → Prop}
    (hq : ∀ t, t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp → t.gpr .r12 = P.B →
      t.gpr .r0 = faultV (rV P σ) → WP isa (.block rest) t Q) :
    WP isa (.block (sp0 :: (faultBit ++ rest))) s Q := by
  have hg := hi.geo
  have hw : WP isa (.block (sp0 :: faultBit)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r12 = P.B ∧ t.gpr .r0 = faultV (rV P σ) := by
    prun [faultBit, sp0, ld, hc.st.sp, hc.rFr hg, slotAt hi (d := sRes) (by decide), hr, sRes_lt, dpVal]
  rw [show sp0 :: (faultBit ++ rest) = (sp0 :: faultBit) ++ rest from rfl]
  exact WP.block_append (WP.mono hw fun t ⟨m, rd, wr, sp, r12, r0⟩ => hq t m rd wr sp r12 r0)

/-- What failing keeps. -/
abbrev Xf (D : Nat) (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ ¬ 2 * D + 2 ≤ P.K ∧ m.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ

theorem out_slot {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    (slotR P.lay d).Disjoint P.OUT :=
  hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 56; unfold frameBytes at hd ⊢; omega)

theorem ml_slot {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    (slotR P.lay d).Disjoint P.ML :=
  hi.ok.stk_fr (R := P.ML) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 56; unfold frameBytes at hd ⊢; omega)

theorem out_ml {P : EP} {σ : State} (hi : In P σ) : P.OUT.Disjoint P.ML := by
  have := hi.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact this.1.1

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

/-- After `*msg_len := 0`. -/
abbrev F3 (D : Nat) (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Xf D P σ s.mem ∧ (∀ i < P.K, s.mem (byteAt P.out i) = 0) ∧
    s.mem.readW (State.addr P.ml) 64 = 0

theorem fail_vp (h g : OHash) (P : EP) :
    VP (fun σ s => C2 h.H.D P σ s ∧ isa.eval .ne s = some true) decFail (Fin h.G g.G P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hb := out_wbuf hi₀
  have hK := hi₀.k64
  show VP _ (.seq (.block [sp0, ld .r0 (arg 0), ld .lr (arg 4), mw .r2 0]) (.seq Impl.Bignum.Arm.maskBytes
    (.seq (.block mlFail) (.seq (.block mlStore) (.block (sp0 :: faultBit)))))) _
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Xf h.H.D P σ s.mem) ∧ s.gpr .r0 = P.out ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 P.K)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, _, hr, hk, z⟩, e⟩ => ?_) ?_
  · have nf : ¬ 2 * h.H.D + 2 ≤ P.K := by
      intro hf
      rw [VG.Proof.X25519.Arm.eval_ne, z, decide_eq_true hf] at e
      cases e
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v0 : s.mem.readW (P.lay.fr (arg 0)) 32 = P.out := v0
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block [sp0, ld .r0 (arg 0), ld .lr (arg 4), mw .r2 0]) s fun t => t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧ t.gpr .r2 = 0 ∧
        t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [sp0, ld, mw, hc.st.sp, a0, r0, v0, a4, r4, v4, arg_lt]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t2, tl⟩ =>
      ⟨⟨hc.regs rd wr sp m, hi, nf, m ▸ hr, hk⟩, t0, t2, tl⟩
  refine VP.seq ((zero_vp hb (by omega) (Inv := Xf h.H.D P)
    fun σ m m' hm hf => ⟨hm.1, hm.2.1, slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact out_slot hm.1 (by decide)) hm.2.2.1, hm.2.2.2⟩).mono
    (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩) fun _ _ h => h) ?_
  -- `msg_len`, and zero.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Xf h.H.D P σ s.mem ∧
      ∀ i < P.K, s.mem (byteAt P.out i) = 0) ∧ s.gpr .r1 = P.ml ∧ s.gpr .r3 = 0 ∧ s.gpr .r2 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, hz⟩ => ?_) ?_
  · obtain ⟨a2, r2, v2⟩ := argAt hm.1 hc.st (j := 2) (by decide)
    replace v2 : s.mem.readW (P.lay.fr (arg 2)) 32 = P.ml := v2
    have hw : WP isa (.block mlFail) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r1 = P.ml ∧ t.gpr .r3 = 0 ∧ t.gpr .r2 = 0 := by
      prun [mlFail, sp0, ld, mw, hc.st.sp, a2, r2, v2, arg_lt]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t1, t3, t2⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hm, m ▸ hz⟩, t1, t3, t2⟩
  refine VP.seq (G := F3 h.H.D P) (mlStore_vp P (fun σ s hs => ⟨⟨hs.1.2.1.1, hs.1.1.st⟩, hs.2.1⟩)
    (fun σ s m ⟨⟨hc, hm, hz⟩, _, r3, _⟩ fr hr ⟨⟨hc', hm', hz'⟩, _⟩ => ⟨hc', hm', hz', by rw [hr, r3]; rfl⟩)
    (fun σ s m ⟨⟨hc, hm, hz⟩, r1, r3, r2⟩ fr => ⟨⟨?_, ?_, ?_⟩, r1, r3, r2⟩) fun σ s hs => hs.2.2.2) ?_
  · exact hc.write (t := { s with mem := m }) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ml_slot hm.1 (by decide)) rfl rfl rfl
  · exact ⟨hm.1, hm.2.1, slot_keep fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ml_slot hm.1 (by decide)) hm.2.2.1, hm.2.2.2⟩
  · intro i hi
    rw [← hz i hi]
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact out_ml hm.1 _ (contains_byte (Region.contains_self _ _) (out_wbuf hm.1).fit hi)
  -- The result.
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hi, nf, hr, hk⟩, hz, hml⟩ => ?_
  refine fault_wp hc hi hr fun t m rd wr sp _ r0 => ?_
  apply WP.block_nil
  refine ⟨⟨hi, hc.st.regs rd wr sp m⟩, ?_⟩
  rw [m, r0]
  have ec : (ctB P σ).length = P.nB.length := by rw [ctB_length, nB_length hi]
  rw [Res, Proof.RsaOaep.decrypt_eq ec, rV]
  exact decOut_fail hk (by rw [h.glen]; omega) (Proof.RsaOaep.out_zero hz) hml

end VG.Proof.RsaOaep.Arm.Dec
