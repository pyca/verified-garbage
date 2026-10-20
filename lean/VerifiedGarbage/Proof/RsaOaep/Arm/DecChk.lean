module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecCall
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaOaep.Arm.DecCall
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP decryption on ARMv7: the check of `k`, and when it fails

`chk_vp`: the private-key operation's result to its slot, and the flags of
`k < 2 hLen + 2`. `fail_vp`: then zeros to `out` and to `*msg_len`, and the
result `(r = 2) ? 2 : 0`, as `decrypt` says (`Proof.RsaOaep.decOut_short`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- The flags of `k < c`: zero exactly when `c ≤ k`. -/
theorem top_z {K c : Nat} (hK : K ≤ 1024) (hc : c ≤ 1024) :
    ((BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 - 0 == 0) = decide (c ≤ K) := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  by_cases h : c ≤ K
  · rw [Offset.ofNat_sub_ofNat (w := 32) h, decide_eq_true h]
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := K) (by omega), Nat.mod_eq_of_lt (a := c) (by omega)] at this
    simp at this; omega

/-- Bytes of our part of `scratch` from its start, kept by a frame that misses them. -/
theorem em_keep {scr : BitVec 32} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr 0 n) r) (hn : n < 2 ^ 64) {f : Nat → Byte}
    (h : ∀ i < n, m (sa scr i) = f i) : ∀ i < n, m' (sa scr i) = f i := by
  have := sbytes_keep (scr := scr) hf hd (by omega) (f := f) (fun i hi => by rw [Nat.zero_add]; exact h i hi)
  intro i hi; have e := this i hi; rwa [Nat.zero_add] at e

/-- After the check. -/
abbrev C2 (D : Nat) (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ In P σ ∧ (∀ i < P.K, s.mem (sa P.scr i) = V P σ i) ∧
    s.mem.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ ∧ s.z = decide (2 * D + 2 ≤ P.K)

theorem chk_vp (h : OHash) (P : EP) : VP (R2 P) (.block (decChk h.H)) (C2 h.H.D P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, hi, he, r0, hk⟩ => ?_
  have hg := hi.geo
  have hD := h.D_le
  have hK := hi.k1024
  obtain ⟨σ', ok⟩ := hg.ok
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  have k4 : ∀ v : BitVec 32, (s.mem.writeW (P.lay.fr sRes) v).readW (P.lay.fr (arg 4)) 32 =
      s.mem.readW (P.lay.fr (arg 4)) 32 := fun v => Lay.readW_fr_other _ _ _ (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sRes; simp) (by decide) (by decide)
  have hw : WP isa (.block (decChk h.H)) s fun t => t.mem = s.mem.writeW (P.lay.fr sRes) (rV P σ) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (2 * h.H.D + 2 ≤ P.K) := by
    prun [decChk, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, a4, r4, v4, k4, r0, sRes_lt, arg_lt,
      movw_val (show 2 * h.H.D + 2 < 2 ^ 16 by omega), dpVal, top_z hK (show 2 * h.H.D + 2 ≤ 1024 by omega)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  have fr : Frame [slotR P.lay sRes] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, em_keep fr (fun r hr => ?_) (by omega) he,
    by rw [m, Mem.readW_writeW_self32], hk, z⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hg.slot ok (o := 0) (n := P.K) (by unfold oRsa; omega) (by rw [hg.F]; decide)).symm

/-! ## When `k` is too short -/

/-- `(r = 2) ? 2 : 0`. -/
abbrev faultV (r : BitVec 32) : BitVec 32 := (((r ^^^ 2) - 1) >>> 31) <<< 1

theorem faultV_rOf (o : Spec.Rsa.Outcome) : faultV (rOf o) = if o = .fault then 2 else 0 := by
  cases o <;> simp only [rOf, reduceCtorEq, ite_false, ite_true] <;> decide

theorem out_wbuf {P : EP} {σ : State} (hi : In P σ) : WBuf P.lay P.out P.K := by
  have hK := hi.k1024
  have hf := hi.ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨hf, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩,
    hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)⟩

theorem nB_length {P : EP} {σ : State} (hi : In P σ) : P.nB.length = P.K := by
  rw [← hi.nB]; simp [Spec.Rsa.bytesAt]

theorem ctB_length (P : EP) (σ : State) : (ctB P σ).length = P.K := by simp [Spec.Rsa.bytesAt]

/-- A 64-bit word written as two 32-bit halves, the high one zero. -/
theorem readW_pair (m : Mem) (a : Addr) {L : Nat} (hL : L < 2 ^ 32) :
    ((m.writeW a (BitVec.ofNat 32 L)).writeW (a + BitVec.ofNat 64 4) (0 : BitVec 32)).readW a 64 =
      BitVec.ofNat 64 L := by
  show (Mem.read _ a 8).setWidth 64 = _
  rw [Mem.read_eq_of_bytes (n := 8) (v := BitVec.ofNat 64 L) fun i hi => ?_]
  · exact BitVec.setWidth_eq _
  by_cases h4 : i < 4
  · have e1 : ¬ (a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4)).toNat < 32 / 8 := by
      rw [show a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4) = BitVec.ofNat 64 i - BitVec.ofNat 64 4 by
        rw [Offset.add_sub_add_left]]
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    simp only [Mem.writeW]
    rw [Mem.write_apply e1]
    simp only [Mem.write, Mem.sub_ofNat_toNat a (by omega : i < 2 ^ 64), show i < 32 / 8 by omega, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L < 2 ^ (8 * (32 / 8)) from hL),
      Nat.mod_eq_of_lt (show L < 2 ^ (8 * 8) from Nat.lt_of_lt_of_le hL (by decide))]
    rw [show 8 * (32 / 8) = 32 from rfl, Nat.mod_eq_of_lt hL]
  · have e : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) := by
      rw [Offset.add_add, show 4 + (i - 4) = i by omega]
    simp only [Mem.writeW, Mem.write]
    rw [e, Mem.sub_ofNat_toNat _ (by omega : i - 4 < 2 ^ 64)]
    simp only [show i - 4 < 32 / 8 by omega, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : 2 ^ 32 ≤ 2 ^ (8 * i) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.div_eq_of_lt (by omega : L % 2 ^ 64 < 2 ^ (8 * i))]
    simp

theorem ml_fit {P : EP} {σ : State} (hi : In P σ) : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := hi.ok.fits P.ML (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this

theorem mlStore_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block mlStore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `*msg_len := r3 (low), r2 (high)`, through `r1 = msg_len`. -/
theorem mlStore_vp (P : EP) {F : State → State → Prop} (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .r1 = P.ml)
    {G : State → State → Prop}
    (hG : ∀ σ s (m : Mem), F σ s → Frame [P.ML] s.mem m →
      m.readW (State.addr P.ml) 64 = BitVec.ofNat 64 (s.gpr .r3).toNat →
      F σ { s with mem := m } → G σ { s with mem := m })
    (hF' : ∀ σ s (m : Mem), F σ s → Frame [P.ML] s.mem m → F σ { s with mem := m })
    (h2 : ∀ σ s, F σ s → s.gpr .r2 = 0) :
    VP F (.block mlStore) G := by
  refine VP.taint _ mlStore_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    rw [(hF _ _ h₁).2, (hF _ _ h₂).2]
  obtain ⟨⟨hi, st⟩, r1⟩ := hF σ s hs
  have fit := ml_fit hi
  have a0 : State.addr P.ml = State.addr (P.ml + BitVec.ofNat 32 0) := by rw [BitVec.add_zero]
  have a4 : State.addr (P.ml + BitVec.ofNat 32 4) = State.addr P.ml + BitVec.ofNat 64 4 := addr_add (by omega)
  have win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (State.addr P.ml + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨P.ML, by rw [st.wr, hi.ok.wr]; simp, Offset.contains_base _ hd (by omega)⟩
  have w0 : InRegions s.wr (State.addr P.ml) 4 := by have := win 0 (by decide); rwa [BitVec.add_zero] at this
  have w4 := win 4 (by decide)
  have hw : WP isa (.block mlStore) s fun t => t.mem = (s.mem.writeW (State.addr P.ml) (s.gpr .r3)).writeW
      (State.addr P.ml + BitVec.ofNat 64 4) (s.gpr .r2) ∧ t = { s with mem := t.mem } := by
    prun [mlStore, r1, a4, w0, w4]
    rfl
  refine WP.mono hw fun t ⟨m, et⟩ => ?_
  have c0 : (⟨State.addr P.ml, 8⟩ : Region).Contains (State.addr P.ml) (32 / 8) := by
    have := Offset.contains_base (State.addr P.ml) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have fr : Frame [P.ML] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s.gpr .r3) c0).writeW
      (List.mem_singleton_self _) (s.gpr .r2) (Offset.contains_base _ (by decide) (by decide))
  rw [et]
  refine hG σ s t.mem hs fr ?_ (hF' σ s t.mem hs fr)
  have e := readW_pair s.mem (State.addr P.ml) (s.gpr .r3).isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  rw [m, h2 σ s hs]
  exact e

end VG.Proof.RsaOaep.Arm.Dec
