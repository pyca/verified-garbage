module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBase
public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
import VerifiedGarbage.Proof.RsaOaep.Encode
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaOaep.Arm.EncBase
meta import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.Encode
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the checks

`chk_vp`: `scratch` to its slot, and the flags of whether the message fits
(`fits`), from the lengths alone. `fail_vp`: when it does not, zeros to
`out` and 0 returned, as `encrypt` (`Proof.RsaOaep.encrypt_none`) says.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h g : OHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.H.D P σ ∧ (P.lay h.H.D).St σ s

/-- The label, the message and the seed, as they are in the run from `σ`. -/
abbrev labB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.lab) P.ll
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.msg) P.ml
abbrev seedB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.seed) h.H.D

/-- Whether the message fits. -/
abbrev fits (P : EP) : Prop := 2 * h.H.D + 2 + P.ml ≤ P.K

/-- What the function writes to `out` and returns. -/
abbrev Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r (Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ)
      (seedB h P σ))

/-- The end of the body. -/
abbrev Fin (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h g P σ s.mem (s.gpr .r0)

theorem arg_lt {j : Nat} (hj : j < 15) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega

/-- An argument: its place, readable, and its value. -/
theorem argAt {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat} (hj : j < 15) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = P.argv.getD j 0 := by
  have hl : j < (P.lay D).argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 44; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {D : Nat} {P : EP} {σ : State} (hi : In D P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = (P.lay D).fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 44; unfold frameBytes at hd ⊢; omega)

/-- The flags of the checks: zero exactly when `c + ml ≤ K`. -/
theorem chk_z {K c ml : Nat} (hK : K ≤ 1024) (hc1 : 1 ≤ c) (hc : c ≤ 1024) (hml : ml < 2 ^ 32) :
    (((BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 ||| BitVec.ofNat 32 ml >>> 10 |||
      (BitVec.ofNat 32 K - BitVec.ofNat 32 c - BitVec.ofNat 32 ml) >>> 31) - 0 == 0) = decide (c + ml ≤ K) := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  by_cases hcK : c ≤ K
  · rw [Offset.ofNat_sub_ofNat (w := 32) hcK]
    have z1 : BitVec.ofNat 32 (K - c) >>> 31 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
    by_cases hm : ml < 1024
    · have z2 : BitVec.ofNat 32 ml >>> 10 = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; simp; omega
      rw [z1, z2, ltBit (a := K - c) (b := ml) (by omega) (by omega)]
      by_cases e : K - c < ml
      · simp [e]; omega
      · simp [e]; omega
    · have hne : BitVec.ofNat 32 ml >>> 10 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at this; simp at this; omega
      rw [decide_eq_false (by omega)]
      exact beq_false_of_ne fun e => hne ((or_eq_zero32 _ _).1 ((or_eq_zero32 _ _).1 e).1).2
  · have hne : (BitVec.ofNat 32 K - BitVec.ofNat 32 c) >>> 31 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := K) (by omega), Nat.mod_eq_of_lt (a := c) (by omega)] at this
      simp at this; omega
    rw [decide_eq_false (by omega)]
    exact beq_false_of_ne fun e => hne ((or_eq_zero32 _ _).1 ((or_eq_zero32 _ _).1 e).1).1

/-! ## The checks -/

/-- After `encChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.H.D) P.scr σ s ∧ In h.H.D P σ ∧ s.z = decide (fits h P)

theorem chk_vp (P : EP) : VP (S h P) (.block (encChk h.H)) (C0 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  have hD := h.D_le
  have hK := hi.k1024
  obtain ⟨a11, r11, v11⟩ := argAt hi hs (j := 11) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hs (j := 3) (by decide)
  obtain ⟨a9, r9, v9⟩ := argAt hi hs (j := 9) (by decide)
  replace v11 : s.mem.readW ((P.lay h.H.D).fr (arg 11)) 32 = P.scr := v11
  replace v3 : s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
  replace v9 : s.mem.readW ((P.lay h.H.D).fr (arg 9)) 32 = BitVec.ofNat 32 P.ml := v9
  have k : ∀ (j : Nat) (v : BitVec 32), j < 15 →
      (s.mem.writeW ((P.lay h.H.D).fr sS) v).readW ((P.lay h.H.D).fr (arg j)) 32 =
        s.mem.readW ((P.lay h.H.D).fr (arg j)) 32 :=
    fun j v hj => Lay.readW_fr_other _ _ _ (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sS; split <;> omega) (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by decide)
  have hw : WP isa (.block (encChk h.H)) s fun t => t.mem = s.mem.writeW ((P.lay h.H.D).fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (fits h P) := by
    prun [encChk, sp0, ld, st, mw, hs.sp, a11, r11, v11, a3, r3, v3, a9, r9, v9, k 3 _ (by decide),
      k 9 _ (by decide), slotAt hi (d := sS) (by decide), hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide),
      arg_lt, movw_val (show 2 * h.H.D + 2 < 2 ^ 16 by omega), dpVal, chk_z hK (show 1 ≤ 2 * h.H.D + 2 by omega) (show 2 * h.H.D + 2 ≤ 1024 by omega) hi.ml32]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ⟨⟨?_, ?_⟩, hi, z⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]

/-! ## A message that does not fit -/

theorem out_wbuf {P : EP} {σ : State} (hi : In h.H.D P σ) : WBuf (P.lay h.H.D) P.out P.K := by
  have hK := hi.k1024
  have hf := hi.ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨hf, by omega, ⟨P.OUT, by simp, Region.contains_self _ _⟩,
    hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)⟩

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB]; simp [Spec.Rsa.bytesAt]

theorem msgB_length (P : EP) (σ : State) : (msgB P σ).length = P.ml := by simp [Spec.Rsa.bytesAt]

theorem fail_vp (P : EP) :
    VP (fun σ s => C0 h P σ s ∧ isa.eval .ne s = some true) (encFail) (Fin h g P) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hb := out_wbuf h hi₀
  have hK := hi₀.k64
  show VP _ (.seq (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) (.seq Impl.Bignum.Arm.maskBytes
    (.block [mw .r0 0]))) _
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.H.D) P.scr σ s ∧ (In h.H.D P σ ∧ ¬ fits h P)) ∧ s.gpr .r0 = P.out ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 P.K)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s ⟨⟨hc, hi, z⟩, e⟩ => ?_) ?_
  · have nf : ¬ fits h P := by
      intro hf
      rw [VG.Proof.X25519.Arm.eval_ne, z, decide_eq_true hf] at e
      cases e
    obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
    obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
    replace v0 : s.mem.readW ((P.lay h.H.D).fr (arg 0)) 32 = P.out := v0
    replace v3 : s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
    have hw : WP isa (.block [sp0, ld .r0 (arg 0), ld .lr (arg 3), mw .r2 0]) s fun t => t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧ t.gpr .r2 = 0 ∧
        t.gpr .lr = BitVec.ofNat 32 P.K := by
      prun [sp0, ld, mw, hc.st.sp, a0, r0, v0, a3, r3, v3, arg_lt]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t2, tl⟩ => ⟨⟨hc.regs rd wr sp m, hi, nf⟩, t0, t2, tl⟩
  refine VP.seq ((zero_vp hb (by omega) (Inv := fun σ _ => In h.H.D P σ ∧ ¬ fits h P)
    fun σ m m' hm _ => hm).mono (fun σ s ⟨⟨hc, hm⟩, r0, r2, lr⟩ => ⟨hc, hm, r0, r2, lr⟩) fun _ _ h => h) ?_
  refine VP.taint [] ⟨_, by taint_decide⟩ (fun _ _ _ _ _ _ r hr => by simp at hr)
    fun σ s ⟨hc, ⟨hi, nf⟩, hz⟩ => ?_
  apply WP.of_runBlock
  simp only [mw, runBlock_cons, runStep_some, runBlock_nil, exec]
  refine ⟨_, rfl, ⟨hi, hc.st.regs rfl rfl rfl rfl⟩, fun _ => ?_⟩
  have en : Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ) (seedB h P σ) = none :=
    Proof.RsaOaep.encrypt_none (by rw [nB_length hi, msgB_length, h.glen]; simp only [fits] at nf; omega)
  rw [en]
  refine ⟨by simp [VG.Arm.RegUpd.gpr_setReg], ?_⟩
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact hz i h1

end VG.Proof.RsaOaep.Arm.Enc
