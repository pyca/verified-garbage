module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Mask
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PubCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  rcases (by omega : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega)]
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
  exact (hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes; omega)).symm

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {P : EP} {σ s : State} {i j : Nat} (ha : A0 h g P σ s i) (hi : i < 10)
    (hj : j < 15) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h g P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  obtain ⟨he, hs⟩ := ha
  have hc := he.1.1
  have hg := he.1.2.1.geo
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine hc.wp_arg hg (enc_arg hj) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega) fun t2 c2 m2 => kk t2 ⟨?_, ?_⟩
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
    (by unfold frameBytes; omega) fun t3 c3 m3 => kk t3 ⟨?_, ?_⟩
  · exact keepE1 h g he hi c3 (by rw [m3.mem, u2.mem, u1.mem])
  · rw [m3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp]
    exact slots_next hs hi _ hv

theorem pubArgs_eq : pubArgs = copyArg 0 0 ++ copyArg 3 1 ++ copyArg 13 2 ++ copyArg 14 3 ++ copyArg 4 4 ++
    copyArg 5 5 ++ (atS .eax oEm ++ [st .eax (4 * 6)]) ++ copyArg 3 7 ++ (atS .eax oRsa ++ [st .eax (4 * 8)]) ++
    [ld .eax (arg 12), .alu .sub .eax (.imm 1024), st .eax (4 * 9)] := by
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
  have z0 : A0 h g P σ s 0 := ⟨hm, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  refine copySlot h g z0 (by decide) (j := 0) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t1 z1 => ?_
  refine copySlot h g z1 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t2 z2 => ?_
  refine copySlot h g z2 (by decide) (j := 13) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t3 z3 => ?_
  refine copySlot h g z3 (by decide) (j := 14) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t4 z4 => ?_
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
  refine c9.wp_arg hg (enc_arg (j := 12) (by decide)) (by decide) (by decide) fun t10 c10 u10 =>
    wp_subi fun t11 u11 _ _ => (c10.upd u11 (by decide) (by decide)).wp_st hg (d := 4 * 9) (by decide)
      fun t12 c12 m12 => WP.block_nil ?_
  have v : t11.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u11.gpr, u10.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) (by omega)
  have m : t12.mem = t9.mem.writeW ((P.lay h.H.D).fr (4 * 9)) (t11.gpr .eax) := by
    rw [m12.mem, u11.mem, u10.mem]
  have sl := slots_next s9 (by decide) _ (v.trans (by simp [outv, pubArgv]))
  rw [← m] at sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨keepE1 h g e9 (i := 9) (by decide) c12 m, fun i hi' => ?_,
    by rw [c12.st.sp]; have : 48 ≤ P.B.toNat := ok.BC; show 44 ≤ P.B.toNat; omega,
    by rw [c12.st.sp]; show P.B.toNat + 40 ≤ _; omega, hi.kv, hi.rlK, hi.el1, hi.elK, hs1.1,
    by have := hi.scl32; omega⟩
  rw [c12.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega)]
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
  have hf := hi.ok.fits P.SCR (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega)] at hf
  have hs := hi.pubScr.2
  have hK := hi.k1024
  have e1 : (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm :=
    addr_eq (by unfold oEm; omega)
  have e2 : (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa :=
    addr_eq (by unfold oRsa; omega)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, hs, hK⟩
  · rw [emR, e1]; exact Offset.sub_base _ (by unfold oEm; omega)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega)
  · rw [emR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega) (by unfold oEm; omega)
      (by unfold oRsa; omega)

theorem eB_at {P : EP} {σ s : State} (hi : In h.H.D P σ) (hs : (P.lay h.H.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- `pre`'s words, in a state of the body. -/
theorem pw_at {P : EP} {σ s : State} (hi : In h.H.D P σ) (hs : (P.lay h.H.D).St σ s) :
    Spec.Rsa.wordsAt s.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hi.ok
  have hR : P.PRE ∈ (P.lay h.H.D).ro := by simp
  have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' hs.frame (fun r hr => ?_) (by omega)).trans hi.pw
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
  have hR : P.PRE ∈ (P.lay h.H.D).ro := by simp
  have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' (hs.callEntry_frame (by show 4 ≤ 48; decide)) (fun r hr => ?_)
    (by omega)).trans (pw_at h hi hs)
  simp only [List.mem_singleton] at hr; subst hr
  exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

theorem emB_length {P : EP} (hf : fits h P) (σ : State) : (emB h g P σ).length = P.K := by
  have hf' : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  have hl := lhB_length h P σ
  simp only [emB, Proof.RsaOaep.emOf, List.length_cons, List.length_append, Proof.Mgf1.xorBytes_length,
    Proof.Mgf1.mgf1_length g.valid, hl, Spec.RsaOaep.zeros, List.length_replicate, seedB, RsaPkcs1Sig.bytesAt_len]
  omega

/-- The masked `EM`, as the call reads it. -/
theorem em_bytes {P : EP} {σ s : State} (hr : E1 h g P σ s) :
    Spec.Rsa.bytesAt s.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K = emB h g P σ := by
  obtain ⟨⟨-, hi, hf⟩, he⟩ := hr
  have hg := hi.geo
  have hK := hi.k1024
  have hl := emB_length h g hf σ
  rw [← hl]
  refine RsaPkcs1Sig.bytesAt_eq fun i hi' => ?_
  rw [hg.scrA (by oomega), sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact he i (by omega)

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
    have dOS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
    have args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.H.D).fr 0, 40⟩ := by simp
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
      have low : Region.Sub (below P.B 44) (P.lay h.H.D).LOW := by
        rw [← ok.low_eq]; exact below_sub (show 44 ≤ 48 by decide) ok.BC
      rw [hsp]
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (ok.low_buf (R := P.OUT) (.inr (by simp))).sub_left low
      · exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS').sub_left low
      · rw [args0]; exact ((Lay.fr_low (by omega) (by show (48 : Nat) ≤ 2 ^ 32; decide)).symm).sub_left low
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
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 40 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega)]
        omega
      · exact ok.fits _ (by simp)
      · exact ok.fits _ (by simp)
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega),
          hg.scr_lt (by decide)]
        unfold oEm; omega
  · -- What the callee is given is ours.
    obtain ⟨⟨⟨hc, hi, -⟩, -⟩, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have hro : ∀ R ∈ (P.lay h.H.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega)⟩
    have hA : Covers [⟨P.B.setWidth 64, 40⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 40) (by simp only [frameBytes]; omega)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have hO : Covers [P.OUT] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hs.inRw (by simp)
    have wr : Covers (pubWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      hO.cons ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega)).cons
        (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    exact (hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons
      ((show Covers [emR P] s.wr by rw [emR, e1]; exact inS (by unfold oEm; omega)).right.cons Covers.nil))
  · rw [hr.1.1.1.st.sp]
    have : 48 ≤ P.B.toNat := hr.1.1.2.1.ok.BC
    have := c.stack
    show _ ≤ P.B.toNat
    omega
  · refine pub_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [pw_at h h₁.1.1.2.1 h₁.1.1.1.st, pw_at h h₂.1.1.2.1 h₂.1.1.1.st]
    · rw [eB_at h h₁.1.1.2.1 h₁.1.1.1.st, eB_at h h₂.1.1.2.1 h₂.1.1.1.st]
    · have ok := h₁.1.1.2.1.ok
      rw [h₁.1.1.1.st.sp]
      exact (ok.low_buf (R := P.PRE) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 44 ≤ 48 by decide) ok.BC)
    · have ok := h₁.1.1.2.1.ok
      rw [h₁.1.1.1.st.sp]
      exact (ok.low_buf (R := P.E) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 44 ≤ 48 by decide) ok.BC)
  · -- After the call.
    obtain ⟨he1, pa⟩ := hr
    obtain ⟨⟨hc, hi, hf⟩, he⟩ := he1
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hfit, hs1, hK⟩ := call_geo h hi
    have low : Region.Sub (below (s.gpr .esp) (stackUse c.code + 4)) (P.lay h.H.D).LOW := by
      rw [hsp, ← ok.low_eq]
      exact below_sub (by have := c.stack; show _ ≤ 48; omega) ok.BC
    have args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.H.D).fr 0, 40⟩ := by simp
    have hw : ∀ r ∈ pubWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024) ++
        [below (s.gpr .esp) (stackUse c.code + 4)], ∃ R ∈ (P.lay h.H.D).W, Region.Sub r R := fun r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨(P.lay h.H.D).FR, by simp, ?_⟩
        rw [args0]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
      · exact ⟨(P.lay h.H.D).LOW, by simp, low⟩
    have st : (P.lay h.H.D).St σ s' := hs.write fr hw rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hi, st⟩, fun hp => ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := pub_post pa po P.nB (nB_length hi) (by rw [callPw h hi hs]; exact hp)
    rw [m₂, g₂ .eax (by decide)] at this
    have eE : Spec.Rsa.bytesAt s.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
      (hs.callEntry_ro (by show 4 ≤ 48; decide) (R := P.E) (by simp)).trans hi.eB
    have eM : Spec.Rsa.bytesAt s.callEntry.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K = emB h g P σ := by
      refine (Proof.RsaPkcs1Sig.bytesAt_frame (hs.callEntry_frame (by show 4 ≤ 48; decide)) (fun r hr => ?_)
        (by omega)).trans (em_bytes h g ⟨⟨hc, hi, hf⟩, he⟩)
      simp only [List.mem_singleton] at hr; subst hr
      exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI).symm
    rw [eE, eM, res_of h g hi hf] at this
    exact this

end VG.Proof.RsaOaep.X86.Enc
