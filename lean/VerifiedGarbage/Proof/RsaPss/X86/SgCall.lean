module

public import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCall
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on x86: the private-key operation

The call's twenty arguments, one word of the frame at a time (`pa_vp`):
`EM` at `scratch + oEm` as the input and the rest of `scratch` from `oRsa`
as the working space; and the call of `vg_rsa_private_checked` (`call_vp`),
whose result is the specification's signature (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  privArgv P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa) P.K
    P.el P.pl P.ql (P.scl - 1024)

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW ((P.lay h.D).fr (4 * i)) 32 = (outv P).getD i 0

/-- During the call's arguments. -/
abbrev A0 (P : EP) (σ s : State) (k : Nat) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ) ∧ Slots h P s.mem k

/-- A word stored below the slots keeps what the encoding left. -/
theorem keepSlot {P : EP} {σ : State} {m : Mem} {d : Nat} (hd : d + 4 ≤ sLo) (v : BitVec 32)
    (hk : Kp h P σ m) (he : EMv P m (emF h P σ)) :
    Kp h P σ (m.writeW ((P.lay h.D).fr d) v) ∧ EMv P (m.writeW ((P.lay h.D).fr d) v) (emF h P σ) := by
  have hg := hk.1.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hk.1.k1024
  have fr := slot_frame (P.lay h.D) m d v
  refine ⟨hk.keep h fr fun r hr => ?_, fun i hi => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact away3_slot (by unfold sLo at hd; unfold frameBytes; omega) (.inl hd)
  · rw [← he i hi]
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (by unfold oEm oRsa; omega)
        (by rw [hg.F]; unfold sLo at hd; unfold frameBytes; omega)).symm _ (Region.contains_self _ _)

theorem slots_next {P : EP} {m : Mem} {i : Nat} (hs : Slots h P m i) (hi : i < 20) (v : BitVec 32)
    (hv : v = (outv P).getD i 0) : Slots h P (m.writeW ((P.lay h.D).fr (4 * i)) v) (i + 1) := by
  intro k hk
  rcases (by omega : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega)]
    exact hs k hki

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {P : EP} {σ s : State} {i j : Nat} (ha : A0 h P σ s i) (hi : i < 20)
    (hj : j < 21) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  obtain ⟨hc, hk, he, hs⟩ := ha
  have hg := hk.1.geo
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine hc.wp_arg hg (sg_arg h hj) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega) fun t2 c2 m2 => kk t2 ⟨c2, ?_⟩
  rw [m2.mem, u1.mem, u1.gpr]
  have kp := keepSlot h (show 4 * i + 4 ≤ sLo by unfold sLo; omega) (P.lay h.D |>.argv.getD j 0) hk he
  exact ⟨kp.1, kp.2, slots_next h hs hi _ hv⟩

/-- `scratch + o` to the call's argument `i`. -/
theorem scrSlot {P : EP} {σ s : State} {i o : Nat} (ha : A0 h P σ s i) (hi : i < 20)
    (hv : P.scr + BitVec.ofNat 32 o = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (atS .eax o ++ [st .eax (4 * i)] ++ is)) s Q := by
  obtain ⟨hc, hk, he, hs⟩ := ha
  have hg := hk.1.geo
  simp only [atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (d := 4 * i)
    (by unfold frameBytes; omega) fun t3 c3 m3 => kk t3 ⟨c3, ?_⟩
  rw [m3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp]
  have kp := keepSlot h (show 4 * i + 4 ≤ sLo by unfold sLo; omega) (P.scr + BitVec.ofNat 32 o) hk he
  exact ⟨kp.1, kp.2, slots_next h hs hi _ hv⟩

theorem privArgs_eq : privArgs = copyArg 0 0 ++ copyArg 3 1 ++ copyArg 2 2 ++ copyArg 3 3 ++ copyArg 4 4 ++
    copyArg 5 5 ++ (atS .eax oEm ++ [st .eax (4 * 6)]) ++ copyArg 3 7 ++ copyArg 6 8 ++ copyArg 7 9 ++
    copyArg 8 10 ++ copyArg 9 11 ++ copyArg 10 12 ++ copyArg 7 13 ++ copyArg 12 14 ++ copyArg 9 15 ++
    copyArg 14 16 ++ copyArg 7 17 ++ (atS .eax oRsa ++ [st .eax (4 * 18)]) ++
    [ld .eax (arg 20), .alu .sub .eax (.imm 1024), st .eax (4 * 19)] := by
  simp only [privArgs, List.append_assoc]; rfl

/-- Before the call. -/
abbrev R1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ) ∧
    PrivArgs s P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024)

theorem pa_vp (P : EP) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ)) (.block privArgs)
      (R1 h P) := by
  refine VP.taint [.esp, .ebp] privArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hs1 : 1024 ≤ P.scl := by
    have := hi.slK; unfold Spec.RsaPss.scratchWords at this; omega
  rw [privArgs_eq]
  simp only [List.append_assoc]
  have z0 : A0 h P σ s 0 := ⟨hc, hk, he, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  refine copySlot h z0 (by decide) (j := 0) (by decide) (by simp [EP.argv, outv, privArgv]) fun t1 z1 => ?_
  refine copySlot h z1 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, privArgv]) fun t2 z2 => ?_
  refine copySlot h z2 (by decide) (j := 2) (by decide) (by simp [EP.argv, outv, privArgv]) fun t3 z3 => ?_
  refine copySlot h z3 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, privArgv]) fun t4 z4 => ?_
  refine copySlot h z4 (by decide) (j := 4) (by decide) (by simp [EP.argv, outv, privArgv]) fun t5 z5 => ?_
  refine copySlot h z5 (by decide) (j := 5) (by decide) (by simp [EP.argv, outv, privArgv]) fun t6 z6 => ?_
  rw [← List.append_assoc (atS .eax oEm)]
  refine scrSlot h z6 (by decide) (by simp [outv, privArgv]) fun t7 z7 => ?_
  refine copySlot h z7 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, privArgv]) fun t8 z8 => ?_
  refine copySlot h z8 (by decide) (j := 6) (by decide) (by simp [EP.argv, outv, privArgv]) fun t9 z9 => ?_
  refine copySlot h z9 (by decide) (j := 7) (by decide) (by simp [EP.argv, outv, privArgv]) fun t10 z10 => ?_
  refine copySlot h z10 (by decide) (j := 8) (by decide) (by simp [EP.argv, outv, privArgv]) fun t11 z11 => ?_
  refine copySlot h z11 (by decide) (j := 9) (by decide) (by simp [EP.argv, outv, privArgv]) fun t12 z12 => ?_
  refine copySlot h z12 (by decide) (j := 10) (by decide) (by simp [EP.argv, outv, privArgv]) fun t13 z13 => ?_
  refine copySlot h z13 (by decide) (j := 7) (by decide) (by simp [EP.argv, outv, privArgv]) fun t14 z14 => ?_
  refine copySlot h z14 (by decide) (j := 12) (by decide) (by simp [EP.argv, outv, privArgv]) fun t15 z15 => ?_
  refine copySlot h z15 (by decide) (j := 9) (by decide) (by simp [EP.argv, outv, privArgv]) fun t16 z16 => ?_
  refine copySlot h z16 (by decide) (j := 14) (by decide) (by simp [EP.argv, outv, privArgv]) fun t17 z17 => ?_
  refine copySlot h z17 (by decide) (j := 7) (by decide) (by simp [EP.argv, outv, privArgv]) fun t18 z18 => ?_
  rw [← List.append_assoc (atS .eax oRsa)]
  refine scrSlot h z18 (by decide) (by simp [outv, privArgv]) fun t19 z19 => ?_
  obtain ⟨c19, k19, e19, s19⟩ := z19
  simp only [ld, st]
  refine c19.wp_arg hg (sg_arg h (j := 20) (by decide)) (by decide) (by decide) fun t20 c20 u20 =>
    wp_subi fun t21 u21 _ _ => (c20.upd u21 (by decide) (by decide)).wp_st hg (d := 4 * 19) (by decide)
      fun t22 c22 m22 => WP.block_nil ?_
  have v : t21.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u21.gpr, u20.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) hs1
  have kp := keepSlot h (show 4 * 19 + 4 ≤ sLo by decide) (t21.gpr .eax) k19 e19
  have sl := slots_next h s19 (by decide) _ (v.trans (by simp [outv, privArgv]))
  have m : t22.mem = t19.mem.writeW ((P.lay h.D).fr (4 * 19)) (t21.gpr .eax) := by
    rw [m22.mem, u21.mem, u20.mem]
  rw [← m] at kp sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨c22, kp.1, kp.2, fun i hi' => ?_, by rw [c22.st.sp]; exact ok.BC, by rw [c22.st.sp]; show P.B.toNat + 80 ≤ _; omega, hi.kv,
    hi.el1, hi.elK, hi.pl1, hi.plK, hi.ql1, hi.qlK, ?_, by have := hi.scl32; omega⟩
  · rw [c22.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega)]
    exact sl i hi'
  · have hs := hi.slK; unfold Spec.RsaPss.scratchWords at hs; omega

/-- What the specification signs: RSASP1 of `EM`, checked against `e`. -/
theorem sign_ok {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    Spec.RsaPss.sign h.G h.G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ) (saltB P σ) =
      Spec.Rsa.privateChecked P.nB P.eB ((List.range P.K).map (emF h P σ)) (pB P σ) (qB P σ) (dpB P σ)
        (dqB P σ) (qiB P σ) := by
  have hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hn0 : n0 P = b := by simp [n0, hbr]
  have hb0 : b ≠ 0 := fun e => hf.1 (by rw [hn0, e])
  have e1 := lo_eq hb0 rest
  have e2 := RsaPss.emLength_eq rest hb0
  have gl : h.G.len = h.D := h.glen
  have hsl := hf.2
  have hlo : lo P = if b.toNat ≤ 1 then 1 else 0 := by unfold lo; rw [hn0]
  rw [hbr, List.length_cons] at hl
  rw [List.length_cons] at e1
  have hbt : b.toNat ≠ 0 := fun e => hb0 (BitVec.eq_of_toNat_eq e)
  have hem : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) = P.K - lo P := by
    rw [hlo]
    by_cases hb1 : b.toNat = 1
    · rw [ite_eq_left hb1] at e2; rw [ite_eq_left (by omega)]; all_goals omega
    · rw [ite_eq_right hb1] at e2; rw [ite_eq_right (by have := b.isLt; omega)]; all_goals omega
  have hlo1 : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) - h.G.len - 1 =
      dbN h P := by
    rw [hem, gl]
  have hm : (digB h P σ).length = h.G.len := by rw [gl]; exact RsaPkcs1Sig.bytesAt_len _ _ _
  have hfit : h.G.len + (saltB P σ).length + 2 ≤
      Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) := by
    rw [gl, RsaPkcs1Sig.bytesAt_len, hem]; have := hf.2; omega
  rw [hbr, RsaPss.sign_eq h.G (PssHash.valid h) hb0 hm rfl rfl e1 hdb hfit]
  refine congrArg (fun em => Spec.Rsa.privateChecked (b :: rest) P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ)
    (qiB P σ)) ?_
  rw [List.length_cons, show rest.length + 1 = P.K by omega]
  refine congrArg (fun f => List.map f (List.range P.K)) (funext fun i => ?_)
  have hc := cW_byte hb0 rest
  unfold emF mkS Hs xB
  rw [hn0, ← hlo, ← hc, RsaPkcs1Sig.bytesAt_len, h.hash]

/-- The call's input and working space, in `scratch`. -/
abbrev inpR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oEm).setWidth 64, P.K⟩
abbrev scrR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oRsa).setWidth 64, (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In h.D P σ) :
    (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm ∧
    (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa ∧
    Region.Sub (inpR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (inpR P).Disjoint (scrR P) ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1024 ≤ P.scl ∧ P.K ≤ 1024 := by
  have hf := hi.ok.fits P.SCR (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega)] at hf
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  have hK := hi.k1024
  have e1 : (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm :=
    addr_eq (by unfold oEm; omega)
  have e2 : (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa :=
    addr_eq (by unfold oRsa; omega)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, by omega, hK⟩
  · rw [inpR, e1]; exact Offset.sub_base _ (by unfold oEm; omega)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega)
  · rw [inpR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega) (by unfold oEm; omega)
      (by unfold oRsa; omega)

theorem nB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- The name of `vg_rsa_private_checked` over `v`. -/
def privName (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix

/-- `out` and the result: the call. -/
theorem call_vp (P : EP) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (R1 h P) (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (Fin h P) := by
  have hv := Proof.Rsa.X86.PrivChecked.code_verified v
  have hst := Proof.Rsa.X86.PrivChecked.code_stack v
  refine VP.call hv.1 hv.2.1 (Proof.Rsa.X86.PrivChecked.privateCode_noSp v)
    (privRd P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun σ s hr => ?_) (fun σ s hr => ?_)
    (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.st.sp, h₂.1.st.sp])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr cs fr po => ?_)
  · -- The callee's precondition.
    obtain ⟨hc, hk, -, pa⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have fit := ok.fit
    simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at fit
    have oS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
    have args0 : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨(P.lay h.D).fr 0, 80⟩ := by simp
    have hsp := hc.st.sp
    rw [show (P.lay h.D).B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    refine priv_pre pa ?_ ?_ ?_ ?_
    · intro w hw r hr
      simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
      · exact oS.sub_right sI
      · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
      · exact (ok.rw_ro (w := P.SCR) (r := P.N) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
      · exact dIS.symm
      · exact (ok.rw_ro (w := P.SCR) (r := P.PP) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.QQ) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.DP) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.DQ) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.QI) (by simp) (by simp)).sub_left sS'
      all_goals rw [args0]
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 80 ≤ frameBytes + 16; decide)
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 80 ≤ frameBytes + 16; decide)
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by show 0 + 80 ≤ frameBytes + 16; decide)).sub_right sI
      all_goals exact ok.stk_fr (.inl (by simp)) (by show 0 + 80 ≤ frameBytes + 16; decide)
    · simp only [privWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨oS.sub_right sS', ?_⟩, ?_, fun _ h => h.elim⟩
      · rw [args0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show 0 + 80 ≤ frameBytes + 16; decide)).symm
      · rw [args0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 80 ≤ frameBytes + 16; decide)).symm).sub_left sS'
    · intro r hr
      rw [hsp, ← show (P.lay h.D).B = P.B from rfl, ok.low_eq]
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
      · rw [args0]; exact (Lay.fr_low (by omega) (by show (3392 : Nat) ≤ 2 ^ 32; decide)).symm
      · exact ok.low_buf (.inl (by simp))
      · exact ok.low_buf (.inl (by simp))
      · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
      all_goals exact ok.low_buf (.inl (by simp))
    · intro r hr
      have hg := hi.geo
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · show ((P.scr + BitVec.ofNat 32 oRsa).setWidth 64).toNat + (P.scl - 1024) * 8 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 80 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega)]
        omega
      · exact ok.fits _ (by simp)
      · exact ok.fits _ (by simp)
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega),
          hg.scr_lt (by decide)]
        unfold oEm; omega
      all_goals exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    obtain ⟨hc, hk, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    have hrw : ∀ R ∈ (P.lay h.D).rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRw hR
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega)⟩
    have hA : Covers [⟨P.B.setWidth 64, 80⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 80) (by simp only [frameBytes]; omega)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (privWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      (hrw P.OUT (by simp)).cons ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    refine (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((show Covers [inpR P] (s.rd ++ s.wr) by rw [inpR, e1]; exact (inS (by unfold oEm; omega)).right).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons Covers.nil)))))))
  · rw [hr.1.st.sp]
    have : 3392 ≤ P.B.toNat := hr.2.1.1.ok.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    show _ ≤ P.B.toNat
    omega
  · refine priv_pub h₁.2.2.2 h₂.2.2.2 (by rw [h₁.1.st.sp, h₂.1.st.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [nB_at h h₁.2.1.1 h₁.1.st, nB_at h h₂.2.1.1 h₂.1.st]
    · rw [eB_at h h₁.2.1.1 h₁.1.st, eB_at h h₂.2.1.1 h₂.1.st]
    · rw [h₁.1.st.sp, h₁.2.1.1.ok.low_eq]
      exact h₁.2.1.1.ok.low_buf (R := P.N) (.inl (by simp))
    · rw [h₁.1.st.sp, h₁.2.1.1.ok.low_eq]
      exact h₁.2.1.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    obtain ⟨hc, hk, he, pa⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have low : Region.Sub (below (s.gpr .esp) (stackUse (Proof.Rsa.X86.PrivChecked.privCode v) + 4))
        (P.lay h.D).LOW := by
      rw [hsp, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega) ok.BC
    have st : (P.lay h.D).St σ s' := hs.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨(P.lay h.D).FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨(P.lay h.D).fr 0, 80⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
      · exact ⟨(P.lay h.D).LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hi, st⟩, ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_post pa po
    rw [m₂, g₂ .eax (by decide)] at this
    have ro := fun {R : Region} (hR : R ∈ (P.lay h.D).ro) => hs.callEntry_ro (by show 4 ≤ 3392; decide) hR
    have hg := hi.geo
    have em : Spec.Rsa.bytesAt s.callEntry.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K =
        (List.range P.K).map (emF h P σ) := by
      rw [RsaPkcs1Sig.bytesAt_frame (hs.callEntry_frame (by show 4 ≤ 3392; decide)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (ok.low_buf (R := P.SCR) (.inr (by simp))).symm.sub_left sI)
        (by omega)]
      unfold Spec.Rsa.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      rw [List.mem_range] at hi'
      rw [← he i hi', e1, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [ro (R := P.N) (by simp), hi.nB, ro (R := P.E) (by simp), hi.eB, em,
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    rw [Res, sign_ok h hi hk.2.1]
    exact this

end VG.Proof.RsaPss.X86.Sg
