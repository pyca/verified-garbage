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
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MdHashTable.X86.Tables
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSpT
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! ### `RsaPss.X86.SgCall`, which only this module used -/

section

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

variable (h : PssHash) (G : Spec.Mgf1.Hash)

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  privArgv P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa) P.K
    P.el P.pl P.ql (P.scl - 1024)

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW ((P.lay h.D).fr (4 * i)) 32 = (outv P).getD i 0

/-- What the call needs of the checks: the parameters' slots are the call's
arguments now. -/
abbrev Kq (P : EP) (σ : State) (_m : Mem) : Prop := In h.D P σ ∧ fits h P ∧ True

/-- During the call's arguments. -/
abbrev A0 (P : EP) (σ s : State) (k : Nat) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ Kq h P σ s.mem ∧ EMv P s.mem (emF h G P σ) ∧ Slots h P s.mem k

/-- A word stored below the slots keeps what the encoding left. -/
theorem keepSlot {P : EP} {σ : State} {m : Mem} {d : Nat} (hd : d + 4 ≤ 80) (v : BitVec 32)
    (hk : Kq h P σ m) (he : EMv P m (emF h G P σ)) :
    Kq h P σ (m.writeW ((P.lay h.D).fr d) v) ∧ EMv P (m.writeW ((P.lay h.D).fr d) v) (emF h G P σ) := by
  have hg := hk.1.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hk.1.k1024
  have fr := slot_frame (P.lay h.D) m d v
  refine ⟨hk, fun i hi => ?_⟩
  · rw [← he i hi]
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (by unfold oEm oRsa; omega_arith)
        (by rw [hg.F]; unfold frameBytes; omega_arith)).symm _ (Region.contains_self _ _)

theorem slots_next {P : EP} {m : Mem} {i : Nat} (hs : Slots h P m i) (hi : i < 20) (v : BitVec 32)
    (hv : v = (outv P).getD i 0) : Slots h P (m.writeW ((P.lay h.D).fr (4 * i)) v) (i + 1) := by
  intro k hk
  rcases (by omega_arith : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hs k hki

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {P : EP} {σ s : State} {i j : Nat} (ha : A0 h G P σ s i) (hi : i < 20)
    (hj : j < 24) (hv : (P.argv h.D).getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h G P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  obtain ⟨hc, hk, he, hs⟩ := ha
  have hg := hk.1.geo
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine hc.wp_arg hg (sg_arg h hj) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega_arith) fun t2 c2 m2 => kk t2 ⟨c2, ?_⟩
  rw [m2.mem, u1.mem, u1.gpr]
  have kp := keepSlot h G (show 4 * i + 4 ≤ 80 by omega_arith) ((P.lay h.D).argv.getD j 0) hk he
  exact ⟨kp.1, kp.2, slots_next h hs hi _ hv⟩

/-- `scratch + o` to the call's argument `i`. -/
theorem scrSlot {P : EP} {σ s : State} {i o : Nat} (ha : A0 h G P σ s i) (hi : i < 20)
    (hv : P.scr + BitVec.ofNat 32 o = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h G P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (atS .eax o ++ [st .eax (4 * i)] ++ is)) s Q := by
  obtain ⟨hc, hk, he, hs⟩ := ha
  have hg := hk.1.geo
  simp only [atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (d := 4 * i)
    (by unfold frameBytes; omega_arith) fun t3 c3 m3 => kk t3 ⟨c3, ?_⟩
  rw [m3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp]
  have kp := keepSlot h G (show 4 * i + 4 ≤ 80 by omega_arith) (P.scr + BitVec.ofNat 32 o) hk he
  exact ⟨kp.1, kp.2, slots_next h hs hi _ hv⟩

theorem privArgs_eq : privArgs = copyArg 0 0 ++ copyArg 3 1 ++ copyArg 2 2 ++ copyArg 3 3 ++ copyArg 4 4 ++
    copyArg 5 5 ++ (atS .eax oEm ++ [st .eax (4 * 6)]) ++ copyArg 3 7 ++ copyArg 6 8 ++ copyArg 7 9 ++
    copyArg 8 10 ++ copyArg 9 11 ++ copyArg 10 12 ++ copyArg 7 13 ++ copyArg 12 14 ++ copyArg 9 15 ++
    copyArg 14 16 ++ copyArg 7 17 ++ (atS .eax oRsa ++ [st .eax (4 * 18)]) ++
    [ld .eax (arg 21), .alu .sub .eax (.imm 1024), st .eax (4 * 19)] := by
  simp only [privArgs, List.append_assoc]; rfl

/-- Before the call. -/
abbrev R1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ Kq h P σ s.mem ∧ EMv P s.mem (emF h G P σ) ∧
    PrivArgs s P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024)

theorem pa_vp (P : EP) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ)) (.block privArgs)
      (R1 h G P) := by
  refine VP.taint [.esp, .ebp] privArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hs1 : 1024 ≤ P.scl := by
    have := hi.slK; unfold Spec.RsaPss.scratchWords at this; omega_arith
  rw [privArgs_eq]
  simp only [List.append_assoc]
  have z0 : A0 h G P σ s 0 := ⟨hc, ⟨hk.1, hk.2.1, trivial⟩, he, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  refine copySlot h G z0 (by decide) (j := 0) (by decide) (by simp [EP.argv, outv, privArgv]) fun t1 z1 => ?_
  refine copySlot h G z1 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, privArgv]) fun t2 z2 => ?_
  refine copySlot h G z2 (by decide) (j := 2) (by decide) (by simp [EP.argv, outv, privArgv]) fun t3 z3 => ?_
  refine copySlot h G z3 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, privArgv]) fun t4 z4 => ?_
  refine copySlot h G z4 (by decide) (j := 4) (by decide) (by simp [EP.argv, outv, privArgv]) fun t5 z5 => ?_
  refine copySlot h G z5 (by decide) (j := 5) (by decide) (by simp [EP.argv, outv, privArgv]) fun t6 z6 => ?_
  rw [← List.append_assoc (atS .eax oEm)]
  refine scrSlot h G z6 (by decide) (by simp [outv, privArgv]) fun t7 z7 => ?_
  refine copySlot h G z7 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, privArgv]) fun t8 z8 => ?_
  refine copySlot h G z8 (by decide) (j := 6) (by decide) (by simp [EP.argv, outv, privArgv]) fun t9 z9 => ?_
  refine copySlot h G z9 (by decide) (j := 7) (by decide) (by simp [EP.argv, outv, privArgv]) fun t10 z10 => ?_
  refine copySlot h G z10 (by decide) (j := 8) (by decide) (by simp [EP.argv, outv, privArgv]) fun t11 z11 => ?_
  refine copySlot h G z11 (by decide) (j := 9) (by decide) (by simp [EP.argv, outv, privArgv]) fun t12 z12 => ?_
  refine copySlot h G z12 (by decide) (j := 10) (by decide) (by simp [EP.argv, outv, privArgv]) fun t13 z13 => ?_
  refine copySlot h G z13 (by decide) (j := 7) (by decide) (by simp [EP.argv, outv, privArgv]) fun t14 z14 => ?_
  refine copySlot h G z14 (by decide) (j := 12) (by decide) (by simp [EP.argv, outv, privArgv]) fun t15 z15 => ?_
  refine copySlot h G z15 (by decide) (j := 9) (by decide) (by simp [EP.argv, outv, privArgv]) fun t16 z16 => ?_
  refine copySlot h G z16 (by decide) (j := 14) (by decide) (by simp [EP.argv, outv, privArgv]) fun t17 z17 => ?_
  refine copySlot h G z17 (by decide) (j := 7) (by decide) (by simp [EP.argv, outv, privArgv]) fun t18 z18 => ?_
  rw [← List.append_assoc (atS .eax oRsa)]
  refine scrSlot h G z18 (by decide) (by simp [outv, privArgv]) fun t19 z19 => ?_
  obtain ⟨c19, k19, e19, s19⟩ := z19
  simp only [ld, st]
  refine c19.wp_arg hg (sg_arg h (j := 21) (by decide)) (by decide) (by decide) fun t20 c20 u20 =>
    wp_subi fun t21 u21 _ _ => (c20.upd u21 (by decide) (by decide)).wp_st hg (d := 4 * 19) (by decide)
      fun t22 c22 m22 => WP.block_nil ?_
  have v : t21.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u21.gpr, u20.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) hs1
  have kp := keepSlot h G (show 4 * 19 + 4 ≤ 80 by decide) (t21.gpr .eax) k19 e19
  have sl := slots_next h s19 (by decide) _ (v.trans (by simp [outv, privArgv]))
  have m : t22.mem = t19.mem.writeW ((P.lay h.D).fr (4 * 19)) (t21.gpr .eax) := by
    rw [m22.mem, u21.mem, u20.mem]
  rw [← m] at kp sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨c22, kp.1, kp.2, fun i hi' => ?_, by rw [c22.st.sp]; exact ok.BC, by rw [c22.st.sp]; show P.B.toNat + 80 ≤ _; omega_arith, hi.kv,
    hi.el1, hi.elK, hi.pl1, hi.plK, hi.ql1, hi.qlK, ?_, by have := hi.scl32; omega_arith⟩
  · rw [c22.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega_arith)]
    exact sl i hi'
  · have hs := hi.slK; unfold Spec.RsaPss.scratchWords at hs; omega_arith

/-- What the specification signs: RSASP1 of `EM`, checked against `e`. -/
theorem sign_ok (hG : Proof.Mgf1.Valid G) {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    Spec.RsaPss.sign h.G G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ) (saltB P σ) =
      Spec.Rsa.privateChecked P.nB P.eB ((List.range P.K).map (emF h G P σ)) (pB P σ) (qB P σ) (dpB P σ)
        (dqB P σ) (qiB P σ) := by
  have hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega_arith
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
    · rw [ite_eq_left hb1] at e2; rw [ite_eq_left (by omega_arith)]; all_goals omega_arith
    · rw [ite_eq_right hb1] at e2; rw [ite_eq_right (by have := b.isLt; omega_arith)]; all_goals omega_arith
  have hlo1 : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) - h.G.len - 1 =
      dbN h P := by
    rw [hem, gl]
  have hm : (digB h P σ).length = h.G.len := by rw [gl]; exact RsaPkcs1Sig.bytesAt_len _ _ _
  have hfit : h.G.len + (saltB P σ).length + 2 ≤
      Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) := by
    rw [gl, RsaPkcs1Sig.bytesAt_len, hem]; have := hf.2; omega_arith
  rw [hbr, RsaPss.sign_eq₂ G h.G (PssHash.valid h) hG hb0 hm rfl rfl e1 hdb hfit]
  refine congrArg (fun em => Spec.Rsa.privateChecked (b :: rest) P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ)
    (qiB P σ)) ?_
  rw [List.length_cons, show rest.length + 1 = P.K by omega_arith]
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
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_arith)] at hf
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  have hK := hi.k1024
  have e1 : (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm :=
    addr_eq (by unfold oEm; omega_arith)
  have e2 : (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa :=
    addr_eq (by unfold oRsa; omega_arith)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, by omega_arith, hK⟩
  · rw [inpR, e1]; exact Offset.sub_base _ (by unfold oEm; omega_arith)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega_arith)
  · rw [inpR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega_arith) (by unfold oEm; omega_arith)
      (by unfold oRsa; omega_arith)

theorem nB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- The name of `vg_rsa_private_checked` over `v`. -/
def privName (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : String := "vg_rsa_private_checked" ++ v.suffix

/-- `out` and the result: the call. -/
theorem call_vp (hG : Proof.Mgf1.Valid G) (P : EP) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (R1 h G P) (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (Fin h G P) := by
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
      · rw [args0]; exact (Lay.fr_low (by omega_arith) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).symm
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
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega_arith),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega_arith
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 80 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_arith)]
        omega_arith
      · exact ok.fits _ (by simp)
      · exact ok.fits _ (by simp)
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega_arith),
          hg.scr_lt (by decide)]
        unfold oEm; omega_arith
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
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega_arith)⟩
    have hA : Covers [⟨P.B.setWidth 64, 80⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 80) (by simp only [frameBytes]; omega_arith)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (privWr P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      (hrw P.OUT (by simp)).cons ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega_arith)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    refine (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((show Covers [inpR P] (s.rd ++ s.wr) by rw [inpR, e1]; exact (inS (by unfold oEm; omega_arith)).right).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons Covers.nil)))))))
  · rw [hr.1.st.sp]
    have : 3448 ≤ P.B.toNat := hr.2.1.1.ok.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    show _ ≤ P.B.toNat
    omega_arith
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
      exact below_sub (by simp only; omega_arith) ok.BC
    have st : (P.lay h.D).St σ s' := hs.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨(P.lay h.D).FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨(P.lay h.D).fr 0, 80⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨(P.lay h.D).LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hi, st⟩, ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_post pa po
    rw [m₂, g₂ .eax (by decide)] at this
    have ro := fun {R : Region} (hR : R ∈ (P.lay h.D).ro) => hs.callEntry_ro (by show 4 ≤ 3448; decide) hR
    have hg := hi.geo
    have em : Spec.Rsa.bytesAt s.callEntry.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K =
        (List.range P.K).map (emF h G P σ) := by
      rw [RsaPkcs1Sig.bytesAt_frame (hs.callEntry_frame (by show 4 ≤ 3448; decide)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (ok.low_buf (R := P.SCR) (.inr (by simp))).symm.sub_left sI)
        (by omega_arith)]
      unfold Spec.Rsa.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      rw [List.mem_range] at hi'
      rw [← he i hi', e1, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [ro (R := P.N) (by simp), hi.nB, ro (R := P.E) (by simp), hi.eB, em,
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    rw [Res, sign_ok h G hG hi hk.2.1]
    exact this

end VG.Proof.RsaPss.X86.Sg

end

end


/-!
# RSASSA-PSS signing on x86: verified

As on ARMv7 (`Proof/RsaPss/Arm/SgVerified.lean`), with the hash functions as
tables: the checks, then zeros or the encoding and the private-key
operation (`tail_vp`), for the hash function `h` of the table of `MdHash` at
the argument 22 and MGF1's `g` of the table of `MdHash` at 23; the index of
`h` (the table's word 5, `idx_vp`) chooses that tail among those of `idxs`
(`body_vp`, by `Proof.RsaOaep.X86.byLen_vp`), whose code for the index is
that for `h`'s sizes (`Shape`). The body writes `esp` only through the frames
of its calls (`body_noSp`); with the frames around it (`wrap_ok`, `wrap_ct`)
and the result as the shared contract states it, for the variants `w` and
`wg` whose tables the arguments are (`held_entered`, `tabFacts_entered`):
`vg_rsa_pss_sign`, calling `vg_rsa_private_checked` over `v`, with the hash
function any of the tables of `vs` and MGF1's any of those of `gs`, is
verified (`sign_verified`), given a state that meets the contract
(`SgSat.lean`). Every stage keeps the addresses of the statics (`VP.syms`),
which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)
open VG.Impl.RsaOaep.X86 (Fns byLen)
open VG.Proof.RsaOaep.X86 (OHash TabFacts VP.syms byLen_vp byLen_noSp St_roW)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

variable (h : PssHash)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- The checks, then zeros or the encoding and the private-key operation,
for the hash function `h` of the table at the argument 22 and MGF1's `g` of
that at 23. -/
theorem tail_vp (P : EP) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (v : CrtImpl) :
    VP (Sy (S h P)) (signTail f h.H fG (privName v) (privCode v)) (Fin h g.G P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  show VP _ (.seq (.block (signChk ++ params h.H)) (.ite .ne signFail (.seq (signEncT f h.H fG)
    (.seq (.block privArgs) (.call (privName v) (privCode v)))))) _
  exact (VP.syms (chk_vp h P)).seq (VP.ite
    (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.1.2.2.2.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((fail_vp h g.G P).mono (fun σ s ⟨⟨h1, _⟩, e⟩ => ⟨h1, e⟩) fun _ _ h => h)
    (((enc_vp h P hP hTH fneH g hT fne).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨e0_of h h1 e, sy⟩)
      fun _ _ h => h.1).seq ((pa_vp h g.G P).seq (call_vp h g.G g.valid P v))))

/-- The index of the hash function of the table at the argument 22, to
`edx`. -/
theorem idx_vp (P : EP) {ix : Nat} (hix : ∀ σ, P.TH σ → σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix) :
    VP (Sy (S h P)) (.block (idxLoad 22)) (fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = BitVec.ofNat 32 ix) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.tblH5
  show VP _ (.block ([ld .edx (arg 22)] ++ [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 20))])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = P.tabH)
    (VP.taint [.esp] idxArg22_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] idxWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.sp, h₂.1.2.sp]
  · obtain ⟨⟨hi, hs⟩, sy⟩ := hs
    simp only [ld]
    refine hs.wp_arg (sg_arg h (j := 22) (by decide)) (by decide) fun t1 s1 u1 => WP.block_nil
      ⟨⟨⟨hi, s1⟩, u1.syms.trans sy⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.2.sp, h₂.1.1.2.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨⟨hi, hs⟩, sy⟩, hdx⟩ := hs
    have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabH 20) 4 := ⟨tR, hs.inRo tRo, tC⟩
    refine wp_ldm (B := P.tabH) hdx hin fun t2 u2 => WP.block_nil ⟨⟨⟨hi, hs.upd u2 (by decide)⟩, u2.syms.trans sy⟩, ?_⟩
    rw [u2.gpr, St_roW hs tRo tC, hix σ hi.tabTH]

/-- The tail for an index is that for the sizes of its hash function. -/
theorem tail_eq {i : Nat} {f : MdFns} {fG : Fns} {pn : String} {pc : Prog isa}
    (hs : sizes h.H = sizesOf i) (pa : List Instr := privArgs) :
    signTail f (ofIdx i) fG pn pc pa = signTail f h.H fG pn pc pa := by
  rw [show ofIdx i = ofSizes (sizes h.H) by rw [hs]; rfl]
  rfl

/-- The body, for the hash function `h` of index `ix` and MGF1's `g`. -/
theorem body_vp (P : EP) {dn : String} {f : MdFns} {ix : Nat} (hix₀ : ix ∈ idxs) (hs : sizes h.H = sizesOf ix)
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ ∧
      σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (v : CrtImpl) :
    VP (Sy (S h P)) (signBodyT f fG (privName v) (privCode v)) (Fin h g.G P) := by
  have hlt : ix < 2 ^ 32 := (cmpIdxs_taint ix hix₀).1
  show VP _ (.seq (.block (idxLoad 22)) (byLen (fun i => signTail f (ofIdx i) fG (privName v) (privCode v)) idxs)) _
  refine (idx_vp h P fun σ hσ => (hTH σ hσ).2).seq (byLen_vp (D := ix) hlt (fun _ _ hs => hs.2)
    (fun σ s t ⟨⟨⟨hi, hs⟩, sy⟩, dx⟩ fu sy' => ⟨⟨⟨hi, hs.fupd fu⟩, sy'.trans sy⟩, by rw [fu.gpr]; exact dx⟩) ?_ hix₀
    cmpIdxs_taint)
  rw [tail_eq h hs]
  exact (tail_vp h P (fun σ hσ => (hTH σ hσ).1) fneH g hT fne v).mono (fun _ _ hs => hs.1) fun _ _ h => h

/-! ## The stack -/

theorem tail_noSp {f : MdFns} (hi : ∀ q ∈ f.init, NoSp q.2) (hc : ∀ q ∈ f.comp, NoSp q.2)
    (hd : ∀ q ∈ f.dig, NoSp q.2) {fG : Fns} (gi : ∀ q ∈ fG.init, NoSp q.2) (gu : ∀ q ∈ fG.upd, NoSp q.2)
    (gf : ∀ q ∈ fG.fin, NoSp q.2) (v : CrtImpl) : NoSp (signTail f h.H fG (privName v) (privCode v)) := by
  have sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig16
  have p3 := sp.cpSalt
  have p4 := sp.lenArgs19
  have p5 := sp.putH
  have p6 := sp.mgfArgs
  have hct := ctHashT_noSp h hi hc hd (j := 22) (NoSp.of_all (by decide +kernel))
  have hm := Proof.RsaOaep.X86.mgfX_noSp gi gu gf (j := 23) (NoSp.of_all (by decide +kernel))
  have hp := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  simp only [signTail, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [signEncT, yDig, signFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

/-- `vs`' and `gs`' functions write `esp` only through their frames. -/
structure FnsSp (f : MdFns) (fG : Fns) : Prop where
  hi : ∀ q ∈ f.init, NoSp q.2
  hc : ∀ q ∈ f.comp, NoSp q.2
  hd : ∀ q ∈ f.dig, NoSp q.2
  gi : ∀ q ∈ fG.init, NoSp q.2
  gu : ∀ q ∈ fG.upd, NoSp q.2
  gf : ∀ q ∈ fG.fin, NoSp q.2

theorem body_noSp {f : MdFns} {fG : Fns} (hf : FnsSp f fG) (hall : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i)
    (v : CrtImpl) : NoSp (signBodyT f fG (privName v) (privCode v)) := by
  refine noSp_seq (NoSp.of_all (by decide +kernel)) (byLen_noSp fun i hi => ?_)
  obtain ⟨h', hs⟩ := hall i hi
  rw [tail_eq h' hs]
  exact tail_noSp h' hf.hi hf.hc hf.hd hf.gi hf.gu hf.gf v

/-! ## The entry -/

/-- What the registration checks of the variants `vs` of the tables of
`MdHash` and `gs` of `MdHash`: the functions of one name have one code, each
hash function has the sizes of its index, each index has a variant, and few
enough functions for the contract's satisfiability. -/
def OK (vs : List MVar) (gs : List TVar) : Prop :=
  Proof.MdHashTable.X86.Coh vs ∧ (∀ w ∈ vs, Proof.MdHashTable.X86.Shape w) ∧ Proof.HashTable.X86.Coh gs ∧
    (∀ i ∈ idxs, ∃ w ∈ vs, Proof.MdHashTable.X86.idx w = i) ∧ gs ≠ [] ∧
    (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24

instance (vs : List MVar) (gs : List TVar) : Decidable (OK vs gs) := by unfold OK; infer_instance

variable {vs : List MVar} {gs : List TVar}

/-- The code, calling `vg_rsa_private_checked` over `v`, with the hash
function any of the tables of `vs` and MGF1's any of `gs`. -/
abbrev signCode (vs : List MVar) (gs : List TVar) (v : CrtImpl) : Prog isa :=
  sign (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs) (privName v) (privCode v)

/-- The contract, with those tables. -/
abbrev sspec (vs : List MVar) (gs : List TVar) : Contract isa :=
  spec (Proof.MdHashTable.X86.tables vs) (Proof.HashTable.X86.tables gs)

theorem fnsSp (vs : List MVar) (gs : List TVar) :
    FnsSp (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs) := by
  obtain ⟨gi, gu, gf⟩ := Proof.HashTable.X86.fnsOf_noSp gs
  refine ⟨?_, ?_, ?_, gi, gu, gf⟩ <;> simp only [Proof.MdHashTable.X86.fnsOf, List.mem_map] <;>
    rintro _ ⟨w, -, rfl⟩
  exacts [w.h.ok.hH.initSp, w.h.ok.comp.nosp, w.h.certs.digSp]

theorem hall_of (hok : OK vs gs) : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i := fun i hi => by
  obtain ⟨w, hw, rfl⟩ := hok.2.2.2.1 i hi
  exact ⟨w.h, (hok.2.1 w hw).2⟩

theorem code_noSp (hok : OK vs gs) (v : CrtImpl) : NoSp (signCode vs gs v) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp (fnsSp vs gs) (hall_of hok) v)) restore_noSp)

theorem code_sp (hok : OK vs gs) (v : CrtImpl) : (signCode vs gs v).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp hok v)

theorem spec_sp {s : State} (hs : (sspec vs gs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sign_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega_using [hsa]⟩

theorem fne_of {w : MVar} (hw : w ∈ vs) {wg : TVar} (hwg : wg ∈ gs) :
    ((Proof.MdHashTable.X86.fnsOf vs).init ≠ [] ∧ (Proof.MdHashTable.X86.fnsOf vs).comp ≠ [] ∧
      (Proof.MdHashTable.X86.fnsOf vs).dig ≠ []) ∧
    ((Proof.HashTable.X86.fnsOf gs).init ≠ [] ∧ (Proof.HashTable.X86.fnsOf gs).upd ≠ [] ∧
      (Proof.HashTable.X86.fnsOf gs).fin ≠ []) := by
  have h1 := List.ne_nil_of_mem hw
  have h2 := List.ne_nil_of_mem hwg
  simp only [Proof.MdHashTable.X86.fnsOf, Proof.HashTable.X86.fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨⟨h1, h1, h1⟩, h2, h2, h2⟩

/-- What the entry state holds of the table of `MdHash` of `w` at `p`, with
its functions where `s'` has them. -/
abbrev THw (vs : List MVar) (w : MVar) (p : BitVec 32) (s' : State) (σ : State) : Prop :=
  HFacts w.h (Proof.MdHashTable.X86.digName w) (Proof.MdHashTable.X86.fnsOf vs) p (s'.syms w.h.H.st.initN)
      (s'.syms w.h.H.compN) (s'.syms (Proof.MdHashTable.X86.digName w)) σ ∧
    σ.mem.readW (VG.X86.addr p 20) 32 = BitVec.ofNat 32 (Proof.MdHashTable.X86.idx w)

/-- The public parameters for the table of `MdHash` of `w` and that of
`Hash` of `wg`, with their functions where `s'` has them. -/
abbrev epw (vs : List MVar) (gs : List TVar) (s s' : State) (w : MVar) (wg : TVar) : EP :=
  ep s (s'.syms w.h.H.st.initN) (s'.syms w.h.H.compN) (s'.syms (Proof.MdHashTable.X86.digName w))
    (THw vs w (arg s 22) s') (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (TabFacts wg.g.H (Proof.HashTable.X86.fnsOf gs) (arg s 23) (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN)
      (s'.syms wg.g.H.finN))

/-- The digest's length, from the hash function the table names. -/
theorem dlen_of {s : State} (hs : (sspec vs gs).pre s) {w : MVar}
    (hh : Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w))) :
    (arg s 17).toNat = w.h.D := by
  obtain ⟨-, -, -, hfitH, -, hdl⟩ := spec_tab hs
  have := hdl _ (Proof.MdHashTable.X86.hashAt_tableOf hfitH (Proof.MdHashTable.X86.held_tableOf hfitH hh).2.2.2)
  rw [this, w.h.glen]

/-- The entry state, for the tables of `w` at the argument 22 and `wg` at
23, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hok : OK vs gs) {s s' : State} (hs : (sspec vs gs).pre s) {w : MVar} {wg : TVar}
    (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hhH : Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w)))
    (hh : Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s (Proof.HashTable.X86.tableOf wg)))
    (hsy : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s.syms n = s'.syms n) :
    Sy (S w.h (epw vs gs s s' w wg)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitH, hfit, -⟩ := spec_tab hs
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  have hD := dlen_of hs hhH
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 fun _ => True
  have ok := (in_of_pre (hai := 0) (hac := 0) (had := 0) (TH := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) hs trivial trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.MdHashTable.X86.mem_names hw
  have hng := Proof.HashTable.X86.mem_names hwg
  have hsyH : ∀ n ∈ Proof.MdHashTable.X86.names vs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_left _ h)
  have hsyG : ∀ n ∈ Proof.HashTable.X86.names gs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_right _ h)
  have tf := Proof.HashTable.X86.tabFacts_entered (argv := e0.argv (arg s 17).toNat) (ro := e0.ro (arg s 17).toNat)
    (rw := e0.rw) (C := 3448) hsp ok (p := arg s 23) (by simp [e0, ep]) hfit hok.2.2.1 hpwG hwg hh
  rw [hsyG _ hng.1, hsyG _ hng.2.1, hsyG _ hng.2.2] at tf
  have sy : (entered frameBytes s).syms = s.syms := pushRegs_syms s _
  obtain ⟨m0, m3, m4, m5⟩ := Proof.MdHashTable.X86.held_entered (argv := e0.argv (arg s 17).toNat)
    (ro := e0.ro (arg s 17).toNat) (rw := e0.rw) (C := 3448) hsp ok (p := arg s 22) (by simp [e0, ep]) hfitH hhH
  have hf := Proof.MdHashTable.X86.hfacts_of hok.1 (σ := entered frameBytes s) (by rw [sy]; exact hpwH) hw m0 m3 m4
  rw [sy, hsyH _ hn.1, hsyH _ hn.2.2.2.1, hsyH _ hn.2.2.2.2] at hf
  have hi := in_of_pre (hai := s'.syms w.h.H.st.initN) (hac := s'.syms w.h.H.compN)
    (had := s'.syms (Proof.MdHashTable.X86.digName w)) (TH := THw vs w (arg s 22) s')
    (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN) (af := s'.syms wg.g.H.finN) hs ⟨hf, m5⟩ tf
  rw [hD] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hok : OK vs gs) (v : CrtImpl) {s : State} (hs : (sspec vs gs).pre s) :
    WP isa (signCode vs gs v) s fun t => abiPreserved s t ∧ (sspec vs gs).post s t := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨T, hT, hh⟩, -, hfitH, hfit, -⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  have hidxH := (Proof.MdHashTable.X86.held_tableOf hfitH hhH).2.2.2
  have hidx := (Proof.HashTable.X86.held_tableOf hfit hh).2.1
  have he := entered_state hok hs hw hwg hhH hh (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  obtain ⟨fneH, fne⟩ := fne_of hw hwg
  have hb := (body_vp w.h (epw vs gs s s w wg) (hok.2.1 w hw).1 (hok.2.1 w hw).2 (fun _ x => x) fneH wg.g
    (fun _ x => x) fne v).wp _ _ he
  have hD := dlen_of hs hhH
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp (fnsSp vs gs) (hall_of hok) v) hsp hfit4
    (W := ((epw vs gs s s w wg).lay w.h.D).W)
    (Q := fun r m => Res w.h wg.g.G (epw vs gs s s w wg) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok hr
    rw [save_eq (argv := (epw vs gs s s w wg).argv (arg s 17).toNat) (ro := (epw vs gs s s w wg).ro (arg s 17).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 3448) hsp,
      ret_eq (argv := (epw vs gs s s w wg).argv (arg s 17).toNat) (ro := (epw vs gs s s w wg).ro (arg s 17).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 3448) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw vs gs s s w wg).ro (arg s 17).toNat) => entered_ro hsp ok hR
    sig_post [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes]
    intro H G hH hG
    rw [Proof.MdHashTable.X86.hashAt_tableOf hfitH hidxH, Option.some.injEq] at hH
    rw [Proof.HashTable.X86.hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    rw [show pB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).PP) (by simp),
      show qB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).QQ) (by simp),
      show dpB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).DP) (by simp),
      show dqB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).DQ) (by simp),
      show qiB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).QI) (by simp),
      show saltB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).SALT) (by simp)]
      at res
    have hdg : digB w.h (epw vs gs s s w wg) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 16).setWidth 64) (arg s 17).toNat := by
      unfold digB; rw [← hD]; exact ro (R := (epw vs gs s s w wg).DIG (arg s 17).toNat) (by simp)
    rw [hdg, hD] at res
    rw [BitVec.setWidth_append_eq_right, w.h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hok : OK vs gs) (v : CrtImpl) : ConstantTime isa (sspec vs gs).pre (sspec vs gs).pub (signCode vs gs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨T, hT, hh₁⟩, -, -, -, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal,
    argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabH, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23⟩ := hp
  have hhH₂ := (htabH _ _ rfl rfl _ hTH).mp hhH₁
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hsy' : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s₂.syms n = s₁.syms n :=
    fun n hn => (hsy n (by simpa [Proof.MdHashTable.X86.names, Proof.HashTable.X86.names] using hn)).symm
  have hep : epw vs gs s₁ s₁ w wg = epw vs gs s₂ s₁ w wg := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.bytesAt_len, a3])
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a12, a14, a16, a18, a19, a20, a21, a22, a23]
    rw [a2, a3] at hn
    rw [a4, a5] at he
    rw [hn, he]
  have hD₁ := dlen_of h₁ hhH₁
  obtain ⟨fneH, fne⟩ := fne_of hw hwg
  refine (wrap_ct (F := frameBytes) (body_noSp (fnsSp vs gs) (hall_of hok) v) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w.h (epw vs gs s₁ s₁ w wg) (hok.2.1 w hw).1 (hok.2.1 w hw).2 (fun _ x => x) fneH wg.g
    (fun _ x => x) fne v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hok h₁ hw hwg hhH₁ hh₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hok h₂ hw hwg hhH₂ hh₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_pss_sign`, calling `vg_rsa_private_checked` over `v`, with the
hash function any of the tables of `vs` and MGF1's any of `gs`, meets the
shared contract (satisfiable, `SgSat.lean`). -/
theorem sign_verified (hok : OK vs gs) (hsat : ∃ s, (sspec vs gs).pre s) (v : CrtImpl) :
    Verified target (signCode vs gs v) (sspec vs gs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hok v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hok v, hsat⟩

end VG.Proof.RsaPss.X86.Sg
