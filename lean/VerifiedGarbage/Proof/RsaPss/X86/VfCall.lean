module

public import VerifiedGarbage.Proof.RsaPss.X86.VfChk
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PubCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the call

As on ARMv7 (`Proof/RsaPss/Arm/VfCall.lean`): the ten arguments of
`vg_rsa_public_precomputed_checked`, one word of the frame at a time
(`pa_vp`): `EM`'s place (`oEm`), `pre`, `e`, the signature, and the rest of
`scratch` from `oRsa` on; and the call (`call_vp`, correct and constant
time: its arguments and the public data it reads are the same in two runs),
which writes RSAVP1 of the signature to `EM`, or zeros (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- `dbLen`. -/
abbrev dbN (P : EP) : Nat := P.K - lo P - h.D - 1

/-- The slots after the checks. -/
abbrev Bm (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P) ∧ m.readW ((P.lay h.D).fr sAny) 32 = anyW P

/-- When everything fits. -/
abbrev M0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ fits h P ∧ Bm h P s.mem

theorem m0_of {P : EP} {σ s : State} (hc : C1 h P σ s) (e : isa.eval .ne s = some false) : M0 h P σ s := by
  obtain ⟨hc, hi, sc, sl, sd, sa, z⟩ := hc
  have hf : fits h P := by
    simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
    exact e
  refine ⟨hc, hi, hf, sc, sl, ?_, sa⟩
  rw [sd, dbW_byte]
  have : lo P ≤ 1 := by unfold lo; split <;> omega
  rw [Offset.ofNat_sub_ofNat (show lo P ≤ P.K by have := hf.2; omega), Offset.ofNat_sub_ofNat (by have := hf.2; omega)]
  congr 1

/-- The slots of the parameters keep their words through a frame missing them. -/
theorem Bm.keep {P : EP} {m m' : Mem} {rs : List Region} (hb : Bm h P m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∀ d ∈ [sC, sLo, sDb, sAny], (slotR (P.lay h.D) d).Disjoint r) : Bm h P m' :=
  ⟨slot_keep hf (fun r hr => hd r hr sC (by simp)) hb.1, slot_keep hf (fun r hr => hd r hr sLo (by simp)) hb.2.1,
    slot_keep hf (fun r hr => hd r hr sDb (by simp)) hb.2.2.1, slot_keep hf (fun r hr => hd r hr sAny (by simp)) hb.2.2.2⟩

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  pubArgv (P.scr + BitVec.ofNat 32 oEm) P.pre P.e P.sig (P.scr + BitVec.ofNat 32 oRsa) P.K P.rl P.el (P.scl - 1024)

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW ((P.lay h.D).fr (4 * i)) 32 = (outv P).getD i 0

/-- During the call's arguments. -/
abbrev A0 (P : EP) (σ s : State) (k : Nat) : Prop := M0 h P σ s ∧ Slots h P s.mem k

theorem vf_arg {j : Nat} (hj : j < 13) {P : EP} : j < ((P.lay h.D).argv).length := by simp; omega

/-- A word stored below the slots keeps them. -/
theorem keepSlot {P : EP} {m : Mem} {d : Nat} (hd : d + 4 ≤ sLo) (v : BitVec 32) (hb : Bm h P m) :
    Bm h P (m.writeW ((P.lay h.D).fr d) v) :=
  hb.keep h (slot_frame (P.lay h.D) m d v) fun r hr e he => by
    simp only [List.mem_singleton] at hr; subst hr
    have e1 : sLo = 80 := rfl
    have e2 : sC = 84 := rfl
    have e3 : sDb = 88 := rfl
    have e4 : sAny = 132 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by unfold frameBytes; omega) (by omega)

theorem slots_next {P : EP} {m : Mem} {i : Nat} (hs : Slots h P m i) (hi : i < 10) (v : BitVec 32)
    (hv : v = (outv P).getD i 0) : Slots h P (m.writeW ((P.lay h.D).fr (4 * i)) v) (i + 1) := by
  intro k hk
  rcases (by omega : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega)]
    exact hs k hki

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {P : EP} {σ s : State} {i j : Nat} (ha : A0 h P σ s i) (hi : i < 10)
    (hj : j < 13) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  obtain ⟨⟨hc, hin, hf, hb⟩, hs⟩ := ha
  have hg := hin.geo
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine hc.wp_arg hg (vf_arg h hj) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega) fun t2 c2 m2 => kk t2 ⟨⟨c2, hin, hf, ?_⟩, ?_⟩
  · rw [m2.mem, u1.mem]
    exact keepSlot h (show 4 * i + 4 ≤ sLo by unfold sLo; omega) _ hb
  · rw [m2.mem, u1.mem, u1.gpr]
    exact slots_next h hs hi _ hv

/-- `scratch + o` to the call's argument `i`. -/
theorem scrSlot {P : EP} {σ s : State} {i o : Nat} (ha : A0 h P σ s i) (hi : i < 10)
    (hv : P.scr + BitVec.ofNat 32 o = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 h P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (atS .eax o ++ [st .eax (4 * i)] ++ is)) s Q := by
  obtain ⟨⟨hc, hin, hf, hb⟩, hs⟩ := ha
  have hg := hin.geo
  simp only [atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (d := 4 * i)
    (by unfold frameBytes; omega) fun t3 c3 m3 => kk t3 ⟨⟨c3, hin, hf, ?_⟩, ?_⟩
  · rw [m3.mem, u2.mem, u1.mem]
    exact keepSlot h (show 4 * i + 4 ≤ sLo by unfold sLo; omega) _ hb
  · rw [m3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp]
    exact slots_next h hs hi _ hv

theorem pubArgs_eq : pubArgs = (atS .eax oEm ++ [st .eax (4 * 0)]) ++ copyArg 1 1 ++ copyArg 11 2 ++
    copyArg 12 3 ++ copyArg 2 4 ++ copyArg 3 5 ++ copyArg 5 6 ++ copyArg 1 7 ++
    (atS .eax oRsa ++ [st .eax (4 * 8)]) ++ [ld .eax (arg 10), .alu .sub .eax (.imm 1024), st .eax (4 * 9)] := by
  simp only [pubArgs, List.append_assoc]; rfl

/-- Before the call. -/
abbrev V1 (P : EP) (σ s : State) : Prop :=
  M0 h P σ s ∧ PubArgs s (P.scr + BitVec.ofNat 32 oEm) P.pre P.e P.sig (P.scr + BitVec.ofNat 32 oRsa) P.K P.rl
    P.el (P.scl - 1024)

theorem pa_vp (P : EP) : VP (M0 h P) (.block pubArgs) (V1 h P) := by
  refine VP.taint [.esp, .ebp] pubArgs_taint (sp_bp fun _ _ h => h.1) fun σ s hm => ?_
  have hi := hm.2.1
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hs1 := hi.pubScr
  rw [pubArgs_eq]
  simp only [List.append_assoc]
  have z0 : A0 h P σ s 0 := ⟨hm, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  refine scrSlot h z0 (by decide) (by simp [outv, pubArgv]) fun t1 z1 => ?_
  refine copySlot h z1 (by decide) (j := 1) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t2 z2 => ?_
  refine copySlot h z2 (by decide) (j := 11) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t3 z3 => ?_
  refine copySlot h z3 (by decide) (j := 12) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t4 z4 => ?_
  refine copySlot h z4 (by decide) (j := 2) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t5 z5 => ?_
  refine copySlot h z5 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t6 z6 => ?_
  refine copySlot h z6 (by decide) (j := 5) (by decide) (by simp [EP.argv, outv, pubArgv, hi.glK]) fun t7 z7 => ?_
  refine copySlot h z7 (by decide) (j := 1) (by decide) (by simp [EP.argv, outv, pubArgv]) fun t8 z8 => ?_
  rw [← List.append_assoc (atS .eax oRsa)]
  refine scrSlot h z8 (by decide) (by simp [outv, pubArgv]) fun t9 z9 => ?_
  obtain ⟨⟨c9, -, hf9, b9⟩, s9⟩ := z9
  simp only [ld, st]
  refine c9.wp_arg hg (vf_arg h (j := 10) (by decide)) (by decide) (by decide) fun t10 c10 u10 =>
    wp_subi fun t11 u11 _ _ => (c10.upd u11 (by decide) (by decide)).wp_st hg (d := 4 * 9) (by decide)
      fun t12 c12 m12 => WP.block_nil ?_
  have v : t11.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u11.gpr, u10.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) (by omega)
  have m : t12.mem = t9.mem.writeW ((P.lay h.D).fr (4 * 9)) (t11.gpr .eax) := by
    rw [m12.mem, u11.mem, u10.mem]
  have kb := keepSlot h (show 4 * 9 + 4 ≤ sLo by decide) (t11.gpr .eax) b9
  have sl := slots_next h s9 (by decide) _ (v.trans (by simp [outv, pubArgv]))
  rw [← m] at kb sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨⟨c12, hi, hf9, kb⟩, fun i hi' => ?_, by rw [c12.st.sp]; have : 48 ≤ P.B.toNat := ok.BC; show 44 ≤ P.B.toNat; omega,
    by rw [c12.st.sp]; show P.B.toNat + 40 ≤ _; omega, hi.kv, hi.rlK, hi.el1, hi.elK, hs1.1,
    by have := hi.scl32; omega⟩
  rw [c12.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega)]
  exact sl i hi'

/-- What the call writes to `EM` and returns. -/
abbrev CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K r
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ))

/-- After the call. -/
abbrev V2 (P : EP) (σ s : State) : Prop := M0 h P σ s ∧ CR P σ s.mem (s.gpr .eax)

/-- The call's output and working space, in `scratch`. -/
abbrev emR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oEm).setWidth 64, P.K⟩
abbrev scrR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oRsa).setWidth 64, (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In h.D P σ) :
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

theorem sigR {P : EP} {σ : State} (hi : In h.D P σ) : (⟨P.sig.setWidth 64, P.K⟩ : Region) = P.SIG := by
  show _ = (⟨P.sig.setWidth 64, P.gl⟩ : Region); rw [hi.glK]

theorem nB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- `pre`'s words, in a state of the body. -/
theorem pw_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.wordsAt s.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hi.ok
  have hR : P.PRE ∈ (P.lay h.D).ro := by simp
  have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' hs.frame (fun r hr => ?_) (by omega)).trans hi.pw
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    false_or] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (ok.wro P.SCR (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- `pre`'s words, in a callee's entry state. -/
theorem callPw {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.wordsAt s.callEntry.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hi.ok
  have hR : P.PRE ∈ (P.lay h.D).ro := by simp
  have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' (hs.callEntry_frame (by show 4 ≤ 48; decide)) (fun r hr => ?_)
    (by omega)).trans (pw_at h hi hs)
  simp only [List.mem_singleton] at hr; subst hr
  exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

theorem call_vp (P : EP) (c : Ver.PublicImpl) : VP (V1 h P) (.call c.name c.code) (V2 h P) := by
  refine VP.call c.verified.1 c.verified.2.1 c.noSp
    (pubRd P.pre P.e P.sig P.K P.rl P.el) (pubWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa)
      P.K (P.scl - 1024))
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ s hr => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.st.sp, h₂.1.1.st.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' hr rd wr cs fr po => ?_)
  · -- The callee's precondition.
    obtain ⟨⟨hc, hi, -, -⟩, pa⟩ := hr
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have fit := ok.fit
    simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at fit
    have sg := sigR h hi
    have args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.D).fr 0, 40⟩ := by simp
    have hsp := hc.st.sp
    rw [show (P.lay h.D).B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    refine pub_pre pa ?_ ?_ ?_ ?_
    · intro w hw r hr
      simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
      · exact (ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).sub_left sI
      · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sI
      · rw [sg]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).sub_left sI
      · exact (ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).sub_left sS'
      · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
      · rw [sg]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).sub_left sS'
      all_goals rw [args0]
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
      · exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
      · rw [sg]; exact ok.stk_fr (.inl (by simp)) (by show 0 + 40 ≤ frameBytes + 16; decide)
    · simp only [pubWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨dIS, ?_⟩, ?_⟩
      · rw [args0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 40 ≤ frameBytes + 16; decide)).symm).sub_left sI
      · rw [args0]; exact ⟨((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 40 ≤ frameBytes + 16; decide)).symm).sub_left sS', fun _ h => h.elim⟩
    · intro r hr
      have low : Region.Sub (below P.B 44) (P.lay h.D).LOW := by
        rw [← ok.low_eq]; exact below_sub (show 44 ≤ 48 by decide) ok.BC
      rw [hsp]
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI).sub_left low
      · exact ((ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS').sub_left low
      · rw [args0]; exact ((Lay.fr_low (by omega) (by show (48 : Nat) ≤ 2 ^ 32; decide)).symm).sub_left low
      · exact (ok.low_buf (R := P.PRE) (.inl (by simp))).sub_left low
      · exact (ok.low_buf (R := P.E) (.inl (by simp))).sub_left low
      · rw [sg]; exact (ok.low_buf (R := P.SIG) (.inl (by simp))).sub_left low
    · intro r hr
      have hg := hi.geo
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega),
          hg.scr_lt (by decide)]
        unfold oEm; omega
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
      · rw [sg]; exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    obtain ⟨⟨hc, hi, -, -⟩, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega)⟩
    have hA : Covers [⟨P.B.setWidth 64, 40⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 40) (by simp only [frameBytes]; omega)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (pubWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
        s.wr :=
      (show Covers [emR P] s.wr by rw [emR, e1]; exact inS (by unfold oEm; omega)).cons
        ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    exact (hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons
      ((show Covers [⟨P.sig.setWidth 64, P.K⟩] (s.rd ++ s.wr) by rw [sigR h hi]; exact hro P.SIG (by simp)).cons
        Covers.nil))
  · rw [hr.1.1.st.sp]
    have : 48 ≤ P.B.toNat := hr.1.2.1.ok.BC
    have := c.stack
    show _ ≤ P.B.toNat
    omega
  · refine pub_pub h₁.2 h₂.2 (by rw [h₁.1.1.st.sp, h₂.1.1.st.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [pw_at h h₁.1.2.1 h₁.1.1.st, pw_at h h₂.1.2.1 h₂.1.1.st]
    · rw [eB_at h h₁.1.2.1 h₁.1.1.st, eB_at h h₂.1.2.1 h₂.1.1.st]
    · have ok := h₁.1.2.1.ok
      rw [h₁.1.1.st.sp]
      exact (ok.low_buf (R := P.PRE) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 44 ≤ 48 by decide) ok.BC)
    · have ok := h₁.1.2.1.ok
      rw [h₁.1.1.st.sp]
      exact (ok.low_buf (R := P.E) (.inl (by simp))).sub_left
        (by rw [← ok.low_eq]; exact below_sub (show 44 ≤ 48 by decide) ok.BC)
  · -- After the call.
    obtain ⟨⟨hc, hi, hf, hb⟩, pa⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hfit, hs1, hK⟩ := call_geo h hi
    have low : Region.Sub (below (s.gpr .esp) (stackUse c.code + 4)) (P.lay h.D).LOW := by
      rw [hsp, ← ok.low_eq]
      exact below_sub (by have := c.stack; show _ ≤ 48; omega) ok.BC
    have args0 : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨(P.lay h.D).fr 0, 40⟩ := by simp
    have hw : ∀ r ∈ pubWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024) ++
        [below (s.gpr .esp) (stackUse c.code + 4)], ∃ R ∈ (P.lay h.D).W, Region.Sub r R := fun r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨(P.lay h.D).FR, by simp, ?_⟩
        rw [args0]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
      · exact ⟨(P.lay h.D).LOW, by simp, low⟩
    have st : (P.lay h.D).St σ s' := hs.write fr hw rd wr (cs .esp (by simp [calleeSaved]))
    have hct : Ctx (P.lay h.D) P.scr σ s' := ⟨st, by rw [cs .ebp (by simp [calleeSaved]), hc.ebp]⟩
    have hb' : Bm h P s'.mem := hb.keep h fr fun r hr d hd => by
      have hd' : 80 ≤ d ∧ d + 4 ≤ frameBytes := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega)).sub_right sI
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega)).sub_right sS'
      · rw [args0]; exact Lay.fr_sep (by omega) (by simp only [frameBytes] at hd' ⊢; omega) (by decide)
      · exact (Lay.fr_low (by simp only [frameBytes] at hd'; omega)
          (by show (48 : Nat) ≤ 2 ^ 32; decide)).sub_right low
    refine ⟨⟨hct, hi, hf, hb'⟩, fun hp => ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := pub_post pa po P.nB (nB_length hi) (by rw [callPw h hi hs]; exact hp)
    rw [m₂, g₂ .eax (by decide)] at this
    have eE : Spec.Rsa.bytesAt s.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
      (hs.callEntry_ro (by show 4 ≤ 48; decide) (R := P.E) (by simp)).trans hi.eB
    have eS : Spec.Rsa.bytesAt s.callEntry.mem (P.sig.setWidth 64) P.K = sigB P σ := by
      have e := hs.callEntry_ro (by show 4 ≤ 48; decide) (R := P.SIG) (by simp)
      dsimp only at e; rw [hi.glK] at e; exact e
    rw [eE, eS] at this
    exact this

end VG.Proof.RsaPss.X86.Vf
