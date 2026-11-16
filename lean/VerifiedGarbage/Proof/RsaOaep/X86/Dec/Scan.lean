module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Base
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCall
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaOaep.X86
public import VerifiedGarbage.Proof.RsaOaep.X86.Base
public import VerifiedGarbage.Proof.RsaPss.X86.Prims
public import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaOaep.X86.Instr
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.RsaOaep.X86.MgfSlots
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.RsaPss.X86.CmpLoop
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.X86.Taint

/-! ### `RsaOaep.X86.Dec.Acc`, which only this module used -/

section

/-! ### `RsaOaep.X86.Dec.Unmask`, which only this module used -/

section

/-! ### `RsaOaep.X86.Dec.Chk`, which only this module used -/

section

/-! ### `RsaOaep.X86.Dec.Call`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on x86: the call of `vg_rsa_private_checked`

As on ARMv7 (`Proof/RsaOaep/Arm/DecCall.lean`): `scratch` into `ebp` and
the call's twenty arguments, one word of the frame at a time (`pa_vp`):
`EM`'s place (at `oEm`) as its output, `n`, `e`, the ciphertext as its
input, the private key, and the rest of `scratch` from `oRsa` on; the call
(`call_vp`), correct and constant time, which writes `EM` (`V`) or zeros and
returns `rV`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st atS addi copyArg)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.p.setWidth 64) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.q.setWidth 64) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dp.setWidth 64) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dq.setWidth 64) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.qinv.setWidth 64) P.pl
abbrev labB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.lab.setWidth 64) P.ll
abbrev ctB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.ct.setWidth 64) P.K

/-- The private-key operation's outcome. -/
abbrev oc (P : EP) (σ : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked P.nB P.eB (ctB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ)

/-- What it writes to `EM`'s place, and returns. -/
def emL (K : Nat) : Spec.Rsa.Outcome → List Byte
  | .ok y => y
  | _ => List.replicate K 0

def rOf : Spec.Rsa.Outcome → BitVec 32
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

/-- `EM`, byte by byte, and the result. -/
abbrev V (P : EP) (σ : State) (i : Nat) : Byte := (emL P.K (oc P σ)).getD i 0
abbrev rV (P : EP) (σ : State) : BitVec 32 := rOf (oc P σ)

/-- A result of the operation has `k` bytes. -/
abbrev OcK (P : EP) (σ : State) : Prop := ∀ y, oc P σ = .ok y → y.length = P.K

/-- The result. -/
abbrev Res (H G : Spec.Mgf1.Hash) (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaOaep.writtenDecrypt m (P.out.setWidth 64) (P.ml.setWidth 64) P.K r
    (Spec.RsaOaep.decrypt H G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (labB P σ) (ctB P σ))

/-- The end of the body. -/
abbrev Fin (H G : Spec.Mgf1.Hash) (P : EP) (σ s : State) : Prop := S P σ s ∧ Res H G P σ s.mem (s.gpr .eax)

theorem dec_arg {j : Nat} (hj : j < 23) {P : EP} : j < P.lay.argv.length := by simp; omega_arith

/-! ## The call's arguments -/

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  privArgv (P.scr + BitVec.ofNat 32 oEm) P.n P.e P.ct P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa) P.K
    P.el P.pl P.ql (P.scl - 1024)

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- During the call's arguments. -/
abbrev A0 (P : EP) (σ s : State) (k : Nat) : Prop := Ctx P.lay P.scr σ s ∧ In P σ ∧ Slots P s.mem k

theorem slots_next {P : EP} {m : Mem} {i : Nat} (hs : Slots P m i) (hi : i < 20) (v : BitVec 32)
    (hv : v = (outv P).getD i 0) : Slots P (m.writeW (P.lay.fr (4 * i)) v) (i + 1) := by
  intro k hk
  rcases (by omega_arith : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hs k hki

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {P : EP} {σ s : State} {i j : Nat} (ha : A0 P σ s i) (hi : i < 20)
    (hj : j < 23) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  obtain ⟨hc, hi', hs⟩ := ha
  have hg := hi'.geo
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine hc.wp_arg hg (dec_arg hj) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega_arith) fun t2 c2 m2 => kk t2 ⟨c2, hi', ?_⟩
  rw [m2.mem, u1.mem, u1.gpr]
  exact slots_next hs hi _ hv

/-- `scratch + o` to the call's argument `i`. -/
theorem scrSlot {P : EP} {σ s : State} {i o : Nat} (ha : A0 P σ s i) (hi : i < 20)
    (hv : P.scr + BitVec.ofNat 32 o = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, A0 P σ t (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (atS .eax o ++ [st .eax (4 * i)] ++ is)) s Q := by
  obtain ⟨hc, hi', hs⟩ := ha
  have hg := hi'.geo
  simp only [atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (d := 4 * i)
    (by unfold frameBytes; omega_arith) fun t3 c3 m3 => kk t3 ⟨c3, hi', ?_⟩
  rw [m3.mem, u2.mem, u1.mem, u2.gpr, u1.gpr, hc.ebp]
  exact slots_next hs hi _ hv

theorem privArgs_eq : decStart ++ privArgs = [ld .ebp (arg 21)] ++ ((atS .eax oEm ++ [st .eax (4 * 0)]) ++
    copyArg 4 1 ++ copyArg 3 2 ++ copyArg 4 3 ++ copyArg 5 4 ++ copyArg 6 5 ++ copyArg 19 6 ++ copyArg 4 7 ++
    copyArg 7 8 ++ copyArg 8 9 ++ copyArg 9 10 ++ copyArg 10 11 ++ copyArg 11 12 ++ copyArg 8 13 ++
    copyArg 13 14 ++ copyArg 10 15 ++ copyArg 15 16 ++ copyArg 8 17 ++ (atS .eax oRsa ++ [st .eax (4 * 18)]) ++
    [ld .eax (arg 22), .alu .sub .eax (.imm 1024), st .eax (4 * 19)]) := by
  simp only [decStart, privArgs, List.append_assoc]; rfl

/-- Before the call. -/
abbrev R1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ In P σ ∧
    PrivArgs s (P.scr + BitVec.ofNat 32 oEm) P.n P.e P.ct P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024)

theorem pa_vp (P : EP) : VP (S P) (.block (decStart ++ privArgs)) (R1 P) := by
  refine VP.taint [.esp] privArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]) fun σ s ⟨hi, hs⟩ => ?_
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hs1 : 1024 ≤ P.scl := by
    have := hi.slK; unfold Spec.RsaPss.scratchWords at this; omega_arith
  rw [privArgs_eq, List.singleton_append]
  simp only [List.append_assoc, ld]
  refine hs.wp_arg (dec_arg (j := 21) (by decide)) (by decide) fun t0 s0 u0 => ?_
  obtain c0 : Ctx P.lay P.scr σ t0 := ⟨s0, by rw [u0.gpr]; rfl⟩
  obtain z0 : A0 P σ t0 0 := ⟨c0, hi, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [← List.append_assoc (atS .eax oEm)]
  refine scrSlot z0 (by decide) (by simp [outv, privArgv]) fun t1 z1 => ?_
  refine copySlot z1 (by decide) (j := 4) (by decide) (by simp [EP.argv, outv, privArgv]) fun t2 z2 => ?_
  refine copySlot z2 (by decide) (j := 3) (by decide) (by simp [EP.argv, outv, privArgv]) fun t3 z3 => ?_
  refine copySlot z3 (by decide) (j := 4) (by decide) (by simp [EP.argv, outv, privArgv]) fun t4 z4 => ?_
  refine copySlot z4 (by decide) (j := 5) (by decide) (by simp [EP.argv, outv, privArgv]) fun t5 z5 => ?_
  refine copySlot z5 (by decide) (j := 6) (by decide) (by simp [EP.argv, outv, privArgv]) fun t6 z6 => ?_
  refine copySlot z6 (by decide) (j := 19) (by decide) (by simp [EP.argv, outv, privArgv]) fun t7 z7 => ?_
  refine copySlot z7 (by decide) (j := 4) (by decide) (by simp [EP.argv, outv, privArgv]) fun t8 z8 => ?_
  refine copySlot z8 (by decide) (j := 7) (by decide) (by simp [EP.argv, outv, privArgv]) fun t9 z9 => ?_
  refine copySlot z9 (by decide) (j := 8) (by decide) (by simp [EP.argv, outv, privArgv]) fun t10 z10 => ?_
  refine copySlot z10 (by decide) (j := 9) (by decide) (by simp [EP.argv, outv, privArgv]) fun t11 z11 => ?_
  refine copySlot z11 (by decide) (j := 10) (by decide) (by simp [EP.argv, outv, privArgv]) fun t12 z12 => ?_
  refine copySlot z12 (by decide) (j := 11) (by decide) (by simp [EP.argv, outv, privArgv]) fun t13 z13 => ?_
  refine copySlot z13 (by decide) (j := 8) (by decide) (by simp [EP.argv, outv, privArgv]) fun t14 z14 => ?_
  refine copySlot z14 (by decide) (j := 13) (by decide) (by simp [EP.argv, outv, privArgv]) fun t15 z15 => ?_
  refine copySlot z15 (by decide) (j := 10) (by decide) (by simp [EP.argv, outv, privArgv]) fun t16 z16 => ?_
  refine copySlot z16 (by decide) (j := 15) (by decide) (by simp [EP.argv, outv, privArgv]) fun t17 z17 => ?_
  refine copySlot z17 (by decide) (j := 8) (by decide) (by simp [EP.argv, outv, privArgv]) fun t18 z18 => ?_
  rw [← List.append_assoc (atS .eax oRsa)]
  refine scrSlot z18 (by decide) (by simp [outv, privArgv]) fun t19 z19 => ?_
  obtain ⟨c19, -, s19⟩ := z19
  simp only [st]
  refine c19.wp_arg hg (dec_arg (j := 22) (by decide)) (by decide) (by decide) fun t20 c20 u20 =>
    wp_subi fun t21 u21 _ _ => (c20.upd u21 (by decide) (by decide)).wp_st hg (d := 4 * 19) (by decide)
      fun t22 c22 m22 => WP.block_nil ?_
  obtain v : t21.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u21.gpr, u20.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) hs1
  obtain sl := slots_next s19 (by decide) _ (v.trans (by simp [outv, privArgv]))
  obtain m : t22.mem = t19.mem.writeW (P.lay.fr (4 * 19)) (t21.gpr .eax) := by
    rw [m22.mem, u21.mem, u20.mem]
  rw [← m] at sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨c22, hi, fun i hi' => ?_, by rw [c22.st.sp]; exact ok.BC, by rw [c22.st.sp]; show P.B.toNat + 80 ≤ _; omega_arith,
    hi.kv, hi.el1, hi.elK, hi.pl1, hi.plK, hi.ql1, hi.qlK, ?_, by have := hi.scl32; omega_arith⟩
  · rw [c22.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega_arith)]
    exact sl i hi'
  · have hs := hi.slK; unfold Spec.RsaPss.scratchWords at hs; omega_arith

/-! ## The call -/

/-- The call's output and working space, in `scratch`. -/
abbrev emR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oEm).setWidth 64, P.K⟩
abbrev scrR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oRsa).setWidth 64, (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In P σ) :
    (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm ∧
    (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa ∧
    Region.Sub (emR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (emR P).Disjoint (scrR P) ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1024 ≤ P.scl ∧ P.K ≤ 1024 := by
  obtain hf := hi.ok.fits P.SCR (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega_arith)] at hf
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  have hK := hi.k1024
  obtain e1 : (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm :=
    addr_eq (by unfold oEm; omega_arith)
  obtain e2 : (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa :=
    addr_eq (by unfold oRsa; omega_arith)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, by omega_arith, hK⟩
  · rw [emR, e1]; exact Offset.sub_base _ (by unfold oEm; omega_arith)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega_arith)
  · rw [emR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega_arith) (by unfold oEm; omega_arith)
      (by unfold oRsa; omega_arith)

theorem nB_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- What the operation writes, byte by byte. -/
theorem em_of {m : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Spec.Rsa.writtenOutcome m a K r o) :
    r = rOf o ∧ (∀ i < K, m (a + BitVec.ofNat 64 i) = (emL K o).getD i 0) ∧ ∀ y, o = .ok y → y.length = K := by
  cases o with
  | ok y =>
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, fun i hi => ?_, fun y' e => ?_⟩
    · rw [emL, ← hb, RsaPkcs1Sig.bytesAt_getD hi]
    · cases e; rw [← hb, RsaPkcs1Sig.bytesAt_len]
  | invalid =>
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, fun i hi => ?_, fun y' e => by cases e⟩
    show _ = (List.replicate K 0).getD i 0
    rw [← hb, RsaPkcs1Sig.bytesAt_getD hi]
  | fault =>
    obtain ⟨hr, hb⟩ := h
    refine ⟨hr, fun i hi => ?_, fun y' e => by cases e⟩
    show _ = (List.replicate K 0).getD i 0
    rw [← hb, RsaPkcs1Sig.bytesAt_getD hi]

/-- After the call. -/
abbrev R2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ In P σ ∧ (∀ i < P.K, s.mem (sa P.scr (oEm + i)) = V P σ i) ∧ s.gpr .eax = rV P σ ∧
    OcK P σ

/-- The name of `vg_rsa_private_checked` over `v`. -/
def privName (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : String := "vg_rsa_private_checked" ++ v.suffix

/-- `EM` and the result: the call. -/
theorem call_vp (P : EP) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (R1 P) (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (R2 P) := by
  obtain hv := Proof.Rsa.X86.PrivChecked.code_verified v
  obtain hst := Proof.Rsa.X86.PrivChecked.code_stack v
  refine VP.call hv.1 hv.2.1 (Proof.Rsa.X86.PrivChecked.privateCode_noSp v)
    (privRd P.n P.e P.ct P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
    (fun σ s hr => ?_) (fun σ s hr => ?_)
    (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.st.sp, h₂.1.st.sp])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr cs fr po => ?_)
  · -- The callee's precondition.
    obtain ⟨hc, hi, pa⟩ := hr
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have fit := ok.fit
    simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at fit
    obtain args0 : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
    have hsp := hc.st.sp
    rw [show P.lay.B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    obtain ro : ∀ R ∈ P.lay.ro, ∀ {w : Region}, Region.Sub w P.SCR → w.Disjoint R := fun R hR w hw =>
      (ok.rw_ro (w := P.SCR) (r := R) (by simp) hR).sub_left hw
    refine priv_pre pa ?_ ?_ ?_ ?_
    · intro w hw r hr
      simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ro P.N (by simp) sI
      · exact ro P.E (by simp) sI
      · exact ro P.CT (by simp) sI
      · exact ro P.PP (by simp) sI
      · exact ro P.QQ (by simp) sI
      · exact ro P.DP (by simp) sI
      · exact ro P.DQ (by simp) sI
      · exact ro P.QI (by simp) sI
      · exact ro P.N (by simp) sS'
      · exact ro P.E (by simp) sS'
      · exact ro P.CT (by simp) sS'
      · exact ro P.PP (by simp) sS'
      · exact ro P.QQ (by simp) sS'
      · exact ro P.DP (by simp) sS'
      · exact ro P.DQ (by simp) sS'
      · exact ro P.QI (by simp) sS'
      all_goals rw [args0]; exact ok.stk_fr (.inl (by simp)) (by show 0 + 80 ≤ frameBytes + 16; decide)
    · simp only [privWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨dIS, ?_⟩, ?_, fun _ h => h.elim⟩
      · rw [args0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 80 ≤ frameBytes + 16; decide)).symm).sub_left sI
      · rw [args0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp))
          (by show 0 + 80 ≤ frameBytes + 16; decide)).symm).sub_left sS'
    · intro r hr
      rw [hsp, ← show P.lay.B = P.B from rfl, ok.low_eq]
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
      · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
      · rw [args0]; exact (Lay.fr_low (by omega_arith) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).symm
      all_goals exact ok.low_buf (.inl (by simp))
    · intro r hr
      have hg := hi.geo
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega_arith),
          hg.scr_lt (by decide)]
        unfold oEm; omega_arith
      · show ((P.scr + BitVec.ofNat 32 oRsa).setWidth 64).toNat + (P.scl - 1024) * 8 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega_arith),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega_arith
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 80 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_arith)]
        omega_arith
      all_goals exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    obtain ⟨hc, hi, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    obtain hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    obtain inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega_arith)⟩
    obtain hA : Covers [⟨P.B.setWidth 64, 80⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 80) (by simp only [frameBytes]; omega_arith)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    obtain wr : Covers (privWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
        s.wr :=
      (show Covers [emR P] s.wr by rw [emR, e1]; exact inS (by unfold oEm; omega_arith)).cons
        ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega_arith)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    exact (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.CT (by simp)).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons Covers.nil)))))))
  · rw [hr.1.st.sp]
    have : 3448 ≤ P.B.toNat := hr.2.1.ok.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    show _ ≤ P.B.toNat
    omega_arith
  · refine priv_pub h₁.2.2 h₂.2.2 (by rw [h₁.1.st.sp, h₂.1.st.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [nB_at h₁.2.1 h₁.1.st, nB_at h₂.2.1 h₂.1.st]
    · rw [eB_at h₁.2.1 h₁.1.st, eB_at h₂.2.1 h₂.1.st]
    · rw [h₁.1.st.sp, h₁.2.1.ok.low_eq]
      exact h₁.2.1.ok.low_buf (R := P.N) (.inl (by simp))
    · rw [h₁.1.st.sp, h₁.2.1.ok.low_eq]
      exact h₁.2.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    obtain ⟨hc, hi, pa⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    obtain low : Region.Sub (below (s.gpr .esp) (stackUse (Proof.Rsa.X86.PrivChecked.privCode v) + 4)) P.lay.LOW := by
      rw [hsp, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega_arith) ok.BC
    obtain hc' : Ctx P.lay P.scr σ s' := hc.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨P.lay.LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
      (cs .ebp (by simp [calleeSaved]))
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_post pa po
    rw [m₂, g₂ .eax (by decide)] at this
    obtain ro := fun {R : Region} (hR : R ∈ P.lay.ro) => hs.callEntry_ro (by show 4 ≤ 3448; decide) hR
    rw [ro (R := P.N) (by simp), hi.nB, ro (R := P.E) (by simp), hi.eB, ro (R := P.CT) (by simp),
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    obtain ⟨r0, hb, hl⟩ := em_of this
    refine ⟨hc', hi, fun i hi' => ?_, r0, hl⟩
    obtain e := hb i hi'
    rw [e1] at e
    refine Eq.trans ?_ e
    simp only [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

end VG.Proof.RsaOaep.X86.Dec

end

end


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
  exact (hg.slot ok (o := oEm) (n := P.K) (by unfold oEm oRsa; omega_using [hK]) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd])).symm

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
    exact sbytes_keep fr (slot_em hi (by decide)) (by unfold oEm; omega_using [hK]) he
  · rw [f3.mem, u2.mem, m1.mem, Mem.readW_writeW_self32, r0]
  · rw [cf3, u2.gpr]
    show some (decide ((BitVec.ofNat 32 P.K).toNat < (BitVec.ofNat 32 (2 * h.H.D + 2)).toNat)) = _
    rw [toNat_ofNat_lt (by omega_using [hK]), toNat_ofNat_lt (by omega_using [hD])]

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
  refine wp_xorI fun t2 u2 => wp_cmpi fun t3 f3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => wp_andi fun t5 u5 => ?_
  obtain c5 : Ctx P.lay P.scr σ t5 :=
    (((c1.upd u2 (by decide) (by decide)).fupd f3).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)
  refine hq t5 c5 (by rw [u5.mem, u4.mem, f3.mem, u2.mem, u1.mem]) ?_
  rw [u5.gpr, u4.gpr, u2.gpr, u1.gpr, hr]

/-- What failing keeps. -/
abbrev Xf (D : Nat) (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ P.K < 2 * D + 2 ∧ m.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ

theorem out_slot {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    (slotR P.lay d).Disjoint P.OUT :=
  hi.ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 16; unfold frameBytes at hd ⊢; omega_using [hd])

theorem ml_slot {P : EP} {σ : State} (hi : In P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    (slotR P.lay d).Disjoint P.ML :=
  hi.ok.stk_fr (R := P.ML) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 16; unfold frameBytes at hd ⊢; omega_using [hd])

theorem out_ml {P : EP} {σ : State} (hi : In P σ) : P.OUT.Disjoint P.ML := by
  have := hi.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact this.1.1

theorem ml_fit {P : EP} {σ : State} (hi : In P σ) : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := hi.ok.fits P.ML (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.ml.isLt; omega_using [])] at this

theorem out_wbuf {P : EP} {σ : State} (hi : In P σ) : WBuf P.lay P.out P.K := by
  have hK := hi.k1024
  obtain hfo := hi.ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at hfo
  rw [Nat.mod_eq_of_lt (by have := P.out.isLt; omega_using [])] at hfo
  exact ⟨hfo, by omega_using [hK], ⟨P.OUT, by simp, Region.contains_self _ _⟩⟩

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
  obtain fit := ml_fit hi
  obtain win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (P.ml.setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd =>
    ⟨P.ML, hc.st.inRw (by simp), Offset.contains_base _ hd (by omega_using [hd])⟩
  simp only [mlZero, mi, List.cons_append, List.drop_succ_cons, List.drop_zero]
  refine wp_movi fun t1 u1 => ?_
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 0)
    (by show t1.ea ⟨.esi, 0⟩ = _; rw [ea_at, u1.other _ (by decide), si]; exact addr_eq (by omega_using []))
    (by rw [u1.wr]; exact win 0 (by decide)) fun t2 m2 => ?_
  refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 4)
    (by show t2.ea ⟨.esi, 4⟩ = _; rw [ea_at, m2.gpr, u1.other _ (by decide), si]; exact addr_eq (by omega_using [fit]))
    (by rw [m2.wr, u1.wr]; exact win 4 (by decide)) fun t3 m3 => ?_
  obtain mm : t3.mem = (s.mem.writeW (P.ml.setWidth 64 + BitVec.ofNat 64 0) (BitVec.ofNat 32 0)).writeW
      (P.ml.setWidth 64 + BitVec.ofNat 64 4) (BitVec.ofNat 32 0) := by
    rw [m3.mem, m2.gpr, m2.mem, u1.gpr, u1.mem]
  obtain fr : Frame [P.ML] s.mem t3.mem := by
    rw [mm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain c3 : Ctx P.lay P.scr σ t3 := hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
    (by rw [m3.rd, m2.rd, u1.rd]) (by rw [m3.wr, m2.wr, u1.wr])
    (by rw [m3.gpr, m2.gpr, u1.other _ (by decide)]) (by rw [m3.gpr, m2.gpr, u1.other _ (by decide)])
  obtain hr3 : t3.mem.readW (P.lay.fr sRes) 32 = rV P σ := by
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
  refine VP.seq ((zero_vp (scr := P.scr) hb (by omega_using [hK]) (Inv := Xf h.H.D P)
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
    exact decOut_fail hk (by rw [h.glen]; omega_using [nf]) (Proof.RsaOaep.out_zero hz') hml

end VG.Proof.RsaOaep.X86.Dec

end

end


/-!
# RSAES-OAEP decryption on x86: `EM` unmasked

As on ARMv7 (`Proof/RsaOaep/Arm/DecUnmask.lean`): the label's hash to
`scratch + oLh` (`labT_vp`, with the label's hash function that of its
table, our argument 23), then the seed unmasked with MGF1 of
`maskedDB` and `DB` with MGF1 of the seed, in place (`mgf_vp`, with the
slots `seedArgs` and `dbArgs` set): `EM`'s place holds `V5`, `EM` unmasked
as `Proof.RsaOaep.chain_eq` states it (`unmask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm oSt oCW arg ld st mi atS addi sCtr sDone)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

variable (h g : OHash)

/-- What the decoding keeps: the result's slot, and that `k` is long enough. -/
abbrev K0 (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ 2 * h.H.D + 2 ≤ P.K ∧ m.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ

/-- `lHash`, and where it is. -/
abbrev lhB (P : EP) (σ : State) : List Byte := h.G.hash (labB P σ)
abbrev LH (P : EP) (σ : State) (m : Mem) : Prop := ∀ i < h.H.D, m (sa P.scr (oLh + i)) = (lhB h P σ).getD i 0

/-- `EM`'s place holds `f`. -/
abbrev EMv (P : EP) (m : Mem) (f : Nat → Byte) : Prop := ∀ x < P.K, m (sa P.scr (oEm + x)) = f x

/-- The seed unmasked (`V3`), then `DB` (`V5`). -/
abbrev mk3 (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.mgf1 g.G (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)) h.H.D
abbrev V3 (P : EP) (σ : State) : Nat → Byte := mixV (V P σ) (mk3 h g P σ) 1 h.H.D
abbrev mk5 (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.mgf1 g.G (srcB (V3 h g P σ) 1 h.H.D) (P.K - h.H.D - 1)
abbrev V5 (P : EP) (σ : State) : Nat → Byte := mixV (V3 h g P σ) (mk5 h g P σ) (1 + h.H.D) (P.K - h.H.D - 1)

theorem srcB_getD (V : Nat → Byte) (a : Nat) {n i : Nat} (hi : i < n) : (srcB V a n).getD i 0 = V (a + i) :=
  Proof.RsaOaep.map_range_getD' (fun i => V (a + i)) hi

theorem srcB_length (V : Nat → Byte) (a n : Nat) : (srcB V a n).length = n := by simp [srcB]

theorem mix_in {V : Nat → Byte} {mk : List Byte} {e n o : Nat} (h₁ : e ≤ o) (h₂ : o < e + n) :
    mixV V mk e n o = V o ^^^ mk.getD (o - e) 0 := by
  simp only [mixV]; rw [ifp ⟨h₁, h₂⟩]

theorem mix_out {V : Nat → Byte} {mk : List Byte} {e n o : Nat} (h : o < e ∨ e + n ≤ o) :
    mixV V mk e n o = V o := by
  simp only [mixV]; rw [ifn (by omega_arith)]

section keep
variable {P : EP} {σ : State} {rs : List Region} {m m' : Mem}

theorem K0.keep (hk : K0 h P σ m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotR P.lay sRes).Disjoint r) :
    K0 h P σ m' :=
  ⟨hk.1, hk.2.1, slot_keep hf hd hk.2.2.1, hk.2.2.2⟩

theorem LH.keep (hl : LH h P σ m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sR P.scr oLh h.H.D).Disjoint r) :
    LH h P σ m' :=
  sbytes_keep hf hd (by have := h.D_le; oomega) hl

theorem EMv.keep {f : Nat → Byte} (he : EMv P m f) (hf : Frame rs m m') (hK : P.K ≤ 1024)
    (hd : ∀ r ∈ rs, (sR P.scr oEm P.K).Disjoint r) : EMv P m' f :=
  sbytes_keep hf hd (by oomega) he

end keep

/-! ## The label's hash -/

/-- After the label's hash. -/
abbrev U1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ (K0 h P σ s.mem ∧ EMv P s.mem (V P σ)) ∧ LH h P σ s.mem

/-- The label's hash function's table, the argument 23, in a buffer only read. -/
theorem tblL_of {P : EP} {σ : State} (hi : In P σ) :
    ∃ R ∈ P.lay.ro, ∀ o, o + 4 ≤ 44 → R.Contains (VG.X86.addr P.tabL o) 4 := by
  obtain hf := hi.ok.fits P.TABL (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tabL.isLt; omega_using [])] at hf
  refine ⟨P.TABL, by simp, fun o ho => ?_⟩
  show (⟨P.tabL.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tabL o) 4
  rw [addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- What the label's hash keeps, with its table's address in its slot. -/
abbrev L0 (P : EP) (σ : State) (m : Mem) : Prop :=
  (K0 h P σ m ∧ EMv P m (V P σ)) ∧ m.readW (P.lay.fr sTab) 32 = P.tabL

/-- The label's hash function's table's address to its slot, and the label's
hash, with that table's hash function `h`. -/
theorem labT_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => (C2 h.H.D P σ s ∧ isa.eval .b s = some false) ∧ s.syms = σ.syms)
      (.seq (.block (tabSlot 23)) (hashLabelT f 17 oLh)) (fun σ s => U1 h P σ s ∧ s.syms = σ.syms) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.D_le
  obtain hl := ok.fits P.LAB (by simp)
  simp only [BitVec.toNat_setWidth] at hl
  rw [Nat.mod_eq_of_lt (by have := P.lab.isLt; omega_arith)] at hl
  obtain hlab : RBuf P.lay P.lab P.ll := ⟨hl, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  obtain dS : ∀ {o n : Nat}, o + n ≤ oRsa → Region.Disjoint ⟨P.lab.setWidth 64, P.ll⟩ (sR P.scr o n) :=
    fun hon => (hg.ro ok hon (R := P.LAB) (by simp)).symm
  -- The table's address to its slot.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ L0 h P σ s.mem) ∧ s.syms = σ.syms)
    (VP.syms (VP.taint [.esp, .ebp] tabSlot23_taint (sp_bp fun _ _ h => h.1.1)
      fun σ s ⟨⟨hc, hi, he, hres, hk, cf⟩, e⟩ => ?_)) ?_
  · have hkD : 2 * h.H.D + 2 ≤ P.K := by
      by_contra hf
      simp only [eval, cf, decide_eq_true (show P.K < 2 * h.H.D + 2 by omega_arith)] at e
      exact absurd e (by decide)
    simp only [tabSlot, ld, st]
    refine hc.wp_arg hg (j := 23) (by simp) (by decide) (by decide) fun t1 c1 u1 =>
      c1.wp_st hg (d := sTab) (by decide) fun t2 c2 m2 => WP.block_nil ?_
    obtain fr : Frame [slotR P.lay sTab] s.mem t2.mem := by
      rw [m2.mem, u1.mem]; exact slot_frame _ _ _ _
    refine ⟨c2, ⟨⟨hi, hkD, slot_keep fr (fun r hr => ?_) hres, hk⟩,
      sbytes_keep fr (slot_em hi (by decide)) (by unfold oEm; omega_using [hK]) he⟩, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact slotSep (L := P.lay) (by decide) (by decide) (by decide)
    · rw [m2.mem, Mem.readW_writeW_self32, u1.gpr]; rfl
  -- The label's hash.
  refine (labelT_vp hg h (f := f) (p := P.tabL) (ai := P.aiL) (au := P.auL) (af := P.afL) (tblL_of hi₀) fne
    (j := 17) (o := oLh) (ll := P.ll) (lab := P.lab) (by simp) updLab17_taint finLab17_taint
    rfl rfl hlab (dS (by oomega)) (dS (by oomega)) (ok.low_buf (R := P.LAB) (.inl (by simp))).symm (by oomega)
    (by oomega) (labB := labB P) (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := L0 h P) ?_ (fun _ _ hm => hm.2) (fun σ _ hm => hTL σ hm.1.1.1.tabTL)).mono
    (fun _ _ h => h) fun σ s ⟨⟨hc, ⟨hk, _⟩, hd⟩, sy⟩ => ⟨⟨hc, hk, hd⟩, sy⟩
  intro σ m m' ⟨⟨hk, he⟩, hs⟩ hf
  obtain dslot : ∀ d, d + 4 ≤ frameBytes → ∀ r ∈ [sR P.scr oSt h.H.S, sR P.scr oCW h.ok.Wb, P.lay.LOW,
      sR P.scr oLh h.H.F], (slotR P.lay d).Disjoint r := fun d hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd])
    · exact hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd])
    · exact Lay.fr_low (by unfold frameBytes at hd; omega_using [hd]) (by show (3448 : Nat) ≤ 2 ^ 32; decide)
    · exact hg.slot ok (by oomega) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd])
  refine ⟨⟨hk.keep h hf (dslot sRes (by decide)), he.keep hf hK fun r hr => ?_⟩, slot_keep hf (dslot sTab (by decide)) hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact hg.low ok (by oomega)
  · exact Geo.sep (by oomega) (by oomega) (by oomega)

/-! ## The seed -/

/-- What unmasking keeps: `K0`, `lHash` and `EM`'s first byte. -/
abbrev X1 (P : EP) (σ : State) (m : Mem) : Prop := K0 h P σ m ∧ LH h P σ m ∧ m (sa P.scr (oEm + 0)) = V P σ 0

theorem x1_keep {P : EP} (hg : Geo P.lay P.scr) {dOff dl : Nat} (hfd : dOff + dl ≤ oBuf) (h0 : oEm + 1 ≤ dOff) :
    ∀ σ m m', X1 h P σ m → Frame (mgfW g P.lay P.scr dOff dl) m m' → X1 h P σ m' := by
  intro σ m m' ⟨hk, hl, h0'⟩ hf
  have := g.S_le; have := g.Wb_le; have := g.F_le; have := h.D_le
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hk.keep h hf (mgfW_slot g hg hfd (by decide) (by decide) (by decide)), hl.keep h hf fun r hr => ?_, ?_⟩
  · simp only [mgfW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact hg.low ok (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
  · rw [← h0']
    exact hf _ fun r hr => mgfW_byte g hg hfd (o := oEm + 0) (by oomega) (by oomega) (by omega_arith) r hr _
      (Region.contains_self _ _)

/-- Four slots written, and the memory around them. -/
theorem slots4 {L : Lay} {scr : BitVec 32} {σ s t : State} (hc : Ctx L scr σ s) (hg : Geo L scr)
    {v1 v2 v3 v4 : BitVec 32}
    (m : t.mem = (((s.mem.writeW (L.fr sDst) v1).writeW (L.fr sDstLen) v2).writeW (L.fr sSrc) v3).writeW
      (L.fr sSrcLen) v4)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) :
    Ctx L scr σ t ∧ Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] s.mem t.mem ∧
      t.mem.readW (L.fr sSrc) 32 = v3 ∧ t.mem.readW (L.fr sSrcLen) 32 = v4 ∧
      t.mem.readW (L.fr sDst) 32 = v1 ∧ t.mem.readW (L.fr sDstLen) 32 = v2 := by
  obtain fr : Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, fr, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · rw [m, Lay.readW_fr_other (d := sSrc) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDst) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sDstLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDstLen) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDstLen) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]

/-- The slots' frame misses our part of `scratch`. -/
theorem slots4_dis {L : Lay} {scr : BitVec 32} (hg : Geo L scr) :
    ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen],
      (sR scr o n).Disjoint r := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro o n hon r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm

theorem x1_keep4 {P : EP} (hg : Geo P.lay P.scr) {σ : State} {m m' : Mem}
    (hf : Frame [slotR P.lay sDst, slotR P.lay sDstLen, slotR P.lay sSrc, slotR P.lay sSrcLen] m m')
    (hx : X1 h P σ m) : X1 h P σ m' := by
  have := h.D_le
  refine ⟨hx.1.keep h hf fun r hr => ?_, hx.2.1.keep h hf (slots4_dis hg _ _ (by oomega)), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [← hx.2.2]
    exact sbytes_keep (o := oEm) (n := 1) hf (slots4_dis hg _ _ (by oomega)) (by oomega)
      (f := fun _ => m (sa P.scr (oEm + 0))) (fun i hi => by rw [show i = 0 by omega_arith]) 0 (by decide)

/-- `k - hLen - 1`, from argument 4. -/
theorem kd_eq {P : EP} {σ : State} {m : Mem} (hk : K0 h P σ m) :
    BitVec.ofNat 32 P.K - BitVec.ofNat 32 (h.H.D + 1) = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
  rw [sub_ofNat (by have := hk.2.1; omega_arith), Nat.sub_add_eq]

/-- The slots for unmasking the seed with MGF1 of `maskedDB`. -/
theorem seed_vp (P : EP) :
    VP (U1 h P) (.block (seedArgs h.H 4))
      (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = V P σ (1 + i)) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)).getD i 0) := by
  refine VP.taint [.esp, .ebp] h.certs.seedArgs4 (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hk, he⟩, hl⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hk.2.1
  simp only [seedArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (by decide) fun t5 c5 m5 => ?_
  refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => ?_
  refine ((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).wp_st hg (by decide) fun t8 c8 m8 => ?_
  refine c8.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t9 c9 u9 => ?_
  refine wp_subi fun t10 u10 _ _ => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  obtain e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by rw [u2.gpr, u1.gpr, hc.ebp]
  obtain e7 : t7.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by
    rw [u7.gpr, u6.gpr, m5.gpr, u4.other _ (by decide), m3.gpr, u2.other _ (by decide), u1.other _ (by decide),
      hc.ebp]
  obtain e10 : t10.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u10.gpr, u9.gpr]; exact kd_eq h hk
  obtain m11 : t11.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW
      (P.lay.fr sDstLen) (BitVec.ofNat 32 h.H.D)).writeW (P.lay.fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW (P.lay.fr sSrcLen)
          (BitVec.ofNat 32 (P.K - h.H.D - 1)) := by
    rw [m11.mem, e10, u10.mem, u9.mem, m8.mem, e7, u7.mem, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  obtain dis := slots4_dis hg
  refine ⟨c, ⟨x1_keep4 h hg fr ⟨hk, hl, he 0 (by omega_arith)⟩, r1, r2, r3, r4⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · rw [← he (1 + i) (by omega_arith), show oEm + (1 + i) = oEm + 1 + i by omega_arith]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1) (n := h.H.D)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + i))) (fun _ _ => rfl) i hi'
  · rw [srcB_getD _ _ hi', ← he (1 + h.H.D + i) (by omega_arith), show oEm + (1 + h.H.D + i) = oEm + 1 + h.H.D + i by omega_arith]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1 + h.H.D) (n := P.K - h.H.D - 1)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + h.H.D + i))) (fun _ _ => rfl) i hi'

/-- The slots for unmasking `DB` with MGF1 of the seed. -/
theorem db_vp (P : EP) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = V P σ (1 + i) ^^^ (mk3 h g P σ).getD i 0) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)).getD i 0)
      (.block (dbArgs h.H 4))
      (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = V3 h g P σ (1 + h.H.D + i)) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (srcB (V3 h g P σ) 1 h.H.D).getD i 0) := by
  refine VP.taint [.esp, .ebp] h.certs.dbArgs4 (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hx, _⟩, hsd, hdb⟩ => ?_
  have hk := hx.1
  have hi := hk.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hk.2.1
  simp only [dbArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_subi fun t5 u5 _ _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (by decide) fun t6 c6 m6 => ?_
  refine wp_mov fun t7 u7 => wp_addi fun t8 u8 => ?_
  refine ((c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)).wp_st hg (by decide) fun t9 c9 m9 => ?_
  refine wp_movi fun t10 u10 => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  obtain e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by rw [u2.gpr, u1.gpr, hc.ebp]
  obtain e5 : t5.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u5.gpr, u4.gpr]; exact kd_eq h hk
  obtain e8 : t8.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by
    rw [u8.gpr, u7.gpr, m6.gpr, u5.other _ (by decide), u4.other _ (by decide), m3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), hc.ebp]
  obtain m11 : t11.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW
      (P.lay.fr sDstLen) (BitVec.ofNat 32 (P.K - h.H.D - 1))).writeW (P.lay.fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW (P.lay.fr sSrcLen) (BitVec.ofNat 32 h.H.D) := by
    rw [m11.mem, u10.gpr, u10.mem, m9.mem, e8, u8.mem, u7.mem, m6.mem, e5, u5.mem, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  obtain dis := slots4_dis hg
  refine ⟨c, ⟨x1_keep4 h hg fr hx, r1, r2, r3, r4⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · rw [V3, mix_out (by omega_arith), sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hdb i hi', srcB_getD _ _ hi']
  · rw [srcB_getD _ _ hi', V3, mix_in (by omega_arith) (by omega_arith), show 1 + i - 1 = i by omega_arith]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hsd i hi'

/-! ## Unmasking -/

/-- After unmasking: `EM`'s place holds `V5`. -/
abbrev U5 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ X1 h P σ s.mem ∧ EMv P s.mem (V5 h g P σ)

/-- MGF1's table, the argument 24, in a buffer only read. -/
theorem tbl_of {P : EP} {σ : State} (hi : In P σ) :
    ∃ R ∈ P.lay.ro, ∀ o, o + 4 ≤ 44 → R.Contains (VG.X86.addr (P.lay.argv.getD 24 0) o) 4 := by
  obtain hf := hi.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.tab.isLt; omega_using [])] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨P.tab.setWidth 64, 11 * (32 / 8)⟩ : Region).Contains (VG.X86.addr P.tab o) 4
  rw [addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

theorem unmask_vp (P : EP) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => U1 h P σ s ∧ s.syms = σ.syms)
      (.seq (.block (seedArgs h.H 4)) (.seq (mgfXor f 24) (.seq (.block (dbArgs h.H 4)) (mgfXor f 24))))
      (fun σ s => U5 h g P σ s ∧ s.syms = σ.syms) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1.1.1, hs.1.2.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  obtain tab : ∀ σ m, X1 h P σ m → TabFacts g.H f (P.lay.argv.getD 24 0) P.ai P.au P.af σ :=
    fun σ m hx => hT σ hx.1.1.tabT
  obtain P1 := mpOf g hg (so := oEm + 1 + h.H.D) (sl := P.K - h.H.D - 1) (dOff := oEm + 1) (dl := h.H.D)
    (by omega_arith) hD0 (by oomega) (by oomega) (by oomega) (by oomega) (.inr (Nat.le_refl _))
    (seed := fun σ => srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)) (fun σ => srcB_length _ _ _)
    (x1_keep h g hg (by oomega) (by oomega)) (by simp) (tbl_of hi₀) tabArg24_taint tab fne
  obtain P2 := mpOf g hg (so := oEm + 1) (sl := h.H.D) (dOff := oEm + 1 + h.H.D) (dl := P.K - h.H.D - 1) hD0
    (by omega_arith) (by oomega) (by oomega) (by oomega) (by oomega) (.inl (Nat.le_refl _))
    (seed := fun σ => srcB (V3 h g P σ) 1 h.H.D) (fun σ => srcB_length _ _ _) (x1_keep h g hg (by oomega) (by oomega))
    (by simp) (tbl_of hi₀) tabArg24_taint tab fne
  refine VP.seq (VP.syms (seed_vp h P)) (VP.seq (mgf_vp g P1 (dstv := fun σ i => V P σ (1 + i)))
    (VP.seq (VP.syms (db_vp h g P)) ((mgf_vp g P2 (dstv := fun σ i => V3 h g P σ (1 + h.H.D + i))).mono
      (fun _ _ hh => hh) fun σ s ⟨⟨hc, ⟨hx, _⟩, hdb, hsd⟩, sy⟩ => ⟨⟨hc, hx, fun x hx' => ?_⟩, sy⟩)))
  by_cases h0 : x = 0
  · subst h0
    rw [hx.2.2, V5, mix_out (by omega_arith), V3, mix_out (by omega_arith)]
  by_cases h1 : x < 1 + h.H.D
  · have e := hsd (x - 1) (by omega_arith)
    rw [show oEm + 1 + (x - 1) = oEm + x by omega_arith, srcB_getD _ _ (by omega_arith), show 1 + (x - 1) = x by omega_arith] at e
    rw [e, V5, mix_out (by omega_arith)]
  · have e := hdb (x - 1 - h.H.D) (by omega_arith)
    rw [show oEm + 1 + h.H.D + (x - 1 - h.H.D) = oEm + x by omega_arith,
      show 1 + h.H.D + (x - 1 - h.H.D) = x by omega_arith] at e
    rw [e, V5, mix_in (by omega_arith) (by omega_arith), show x - (1 + h.H.D) = x - 1 - h.H.D by omega_arith]

end VG.Proof.RsaOaep.X86.Dec

end

end


/-!
# RSAES-OAEP decryption on x86: `EM`'s first byte and `lHash`

As on ARMv7 (`Proof/RsaOaep/Arm/DecAcc.lean`): `lHash'` compared with
`lHash` (`cmpLoop_vp`, of RSASSA-PSS), then the accumulator `acc` (in its
slot) zero exactly when `EM`'s first byte is zero and `lHash' = lHash`
(`acc_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sAcc countLoop cmpBody)

variable (h g : OHash)

/-- What the checks keep: `X1` and `EM` unmasked. -/
abbrev Y (P : EP) (σ : State) (m : Mem) : Prop := X1 h P σ m ∧ EMv P m (V5 h g P σ)

/-- `EM`'s first byte is zero and `lHash' = lHash`. -/
abbrev hdOk (P : EP) (σ : State) : Prop :=
  V P σ 0 = 0 ∧ ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0

/-- After the checks of `EM`'s first byte and `lHash'`. -/
abbrev A1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ ∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧
    (a = 0 ↔ hdOk h g P σ)

theorem setWidth_byte_eq_zero (b : Byte) : b.setWidth 32 = 0 ↔ b = 0 := by
  constructor
  · intro e; have := congrArg (BitVec.setWidth 8) e; simpa using this
  · rintro rfl; rfl

theorem or_eq_zero32 (a b : BitVec 32) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := BitVec.or_eq_zero_iff

theorem acc_vp (P : EP) :
    VP (U5 h g P) (.seq (.block (cmpSet h.H)) (.seq (countLoop cmpBody) (.block accPut))) (A1 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1, hs.2.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  -- The comparison's registers.
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 oLh ∧
      s.gpr .ecx = BitVec.ofNat 32 h.H.D ∧ s.gpr .edx = 0)
    (VP.taint [.esp, .ebp] h.certs.cmpSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx, he⟩ => ?_) ?_
  · simp only [cmpSet, atS, addi, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 =>
      wp_movi fun t5 u5 => wp_movi fun t6 u6 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (((((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
        (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
    · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact ⟨hx, he⟩
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · simp (disch := decide) only [u6.other, u5.other, u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
    · rw [u6.gpr]
    · rw [u6.other _ (by decide), u5.gpr]; rfl
  refine VP.seq (Vf.cmpLoop_vp hg (oa := oEm + 1 + h.H.D) (ob := oLh) (n := h.H.D) hD0 (by oomega) (by oomega)
    (X := Y h g P) (f := fun σ i => V5 h g P σ (1 + h.H.D + i)) (g := fun σ i => (lhB h P σ).getD i 0)
    (fun σ m hy i hi => by
      rw [show oEm + 1 + h.H.D + i = oEm + (1 + h.H.D + i) by omega_using []]; exact hy.2 _ (by omega_using [hfit, hi]))
    fun σ m hy i hi => hy.1.2.1 i hi) ?_
  -- `acc := EM[0] ∨ edx`, to its slot.
  refine VP.taint [.esp, .ebp] accPut_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hy, he⟩ => ?_
  have hi := hy.1.1.1
  simp only [accPut, atS, addi, st, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  obtain c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  obtain e2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 oEm := by rw [u2.gpr, u1.gpr, hc.ebp]
  obtain m2 : t2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine wp_movzx8 (a := sa P.scr (oEm + 0)) (by show t2.ea ⟨.esi, 0⟩ = _; rw [ea_at, e2]; exact hg.addrD (by oomega))
    (hg.rd c2.st (by oomega)) fun t3 u3 => wp_or fun t4 u4 => ?_
  obtain c4 := (c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
  refine c4.wp_st hg (d := sAcc) (by decide) fun t5 c5 m5 => WP.block_nil ?_
  obtain fr : Frame [slotR P.lay sAcc] s.mem t5.mem := by
    rw [m5.mem, u4.mem, u3.mem, m2]; exact slot_frame _ _ _ _
  obtain dS : ∀ {o n : Nat}, o + n ≤ oRsa → ∀ r ∈ [slotR P.lay sAcc], (sR P.scr o n).Disjoint r :=
    fun hon r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  refine ⟨c5, ⟨⟨hy.1.1.keep h fr fun r hr => ?_, hy.1.2.1.keep h fr (dS (by oomega)), ?_⟩,
    hy.2.keep fr hK (dS (by oomega))⟩, t4.gpr .edx, by rw [m5.mem, Mem.readW_writeW_self32], ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · rw [← hy.1.2.2]
    exact sbytes_keep (o := oEm) (n := 1) fr (dS (by oomega)) (by oomega) (f := fun _ => s.mem (sa P.scr (oEm + 0)))
      (fun i hi => by rw [show i = 0 by omega_using [hi]]) 0 (by decide)
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), u3.gpr, m2,
      or_eq_zero32, he, setWidth_byte_eq_zero, hy.1.2.2]
    exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

end VG.Proof.RsaOaep.X86.Dec

end

end


/-!
# RSAES-OAEP decryption on x86: the scan of `T`

As on ARMv7 (`Proof/RsaOaep/Arm/DecScan.lean`): `scan_vp`: the scan of `n`
bytes of our part of `scratch` finds the index (`pzS`) and the value (`vzS`)
of their first byte that is not zero, if any (`nfS`), without a branch. As
in RSASSA-PSS (`Proof/RsaPss/X86/VfScan.lean`), the index and the value are
kept in their slots, through `ebp`, so the loop's states are states of the
body (`Lay.St`), not `Ctx`. `tscan_vp`: on `T = DB[hLen..]`, then `scanEnd`
loads `scratch` into `ebp` again, and `acc` takes in that this byte is
`0x01`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sAcc sPos sVal countLoop scanBody isZero)

/-! ## The scan -/

section Scan

/-- The bytes, as a list. -/
abbrev sL (n : Nat) (f : Nat → Byte) : List Byte := (List.range n).map f

/-- Where the zeros end. -/
abbrev lzS (n : Nat) (f : Nat → Byte) : Nat := RsaPss.lz (sL n f)

/-- The index and value of the first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzS (n : Nat) (f : Nat → Byte) (j : Nat) : Nat := if lzS n f < j then lzS n f else 0
abbrev vzS (n : Nat) (f : Nat → Byte) (j : Nat) : Byte := if lzS n f < j then f (lzS n f) else 0
abbrev nfS (n : Nat) (f : Nat → Byte) (j : Nat) : BitVec 32 := if lzS n f < j then 0 else BitVec.allOnes 32

/-- The mask `sub r, 1; sbb r, r` leaves of a byte. -/
theorem bz : ∀ b : Byte, (if decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32
    else 0) = if b = 0 then BitVec.allOnes 32 else (0 : BitVec 32) := by decide

variable {L : Lay} {scr : BitVec 32}

/-- After `j` bytes of the scan of the `n` bytes at `o`. -/
structure SC (L : Lay) (scr : BitVec 32) (o n : Nat) (f : Nat → Byte) (j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr + BitVec.ofNat 32 (o + j)
  edi : s.gpr .edi = BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  ebx : s.gpr .ebx = nfS n f j
  pos : s.mem.readW (L.fr sPos) 32 = BitVec.ofNat 32 (pzS n f j)
  val : s.mem.readW (L.fr sVal) 32 = (vzS n f j).setWidth 32

theorem sL_getD {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) : (sL n f).getD j 0 = f j := by
  simp [sL, List.getD_eq_getElem?_getD, hj]

theorem sL_length (n : Nat) (f : Nat → Byte) : (sL n f).length = n := by simp [sL]

theorem lzS_le (n : Nat) (f : Nat → Byte) : lzS n f ≤ n := by
  obtain e := RsaPss.lz_le (sL n f); rwa [sL_length] at e

/-- One byte of the scan. -/
theorem scan_step {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) (b : Byte) (hb : b = f j) :
    let m : BitVec 32 := ((if b = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&& nfS n f j
    BitVec.ofNat 32 (pzS n f j) ||| BitVec.ofNat 32 j &&& m = BitVec.ofNat 32 (pzS n f (j + 1)) ∧
    (vzS n f j).setWidth 32 ||| b.setWidth 32 &&& m = (vzS n f (j + 1)).setWidth 32 ∧
    nfS n f j &&& (m ^^^ BitVec.allOnes 32) = nfS n f (j + 1) := by
  intro m
  obtain az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  obtain za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  obtain oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  obtain zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  obtain hlt := lzS_le n f
  rcases Nat.lt_trichotomy (lzS n f) j with hl | hl | hl
  · have h8 : m = 0 := by simp only [m, nfS, ite_eq_left hl, az]
    simp only [h8, az, oz, pzS, vzS, nfS, ite_eq_left hl, ite_eq_left (by omega_arith : lzS n f < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← sL_getD (n := n) (f := f) (by omega_arith)]
      exact RsaPss.getD_lz_ne (by rw [sL_length]; show lzS n f < n; omega_arith)
    obtain h8 : m = BitVec.allOnes 32 := by
      simp only [m, hne, ite_false, nfS, ite_eq_right (show ¬ lzS n f < j by omega_arith)]; decide
    simp only [h8, BitVec.and_allOnes, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega_arith),
      ite_eq_left (show lzS n f < j + 1 by omega_arith)]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← sL_getD (n := n) (f := f) hj]; exact RsaPss.getD_lt_lz hl
    obtain h8 : m = 0 := by
      simp only [m, hz, ite_true]; rw [show BitVec.allOnes 32 ^^^ BitVec.allOnes 32 = 0 by decide, za]
    simp only [h8, az, oz, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega_arith),
      ite_eq_right (show ¬ lzS n f < j + 1 by omega_arith)]
    exact ⟨trivial, trivial, by decide⟩

/-- The scan of the `n` bytes at `o`, keeping `X`, which writes to the
index's and the value's slots keep. -/
theorem scan_vp (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa) (hn : 0 < n) {f : State → Nat → Byte}
    {X : State → Mem → Prop} (hX : ∀ σ m, X σ m → ∀ i < n, m (sa scr (o + i)) = f σ i)
    (hW : ∀ σ m d (v : BitVec 32), X σ m → d = sVal ∨ d = sPos → X σ (m.writeW (L.fr d) v)) :
    VP (fun σ s => L.St σ s ∧ X σ s.mem ∧ SC L scr o n (f σ) 0 s)
      (countLoop scanBody)
      (fun σ s => L.St σ s ∧ X σ s.mem ∧ SC L scr o n (f σ) n s) := by
  have fit := hg.fit
  have hF := hg.F
  unfold oRsa at fit ho
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ L.St σ s ∧ X σ s.mem ∧ SC L scr o n (f σ) (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, hs⟩ => ⟨by omega_arith, hc, hx,
    by rw [show n - (n - 1 + 1) = 0 by omega_arith]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hs, hx, hp⟩ => ?_
  · obtain ⟨-, s₁, -, p₁⟩ := h₁
    obtain ⟨-, s₂, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [s₁.sp, s₂.sp]
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ecx, p₂.ecx]
  generalize hj : n - (k + 1) = j at hp
  obtain hjn : j < n := by omega_arith
  obtain ad : addr (scr + BitVec.ofNat 32 (o + j)) 0 = sa scr (o + j) := by
    rw [hg.addrD (by unfold oRsa; omega_arith), Nat.add_zero]
  obtain rd : InRegions (s.rd ++ s.wr) (sa scr (o + j)) 1 := hg.rd hs (by unfold oRsa; omega_arith)
  obtain hb := hX σ s.mem hx j hjn
  simp only [scanBody, isZero, ld, st, addi, Impl.RsaPkcs1Sig.X86.at_, List.cons_append, List.nil_append]
  refine wp_movzx8 (a := sa scr (o + j)) (by rw [ea_at, hp.esi]; exact ad) rd fun t1 u1 => ?_
  refine wp_mov fun t2 u2 => wp_subi fun t3 u3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => ?_
  refine wp_xorI fun t5 u5 => wp_and fun t6 u6 => wp_and fun t7 u7 => ?_
  obtain s7 : L.St σ t7 := (((((((hs.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).upd u4
    (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide))
  refine s7.wp_slot (d := sVal) (by rw [hF]; decide) (by decide) fun t8 s8 u8 => wp_or fun t9 u9 => ?_
  refine (s8.upd u9 (by decide)).wp_strFr (d := sVal) (by rw [hF]; decide) fun t10 s10 m10 => ?_
  refine wp_mov fun t11 u11 => wp_and fun t12 u12 => ?_
  obtain s12 : L.St σ t12 := (s10.upd u11 (by decide)).upd u12 (by decide)
  refine s12.wp_slot (d := sPos) (by rw [hF]; decide) (by decide) fun t13 s13 u13 => wp_or fun t14 u14 => ?_
  refine (s13.upd u14 (by decide)).wp_strFr (d := sPos) (by rw [hF]; decide) fun t15 s15 m15 => ?_
  refine wp_xorI fun t16 u16 => wp_and fun t17 u17 => wp_addi fun t18 u18 => wp_addi fun t19 u19 => ?_
  refine wp_subi fun t20 u20 _ z20 => WP.block_nil ?_
  -- The values.
  obtain b1 : t1.gpr .eax = (f σ j).setWidth 32 := by rw [u1.gpr, hb]
  obtain e2 : t2.gpr .edx = (f σ j).setWidth 32 := by rw [u2.gpr, b1]
  rw [e2, bz] at u4
  obtain mk : t6.gpr .edx = ((if f σ j = 0 then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32) &&&
      nfS n (f σ) j := by
    simp (disch := decide) only [u6.gpr, u5.gpr, u4.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hp.ebx]
  obtain stp := scan_step hjn _ rfl (f := f σ)
  obtain m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain a6 : t6.gpr .eax = (f σ j).setWidth 32 := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, b1]
  obtain vV : t9.gpr .ebp = (vzS n (f σ) (j + 1)).setWidth 32 := by
    rw [u9.gpr, u8.gpr, u8.other .eax (by decide), u7.gpr, mk, m7, hp.val, a6]
    exact stp.2.1
  obtain d9 : t9.gpr .edx = t6.gpr .edx := by simp (disch := decide) only [u9.other, u8.other, u7.other]
  obtain i9 : t9.gpr .edi = BitVec.ofNat 32 j := by
    simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other,
      u1.other, hp.edi]
  obtain mm10 : t10.mem = s.mem.writeW (L.fr sVal) ((vzS n (f σ) (j + 1)).setWidth 32) := by
    rw [m10.mem, vV, u9.mem, u8.mem, m7]
  obtain pV : t14.gpr .ebp = BitVec.ofNat 32 (pzS n (f σ) (j + 1)) := by
    rw [u14.gpr, u13.gpr, u13.other .eax (by decide), u12.gpr, u11.gpr, u12.mem, u11.mem, mm10,
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hp.pos, u11.other .edx (by decide),
      m10.gpr, d9, mk, i9]
    exact stp.1
  obtain mm15 : t20.mem = (s.mem.writeW (L.fr sVal) ((vzS n (f σ) (j + 1)).setWidth 32)).writeW
      (L.fr sPos) (BitVec.ofNat 32 (pzS n (f σ) (j + 1))) := by
    rw [u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, m15.mem, pV, u14.mem, u13.mem, u12.mem, u11.mem, mm10]
  obtain s20 : L.St σ t20 :=
    ((((s15.upd u16 (by decide)).upd u17 (by decide)).upd u18 (by decide)).upd u19 (by decide)).upd u20 (by decide)
  obtain kd : X σ t20.mem := by
    rw [mm15]; exact hW _ _ _ _ (hW _ _ _ _ hx (.inl rfl)) (.inr rfl)
  obtain c19 : t19.gpr .ecx = BitVec.ofNat 32 (n - j) := by
    simp (disch := decide) only [u19.other, u18.other, u17.other, u16.other, m15.gpr, u14.other, u13.other,
      u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
      u2.other, u1.other, hp.ecx]
  obtain sk : SC L scr o n (f σ) (j + 1) t20 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u20.other, u19.other, u18.gpr, u17.other, u16.other, m15.gpr, u14.other,
        u13.other, u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other,
        u3.other, u2.other, u1.other, hp.esi]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · simp (disch := decide) only [u20.other, u19.gpr, u18.other, u17.other, u16.other, m15.gpr, u14.other,
        u13.other, u12.other, u11.other, m10.gpr, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other,
        u3.other, u2.other, u1.other, hp.edi]
      rw [BitVec.ofNat_add_ofNat]
    · rw [u20.gpr, c19, ofNat_pred (by omega_arith), Nat.sub_sub]
    · have b9 : t9.gpr .ebx = nfS n (f σ) j := by
        simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
          u2.other, u1.other, hp.ebx]
      obtain x16 : t16.gpr .edx = t6.gpr .edx ^^^ BitVec.allOnes 32 := by
        rw [u16.gpr, m15.gpr, u14.other .edx (by decide), u13.other .edx (by decide), u12.other .edx (by decide),
          u11.other .edx (by decide), m10.gpr, d9]
      obtain b16 : t16.gpr .ebx = t9.gpr .ebx := by
        rw [u16.other .ebx (by decide), m15.gpr, u14.other .ebx (by decide), u13.other .ebx (by decide),
          u12.other .ebx (by decide), u11.other .ebx (by decide), m10.gpr]
      rw [u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide), u17.gpr, x16, b16, b9, mk]
      exact stp.2.2
    · rw [mm15, Mem.readW_writeW_self32]
    · rw [mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  rw [c19, ofNat_pred (by omega_arith), Nat.sub_sub, ofNat_beq_zero (by omega_arith), show n - (j + 1) = k by omega_arith] at z20
  refine ⟨?_, fun h0 => ⟨s20, kd, (show j + 1 = n by omega_arith) ▸ sk⟩,
    fun hpos => ⟨by omega_arith, s20, kd, by rw [show n - k = j + 1 by omega_arith]; exact sk⟩⟩
  show eval .ne t20 = _
  simp only [eval, z20]
  by_cases h0 : k = 0 <;> simp [h0] <;> omega_arith

end Scan

/-! ## `T` -/

variable (h g : OHash)

/-- `T = DB[hLen..]`, its length, and the index after its first byte not zero. -/
abbrev tN (P : EP) : Nat := P.K - (2 * h.H.D + 1)
abbrev T (P : EP) (σ : State) (j : Nat) : Byte := V5 h g P σ (1 + 2 * h.H.D + j)
abbrev idx (P : EP) (σ : State) : Nat := pzS (tN h P) (T h g P σ) (tN h P)

/-- The decoding's checks all pass. -/
abbrev allOk (P : EP) (σ : State) : Prop :=
  hdOk h g P σ ∧ lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1

/-- After the scan. -/
abbrev A2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
    (∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧ (a = 0 ↔ allOk h g P σ)) ∧
    s.mem.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ)

theorem endB : ∀ b : Byte, (b.setWidth 32 ^^^ (1 : BitVec 32) = 0 ↔ b = 1) := by decide

/-- What the end of the scan adds to `acc`. -/
theorem endX (c : Prop) [Decidable c] (b : Byte) :
    ((if c then b else 0).setWidth 32 ^^^ (1 : BitVec 32)) ||| (if c then (0 : BitVec 32) else BitVec.allOnes 32) >>> 31
      = 0 ↔ c ∧ b = 1 := by
  by_cases hc : c
  · simp only [hc, ite_true, true_and]
    rw [show (0 : BitVec 32) >>> 31 = 0 from rfl, show ∀ x : BitVec 32, x ||| 0 = x from fun x => BitVec.or_zero]
    exact endB b
  · simp only [hc, ite_false, false_and, iff_false]
    decide

/-- What the scan keeps. -/
abbrev Xs (P : EP) (σ : State) (m : Mem) : Prop :=
  Y h g P σ m ∧ ∃ a : BitVec 32, m.readW (P.lay.fr sAcc) 32 = a ∧ (a = 0 ↔ hdOk h g P σ)

theorem Y.slot {P : EP} {σ : State} {m : Mem} (hy : Y h g P σ m) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hr : d + 4 ≤ sRes ∨ sRes + 4 ≤ d) (v : BitVec 32) : Y h g P σ (m.writeW (P.lay.fr d) v) := by
  have hg := hy.1.1.1.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hy.1.1.1.k1024
  have hD := h.D_le
  obtain fr := slot_frame P.lay m d v
  obtain dS : ∀ {o n : Nat}, o + n ≤ oRsa → ∀ r ∈ [slotR P.lay d], (sR P.scr o n).Disjoint r :=
    fun hon r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok hon (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_arith)).symm
  refine ⟨⟨hy.1.1.keep h fr fun r hr => ?_, hy.1.2.1.keep h fr (dS (by oomega)), ?_⟩, hy.2.keep fr hK (dS (by oomega))⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) hd (by omega_arith)
  · rw [← hy.1.2.2]
    exact sbytes_keep (o := oEm) (n := 1) fr (dS (by oomega)) (by oomega) (f := fun _ => m (sa P.scr (oEm + 0)))
      (fun i hi => by rw [show i = 0 by omega_arith]) 0 (by decide)

theorem tscan_vp (P : EP) :
    VP (A1 h g P) (.seq (.block (scanSet h.H)) (.seq (countLoop scanBody) (.block scanEnd))) (A2 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1.1, hs.2.1.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  obtain xs : ∀ σ m d (v : BitVec 32), Xs h g P σ m → d = sVal ∨ d = sPos → Xs h g P σ (m.writeW (P.lay.fr d) v) := by
    intro σ m d v ⟨hy, a, ha, he⟩ hd
    refine ⟨hy.slot h g (d := d) (by rcases hd with rfl | rfl <;> decide)
      (by rcases hd with rfl | rfl <;> decide) v, a, ?_, he⟩
    rw [Lay.readW_fr_other _ _ _ (by rcases hd with rfl | rfl <;> decide) (by decide)
      (by rcases hd with rfl | rfl <;> decide)]
    exact ha
  refine VP.seq (G := fun σ s => P.lay.St σ s ∧ Xs h g P σ s.mem ∧
      SC P.lay P.scr (oEm + 1 + 2 * h.H.D) (tN h P) (T h g P σ) 0 s)
    (VP.taint [.esp, .ebp] h.certs.scanSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hy, ha⟩ => ?_)
    (VP.seq (scan_vp hg (o := oEm + 1 + 2 * h.H.D) (n := tN h P) (by unfold tN; oomega) (by unfold tN; omega_arith) (f := T h g P)
      (X := Xs h g P) (fun σ m hx i hi => by
        rw [show oEm + 1 + 2 * h.H.D + i = oEm + (1 + 2 * h.H.D + i) by omega_arith]; exact hx.1.2 _ (by unfold tN at hi; omega_arith)) xs) ?_)
  · simp only [scanSet, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    obtain c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine c2.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t3 c3 u3 => ?_
    refine wp_subi fun t4 u4 _ _ => wp_movi fun t5 u5 => wp_movi fun t6 u6 => ?_
    obtain c6 := ((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)
    refine c6.wp_st hg (d := sPos) (by decide) fun t7 c7 m7 => c7.wp_st hg (d := sVal) (by decide) fun t8 c8 m8 => ?_
    refine wp_movi fun t9 u9 => wp_subi fun t10 u10 _ _ => WP.block_nil ?_
    obtain m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    obtain ax : t6.gpr .eax = 0 := by rw [u6.gpr]; rfl
    obtain mem : t10.mem = (s.mem.writeW (P.lay.fr sPos) (0 : BitVec 32)).writeW (P.lay.fr sVal) (0 : BitVec 32) := by
      rw [u10.mem, u9.mem, m8.mem, m7.gpr, ax, m7.mem, ax, m6]
    refine ⟨((c8.upd u9 (by decide) (by decide)).upd u10 (by decide) (by decide)).st, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem]; exact xs _ _ _ _ (xs _ _ _ _ ⟨hy, ha⟩ (.inr rfl)) (.inl rfl)
    · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.other, u3.other,
        u2.gpr, u1.gpr, hc.ebp, Nat.add_zero]
    · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.gpr]
    · simp (disch := decide) only [u10.other, u9.other, m8.gpr, m7.gpr, u6.other, u5.other, u4.gpr, u3.gpr]
      show BitVec.ofNat 32 P.K - BitVec.ofNat 32 (2 * h.H.D + 1) = _
      rw [sub_ofNat (by omega_arith)]; rfl
    · rw [u10.gpr, u9.gpr]; simp only [nfS, Nat.not_lt_zero, ite_false]; decide
    · rw [mem, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
      simp only [pzS, Nat.not_lt_zero, ite_false]; rfl
    · rw [mem, Mem.readW_writeW_self32]
      simp only [vzS, Nat.not_lt_zero, ite_false]; rfl
  -- `scratch` into `ebp`, and `acc |= (val ⊕ 1) | notFound`.
  refine VP.taint [.esp] scanEnd_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.sp, h₂.1.sp])
    fun σ s ⟨hs, ⟨hy, a, ha, he⟩, sc⟩ => ?_
  simp only [scanEnd, ld, st]
  refine hs.wp_arg (dec_arg (j := 21) (by decide)) (by decide) fun t0 s0 u0 => ?_
  obtain c0 : Ctx P.lay P.scr σ t0 := ⟨s0, by rw [u0.gpr]; rfl⟩
  refine c0.wp_slot hg (d := sAcc) (by decide) (by decide) (by decide) fun t1 c1 u1 =>
    c1.wp_slot hg (d := sVal) (by decide) (by decide) (by decide) fun t2 c2 u2 => ?_
  refine wp_xorI fun t3 u3 => wp_or fun t4 u4 => wp_shr (n := 31) (by decide) fun t5 u5 _ => wp_or fun t6 u6 => ?_
  obtain c6 := (((c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide)
    (by decide)).upd u6 (by decide) (by decide)
  refine c6.wp_st hg (d := sAcc) (by decide) fun t7 c7 m7 => WP.block_nil ?_
  obtain m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u0.mem]
  obtain v6 : t6.gpr .eax = (a ||| ((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32))) |||
      nfS (tN h P) (T h g P σ) (tN h P) >>> 31 := by
    simp (disch := decide) only [u6.gpr, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other,
      u1.gpr, u1.other, u0.other, u1.mem, u0.mem, ha, sc.val, sc.ebx]
  refine ⟨c7, ?_, ⟨_, by rw [m7.mem, Mem.readW_writeW_self32], ?_⟩, ?_⟩
  · rw [m7.mem, m6]; exact hy.slot h g (d := sAcc) (by decide) (by decide) _
  · rw [v6, BitVec.or_assoc, or_eq_zero32, he, endX]
  · rw [m7.mem, m6, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact sc.pos

end VG.Proof.RsaOaep.X86.Dec
