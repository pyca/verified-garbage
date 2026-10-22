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

theorem dec_arg {j : Nat} (hj : j < 23) {P : EP} : j < P.lay.argv.length := by simp; omega

/-- An argument's place may be read. -/
theorem argR {P : EP} {σ t : State} (hg : Geo P.lay P.scr) (ct : Ctx P.lay P.scr σ t) {j : Nat}
    (hj : j < 23) : InRegions (t.rd ++ t.wr) (VG.X86.addr P.lay.B (Impl.RsaPkcs1Sig.X86.argOff frameBytes j)) 4 := by
  rw [hg.aArg ct.st.ok j (dec_arg hj), ct.st.rd, ct.st.wr]; exact ct.st.ok.arg_read (dec_arg hj)

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
  rcases (by omega : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega)]
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
    c1.wp_st hg (d := 4 * i) (by unfold frameBytes; omega) fun t2 c2 m2 => kk t2 ⟨c2, hi', ?_⟩
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
    (by unfold frameBytes; omega) fun t3 c3 m3 => kk t3 ⟨c3, hi', ?_⟩
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
  have hs1 : 1024 ≤ P.scl := by
    have := hi.slK; unfold Spec.RsaPss.scratchWords at this; omega
  rw [privArgs_eq, List.singleton_append]
  simp only [List.append_assoc, ld]
  refine hs.wp_arg (dec_arg (j := 21) (by decide)) (by decide) fun t0 s0 u0 => ?_
  have c0 : Ctx P.lay P.scr σ t0 := ⟨s0, by rw [u0.gpr]; rfl⟩
  have z0 : A0 P σ t0 0 := ⟨c0, hi, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
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
  have v : t21.gpr .eax = BitVec.ofNat 32 (P.scl - 1024) := by
    rw [u21.gpr, u20.gpr]
    exact Offset.ofNat_sub_ofNat (w := 32) (d := 1024) hs1
  have sl := slots_next s19 (by decide) _ (v.trans (by simp [outv, privArgv]))
  have m : t22.mem = t19.mem.writeW (P.lay.fr (4 * 19)) (t21.gpr .eax) := by
    rw [m22.mem, u21.mem, u20.mem]
  rw [← m] at sl
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  refine ⟨c22, hi, fun i hi' => ?_, by rw [c22.st.sp]; exact ok.BC, by rw [c22.st.sp]; show P.B.toNat + 80 ≤ _; omega,
    hi.kv, hi.el1, hi.elK, hi.pl1, hi.plK, hi.ql1, hi.qlK, ?_, by have := hi.scl32; omega⟩
  · rw [c22.st.sp, hg.aFr ok (4 * i) (by unfold frameBytes; omega)]
    exact sl i hi'
  · have hs := hi.slK; unfold Spec.RsaPss.scratchWords at hs; omega

/-! ## The call -/

/-- The call's output and working space, in `scratch`. -/
abbrev emR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oEm).setWidth 64, P.K⟩
abbrev scrR (P : EP) : Region := ⟨(P.scr + BitVec.ofNat 32 oRsa).setWidth 64, (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In P σ) :
    (P.scr + BitVec.ofNat 32 oEm).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oEm ∧
    (P.scr + BitVec.ofNat 32 oRsa).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 oRsa ∧
    Region.Sub (emR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (emR P).Disjoint (scrR P) ∧
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
  · rw [emR, e1]; exact Offset.sub_base _ (by unfold oEm; omega)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega)
  · rw [emR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega) (by unfold oEm; omega)
      (by unfold oRsa; omega)

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
def privName (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix

/-- `EM` and the result: the call. -/
theorem call_vp (P : EP) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (R1 P) (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (R2 P) := by
  have hv := Proof.Rsa.X86.PrivChecked.code_verified v
  have hst := Proof.Rsa.X86.PrivChecked.code_stack v
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
    have args0 : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
    have hsp := hc.st.sp
    rw [show P.lay.B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    have ro : ∀ R ∈ P.lay.ro, ∀ {w : Region}, Region.Sub w P.SCR → w.Disjoint R := fun R hR w hw =>
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
      · rw [args0]; exact (Lay.fr_low (by omega) (by show (3392 : Nat) ≤ 2 ^ 32; decide)).symm
      all_goals exact ok.low_buf (.inl (by simp))
    · intro r hr
      have hg := hi.geo
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega),
          hg.scr_lt (by decide)]
        unfold oEm; omega
      · show ((P.scr + BitVec.ofNat 32 oRsa).setWidth 64).toNat + (P.scl - 1024) * 8 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 80 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega)]
        omega
      all_goals exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    obtain ⟨hc, hi, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega)⟩
    have hA : Covers [⟨P.B.setWidth 64, 80⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 80) (by simp only [frameBytes]; omega)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (privWr P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
        s.wr :=
      (show Covers [emR P] s.wr by rw [emR, e1]; exact inS (by unfold oEm; omega)).cons
        ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    exact (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.CT (by simp)).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons Covers.nil)))))))
  · rw [hr.1.st.sp]
    have : 3392 ≤ P.B.toNat := hr.2.1.ok.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    show _ ≤ P.B.toNat
    omega
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
    have low : Region.Sub (below (s.gpr .esp) (stackUse (Proof.Rsa.X86.PrivChecked.privCode v) + 4)) P.lay.LOW := by
      rw [hsp, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega) ok.BC
    have hc' : Ctx P.lay P.scr σ s' := hc.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
      · exact ⟨P.lay.LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
      (cs .ebp (by simp [calleeSaved]))
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_post pa po
    rw [m₂, g₂ .eax (by decide)] at this
    have ro := fun {R : Region} (hR : R ∈ P.lay.ro) => hs.callEntry_ro (by show 4 ≤ 3392; decide) hR
    rw [ro (R := P.N) (by simp), hi.nB, ro (R := P.E) (by simp), hi.eB, ro (R := P.CT) (by simp),
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    obtain ⟨r0, hb, hl⟩ := em_of this
    refine ⟨hc', hi, fun i hi' => ?_, r0, hl⟩
    have e := hb i hi'
    rw [e1] at e
    refine Eq.trans ?_ e
    simp only [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

end VG.Proof.RsaOaep.X86.Dec
