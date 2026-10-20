module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_ffdh_check_domain` on AArch64: the stages of a run

Every input is public (`CdP`). A run from a state with the public data `p`
(`CR p`) goes through the shared stages (`Stage.lean`) of the data `p.D`, and
through those of q's checks.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckDomain

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data: the working space, the lengths, the domain's pointer and
octets, and the stack pointer. -/
structure CdP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  sp : Addr

/-- The run's data. -/
def CdP.D (p : CdP) : FD := ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, [], []⟩

@[simp] theorem CdP.D_hs (p : CdP) : p.D.hs = [] := rfl
theorem CdP.D_dom (p : CdP) : p.D.dom = p.dom := rfl
theorem CdP.D_k (p : CdP) : p.D.k = p.k := rfl
theorem CdP.D_dl (p : CdP) : p.D.dl = p.dl := rfl
@[simp] theorem CdP.D_srcs (p : CdP) : p.D.srcs = [] := rfl

/-- A state the contract allows, with the public data `p`. -/
def CR (p : CdP) (s : State) : Prop :=
  cdPre s ∧ s.sp = p.sp ∧ s.gpr .x3 = p.D.B ∧ (s.gpr .x4).toNat * 8 = p.D.Z ∧ (s.gpr .x2).toNat = p.D.k ∧
    (s.gpr .x1).toNat = p.D.dl ∧ s.gpr .x0 = p.D.dp ∧ cdDom s = p.D.dom

/-- The entry: the arguments into the header at `scratch`. -/
theorem cdEntry_ok {s : State} {B : Addr} (hB : s.gpr .x3 = B) (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block CheckDomain.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sDom) = s.gpr .x0 ∧ word t.mem B (8 * sDomLen) = s.gpr .x1 ∧
      word t.mem B (8 * sK) = s.gpr .x2 ∧ Outside B (8 * 16) (8 * 3) s.mem t.mem ∧ Keep [.x0] s t := by
  have eD : sDom = 16 := rfl
  have eL : sDomLen = 17 := rfl
  have eK : sK = 18 := rfl
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = ((s.mem.writeW (off B (8 * sDom)) (s.gpr .x0)).writeW (off B (8 * sDomLen)) (s.gpr .x1)).writeW
        (off B (8 * sK)) (s.gpr .x2)) (by
    unfold CheckDomain.entry
    brun [Crt.stw, hB, hdr_enc (show sDom < 32 by decide), hdr_enc (show sDomLen < 32 by decide),
      hdr_enc (show sK < 32 by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, k⟩ <;> rw [hm]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [word_writeW_self]
  · intro x hx
    rw [writeW_outside _ B _ (by omega_arith) x (by omega_arith), writeW_outside _ B _ (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by omega_arith)]

theorem cr_base (p : CdP) (s : State) (h : CR p s) : Base p.D s := by
  obtain ⟨B, Z, k, dl, dp, dom, sp⟩ := p
  unfold CdP.D at *
  obtain ⟨⟨hrd, hwr, dds, wD, wS, ⟨hk1, hk2⟩, hdl, hsl⟩, -, hB, hZ, hk, hdl', hdp, hdom⟩ := h
  subst hB hZ hk hdl' hdp hdom
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨Scr.of_mem (by rw [hwr]; simp) wS, hk1, hk2, hdl,
    show 128 * (s.gpr .x2).toNat + 256 ≤ (s.gpr .x4).toNat * 8 by omega_arith,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dds, bytesAt_length _ _ _, fun e he => absurd he List.not_mem_nil,
    fun q hq => absurd hq List.not_mem_nil⟩

/-- The entry's registers. -/
def entryRegs (p : CdP) (r : Reg) : BitVec 64 :=
  if r = .x0 then p.D.dp else if r = .x1 then BitVec.ofNat 64 p.D.dl else if r = .x2 then BitVec.ofNat 64 p.D.k else p.D.B

theorem cr_regs (p : CdP) (s : State) (h : CR p s) : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, hB, -, hk, hdl, hdp, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hB

theorem cr_e1 (p : CdP) (s : State) (h : CR p s) : WP isa (.block CheckDomain.entry) s fun t => E1 p.D t ∧ KX s t := by
  have hb := cr_base p s h
  have hn : p.D.B.toNat + p.D.Z ≤ 2 ^ 64 := hb.scr.nowrap
  have hZ : 128 * p.D.k + 256 ≤ p.D.Z := hb.hZ
  have hk1 : 64 ≤ p.D.k := hb.k1
  obtain ⟨⟨-, hwr, -⟩, -, hB, hZ', hk, hdl, hdp, -⟩ := h
  have hs : Scr s p.D.B p.D.Z := hb.scr
  have hw : ∀ i < 22, InRegions s.wr (off (s.gpr .x3) (8 * i)) 8 := fun i hi => by
    rw [hB]; exact hs.st (by omega_arith)
  refine WP.mono (cdEntry_ok rfl hw) fun t ⟨h0, hD, hL, hK, ho, k⟩ => ?_
  rw [hB] at h0 hD hL hK ho
  refine ⟨⟨hb.keep (InScr.of_outside ho (show 8 * 16 + 8 * 3 ≤ p.D.Z by omega_arith)) k, h0, ?_⟩, k.mono (by decide)⟩
  intro q hq
  simp only [FD.hdr, CdP.D_hs, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact hD.trans hdp
  · rw [hL, ← hdl, ofNat_toNat64]
  · rw [hK, ← hk, ofNat_toNat64]

/-! ## g and its range -/

abbrev CdP.G (p : CdP) : Nat := p.D.G
abbrev CdP.Q (p : CdP) : Nat := Spec.Rsa.os2ip p.D.qb
abbrev CdP.P (p : CdP) : Nat := p.D.P

/-- In the inner workspace for p. -/
def S1 (p : CdP) (t : State) : Prop := ∃ mi, In p.D mi t

/-- With g in `aXm`. -/
def S2 (p : CdP) (t : State) : Prop :=
  ∃ mi, In p.D mi t ∧ wv t.mem (off p.D.B (inner p.D.w)) (slot p.D.w aXm) p.D.w = p.G

theorem s1_s2 (p : CdP) (t : State) (h : S1 p t) : WP isa (seqs (Crt.loadArr aXm sG sK)) t fun u => S2 p u ∧ KX t u := by
  obtain ⟨mi, hI⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  exact WP.mono (hI.load (show aXm < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := p.D.dp + BitVec.ofNat 64 p.D.k) (by simp)) (by rw [hb.glen]; exact hs.get (by simp))
    hb.gsrc (by rw [hb.glen]; have := hb.k1; omega_arith) (by rw [hb.glen])) fun u ⟨⟨hu, hv, _⟩, k⟩ => ⟨⟨mi, hu, hv⟩, k⟩

theorem s1_lpre (p : CdP) (t : State) (h : S1 p t) :
    LPre aXm sG sK (p.D.ld (p.D.dp + BitVec.ofNat 64 p.D.k) ((p.D.dom.drop p.D.k).take p.D.k).length) t := by
  obtain ⟨mi, hI⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  exact hI.lpre (show aXm < 8 by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := p.D.dp + BitVec.ofNat 64 p.D.k) (by simp)) (by rw [hb.glen]; exact hs.get (by simp))
    hb.gsrc (by rw [hb.glen]; have := hb.k1; omega_arith) (by rw [hb.glen])

/-- Whether `1 < g < p − 1`, as the code compares. -/
abbrev CdP.rg (p : CdP) : Prop := 1 < p.G ∧ 2 * (p.G / 2) + 1 < p.P

/-- After g's range. -/
def S3 (p : CdP) (t : State) : Prop := ∃ mi, In p.D mi t ∧ t.gpr .x9 = bit p.rg

theorem s2_s3 (p : CdP) (t : State) (h : S2 p t) : WP isa (seqs (range aXm)) t fun u => S3 p u ∧ KX t u := by
  obtain ⟨mi, hI, hg⟩ := h
  exact WP.mono (hI.range (show aXm < 8 by decide) (by decide)) fun u ⟨⟨hu, h9, _⟩, k⟩ => ⟨⟨mi, hu, by rw [h9, hg]⟩, k⟩

theorem s3_eval {p : CdP} {t : State} (h : S3 p t) : isa.eval (.zero .x .x9) t = some (bit p.rg == 0) := by
  obtain ⟨_, _, h9⟩ := h
  rw [eval_zero, h9]

/-- Back in the outer workspace, and the test of the domain's length. -/
def S4 (p : CdP) (t : State) : Prop :=
  ∃ mi, Pa p.D mi t ∧ t.gpr .x3 = BitVec.ofNat 64 (p.D.dl - 2 * p.D.k)

theorem s3_s4 (p : CdP) (t : State) (h : S3 p t) : WP isa (.block (leave :: qTest)) t fun u => S4 p u ∧ KX t u := by
  obtain ⟨mi, hI, -⟩ := h
  exact WP.mono hI.leaveQ fun u ⟨⟨hu, h3⟩, k⟩ => ⟨⟨mi, hu, h3⟩, k⟩

theorem s4_eval {p : CdP} {t : State} (h : S4 p t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (p.D.dl - 2 * p.D.k) == 0) := by
  obtain ⟨_, _, h3⟩ := h
  rw [eval_zero, h3]

/-! ## q's range -/

/-- With q, in the inner workspace. -/
def Q0 (p : CdP) (t : State) : Prop := ∃ mi, In p.D mi t ∧ p.D.dl = 3 * p.D.k

theorem s4_q0 (p : CdP) (t : State) (h : S4 p t) (he : isa.eval (.zero .x .x3) t = some false) :
    WP isa (.block [enter]) t fun u => Q0 p u ∧ KX t u := by
  have he' := he
  rw [s4_eval h] at he'
  obtain ⟨mi, hP, -⟩ := h
  have hq := hP.1.q (by simpa using he')
  exact WP.mono hP.enter fun u ⟨hu, k⟩ => ⟨⟨mi, hu, hq⟩, k⟩

/-- With q in `aXm`. -/
def Q1 (p : CdP) (t : State) : Prop :=
  ∃ mi, In p.D mi t ∧ p.D.dl = 3 * p.D.k ∧ wv t.mem (off p.D.B (inner p.D.w)) (slot p.D.w aXm) p.D.w = p.Q

theorem q0_q1 (p : CdP) (t : State) (h : Q0 p t) : WP isa (seqs (Crt.loadArr aXm sQ sK)) t fun u => Q1 p u ∧ KX t u := by
  obtain ⟨mi, hI, hq⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hl := hb.qlen hq
  exact WP.mono (hI.load (show aXm < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sQ) (v := p.D.dp + BitVec.ofNat 64 (2 * p.D.k)) (by simp)) (by rw [hl]; exact hs.get (by simp))
    hb.qsrc (by rw [hl]; have := hb.k1; omega_arith) (by rw [hl])) fun u ⟨⟨hu, hv, _⟩, k⟩ => ⟨⟨mi, hu, hq, hv⟩, k⟩

theorem q0_lpre (p : CdP) (t : State) (h : Q0 p t) :
    LPre aXm sQ sK (p.D.ld (p.D.dp + BitVec.ofNat 64 (2 * p.D.k)) p.D.qb.length) t := by
  obtain ⟨mi, hI, hq⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hl := hb.qlen hq
  exact hI.lpre (show aXm < 8 by decide) (by decide) (by decide)
    (hs.get (i := sQ) (v := p.D.dp + BitVec.ofNat 64 (2 * p.D.k)) (by simp)) (by rw [hl]; exact hs.get (by simp))
    hb.qsrc (by rw [hl]; have := hb.k1; omega_arith) (by rw [hl])

/-- q's range, as the code checks it. -/
abbrev CdP.qr (p : CdP) : Prop := p.Q % 2 = 1 ∧ 1 < p.Q ∧ 2 * (p.Q / 2) + 1 < p.P

/-- After q's range. -/
def Q2 (p : CdP) (t : State) : Prop := ∃ mi, In p.D mi t ∧ p.D.dl = 3 * p.D.k ∧ t.gpr .x9 = bit p.qr

theorem q1_q2 (p : CdP) (t : State) (h : Q1 p t) :
    WP isa (seqs (isOdd aXm ++ ([.block [sth .x9 sF]] : List (Prog isa)) ++ gt1 aXm ++ ([.block andF] : List (Prog isa)) ++ ltP aXm ++ ([.block andF] : List (Prog isa)))) t
      fun u => Q2 p u ∧ KX t u := by
  obtain ⟨mi, hI, hq, hQ⟩ := h
  exact WP.mono (hI.qrange hQ) fun u ⟨⟨hu, h9⟩, k⟩ => ⟨⟨mi, hu, hq, h9⟩, k⟩

theorem q2_eval {p : CdP} {t : State} (h : Q2 p t) : isa.eval (.zero .x .x9) t = some (bit p.qr == 0) := by
  obtain ⟨_, _, _, h9⟩ := h
  rw [eval_zero, h9]

theorem bit_ne {P : Prop} [Decidable P] (h : (bit P == 0) = false) : P := by
  by_cases hp : P
  · exact hp
  · simp [bit, hp] at h

/-! ## `q ∣ p − 1` -/

/-- Back in the outer workspace, with q's range. -/
def Q3 (p : CdP) (t : State) : Prop := ∃ mi, Pa p.D mi t ∧ p.D.dl = 3 * p.D.k ∧ p.qr

theorem q2_q3 (p : CdP) (t : State) (h : Q2 p t) (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (.block [leave]) t fun u => Q3 p u ∧ KX t u := by
  have hr : p.qr := bit_ne (by rw [q2_eval h] at he; simpa using he)
  obtain ⟨mi, hI, hq, -⟩ := h
  exact WP.mono hI.leave fun u ⟨hu, k⟩ => ⟨⟨mi, hu, hq, hr⟩, k⟩

/-- After the scan of q. -/
def Q4 (p : CdP) (t : State) : Prop := ∃ mi, Sc p.D mi t ∧ p.D.dl = 3 * p.D.k ∧ p.qr

theorem q3_q4 (p : CdP) (t : State) (h : Q3 p t) : WP isa (seqs (scan sQ)) t fun u => Q4 p u ∧ KX t u := by
  obtain ⟨mi, hP, hq, hr⟩ := h
  exact WP.mono (hP.scan hq) fun u ⟨⟨hu, _⟩, k⟩ => ⟨⟨mi, hu, hq, hr⟩, k⟩

/-- With `p − 1` in the outer array `aX`. -/
def Q5 (p : CdP) (t : State) : Prop :=
  ∃ mi, Sc p.D mi t ∧ p.D.dl = 3 * p.D.k ∧ p.qr ∧ wv t.mem p.D.B (slot p.D.w aX) p.D.w = p.P - 1

theorem q4_q5 (p : CdP) (t : State) (h : Q4 p t) : WP isa (seqs CheckDomain.pMinus1) t fun u => Q5 p u ∧ KX t u := by
  obtain ⟨mi, ⟨hP, hEp, hEl⟩, hq, hr⟩ := h
  exact WP.mono hP.pMinus1 fun u ⟨hu, hX, hw, k⟩ => ⟨⟨mi, ⟨hu, by rw [hw _ (by decide)]; exact hEp,
    by rw [hw _ (by decide)]; exact hEl⟩, hq, hr, hX⟩, k⟩

/-! ## q's workspace -/

/-- q's octets from its first nonzero one. -/
abbrev CdP.qe (p : CdP) : List Byte := p.D.qb.drop (lead p.D.qb)

/-- q's workspace's words. -/
abbrev CdP.wq (p : CdP) : Nat := wsWords (p.D.k - lead p.D.qb)

/-- The outer header's exponent slots: q from its first nonzero octet. -/
abbrev CdP.ep (p : CdP) : List (Nat × BitVec 64) :=
  [(sEp, off (p.D.dp + BitVec.ofNat 64 (2 * p.D.k)) (lead p.D.qb)), (sEl, BitVec.ofNat 64 (p.D.k - lead p.D.qb))]

theorem qe_facts {p : CdP} {t : State} (hb : Base p.D t) (hq : p.D.dl = 3 * p.D.k) :
    p.qe.length = p.D.k - lead p.D.qb ∧ 1 ≤ p.qe.length ∧ p.qe.length ≤ p.D.k ∧
      Spec.Rsa.os2ip p.qe = p.Q ∧ Src t p.D.B p.D.Z (off (p.D.dp + BitVec.ofNat 64 (2 * p.D.k)) (lead p.D.qb)) p.qe := by
  have hl := hb.qlen hq
  have := hb.k1
  have hne : p.D.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
  have hlead := lead_lt hne
  refine ⟨by rw [List.length_drop, hl], by rw [List.length_drop]; omega_arith, by rw [List.length_drop]; omega_arith,
    os2ip_drop_lead _, hb.qsrc.drop _⟩

/-- In q's workspace. -/
def Q6 (p : CdP) (t : State) : Prop :=
  ∃ mq, Base p.D t ∧ SubCtx t p.D.B p.D.Z (inner p.D.w) p.D.w p.wq mq ∧ XVals t p.D.B (inner p.D.w) p.wq mq p.Q ∧
    word t.mem p.D.B (8 * sWs) = off p.D.B (inner p.D.w) ∧ Slots t.mem p.D.B (p.D.hdrQ ++ p.ep) ∧ p.D.mv = true ∧
    p.D.dl = 3 * p.D.k ∧ p.qr ∧ wv t.mem p.D.B (slot p.D.w aX) p.D.w = p.P - 1

theorem q5_q6 (p : CdP) (t : State) (h : Q5 p t) :
    WP isa (seqs (([.block (wsSetup sEl ++ [enter])] : List (Prog isa)) ++ modSetup sEp sEl)) t fun u => Q6 p u ∧ KX t u := by
  obtain ⟨mi, ⟨hP, hEp, hEl⟩, hq, hr, hX⟩ := h
  have hb := hP.1
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts hb hq
  have hodd : Spec.Rsa.os2ip p.qe % 2 = 1 := by rw [hQ]; exact hr.1
  have hroom := hb.room
  have hn := hb.scr.nowrap
  have h8 := hdr_lt_slot p.D.w 8 (show 31 < 32 by decide)
  have hi256 : 256 ≤ inner p.D.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner p.D.w + slot p.D.w 8 ≤ p.D.Z := by unfold tabBytes32 at hroom; omega_arith
  have hsX := slot_le (w := p.D.w) (show aX < 8 by decide)
  have hX0 := hdr_lt_slot p.D.w aX (show 31 < 32 by decide)
  have ei : inner p.D.w = slot p.D.w 8 := rfl
  refine WP.mono (hP.ou.wsMod (show sEp < 32 by decide) (show sEl < 32 by decide) (by decide) (by decide) hEp
    (by rw [hl]; exact hEl) hsrc h1 hk hodd) fun u ⟨mq, hb', hc, hv, hWs, f, k⟩ => ?_
  rw [hl, hQ] at *
  refine ⟨⟨mq, hb', hc, hv, hWs, fun e he => ?_, hP.2.2.2.2.2.1, hq, hr, ?_⟩, k⟩
  · rcases List.mem_append.mp he with he | he
    · exact slots_frm hb.hs hP.2.2.2.2.1 f (kept_wsR p.D.w) e he
    · simp only [CdP.ep, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · rw [f.word_eq (fun r hr' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl <;> simp only [sWs, sEp, sFn] <;> omega_arith) (show 8 * sEp + 8 ≤ 2 ^ 64 by decide)]
        exact hEp
      · rw [f.word_eq (fun r hr' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl <;> simp only [sWs, sEl, sFn] <;> omega_arith) (show 8 * sEl + 8 ≤ 2 ^ 64 by decide)]
        exact hEl
  · rw [f.wv_eq (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> simp only [sWs, sFn] <;> omega_arith) (by omega_arith)]; exact hX

theorem Slots.of_eq {m m' : Mem} {B : Addr} {L : List (Nat × BitVec 64)} (h : Slots m B L)
    (he : ∀ q ∈ L, word m' B (8 * q.1) = word m B (8 * q.1)) : Slots m' B L := fun q hq => by
  rw [he q hq]; exact h q hq

theorem ep_lt (p : CdP) : ∀ q ∈ p.D.hdrQ ++ p.ep, q.1 < 32 := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact kept_lt _ (hdr_kept p.D (by simp) q hq)
  · simp only [CdP.ep, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [sEp, sEl, sFn]

/-- The exponent of the reduction: `R` to the chunks' count. -/
abbrev CdP.R (p : CdP) : Nat := 2 ^ (64 * p.wq * ((p.D.w + p.wq - 1) / p.wq))

/-- After the reduction of `p − 1` modulo q. -/
def Q7 (p : CdP) (t : State) : Prop :=
  ∃ mq, Base p.D t ∧ SubCtx t p.D.B p.D.Z (inner p.D.w) p.D.w p.wq mq ∧
    word t.mem p.D.B (8 * sWs) = off p.D.B (inner p.D.w) ∧ Slots t.mem p.D.B (p.D.hdrQ ++ p.ep) ∧
    p.D.mv = true ∧ p.D.dl = 3 * p.D.k ∧ p.qr ∧
    wv t.mem (off p.D.B (inner p.D.w)) (slot p.wq Crt.aXc) p.wq < p.Q ∧
    wv t.mem (off p.D.B (inner p.D.w)) (slot p.wq Crt.aXc) p.wq * p.R % p.Q = (p.P - 1) % p.Q ∧
    wv t.mem (off p.D.B (inner p.D.w)) (slot p.wq aOne) p.wq = 1

theorem q6_q7 (M : Mont) (p : CdP) (t : State) (h : Q6 p t) : WP isa (seqs (Crt.redc M.mm aX)) t fun u => Q7 p u ∧ KX t u := by
  obtain ⟨mq, hb, hc, hv, hWs, hs, hm, hq, hr, hX⟩ := h
  have hw2 := hb.w2
  have hw28 := hb.w28
  have hwq2 : 2 ≤ p.wq := by unfold CdP.wq wsWords; omega_arith
  have hwq : p.wq ≤ p.D.w := by
    have := hb.qlen hq
    have := hb.ew
    unfold CdP.wq wsWords; omega_arith
  have h1Q : 1 < p.Q := hr.2.1
  refine WP.mono (redc_ok M hc hv hwq2 hwq (show p.D.w < 2 ^ 30 by omega_arith) h1Q (show aX < 8 by decide))
    fun u ⟨hc', hv', hlt, hR, f, k⟩ => ?_
  obtain ⟨hbw, hi⟩ := child_frm' hc f (fun r hr' => by have := (redcRanges_ok p.wq r hr').2; omega_arith)
  have h256 : 256 ≤ inner p.D.w := by simp only [inner, slot, hdrBytes]; omega_arith
  refine ⟨⟨mq, hb.keep hi k, hc', by rw [hbw _ (show 8 * sWs + 8 ≤ inner p.D.w by simp only [sWs, sFn]; omega_arith)]; exact hWs,
    Slots.of_eq hs fun q hq' => hbw _ (by have := ep_lt p q hq'; omega_arith), hm, hq, hr, hlt, by rw [hR, hX], hv'.one⟩,
    k.mono (by decide)⟩

/-- After the test of the reduction. -/
def Q8 (p : CdP) (t : State) : Prop :=
  ∃ mq, Base p.D t ∧ SubCtx t p.D.B p.D.Z (inner p.D.w) p.D.w p.wq mq ∧
    word t.mem p.D.B (8 * sWs) = off p.D.B (inner p.D.w) ∧ Slots t.mem p.D.B (p.D.hdrQ ++ p.ep) ∧
    p.D.mv = true ∧ p.D.dl = 3 * p.D.k ∧ p.qr ∧ t.gpr .x9 = bit ((p.P - 1) % p.Q = 0)

theorem q7_q8 (p : CdP) (t : State) (h : Q7 p t) : WP isa (seqs (isZero Crt.aXc)) t fun u => Q8 p u ∧ KX t u := by
  obtain ⟨mq, hb, hc, hWs, hs, hm, hq, hr, hlt, hR, h1⟩ := h
  have hwq2 : 2 ≤ p.wq := by unfold CdP.wq wsWords; omega_arith
  have hwq : p.wq < 2 ^ 31 := by
    have := hb.qlen hq
    have := hb.k2
    unfold CdP.wq wsWords; omega_arith
  refine WP.mono (ltArr_ok hc.good (Nat.le_refl _) (by omega_arith) hwq (show Crt.aXc < 8 by decide)
    (show aOne < 8 by decide)) fun u ⟨h9, hmu, k⟩ => ⟨⟨mq, hb.keep (by rw [hmu]; exact InScr.refl _ _ _) k,
      (hc.toMem.congr hmu k.wr).ctx ((k.gpr .x0 (by decide)).trans hc.x0), by rw [hmu]; exact hWs,
      by rw [hmu]; exact hs, hm, hq, hr, ?_⟩, k.mono (by decide)⟩
  rw [h9, h1]
  have e := redc_zero hr.1 hlt hR
  by_cases h0 : (p.P - 1) % p.Q = 0
  · simp only [bit, h0, ↓reduceIte, show wv t.mem (off p.D.B (inner p.D.w)) (slot p.wq Crt.aXc) p.wq < 1 by
      have := e.mpr h0; omega_arith]
  · simp only [bit, h0, ↓reduceIte, show ¬ wv t.mem (off p.D.B (inner p.D.w)) (slot p.wq Crt.aXc) p.wq < 1 by
      intro hlt'; exact h0 (e.mp (by omega_arith))]

theorem q8_eval {p : CdP} {t : State} (h : Q8 p t) :
    isa.eval (.zero .x .x9) t = some (bit ((p.P - 1) % p.Q = 0) == 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, h9⟩ := h
  rw [eval_zero, h9]

/-- Back in the outer workspace, with `q ∣ p − 1`. -/
def Q9 (p : CdP) (t : State) : Prop :=
  Ou p.D t ∧ word t.mem p.D.B (8 * sWs) = off p.D.B (inner p.D.w) ∧ Slots t.mem p.D.B (p.D.hdrQ ++ p.ep) ∧
    p.D.dl = 3 * p.D.k ∧ p.qr ∧ (p.P - 1) % p.Q = 0

theorem q8_q9 (p : CdP) (t : State) (h : Q8 p t) (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (.block [leave]) t fun u => Q9 p u ∧ KX t u := by
  have hd : (p.P - 1) % p.Q = 0 := bit_ne (by rw [q8_eval h] at he; simpa using he)
  obtain ⟨mq, hb, hc, hWs, hs, hm, hq, hr, -⟩ := h
  refine WP.mono (leave_ok hc) fun u ⟨⟨h0, hmu⟩, k⟩ => ?_
  have hs' : Slots u.mem p.D.B (p.D.hdrQ ++ p.ep) := by rw [hmu]; exact hs
  have hc' := hc.toMem.congr hmu k.wr
  exact ⟨⟨⟨hb.keep (by rw [hmu]; exact InScr.refl _ _ _) k, Outer.of_mem hc' h0 hb.room hb.w2 hb.w28,
    fun q hq => hs' q (List.mem_append_left _ hq), hm⟩, by rw [hmu]; exact hWs, hs', hq, hr, hd⟩, k.mono (by decide)⟩

/-! ## `g^q mod p` -/

/-- Common facts once `q ∣ p − 1`. -/
abbrev CdP.qd (p : CdP) : Prop := p.D.dl = 3 * p.D.k ∧ p.qr ∧ (p.P - 1) % p.Q = 0

/-- p's workspace again. -/
def Q10 (p : CdP) (t : State) : Prop := ∃ mi, In p.D mi t ∧ Slots t.mem p.D.B (p.D.hdrQ ++ p.ep) ∧ p.qd

theorem q9_q10 (p : CdP) (t : State) (h : Q9 p t) : WP isa (seqs pSetup) t fun u => Q10 p u ∧ KX t u := by
  obtain ⟨hO, hWs, hs, hq, hr, hd⟩ := h
  have hb := hO.1
  have hs' := hO.2.2.1
  have hn := hb.scr.nowrap
  have hroom := hb.room
  have h256 : 256 ≤ inner p.D.w := by simp only [inner, slot, hdrBytes]; omega_arith
  obtain ⟨hodd, -⟩ := valid_facts hO.2.2.2 hb.k1
  refine WP.mono (hO.wsMod (show sDom < 32 by decide) (show sK < 32 by decide) (by decide) (by decide)
    (hs'.get (i := sDom) (v := p.D.dp) (by simp)) (by rw [hb.plen]; exact hs'.get (by simp)) (hb.dom.take p.D.k)
    (by rw [hb.plen]; have := hb.k1; omega_arith) (by rw [hb.plen]) hodd) fun u ⟨mi, hb', hc, hv, hWs', f, k⟩ => ?_
  rw [hb.plen, wsWords_k (by have := hb.k1; omega_arith)] at hc hv
  have hw : ∀ q ∈ p.D.hdrQ ++ p.ep, word u.mem p.D.B (8 * q.1) = word t.mem p.D.B (8 * q.1) := fun q hq' => by
    have := ep_lt p q hq'
    refine f.word_eq (fun r hr' => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · rcases List.mem_append.mp hq' with hq' | hq'
      · have hk := hdr_kept p.D (by simp) q hq'
        simp only [keptSlots, argSlots, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hk
        rcases hk with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
      · simp only [CdP.ep, List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl <;> simp only [sWs, sEp, sEl, sFn] <;> omega_arith
    · simp only; omega_arith
  exact ⟨⟨mi, ⟨hb', hc, hv, hWs', Slots.of_eq hs' fun q hq' => hw q (List.mem_append_left _ hq'), hO.2.2.2⟩,
    Slots.of_eq hs hw, hq, hr, hd⟩, k⟩

/-- After `R² mod p`. -/
def Q11 (p : CdP) (t : State) : Prop := ∃ mi, Md p.D mi t ∧ Slots t.mem p.D.B (p.D.hdrQ ++ p.ep) ∧ p.qd

theorem q10_q11 (M : Mont) (p : CdP) (t : State) (h : Q10 p t) : WP isa (seqs (r2Steps M.mm)) t fun u => Q11 p u ∧ KX t u := by
  obtain ⟨mi, hI, hs, hd⟩ := h
  exact WP.mono (hI.r2 M) fun u ⟨⟨hu, hw⟩, k⟩ => ⟨⟨mi, hu, Slots.of_eq hs fun q hq => hw _ (ep_lt p q hq), hd⟩, k⟩

/-- `g^q mod p` in `aY`. -/
def Q12 (p : CdP) (t : State) : Prop :=
  ∃ mi, Md p.D mi t ∧ wv t.mem (off p.D.B (inner p.D.w)) (slot p.D.w aY) p.D.w = p.G ^ p.Q % p.P ∧ p.qd

theorem q11_pre (p : CdP) (t : State) (h : Q11 p t) :
    PS0 sG sK sEp sEl (p.D.pw (p.D.dp + BitVec.ofNat 64 p.D.k) ((p.D.dom.drop p.D.k).take p.D.k).length
      (off (p.D.dp + BitVec.ofNat 64 (2 * p.D.k)) (lead p.D.qb)) p.qe.length) t := by
  obtain ⟨mi, hM, hs, hq, -⟩ := h
  have hb := hM.1
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts hb hq
  exact hM.ps0 (by decide) (by decide) (by decide) (by decide) (hs.get (i := sG) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; have := hb.k1; omega_arith)
    (by rw [hb.glen]) (hs.get (i := sEp) (by simp)) (by rw [hl]; exact hs.get (i := sEl) (by simp)) hsrc h1
    (by have := hb.k2; omega_arith)

theorem q11_q12 (W : Window) (M : Mont) (S : Selector) (p : CdP) (t : State) (h : Q11 p t) :
    WP isa (seqs (pow W.code S.code M.mm sG sK sEp sEl)) t fun u => Q12 p u ∧ KX t u := by
  obtain ⟨mi, hM, hs, hd⟩ := h
  have hb := hM.1
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts hb hd.1
  exact WP.mono (hM.pow W M S (by decide) (by decide) (by decide) (by decide) (hs.get (i := sG) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; have := hb.k1; omega_arith)
    (by rw [hb.glen]) (hs.get (i := sEp) (by simp)) (by rw [hl]; exact hs.get (i := sEl) (by simp)) hsrc h1
    (by have := hb.k2; omega_arith)) fun u ⟨hu, hY, _, k⟩ => ⟨⟨mi, hu, by rw [hY, hQ], hd⟩, k⟩

/-- After the comparison of `g^q mod p` with 1. -/
def Q13 (p : CdP) (t : State) : Prop := t.gpr .x9 = bit (p.G ^ p.Q % p.P = 1)

theorem q12_q13 (p : CdP) (t : State) (h : Q12 p t) : WP isa (seqs (isOne aY)) t fun u => Q13 p u ∧ KX t u := by
  obtain ⟨mi, hM, hY, -⟩ := h
  have hI := hM.inn
  have hb := hI.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  exact WP.mono (eqArr_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ p.D.w by omega_arith) (show p.D.w < 2 ^ 31 by omega_arith)
    (show aY < 8 by decide) (show aOne < 8 by decide)) fun u ⟨h9, _, k⟩ => ⟨by
      show u.gpr .x9 = _; rw [h9, hY, hI.2.2.1.one], k.mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.CheckDomain
