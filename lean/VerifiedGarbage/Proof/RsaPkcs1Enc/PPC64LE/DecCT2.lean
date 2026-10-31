module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCTBase
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecKdk
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCTBase
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecKdk
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Covers

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time of `DH` and `KDK`

The argument blocks, by the taint analysis, and the calls of SHA-256's and
HMAC's functions, the same in both runs (`DecCalls.lean`), with the
arguments correctness fixes: `hashD_ct`, `kdkMac_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- `Post`, for some result and `EM`. -/
def PP (s u : State) : Prop := ∃ R EM, Post s R EM u

section
variable {s : State} (h : DPre s)
include h

theorem initCall_pp {u : State} (hu : PP s u) (u3 : u.gpr .r3 = scA s sSt) : WP isa initCall u (PP s) := by
  obtain ⟨R, EM, hu⟩ := hu
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega
  exact hH.callInit_ok u3 ⟨hs, by rw [hu.sp]; exact lowD h (by decide) (by decide)⟩
    (scCovR h hu.wr (by decide)) (scCov h hu.wr (by decide)) fun v hrd hwr hsp hf hcs _ =>
      ⟨R, EM, hu.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact scSub (by decide)⟩

theorem updCall_pp {u : State} (hu : PP s u) (u3 : u.gpr .r3 = scA s sSt) (u5 : u.gpr .r5 = scA s sD)
    (u6 : u.gpr .r6 = s.gpr .r7) (u7 : u.gpr .r7 = scA s sWork) : WP isa updCall u (PP s) := by
  obtain ⟨R, EM, hu⟩ := hu
  have hk := h.k2
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega
  have lk : sD + (s.gpr .r7).toNat ≤ scrBytes := by unfold sD scrBytes; omega
  exact hH.callUpd_ok (len := (s.gpr .r7).toNat) u3 u5 (by rw [u6]) u7 (scD h (by decide) (by decide) (by decide))
    (scD h (.inr (by decide)) lk (by decide)) (scD h (.inr (by decide)) lk (by decide)) hs
    (by rw [hu.sp]; exact lowD h (by decide) (by decide)) (by rw [hu.sp]; exact lowD h (by decide) lk)
    (by rw [hu.sp]; exact lowD h (by decide) (by decide))
    (Covers.append_left (scCovR h hu.wr lk) (Covers.pair (scCovR h hu.wr (by decide)) (scCovR h hu.wr (by decide))))
    (Covers.pair (scCov h hu.wr (by decide)) (scCov h hu.wr (by decide)))
    fun v hrd hwr hsp hf hcs _ => ⟨R, EM, hu.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact scSub (by decide)⟩

theorem finCall_pp {u : State} (hu : PP s u) (u3 : u.gpr .r3 = scA s sSt) (u5 : u.gpr .r5 = scA s sDH)
    (u6 : u.gpr .r6 = scA s sWork) : WP isa finCall u (PP s) := by
  obtain ⟨R, EM, hu⟩ := hu
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega
  exact hH.callFin_ok u3 u5 u6 (scD h (by decide) (by decide) (by decide))
    (scD h (by decide) (by decide) (by decide)) (scD h (by decide) (by decide) (by decide)) hs
    (by rw [hu.sp]; exact lowD h (by decide) (by decide)) (by rw [hu.sp]; exact lowD h (by decide) (by decide))
    (by rw [hu.sp]; exact lowD h (by decide) (by decide))
    ((scCovR h hu.wr (a := sSt) (n := H.S) (by decide)).cons ((scCovR h hu.wr (a := sDH) (n := H.FD) (by decide)).cons
      (scCovR h hu.wr (a := sWork) (n := H.W) (by decide))))
    ((scCov h hu.wr (a := sSt) (n := H.S) (by decide)).cons ((scCov h hu.wr (a := sDH) (n := H.FD) (by decide)).cons
      (scCov h hu.wr (a := sWork) (n := H.W) (by decide))))
    fun v hrd hwr hsp hf hcs _ => ⟨R, EM, hu.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scSub (by decide)⟩

theorem macInit_pp {u : State} (hu : PP s u) {key : Nat} (hk₁ : 400 ≤ key) (hk₂ : key + 32 ≤ scrBytes)
    (u3 : u.gpr .r3 = scA s sSt) (u4 : u.gpr .r4 = scA s sOuter) (u5 : u.gpr .r5 = scA s key)
    (u6 : u.gpr .r6 = BitVec.ofNat 64 32) (u7 : u.gpr .r7 = scA s sWork) : WP isa macInitCall u (PP s) :=
  let ⟨_, _, hu⟩ := hu
  macInit_call h hu hk₁ hk₂ u3 u4 u5 u6 u7 fun _ hv _ _ _ => ⟨_, _, hv⟩

theorem macFin_pp {u : State} (hu : PP s u) {o : Nat} (ho₁ : 432 ≤ o) (ho₂ : o + 32 ≤ scrBytes)
    (u3 : u.gpr .r3 = scA s sSt) (u4 : u.gpr .r4 = scA s sOuter) (u6 : u.gpr .r6 = scA s o)
    (u7 : u.gpr .r7 = scA s sWork) : WP isa macFinCall u (PP s) :=
  let ⟨_, _, hu⟩ := hu
  macFin_call h hu ho₁ ho₂ u3 u4 u6 u7 fun _ hv _ _ => ⟨_, _, hv⟩

end

/-- A block of the frame's registers, after which `Post` holds still, with
`X`. -/
theorem pp_block {s : State} {c : List Instr} {u : State} (hu : PP s u) {X : State → Prop} (rs : List Reg)
    (hw : ∀ R EM, Post s R EM u → WP isa (.block c) u fun v => (v.mem = u.mem ∧ X v) ∧ VG.Proof.Bignum.PPC64LE.Keep rs u v)
    (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    WP isa (.block c) u fun v => PP s v ∧ v.mem = u.mem ∧ X v :=
  let ⟨R, EM, hc⟩ := hu
  WP.mono (hw R EM hc) fun _ ⟨⟨vm, vx⟩, kv⟩ => ⟨⟨R, EM, hc.regs kv.rd kv.wr kv.sp vm fun r hr =>
    kv.gpr r fun h' => hrs r h' hr⟩, vm, vx⟩

section
variable {e : Env}

theorem pp_sp {a b : State} (ha : PP e.s₁ a) (hb : PP e.s₂ b) : a.sp = b.sp := by
  obtain ⟨_, _, ha⟩ := ha; obtain ⟨_, _, hb⟩ := hb
  rw [ha.sp, hb.sp, e.fb_eq]

/-! ## `DH` -/

def PI (s u : State) : Prop := PP s u ∧ u.gpr .r3 = scA s sSt
def PU (s u : State) : Prop := PP s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = 0 ∧ u.gpr .r5 = scA s sD ∧
  u.gpr .r6 = s.gpr .r7 ∧ u.gpr .r7 = scA s sWork
def PF (s u : State) : Prop := PP s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = s.gpr .r7 ∧ u.gpr .r5 = scA s sDH ∧
  u.gpr .r6 = scA s sWork

theorem hashD_ct : RelCT isa (Rel e PP) hashD (Rel e PP) := by
  unfold hashD
  refine RelCT.seq (rel_step [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u _ hu => (WP.mono (pp_block hu [.r12, .r3] fun _ _ hc => shaInitArgs_ok hc)
      fun _ ⟨hv, _, x⟩ => ⟨hv, x⟩ : WP isa _ u (PI s))) ?_
  refine RelCT.seq (rel_post (init_rel fun a b ⟨⟨ha, a3⟩, hb, b3⟩ => ⟨pp_sp ha hb, fun r hr => by
    rw [List.mem_singleton.mp hr, a3, b3, e.scA_eq]⟩) fun s u h ⟨hu, u3⟩ => initCall_pp h hu u3) ?_
  refine RelCT.seq (rel_step [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u _ hu => (WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc => shaUpdArgs_ok hc)
      fun _ ⟨hv, _, x⟩ => ⟨hv, x⟩ : WP isa _ u (PU s))) ?_
  refine RelCT.seq (rel_post (upd_rel fun a b ⟨⟨ha, a3, a4, a5, a6, a7⟩, hb, b3, b4, b5, b6, b7⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4]
      · rw [a5, b5, e.scA_eq]
      · rw [a6, b6, e.r]
      · rw [a7, b7, e.scA_eq]⟩) fun s u h ⟨hu, _, _, u5, u6, u7⟩ => updCall_pp h hu ‹_› u5 u6 u7) ?_
  refine RelCT.seq (rel_step [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u _ hu => (WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6] fun _ _ hc => shaFinArgs_ok hc)
      fun _ ⟨hv, _, x⟩ => ⟨hv, x⟩ : WP isa _ u (PF s))) ?_
  exact rel_post (fin_rel fun a b ⟨⟨ha, a3, a4, a5, a6⟩, hb, b3, b4, b5, b6⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4, e.r]
      · rw [a5, b5, e.scA_eq]
      · rw [a6, b6, e.scA_eq]⟩) fun s u h ⟨hu, u3, _, u5, u6⟩ => finCall_pp h hu u3 u5 u6

/-! ## `KDK` -/

def PMI (key : Nat) (s u : State) : Prop := PP s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = scA s sOuter ∧
  u.gpr .r5 = scA s key ∧ u.gpr .r6 = BitVec.ofNat 64 32 ∧ u.gpr .r7 = scA s sWork
def PKU (s u : State) : Prop := PP s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = BitVec.ofNat 64 64 ∧
  u.gpr .r5 = stackArg s 1 ∧ u.gpr .r6 = s.gpr .r7 ∧ u.gpr .r7 = scA s sWork
def PKF (s u : State) : Prop := PP s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = scA s sOuter ∧
  u.gpr .r5 = s.gpr .r7 + BitVec.ofNat 64 64 ∧ u.gpr .r6 = scA s sKDK ∧ u.gpr .r7 = scA s sWork

theorem pmi_agree {key : Nat} {a b : State} (ha : PMI key e.s₁ a) (hb : PMI key e.s₂ b) :
    AgreeOn [.r3, .r4, .r5, .r6, .r7] a b := by
  obtain ⟨ha, a3, a4, a5, a6, a7⟩ := ha
  obtain ⟨hb, b3, b4, b5, b6, b7⟩ := hb
  refine ⟨pp_sp ha hb, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a3, b3, e.scA_eq]
  · rw [a4, b4, e.scA_eq]
  · rw [a5, b5, e.scA_eq]
  · rw [a6, b6]
  · rw [a7, b7, e.scA_eq]

/-- The arguments of HMAC's `init` for the key at `scratch + key`. -/
theorem macInitArgs_ct {key : Nat} (hk : key < 2 ^ 15) {hc : VG.Taint.Hint T}
    (ht : (vectorTaint.check (ofRegs []) (.block (macInitArgs key)) hc).isSome = true) {P : State → State → Prop}
    (hP : ∀ s u, P s u → PP s u) :
    RelCT isa (Rel e P) (.block (macInitArgs key)) (Rel e (PMI key)) :=
  rel_step [] ht (fun a b ha hb => ⟨pp_sp (hP _ _ ha) (hP _ _ hb), fun _ h => nomatch h⟩)
    fun s u _ hu => WP.mono (pp_block (hP _ _ hu) [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc => macInitArgs_ok hc hk)
      fun _ ⟨hv, _, x⟩ => ⟨hv, x⟩

theorem kdkMac_ct : RelCT isa (Rel e PP) kdkMac (Rel e PP) := by
  unfold kdkMac
  refine RelCT.seq (macInitArgs_ct (key := sDH) (by decide) (by taint_decide) fun _ _ h => h) ?_
  refine RelCT.seq (rel_post (macInit_rel fun a b ⟨ha, hb⟩ => pmi_agree ha hb)
    fun s u h ⟨hu, u3, u4, u5, u6, u7⟩ => macInit_pp h hu (by decide) (by decide) u3 u4 u5 u6 u7) ?_
  refine RelCT.seq (rel_step [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u _ hu => (WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc => kdkUpdArgs_ok hc)
      fun _ ⟨hv, _, x⟩ => ⟨hv, x⟩ : WP isa _ u (PKU s))) ?_
  refine RelCT.seq (rel_post (upd_rel fun a b ⟨⟨ha, a3, a4, a5, a6, a7⟩, hb, b3, b4, b5, b6, b7⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4]
      · rw [a5, b5, e.arg]
      · rw [a6, b6, e.r]
      · rw [a7, b7, e.scA_eq]⟩) fun s u h ⟨⟨_, _, hu⟩, u3, _, u5, u6, u7⟩ =>
    (upd_call h hu u3 u5 (by rw [u6]) u7 (c_sc h (by decide)) (c_sc h (by decide)) (c_low h (by decide))
      (c_cov h hu) fun _ hv _ _ => ⟨_, _, hv⟩ : WP isa updCall u (PP s))) ?_
  refine RelCT.seq (rel_step [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u _ hu => (WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc => kdkFinArgs_ok hc)
      fun _ ⟨hv, _, x⟩ => ⟨hv, x⟩ : WP isa _ u (PKF s))) ?_
  exact rel_post (macFin_rel fun a b ⟨⟨ha, a3, a4, a5, a6, a7⟩, hb, b3, b4, b5, b6, b7⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4, e.scA_eq]
      · rw [a5, b5, e.r]
      · rw [a6, b6, e.scA_eq]
      · rw [a7, b7, e.scA_eq]⟩) fun s u h ⟨hu, u3, u4, _, u6, u7⟩ =>
    macFin_pp h hu (by decide) (by decide) u3 u4 u6 u7

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
