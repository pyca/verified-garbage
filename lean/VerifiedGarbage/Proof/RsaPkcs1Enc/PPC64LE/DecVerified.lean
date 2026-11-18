module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Data.List.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecIrprf
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecIrprf
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCTBase
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecD
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCTBase
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecD
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecKdk
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecKdk
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Covers

/-! ### `RsaPkcs1Enc.PPC64LE.DecCT4`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecCT3`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecCT2`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time of `DH` and `KDK`

The argument blocks, by the taint analysis, and the calls of SHA-256's and
HMAC's functions, the same in both runs (`DecCalls.lean`), with the
arguments correctness fixes: `hashD_ct`, `kdkMac_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

variable {pc : Bool}

/-- `Post`, for some result and `EM`. -/
def PP (s u : State) : Prop := ∃ R EM, Post s R EM u

section
variable {s : State} (h : DPre pc s)
include h

theorem initCall_pp {u : State} (hu : PP s u) (u3 : u.gpr .r3 = scA s sSt) : WP isa initCall u (PP s) := by
  obtain ⟨R, EM, hu⟩ := hu
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega_using [this]
  exact hH.callInit_ok u3 ⟨hs, by rw [hu.sp]; exact lowD h (by decide) (by decide)⟩
    (scCovR h hu.wr (by decide)) (scCov h hu.wr (by decide)) fun v hrd hwr hsp hf hcs _ =>
      ⟨R, EM, hu.call h hrd hwr hsp hcs (by decide) hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact scSub (by decide)⟩

theorem updCall_pp {u : State} (hu : PP s u) (u3 : u.gpr .r3 = scA s sSt) (u5 : u.gpr .r5 = scA s sD)
    (u6 : u.gpr .r6 = s.gpr .r7) (u7 : u.gpr .r7 = scA s sWork) : WP isa updCall u (PP s) := by
  obtain ⟨R, EM, hu⟩ := hu
  have hk := h.k2
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega_using [this]
  have lk : sD + (s.gpr .r7).toNat ≤ scrBytes := by unfold sD scrBytes; omega_using [hk]
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
  have hs : 48 ≤ u.sp.toNat := by rw [hu.sp]; have := fb_ge h; omega_using [this]
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
    (hw : ∀ R EM, Post s R EM u → WP isa (.block c) u fun v => (v.mem = u.mem ∧ X v) ∧ Keep rs u v)
    (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    WP isa (.block c) u fun v => PP s v ∧ v.mem = u.mem ∧ X v :=
  let ⟨R, EM, hc⟩ := hu
  WP.mono (hw R EM hc) fun _ ⟨⟨vm, vx⟩, kv⟩ => ⟨⟨R, EM, hc.regs kv.rd kv.wr kv.sp vm fun r hr =>
    kv.gpr r fun h' => hrs r h' hr⟩, vm, vx⟩

section
variable {e : Env pc}

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
    (ht : (taint.check (ofRegs []) (.block (macInitArgs key)) hc).isSome = true) {P : State → State → Prop}
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

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time of IRPRF

A block of IRPRF (`prfBody_ct`) keeps `Post` and the counters in their
slots (`SL`), the blocks by the taint analysis and the calls the same in
both runs; the loops (`clLoop_ct`, `amLoop_ct`) run the same number of
blocks in both runs, which the public `k` fixes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

variable {pc : Bool}

/-- The counter `i` and the number of blocks `nb s` in their slots. -/
def SL (i : Nat) (nb : State → BitVec 64) (s u : State) : Prop :=
  sl s u oI = BitVec.ofNat 64 i ∧ sl s u oNB = nb s

theorem SL.mem {i : Nat} {nb : State → BitVec 64} {s u v : State} (h : SL i nb s u) (hm : v.mem = u.mem) :
    SL i nb s v := by
  unfold SL sl at *; rw [hm]; exact h

/-- The counters stay through a call working in `scratch`. -/
theorem SL.call {i : Nat} {nb : State → BitVec 64} {s u v : State} (hd : DPre pc s) (h : SL i nb s u)
    {ws : List Region} {n : Nat} (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes)
    (hf : Frame (ws ++ [below (fb s) n]) u.mem v.mem) (hs : ∀ r ∈ ws, Region.Sub r (SC s)) : SL i nb s v :=
  ⟨(slot_call hd hn hf hs (by decide)).trans h.1, (slot_call hd hn hf hs (by decide)).trans h.2⟩

/-- The counters stay through a write in `scratch`. -/
theorem SL.sc {i : Nat} {nb : State → BitVec 64} {s u v : State} (hd : DPre pc s) (h : SL i nb s u)
    {ws : List Region} (hf : Frame ws u.mem v.mem) (hs : ∀ r ∈ ws, Region.Sub r (SC s)) : SL i nb s v := by
  have hf' : Frame (ws ++ [below (fb s) 0]) u.mem v.mem :=
    hf.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  exact h.call hd (by decide) hf' hs

/-! ## A block -/

section
variable {e : Env pc}

/-- The facts at a block's start. -/
def B0 (i : Nat) (nb : State → BitVec 64) (s u : State) : Prop := PP s u ∧ SL i nb s u

theorem b0_sp {i : Nat} {nb : State → BitVec 64} {a b : State} (ha : B0 i nb e.s₁ a) (hb : B0 i nb e.s₂ b) :
    a.sp = b.sp := pp_sp ha.1 hb.1

/-- One block of IRPRF, with the label `label`, the bit length's code `len`,
to `scratch + dst + 32 i`, the blocks left from `C`. -/
theorem prfBody_ct {label : List Nat} {len count : List Instr} {dst i : Nat} {nb C : State → BitVec 64}
    (hi : i < 256) (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes) (hdst : dst < 2 ^ 15)
    (hn : label.length + 4 ≤ 16)
    {hc₁ : VG.Taint.Hint T} (ht₁ : (taint.check (ofRegs [.r9, .r11, .r8]) (.block (msgBytes label len)) hc₁).isSome = true)
    (hmsg : ∀ s u, DPre pc s → PP s u → u.gpr .r9 = scA s sMsg → u.gpr .r11 = BitVec.ofNat 64 i →
      u.gpr .r8 = s.gpr .r7 → WP isa (.block (msgBytes label len)) u fun w =>
        Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ Keep [.r10] u w)
    {hc₂ : VG.Taint.Hint T} (ht₂ : (taint.check (ofRegs []) (.block (incr count)) hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint T} (ht₃ : (taint.check (ofRegs []) (.block (prfUpdArgs (label.length + 4))) hc₃).isSome = true)
    {hc₄ : VG.Taint.Hint T}
    (ht₄ : (taint.check (ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) hc₄).isSome = true)
    (hcount : ∀ s u, DPre pc s → PP s u → sl s u oNB = nb s → WP isa (.block (incr count)) u fun w =>
      (w.mem = u.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s u oI + 1) ∧
        w.gpr .r9 = C s - (sl s u oI + 1)) ∧ Keep [.r12, .r11, .r9] u w) :
    RelCT isa (Rel e (B0 i nb)) (prfBody label len dst count)
      (Rel e fun s u => PP s u ∧ SL (i + 1) nb s u ∧ u.gpr .r9 = C s - BitVec.ofNat 64 (i + 1)) := by
  have e₁ : H.S = 96 := rfl
  have e₂ : H.W = 160 := rfl
  have e₃ : H.D = 32 := rfl
  unfold prfBody
  -- The head.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ u.gpr .r9 = scA s sMsg ∧
      u.gpr .r11 = BitVec.ofNat 64 i ∧ u.gpr .r8 = s.gpr .r7) [] (by taint_decide) (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r9, .r11, .r8] fun _ _ hc => prfHead_ok hc)
        fun v ⟨hv, vm, x9, x11, x8⟩ => ⟨⟨hv, hs.mem vm⟩, x9, by rw [x11, hs.1], x8⟩) ?_
  -- The message.
  refine RelCT.seq
    (rel_step (P' := B0 i nb) [.r9, .r11, .r8] ht₁ (fun a b ⟨ha, a9, a11, a8⟩ ⟨hb, b9, b11, b8⟩ => ⟨b0_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a9, b9, e.scA_eq]
      · rw [a11, b11]
      · rw [a8, b8, e.r]⟩)
      fun s u h ⟨⟨⟨R, EM, hu⟩, hs⟩, x9, x11, x8⟩ => WP.mono (hmsg s u h ⟨R, EM, hu⟩ x9 x11 x8)
        fun v ⟨F, kv⟩ => ⟨⟨R, EM, hu.step h kv.rd kv.wr kv.sp (fun r hr => kv.gpr r (by revert r; decide)) F
          fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (scSub (by decide))⟩,
          hs.sc h F fun r hr => by rw [List.mem_singleton.mp hr]; exact scSub (by decide)⟩) ?_
  -- HMAC's `init` with `KDK`.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ PMI sKDK s u) [] (by taint_decide) (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc =>
        macInitArgs_ok hc (key := sKDK) (by decide))
        fun v ⟨hv, vm, x⟩ => ⟨⟨hv, hs.mem vm⟩, hv, x⟩) ?_
  refine RelCT.seq
    (rel_post (P' := B0 i nb) (macInit_rel fun a b ⟨⟨_, ha⟩, _, hb⟩ => pmi_agree ha hb)
      fun s u h ⟨⟨_, hs⟩, ⟨_, _, hu⟩, u3, u4, u5, u6, u7⟩ => macInit_call h hu (by decide) (by decide) u3 u4 u5 u6 u7
        fun v hv _ _ hf => ⟨⟨_, _, hv⟩, hs.call h (by decide) hf fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact scSub (by decide)⟩) ?_
  -- `update` with the message.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = BitVec.ofNat 64 64 ∧
      u.gpr .r5 = scA s sMsg ∧ u.gpr .r6 = BitVec.ofNat 64 (label.length + 4) ∧ u.gpr .r7 = scA s sWork)
      [] ht₃ (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r7] fun _ _ hc =>
        prfUpdArgs_ok hc (n := label.length + 4) (by omega))
        fun v ⟨hv, vm, x⟩ => ⟨⟨hv, hs.mem vm⟩, x⟩) ?_
  refine RelCT.seq
    (rel_post (P' := B0 i nb) (upd_rel fun a b ⟨⟨ha, a3, a4, a5, a6, a7⟩, hb, b3, b4, b5, b6, b7⟩ => ⟨b0_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4]
      · rw [a5, b5, e.scA_eq]
      · rw [a6, b6]
      · rw [a7, b7, e.scA_eq]⟩)
      fun s u h ⟨⟨⟨_, _, hu⟩, hs⟩, u3, _, u5, u6, u7⟩ =>
        upd_call h hu (len := label.length + 4) u3 u5 (by rw [u6, BitVec.toNat_ofNat]; omega) u7
          (scD h (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide))
          (scD h (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide))
          (lowD h (by decide) (by unfold sMsg scrBytes; omega)) (scCovR h hu.wr (by unfold sMsg scrBytes; omega))
          fun v hv _ hf => ⟨⟨_, _, hv⟩, hs.call h (by decide) hf fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> exact scSub (by decide)⟩) ?_
  -- HMAC's `finalize` to the block.
  refine RelCT.seq
    (rel_step (P' := fun s u => B0 i nb s u ∧ u.gpr .r3 = scA s sSt ∧ u.gpr .r4 = scA s sOuter ∧
      u.gpr .r5 = BitVec.ofNat 64 (64 + (label.length + 4)) ∧ u.gpr .r6 = scA s (dst + 32 * i) ∧
      u.gpr .r7 = scA s sWork) [] ht₄ (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
      fun s u _ ⟨hu, hs⟩ => WP.mono (pp_block hu [.r12, .r3, .r4, .r5, .r6, .r10, .r7] fun _ _ hc =>
        prfFinArgs_ok hc (n := label.length + 4) (dst := dst) (by omega) hdst)
        fun v ⟨hv, vm, x3, x4, x5, x6, x7⟩ => ⟨⟨hv, hs.mem vm⟩, x3, x4, x5, by rw [x6, hs.1, shl5], x7⟩) ?_
  refine RelCT.seq
    (rel_post (P' := B0 i nb) (macFin_rel fun a b ⟨⟨ha, a3, a4, a5, a6, a7⟩, hb, b3, b4, b5, b6, b7⟩ => ⟨b0_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a3, b3, e.scA_eq]
      · rw [a4, b4, e.scA_eq]
      · rw [a5, b5]
      · rw [a6, b6, e.scA_eq]
      · rw [a7, b7, e.scA_eq]⟩)
      fun s u h ⟨⟨⟨_, _, hu⟩, hs⟩, u3, u4, _, u6, u7⟩ =>
        macFin_call h hu (o := dst + 32 * i) (by omega) hd2 u3 u4 u6 u7
          fun v hv _ hf => ⟨⟨_, _, hv⟩, hs.call h (by decide) hf fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact scSub (by decide)
            · exact scSub hd2
            · exact scSub (by decide)⟩) ?_
  -- The counter.
  refine rel_step [] ht₂ (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h ⟨⟨R, EM, hu⟩, hs⟩ => WP.mono (hcount s u h ⟨R, EM, hu⟩ hs.2) fun w ⟨⟨wm, w9⟩, kw⟩ => ?_
  have Fw : Frame [⟨fb s + BitVec.ofNat 64 oI, 8⟩] u.mem w.mem := by
    rw [wm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have one : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  refine ⟨⟨R, EM, hu.step h kw.rd kw.wr kw.sp (fun r hr => kw.gpr r (by revert r; decide)) Fw fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, show oI + 8 ≤ oLr by decide, rfl⟩)⟩,
    ⟨?_, ?_⟩, by rw [w9, hs.1, one]⟩
  · show w.mem.readW _ 64 = _
    rw [wm, Mem.readW_writeW_self64, hs.1, one]
  · show w.mem.readW _ 64 = _
    rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hs.2

/-! ## The loops -/

/-- The loop's invariant, `n` blocks before its end. -/
def LI (N : State → Nat) (nb : State → BitVec 64) (n : Nat) (s u : State) : Prop :=
  n ≤ N s ∧ 0 < n ∧ B0 (N s - n) nb s u

theorem prfLoop_ct {label : List Nat} {len count : List Instr} {dst : Nat} {N : State → Nat}
    {nb C : State → BitVec 64} (hN : N e.s₁ = N e.s₂) (hN0 : 0 < N e.s₁) (hN256 : N e.s₁ ≤ 256)
    (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * N e.s₁ ≤ scrBytes) (hdst : dst < 2 ^ 15) (hn : label.length + 4 ≤ 16)
    (hCe : C e.s₁ = C e.s₂) (hCv : ∀ i < N e.s₁, C e.s₁ - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N e.s₁ - (i + 1)))
    {hc₁ : VG.Taint.Hint T} (ht₁ : (taint.check (ofRegs [.r9, .r11, .r8]) (.block (msgBytes label len)) hc₁).isSome = true)
    (hmsg : ∀ i < 256, ∀ s u, DPre pc s → PP s u → u.gpr .r9 = scA s sMsg → u.gpr .r11 = BitVec.ofNat 64 i →
      u.gpr .r8 = s.gpr .r7 → WP isa (.block (msgBytes label len)) u fun w =>
        Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ Keep [.r10] u w)
    {hc₂ : VG.Taint.Hint T} (ht₂ : (taint.check (ofRegs []) (.block (incr count)) hc₂).isSome = true)
    (hcount : ∀ s u, DPre pc s → PP s u → sl s u oNB = nb s → WP isa (.block (incr count)) u fun w =>
      (w.mem = u.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s u oI + 1) ∧
        w.gpr .r9 = C s - (sl s u oI + 1)) ∧ Keep [.r12, .r11, .r9] u w)
    {hc₃ : VG.Taint.Hint T} (ht₃ : (taint.check (ofRegs []) (.block (prfUpdArgs (label.length + 4))) hc₃).isSome = true)
    {hc₄ : VG.Taint.Hint T}
    (ht₄ : (taint.check (ofRegs []) (.block (prfFinArgs (label.length + 4) dst)) hc₄).isSome = true) :
    RelCT isa (Rel e (B0 0 nb)) (.loop (prfBody label len dst count) (.nonzero .d .r9))
      (Rel e fun s u => B0 (N s) nb s u) := by
  have step : ∀ n, RelCT isa (Rel e (LI N nb n)) (prfBody label len dst count) fun a b =>
      isa.eval (.nonzero .d .r9) a = isa.eval (.nonzero .d .r9) b ∧
      (isa.eval (.nonzero .d .r9) a = some false → Rel e (fun s u => B0 (N s) nb s u) a b) ∧
      (isa.eval (.nonzero .d .r9) a = some true → ∃ m < n, Rel e (LI N nb m) a b) := by
    intro n
    by_cases hn' : 0 < n ∧ n ≤ N e.s₁
    · have hi : N e.s₁ - n < N e.s₁ := by omega_using [hn']
      refine (prfBody_ct (e := e) (i := N e.s₁ - n) (C := C) (by omega_using [hN256, hn']) hd1 (by omega_using [hd2, hn']) hdst hn ht₁
        (hmsg _ (by omega_using [hN256, hn'])) ht₂ ht₃ ht₄ hcount).mono
        (fun a b ⟨⟨_, _, ha⟩, _, _, hb⟩ => ⟨ha, by rw [hN]; exact hb⟩) fun a b ⟨⟨ha, sa, a9⟩, hb, sb, b9⟩ => ?_
      have ev : ∀ x : State, isa.eval (.nonzero .d .r9) x = some (x.gpr .r9 != 0) :=
        fun x => VG.Proof.Bignum.PPC64LE.eval_nonzero x .r9
      have a9' : a.gpr .r9 = BitVec.ofNat 64 (N e.s₁ - (N e.s₁ - n + 1)) := by rw [a9, hCv _ hi]
      have b9' : b.gpr .r9 = BitVec.ofNat 64 (N e.s₁ - (N e.s₁ - n + 1)) := by rw [b9, ← hCe, hCv _ hi]
      have hz : (BitVec.ofNat 64 (N e.s₁ - (N e.s₁ - n + 1)) != 0) = decide (n ≠ 1) := by
        rw [VG.Proof.Bignum.PPC64LE.ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hN256])]
        exact decide_eq_decide.mpr (by omega_using [hn'])
      refine ⟨by rw [ev, ev, a9', b9'], fun hf => ?_, fun ht => ?_⟩
      · rw [ev, a9', hz] at hf
        have : n = 1 := by simpa using hf
        subst this
        exact ⟨⟨ha, by rw [show N e.s₁ - 1 + 1 = N e.s₁ by omega_using [hN0]] at sa; exact sa⟩,
          ⟨hb, by rw [show N e.s₁ - 1 + 1 = N e.s₁ by omega_using [hN0], hN] at sb; exact sb⟩⟩
      · rw [ev, a9', hz] at ht
        have : n ≠ 1 := by simpa using ht
        refine ⟨n - 1, by omega_using [hn'], ⟨by omega_using [hn'], by omega_using [hn', this], ha, ?_⟩, ⟨by rw [← hN]; omega_using [hn'], by omega_using [hn', this], hb, ?_⟩⟩
        · rw [show N e.s₁ - (n - 1) = N e.s₁ - n + 1 by omega_using [hn']]; exact sa
        · rw [← hN, show N e.s₁ - (n - 1) = N e.s₁ - n + 1 by omega_using [hn']]; exact sb
    · exact RelCT.of_false fun a b ⟨⟨h₁, h₂, _⟩, _⟩ => hn' ⟨h₂, h₁⟩
  exact (RelCT.loop (Q := Rel e fun s u => B0 (N s) nb s u) _ step (N e.s₁)).mono
    (fun a b ⟨ha, hb⟩ => ⟨⟨Nat.le_refl _, hN0, by rw [Nat.sub_self]; exact ha⟩,
      ⟨by rw [← hN], hN0, by rw [← hN, Nat.sub_self]; exact hb⟩⟩) fun _ _ h => h

/-- The number of `AM`'s blocks. -/
abbrev nbOf (s : State) : BitVec 64 := BitVec.ofNat 64 (((s.gpr .r7).toNat + 31) / 32)

theorem clLoop_ct : RelCT isa (Rel e PP) clLoop (Rel e fun s u => B0 8 nbOf s u) := by
  have hk₁ := e.h₁.k2
  have hk₁' := e.h₁.k1
  unfold clLoop
  refine RelCT.seq (rel_step (P' := B0 0 nbOf) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h ⟨R, EM, hu⟩ => WP.mono (clStart_ok h hu) fun v ⟨hv, c, n, _⟩ => ⟨⟨_, _, hv⟩, c, n⟩) ?_
  exact prfLoop_ct (N := fun _ => 8) rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl (fun i hi => Offset.ofNat_sub_ofNat (by omega_using [hi])) (by taint_decide)
    (fun i hi s u h hu x9 x11 _ => WP.mono (msgCL_ok x9 x11 hi (let ⟨_, _, hu⟩ := hu; hu.msgW h))
      fun w ⟨⟨F, _⟩, k⟩ => ⟨F, k⟩)
    (by taint_decide) (fun s u _ ⟨_, _, hu⟩ _ => incrCL_ok hu) (by taint_decide) (by taint_decide)

theorem amLoop_ct : RelCT isa (Rel e fun s u => B0 8 nbOf s u) amLoop (Rel e PP) := by
  have hk₁ := e.h₁.k2
  have hk₁' := e.h₁.k1
  unfold amLoop
  refine RelCT.seq (rel_step (P' := B0 0 nbOf) [] (by taint_decide)
    (fun a b ha hb => ⟨b0_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h ⟨⟨R, EM, hu⟩, _, hnb⟩ => WP.mono (amStart_ok h hu hnb) fun v ⟨hv, c, n, _⟩ => ⟨⟨_, _, hv⟩, c, n⟩) ?_
  refine rel_mono (prfLoop_ct (N := fun s => ((s.gpr .r7).toNat + 31) / 32) (C := nbOf) (by rw [e.r]) (by omega_using [hk₁'])
    (by omega_using [hk₁]) (by decide) (by unfold sAM scrBytes; omega_using [hk₁]) (by decide) (by decide)
    (by show nbOf e.s₁ = nbOf e.s₂; rw [nbOf, nbOf, e.r]) (fun i hi => Offset.ofNat_sub_ofNat (by omega_using [hi]))
    (by taint_decide)
    (fun i hi s u h hu x9 x11 x8 => WP.mono (msgAM_ok x9 x11 x8 hi (DPre.k2 h) (let ⟨_, _, hu⟩ := hu; hu.msgW h))
      fun w ⟨⟨F, _⟩, k⟩ => ⟨F, k⟩)
    (by taint_decide) (fun s u _ ⟨_, _, hu⟩ hnb => WP.mono (incrAM_ok hu) fun w ⟨⟨a, b⟩, c⟩ => ⟨⟨a, by rw [b, hnb]⟩, c⟩)
    (by taint_decide) (by taint_decide)) fun _ _ h => h.1

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end

/-! ### `RsaPkcs1Enc.PPC64LE.DecCT1`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time up to `D`

The setup and `D`'s blocks and loops, by the taint analysis from the
registers correctness fixes (`setup_ct`, `dBuild_ct`), and the call of
`vg_rsa_private_checked`, by its constant time (`priv_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

section
variable {pc : Bool} {e : Env pc}

/-- After the frame's push. -/
def PEnt (s u : State) : Prop := u = allocated frameBytes s

theorem setup_ct : RelCT isa (Rel e PEnt) (.block (setup pc)) (Rel e (AtPriv pc)) := by
  have hpin : ∀ a b, PEnt e.s₁ a → PEnt e.s₂ b → AgreeOn [] a b := fun a b ha hb =>
    ⟨by rw [ha, hb]; show e.s₁.sp - _ = e.s₂.sp - _; rw [e.S.sp], fun _ h => nomatch h⟩
  cases pc
  · exact rel_step [] (by taint_decide) hpin fun _ _ h hu => hu ▸ setup_ok h
  · exact rel_step [] (by taint_decide) hpin fun _ _ h hu => hu ▸ setup_ok h

omit e in
theorem bytes_priv {s u : State} (A : AtPriv pc s u) {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨p, n⟩ (kR s))
    (hl : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt u.mem p n = Spec.Rsa.bytesAt s.mem p n :=
  bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl

/-- What two runs share at the call. -/
theorem priv_facts {u₁ u₂ : State} (A₁ : AtPriv pc e.s₁ u₁) (A₂ : AtPriv pc e.s₂ u₂) :
    (callE pc e.s₁ u₁).sp = (callE pc e.s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc e.s₁ u₁).gpr r = (callE pc e.s₂ u₂).gpr r) ∧
      (∀ i < nCallArgs pc, stackArg (callE pc e.s₁ u₁) i = stackArg (callE pc e.s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc e.s₁ u₁).mem ((callE pc e.s₁ u₁).gpr .r5) ((callE pc e.s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc e.s₂ u₂).mem ((callE pc e.s₂ u₂).gpr .r5) ((callE pc e.s₂ u₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc e.s₁ u₁).mem ((callE pc e.s₁ u₁).gpr .r7) ((callE pc e.s₁ u₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc e.s₂ u₂).mem ((callE pc e.s₂ u₂).gpr .r7) ((callE pc e.s₂ u₂).gpr .r8).toNat := by
  have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
  refine ⟨by rw [show (callE pc e.s₁ u₁).sp = fb e.s₁ from A₁.sp, show (callE pc e.s₂ u₂).sp = fb e.s₂ from A₂.sp,
    e.fb_eq], fun r hr => ?_, fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, e.S.arg _ (nCall_lt hi).2],
    ?_, ?_⟩
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, e.r]
    · rw [A₁.r4, A₂.r4, e.r]
    · rw [A₁.r5, A₂.r5, e.r]
    · rw [A₁.r6, A₂.r6, e.r]
    · rw [A₁.r7, A₂.r7, e.r]
    · rw [A₁.r8, A₂.r8, e.r]
    · rw [A₁.r9, A₂.r9, e.arg]
    · rw [A₁.r10, A₂.r10, e.r]
  · rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6,
      bytes_priv A₁ e.h₁.kn.symm (by have := e.h₁.wn; omega_using []), bytes_priv A₂ e.h₂.kn.symm (by have := e.h₂.wn; omega_using []), e.S.n]
  · rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8,
      bytes_priv A₁ e.h₁.ke.symm (by have := e.h₁.we; omega_using []), bytes_priv A₂ e.h₂.ke.symm (by have := e.h₂.we; omega_using []), e.S.e]

omit e in
/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s u : State} (X : PreX s) (A : AtPriv true s u) :
    Spec.Rsa.privatePrecomputedLeak (callE true s u).mem (stackArg (callE true s u) 12)
        ((callE true s u).gpr .r6).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 15) (s.gpr .r7).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .r7).toNat ≤ (stackArg s 16).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide),
    callE_gpr (pc := true) s u (r := .r6), A.r6]
  refine congrArg (List.map BitVec.toNat) ?_
  have subPre : Region.Sub ⟨stackArg s 15, 8 * Spec.Rsa.precomputedWords (s.gpr .r7).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

theorem priv_ct : RelCT isa (Rel e (AtPriv pc)) (privCall pc) (Rel e AtD) := by
  refine rel_postX ?_ fun s u h X A => call_ok h X A fun v hv => hv
  cases pc with
  | false =>
    exact VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨A₁, A₂⟩ =>
        let ⟨hsp, hr, ha, hn, he⟩ := priv_facts A₁ A₂
        ⟨callRd false e.s₁, callWr e.s₁, callRd false e.s₂, callWr e.s₂,
          Rsa.PPC64LE.Priv.pre_of_preP (preP_entry e.h₁ A₁), Rsa.PPC64LE.Priv.pre_of_preP (preP_entry e.h₂ A₂),
          Rsa.PPC64LE.Priv.pub_of hsp hr (fun i hi => ha i (lt_nCall hi)) hn he,
          (call_covers e.h₁ A₁).1, (call_covers e.h₁ A₁).2, (call_covers e.h₂ A₂).1, (call_covers e.h₂ A₂).2⟩
  | true =>
    exact VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨A₁, A₂⟩ =>
        let ⟨hsp, hr, ha, hn, he⟩ := priv_facts A₁ A₂
        ⟨callRd true e.s₁, callWr e.s₁, callRd true e.s₂, callWr e.s₂,
          Rsa.PPC64LE.Priv.pre_of_prePX (preP_entry e.h₁ A₁) (preX_entry e.h₁ (e.X₁ rfl) A₁),
          Rsa.PPC64LE.Priv.pre_of_prePX (preP_entry e.h₂ A₂) (preX_entry e.h₂ (e.X₂ rfl) A₂),
          Rsa.PPC64LE.Priv.pub_ofP hsp hr (fun i hi => ha i (by simp only [nCallArgs, ↓reduceIte]; exact hi)) hn he
            (by rw [pre_leak (e.X₁ rfl) A₁, pre_leak (e.X₂ rfl) A₂]; exact e.S.leak rfl),
          (call_covers e.h₁ A₁).1, (call_covers e.h₁ A₁).2, (call_covers e.h₂ A₂).1, (call_covers e.h₂ A₂).2⟩

/-! ## `D` -/

def PZ0 (s u : State) : Prop := ∃ R EM, ZInv s R EM 0 u ∧ u.gpr .r9 = s.gpr .r7
def PZ (s u : State) : Prop := ∃ R EM, ZInv s R EM (s.gpr .r7).toNat u
def PC0 (s u : State) : Prop := ∃ R EM, CInv s R EM 0 u ∧ u.gpr .r9 = stackArg s 0
def PDB (s u : State) : Prop := ∃ R EM, DB s R EM u

theorem dBuild_ct : RelCT isa (Rel e AtD) dBuild (Rel e PDB) := by
  refine RelCT.seq (rel_step [] (by taint_decide)
    (fun a b A B => ⟨by rw [A.sp, B.sp, e.fb_eq], fun _ h => nomatch h⟩)
    fun s u h A => WP.mono (dPtrs₁_inv h A) fun v ⟨z, z9⟩ => (⟨_, _, z, z9⟩ : PZ0 s v)) ?_
  refine RelCT.seq (rel_step [.r11, .r9] (by taint_decide)
    (fun a b ⟨_, _, za, a9⟩ ⟨_, _, zb, b9⟩ => ⟨by rw [za.post.sp, zb.post.sp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [za.r11, zb.r11, e.scA_eq]
      · rw [a9, b9, e.r]⟩)
    fun s u h ⟨_, _, z, z9⟩ => WP.mono (zeroLoop_ok h z z9) fun v hv => (⟨_, _, hv⟩ : PZ s v)) ?_
  refine RelCT.seq (rel_step [.r12] (by taint_decide)
    (fun a b ⟨_, _, za⟩ ⟨_, _, zb⟩ => ⟨by rw [za.post.sp, zb.post.sp, e.fb_eq], fun r hr => by
      rw [List.mem_singleton.mp hr, za.r12, zb.r12, e.fb_eq]⟩)
    fun s u h ⟨_, _, z⟩ => WP.mono (dPtrs₂_inv h z) fun v ⟨c, c9⟩ => (⟨_, _, c, c9⟩ : PC0 s v)) ?_
  refine rel_step [.r10, .r11, .r9] (by taint_decide)
    (fun a b ⟨_, _, ca, a9⟩ ⟨_, _, cb, b9⟩ => ⟨by rw [ca.post.sp, cb.post.sp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [ca.r10, cb.r10, e.r]
      · rw [ca.r11, cb.r11, e.r, e.arg, e.scA_eq]
      · rw [a9, b9, e.arg]⟩)
    fun s u h ⟨_, _, c, c9⟩ => WP.mono (copyLoop_ok h c c9) fun v hv => (⟨_, _, cinv_db h hv⟩ : PDB s v)

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end

/-! ### `RsaPkcs1Enc.PPC64LE.DecFin`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecSel`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecScan`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.DecAl`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the alternative length

The mask of the candidates, `bitMask (k - 11)`, by doublings (`maskPart_ok`),
and the alternative length, the last masked candidate of `CL` not above
`k - 11` (`alPart_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (bitMask altStep)

variable {pc : Bool}

/-- The borrow of `a - b`, for values below `2 ^ 63`. -/
theorem borrow (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if b ≤ a then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> omega_arith

/-- The select by a mask from a borrow. -/
theorem xor_sel (a c : BitVec 64) (p : Prop) [Decidable p] :
    a ^^^ ((a ^^^ c) &&& (BitVec.ofNat 64 (if p then 0 else 1) - BitVec.ofNat 64 1)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [hp, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

theorem read1_64 (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = (m a).setWidth 64 := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp

theorem maskBody_ok {t : State} :
    WP isa (.block [.add .r8 .r8 .r8, .addi .r8 .r8 1, .sub .r10 .r8 .r9, .lsr .d .r10 .r10 63]) t
      fun u => (u.mem = t.mem ∧ u.gpr .r8 = t.gpr .r8 + t.gpr .r8 + BitVec.ofNat 64 1 ∧
        u.gpr .r10 = (t.gpr .r8 + t.gpr .r8 + BitVec.ofNat 64 1 - t.gpr .r9) >>> 63) ∧ Keep [.r8, .r10] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  prun [exec_addi (show Reg.r8 ≠ .r0 by decide) (show 1 < 2 ^ 15 by decide)]

theorem dbl (p : Nat) (h1 : 1 ≤ p) (h : p * 2 < 2 ^ 34) :
    BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (p * 2 - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- An iteration of the mask's loop: `2 ^ j - 1` to `2 ^ (j + 1) - 1`, and whether to go on. -/
theorem maskStep_ok {x j : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (hj : j < Spec.RsaPkcs1Enc.bitLength x)
    {u : State} (hu8 : u.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1)) (hu9 : u.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa (.block [.add .r8 .r8 .r8, .addi .r8 .r8 1, .sub .r10 .r8 .r9, .lsr .d .r10 .r10 63]) u
      fun w => (w.mem = u.mem ∧ Keep [.r8, .r10] u w ∧ w.gpr .r8 = BitVec.ofNat 64 (2 ^ (j + 1) - 1)) ∧
        ((w.gpr .r10).toNat ≠ 0 ↔ j + 1 ≠ Spec.RsaPkcs1Enc.bitLength x) := by
  have hlt := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j) (by omega_using [hx1]) hj
  have hpj : 2 ^ (j + 1) < 2 ^ 34 := by
    rw [Nat.pow_succ]; generalize 2 ^ j = p at *; omega_using [hx, hlt]
  have e8 : BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (2 ^ (j + 1) - 1) := by
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ ..] at hpj ⊢
    exact dbl _ Nat.one_le_two_pow hpj
  refine WP.mono maskBody_ok fun w ⟨⟨wm, w8, w10⟩, kw⟩ => ⟨⟨wm, kw, by rw [w8, hu8, e8]⟩, ?_⟩
  rw [w10, hu8, hu9, e8, borrow _ _ (by omega_using [hpj]) (by omega_using [hx]), BitVec.toNat_ofNat]
  by_cases he : j + 1 = Spec.RsaPkcs1Enc.bitLength x
  · have h1 := Proof.RsaPkcs1Enc.bitMask_ge (x := x) (by omega_using [hx1])
    rw [he]
    simp only [show x ≤ 2 ^ Spec.RsaPkcs1Enc.bitLength x - 1 from h1, ↓reduceIte]; omega_using []
  · have h1 := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j + 1) (by omega_using [hx1]) (by omega_using [hj, he])
    simp only [show ¬ x ≤ 2 ^ (j + 1) - 1 by omega_using [h1], ↓reduceIte]; omega_using [he]

theorem bitLength_pos {x : Nat} (hx1 : 1 ≤ x) : 0 < Spec.RsaPkcs1Enc.bitLength x := by
  simp only [Spec.RsaPkcs1Enc.bitLength]; split <;> omega_arith

theorem maskLoop_ok {t₀ : State} {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (h8 : t₀.gpr .r8 = BitVec.ofNat 64 0)
    (h9 : t₀.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa maskLoop t₀ fun u => u.mem = t₀.mem ∧ Keep [.r8, .r10] t₀ u ∧ u.gpr .r8 = BitVec.ofNat 64 (bitMask x) :=
  VG.Proof.Bignum.PPC64LE.count_loop (bitLength_pos hx1) (fun j u => u.mem = t₀.mem ∧ Keep [.r8, .r10] t₀ u ∧
    u.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1))
    (fun _ hj u ⟨hm, hk, hu8⟩ => WP.mono (maskStep_ok hx1 hx hj hu8
      (by rw [hk.gpr _ (by decide), h9])) fun _ ⟨⟨wm, kw, w8⟩, w10⟩ => ⟨⟨wm.trans hm, hk.trans' kw, w8⟩, w10⟩)
    ⟨rfl, Keep.refl _ _, h8⟩

theorem cand_bv (a b : Byte) {M : Nat} (hM : M < 2 ^ 64) :
    (a.setWidth 64 <<< 8 + b.setWidth 64) &&& BitVec.ofNat 64 M =
      BitVec.ofNat 64 ((256 * a.toNat + b.toNat) &&& M) := by
  have ha := a.isLt
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  have hl : (256 * a.toNat + b.toNat) &&& M ≤ 256 * a.toNat + b.toNat := Nat.and_le_left
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega_using []), Nat.mod_eq_of_lt (a := b.toNat) (by omega_using []),
    Nat.mod_eq_of_lt (a := M) hM, Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8) (by omega_using []),
    Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8 + b.toNat) (by omega_using []), show a.toNat * 2 ^ 8 = 256 * a.toNat by omega_using [],
    Nat.mod_eq_of_lt (by omega_using [hl])]

theorem alBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 1) 1) :
    WP isa (.block alBody) t fun u => (u.mem = t.mem ∧
      u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 2 ∧ u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1 ∧
      u.gpr .r6 = t.gpr .r6 ^^^ ((t.gpr .r6 ^^^ (((t.mem (t.gpr .r11 + BitVec.ofNat 64 0)).setWidth 64 <<< 8 +
          (t.mem (t.gpr .r11 + BitVec.ofNat 64 1)).setWidth 64) &&& t.gpr .r8)) &&&
        (((t.gpr .r9 - (((t.mem (t.gpr .r11 + BitVec.ofNat 64 0)).setWidth 64 <<< 8 +
          (t.mem (t.gpr .r11 + BitVec.ofNat 64 1)).setWidth 64) &&& t.gpr .r8)) >>> 63) - BitVec.ofNat 64 1))) ∧
      Keep [.r10, .r5, .r4, .r6, .r11, .r7] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  unfold alBody
  prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c0 h0,
    exec_lbz (s := (t.write .r10 ((t.mem.read (t.gpr .r11 + BitVec.ofNat 64 0) 1).setWidth 64)).write .r10
      (((t.mem.read (t.gpr .r11 + BitVec.ofNat 64 0) 1).setWidth 64) <<< 8))
      (show Reg.r11 ≠ .r0 by decide) c1 (by exact h1),
    exec_addi (show Reg.r11 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide)]
  simp only [read1_64]

theorem bytes_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem alLoop_ok {t₀ : State} {x M : Nat} {CL : List Byte} {B : Addr}
    (hx : x < 2 ^ 32) (hM : M = bitMask x) (hMl : M < 2 ^ 32)
    (hm : ∀ i < 256, t₀.mem (B + BitVec.ofNat 64 i) = CL.getD i 0)
    (hr : ∀ i < 256, InRegions (t₀.rd ++ t₀.wr) (B + BitVec.ofNat 64 i) 1)
    (h8 : t₀.gpr .r8 = BitVec.ofNat 64 M) (h9 : t₀.gpr .r9 = BitVec.ofNat 64 x) (h11 : t₀.gpr .r11 = B)
    (h7 : t₀.gpr .r7 = BitVec.ofNat 64 128) (h6 : t₀.gpr .r6 = 0) :
    WP isa alLoop t₀ fun u => u.mem = t₀.mem ∧ Keep [.r10, .r5, .r4, .r6, .r11, .r7] t₀ u ∧
      u.gpr .r6 = BitVec.ofNat 64 ((List.range 128).foldl (altStep (x + 11) CL) 0) := by
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (N := 128) (by decide) (by decide)
    (fun j u => u.mem = t₀.mem ∧ Keep [.r10, .r5, .r4, .r6, .r11, .r7] t₀ u ∧ u.gpr .r11 = B + BitVec.ofNat 64 (2 * j) ∧
      u.gpr .r6 = BitVec.ofNat 64 ((List.range j).foldl (altStep (x + 11) CL) 0))
    (fun j hj u ⟨um, ku, u11, u6⟩ _ => ?_) ⟨rfl, Keep.refl _ _, by rw [h11]; exact (BitVec.add_zero _).symm, h6⟩
    h7 |>.mono fun u ⟨a, b, _, c⟩ => ⟨a, b, c⟩
  have hr0 := hr (2 * j) (by omega_using [hj])
  have hr1 := hr (2 * j + 1) (by omega_using [hj])
  rw [← ku.rd, ← ku.wr] at hr0 hr1
  have u8 : u.gpr .r8 = BitVec.ofNat 64 M := (ku.gpr _ (by decide)).trans h8
  have u9 : u.gpr .r9 = BitVec.ofNat 64 x := (ku.gpr _ (by decide)).trans h9
  refine WP.mono (alBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) (by rw [u11, Offset.add_add]; exact hr1))
    fun w ⟨⟨wm, w11, w7, w6⟩, kw⟩ => ⟨⟨wm.trans um, ku.trans' kw, by rw [w11, u11, Offset.add_add]; rfl, ?_⟩, w7⟩
  rw [w6, u6, u8, u9, u11, BitVec.add_zero, Offset.add_add, um, hm _ (by omega_using [hj]), hm _ (by omega_using [hj]),
    cand_bv _ _ (by omega_using [hMl]), Proof.RsaPkcs1Enc.foldl_range_succ]
  have hc : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M < 2 ^ 32 :=
    Nat.lt_of_le_of_lt Nat.and_le_right hMl
  rw [borrow _ _ (by omega_using [hx]) (by omega_using [hc]), xor_sel]
  have he : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M =
      Spec.Rsa.os2ip [CL.getD (2 * j) 0, CL.getD (2 * j + 1) 0] % 2 ^ Spec.RsaPkcs1Enc.bitLength (x + 11 - 11) := by
    rw [Proof.RsaPkcs1Enc.cand_eq, Nat.add_sub_cancel, hM, Proof.RsaPkcs1Enc.bitMask, Nat.and_two_pow_sub_one_eq_mod]
  rw [he]
  simp only [altStep, Nat.add_sub_cancel]
  split <;> rfl

/-! ## The parts -/

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

omit h in
theorem AMR.regs {t u : State} (hl : AMR s R EM kd t) (hk : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10,
    .r11, .r12] t u) (hm : u.mem = t.mem) : AMR s R EM kd u :=
  ⟨hl.post.regs hk.rd hk.wr hk.sp hm fun r hr => hk.gpr r (by revert r; decide), by rw [hm]; exact hl.cl,
    by rw [hm]; exact hl.am⟩

/-- After the mask: `bitMask (k - 11)` in `r8` and `k - 11` in `r9`. -/
structure MK (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR s R EM kd t
  r8 : t.gpr .r8 = BitVec.ofNat 64 (bitMask ((s.gpr .r7).toNat - 11))
  r9 : t.gpr .r9 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11)

theorem maskPart_ok {t : State} (hl : AMR s R EM kd t) : WP isa maskPart t (MK s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hl.post
  have c1 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have i1 := slot_rd hc (d := oK) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r9, .r8] (Q := fun u => u.mem = t.mem ∧
    u.gpr .r9 = s.gpr .r7 - BitVec.ofNat 64 11 ∧ u.gpr .r8 = BitVec.ofNat 64 0) ?_ rfl)
    fun t₁ ⟨⟨m₁, x9, x8⟩, k₁⟩ => ?_)
  · unfold maskInit
    prun [fp, exec_addSp0, hc.sp, c1, i1, hc.sl.k]
  have e9 : s.gpr .r7 - BitVec.ofNat 64 11 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hk64]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  rw [e9] at x9
  exact WP.mono (maskLoop_ok (x := (s.gpr .r7).toNat - 11) (by omega_using [hk64]) (by omega_using [hk]) x8 x9) fun u ⟨um, ku, u8⟩ =>
    ⟨hl.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁), u8,
      (ku.gpr _ (by decide)).trans x9⟩

/-- `CL`. -/
abbrev clOf (kd : List Byte) : List Byte := Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

/-- After the alternative length. -/
structure AL (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR s R EM kd t
  al : t.gpr .r6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))

theorem alPart_ok {t : State} (hm : MK s R EM kd t) : WP isa alPart t (AL s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hm.amr.post
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : sCL < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r11, .r7, .r6] (Q := fun u => u.mem = t.mem ∧
    u.gpr .r11 = scA s sCL ∧ u.gpr .r7 = BitVec.ofNat 64 128 ∧ u.gpr .r6 = BitVec.ofNat 64 0) ?_ rfl)
    fun t₁ ⟨⟨m₁, x11, x7, x6⟩, k₁⟩ => ?_)
  · unfold alInit scr
    prun [fp, exec_addSp0, hc.sp, c1, c2, i1, hc.sl.scr, exec_addi (show Reg.r11 ≠ .r0 by decide) c2]
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  have hcl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = clOf kd := hm.amr.cl
  have hM := Proof.RsaPkcs1Enc.bitMask_le (x := (s.gpr .r7).toNat - 11) (by omega_using [hk64])
  refine WP.mono (alLoop_ok (x := (s.gpr .r7).toNat - 11) (M := bitMask ((s.gpr .r7).toNat - 11)) (CL := clOf kd)
    (B := scA s sCL) (by omega_using [hk]) rfl (by omega_using [hk, hM])
    (fun i hi => by rw [← hcl, bytes_getD _ _ hi, m₁])
    (fun i hi => by rw [Offset.add_add]; exact scInR h hc₁.wr (a := sCL + i) (n := 1) (by unfold sCL scrBytes; omega_using [hi]))
    (by rw [k₁.gpr _ (by decide), hm.r8]) (by rw [k₁.gpr _ (by decide), hm.r9]) x11 x7 x6) fun u ⟨um, ku, u6⟩ =>
    ⟨hm.amr.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁),
      by rw [u6, Nat.sub_add_cancel (by omega_using [hk64])]; rfl⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the scan of `EM`

The first zero of `EM` from index 2 (`scanPart_ok`): whether there is one as
a mask in `r5`, and where in `r3`, as `firstZero` says.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero)

variable {pc : Bool}

/-- A Boolean as a mask. -/
def bm (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem zero_mask (b : Byte) :
    (0 : BitVec 64) - ((b.setWidth 64 - BitVec.ofNat 64 1) >>> 63) = bm (decide (b = 0)) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have hl := b.isLt
    have e : b.setWidth 64 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (b.toNat - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hb]),
        BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using []
    have e2 : BitVec.ofNat 64 (b.toNat - 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega_using []
    rw [e, e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

theorem scanBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1)
    (h0' : t.gpr .r0 = 0) (h8 : t.gpr .r8 = BitVec.allOnes 64) :
    WP isa (.block scanBody) t fun u => (u.mem = t.mem ∧ u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 1 ∧
      u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1 ∧ u.gpr .r4 = t.gpr .r4 + BitVec.ofNat 64 1 ∧
      u.gpr .r5 = t.gpr .r5 ||| bm (decide (t.mem (t.gpr .r11 + BitVec.ofNat 64 0) = 0)) ∧
      u.gpr .r3 = t.gpr .r3 ||| ((t.gpr .r5 ^^^ BitVec.allOnes 64) &&&
        bm (decide (t.mem (t.gpr .r11 + BitVec.ofNat 64 0) = 0)) &&& t.gpr .r4)) ∧
      Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  unfold scanBody
  prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c0 h0, exec_addi (show Reg.r4 ≠ .r0 by decide) c1,
    exec_addi (show Reg.r11 ≠ .r0 by decide) c1, h0', h8]
  simp only [read1_64, zero_mask]
  exact ⟨trivial, trivial⟩

theorem firstZero_succ (EM : List Byte) (j : Nat) :
    firstZero EM (2 + (j + 1)) = match firstZero EM (2 + j) with
      | some i => some i
      | none => if EM.getD (2 + j) 1 = 0 then some (2 + j) else none := by
  show firstZero EM ((2 + j) + 1) = _
  rw [firstZero]
  cases firstZero EM (2 + j) with
  | some i => rfl
  | none => simp

theorem r3_pos (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm true &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  show 0#64 ||| ((0#64 ^^^ BitVec.allOnes 64) &&& BitVec.allOnes 64 &&& BitVec.ofNat 64 n) = _
  rw [BitVec.zero_xor, BitVec.and_allOnes, BitVec.allOnes_and, BitVec.zero_or]

theorem r3_neg (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm false &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bm]

theorem scanLoop_ok {t₀ : State} {O : Addr} {EM : List Byte} {k : Nat} (hk : 3 ≤ k) (hk2 : k < 2 ^ 32)
    (hEM : ∀ i < k, t₀.mem (O + BitVec.ofNat 64 i) = EM.getD i 1)
    (hr : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (O + BitVec.ofNat 64 i) 1)
    (h11 : t₀.gpr .r11 = O + BitVec.ofNat 64 2) (h7 : t₀.gpr .r7 = BitVec.ofNat 64 (k - 2))
    (h4 : t₀.gpr .r4 = BitVec.ofNat 64 2) (h5 : t₀.gpr .r5 = 0) (h3 : t₀.gpr .r3 = 0)
    (h0 : t₀.gpr .r0 = 0) (h8 : t₀.gpr .r8 = BitVec.allOnes 64) :
    WP isa scanLoop t₀ fun u => u.mem = t₀.mem ∧ Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t₀ u ∧
      u.gpr .r5 = bm (firstZero EM k).isSome ∧ u.gpr .r3 = BitVec.ofNat 64 ((firstZero EM k).getD 0) := by
  refine (VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (N := k - 2) (by omega_using [hk2]) (by omega_using [hk])
    (fun j u => u.mem = t₀.mem ∧ Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t₀ u ∧
      u.gpr .r11 = O + BitVec.ofNat 64 (2 + j) ∧ u.gpr .r4 = BitVec.ofNat 64 (2 + j) ∧
      u.gpr .r5 = bm (firstZero EM (2 + j)).isSome ∧ u.gpr .r3 = BitVec.ofNat 64 ((firstZero EM (2 + j)).getD 0))
    (fun j hj u ⟨um, ku, u11, u4, u5, u3⟩ _ => ?_)
    ⟨rfl, Keep.refl _ _, h11, h4, by rw [h5]; rfl, by rw [h3]; rfl⟩ h7).mono
    fun u ⟨um, ku, _, _, u5, u3⟩ => by
      rw [show 2 + (k - 2) = k by omega_using [hk]] at u5 u3
      exact ⟨um, ku, u5, u3⟩
  have hr0 := hr (2 + j) (by omega_using [hj])
  rw [← ku.rd, ← ku.wr] at hr0
  have hb : u.mem (u.gpr .r11 + BitVec.ofNat 64 0) = EM.getD (2 + j) 1 := by
    rw [u11, BitVec.add_zero, um, hEM _ (by omega_using [hj])]
  refine WP.mono (scanBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) ((ku.gpr _ (by decide)).trans h0)
    ((ku.gpr _ (by decide)).trans h8))
    fun w ⟨⟨wm, w11, w7, w4, w5, w3⟩, kw⟩ => ⟨⟨wm.trans um, ku.trans' kw, by rw [w11, u11, Offset.add_add]; rfl,
      by rw [w4, u4, ← BitVec.ofNat_add]; rfl, ?_, ?_⟩, w7⟩
  · rw [w5, u5, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i => simp only [Option.isSome_some, bm, ite_true, BitVec.allOnes_or]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, bm, hz, decide_true, Bool.false_eq_true, ite_true, ite_false,
          Option.isSome_some]
        rfl
      · simp only [Option.isSome_none, bm, hz, decide_false, Bool.false_eq_true, ite_false]
        rfl
  · rw [w3, u3, u5, u4, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i =>
      simp only [Option.isSome_some, bm, ite_true, BitVec.xor_self, BitVec.zero_and, BitVec.or_zero,
        Option.getD_some]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, hz, decide_true, ite_true, Option.getD_none, Option.getD_some]
        exact r3_pos _
      · simp only [Option.isSome_none, hz, decide_false, ite_false, Option.getD_none]
        exact r3_neg _

theorem bytes_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

/-- After the scan. -/
structure SCN (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR s R EM kd t
  al : t.gpr .r6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))
  r5 : t.gpr .r5 = bm (firstZero EM (s.gpr .r7).toNat).isSome
  r3 : t.gpr .r3 = BitVec.ofNat 64 ((firstZero EM (s.gpr .r7).toNat).getD 0)
  r0 : t.gpr .r0 = 0
  r8 : t.gpr .r8 = BitVec.allOnes 64

/-- A byte of `out` is accessible. -/
theorem outIn {t : State} (hc : Post s R EM t) {i : Nat} (hi : i < (s.gpr .r7).toNat) :
    InRegions (t.rd ++ t.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h4] at this
  exact ⟨oR s, by rw [hc.wr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem scanPart_ok {t : State} (hl : AL s R EM kd t) : WP isa scanPart t (SCN s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hl.amr.post
  have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have i1 := slot_rd hc (d := oOut) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  have e7 : s.gpr .r7 - BitVec.ofNat 64 2 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hk64]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r11, .r7, .r4, .r5, .r3, .r0, .r8]
    (Q := fun u => u.mem = t.mem ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 2 ∧
      u.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) ∧ u.gpr .r4 = BitVec.ofNat 64 2 ∧ u.gpr .r5 = 0 ∧
      u.gpr .r3 = 0 ∧ u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.allOnes 64) ?_ rfl)
    fun t₁ ⟨⟨m₁, x11, x7, x4, x5, x3, x0, x8⟩, k₁⟩ => ?_)
  · unfold scanInit
    prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.sl.out, hc.sl.k, e7,
      exec_addi (show Reg.r11 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide),
      exec_subi (show Reg.r7 ≠ .r0 by decide) (show 2 ≤ 2 ^ 15 by decide),
      exec_subi (show Reg.r8 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide)]
    exact ⟨rfl, rfl, rfl, by decide⟩
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  refine WP.mono (scanLoop_ok (O := s.gpr .r3) (EM := EM) (k := (s.gpr .r7).toNat) (by omega_using [hk64]) (by omega_using [hk])
    (fun i hi => by rw [← hc₁.em, bytes_getD' _ _ hi]) (fun i hi => outIn h hc₁ hi) x11 x7 x4 x5 x3 x0 x8)
    fun u ⟨um, ku, u5, u3⟩ => ⟨hl.amr.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁),
      by rw [ku.gpr _ (by decide), k₁.gpr _ (by decide), hl.al], u5, u3, by rw [ku.gpr _ (by decide), x0],
      by rw [ku.gpr _ (by decide), x8]⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the validity of the padding

The validity of the padding, the selected length and the mask of the
private-key operation's success (`validBlock_ok`), from the registers the
scan left.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero vOf lselOf outByte)

/-- `-(x = 0)`, for `x < 2 ^ 63`. -/
theorem zero_mask64 (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (0 : BitVec 64) - ((x - BitVec.ofNat 64 1) >>> 63) = bm (decide (x = 0)) := by
  by_cases h : x = 0
  · subst h; decide
  · have hb : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have e2 : (x - BitVec.ofNat 64 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hb]),
        BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega_using [hx]
    rw [e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

theorem ten_mask {sep : Nat} (h : sep < 2 ^ 63) :
    (0 : BitVec 64) - ((BitVec.ofNat 64 sep - BitVec.ofNat 64 10) >>> 63) = bm (decide (sep < 10)) := by
  rw [borrow _ _ h (by decide)]
  by_cases hs : sep < 10
  · simp only [show ¬ 10 ≤ sep by omega_using [hs], ↓reduceIte, bm, hs, decide_true]; decide
  · simp only [show 10 ≤ sep by omega_using [hs], ↓reduceIte, bm, hs, decide_false, Bool.false_eq_true]; decide

theorem bm_and (a b : Bool) : bm a &&& bm b = bm (a && b) := by
  cases a <;> cases b <;> rfl

theorem bm_not (a : Bool) : bm a ^^^ BitVec.allOnes 64 = bm (!a) := by
  cases a <;> decide

theorem sel_xor (x y : BitVec 64) (v : Bool) : x ^^^ ((y ^^^ x) &&& bm v) = if v then y else x := by
  cases v
  · simp [bm]
  · simp only [bm, ite_true, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem byte_zero (b : Byte) : decide (b.setWidth 64 = (0 : BitVec 64)) = decide (b = 0) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have : b.setWidth 64 ≠ 0 := fun e => hb (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this)
    simp only [this, h, decide_false]

theorem byte_two (b : Byte) :
    decide (b.setWidth 64 ^^^ BitVec.ofNat 64 2 = (0 : BitVec 64)) = decide (b = 2) := by
  rw [decide_eq_decide, show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro e
    have := congrArg (BitVec.setWidth 8) e
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · intro e; subst e; decide

theorem byte_lt (b : Byte) : (b.setWidth 64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))]
  exact Nat.lt_trans b.isLt (by decide)

theorem byte2_lt (b : Byte) : (b.setWidth 64 ^^^ BitVec.ofNat 64 2).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide)),
    BitVec.toNat_ofNat]
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 8) b.isLt (by decide)) (by decide)

theorem vOf_bm (a b : Byte) (f : Bool) (sep : Nat) :
    bm f &&& (bm (decide (a = 0)) &&& bm (decide (b = 2))) &&& bm (!decide (sep < 10)) = bm (vOf a b f sep) := by
  have e : (!decide (sep < 10)) = decide (10 ≤ sep) := by
    by_cases hs : sep < 10
    · simp only [hs, decide_true, Bool.not_true, show ¬ 10 ≤ sep by omega_using [hs], decide_false]
    · simp only [hs, decide_false, Bool.not_false, show 10 ≤ sep by omega_using [hs], decide_true]
  rw [bm_and, bm_and, bm_and, e]
  congr 1
  unfold vOf
  cases f <;> by_cases ha : a = 0 <;> by_cases hb : b = 2 <;> by_cases hs : 10 ≤ sep <;> simp [ha, hb, hs]

/-- `validBlock` from the load of `EM[1]` on. -/
def validRest : List Instr :=
  [.lbz .r9 .r11 1, .li .r4 2, .logic .xor .r9 .r9 .r4, .subi .r9 .r9 1, .lsr .d .r9 .r9 63,
    .sub .r9 .r0 .r9, .logic .and .r10 .r10 .r9, .logic .and .r5 .r5 .r10,
    .li .r4 10, .sub .r9 .r3 .r4, .lsr .d .r9 .r9 63, .sub .r9 .r0 .r9, .logic .xor .r9 .r9 .r8,
    .logic .and .r5 .r5 .r9,
    .sub .r9 .r7 .r3, .subi .r9 .r9 1, .logic .xor .r9 .r9 .r6, .logic .and .r9 .r9 .r5,
    .logic .xor .r6 .r6 .r9,
    .load .d .r4 .r12 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR, .li .r9 1, .logic .xor .r4 .r4 .r9, .subi .r4 .r4 1,
    .lsr .d .r4 .r4 63, .sub .r4 .r0 .r4,
    .sub .r3 .r7 .r6, .logic .and .r6 .r6 .r4]

/-- The block's results, from the registers the scan left. -/
theorem validBlock_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t)
    (h0 : InRegions (t.rd ++ t.wr) (s.gpr .r3 + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (s.gpr .r3 + BitVec.ofNat 64 1) 1)
    {f : Bool} {sep al : Nat} (h5 : t.gpr .r5 = bm f) (h3 : t.gpr .r3 = BitVec.ofNat 64 sep)
    (h6 : t.gpr .r6 = BitVec.ofNat 64 al) (h0' : t.gpr .r0 = 0) (h8 : t.gpr .r8 = BitVec.allOnes 64)
    (hsep : sep < 2 ^ 63) (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa (.block validBlock) t fun u => (u.mem = t.mem ∧ u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r7 = s.gpr .r7 ∧
      u.gpr .r5 = bm (vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep) ∧
      u.gpr .r4 = bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .r6 = (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep then
          s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) &&&
        bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .r3 = s.gpr .r7 - (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1))
          f sep then s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) ∧
      u.gpr .r12 = fb s) ∧
      Keep [.r12, .r11, .r7, .r10, .r9, .r4, .r5, .r6, .r3] t u := by
  have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c3 : Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR < 2 ^ 15 ∧ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR % 4 = 0 := by decide
  have i1 := slot_rd hc (d := oOut) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  have i3 := slot_rd hc (d := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) (by decide) (by decide)
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1' : (1 : Nat) < 2 ^ 15 := by decide
  rw [show validBlock = ([fp, .load .d .r11 .r12 oOut, .load .d .r7 .r12 oK, .lbz .r10 .r11 0, .subi .r10 .r10 1,
      .lsr .d .r10 .r10 63, .sub .r10 .r0 .r10] : List Instr) ++ validRest from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r11, .r7, .r10] (Q := fun u => u.mem = t.mem ∧
    u.gpr .r12 = fb s ∧ u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r7 = s.gpr .r7 ∧
    u.gpr .r10 = bm (decide (t.mem (s.gpr .r3 + BitVec.ofNat 64 0) = 0))) ?_ rfl) fun u ⟨⟨um, u12, u11, u7, u10⟩, ku⟩ => ?_
  · prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.sl.out, hc.sl.k, h0',
      exec_lbz (s := ((t.write .r12 (fb s)).write .r11 (s.gpr .r3)).write .r7 (s.gpr .r7))
        (show Reg.r11 ≠ .r0 by decide) c0 (by exact h0)]
    simp only [read1_64, zero_mask64 _ (byte_lt _), byte_zero]
  have u0 : u.gpr .r0 = 0 := (ku.gpr _ (by decide)).trans h0'
  have u3 : u.gpr .r3 = BitVec.ofNat 64 sep := (ku.gpr _ (by decide)).trans h3
  have u5 : u.gpr .r5 = bm f := (ku.gpr _ (by decide)).trans h5
  have u6 : u.gpr .r6 = BitVec.ofNat 64 al := (ku.gpr _ (by decide)).trans h6
  have u8 : u.gpr .r8 = BitVec.allOnes 64 := (ku.gpr _ (by decide)).trans h8
  have j1 : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 1) 1 := by rw [ku.rd, ku.wr, u11]; exact h1
  have j3 : InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 8 := by
    rw [ku.rd, ku.wr]; exact i3
  have hr : u.mem.readW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 64 = R := by rw [um]; exact hc.r
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r9, .r4, .r10, .r5, .r6, .r3] (Q := fun w => w.mem = u.mem ∧
    w.gpr .r5 = bm (vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep) ∧
    w.gpr .r4 = bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
    w.gpr .r6 = (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep then
        s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) &&&
      bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
    w.gpr .r3 = s.gpr .r7 - (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1))
        f sep then s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al)) ?_ rfl)
    fun w ⟨⟨wm, w5, w4, w6, w3⟩, kw⟩ => ⟨⟨wm.trans um, by rw [kw.gpr _ (by decide), u11],
      by rw [kw.gpr _ (by decide), u7], w5, w4, w6, w3, by rw [kw.gpr _ (by decide), u12]⟩,
      (ku.mono (by decide)).trans' (kw.mono (by decide))⟩
  · unfold validRest
    prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c1' j1, u0, u3, u5, u6, u7, u8, u10, u11, u12, c3, j3, hr]
    simp only [read1_64, zero_mask64 _ (byte2_lt _), zero_mask64 _ hR, ten_mask hsep, bm_not, byte_two, um,
      vOf_bm, sel_xor]
    exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end

/-! ### `RsaPkcs1Enc.PPC64LE.DecOut`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: writing the output

`*msg_len` (`outInit`) and the output, byte by byte (`selBody_ok`,
`selLoop_ok`): byte `i` of `out` is `outByte v ok kl i EM[i] AM[i]`; then the
result and our return address (`selPart_ok`, into `Fin`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

variable {pc : Bool}

/-- After the private-key operation's output is read: the frame, the slots
and the result `R` in its slot, memory changed only in our stack, `out`,
`*msg_len` and `scratch`. -/
structure Fr3 (s : State) (R : BitVec 64) (u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  hi : ∀ r ∈ preserved, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, mlR s, sR s] s.mem u.mem
  sl : Slots s u.mem
  r : u.mem.readW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 64 = R

theorem Post.fr3 {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t) : Fr3 s R t :=
  ⟨hc.sp, hc.rd, hc.wr, hc.hi, hc.mem.sub fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩, hc.sl, hc.r⟩

/-- A store to `out` or `*msg_len`. -/
theorem Fr3.store {s : State} (h : DPre pc s) {R : BitVec 64} {t u : State} (hc : Fr3 s R t) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) (hsp : u.sp = t.sp) (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) {X : Region}
    (hX : X = oR s ∨ X = mlR s) {Y : Region} (hY : Region.Sub Y X) (hf : Frame [Y] t.mem u.mem) :
    Fr3 s R u := by
  have hk : Region.Disjoint (kR s) Y := by
    rcases hX with rfl | rfl
    · exact h.ko.sub_right hY
    · exact h.km.sub_right hY
  refine ⟨hsp.trans hc.sp, hrd.trans hc.rd, hwr.trans hc.wr, fun r hr => (hg r hr).trans (hc.hi r hr),
    hc.mem.trans (hf.sub fun r hr => ?_), hc.sl.words hf fun r hr d _ hn => ?_, ?_⟩
  · rw [List.mem_singleton.mp hr]
    rcases hX with rfl | rfl
    · exact ⟨_, by simp, hY⟩
    · exact ⟨_, by simp, hY⟩
  · rw [List.mem_singleton.mp hr]; exact hk.sub_left (frame_sub s hn)
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hk.sub_left (frame_sub s (by decide))) (by decide)]
    exact hc.r

/-! ## A byte of the output -/

/-- The first part of `selBody`: the byte, in `r6`. -/
def selA : List Instr :=
  [.lbz .r6 .r11 0, .lbz .r12 .r10 0, .logic .xor .r6 .r6 .r12, .logic .and .r6 .r6 .r5,
    .logic .xor .r6 .r6 .r12, .sub .r12 .r9 .r3, .lsr .d .r12 .r12 63, .sub .r12 .r0 .r12,
    .logic .xor .r12 .r12 .r8, .logic .and .r12 .r12 .r4, .logic .and .r6 .r6 .r12]

/-- The rest: its store, and the pointers and counter advanced. -/
def selB : List Instr :=
  [.stb .r6 .r11 0, .addi .r9 .r9 1, .addi .r11 .r11 1, .addi .r10 .r10 1, .subi .r7 .r7 1]

theorem selBody_eq : selBody = selA ++ selB := rfl

theorem outB_eq (v ok : Bool) {kl i : Nat} (hkl : kl < 2 ^ 63) (hi : i < 2 ^ 63) (e a : Byte) :
    ((((e.setWidth 64 ^^^ a.setWidth 64) &&& bm v) ^^^ a.setWidth 64) &&&
      ((((0 : BitVec 64) - ((BitVec.ofNat 64 i - BitVec.ofNat 64 kl) >>> 63)) ^^^ BitVec.allOnes 64) &&& bm ok)).setWidth 8 =
      outByte v ok kl i e a := by
  have sel : ((e.setWidth 64 ^^^ a.setWidth 64) &&& bm v) ^^^ a.setWidth 64 = (if v then e else a).setWidth 64 := by
    cases v
    · simp [bm]
    · simp only [bm, ite_true, BitVec.and_allOnes]
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [sel, borrow _ _ hi hkl]
  simp only [outByte]
  by_cases hk : kl ≤ i
  · cases ok
    · simp only [hk, ↓reduceIte, bm, Bool.false_eq_true, and_false]
      apply BitVec.eq_of_toNat_eq; simp
    · simp only [hk, ↓reduceIte, bm, and_self]
      rw [show ((0 : BitVec 64) - BitVec.ofNat 64 0) ^^^ BitVec.allOnes 64 = BitVec.allOnes 64 by decide,
        BitVec.and_allOnes, BitVec.and_allOnes, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · simp only [hk, ↓reduceIte, false_and]
    rw [show ((0 : BitVec 64) - BitVec.ofNat 64 1) ^^^ BitVec.allOnes 64 = 0 by decide]
    apply BitVec.eq_of_toNat_eq; simp

theorem selA_ok {t : State} (he : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1)
    (ha : InRegions (t.rd ++ t.wr) (t.gpr .r10 + BitVec.ofNat 64 0) 1) (h0 : t.gpr .r0 = 0) :
    WP isa (.block selA) t fun u => (u.mem = t.mem ∧
      u.gpr .r6 = ((((t.mem (t.gpr .r11 + BitVec.ofNat 64 0)).setWidth 64 ^^^
          (t.mem (t.gpr .r10 + BitVec.ofNat 64 0)).setWidth 64) &&& t.gpr .r5) ^^^
          (t.mem (t.gpr .r10 + BitVec.ofNat 64 0)).setWidth 64) &&&
        ((((0 : BitVec 64) - ((t.gpr .r9 - t.gpr .r3) >>> 63)) ^^^ t.gpr .r8) &&& t.gpr .r4)) ∧
      Keep [.r6, .r12] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  unfold selA
  prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c0 he,
    exec_lbz (s := t.write .r6 ((t.mem.read (t.gpr .r11 + BitVec.ofNat 64 0) 1).setWidth 64))
      (show Reg.r10 ≠ .r0 by decide) c0 (by exact ha), h0]
  simp only [read1_64]

theorem selB_ok {t : State} (hw : InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block selB) t fun u => (u.mem = t.mem.write (t.gpr .r11 + BitVec.ofNat 64 0) 1 ((t.gpr .r6).setWidth 8) ∧
      u.gpr .r9 = t.gpr .r9 + BitVec.ofNat 64 1 ∧ u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 1 ∧
      u.gpr .r10 = t.gpr .r10 + BitVec.ofNat 64 1 ∧ u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1) ∧
      Keep [.r9, .r11, .r10, .r7] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  unfold selB
  prun [exec_stb (show Reg.r11 ≠ .r0 by decide) c0 hw, exec_addi (show Reg.r9 ≠ .r0 by decide) c1,
    exec_addi (show Reg.r11 ≠ .r0 by decide) c1, exec_addi (show Reg.r10 ≠ .r0 by decide) c1]

/-! ## The loop -/

/-- After `i` bytes of the output. -/
structure OInv (s : State) (R MLV : BitVec 64) (EM AM : List Byte) (v ok : Bool) (kl : Nat) (i : Nat) (t : State) :
    Prop where
  fr : Fr3 s R t
  ml : t.mem.readW (s.gpr .r5) 64 = MLV
  r9 : t.gpr .r9 = BitVec.ofNat 64 i
  r11 : t.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 i
  r10 : t.gpr .r10 = scA s sAM + BitVec.ofNat 64 i
  r4 : t.gpr .r4 = bm ok
  r5 : t.gpr .r5 = bm v
  r3 : t.gpr .r3 = BitVec.ofNat 64 kl
  r0 : t.gpr .r0 = 0
  r8 : t.gpr .r8 = BitVec.allOnes 64
  done : ∀ j < i, t.mem (s.gpr .r3 + BitVec.ofNat 64 j) = outByte v ok kl j (EM.getD j 1) (AM.getD j 0)
  todo : ∀ j, i ≤ j → j < (s.gpr .r7).toNat → t.mem (s.gpr .r3 + BitVec.ofNat 64 j) = EM.getD j 1
  am : ∀ j < (s.gpr .r7).toNat, t.mem (scA s sAM + BitVec.ofNat 64 j) = AM.getD j 0

section
variable {s : State} (h : DPre pc s)
include h

theorem outW {t : State} (hwr : t.wr = fr s :: s.wr) {i : Nat} (hi : i < (s.gpr .r7).toNat) :
    InRegions t.wr (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h4] at this
  exact ⟨oR s, by rw [hwr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem selLoop_ok {R MLV : BitVec 64} {EM AM : List Byte} {v ok : Bool} {kl : Nat}
    (hkl : kl < 2 ^ 63) {t : State} (h0 : OInv s R MLV EM AM v ok kl 0 t) (h7 : t.gpr .r7 = s.gpr .r7) :
    WP isa selLoop t (OInv s R MLV EM AM v ok kl (s.gpr .r7).toNat) := by
  have hk := h.k2
  have hk64 := h.k1
  have hwo := h.wo
  rw [h.h4] at hwo
  have := h.ws; have := scr_le h
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (by omega_using []) (by omega_using [hk64]) (OInv s R MLV EM AM v ok kl)
    (fun i hi u hu _ => ?_) h0 (by rw [h7, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hc := hu.fr
  have he : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r11, BitVec.add_zero]
    obtain ⟨r, hr, hcr⟩ := outW h hc.wr hi
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .r10 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r10, BitVec.add_zero, Offset.add_add]
    exact scInR h hc.wr (a := sAM + i) (n := 1) (by unfold sAM scrBytes; omega_using [hk, hi])
  rw [selBody_eq, WP.block_append_iff]
  refine WP.mono (selA_ok he ha hu.r0) fun w ⟨⟨wm, w6⟩, kw⟩ => ?_
  have hw : InRegions w.wr (w.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [kw.wr, kw.gpr _ (by decide), hu.r11, BitVec.add_zero]; exact outW h hc.wr hi
  refine WP.mono (selB_ok hw) fun x ⟨⟨xm, x9, x11, x10, x7⟩, kx⟩ => ⟨?_, ?_⟩
  · have hb : (w.gpr .r6).setWidth 8 = outByte v ok kl i (EM.getD i 1) (AM.getD i 0) := by
      rw [w6, hu.r5, hu.r4, hu.r9, hu.r3, hu.r8, hu.r11, hu.r10, BitVec.add_zero, BitVec.add_zero,
        hu.todo i (Nat.le_refl _) hi, hu.am i hi, outB_eq _ _ hkl (by omega_using [hk, hi])]
    rw [hb, kw.gpr _ (by decide), hu.r11, BitVec.add_zero, wm] at xm
    have hf : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩] u.mem x.mem := by
      rw [xm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hsub : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩ (oR s) := by
      rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]; exact Offset.sub_base _ (by omega_using [hi])
    have hne : ∀ j, j ≠ i → j < (s.gpr .r7).toNat → s.gpr .r3 + BitVec.ofNat 64 j ≠ s.gpr .r3 + BitVec.ofNat 64 i :=
      fun j hj hjk => Offset.add_ofNat_ne _ (by omega_using [hjk]) (by omega_using [hi]) hj
    have kk : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] u x :=
      (kw.mono (by decide)).trans' (kx.mono (by decide))
    have g : ∀ r, r ∉ [Reg.r9, .r11, .r10, .r7] → r ∉ [Reg.r6, .r12] → x.gpr r = u.gpr r := fun r h₁ h₂ =>
      (kx.gpr r h₁).trans (kw.gpr r h₂)
    refine ⟨hc.store h kk.rd kk.wr kk.sp (fun r hr => kk.gpr r (by revert r; decide)) (.inl rfl) hsub hf, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun X hX => by
        rw [List.mem_singleton.mp hX]; exact (h.om.sub_left hsub).symm) (by decide), hu.ml]
    · rw [x9, kw.gpr _ (by decide), hu.r9, ← BitVec.ofNat_add]
    · rw [x11, kw.gpr _ (by decide), hu.r11, Offset.add_add]
    · rw [x10, kw.gpr _ (by decide), hu.r10, Offset.add_add]
    · rw [g _ (by decide) (by decide), hu.r4]
    · rw [g _ (by decide) (by decide), hu.r5]
    · rw [g _ (by decide) (by decide), hu.r3]
    · rw [g _ (by decide) (by decide), hu.r0]
    · rw [g _ (by decide) (by decide), hu.r8]
    · intro j hj
      rw [xm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [write1_ne' _ _ (hne j (by omega_using [hj]) (by omega_arith)), hu.done j hj]
      · exact VG.Proof.Bignum.PPC64LE.write1_self _ _ _
    · intro j hj hjk
      rw [xm, write1_ne' _ _ (hne j (by omega_using [hj]) hjk), hu.todo j (by omega_using [hj]) hjk]
    · intro j hj
      rw [hf.bytes (R := ⟨scA s sAM, (s.gpr .r7).toNat⟩) (fun X hX => by
        rw [List.mem_singleton.mp hX]
        exact ((h.os.sub_left hsub).sub_right (sc_sub h)).symm.sub_left (scSub (by unfold sAM scrBytes; omega_using [hk])))
        (by show (s.gpr .r7).toNat ≤ 2 ^ 64; omega_using []) hj, hu.am j hj]
  · rw [x7, kw.gpr _ (by decide)]

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the selection

The validity and `*msg_len` (`selInit_ok`), the output's loop, and the
result and our return address (`finish_ok`): `selPart_ok`, from `SCN` to
`Fin`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

variable {pc : Bool}

/-- `AM`. -/
abbrev amOf (s : State) (kd : List Byte) : List Byte :=
  Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .r7).toNat

/-- The validity of `EM`, as the scan found it. -/
abbrev vOfEM (s : State) (EM : List Byte) : Bool := Proof.RsaPkcs1Enc.vEM EM (s.gpr .r7).toNat

/-- The selected length. -/
abbrev lenOf (s : State) (EM : List Byte) (kd : List Byte) : Nat :=
  Proof.RsaPkcs1Enc.lselOf (vOfEM s EM) ((firstZero EM (s.gpr .r7).toNat).getD 0)
    (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd)) (s.gpr .r7).toNat

theorem sep_lt (EM : List Byte) {k : Nat} (hk : 0 < k) : (firstZero EM k).getD 0 < k := by
  cases h : firstZero EM k with
  | none => simp; omega_using [hk]
  | some i => exact (Proof.RsaPkcs1Enc.firstZero_some h).2.1

/-- At the end of the body: the output and `*msg_len` written, the result in
`r3` and our return address in the link register. -/
structure Fin (s : State) (R : BitVec 64) (EM AM : List Byte) (v ok : Bool) (len : Nat) (u : State) : Prop
    extends Fr3 s R u where
  r3 : u.gpr .r3 = R
  lr : u.lr = s.lr
  out : ∀ i < (s.gpr .r7).toNat, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
    outByte v ok ((s.gpr .r7).toNat - len) i (EM.getD i 1) (AM.getD i 0)
  ml : u.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 len &&& bm ok

section
variable {s : State} (h : DPre pc s) {R : BitVec 64}
include h

theorem outInit_ok {t : State} (hc : Fr3 s R t) (h12 : t.gpr .r12 = fb s) :
    WP isa (.block outInit) t fun u => (u.mem = t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) (t.gpr .r6) ∧
      u.gpr .r10 = scA s sAM ∧ u.gpr .r9 = 0) ∧ Keep [.r10, .r9] t u := by
  have c1 : oML < 2 ^ 15 ∧ oML % 4 = 0 := by decide
  have c2 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c3 : sAM < 2 ^ 15 := by decide
  have i1 := slotIn (u := t) hc.wr (d := oML) (by decide) (by decide)
  have i2 := slotIn (u := t) hc.wr (d := oScr) (by decide) (by decide)
  have hw : InRegions t.wr (s.gpr .r5 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, hc.wr, h.hwr]; exact ⟨mlR s, by simp, Region.contains_self _ _⟩
  have rS : ∀ v : BitVec 64, (t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) v).readW (fb s + BitVec.ofNat 64 oScr) 64 =
      stackArg s 13 := fun v => by
    have hf : Frame [mlR s] t.mem (t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by rw [BitVec.add_zero]; exact Region.contains_self _ _)
    rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.km.sub_left (frame_sub s (by decide))) (by decide)]
    exact hc.sl.scr
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold outInit scr
  prun [h12, c1, c2, c3, i1, i2, hc.sl.ml, hw, rS, exec_addi (show Reg.r10 ≠ .r0 by decide) c3]
  rfl

omit h in
theorem finish_ok {t : State} (hc : Fr3 s R t) :
    WP isa (.block finish) t fun u => u.gpr .r3 = R ∧ u.lr = s.lr ∧ u.mem = t.mem ∧ u.sp = t.sp ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  have c1 : Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR < 2 ^ 15 ∧ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR % 4 = 0 := by decide
  have c2 : oLr < 2 ^ 15 ∧ oLr % 4 = 0 := by decide
  have i1 := slotIn (u := t) hc.wr (d := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) (by decide) (by decide)
  have i2 := slotIn (u := t) hc.wr (d := oLr) (by decide) (by decide)
  unfold finish
  prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.r, hc.sl.lr, exec_mtlr]
  intro r hr
  have : r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r12 := by revert r; decide
  simp only [this, ↓reduceIte]

/-- The selection: the validity, `*msg_len`, the output and the end. -/
theorem selPart_ok {EM kd : List Byte} {t : State} (hs : SCN s R EM kd t)
    (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa selPart t (Fin s R EM (amOf s kd) (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) (lenOf s EM kd)) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hs.amr.post
  have hsep := sep_lt EM (k := (s.gpr .r7).toNat) (by omega_using [hk64])
  have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .r7).toNat (clOf kd)
  refine WP.seq (WP.mono (validBlock_ok hc (outIn h hc (by omega_using [hk64])) (outIn h hc (by omega_using [hk64])) hs.r5 hs.r3 hs.al hs.r0 hs.r8
    (by omega_using [hk, hsep]) hR) fun t₁ ⟨⟨m₁, x11, x7, x5, x4, x6, x3, x12⟩, k₁⟩ => ?_)
  -- The values the block computed.
  have e0 : t.mem (s.gpr .r3 + BitVec.ofNat 64 0) = EM.getD 0 1 := by rw [← hc.em, bytes_getD' _ _ (by omega_using [hk64])]
  have e1 : t.mem (s.gpr .r3 + BitVec.ofNat 64 1) = EM.getD 1 1 := by rw [← hc.em, bytes_getD' _ _ (by omega_using [hk64])]
  have eL : (if Proof.RsaPkcs1Enc.vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM (s.gpr .r7).toNat).isSome
      ((firstZero EM (s.gpr .r7).toNat).getD 0) then s.gpr .r7 - BitVec.ofNat 64 ((firstZero EM (s.gpr .r7).toNat).getD 0) -
        BitVec.ofNat 64 1 else BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))) =
      BitVec.ofNat 64 (lenOf s EM kd) := by
    simp only [lenOf, vOfEM, Proof.RsaPkcs1Enc.vEM, Proof.RsaPkcs1Enc.lselOf]
    split
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsep]), BitVec.toNat_ofNat]; omega_using [hsep]),
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsep]), BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [hsep]
    · rfl
  have hlen : lenOf s EM kd ≤ (s.gpr .r7).toNat := by
    simp only [lenOf, Proof.RsaPkcs1Enc.lselOf]; split <;> omega_arith
  simp only [e0, e1] at x5 x6 x3
  rw [eL] at x6 x3
  rw [show s.gpr .r7 - BitVec.ofNat 64 (lenOf s EM kd) = BitVec.ofNat 64 ((s.gpr .r7).toNat - lenOf s EM kd) by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hlen]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega_using [hlen]] at x3
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  -- `*msg_len`.
  refine WP.seq (WP.mono (outInit_ok h hc₁.fr3 x12) fun t₂ ⟨⟨m₂, x10, x9⟩, k₂⟩ => ?_)
  rw [x6] at m₂
  have hY : Region.Sub ⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩ (mlR s) := by rw [BitVec.add_zero]; exact fun _ h => h
  have F₂ : Frame [⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₂ : Fr3 s R t₂ := hc₁.fr3.store h k₂.rd k₂.wr k₂.sp (fun r hr => k₂.gpr r (by revert r; decide)) (.inr rfl) hY F₂
  have bk : ∀ (X : Region), X.Disjoint (mlR s) → X.len ≤ 2 ^ 64 → ∀ i < X.len,
      t₂.mem (X.base + BitVec.ofNat 64 i) = t.mem (X.base + BitVec.ofNat 64 i) := fun X hX hl i hi => by
    rw [F₂.bytes (fun Y hY' => by rw [List.mem_singleton.mp hY']; exact hX.sub_right hY) hl hi, m₁]
  have hwo := h.wo; have h4 := h.h4
  have g : ∀ r, r ∉ [Reg.r10, .r9] → r ∉ [Reg.r12, .r11, .r7, .r10, .r9, .r4, .r5, .r6, .r3] → t₂.gpr r = t.gpr r :=
    fun r h₁ h₂ => (k₂.gpr r h₁).trans (k₁.gpr r h₂)
  have h0 : OInv s R (BitVec.ofNat 64 (lenOf s EM kd) &&& bm (decide (R ^^^ BitVec.ofNat 64 1 = 0))) EM (amOf s kd)
      (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ((s.gpr .r7).toNat - lenOf s EM kd) 0 t₂ :=
    { fr := hc₂
      ml := by rw [m₂, BitVec.add_zero, Mem.readW_writeW_self64]
      r9 := by rw [x9]; rfl
      r11 := by rw [k₂.gpr _ (by decide), x11, BitVec.add_zero]
      r10 := by rw [x10, BitVec.add_zero]
      r4 := by rw [k₂.gpr _ (by decide), x4]
      r5 := by rw [k₂.gpr _ (by decide), x5]
      r3 := by rw [k₂.gpr _ (by decide), x3]
      r0 := by rw [g _ (by decide) (by decide), hs.r0]
      r8 := by rw [g _ (by decide) (by decide), hs.r8]
      done := fun j hj => absurd hj (Nat.not_lt_zero _)
      todo := fun j _ hj => by
        rw [show s.gpr .r3 = (oR s).base from rfl, bk (oR s) h.om (by show (s.gpr .r4).toNat ≤ 2 ^ 64; omega_using []) j
          (by show j < (s.gpr .r4).toNat; omega_using [h4, hj]), show (oR s).base = s.gpr .r3 from rfl, ← hc.em, bytes_getD' _ _ hj]
      am := fun j hj => by
        rw [show scA s sAM = (⟨scA s sAM, (s.gpr .r7).toNat⟩ : Region).base from rfl,
          bk ⟨scA s sAM, (s.gpr .r7).toNat⟩ ((h.ms.symm.sub_left (sub_trans (scSub (by unfold sAM scrBytes; omega_using [hk]))
            (sc_sub h)))) (by show (s.gpr .r7).toNat ≤ 2 ^ 64; omega_using []) j hj]
        have ham : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .r7).toNat = amOf s kd := hs.amr.am
        rw [← ham, bytes_getD' _ _ hj] }
  refine WP.seq (WP.mono (selLoop_ok h (by omega_using [hk]) h0 (by rw [k₂.gpr _ (by decide), x7])) fun t₃ h₃ => ?_)
  refine WP.mono (finish_ok h₃.fr) fun u ⟨u3, ul, um, usp, urd, uwr, uh⟩ => ?_
  have hc₃ := h₃.fr
  exact ⟨⟨usp.trans hc₃.sp, urd.trans hc₃.rd, uwr.trans hc₃.wr, fun r hr => (uh r hr).trans (hc₃.hi r hr),
    um ▸ hc₃.mem, um ▸ hc₃.sl, um ▸ hc₃.r⟩, u3, ul, fun i hi => by rw [um]; exact h₃.done i hi,
    by rw [um]; exact h₃.ml⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time from the mask on

The mask, the alternative length, the scan and the output, by the taint
analysis from the registers correctness fixes; the blocks that load a
pointer from a slot and use it are split there (`rel_split`). With the
earlier parts, the function (`code_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (bitMask)

variable {pc : Bool}

section
variable {e : Env pc}

/-- A block split where a pointer it loads is used: the first part's taint
from `rs₁`, the second's from `rs₂`, which `X` fixes. -/
theorem rel_split {P Q X : State → State → Prop} {l₁ l₂ : List Instr} (rs₁ rs₂ : List Reg)
    {hc₁ : VG.Taint.Hint T} (ht₁ : (taint.check (ofRegs rs₁) (.block l₁) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint T} (ht₂ : (taint.check (ofRegs rs₂) (.block l₂) hc₂).isSome = true)
    (hpin₁ : ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs₁ a b) (hpin₂ : ∀ a b, X e.s₁ a → X e.s₂ b → AgreeOn rs₂ a b)
    (hw₁ : ∀ s u, DPre pc s → P s u → WP isa (.block l₁) u (X s))
    (hw : ∀ s u, DPre pc s → P s u → WP isa (.block (l₁ ++ l₂)) u (Q s)) :
    RelCT isa (Rel e P) (.block (l₁ ++ l₂)) (Rel e Q) :=
  RelCT.block_append (RelCT.seq
    (rel_step (P' := fun s u => X s u ∧ WP isa (.block l₂) u (Q s)) rs₁ ht₁ hpin₁
      fun s u h hu => WP.and (hw₁ s u h hu) (WP.block_append_iff.mp (hw s u h hu)))
    (rel_step rs₂ ht₂ (fun a b ha hb => hpin₂ a b ha.1 hb.1) fun _ _ _ hu => hu.2))

/-! ## The mask and the alternative length -/

def PM (s u : State) : Prop := PP s u ∧ u.gpr .r9 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11) ∧
  u.gpr .r8 = BitVec.ofNat 64 0
def PMK (s u : State) : Prop := PP s u ∧ u.gpr .r8 = BitVec.ofNat 64 (bitMask ((s.gpr .r7).toNat - 11)) ∧
  u.gpr .r9 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11)
def PA (s u : State) : Prop := PMK s u ∧ u.gpr .r11 = scA s sCL ∧ u.gpr .r7 = BitVec.ofNat 64 128 ∧
  u.gpr .r6 = BitVec.ofNat 64 0
def PAL (s u : State) : Prop := PP s u ∧ ∃ al, u.gpr .r6 = BitVec.ofNat 64 al

omit e in
theorem k11 {s : State} (h : DPre pc s) : s.gpr .r7 - BitVec.ofNat 64 11 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11) := by
  have := h.k1; have := h.k2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]

theorem maskPart_ct : RelCT isa (Rel e PP) maskPart (Rel e PMK) := by
  unfold maskPart
  refine RelCT.seq (rel_step (P' := PM) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h hu => WP.mono (pp_block hu [.r12, .r9, .r8] (X := fun v => v.gpr .r9 = s.gpr .r7 - BitVec.ofNat 64 11 ∧
      v.gpr .r8 = BitVec.ofNat 64 0) fun _ _ hc => by
        have c1 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
        have i1 := slot_rd hc (d := oK) (by decide) (by decide)
        refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
        unfold maskInit
        prun [fp, exec_addSp0, hc.sp, c1, i1, hc.sl.k])
      fun v ⟨hv, _, x9, x8⟩ => ⟨hv, by rw [x9, k11 h], x8⟩) ?_
  refine rel_step [.r8, .r9] (by taint_decide) (fun a b ⟨ha, a9, a8⟩ ⟨hb, b9, b8⟩ => ⟨pp_sp ha hb, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a8, b8]
    · rw [a9, b9, e.r]⟩) fun s u h ⟨⟨R, EM, hu⟩, u9, u8⟩ => ?_
  have hk := h.k1; have hk' := h.k2
  exact WP.mono (maskLoop_ok (x := (s.gpr .r7).toNat - 11) (by omega_using [hk]) (by omega_using [hk']) u8 u9) fun v ⟨vm, kv, v8⟩ =>
    ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩, v8,
      (kv.gpr _ (by decide)).trans u9⟩

theorem alPart_ct : RelCT isa (Rel e PMK) alPart (Rel e PAL) := by
  unfold alPart
  refine RelCT.seq (rel_step (P' := PA) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha.1 hb.1, fun _ h => nomatch h⟩)
    fun s u h ⟨hu, u8, u9⟩ => WP.mono (pp_block hu [.r12, .r11, .r7, .r6] (X := fun v => v.gpr .r11 = scA s sCL ∧
      v.gpr .r7 = BitVec.ofNat 64 128 ∧ v.gpr .r6 = BitVec.ofNat 64 0 ∧ v.gpr .r8 = u.gpr .r8 ∧
      v.gpr .r9 = u.gpr .r9) fun _ _ hc => by
        have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
        have c2 : sCL < 2 ^ 15 := by decide
        have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
        refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
        unfold alInit scr
        prun [fp, exec_addSp0, hc.sp, c1, c2, i1, hc.sl.scr, exec_addi (show Reg.r11 ≠ .r0 by decide) c2])
      fun v ⟨hv, _, x11, x7, x6, x8, x9⟩ => ⟨⟨hv, by rw [x8, u8], by rw [x9, u9]⟩, x11, x7, x6⟩) ?_
  refine rel_step [.r11, .r7] (by taint_decide) (fun a b ⟨⟨ha, _⟩, a11, a7, _⟩ ⟨⟨hb, _⟩, b11, b7, _⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a11, b11, e.scA_eq]
      · rw [a7, b7]⟩) fun s u h ⟨⟨⟨R, EM, hu⟩, u8, u9⟩, u11, u7, u6⟩ => ?_
  have hk := h.k1; have hk' := h.k2
  have hM := Proof.RsaPkcs1Enc.bitMask_le (x := (s.gpr .r7).toNat - 11) (by omega_using [hk])
  exact WP.mono (alLoop_ok (x := (s.gpr .r7).toNat - 11) (CL := Spec.Rsa.bytesAt u.mem (scA s sCL) 256)
    (by omega_using [hk']) rfl (by omega_using [hk', hM]) (fun i hi => (bytes_getD _ _ hi).symm)
    (fun i hi => by rw [Offset.add_add]; exact scInR h hu.wr (a := sCL + i) (n := 1) (by unfold sCL scrBytes; omega_using [hi]))
    u8 u9 u11 u7 u6) fun v ⟨vm, kv, v6⟩ =>
    ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩, _, v6⟩

/-! ## The scan -/

def PSI (s u : State) : Prop := PAL s u ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 2 ∧
  u.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) ∧ u.gpr .r4 = BitVec.ofNat 64 2 ∧ u.gpr .r5 = 0 ∧
  u.gpr .r3 = 0 ∧ u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.allOnes 64
def PSC (s u : State) : Prop := PP s u ∧ (∃ al, u.gpr .r6 = BitVec.ofNat 64 al) ∧ (∃ f, u.gpr .r5 = bm f) ∧
  (∃ sep, u.gpr .r3 = BitVec.ofNat 64 sep ∧ sep < 2 ^ 63) ∧ u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.allOnes 64

omit e in
theorem k2' {s : State} (h : DPre pc s) : s.gpr .r7 - BitVec.ofNat 64 2 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) := by
  have := h.k1; have := h.k2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]

theorem scanPart_ct : RelCT isa (Rel e PAL) scanPart (Rel e PSC) := by
  unfold scanPart
  refine RelCT.seq (rel_step (P' := PSI) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha.1 hb.1, fun _ h => nomatch h⟩)
    fun s u h ⟨hu, al, u6⟩ => WP.mono (pp_block hu [.r12, .r11, .r7, .r4, .r5, .r3, .r0, .r8]
      (X := fun v => v.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 2 ∧
        v.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) ∧ v.gpr .r4 = BitVec.ofNat 64 2 ∧ v.gpr .r5 = 0 ∧
        v.gpr .r3 = 0 ∧ v.gpr .r0 = 0 ∧ v.gpr .r8 = BitVec.allOnes 64 ∧ v.gpr .r6 = u.gpr .r6) fun _ _ hc => by
        have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
        have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
        have i1 := slot_rd hc (d := oOut) (by decide) (by decide)
        have i2 := slot_rd hc (d := oK) (by decide) (by decide)
        have e7 := k2' h
        refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
        unfold scanInit
        prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.sl.out, hc.sl.k, e7,
          exec_addi (show Reg.r11 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide),
          exec_subi (show Reg.r7 ≠ .r0 by decide) (show 2 ≤ 2 ^ 15 by decide),
          exec_subi (show Reg.r8 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide)]
        exact ⟨rfl, rfl, rfl, by decide⟩)
      fun v ⟨hv, _, x11, x7, x4, x5, x3, x0, x8, x6⟩ => ⟨⟨hv, al, by rw [x6, u6]⟩, x11, x7, x4, x5, x3, x0, x8⟩) ?_
  refine rel_step [.r11, .r7] (by taint_decide) (fun a b ⟨⟨ha, _⟩, a11, a7, _⟩ ⟨⟨hb, _⟩, b11, b7, _⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a11, b11, e.r]
      · rw [a7, b7, e.r]⟩) fun s u h ⟨⟨⟨R, EM, hu⟩, al, u6⟩, u11, u7, u4, u5, u3, u0, u8⟩ => ?_
  have hk := h.k1; have hk' := h.k2
  have hs := sep_lt (Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat) (k := (s.gpr .r7).toNat) (by omega_using [hk])
  exact WP.mono (scanLoop_ok (O := s.gpr .r3) (EM := Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat)
    (k := (s.gpr .r7).toNat) (by omega_using [hk]) (by omega_using [hk']) (fun i hi => (bytes_getD' _ _ hi _).symm)
    (fun i hi => outIn h hu hi) u11 u7 u4 u5 u3 u0 u8) fun v ⟨vm, kv, v5, v3⟩ =>
    ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩,
      ⟨al, by rw [kv.gpr _ (by decide), u6]⟩, ⟨_, v5⟩,
      ⟨_, v3, by omega_using [hk', hs]⟩,
      by rw [kv.gpr _ (by decide), u0], by rw [kv.gpr _ (by decide), u8]⟩

/-! ## The output -/

def PV (s u : State) : Prop := PP s u ∧ u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r7 = s.gpr .r7 ∧ u.gpr .r12 = fb s ∧
  u.gpr .r0 = 0
def PO (s u : State) : Prop := (∃ R, Fr3 s R u) ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 0 ∧
  u.gpr .r10 = scA s sAM + BitVec.ofNat 64 0 ∧ u.gpr .r7 = s.gpr .r7 ∧ u.gpr .r0 = 0

omit e in
theorem selLoop_run {s : State} (h : DPre pc s) {R : BitVec 64} {t : State} (hc : Fr3 s R t)
    (h11 : t.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 0) (h10 : t.gpr .r10 = scA s sAM + BitVec.ofNat 64 0)
    (h7 : t.gpr .r7 = s.gpr .r7) (h0 : t.gpr .r0 = 0) : WP isa selLoop t fun u => Fr3 s R u := by
  have hk := h.k2
  have hk64 := h.k1
  have := h.ws; have := scr_le h
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (N := (s.gpr .r7).toNat) (by omega_using []) (by omega_using [hk64])
    (fun j u => Fr3 s R u ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 j ∧ u.gpr .r10 = scA s sAM + BitVec.ofNat 64 j ∧
      u.gpr .r0 = 0) (fun i hi u ⟨hu, u11, u10, u0⟩ _ => ?_) ⟨hc, h11, h10, h0⟩
    (by rw [h7, BitVec.ofNat_toNat, BitVec.setWidth_eq])) fun u hu => hu.1
  have he : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [u11, BitVec.add_zero]
    obtain ⟨r, hr, hcr⟩ := outW h hu.wr hi
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .r10 + BitVec.ofNat 64 0) 1 := by
    rw [u10, BitVec.add_zero, Offset.add_add]
    exact scInR h hu.wr (a := sAM + i) (n := 1) (by unfold sAM scrBytes; omega_using [hk, hi])
  rw [selBody_eq, WP.block_append_iff]
  refine WP.mono (selA_ok he ha u0) fun w ⟨⟨wm, _⟩, kw⟩ => ?_
  have hw : InRegions w.wr (w.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [kw.wr, kw.gpr _ (by decide), u11, BitVec.add_zero]; exact outW h hu.wr hi
  refine WP.mono (selB_ok hw) fun x ⟨⟨xm, _, x11, x10, x7⟩, kx⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kw.gpr _ (by decide), u11, BitVec.add_zero, wm] at xm
    have hf : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩] u.mem x.mem := by
      rw [xm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hwo := h.wo; rw [h.h4] at hwo
    have hsub : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩ (oR s) := by
      rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]; exact Offset.sub_base _ (by omega_using [hi])
    have kk : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] u x :=
      (kw.mono (by decide)).trans' (kx.mono (by decide))
    exact hu.store h kk.rd kk.wr kk.sp (fun r hr => kk.gpr r (by revert r; decide)) (.inl rfl) hsub hf
  · rw [x11, kw.gpr _ (by decide), u11, Offset.add_add]
  · rw [x10, kw.gpr _ (by decide), u10, Offset.add_add]
  · rw [kx.gpr _ (by decide), kw.gpr _ (by decide), u0]
  · rw [x7, kw.gpr _ (by decide)]

theorem selPart_ct : RelCT isa (Rel e PSC) selPart (Rel e fun _ _ => True) := by
  unfold selPart
  refine RelCT.seq (rel_split (X := fun s u => u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r12 = fb s ∧ u.sp = fb s) (Q := PV)
    (l₁ := [fp, .load .d .r11 .r12 oOut, .load .d .r7 .r12 oK]) [] [.r11, .r12] (by taint_decide) (by taint_decide)
    (fun a b ha hb => ⟨pp_sp ha.1 hb.1, fun _ h => nomatch h⟩)
    (fun a b ⟨a11, a12, asp⟩ ⟨b11, b12, bsp⟩ => ⟨by rw [asp, bsp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a11, b11, e.r]
      · rw [a12, b12, e.fb_eq]⟩)
    (fun s u h ⟨⟨R, EM, hu⟩, _⟩ => by
      have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
      have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
      have i1 := slot_rd hu (d := oOut) (by decide) (by decide)
      have i2 := slot_rd hu (d := oK) (by decide) (by decide)
      prun [fp, exec_addSp0, hu.sp, c1, c2, i1, i2, hu.sl.out, hu.sl.k])
    fun s u h ⟨⟨R, EM, hu⟩, ⟨al, u6⟩, ⟨f, u5⟩, ⟨sep, u3, hsep⟩, u0, u8⟩ => by
      have hk := h.k1
      exact WP.mono (validBlock_ok hu (outIn h hu (by omega_using [hk])) (outIn h hu (by omega_using [hk])) u5 u3 u6 u0 u8 hsep hu.rb)
        fun v ⟨⟨vm, v11, v7, _, _, _, _, v12⟩, kv⟩ =>
          ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩, v11, v7, v12,
            by rw [kv.gpr _ (by decide), u0]⟩) ?_
  refine RelCT.seq (rel_split (X := fun s u => u.gpr .r10 = s.gpr .r5 ∧ u.gpr .r12 = fb s ∧ u.sp = fb s) (Q := PO)
    (l₁ := [.load .d .r10 .r12 oML]) [.r12] [.r10, .r12] (by taint_decide) (by taint_decide)
    (fun a b ⟨ha, _, _, a12, _⟩ ⟨hb, _, _, b12, _⟩ => ⟨pp_sp ha hb, fun r hr => by
      rw [List.mem_singleton.mp hr, a12, b12, e.fb_eq]⟩)
    (fun a b ⟨a10, a12, asp⟩ ⟨b10, b12, bsp⟩ => ⟨by rw [asp, bsp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a10, b10, e.r]
      · rw [a12, b12, e.fb_eq]⟩)
    (fun s u h ⟨⟨R, EM, hu⟩, _, _, u12, _⟩ => by
      have c1 : oML < 2 ^ 15 ∧ oML % 4 = 0 := by decide
      have i1 := slot_rd hu (d := oML) (by decide) (by decide)
      prun [u12, c1, i1, hu.sl.ml]
      exact hu.sp)
    fun s u h ⟨⟨R, EM, hu⟩, u11, u7, u12, u0⟩ => WP.mono (outInit_ok h hu.fr3 u12)
      fun v ⟨⟨vm, v10, _⟩, kv⟩ => ?_) ?_
  · have hY : Region.Sub ⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩ (mlR s) := by rw [BitVec.add_zero]; exact fun _ h => h
    have F : Frame [⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩] u.mem v.mem := by
      rw [vm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact ⟨⟨R, hu.fr3.store h kv.rd kv.wr kv.sp (fun r hr => kv.gpr r (by revert r; decide)) (.inr rfl) hY F⟩,
      by rw [kv.gpr _ (by decide), u11, BitVec.add_zero], by rw [v10, BitVec.add_zero],
      by rw [kv.gpr _ (by decide), u7], by rw [kv.gpr _ (by decide), u0]⟩
  refine RelCT.seq (rel_step (P' := fun s u => ∃ R, Fr3 s R u) [.r11, .r10, .r7] (by taint_decide)
    (fun a b ⟨⟨_, ha⟩, a11, a10, a7, _⟩ ⟨⟨_, hb⟩, b11, b10, b7, _⟩ => ⟨by rw [ha.sp, hb.sp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a11, b11, e.r]
      · rw [a10, b10, e.scA_eq]
      · rw [a7, b7, e.r]⟩)
    fun s u h ⟨⟨R, hu⟩, u11, u10, u7, u0⟩ => WP.mono (selLoop_run h hu u11 u10 u7 u0) fun v hv => ⟨R, hv⟩) ?_
  exact rel_step [] (by taint_decide) (fun a b ⟨_, ha⟩ ⟨_, hb⟩ => ⟨by rw [ha.sp, hb.sp, e.fb_eq], fun _ h => nomatch h⟩)
    fun s u h ⟨R, hu⟩ => WP.mono (finish_ok hu) fun _ _ => trivial

theorem body_ct : RelCT isa (Rel e PEnt) (body pc) fun _ _ => True := by
  unfold body
  refine RelCT.seq setup_ct ?_
  refine RelCT.seq priv_ct ?_
  refine RelCT.seq dBuild_ct ?_
  refine RelCT.seq (hashD_ct.mono (fun a b ⟨⟨_, _, ha⟩, _, _, hb⟩ => ⟨⟨_, _, ha.post⟩, _, _, hb.post⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq kdkMac_ct ?_
  refine RelCT.seq clLoop_ct ?_
  refine RelCT.seq amLoop_ct ?_
  refine RelCT.seq maskPart_ct ?_
  refine RelCT.seq alPart_ct ?_
  refine RelCT.seq scanPart_ct ?_
  exact selPart_ct.mono (fun _ _ h => h) fun _ _ _ => trivial

end

theorem code_ct : ConstantTime isa (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre
    (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pub code :=
  RelCT.constantTime (RelCT.alloc (fun _ _ ⟨_, _, hp⟩ => (same_of (pub_data hp)).sp)
    ((RelCT.exists_ fun e : Env false => body_ct (e := e)).mono
      (fun _ _ ⟨s, t, ⟨hs, ht, hp⟩, ea, eb⟩ =>
        ⟨⟨s, t, dPre_of hs, dPre_of ht, nofun, nofun, same_of (pub_data hp)⟩, ea, eb⟩)
      fun _ _ h => h))

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end

/-! ### `RsaPkcs1Enc.PPC64LE.DecCorrect`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: correctness

The frame's push, the setup, the private-key operation, `D`, `DH`, `KDK`,
`CL`, `AM`, the alternative length, the scan and the output, and the pop
(`code_correct`), to the outcome on the registers and the stack (`fnPost`,
`result_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.RsaPkcs1Enc (outByte)

variable {pc : Bool}

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg s'.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r7).toNat ((s'.gpr .r3).setWidth 32)
    (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (dOf s)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat) (cOf s))

theorem rOf_setWidth (x : BitVec 64) : (rOf x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [rOf, BitVec.toNat_setWidth]
  omega_using []

theorem rOf_one (x : BitVec 64) : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = decide (x.setWidth 32 = 1) := by
  have : rOf x ^^^ BitVec.ofNat 64 1 = 0 ↔ x.setWidth 32 = 1 := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro h; rw [← rOf_setWidth, h]; rfl
    · intro h; simp only [rOf, h]; rfl
  simp only [this]

/-- RSADP, as the specification calls the private-key operation. -/
def rsadpOf (s : State) (C : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) C
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)

/-- The outcome, from what the private-key operation gave and the end. -/
theorem result_ok {s : State} (h : DPre pc s) {x : BitVec 64} {mc : Mem} {t : State} {kd : List Byte}
    (hkd : kd = Spec.RsaPkcs1Enc.kdk (s.gpr .r7).toNat (dOf s) (cOf s))
    (hres : Spec.Rsa.writtenOutcome mc (s.gpr .r3) (s.gpr .r7).toNat (x.setWidth 32) (rsadpOf s (cOf s)))
    (hx : t.gpr .r3 = rOf x)
    (hout : ∀ i < (s.gpr .r7).toNat, t.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
      outByte (vOfEM s (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat)) (decide (rOf x ^^^ BitVec.ofNat 64 1 = 0))
        ((s.gpr .r7).toNat - lenOf s (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) kd) i
        ((Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat).getD i 1) ((amOf s kd).getD i 0))
    (hml : t.mem.readW (s.gpr .r5) 64 =
      BitVec.ofNat 64 (lenOf s (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) kd) &&&
        bm (decide (rOf x ^^^ BitVec.ofNat 64 1 = 0)))
    (hAM : (amOf s kd).length = (s.gpr .r7).toNat) : fnPost s t := by
  have hk := h.k1
  unfold fnPost
  have hn : (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat).length = (s.gpr .r7).toNat :=
    Proof.Rsa.bytesAt_length' _ _ _
  have hC : (cOf s).length = (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat).length := by
    rw [hn]; exact Proof.Rsa.bytesAt_length' _ _ _
  have hbytes : Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r7).toNat =
      (List.range (s.gpr .r7).toNat).map fun i => t.mem (s.gpr .r3 + BitVec.ofNat 64 i) := rfl
  have hw : Spec.Rsa.wordsAt t.mem (s.gpr .r5) 1 = [t.mem.readW (s.gpr .r5) 64] := by
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
  simp only [Spec.RsaPkcs1Enc.decrypt]
  show Spec.RsaPkcs1Enc.writtenMsg _ _ _ _ _ (Spec.RsaPkcs1Enc.decryptWith (rsadpOf s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat).length (dOf s) (cOf s))
  cases hO : rsadpOf s (cOf s) with
  | ok EM' =>
    rw [hO] at hres
    obtain ⟨hr, hb⟩ := hres
    have hok : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = true := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by rw [hn]; omega_using [hk]) hO]
    subst hb
    have hEMl := Proof.Rsa.bytesAt_length' mc (s.gpr .r3) (s.gpr .r7).toNat
    have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .r7).toNat (clOf kd)
    obtain ⟨hL1, hmap⟩ := Proof.RsaPkcs1Enc.sel_eq hEMl hAM (by omega_using [hk]) hal
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dOf s) (cOf s) (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) =
        (if Spec.RsaPkcs1Enc.valid (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) then
          Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat))
            (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat)
        else Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd)) (amOf s kd)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEMl, hkd]
    rw [hM]
    refine ⟨by rw [hx, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, ← hmap]
      exact List.map_congr_left fun i hi => by rw [hout i (List.mem_range.mp hi), hok]
    · rw [hw, hml, hok, show bm true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← hL1]
  | invalid =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_invalid hO]
    refine ⟨by rw [hx, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]
  | fault =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by rw [hn]; omega_using [hk]) hO]
    refine ⟨by rw [hx, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem codeG_correct (s : State) (h : DPre pc s) (X : pc = true → PreX s) :
    WP isa (codeG pc) s fun t => abiPreserved s t ∧ fnPost s t := by
  have hk := h.k2
  unfold codeG
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega_using [this]) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (call_ok h X A fun t₂ A₂ => ?_)
  refine WP.seq (WP.mono (dBuild_ok h A₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (hashD_ok h h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (kdkMac_ok h h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (clLoop_ok h h₅.post h₅.kdk) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (amLoop_ok h h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (maskPart_ok h h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (alPart_ok h h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (scanPart_ok h h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.mono (selPart_ok h h₁₀ (rOf_lt _)) fun u hu mL _ fl => ?_
  have hAM : (amOf s (Spec.RsaPkcs1Enc.kdk (s.gpr .r7).toNat (dOf s) (cOf s))).length = (s.gpr .r7).toNat := by
    show (Spec.RsaPkcs1Enc.irprf _ _ _).length = _
    rw [← h₇.am]; exact Proof.Rsa.bytesAt_length' _ _ _
  refine ⟨abiPreserved_lost ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [freed_gpr]; exact hu.hi r hr
  · rw [freed_sp, hu.sp]; exact BitVec.sub_add_cancel _ _
  · rw [freed_lr]; exact hu.lr
  · -- The `free` loses the frame's bytes, which lie apart from the outputs.
    have hfb : frameBytes ≤ stackBytes := by unfold stackBytes; omega_using []
    have hsub : Region.Sub ⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ (kR s) :=
      Offset.sub_below _ hfb (by omega_using [hfb])
    have hoR : (⟨s.gpr .r3, (s.gpr .r7).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
    refine result_ok h rfl ?_ hu.r3
      (fun i hi => (lost_byte fl (R := ⟨s.gpr .r3, (s.gpr .r7).toNat⟩)
        (by rw [hoR]; exact (h.ko.sub_left hsub).symm) hi).trans (hu.out i hi))
      ((fl.readW (r := mlR s) (by simp only [Region.Contains]; rw [BitVec.sub_self]; decide)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (h.km.sub_left hsub).symm)
        (by decide)).trans hu.ml) hAM
    have e : rsadpOf s (cOf s) = Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .r7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat) := rfl
    rw [e]
    exact A₂.out

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t :=
  codeG_correct s (dPre_of hpre) nofun

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract's postcondition on the registers and
the stack (`dec_implies`); with correctness (`code_correct`) and constant
time (`code_ct`), `code` is verified for the stack its frame and
`vg_rsa_private_checked`'s use (`dec_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pub

/-- A state meeting the precondition: a 64-byte modulus, input and `out`,
one-byte exponents, primes, CRT exponents and `qInv`, and the stack
arguments at `0x10060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000
    | .r9 => 1 | .r10 => 0x3100 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := if a = 0x10060 then 1 else if a = 0x10069 then 0x40 else if a = 0x10070 then 0x40
    else if a = 0x10079 then 0x41 else if a = 0x10080 then 1 else if a = 0x10089 then 0x42
    else if a = 0x10090 then 1 else if a = 0x10099 then 0x43 else if a = 0x100A0 then 1
    else if a = 0x100A9 then 0x44 else if a = 0x100B0 then 1 else if a = 0x100B9 then 0x45
    else if a = 0x100C0 then 1 else if a = 0x100CA then 0x02 else if a = 0x100D0 then 0x20
    else if a = 0x100D1 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x10060, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x20000, 8448⟩]

theorem dec_implies : fnContract.Implies (Spec.RsaPkcs1Enc.decryptContract abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContract,
      fnPost, stackArgs_fifteen, List.append_eq, dOf, cOf]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContract,
      stackArgs_fifteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_pkcs1_decrypt`. -/
theorem dec_verified : Verified target code (Spec.RsaPkcs1Enc.decryptContract abi stackBytes) :=
  Verified.of_correct code_correct code_ct dec_implies

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
