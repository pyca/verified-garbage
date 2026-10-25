module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc3
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS signing on ARMv7: the call of `vg_rsa_private_checked`

The call's arguments (`pa_vp`): `out`, `n`, `e`, `EM` (at `oEm`) as its
input, the private key, and the rest of `scratch` from `oRsa` on; the call
(`call_vp`), correct and constant time: its arguments and the public key it
reads are the same in two runs, and it writes RSASP1 of `EM`, checked
against `e`, the specification's signature (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

theorem rdArg {L : Lay} (m : Mem) (v : BitVec 32) {d j : Nat} (hd : d + 4 ≤ 64) (hj : j < 21) :
    (m.writeW (L.fr d) v).readW (L.fr (arg j)) 32 = m.readW (L.fr (arg j)) 32 :=
  Lay.readW_fr_other L m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by omega_arith)

theorem rdS {L : Lay} (m : Mem) (v : BitVec 32) {d : Nat} (hd : d + 4 ≤ 64) :
    (m.writeW (L.fr d) v).readW (L.fr sS) 32 = m.readW (L.fr sS) 32 :=
  Lay.readW_fr_other L m v (by unfold sS; omega_arith) (by decide) (by omega_arith)

/-- Words written to the frame from slot `k` on. -/
def wl (L : Lay) : Mem → Nat → List (BitVec 32) → Mem
  | m, _, [] => m
  | m, k, v :: vs => wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs

theorem wl_nil (L : Lay) (m : Mem) (k : Nat) : wl L m k [] = m := rfl
theorem wl_cons (L : Lay) (m : Mem) (k : Nat) (v : BitVec 32) (vs : List (BitVec 32)) :
    wl L m k (v :: vs) = wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs := rfl

theorem wl_other (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k j : Nat), j < k → k + vs.length ≤ 16 →
    (wl L m k vs).readW (L.fr (4 * j)) 32 = m.readW (L.fr (4 * j)) 32
  | [], _, _, _, _, _ => rfl
  | v :: vs, m, k, j, hj, hl => by
    rw [wl_cons, wl_other L vs _ (k + 1) j (by omega_arith) (by simp at hl; omega_arith),
      Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by simp at hl; omega_arith)]

theorem wl_read (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k i : Nat), k ≤ i → i < k + vs.length →
    k + vs.length ≤ 16 → (wl L m k vs).readW (L.fr (4 * i)) 32 = vs.getD (i - k) 0
  | [], _, _, _, h₁, h₂, _ => by simp at h₂; omega_arith
  | v :: vs, m, k, i, h₁, h₂, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at h₂ hl
    by_cases e : i = k
    · subst e
      rw [wl_other L vs _ (i + 1) i (by omega_arith) (by omega_arith), Mem.readW_writeW_self32, Nat.sub_self]; rfl
    · rw [wl_read L vs _ (k + 1) i (by omega_arith) (by omega_arith) (by omega_arith), show i - k = (i - (k + 1)) + 1 by omega_arith]; rfl

theorem wl_frame (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k : Nat), k + vs.length ≤ 16 →
    Frame [⟨L.fr 0, 64⟩] m (wl L m k vs)
  | [], _, _, _ => Frame.refl _ _
  | v :: vs, m, k, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.zero_le _) (by omega_arith) (by omega_arith))).trans (wl_frame L vs _ (k + 1) (by omega_arith))

/-- The call's stack arguments but the first. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [BitVec.ofNat 32 P.el, P.scr + BitVec.ofNat 32 oEm, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q,
    BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl,
    P.scr + BitVec.ofNat 32 oRsa, BitVec.ofNat 32 (P.scl - 1024)]

theorem pa_wp (P : EP) {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) (hi : In h.D P σ) :
    WP isa (.block privArgs) s fun t =>
      t.mem = wl (P.lay h.D) (s.mem.writeW (State.addr P.B) P.e) 1 (outv P) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧ t.gpr .r1 = BitVec.ofNat 32 P.K ∧
      t.gpr .r2 = P.n ∧ t.gpr .r3 = BitVec.ofNat 32 P.K := by
  have hg := hi.geo
  have hs1 : 1024 ≤ P.scl := by
    have := hi.slK; unfold Spec.RsaPss.scratchWords at this; omega_arith
  obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
  obtain ⟨a2, r2, v2⟩ := argAt hi hc.st (j := 2) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  obtain ⟨a5, r5, v5⟩ := argAt hi hc.st (j := 5) (by decide)
  obtain ⟨a6, r6, v6⟩ := argAt hi hc.st (j := 6) (by decide)
  obtain ⟨a7, r7, v7⟩ := argAt hi hc.st (j := 7) (by decide)
  obtain ⟨a8, r8, v8⟩ := argAt hi hc.st (j := 8) (by decide)
  obtain ⟨a9, r9, v9⟩ := argAt hi hc.st (j := 9) (by decide)
  obtain ⟨a10, r10, v10⟩ := argAt hi hc.st (j := 10) (by decide)
  obtain ⟨a12, r12, v12⟩ := argAt hi hc.st (j := 12) (by decide)
  obtain ⟨a14, r14, v14⟩ := argAt hi hc.st (j := 14) (by decide)
  obtain ⟨a20, r20, v20⟩ := argAt hi hc.st (j := 20) (by decide)
  replace v0 : s.mem.readW ((P.lay h.D).fr (arg 0)) 32 = P.out := v0
  replace v2 : s.mem.readW ((P.lay h.D).fr (arg 2)) 32 = P.n := v2
  replace v3 : s.mem.readW ((P.lay h.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
  replace v4 : s.mem.readW ((P.lay h.D).fr (arg 4)) 32 = P.e := v4
  replace v5 : s.mem.readW ((P.lay h.D).fr (arg 5)) 32 = BitVec.ofNat 32 P.el := v5
  replace v6 : s.mem.readW ((P.lay h.D).fr (arg 6)) 32 = P.p := v6
  replace v7 : s.mem.readW ((P.lay h.D).fr (arg 7)) 32 = BitVec.ofNat 32 P.pl := v7
  replace v8 : s.mem.readW ((P.lay h.D).fr (arg 8)) 32 = P.q := v8
  replace v9 : s.mem.readW ((P.lay h.D).fr (arg 9)) 32 = BitVec.ofNat 32 P.ql := v9
  replace v10 : s.mem.readW ((P.lay h.D).fr (arg 10)) 32 = P.dp := v10
  replace v12 : s.mem.readW ((P.lay h.D).fr (arg 12)) 32 = P.dq := v12
  replace v14 : s.mem.readW ((P.lay h.D).fr (arg 14)) 32 = P.qinv := v14
  replace v20 : s.mem.readW ((P.lay h.D).fr (arg 20)) 32 = BitVec.ofNat 32 P.scl := v20
  have wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr ((P.lay h.D).fr d) 4 := fun d hd => hc.st.inFr hd
  have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  have w0 : InRegions s.wr (State.addr P.B) 4 := by rw [q0]; exact wF 0 (by decide)
  have rdA0 : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j < 21 →
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr (arg j)) 32 = m.readW ((P.lay h.D).fr (arg j)) 32 :=
    fun m v j hj => by rw [q0]; exact rdArg m v (by decide) hj
  have rdS0 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr sS) 32 = m.readW ((P.lay h.D).fr sS) 32 :=
    fun m v => by rw [q0]; exact rdS m v (by decide)
  prun [privArgs, copyArg, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, hc.slotS, arg_lt,
    a0, r0, v0, a2, r2, v2, a3, r3, v3, a4, r4, v4, a5, r5, v5, a6, r6, v6, a7, r7, v7, a8, r8, v8, a9, r9, v9,
    a10, r10, v10, a12, r12, v12, a14, r14, v14, a20, r20, v20, rdArg, rdS, w0, rdA0, rdS0,
    movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oRsa < 2 ^ 16 by decide),
    movw_val (show 1024 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (w := 32) hs1, Nat.reduceMul, wl_cons, wl_nil,
    Nat.reduceAdd]

/-- Before the call. -/
abbrev R1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ) ∧
    PrivArgs s P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024)

theorem pa_vp (P : EP) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ)) (.block privArgs)
      (R1 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  refine WP.mono (pa_wp h P hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  rw [q0] at m
  obtain ⟨σ', ok⟩ := hg.ok
  have fr : Frame [⟨(P.lay h.D).fr 0, 64⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 0) (by decide)
      (by decide))).trans (wl_frame _ _ _ 1 (by simp))
  have rd0 : ∀ i, i < 16 → stackArg t i = t.mem.readW ((P.lay h.D).fr (4 * i)) 32 := by
    intro i hi
    simp only [stackArg, stackArgAddr, sp, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega_arith)]
  have v0 : stackArg t 0 = P.e := by
    rw [rd0 0 (by decide), m, wl_other _ _ _ 1 0 (by decide) (by simp), Mem.readW_writeW_self32]
  have v : ∀ i, 1 ≤ i → i < 16 → stackArg t i = (outv P).getD (i - 1) 0 := fun i h1 h2 => by
    rw [rd0 i h2, m, wl_read _ _ _ 1 i h1 (by simp; omega_arith) (by simp)]
  have hK := hi.k1024
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h fr fun r hr => ?_, fun i hi' => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (show 0 + 64 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Lay.fr_sep (by decide) (by decide) (by decide), Lay.fr_sep (by decide) (by decide) (by decide),
      Lay.fr_sep (by decide) (by decide) (by decide)⟩
  · rw [← he i hi']
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (d := 0) (k := 64) (by have := hi'; unfold oEm oRsa; omega_arith)
        (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords at hs
  exact ⟨t0, t1, t2, t3, v0, v 1 (by decide) (by decide), v 2 (by decide) (by decide), v 3 (by decide) (by decide),
    v 4 (by decide) (by decide), v 5 (by decide) (by decide), v 6 (by decide) (by decide), v 7 (by decide) (by decide),
    v 8 (by decide) (by decide), v 9 (by decide) (by decide), v 10 (by decide) (by decide),
    v 11 (by decide) (by decide), v 12 (by decide) (by decide), v 13 (by decide) (by decide),
    v 14 (by decide) (by decide), v 15 (by decide) (by decide), hi.kv, hi.el1, hi.elK, hi.pl1, hi.plK, hi.ql1, hi.qlK,
    by omega_arith, by have := hi.scl32; omega_arith⟩

/-- What the specification signs: RSASP1 of `EM`, checked against `e`. -/
theorem sign_ok {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    Spec.RsaPss.sign h.G h.G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ) (saltB P σ) =
      Spec.Rsa.privateChecked P.nB P.eB ((List.range P.K).map (emF h P σ)) (pB P σ) (qB P σ) (dpB P σ)
        (dqB P σ) (qiB P σ) := by
  have hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega_arith
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hn0 : n0 P = b := by simp [n0, hbr]
  have hb0 : b ≠ 0 := fun e => hf.1 (by rw [hn0, e]; rfl)
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
  have hm : (digB h P σ).length = h.G.len := by rw [gl]; exact RsaPkcs1Sig.Arm.bytesAt_length _ _ _
  have hfit : h.G.len + (saltB P σ).length + 2 ≤
      Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) := by
    rw [gl, RsaPkcs1Sig.Arm.bytesAt_length, hem]; have := hf.2; omega_arith
  rw [hbr, RsaPss.sign_eq h.G (PssHash.valid h) hb0 hm rfl rfl e1 hdb hfit]
  refine congrArg (fun em => Spec.Rsa.privateChecked (b :: rest) P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ)
    (qiB P σ)) ?_
  rw [List.length_cons, show rest.length + 1 = P.K by omega_arith]
  refine congrArg (fun f => List.map f (List.range P.K)) (funext fun i => ?_)
  have hc := cW_byte hb0 rest
  unfold emF mkS Hs xB
  rw [hn0, ← hlo, ← hc, RsaPkcs1Sig.Arm.bytesAt_length, h.hash]

/-- The call's input and working space, in `scratch`. -/
abbrev inpR (P : EP) : Region := ⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩
abbrev scrR (P : EP) : Region := ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In h.D P σ) :
    State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm ∧
    State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa ∧
    Region.Sub (inpR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (inpR P).Disjoint (scrR P) ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1024 ≤ P.scl ∧ P.K ≤ 1024 := by
  have hf := hi.ok.fits P.SCR (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  have hK := hi.k1024
  have e1 : State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm :=
    addr_add (by unfold oEm; omega_arith)
  have e2 : State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa :=
    addr_add (by unfold oRsa; omega_arith)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, by omega_arith, hK⟩
  · rw [inpR, e1]; exact Offset.sub_base _ (by unfold oEm; omega_arith)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega_arith)
  · rw [inpR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega_arith) (by unfold oEm; omega_arith)
      (by unfold oRsa; omega_arith)

theorem call_pre {P : EP} {σ s : State} (hr : R1 h P σ s) :
    (Spec.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRd P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.K P.el
        P.pl P.ql) (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨hc, hk, -, pa⟩ := hr
  have hi := hk.1
  have ok := hi.ok
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
  have fit := ok.fit
  have hB := ok.B56
  have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  have oS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
  refine priv_pre pa hc.st.sp hB (by simp only [frameBytes] at fit; omega_arith) ?_ (oS.sub_right sS') ?_ ?_
  · intro w hw r hr
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact oS.sub_right sI
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · rw [q0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := 0) (n := 64) (by show 0 + 64 ≤ frameBytes + 56; decide)).symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.N) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
    · exact dIS.symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.PP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QI) (by simp) (by simp)).sub_left sS'
    · rw [q0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 64)
        (by show 0 + 64 ≤ frameBytes + 56; decide)).symm).sub_left sS'
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = (P.lay h.D).LOW := rfl
    rw [low]
    simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.mem_cons, List.not_mem_nil, or_false] at hr
    have fs := fun {R : Region} (hR : R ∈ (P.lay h.D).ro ++ (P.lay h.D).rw) => ok.fits R hR
    have hg := hi.geo
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (by decide)]; unfold oEm; omega_arith
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega_arith

theorem nB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- `out` and the result: the call. -/
theorem call_vp (P : EP) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1 h P) (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Fin h P) := by
  refine VP.callF (Proof.Rsa.Arm.code_verified v) (privCode_stack v)
    (privRd P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun _ _ hr => call_pre h hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨hc, hk, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
    have hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    have hscr : Covers [P.SCR] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hs.wr, ok.wr]; simp
    have hout : Covers [P.OUT] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hs.wr, ok.wr]; simp
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega_arith)⟩
    have wr' : Covers (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      hout.cons (by rw [e2]; exact inS (by unfold oRsa; omega_arith))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine Covers.cons ?_ ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons (Covers.cons ?_ Covers.nil))))))
    · rw [e1]; exact (inS (by unfold oEm; omega_arith)).right
    · rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 64 ≤ frameBytes; decide))).right
  · rw [hr.1.st.sp]; exact hr.2.1.1.ok.B56
  · exact priv_pub h₁.2.2.2 h₂.2.2.2 (by rw [h₁.1.st.sp, h₂.1.st.sp]) (by rw [nB_at h h₁.2.1.1 h₁.1.st,
      nB_at h h₂.2.1.1 h₂.1.st]) (by rw [eB_at h h₁.2.1.1 h₁.1.st, eB_at h h₂.2.1.1 h₂.1.st]) _ _
  · obtain ⟨hc, hk, he, pa⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = (P.lay h.D).LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    have st : (P.lay h.D).St σ s' := hs.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨(P.lay h.D).LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hi, st⟩, ?_⟩
    have em : Spec.Rsa.bytesAt s.mem (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K = (List.range P.K).map (emF h P σ) := by
      unfold Spec.Rsa.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      rw [List.mem_range] at hi'
      rw [← he i hi', e1, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have := priv_post pa po
    rw [nB_at h hi hs, eB_at h hi hs, em, hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp),
      hs.ro (R := P.DP) (by simp), hs.ro (R := P.DQ) (by simp), hs.ro (R := P.QI) (by simp)] at this
    rw [Res, sign_ok h hi hk.2.1]
    exact this

end VG.Proof.RsaPss.Arm.Sg
