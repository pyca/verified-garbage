module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndInvoke
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndTail
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndTaint
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`main_vp`): from the state the body starts from, it ends with the result
(`Fin`), and two runs with the same public data (the trace among it) leak
the same trace.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (eval_ne eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-! ## With `PS` full -/

theorem tapeLoad_vp : VP (Acc P) (.block tapeLoad) (C0 P) :=
  VP.ldrSp (c := [(.r7, arg 2)]) (fun _ _ _ _ h₁ h₂ => by rw [h₁.1.st.2.sp, h₂.1.st.2.sp])
    fun _ _ h => tapeLoad_wp h

theorem tapeStore_vp : VP (C0 P) (.block tapeStore) (C1 P) :=
  VP.taint [.r7, .r4] tapeStore_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]) fun _ _ h => tapeStore_wp h

theorem callArgs_vp : VP (C1 P) (.block callArgs) (C2 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) fun _ _ h => callArgs_wp h

theorem status_vp : VP (C3 P) (.block status) (D1 P) :=
  VP.taint [] status_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => status_wp h

theorem wipeArgs_vp : VP (D1 P) (.block wipeArgs) (D2 P) :=
  VP.stk (code := [_, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) fun _ _ h => wipeArgs_wp h

theorem wipe_vp : VP (D2 P) Impl.Bignum.Arm.maskBytes (D3 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.1, h₂.2.1], by rw [h₁.2.2.1, h₂.2.2.1]⟩)
    fun _ _ h => wipe_wp h

theorem fin_vp : VP (D3 P) (.block [.mov .r0 (.reg .r4)]) (Fin P) :=
  VP.taint [] fin_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => fin_wp h

theorem accept_vp (encName : String) (c : PdImpl) :
    VP (Acc P) (accept encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code)) (Fin P) :=
  tapeLoad_vp.seq (tapeStore_vp.seq (callArgs_vp.seq ((call_vp encName c).seq (status_vp.seq
    (wipeArgs_vp.seq (wipe_vp.seq fin_vp))))))

/-! ## Without `PS` full -/

theorem zeroArgs_vp : VP (RJ P) (.block zeroArgs) (R1 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => by rw [h₁.1.2.sp, h₂.1.2.sp]) fun _ _ h => zeroArgs_wp h

theorem zeroOut_vp : VP (R1 P) Impl.Bignum.Arm.maskBytes (R2 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.1, h₂.2.1], by rw [h₁.2.2.1, h₂.2.2.1]⟩)
    fun _ _ h => zeroOut_wp h

theorem wipeDrawn_vp : VP (R2 P) wipeDrawn (R2 P) := by
  refine VP.seq (G := fun σ s => R2 P σ s ∧ s.z = decide (cnt P σ (N P) = 0))
    (VP.taint [.r5] cmp50_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1, cnt_eq h₁.1.1.1 h₂.1.1.1 (Nat.le_refl _)]) fun _ _ h => cmp50_wp h) ?_
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [eval_eq, eval_eq, h₁.2, h₂.2, cnt_eq h₁.1.1.1.1 h₂.1.1.1.1 (Nat.le_refl _)]) ?_ ?_
  · exact VP.block_nil fun _ _ h => h.1.1
  · refine VP.seq (G := R2d P) (VP.stk (code := [_, _]) (by decide) (by decide)
      (fun _ _ _ _ h₁ h₂ => by rw [h₁.1.1.1.1.2.sp, h₂.1.1.1.1.2.sp]) fun _ _ h => drawnArgs_wp h.1.1 (by
        have := h.2; rw [eval_eq, h.1.2] at this; simpa using this)) ?_
    exact VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
      by rw [h₁.2.2.2, h₂.2.2.2, cnt_eq h₁.1.1.1.1 h₂.1.1.1.1 (Nat.le_refl _)]⟩) fun _ _ h => drawn_wp h

theorem tapeLoad'_vp : VP (R2 P) (.block tapeLoad) (R4 P) :=
  VP.ldrSp (c := [(.r7, arg 2)]) (fun _ _ _ _ h₁ h₂ => by rw [h₁.1.1.2.sp, h₂.1.1.2.sp])
    fun _ _ h => tapeLoad'_wp h

theorem budget_vp : VP (R4 P) (.block budget) (R5 P) :=
  VP.taint [.r3, .r8] budget_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.2.2.1, h₂.1.1.2.2.1]
    · rw [h₁.1.1.2.2.2.2, h₂.1.1.2.2.2.2]) fun _ _ h => budget_wp h

theorem tapeEnd_vp : VP (R5 P) (.ite .eq (.block exhausted) (.block request)) (Fin P) := by
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [eval_eq, eval_eq, h₁.2.2, h₂.2.2]) ?_ ?_
  · exact VP.taint [.r7, .r8] exhausted_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.2, h₂.1.1.2]
      · rw [h₁.1.1.1.1.2.2.2.2, h₂.1.1.1.1.2.2.2.2]) fun _ _ h => exhausted_wp h.1 (by
        have := h.2; rw [eval_eq, h.1.2.2] at this; simpa using this)
  · exact VP.taint [.r3, .r5, .r6, .r7, .r8] request_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.1.1.1.1.2.2.1, h₂.1.1.1.1.2.2.1]
      · rw [h₁.1.1.1.1.2.2.2.1, h₂.1.1.1.1.2.2.2.1, cnt_eq h₁.1.1.1.1.1.1 h₂.1.1.1.1.1.1 (Nat.le_refl _)]
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.1.2, h₂.1.1.2]
      · rw [h₁.1.1.1.1.2.2.2.2, h₂.1.1.1.1.2.2.2.2]) fun _ _ h => request_wp h.1 (by
        have := h.2; rw [eval_eq, h.1.2.2] at this; simpa using this)

theorem reject_vp : VP (RJ P) reject (Fin P) :=
  zeroArgs_vp.seq (zeroOut_vp.seq (wipeDrawn_vp.seq (tapeLoad'_vp.seq (budget_vp.seq tapeEnd_vp))))

/-! ## The body -/

theorem main_vp (encName : String) (c : PdImpl) :
    VP (S P) (body encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code)) (Fin P) := by
  refine start_vp.seq (scan_vp.seq (full_vp.seq ?_))
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [eval_eq, eval_eq, h₁.2, h₂.2, cnt_eq (At.st h₁.1).1 (At.st h₂.1).1 (Nat.le_refl _)]) ?_ ?_
  · exact (accept_vp encName c).mono (fun _ _ h => ⟨h.1.1, by
      have := h.2; rw [eval_eq, h.1.2] at this; simpa using this⟩) fun _ _ h => h
  · exact reject_vp.mono (fun _ _ h => rj_of h.1.1 (by
      have := h.2; rw [eval_eq, h.1.2] at this; simpa using this)) fun _ _ h => h

end VG.Proof.RsaPkcs1Enc.Arm.Rnd


namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

/-! ## Verified

The frames around the body (`wrap_ok`, `wrap_ct`), the result as the shared
contract states it, and a state that meets it (`sat`):
`vg_rsa_pkcs1_encrypt_random`, calling any implementation `c` of
`vg_rsa_public_precomputed_checked` through `vg_rsa_pkcs1_encrypt_precomputed`,
is verified (`code_verified`), with `stackBytes` (2312) bytes of stack.
-/

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (h : spec.pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  exact h.1

theorem code_ok (encName : String) (c : PdImpl) {s : State} (h : spec.pre s) :
    WP isa (code encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code)) s fun t =>
      abiPreserved s t ∧ spec.post s t := by
  have hs : 2312 ≤ s.sp.toNat := spec_sp h
  have hin := in_of_pre h
  have st := entered_state h
  have hsp : 56 + frameBytes ≤ s.sp.toNat := by show 56 + 1088 ≤ _; omega
  refine WP.mono (wrap_ok (by decide) (show frameBytes + 56 ≤ s.sp.toNat by show 1088 + 56 ≤ _; omega)
    (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono ((main_vp encName c).wp _ _ st) fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 44) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).MSG, (ep s).RAND, (ep s).PRE])
      (rw := [(ep s).OUT, (ep s).TAPE, (ep s).SCR]) (C := callStack) hsp]
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
      argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).MSG, (ep s).RAND, (ep s).PRE]) =>
      entered_ro (F := frameBytes) (A := 44) (C := callStack) (argv := (ep s).argv)
        (rw := [(ep s).OUT, (ep s).TAPE, (ep s).SCR]) hin.ok hsp hR
    have hR : randB (ep s) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (stackArg s 5)) (stackArg s 6).toNat :=
      ro (R := (ep s).RAND) (by simp)
    have hM : msgB (ep s) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (stackArg s 3)) (stackArg s 4).toNat :=
      ro (R := (ep s).MSG) (by simp)
    unfold Res at res
    rw [hR, hM] at res
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

theorem wordsAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.wordsAt m p n).length = n := by
  simp [Spec.Rsa.wordsAt]

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
    argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hp
  obtain ⟨hab, hc⟩ := List.append_inj hl (by simp [bytesAt_length, wordsAt_length, a0, a2, a10])
  obtain ⟨hA, hB⟩ := List.append_inj hab (by simp [bytesAt_length, a0, a2])
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hA) (by simp [bytesAt_length, a0])
  have hw := map_toNat_inj hB
  rw [h3, a0] at hn
  rw [a1, a2] at he
  rw [a9, a10] at hw
  rw [a0, a4, a5, a6] at hc
  simp only [ep, State.addr, hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hn, he, hw, hc]

theorem code_ct (encName : String) (c : PdImpl) :
    ConstantTime isa spec.pre spec.pub (code encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
      argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (VG.Proof.RsaPkcs1Sig.Arm.wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)
    (fun a b h => by
      rw [h.1]; have : 2312 ≤ s₁.sp.toNat := spec_sp h₁; show 1088 + 56 ≤ _; omega) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (main_vp (P := ep s₁) encName c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus of 64 bytes, `e` of one,
an empty message and tape, and the stack arguments at `0x8000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x6200 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x40 else
    if a = 0x8005 then 0x21 else
    if a = 0x8008 then 1 else
    if a = 0x800d then 0x30 else
    if a = 0x8015 then 0x31 else
    if a = 0x801d then 0x40 else
    if a = 0x8020 then 0x20 else
    if a = 0x8021 then 4 else
    if a = 0x8025 then 0x70 else
    if a = 0x8028 then 0x10 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x7000, 128⟩, ⟨0x8000, 44⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x6200, 16⟩, ⟨0x4000, 8448⟩]

theorem sat : ∃ s, spec.pre s := by
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.RsaPkcs1Enc.padEntropy] using satState

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
over `c` (by the name `encName`), meets the shared contract. -/
theorem code_verified (encName : String) (c : PdImpl) :
    Verified target (code encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code)) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok encName c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct encName c, sat⟩

end VG.Proof.RsaPkcs1Enc.Arm.Rnd
