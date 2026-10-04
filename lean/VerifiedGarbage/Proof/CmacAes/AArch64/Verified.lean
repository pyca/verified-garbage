import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.AArch64.FinalizeCorrect
import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `x19` and
`x20`); the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- What is known between the code before the call and the call. -/
structure SMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) K S R
  x19 : s.gpr .x19 = K
  x20 : s.gpr .x20 = S
  sp : s.sp = s₀.sp

theorem smid_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SMid s₀ W K S R) := by
  have sw := hp.scr_wrap
  have kw := hp.k_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x3]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (s₀.gpr .x2 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x2]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, x20₁, _, sp₁, mem₁, rd₁, wr₁⟩ :=
    subkeysPre_ok s₀ (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide))
      (inS _ (by decide)) (inK _ (by decide)) (inK _ (by decide))
  exact WP.of_runBlock ⟨s₁, run₁,
    callPre_of hp x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ mem₁ rd₁ wr₁, by rw [x19₁, hp.x2], by rw [x20₁, hp.x3], sp₁⟩

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysAArch64.pre s₀)
    (h0' : subkeysAArch64.pre s₀') (hq : subkeysAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SMid s₀ _ _ _ _) (F₂ := SMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨smid_wp hp, smid_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      SMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₁ ∧
      SMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.1.x20], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.2.x20], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x2 ∧ s₁.gpr .x20 = s₀.gpr .x3 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .x19 = s₀.gpr .x2 ∧ s₂.gpr .x20 = s₀.gpr .x3 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2.2, h.2.2.2, q5]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct (v : Ctr32Impl) :
    ConstantTime isa subkeysAArch64.pre subkeysAArch64.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis (its branches and
the copy loop depend only on `last_len`), the call of `vg_aes_ctr32` is
constant time by its own proof (`ctr_rel`), its arguments pinned by the
correctness proof (`FMid`), and the restore after it by the taint analysis
again, from `x19` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeAArch64.pre s₀)
    (h0' : finalizeAArch64.pre s₀') (hq : finalizeAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat
      (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19])
      (.block [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064]) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMid s₀ _ _ _ _ _ _) (F₂ := FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₁ ∧
      FMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₂)
    fun s₁ s₂ h => ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x5 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .x19 = s₀.gpr .x5 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2, h.2.2, q7]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct (v : Ctr32Impl) :
    ConstantTime isa finalizeAArch64.pre finalizeAArch64.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

/-!
# AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of `vg_aes_ctr32`),
a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem update_keepsV (v : Ctr32Impl) : (update v.callee).allInstrs keepsV = true := by
  simp only [update, body, Code.allInstrs, v.keepsV]; decide +kernel

theorem subkeys_keepsV (v : Ctr32Impl) : (subkeys v.callee).allInstrs keepsV = true := by
  simp only [subkeys, Code.allInstrs, v.keepsV]; decide +kernel

theorem finalize_keepsV (v : Ctr32Impl) : (finalize v.callee).allInstrs keepsV = true := by
  simp only [finalize, finPre, partialBlock, copy, Code.allInstrs, v.keepsV]; decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' :=
  WP.withPreservedV (update_wp v hs) (update_keepsV v)

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysAArch64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysAArch64.post s s' :=
  WP.withPreservedV (subkeys_wp v hs) (subkeys_keepsV v)

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeAArch64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeAArch64.post s s' :=
  WP.withPreservedV (finalize_wp v hs) (finalize_keepsV v)

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified (v : Ctr32Impl) :
    Verified AArch64.target (update v.callee) (Spec.Cmac.aesUpdateContract AArch64.abi) :=
  Verified.of_correct (update_correct v) (update_ct v) (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, updateAArch64, AArch64.abi,
      AArch64.argRegs] [updSat] using updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified (v : Ctr32Impl) :
    Verified AArch64.target (subkeys v.callee) (Spec.Cmac.aesSubkeysContract AArch64.abi) :=
  Verified.of_correct (subkeys_correct v) (subkeys_ct v) (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, subkeysAArch64, AArch64.abi,
      AArch64.argRegs] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified (v : Ctr32Impl) :
    Verified AArch64.target (finalize v.callee) (Spec.Cmac.aesFinalizeContract AArch64.abi) :=
  Verified.of_correct (finalize_correct v) (finalize_ct v) (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, finalizeAArch64, AArch64.abi,
      AArch64.argRegs] [finSat] using finSat)

end VG.Proof.CmacAes.AArch64
