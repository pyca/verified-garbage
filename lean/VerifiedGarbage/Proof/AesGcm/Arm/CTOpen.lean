module

public import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
meta import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
public import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.ZeroTest32
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
public import VerifiedGarbage.Proof.AesGcm.Arm.Args
public import VerifiedGarbage.Proof.AesGcm.Arm.Tag
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.AesGcm.Arm.Args
meta import VerifiedGarbage.Proof.AesGcm.Arm.Tag
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Impl.AesGcm.Arm
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
meta import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.AesGcm.Arm.CTBase
import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
meta import VerifiedGarbage.Proof.AesGcm.Arm.Fn

/-! ### `AesGcm.Arm.CTJ0`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: `j0` is constant time

Untrusted: everything here is checked by Lean. The invariant fixes the
context, the state, `W`, the stack pointer and the nonce's address and
length.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Before `j0`. -/
def J0I (c st w sp : BitVec 32) (Np : BitVec 32) (n : Nat) (s : State) : Prop :=
  ∃ k7 k8 H, J0In c st w sp k7 k8 H Np n s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem j0hash_ct [VG.Proof.Gcm.Arm.GhashLaw] {Np : BitVec 32} {n : Nat} (hlt : n < 2 ^ 32) : CT (J0I c st w sp Np n) j0hash := by
  -- the accumulator zeroed, then the nonce absorbed
  let A : State → Prop := fun s => ∃ k8 H, AbsIn c st w sp (BitVec.ofNat 32 n) k8 0 H [] Np n s ∧
    blockAt s.mem (State.addr st + BitVec.ofNat 64 0) = 0
  refine CT.seq (J := A) ?_ (fun s ⟨k7, k8, H, hs⟩ => WP.mono (j0zero_ok L hs)
    fun s' h => ⟨k8, H, h.1, h.2.1⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5, .r10]) (.block [.mov .r0 (imm 0),
        .str .r0 .r10 0, .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12, .mov .r7 (.reg .r5), .mov .r6 (imm 0)])
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r5, h₂.r5]
    · exact h₁.env.pin h₂.env (by simp)
  let E : State → Prop := fun s => ∃ k8, Env c st w sp (BitVec.ofNat 32 n) k8 s
  refine CT.seq (J := E) ((absorb_ct L (.inl rfl) (by decide)).mono fun s ⟨k8, H, hs, _⟩ => ⟨_, k8, H, [], rfl, hs⟩)
    (fun s ⟨k8, H, hs, _⟩ => WP.mono (absorb_ok L (.inl rfl) hs) fun s' h => ⟨k8, h.env⟩) ?_
  -- the length of the nonce modulo 16
  let F : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧
    s.gpr .r7 = BitVec.ofNat 32 n
  refine CT.seq (J := F) ?_ (fun s ⟨k8, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7]) (.block [.dp .and .r6 .r7 (imm 15)])
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r7, h₂.r7]) hc
  · have hand := and15 (BitVec.ofNat 32 n)
    rw [toNat32 hlt] at hand
    refine WP.of_runBlock ⟨s.setReg .r6 (s.gpr .r7 &&& BitVec.ofNat 32 15), by arun [], _, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, he.r7, hand]
    · simp [gpr_setReg, he.r7]
  let G : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s
  refine CT.seq (J := G) ((flush_ct L (yo := 0) (.inl rfl) (q := n % 16) (Nat.mod_lt _ (by decide))).mono
    fun s ⟨k7, k8, he, h6, _⟩ => ⟨k7, k8, he, h6⟩) (fun s ⟨k7, k8, he, h6, _⟩ => WP.mono
      (flush_ok L (yo := 0) (.inl rfl) (x := List.replicate n 0) (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240))
        ⟨he, rfl⟩ (by rw [h6]; simp)) fun s' h => ⟨k7, k8, h.env⟩) ?_
  refine CT.seq (J := G) ?_ (fun s ⟨k7, k8, he⟩ => ?_) ((lens_ct L (.inl rfl)).mono fun s h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r4 (imm 0), .mov .r5 (imm 0),
        .mov .r6 (.reg .r7), .mov .r7 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun _ _ _ _ r hr => by simp at hr) hc
  · exact WP.of_runBlock ⟨(((s.setReg .r4 (BitVec.ofNat 32 0)).setReg .r5 (BitVec.ofNat 32 0)).setReg .r6
      (s.gpr .r7)).setReg .r7 (BitVec.ofNat 32 0), by arun [], _, k8, he.set7 (k7' := 0) (by simp [gpr_setReg]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl⟩

theorem j0_ct [VG.Proof.Gcm.Arm.GhashLaw] {Np : BitVec 32} {n : Nat} (hlt : n < 2 ^ 32) : CT (J0I c st w sp Np n) j0 := by
  refine CT.seq (J := fun s => J0I c st w sp Np n s ∧ s.z = decide (n = 12)) ?_ (fun s ⟨k7, k8, H, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 12)])
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmpk_ok s .r5 hs.r5 hlt (k := 12) (by decide) (by decide)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, H, ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁,
      by rw [hm₁]; exact hs.hH, by rw [hg₁]; exact hs.r4, by rw [hg₁]; exact hs.r5, hs.data.of_eq hrd₁ hwr₁⟩⟩, hz⟩
  let M : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s
  refine CT.seq (J := M) ?_ (fun s ⟨⟨k7, k8, H, hs⟩, hz⟩ => ?_) ?_
  · refine CT.ite (decide (n = 12)) (fun s h => h.2) (fun hb => ?_) (fun _ => (j0hash_ct L hlt).mono fun s h => h.1)
    obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r10]) (.block j012) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, h₁⟩, _⟩ ⟨⟨_, _, _, h₂⟩, _⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · exact h₁.env.pin h₂.env (by simp)
  · refine WP.ite (decide (n = 12)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
    · have h12 : n = 12 := by simpa using ht
      subst h12
      exact WP.mono (j012_ok L hs) fun s' h => h.env.elim fun k7 he => ⟨k7, k8, he⟩
    · exact WP.mono (j0hash_ok L hs (by simpa using hf)) fun s' h => h.env.elim fun k7 he => ⟨k7, k8, he⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r10]) (.block initState) h).isSome = true :=
      ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr => h₁.pin h₂ (by simp at hr; simp [hr])) hc

end

end VG.Proof.AesGcm.Arm

end

end

/-! ### `AesGcm.Arm.CTFn`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: constant time of the functions, the tools

Untrusted: everything here is checked by Lean. The functions relate two runs
from initial states `s₀` and `s₀'` with the same public data (`F`, `F'`
describe each run from its initial state); the pieces' `CT` lemmas apply
with the public data of `s₀` (`rel_of_ct`); blocks that read stack
arguments are checked with them public (`rel_argTaint`), from `ArgsKeep`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem rel_of_ct {I F F' : State → Prop} {c : Prog isa} (h : CT I c) (h₁ : ∀ s, F s → I s)
    (h₂ : ∀ s, F' s → I s) : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True :=
  RelCT.mono h (fun _ _ hh => ⟨h₁ _ hh.1, h₂ _ hh.2⟩) fun _ _ _ => trivial

/-- The stack arguments, as public in the taint analysis, from two runs that keep them. -/
theorem ArgsKeep.agree {n : Nat} {s₀ s₀' s s' : State} (hk : ArgsKeep n s₀ s) (hk' : ArgsKeep n s₀' s')
    (hsp : s₀.sp = s₀'.sp) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32) (ha : ∀ i < n, stackArg s₀ i = stackArg s₀' i)
    (hw : ∀ r ∈ s₀.wr, (args s₀ n).Disjoint r) (hw' : ∀ r ∈ s₀'.wr, (args s₀' n).Disjoint r)
    {rs : List Reg} (hr : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    VG.Arm.Taint.Agree (argTaint rs (4 * n)) s s' := by
  have e : ∀ {t₀ t : State}, ArgsKeep n t₀ t → (∀ r ∈ t₀.wr, (args t₀ n).Disjoint r) →
      t.sp.toNat + 4 * n ≤ 2 ^ 32 → t.sp.toNat + 4 * n ≤ 2 ^ 32 ∧
        ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4 * n⟩ r := fun {t₀ t} k w f => by
    refine ⟨f, fun r hr => ?_⟩
    rw [k.wr] at hr
    have := w r hr
    simp only [args, argAddr_zero] at this
    rwa [← k.sp] at this
  have f : s.sp.toNat + 4 * n ≤ 2 ^ 32 := by rw [hk.sp]; exact hf
  have f' : s'.sp.toNat + 4 * n ≤ 2 ^ 32 := by rw [hk'.sp, ← hsp]; exact hf
  have hsp' : s.sp = s'.sp := by rw [hk.sp, hk'.sp, hsp]
  exact agree_argTaint hr hsp' (e hk hw f) (e hk' hw' f')
    (argMem_of hsp' f fun i hi => by rw [hk.arg i hi, hk'.arg i hi, ha i hi])

theorem ArgsKeep.weaken {n m : Nat} {s₀ s : State} (h : ArgsKeep n s₀ s) (hm : m ≤ n) : ArgsKeep m s₀ s :=
  ⟨h.sp, h.rd, h.wr, fun i hi => h.arg i (by omega_using [hm, hi])⟩

theorem args_sub (s : State) {m n : Nat} (hm : m ≤ n) : Region.Sub (args s m) (args s n) :=
  Region.sub_prefix (by omega_using [hm])

theorem rel_ite {F F' : State → Prop} {t e : Prog isa} (b : Bool) (hz : ∀ s, F s → s.z = b)
    (hz' : ∀ s, F' s → s.z = b) (ht : b = true → RelCT isa (fun a b => F a ∧ F' b) t fun _ _ => True)
    (he : b = false → RelCT isa (fun a b => F a ∧ F' b) e fun _ _ => True) :
    RelCT isa (fun a b => F a ∧ F' b) (.ite .eq t e) fun _ _ => True := by
  refine RelCT.ite (fun _ _ h => by rw [eval_eq' (hz _ h.1), eval_eq' (hz' _ h.2)]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

theorem rel_skip {F F' : State → Prop} : RelCT isa (fun a b => F a ∧ F' b) (.block []) fun _ _ => True :=
  rel_of_ct (I := fun _ => True) CT.skip (fun _ _ => trivial) (fun _ _ => trivial)

end VG.Proof.AesGcm.Arm

end

end

/-! ### `AesGcm.Arm.CTOne`, which this module and modules that import it used -/

section

/-! ### `AesGcm.Arm.CTVerify`, which this module and modules that import it used -/

section

/-! ### `AesGcm.Arm.CTFin`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: `finTag`, `vg_aes_gcm_stream_finish` and `vg_aes_gcm_stream_verify` are constant time

Untrusted: everything here is checked by Lean. `finish` copies the tag to
`tag` through a pointer read from the stack (`tagOut_wp`); `verify` compares
the tags without a branch: only the tag length decides which code runs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

/-- What `finTag` needs, in a run from `s₀`. -/
def FT (na : Nat) (s₀ : State) (c st w sp : BitVec 32) (R : Nat) (s : State) : Prop :=
  ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s ∧ ArgsKeep na s₀ s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_rel [VG.Proof.Gcm.Arm.GhashLaw] {na : Nat} (hna : 4 ≤ na) {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {s₀ s₀' : State} (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hsp : s₀.sp = s₀'.sp)
    (ha : ∀ i < na, arg s₀ i = arg s₀' i) (hw : ∀ r ∈ s₀.wr, (args s₀ na).Disjoint r)
    (hw' : ∀ r ∈ s₀'.wr, (args s₀' na).Disjoint r) (hin : args s₀ na ∈ s₀.rd) (hin' : args s₀' na ∈ s₀'.rd)
    (hA : ∀ r ∈ tagFrame st w sp o, (args s₀ na).Disjoint r) (hA' : ∀ r ∈ tagFrame st w sp o, (args s₀' na).Disjoint r) :
    RelCT isa (fun a b => FT na s₀ c st w sp R a ∧ FT na s₀' c st w sp R b) (finTag o) fun _ _ => True := by
  have hf' : s₀'.sp.toNat + 4 * na ≤ 2 ^ 32 := by rw [← hsp]; exact hf
  have ag : ∀ {s s'}, ArgsKeep na s₀ s → ArgsKeep na s₀' s' →
      VG.Arm.Taint.Agree (argTaint [] (4 * 4)) s s' := fun k k' =>
    (k.weaken hna).agree (k'.weaken hna) hsp (by omega_arith) (fun i hi => ha i (by omega_arith))
      (fun r hr => (hw r hr).sub_left (args_sub _ hna)) (fun r hr => (hw' r hr).sub_left (args_sub _ hna)) (by simp)
  have keep : ∀ {s s' : State} {k7 : BitVec 32} (rs : List Reg), Env c st w sp k7 (BitVec.ofNat 32 R) s →
      (∀ r, r ∉ rs → s'.gpr r = s.gpr r) → (∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], r ∉ rs) → Keeps s s' →
      Env c st w sp k7 (BitVec.ofNat 32 R) s' := fun rs he hg hn hK =>
    he.keep (fun r hr => hg r (hn r hr)) hK.sp hK.rd hK.wr
  -- whether there is text
  let GA : State → State → Prop := fun t₀ s => FT na t₀ c st w sp R s ∧
    s.z = decide ((arg t₀ 3 ++ arg t₀ 2).toNat = 0)
  have runA : ∀ {t₀ s : State}, FT na t₀ c st w sp R s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd →
      WP isa (.block tlenZero) s (GA t₀) := fun {t₀ s} ⟨k7, he, hk⟩ f i => by
    obtain ⟨i2, v2⟩ := hk.at f i 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
    obtain ⟨i3, v3⟩ := hk.at f i 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_subFlags]) rfl rfl rfl,
      hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
    rw [z_sub0]
    exact decide_eq_decide.mpr (or_zero_iff _ _)
  have a := rel_agree (F := FT na s₀ c st w sp R) (F' := FT na s₀' c st w sp R) (G := GA s₀) (G' := GA s₀')
    (argTaint [] (4 * 4)) (c := .block tlenZero)
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runA h hf hin) (fun s h => runA h hf' hin')
  refine a.seq ?_
  -- the buffered bytes' length
  let v : State → BitVec 32 := fun t₀ => if (arg t₀ 3 ++ arg t₀ 2).toNat = 0 then arg t₀ 0 else arg t₀ 2
  let GB : State → State → Prop := fun t₀ s => FT na t₀ c st w sp R s ∧ s.gpr .r6 = v t₀
  have runB : ∀ {t₀ s : State}, GA t₀ s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd →
      WP isa (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8])) s (GB t₀) :=
    fun {t₀ s} ⟨⟨k7, he, hk⟩, hz⟩ f i => by
    refine WP.ite _ (eval_eq' hz) (fun ht => ?_) (fun hf₀ => ?_)
    · obtain ⟨i0, v0⟩ := hk.at f i 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (arg t₀ 3 ++ arg t₀ 2).toNat = 0 := by simpa using ht
      simp [gpr_setReg, v0, v, this]
    · obtain ⟨i2, v2⟩ := hk.at f i 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2, v2], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (arg t₀ 3 ++ arg t₀ 2).toNat ≠ 0 := by simpa using hf₀
      simp [gpr_setReg, v2, v, this]
  have b : RelCT isa (fun a b => GA s₀ a ∧ GA s₀' b) (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8]))
      fun _ _ => True := by
    refine rel_ite (decide ((arg s₀ 3 ++ arg s₀ 2).toNat = 0)) (fun s h => h.2)
      (fun s h => by rw [h.2, ha 3 (by omega_arith), ha 2 (by omega_arith)]) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (argTaint [] (4 * 4)) (.block [.ldrSp .r6 0]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := taint) (argTaint [] (4 * 4)) (fun s s' h =>
        ag h.1.1.choose_spec.2 h.2.1.choose_spec.2) hc
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (argTaint [] (4 * 4)) (.block [.ldrSp .r6 8]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := taint) (argTaint [] (4 * 4)) (fun s s' h =>
        ag h.1.1.choose_spec.2 h.2.1.choose_spec.2) hc
  refine (rel_wp b (fun s h => runB h hf hin) (fun s h => runB h hf' hin')).seq ?_
  have hv : v s₀' = v s₀ := by simp only [v, ha 0 (by omega_arith), ha 2 (by omega_arith), ha 3 (by omega_arith)]
  -- modulo 16
  let GC : State → State → Prop := fun t₀ s => FT na t₀ c st w sp R s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((v s₀).toNat % 16)
  have runC : ∀ {t₀ s : State}, v t₀ = v s₀ → GB t₀ s → WP isa (.block [.dp .and .r6 .r6 (imm 15)]) s (GC t₀) :=
    fun {t₀ s} e ⟨⟨k7, he, hk⟩, h6⟩ => by
    refine WP.of_runBlock ⟨_, by arun [], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [gpr_setReg, ite_true, h6, and15, e]
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) (.block [.dp .and .r6 .r6 (imm 15)]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have cC := rel_wp (F := GB s₀) (F' := GB s₀') (G := GC s₀) (G' := GC s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s s' h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hv]) hC)
    (fun s h => runC rfl h) (fun s h => runC hv h)
  refine cC.seq ?_
  -- the buffered bytes padded
  have runF : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → (∀ r ∈ tagFrame st w sp o, (args t₀ na).Disjoint r) →
      GC t₀ s → WP isa (flush 16) s (FT na t₀ c st w sp R) := fun {t₀ s} f hA₀ ⟨⟨k7, he, hk⟩, h6⟩ => by
    have hq := Nat.mod_lt (v s₀).toNat (show 16 > 0 by decide)
    refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate ((v s₀).toNat % 16) 0)
      (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
      fun s' ⟨fl, rd, wr, sp'⟩ => ⟨k7, fl.env, hk.frame f fl.frame (disj_sub hA₀ tFrame_sub) sp' rd wr⟩
  have cF := rel_wp (F := GC s₀) (F' := GC s₀') (G := FT na s₀ c st w sp R) (G' := FT na s₀' c st w sp R)
    (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (v s₀).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => runF hf hA h) (fun s h => runF hf' hA' h)
  refine cF.seq ?_
  -- the lengths
  have runD : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → args t₀ na ∈ t₀.rd → FT na t₀ c st w sp R s →
      WP isa (.block [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12]) s (FT na t₀ c st w sp R) :=
    fun {t₀ s} f i ⟨k7, he, hk⟩ => by
    obtain ⟨j0, w0⟩ := hk.at f i 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
    obtain ⟨j1, w1⟩ := hk.at f i 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
    obtain ⟨j2, w2⟩ := hk.at f i 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
    obtain ⟨j3, w3⟩ := hk.at f i 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by arun [j0, w0, j1, w1, j2, w2, j3, w3], ?_⟩
    exact ⟨_, he.set7 (k7' := arg t₀ 3) (by simp [gpr_setReg, w3]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩
  have cD := rel_agree (F := FT na s₀ c st w sp R) (F' := FT na s₀' c st w sp R) (G := FT na s₀ c st w sp R)
    (G' := FT na s₀' c st w sp R) (argTaint [] (4 * 4))
    (c := .block [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12])
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runD hf hin h) (fun s h => runD hf' hin' h)
  exact cD.seq (rel_of_ct (tag_ct L ho hR) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩))

end

/-- `tagOut` in a run from `t₀`, with the tag at its stack argument 4: what follows needs only `r11`. -/
theorem tagOut_wp {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {n : Nat} (hn : 5 ≤ n) {t₀ s : State}
    (he : Env c st w sp k7 k8 s) (hk : ArgsKeep n t₀ s) (hf : t₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args t₀ n ∈ t₀.rd) (hTw : (⟨State.addr (arg t₀ 4), 16⟩ : Region) ∈ t₀.wr)
    (hTf : (arg t₀ 4).toNat + 16 ≤ 2 ^ 32) (hTd : (⟨State.addr (arg t₀ 4), 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    WP isa (.block tagOut) s fun s' => s'.gpr .r11 = w := by
  obtain ⟨i4, v4⟩ := hk.at hf hin 4 (by omega_arith) (show 4 * 4 = 16 from rfl)
  obtain ⟨s', run, -, -, g, -⟩ := tagOut_ok L he i4 v4 (by rw [hk.wr]; exact covers_of_mem hTw) hTf hTd
  exact WP.of_runBlock ⟨s', run, by rw [g _ (by decide) (by decide), he.r11]⟩

theorem fin_hw {n wi : Nat} {t : State} (ht : finPre n wi t) : ∀ r ∈ t.wr, (args t n).Disjoint r := ht.2.1.2.2

theorem fin_entry_agree {n wi : Nat} {s₀ s₀' : State} (h0 : finPre n wi s₀) (h0' : finPre n wi s₀')
    (hq : finPub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2] (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀ h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 qa (fin_hw h0) (fin_hw h0')
    fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem streamFinish_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamFinishArm.pre s₀) (h0' : streamFinishArm.pre s₀')
    (hq : streamFinishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamFinish fun _ _ => True := by
  have h0₆ : finPre 6 5 s₀ := streamFinishPreArm.fin h0
  have h0₆' : finPre 6 5 s₀' := streamFinishPreArm.fin h0'
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := id hq
  have L := finLay h0₆
  have hR := h0₆.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h0₆.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0₆'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SF1 6 5 s₀) (G' := SF1 6 5 s₀')
    (argTaint [.r0, .r1, .r2] (4 * 6)) (c := .block (finEntry 20)) (fin_entry_agree h0₆ h0₆' hq) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact fin1_wp h0₆ (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact fin1_wp h0₆' (by decide) (by decide) fun _ h => h)
  let G : State → State → Prop := fun t₀ s =>
    (∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 5) s₀.sp k7 k8 s) ∧ ArgsKeep 6 t₀ s
  have tg : ∀ {t₀ : State}, finPre 6 5 t₀ → t₀.sp = s₀.sp → arg t₀ 5 = arg s₀ 5 → t₀.gpr .r0 = s₀.gpr .r0 →
      t₀.gpr .r2 = s₀.gpr .r2 → ∀ s, SF1 6 5 t₀ s → WP isa (finTag 0) s (G t₀) := fun {t₀} ht e0 e4 er0 er2 s h1 =>
    WP.mono (fin_tag ht (by decide) h1 (.inl rfl) (a := List.replicate ((arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0) (by simp) (by simp)) fun s' h => by
      obtain ⟨k7, he⟩ := h.env
      rw [e0, e4, er0, er2] at he
      exact ⟨⟨k7, _, he⟩, h.args⟩
  have e1 : BitVec.ofNat 32 (s₀.gpr .r1).toNat = s₀.gpr .r1 := by simp
  have b := rel_wp (F := SF1 6 5 s₀) (F' := SF1 6 5 s₀') (G := G s₀) (G' := G s₀')
    (finTag_rel L (na := 6) (by decide) (o := 0) (.inl rfl) hR spf q₀ qa (fin_hw h0₆) (fin_hw h0₆')
      h0₆.1.2 h0₆'.1.2 (fin_argsTag h0₆ (.inl rfl))
      (by have := fin_argsTag h0₆' (o := 0) (.inl rfl); rwa [← q₃, ← qa 5 (by decide), ← q₀] at this) |>.mono
      (fun s s' ⟨h₁, h₂⟩ => ⟨⟨_, by rw [e1]; exact h₁.env, h₁.args⟩, ⟨_, by
        have := h₂.env; rw [← q₁, ← q₂, ← q₃, ← qa 5 (by decide), ← q₀] at this; rw [e1]; exact this, h₂.args⟩⟩)
      fun _ _ h => h)
    (tg h0₆ rfl rfl rfl rfl) (tg h0₆' q₀.symm (qa 5 (by decide)).symm q₁.symm q₃.symm)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 5
  obtain ⟨hrd, hwr, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨-, hwr', -, -, -, -, -, -, tW', -, -, -, -, -, -, -, -, fT', -⟩ := h0'
  have c := rel_agree (F := G s₀) (F' := G s₀') (G := W) (G' := W) (argTaint [.r11] (4 * 6)) (c := .block tagOut)
    (fun s s' ⟨⟨_, _, he⟩, hk⟩ ⟨⟨_, _, he'⟩, hk'⟩ => hk.agree hk' q₀ spf qa (fin_hw h0₆) (fin_hw h0₆') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨⟨_, _, he⟩, hk⟩ => tagOut_wp L (by decide) he hk spf h0₆.1.2 (by rw [hwr]; simp) fT
      (tW.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨⟨_, _, he⟩, hk⟩ => tagOut_wp L (by decide) he hk spf' h0₆'.1.2 (by rw [hwr']; simp) fT'
      (by rw [qa 5 (by decide)]; exact tW'.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨h₁, h₂⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) hB
  exact a.seq (b.seq (c.seq d))

theorem streamFinish_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamFinishArm.pre streamFinishArm.pub streamFinish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamFinish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

end

/-! ### `AesGcm.Arm.CTCryptFn`, which this module and modules that import it used -/

section

/-! ### `AesGcm.Arm.CTText`, which only this module used -/

section

/-!
# AES-GCM on ARMv7: `textAbsorb` is constant time

Untrusted: everything here is checked by Lean. Two runs from initial states
`s₀` and `s₀'` with the same stack arguments: the blocks read them as
public, and `flush` and `absorb` are constant time by `flush_ct` and
`absorb_ct`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `textAbsorb` needs, in a run from `s₀`. -/
def TA (s₀ : State) (c st w sp : BitVec 32) (s : State) : Prop :=
  ∃ k7 k8, Env c st w sp k7 k8 s ∧ ArgsKeep 7 s₀ s ∧ DataOk st w sp s (arg s₀ 4) (arg s₀ 5).toNat

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

/-- `flush 16`, for one run, kept to what `textAbsorb` needs. -/
theorem ta_flush [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s : State} (h : TA s₀ c st w sp s) {q : Nat} (hq : q < 16) (h6 : s.gpr .r6 = BitVec.ofNat 32 q)
    (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hA : ∀ r ∈ taFrame st w sp, (args s₀ 7).Disjoint r) :
    WP isa (flush 16) s (TA s₀ c st w sp) := by
  obtain ⟨k7, k8, he, hk, hd⟩ := h
  refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate q 0)
    (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
    fun s' ⟨fl, rd, wr, sp'⟩ => ⟨k7, k8, fl.env, hk.frame hf fl.frame (fun r hr => hA r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp' rd wr, hd.of_eq rd wr⟩

theorem textAbsorb_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hsp : s₀.sp = s₀'.sp)
    (ha : ∀ i < 7, arg s₀ i = arg s₀' i) (hw : ∀ r ∈ s₀.wr, (args s₀ 7).Disjoint r)
    (hw' : ∀ r ∈ s₀'.wr, (args s₀' 7).Disjoint r) (hin : args s₀ 7 ∈ s₀.rd) (hin' : args s₀' 7 ∈ s₀'.rd)
    (hA : ∀ r ∈ taFrame st w sp, (args s₀ 7).Disjoint r) (hA' : ∀ r ∈ taFrame st w sp, (args s₀' 7).Disjoint r) :
    RelCT isa (fun a b => TA s₀ c st w sp a ∧ TA s₀' c st w sp b) textAbsorb fun _ _ => True := by
  have hf' : s₀'.sp.toNat + 4 * 7 ≤ 2 ^ 32 := by rw [← hsp]; exact hf
  have ag : ∀ {s s'}, ArgsKeep 7 s₀ s → ArgsKeep 7 s₀' s' →
      VG.Arm.Taint.Agree (argTaint [] (4 * 7)) s s' := fun k k' =>
    k.agree k' hsp hf ha hw hw' (by simp)
  -- the length of the data
  let G₁ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.z = decide ((arg t₀ 5).toNat = 0)
  have run₁ : ∀ {t₀ s : State}, TA t₀ c st w sp s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      WP isa (.block [.ldrSp .r5 20, .cmp .r5 (imm 0)]) s (G₁ t₀) := fun {t₀ s} ⟨k7, k8, he, hk, hd⟩ f i => by
    obtain ⟨i5, v5⟩ := hk.at f i 5 (by decide) (show 4 * 5 = 20 from rfl)
    refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
    refine ⟨⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
      hd.of_eq rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, v5]; exact z_sub0 _
  have a := rel_agree (F := TA s₀ c st w sp) (F' := TA s₀' c st w sp) (G := G₁ s₀) (G' := G₁ s₀')
    (argTaint [] (4 * 7)) (c := .block [.ldrSp .r5 20, .cmp .r5 (imm 0)])
    (fun s s' ⟨_, _, _, k, _⟩ ⟨_, _, _, k', _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₁ h hf hin) (fun s h => run₁ h hf' hin')
  refine a.seq (rel_ite (decide ((arg s₀ 5).toNat = 0)) (fun s h => h.2) (fun s h => by rw [h.2, ha 5 (by decide)])
    (fun _ => rel_skip) fun _ => ?_)
  -- whether there is text so far
  let G₂ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.z = decide ((arg t₀ 3 ++ arg t₀ 2).toNat = 0)
  have run₂ : ∀ {t₀ s : State}, G₁ t₀ s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      WP isa (.block tlenZero) s (G₂ t₀) := fun {t₀ s} ⟨⟨k7, k8, he, hk, hd⟩, _⟩ f i => by
    obtain ⟨i2, v2⟩ := hk.at f i 2 (by decide) (show 4 * 2 = 8 from rfl)
    obtain ⟨i3, v3⟩ := hk.at f i 3 (by decide) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_⟩
    refine ⟨⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_subFlags]) rfl rfl rfl,
      hk.of_eq rfl rfl rfl rfl, hd.of_eq rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
    rw [z_sub0]
    exact decide_eq_decide.mpr (or_zero_iff _ _)
  have b := rel_agree (F := G₁ s₀) (F' := G₁ s₀') (G := G₂ s₀) (G' := G₂ s₀')
    (argTaint [] (4 * 7)) (c := .block tlenZero)
    (fun s s' ⟨⟨_, _, _, k, _⟩, _⟩ ⟨⟨_, _, _, k', _⟩, _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₂ h hf hin) (fun s h => run₂ h hf' hin')
  refine b.seq ?_
  -- the additional data padded, before the first text
  have ff : ∀ {t₀ : State}, t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      (∀ r ∈ taFrame st w sp, (args t₀ 7).Disjoint r) →
      ∀ s, G₂ t₀ s → WP isa (.ite .eq firstFlush (.block [])) s (TA t₀ c st w sp) := fun {t₀} f i hA₀ s ⟨hs, hz⟩ => by
    refine WP.ite _ (eval_eq' hz) (fun _ => ?_) (fun _ => WP.block_nil hs)
    obtain ⟨k7, k8, he, hk, hd⟩ := hs
    obtain ⟨i0, v0⟩ := hk.at f i 0 (by decide) (show 4 * 0 = 0 from rfl)
    refine WP.seq (WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩)
    refine ta_flush L ⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
      hd.of_eq rfl rfl⟩ (q := (arg t₀ 0).toNat % 16) (Nat.mod_lt _ (by decide)) ?_ f hA₀
    simp only [gpr_setReg, ite_true, v0, and15]
  have cF : RelCT isa (fun a b => G₂ s₀ a ∧ G₂ s₀' b) (.ite .eq firstFlush (.block [])) fun _ _ => True := by
    refine rel_ite (decide ((arg s₀ 3 ++ arg s₀ 2).toNat = 0)) (fun s h => h.2)
      (fun s h => by rw [h.2, ha 3 (by decide), ha 2 (by decide)]) (fun _ => ?_) (fun _ => rel_skip)
    let G₃ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 0).toNat % 16)
    have run₃ : ∀ {t₀ s : State}, G₂ t₀ s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
        WP isa (.block [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)]) s (G₃ t₀) := fun {t₀ s} ⟨⟨k7, k8, he, hk, hd⟩, _⟩ f i => by
      obtain ⟨i0, v0⟩ := hk.at f i 0 (by decide) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩
      refine ⟨⟨k7, k8, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
        hd.of_eq rfl rfl⟩, ?_⟩
      simp only [gpr_setReg, ite_true, v0, and15]
    have c₁ := rel_agree (F := G₂ s₀) (F' := G₂ s₀') (G := G₃ s₀) (G' := G₃ s₀')
      (argTaint [] (4 * 7)) (c := .block [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)])
      (fun s s' ⟨⟨_, _, _, k, _⟩, _⟩ ⟨⟨_, _, _, k', _⟩, _⟩ => ag k k') ⟨_, by taint_decide⟩
      (fun s h => run₃ h hf hin) (fun s h => run₃ h hf' hin')
    exact c₁.seq (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (arg s₀ 0).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, k8, he, _⟩, h6⟩ => ⟨k7, k8, he, h6⟩)
      (fun s ⟨⟨k7, k8, he, _⟩, h6⟩ => ⟨k7, k8, he, by rw [h6, ha 0 (by decide)]⟩))
  refine (rel_wp cF (ff hf hin hA) (ff hf' hin' hA')).seq ?_
  -- the arguments of `absorb`
  let G₄ : State → State → Prop := fun t₀ s => TA t₀ c st w sp s ∧ s.gpr .r4 = arg t₀ 4 ∧ s.gpr .r5 = arg t₀ 5 ∧
    s.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 2).toNat % 16)
  have run₄ : ∀ {t₀ s : State}, TA t₀ c st w sp s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → args t₀ 7 ∈ t₀.rd →
      WP isa (.block textArgs) s (G₄ t₀) := fun {t₀ s} ⟨k7, k8, he, hk, hd⟩ f i => by
    obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := textArgs_run hk f i
    exact WP.of_runBlock ⟨s', run, ⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
      hk.of_eq hK.mem hK.sp hK.rd hK.wr, hd.of_eq hK.rd hK.wr⟩, h4, h5, h6⟩
  have d := rel_agree (F := TA s₀ c st w sp) (F' := TA s₀' c st w sp) (G := G₄ s₀) (G' := G₄ s₀')
    (argTaint [] (4 * 7)) (c := .block textArgs)
    (fun s s' ⟨_, _, _, k, _⟩ ⟨_, _, _, k', _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₄ h hf hin) (fun s h => run₄ h hf' hin')
  refine d.seq (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 4) (n := (arg s₀ 5).toNat)
    (q := (arg s₀ 2).toNat % 16) (Nat.mod_lt _ (by decide))) ?_ ?_)
  · intro s ⟨⟨k7, k8, he, _, hd⟩, h4, h5, h6⟩
    exact ⟨k7, k8, blockAt s.mem (State.addr c + BitVec.ofNat 64 240), List.replicate ((arg s₀ 2).toNat % 16) 0,
      by simp, ⟨he, h4, by rw [h5]; simp, by rw [h6]; simp, hd, rfl⟩⟩
  · intro s ⟨⟨k7, k8, he, _, hd⟩, h4, h5, h6⟩
    rw [← ha 4 (by decide), ← ha 5 (by decide)] at hd
    exact ⟨k7, k8, blockAt s.mem (State.addr c + BitVec.ofNat 64 240), List.replicate ((arg s₀ 2).toNat % 16) 0,
      by simp, ⟨he, by rw [h4, ha 4 (by decide)], by rw [h5, ha 5 (by decide)]; simp,
        by rw [h6, ha 2 (by decide)]; simp, hd, rfl⟩⟩

end

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

theorem sc_pubs {s₀ s₀' : State} (hq : streamCryptPub s₀ s₀') : s₀.sp = s₀'.sp ∧ s₀.gpr .r0 = s₀'.gpr .r0 ∧
    s₀.gpr .r1 = s₀'.gpr .r1 ∧ s₀.gpr .r2 = s₀'.gpr .r2 ∧ ∀ i < 7, arg s₀ i = arg s₀' i := hq

/-- The stack arguments are apart from the writable regions. -/
theorem sc_hw {t : State} (ht : streamCryptPre t) : ∀ r ∈ t.wr, (args t 7).Disjoint r := by
  obtain ⟨-, hwr, -, -, -, -, -, dsA, -, dDA, dWA, -⟩ := ht
  intro r hr
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dsA.symm
  · exact dDA.symm
  · exact dWA.symm

/-- After the entry of `encrypt` (or the arguments of `crypt`). -/
def EC1 (s₀ : State) (s : State) : Prop :=
  ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s ∧ ArgsKeep 7 s₀ s ∧
    s.gpr .r4 = arg s₀ 4 ∧ s.gpr .r5 = arg s₀ 5 ∧ s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16)

/-- Two runs' pieces agree on everything public. -/
theorem ec1_crI {s₀ s : State} (h : streamCryptPre s₀) (he : EC1 s₀ s) :
    CrI (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp (s₀.gpr .r1) (s₀.gpr .r1).toNat (arg s₀ 4) (arg s₀ 5).toNat
      ((arg s₀ 2).toNat % 16) s := by
  obtain ⟨k7, he, hk, h4, h5, h6⟩ := he
  exact ⟨k7, 0, (arg s₀ 3 ++ arg s₀ 2).toNat, (lowTo_mod16 rfl).symm, sc_crIn h he hk h4 h5 h6 0 rfl⟩

theorem ec1_crypt {s₀ s : State} (h : streamCryptPre s₀) (he : EC1 s₀ s) :
    WP isa crypt s (fun s' => TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s' ∧
      ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s') := by
  have L := scLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨k7, icb, P, -, ci⟩ := ec1_crI h he
  obtain ⟨_, _, hk, _⟩ := he
  refine WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s' ⟨co, rd, wr, sp⟩ => ?_
  have hk' := hk.frame spf co.frame (sc_argsCr h) sp rd wr
  exact ⟨⟨_, _, co.env, hk', (sc_dataW (k7 := k7) h hk').ok⟩, _, co.env⟩

theorem streamEncrypt_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamCryptPre s₀) (h0' : streamCryptPre s₀')
    (hq : streamCryptPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamEncrypt fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := sc_pubs hq
  have L := scLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : ∀ {t : State}, streamCryptPre t → args t 7 ∈ t.rd := fun {t} ht => by rw [ht.1]; simp
  have e1 : ∀ {t : State}, streamCryptPre t → WP isa (.block (cryptEntry ++ textArgs)) t (EC1 t) := fun {t} ht => by
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine WP.block_append (sc1_wp ht fun s₁ h1 => ?_)
    obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := textArgs_run h1.args spf (hin ht)
    exact WP.of_runBlock ⟨s', run, _, h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
      h1.args.of_eq hK.mem hK.sp hK.rd hK.wr, h4, h5, h6⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := EC1 s₀) (G' := EC1 s₀')
    (argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block (cryptEntry ++ textArgs))
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 7 s).agree (ArgsKeep.refl 7 s') q₀ spf qa (sc_hw h0) (sc_hw h0')
        fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact e1 h0) (fun s e => by rw [e]; exact e1 h0')
  let G₂ : State → Prop := fun s => TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s
  let G₂' : State → Prop := fun s => TA s₀' (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s
  have b := rel_wp (F := EC1 s₀) (F' := EC1 s₀') (G := G₂) (G' := G₂')
    (rel_of_ct (crypt_ct L) (fun s he => ec1_crI h0 he) (fun s he => by
      have := ec1_crI h0' he
      rwa [← q₁, ← q₂, ← q₃, ← q₀, ← qa 2 (by decide), ← qa 4 (by decide), ← qa 5 (by decide),
        ← qa 6 (by decide)] at this))
    (fun s he => WP.mono (ec1_crypt h0 he) fun _ h => h.1)
    (fun s he => WP.mono (ec1_crypt h0' he) fun _ h => by
      have := h.1; rwa [← q₁, ← q₃, ← q₀, ← qa 6 (by decide)] at this)
  have c := textAbsorb_rel L spf q₀ qa (sc_hw h0) (sc_hw h0') (hin h0) (hin h0')
    (sc_argsTa h0) (by
      have := sc_argsTa h0'; rwa [← q₃, ← qa 6 (by decide), ← q₀] at this)
  let G₃ : State → Prop := fun s => ∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 k8 s
  have ta : ∀ {t₀ : State}, streamCryptPre t₀ → t₀.sp = s₀.sp → arg t₀ 6 = arg s₀ 6 →
      t₀.gpr .r0 = s₀.gpr .r0 → t₀.gpr .r2 = s₀.gpr .r2 → ∀ s, TA t₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s →
      WP isa textAbsorb s G₃ := fun {t₀} ht e0 e6 er0 er2 s ⟨k7, k8, he, hk, hd⟩ => by
    have Lt := scLay ht
    rw [e0, e6, er0, er2] at Lt
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hA := sc_argsTa ht
    rw [e0, e6, er2] at hA
    exact WP.mono (textAbsorb_ok Lt (a := List.replicate ((arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0) he hk spf (hin ht) hA rfl hd (by simp) (by simp))
      fun s' h => ⟨_, _, h.env⟩
  have d := rel_wp (F := G₂) (F' := G₂') (G := G₃) (G' := G₃) c
    (ta h0 rfl rfl rfl rfl) (ta h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₃.symm)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) (P := fun s₁ s₂ => G₃ s₁ ∧ G₃ s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hB
  exact a.seq (b.seq (d.seq e))

theorem streamDecrypt_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamCryptPre s₀) (h0' : streamCryptPre s₀')
    (hq : streamCryptPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamDecrypt fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := sc_pubs hq
  have L := scLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : ∀ {t : State}, streamCryptPre t → args t 7 ∈ t.rd := fun {t} ht => by rw [ht.1]; simp
  let G₁ : State → Prop := fun s => TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
    ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s
  let G₁' : State → Prop := fun s => TA s₀' (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
    ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s
  have e1 : ∀ {t : State}, streamCryptPre t → t.sp = s₀.sp → arg t 6 = arg s₀ 6 → t.gpr .r0 = s₀.gpr .r0 →
      t.gpr .r1 = s₀.gpr .r1 → t.gpr .r2 = s₀.gpr .r2 →
      WP isa (.block cryptEntry) t fun s => TA t (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
        ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s :=
    fun {t} ht e0 e6 er0 er1 er2 => sc1_wp ht fun s₁ h1 => by
      have he := h1.env
      rw [e0, e6, er0, er1, er2] at he
      have hd := (sc_dataW (k7 := t.gpr .r7) ht h1.args).ok
      rw [e0, e6, er2] at hd
      exact ⟨⟨_, _, he, h1.args, hd⟩, _, he⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G₁) (G' := G₁')
    (argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block cryptEntry)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 7 s).agree (ArgsKeep.refl 7 s') q₀ spf qa (sc_hw h0) (sc_hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact e1 h0 rfl rfl rfl rfl rfl)
    (fun s e => by rw [e]; exact e1 h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₂.symm q₃.symm)
  have c := textAbsorb_rel L spf q₀ qa (sc_hw h0) (sc_hw h0') (hin h0) (hin h0')
    (sc_argsTa h0) (by
      have := sc_argsTa h0'; rwa [← q₃, ← qa 6 (by decide), ← q₀] at this)
  let G₂ : State → State → Prop := fun t₀ s =>
    ∃ k7, Env (t₀.gpr .r0) (t₀.gpr .r2) (arg t₀ 6) t₀.sp k7 (t₀.gpr .r1) s ∧ ArgsKeep 7 t₀ s
  have ta : ∀ {t₀ : State}, streamCryptPre t₀ → t₀.sp = s₀.sp → arg t₀ 6 = arg s₀ 6 →
      t₀.gpr .r0 = s₀.gpr .r0 → t₀.gpr .r1 = s₀.gpr .r1 → t₀.gpr .r2 = s₀.gpr .r2 → ∀ s,
      (TA t₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp s ∧
        ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s) →
      WP isa textAbsorb s (G₂ t₀) := fun {t₀} ht e0 e6 er0 er1 er2 s ⟨⟨_, _, _, hk, hd⟩, k7, he⟩ => by
    have Lt := scLay ht
    rw [e0, e6, er0, er2] at Lt
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hA := sc_argsTa ht
    rw [e0, e6, er2] at hA
    refine WP.mono (textAbsorb_ok Lt (a := List.replicate ((arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0) he hk spf (hin ht) hA rfl hd (by simp) (by simp))
      fun s' h => ⟨k7, ?_, h.args⟩
    have := h.env
    rwa [← e0, ← e6, ← er0, ← er1, ← er2] at this
  have d := rel_wp (F := G₁) (F' := G₁') (G := G₂ s₀) (G' := G₂ s₀') (c.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
    fun _ _ h => h) (ta h0 rfl rfl rfl rfl rfl) (ta h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₂.symm q₃.symm)
  -- the arguments of `crypt`
  have e3 : ∀ {t₀ : State}, streamCryptPre t₀ → ∀ s, G₂ t₀ s → WP isa (.block textArgs) s (EC1 t₀) :=
    fun {t₀} ht s ⟨k7, he, hk⟩ => by
      have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := textArgs_run hk spf (hin ht)
      exact WP.of_runBlock ⟨s', run, _, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
        hk.of_eq hK.mem hK.sp hK.rd hK.wr, h4, h5, h6⟩
  have f := rel_agree (F := G₂ s₀) (F' := G₂ s₀') (argTaint [] (4 * 7)) (c := .block textArgs)
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => k.agree k' q₀ spf qa (sc_hw h0) (sc_hw h0') (by simp)) ⟨_, by taint_decide⟩
    (e3 h0) (e3 h0')
  let G₃ : State → Prop := fun s => ∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp k7 k8 s
  have g := rel_wp (F := EC1 s₀) (F' := EC1 s₀') (G := G₃) (G' := G₃)
    (rel_of_ct (crypt_ct L) (fun s he => ec1_crI h0 he) (fun s he => by
      have := ec1_crI h0' he
      rwa [← q₁, ← q₂, ← q₃, ← q₀, ← qa 2 (by decide), ← qa 4 (by decide), ← qa 5 (by decide),
        ← qa 6 (by decide)] at this))
    (fun s he => WP.mono (ec1_crypt h0 he) fun _ h => h.2.elim fun k7 he => ⟨k7, _, he⟩)
    (fun s he => WP.mono (ec1_crypt h0' he) fun _ h => h.2.elim fun k7 he => by
      rw [← q₁, ← q₃, ← q₀, ← qa 6 (by decide)] at he; exact ⟨k7, _, he⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) (P := fun s₁ s₂ => G₃ s₁ ∧ G₃ s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hB
  exact a.seq (d.seq (f.seq (g.seq e)))

theorem streamEncrypt_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamEncryptArm.pre streamEncryptArm.pub streamEncrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamEncrypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem streamDecrypt_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamDecryptArm.pre streamDecryptArm.pub streamDecrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamDecrypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. Only the (public) tag length
decides which code runs: the tags are compared without a branch.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

/-- `rel_ite`, with a postcondition. -/
theorem rel_iteQ {F F' : State → Prop} {Q : State → State → Prop} {t e : Prog isa} (b : Bool)
    (hz : ∀ s, F s → s.z = b) (hz' : ∀ s, F' s → s.z = b)
    (ht : b = true → RelCT isa (fun a b => F a ∧ F' b) t Q)
    (he : b = false → RelCT isa (fun a b => F a ∧ F' b) e Q) :
    RelCT isa (fun a b => F a ∧ F' b) (.ite .eq t e) Q := by
  refine RelCT.ite (fun _ _ h => by rw [eval_eq' (hz _ h.1), eval_eq' (hz' _ h.2)]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

/-- `finTag`'s state with the tag length in `r6`, with `na` words of stack arguments. -/
def P6n (na : Nat) (c st w sp : BitVec 32) (R tl : Nat) (t₀ s : State) : Prop :=
  FT na t₀ c st w sp R s ∧ s.gpr .r6 = BitVec.ofNat 32 tl

/-- After the comparison: `r0` is 1 or 0. -/
def P7n (na : Nat) (c st w sp : BitVec 32) (R : Nat) (t₀ s : State) : Prop :=
  FT na t₀ c st w sp R s ∧ ∃ b : Bool, s.gpr .r0 = if b then 1 else 0

/-- With 7 words of stack arguments. -/
abbrev P6 (c st w sp : BitVec 32) (R tl : Nat) (t₀ s : State) : Prop := P6n 7 c st w sp R tl t₀ s
abbrev P7 (c st w sp : BitVec 32) (R : Nat) (t₀ s : State) : Prop := P7n 7 c st w sp R t₀ s

theorem ite_bool {p : Prop} [Decidable p] {x : BitVec 32} (h : x = if p then 1 else 0) :
    ∃ b : Bool, x = if b then 1 else 0 :=
  ⟨decide p, by rw [h]; simp only [decide_eq_true_eq]⟩

section
variable {c st w sp : BitVec 32} {R tl : Nat} {t₀ : State} {na : Nat}

/-- The tag length, stack argument `li`, to `r6`. -/
theorem ld6n_wp {s : State} {li off : Nat} (ho : off < 4096) (hli : li < na) (hoff : 4 * li = off)
    (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd)
    (h5 : (arg t₀ li).toNat = tl) (h : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 off]) s (P6n na c st w sp R tl t₀) := by
  subst h5
  obtain ⟨k7, he, hk⟩ := h
  obtain ⟨i5, v5⟩ := hk.at hf hin li hli hoff
  refine WP.of_runBlock ⟨_, by arun [ho, i5, v5], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp [gpr_setReg, v5]

theorem ld6_wp {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : args t₀ 7 ∈ t₀.rd)
    (h5 : (arg t₀ 5).toNat = tl) (h : FT 7 t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 20]) s (P6 c st w sp R tl t₀) :=
  ld6n_wp (by decide) (by decide) rfl hf hin h5 h

theorem tlon_wp {s : State} (htl : tl < 2 ^ 32) (h : P6n na c st w sp R tl t₀ s) :
    WP isa tagLenOk s fun s' => P6n na c st w sp R tl t₀ s' ∧ s'.z = !Spec.Gcm.tagLenOk tl := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (tagLenOk_ok h6 htl) fun s' ⟨hz, g, k⟩ => ⟨⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, by rw [g _ (by decide), h6]⟩, hz⟩

theorem tlo_wp {s : State} (htl : tl < 2 ^ 32) (h : P6 c st w sp R tl t₀ s) :
    WP isa tagLenOk s fun s' => P6 c st w sp R tl t₀ s' ∧ s'.z = !Spec.Gcm.tagLenOk tl :=
  tlon_wp htl h

theorem mov0_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (imm 0)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

variable (L : Lay c st w sp)
include L

/-- The received tag, stack argument `ti`, padded. -/
theorem recvn_wp {s : State} {ti off : Nat} (ho : off < 4096) (hti : ti < na) (hoff : 4 * ti = off)
    (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd)
    (hD : (args t₀ na).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (hTr : (⟨State.addr (arg t₀ ti), tl⟩ : Region) ∈ t₀.rd) (hTf : (arg t₀ ti).toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr (arg t₀ ti), tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (h : P6n na c st w sp R tl t₀ s) :
    WP isa (recvAt off) s (P6n na c st w sp R tl t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  obtain ⟨i4, v4⟩ := hk.at hf hin ti hti hoff
  refine WP.mono (recvAt_ok L ho he i4 v4 (by rw [hk.rd, hk.wr]; exact covers_of_mem (List.mem_append_left _ hTr))
    hTf hTd h6 h1 h16) fun s' ⟨_, hf₄, g₄, rd₄, wr₄, sp₄⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₄ rd₄ wr₄,
    hk.frame hf hf₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₄ rd₄ wr₄⟩, ?_⟩
  rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]

theorem recv_wp {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : args t₀ 7 ∈ t₀.rd)
    (hD : (args t₀ 7).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (hTr : (⟨State.addr (arg t₀ 4), tl⟩ : Region) ∈ t₀.rd) (hTf : (arg t₀ 4).toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr (arg t₀ 4), tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (h : P6 c st w sp R tl t₀ s) : WP isa recv s (P6 c st w sp R tl t₀) :=
  recvn_wp L (by decide) (by decide) rfl hf hin hD hTr hTf hTd h1 h16 h

theorem ft_wp [VG.Proof.Gcm.Arm.GhashLaw] {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : args t₀ 7 ∈ t₀.rd)
    (hA : ∀ r ∈ tagFrame st w sp 0, (args t₀ 7).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h : FT 7 t₀ c st w sp R s) : WP isa (finTag 0) s (FT 7 t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := h
  exact WP.mono (finTag_ok L (by decide) (.inl rfl) he hk hf hin hA rfl hR rfl
    (a := List.replicate ((arg t₀ 0).toNat % 16) 0) (ct := List.replicate (arg t₀ 3 ++ arg t₀ 2).toNat 0)
    (by simp) (by simp)) fun s' h => ⟨h.env.choose, h.env.choose_spec, h.args⟩

theorem cmpn_wp {s : State} (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hD : (args t₀ na).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (h : P6n na c st w sp R tl t₀ s) : WP isa (cmp o) s (P7n na c st w sp R t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (cmp_ok L he ho h6 h1 h16) fun s' ⟨h0, hf₇, g₇, rd₇, wr₇, sp₇⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₇ rd₇ wr₇,
    hk.frame hf hf₇ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₇ rd₇ wr₇⟩,
    ite_bool h0⟩

theorem cmp_wp {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hD : (args t₀ 7).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (h : P6 c st w sp R tl t₀ s) : WP isa (cmp o) s (P7 c st w sp R t₀) :=
  cmpn_wp L hf ho hD h1 h16 h

end

theorem streamVerify_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamVerifyArm.pre s₀) (h0' : streamVerifyArm.pre s₀')
    (hq : streamVerifyArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamVerify fun _ _ => True := by
  have h0₇ : finPre 7 6 s₀ := streamVerifyPreArm.fin h0
  have h0₇' : finPre 7 6 s₀' := streamVerifyPreArm.fin h0'
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := id hq
  have L := finLay h0₇
  have hR := h0₇.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h0₇.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0₇'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 7 ∈ s₀.rd := h0₇.1.2
  have hin' : args s₀' 7 ∈ s₀'.rd := h0₇'.1.2
  obtain ⟨hrd, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨hrd', -, -, -, -, -, -, tW', -, -, -, -, -, -, -, fT', -⟩ := h0'
  have hA := fin_argsTag h0₇ (o := 0) (.inl rfl)
  have hA' : ∀ r ∈ tagFrame (s₀.gpr .r2) (arg s₀ 6) s₀.sp 0, (args s₀' 7).Disjoint r := by
    have := fin_argsTag h0₇' (o := 0) (.inl rfl); rwa [← q₃, ← qa 6 (by decide), ← q₀] at this
  have hD : ∀ {d k : Nat}, d + k ≤ 2560 →
      (args s₀ 7).Disjoint ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
    fun hd => (h0₇.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have hD' : ∀ {d k : Nat}, d + k ≤ 2560 →
      (args s₀' 7).Disjoint ⟨State.addr (arg s₀ 6) + BitVec.ofNat 64 d, k⟩ := fun hd => by
    rw [qa 6 (by decide)]; exact (h0₇'.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have h5' : (arg s₀' 5).toNat = (arg s₀ 5).toNat := by rw [qa 5 (by decide)]
  have e1 : BitVec.ofNat 32 (s₀.gpr .r1).toNat = s₀.gpr .r1 := by simp
  -- shorthands for the public data
  let P6₀ := P6 (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (arg s₀ 5).toNat
  let FT₀ := fun t₀ => FT 7 t₀ (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat
  let P7₀ := P7 (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat
  let P3 : State → State → Prop := fun t₀ s => P6₀ t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (arg s₀ 5).toNat
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 6
  have r11 : ∀ {t₀ s}, FT₀ t₀ s → s.gpr .r11 = arg s₀ 6 := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
    (argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block (finEntry 24 ++ [.ldrSp .r6 20]))
    (fin_entry_agree h0₇ h0₇' hq) ⟨_, by taint_decide⟩
    (fun s e => by
      rw [e]
      exact WP.block_append (fin1_wp h0₇ (by decide) (by decide) fun s₁ h1 =>
        ld6_wp spf hin rfl ⟨_, by rw [e1]; exact h1.env, h1.args⟩))
    (fun s e => by
      rw [e]
      exact WP.block_append (fin1_wp h0₇' (by decide) (by decide) fun s₁ h1 =>
        ld6_wp spf' hin' h5' ⟨_, by
          have := h1.env; rw [← q₁, ← q₂, ← q₃, ← qa 6 (by decide), ← q₀] at this; rw [e1]; exact this, h1.args⟩))
  -- whether the length is allowed
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  have b := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := P3 s₀) (G' := P3 s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tlo_wp (arg s₀ 5).isLt h) (fun s h => tlo_wp (arg s₀ 5).isLt h)
  -- the branches
  have mid : RelCT isa (fun a b => P3 s₀ a ∧ P3 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) (.seq recv (.seq (finTag 0) (.seq (.block [.ldrSp .r6 20])
        (cmp 0))))) fun a b => W a ∧ W b := by
    refine rel_iteQ (!Spec.Gcm.tagLenOk (arg s₀ 5).toNat) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := P3 s₀) (F' := P3 s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => mov0_wp (r11 h.1.1)) (fun s h => mov0_wp (r11 h.1.1))
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 5).toNat = true := by simpa using hb
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      have x1 := rel_agree (F := P3 s₀) (F' := P3 s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (argTaint [.r6, .r11] (4 * 7)) (c := recv)
        (fun s s' h h' => h.1.1.choose_spec.2.agree h'.1.1.choose_spec.2 q₀ spf qa (fin_hw h0₇) (fin_hw h0₇')
          fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h'.1.2]
            · rw [r11 h.1.1, r11 h'.1.1]) ⟨_, by taint_decide⟩
        (fun s h => recv_wp L spf hin (hD (by decide)) (by rw [hrd]; simp) fT
          (tW.sub_right (Lay.wSub (by decide))) t1 t16 h.1)
        (fun s h => recv_wp L spf' hin' (hD' (by decide)) (by rw [hrd', h5']; simp)
          (by rw [← h5']; exact fT') (by rw [← h5', qa 6 (by decide)]; exact tW'.sub_right (Lay.wSub (by decide)))
          t1 t16 h.1)
      have x2 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := FT₀ s₀) (G' := FT₀ s₀')
        (finTag_rel L (na := 7) (by decide) (o := 0) (.inl rfl) hR spf q₀ qa (fin_hw h0₇) (fin_hw h0₇') hin hin'
          hA hA' |>.mono (fun s s' h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
        (fun s h => ft_wp L spf hin hA hR h.1) (fun s h => ft_wp L spf' hin' hA' hR h.1)
      have x3 := rel_agree (F := FT₀ s₀) (F' := FT₀ s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (argTaint [] (4 * 7)) (c := .block [.ldrSp .r6 20])
        (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (fin_hw h0₇) (fin_hw h0₇') (rs := [])
          (by simp)) ⟨_, by taint_decide⟩
        (fun s h => ld6_wp spf hin rfl h) (fun s h => ld6_wp spf' hin' h5' h)
      obtain ⟨_, c4⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp 0) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have x4 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.2, h.2.2]
          · rw [r11 h.1.1, r11 h.2.1]) c4)
        (fun s h => WP.mono (cmp_wp L spf (.inl rfl) (hD (by decide)) t1 t16 h) fun _ h => r11 h.1)
        (fun s h => WP.mono (cmp_wp L spf' (.inl rfl) (hD' (by decide)) t1 t16 h) fun _ h => r11 h.1)
      exact x1.seq (x2.seq (x3.seq x4))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) hB
  exact a.seq (b.seq (mid.seq d))

theorem streamVerify_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamVerifyArm.pre streamVerifyArm.pub streamVerify :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamVerify_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. Each piece is related across
two runs from `s₀` and `s₀'` with the same public data (`onePub`), from
what it needs in each run, to what the next piece needs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

/-- A relation of two runs of `c` carries what a further `R` reaches from them. -/
theorem rel_ghost {F F' G G' Z Z' : State → Prop} {c R : Prog isa}
    (h : RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b) :
    RelCT isa (fun a b => (F a ∧ WP isa (.seq c R) a Z) ∧ (F' b ∧ WP isa (.seq c R) b Z')) c
      fun a b => (G a ∧ WP isa R a Z) ∧ (G' b ∧ WP isa R b Z') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hg, hg'⟩ := h _ _ _ _ _ _ ⟨hp.1.1, hp.2.1⟩ e₁ e₂
  obtain ⟨u₁, x₁, f₁, w₁⟩ := WP.seq_iff.mp hp.1.2
  obtain ⟨u₂, x₂, f₂, w₂⟩ := WP.seq_iff.mp hp.2.2
  obtain ⟨-, rfl⟩ := Exec.det f₁ e₁
  obtain ⟨-, rfl⟩ := Exec.det f₂ e₂
  exact ⟨ht, ⟨hg, w₁⟩, ⟨hg', w₂⟩⟩

theorem wp_nil {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨t, s', e, hq⟩ := h
  rw [Exec.block_iff] at e
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, -⟩ := e
  exact hq

/-- The stack arguments are apart from what the code writes. -/
theorem one_hw {n wi : Nat} {t : State} (ht : onePre n wi t) : ∀ r ∈ t.wr, (args t n).Disjoint r := ht.2.1.2.2

/-- A block reading stack arguments below 20 is constant time in two runs that keep them. -/
theorem argsR {na : Nat} (hna : 5 ≤ na) {t₀ t₀' : State} (hsp : t₀.sp = t₀'.sp)
    (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (ha : ∀ i < na, arg t₀ i = arg t₀' i)
    (hw : ∀ r ∈ t₀.wr, (args t₀ na).Disjoint r) (hw' : ∀ r ∈ t₀'.wr, (args t₀' na).Disjoint r)
    {b : List Instr} (hb : ∃ hc, (taint.check (argTaint [] (4 * 5)) (.block b) hc).isSome = true)
    {P P' : State → Prop} (hP : ∀ s, P s → ArgsKeep na t₀ s) (hP' : ∀ s, P' s → ArgsKeep na t₀' s) :
    RelCT isa (fun a b => P a ∧ P' b) (.block b) fun _ _ => True := by
  obtain ⟨_, hc⟩ := hb
  exact RelCT.taint (A := taint) (argTaint [] (4 * 5)) (fun s s' h =>
    ((hP _ h.1).weaken hna).agree ((hP' _ h.2).weaken hna) hsp (by omega_arith) (fun i hi => ha i (by omega_arith))
      (fun r hr => (hw r hr).sub_left (args_sub _ hna)) (fun r hr => (hw' r hr).sub_left (args_sub _ hna))
      (by simp)) hc

/-! ## Each run -/

section
variable {na wi : Nat} {t₀ : State} {c w sp : BitVec 32} {R : Nat}

theorem so1_FT {s : State} (h1 : SO1 na wi t₀ s) (ec : t₀.gpr .r0 = c) (ew : arg t₀ wi = w) (esp : t₀.sp = sp)
    (eR : (t₀.gpr .r1).toNat = R) : FT na t₀ c (w + BitVec.ofNat 32 16) w sp R s := by
  subst ec ew esp eR
  exact ⟨_, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h1.env, h1.args⟩

theorem j0_wpI [VG.Proof.Gcm.Arm.GhashLaw] (h : onePre na wi t₀) (ec : t₀.gpr .r0 = c) (ew : arg t₀ wi = w) (esp : t₀.sp = sp) {s : State}
    (hs : FT na t₀ c (w + BitVec.ofNat 32 16) w sp R s) (h4 : s.gpr .r4 = t₀.gpr .r2)
    (h5 : s.gpr .r5 = t₀.gpr .r3) :
    J0I c (w + BitVec.ofNat 32 16) w sp (t₀.gpr .r2) (t₀.gpr .r3).toNat s ∧
      WP isa j0 s (FT na t₀ c (w + BitVec.ofNat 32 16) w sp R) := by
  subst ec ew esp
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨k7, he, hk⟩ := hs
  have hp := h
  obtain ⟨hrd, -, -, -, -, dnW, -, -, -, -, -, -, bn, -, -, -, -, fn, -⟩ := hp
  obtain ji : J0In (t₀.gpr .r0) (oSt t₀ wi) (arg t₀ wi) t₀.sp k7 (BitVec.ofNat 32 R)
      (blockAt s.mem (State.addr (t₀.gpr .r0) + BitVec.ofNat 64 240)) (t₀.gpr .r2) (t₀.gpr .r3).toNat s :=
    ⟨he, rfl, h4, by rw [h5]; simp, ⟨by rw [hk.rd, hk.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.1),
      (t₀.gpr .r3).isLt, fn, oSt_disj h dnW, dnW, bn⟩⟩
  exact ⟨⟨_, _, _, ji⟩, WP.mono (WP.with_rdwr (j0_ok L ji)) fun s' ⟨jo, rd', wr', sp'⟩ =>
    ⟨jo.env.choose, jo.env.choose_spec, hk.frame spf jo.frame (one_argsJ0 h) sp' rd' wr'⟩⟩

variable {st : BitVec 32}

theorem b1_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r4 0, .ldrSp .r5 4, .mov .r6 (imm 0)]) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r4 = arg t₀ 0 ∧ s'.gpr .r5 = arg t₀ 1 ∧ s'.gpr .r6 = BitVec.ofNat 32 0 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨a0, v0⟩ := hk.at hf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  obtain ⟨a1, v1⟩ := hk.at hf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  refine WP.of_runBlock ⟨_, by arun [a0, v0, a1, v1], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩,
    ?_, ?_, ?_⟩
  · simp [gpr_setReg, v0]
  · simp [gpr_setReg, v1]
  · simp [gpr_setReg]

theorem b2_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 4, .dp .and .r6 .r6 (imm 15)]) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 1).toNat % 16) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨b1, w1⟩ := hk.at hf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  refine WP.of_runBlock ⟨_, by arun [b1, w1], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp only [gpr_setReg, ite_true, w1, and15]

theorem b3_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 12, .dp .and .r6 .r6 (imm 15)]) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 3).toNat % 16) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨b3, w3⟩ := hk.at hf hin 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
  refine WP.of_runBlock ⟨_, by arun [b3, w3], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp only [gpr_setReg, ite_true, w3, and15]

theorem b4_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r4 4, .mov .r5 (imm 0), .ldrSp .r6 12, .mov .r7 (imm 0)]) s
      (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨j1, w1⟩ := hk.at hf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨j3, w3⟩ := hk.at hf hin 3 (by omega_arith) (show 4 * 3 = 12 from rfl)
  refine WP.of_runBlock ⟨_, by arun [j1, w1, j3, w3], ?_⟩
  exact ⟨_, he.set7 (k7' := BitVec.ofNat 32 0) (by simp [gpr_setReg]) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem da_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block dataArgs) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r4 = arg t₀ 2 ∧ s'.gpr .r5 = arg t₀ 3 ∧ s'.gpr .r6 = BitVec.ofNat 32 0 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨s', run, h4, h5, h6, g, k⟩ := dataArgs_run hk hf hin hn
  exact WP.of_runBlock ⟨s', run, ⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, h4, h5, h6⟩

variable (L : Lay c st w sp)
include L

theorem abs_wpI [VG.Proof.Gcm.Arm.GhashLaw] (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hJ : ∀ r ∈ j0Frame st w sp, (args t₀ na).Disjoint r)
    {D : BitVec 32} {n : Nat} (hd : DataOk st w sp t₀ D n) {s : State} (hs : FT na t₀ c st w sp R s)
    (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (h6 : s.gpr .r6 = BitVec.ofNat 32 0) :
    AbsI c st w sp 16 D n 0 s ∧ WP isa (absorb 16) s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ai : AbsIn c st w sp k7 (BitVec.ofNat 32 R) 16 (blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) []
      D n s := ⟨he, h4, h5, by rw [h6]; rfl, hd.of_eq hk.rd hk.wr, rfl⟩
  exact ⟨⟨_, _, _, _, rfl, ai⟩, WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s' ⟨ab, rd', wr', sp'⟩ =>
    ⟨k7, ab.env, hk.frame hf ab.frame (disj_sub hJ abs16_sub) sp' rd' wr'⟩⟩

theorem fl_wpI [VG.Proof.Gcm.Arm.GhashLaw] (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hJ : ∀ r ∈ j0Frame st w sp, (args t₀ na).Disjoint r)
    {q : Nat} (hq : q < 16) {s : State} (hs : FT na t₀ c st w sp R s) (h6 : s.gpr .r6 = BitVec.ofNat 32 q) :
    WP isa (flush 16) s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  exact WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate q 0)
    (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
    fun s' ⟨fl, rd', wr', sp'⟩ => ⟨k7, fl.env, hk.frame hf fl.frame (disj_sub hJ t16_sub) sp' rd' wr'⟩

theorem cr_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {D : BitVec 32} {n : Nat} (hd : DataOk st w sp t₀ D n)
    (hwD : Covers [⟨State.addr D, n⟩] t₀.wr) (hcD : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hA : ∀ r ∈ crFrame st w sp D n, (args t₀ na).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State}
    (hs : FT na t₀ c st w sp R s) (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 0) :
    CrI c st w sp (BitVec.ofNat 32 R) R D n 0 s ∧ WP isa crypt s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ci : CrIn c st w sp k7 (BitVec.ofNat 32 R) R (blockAt s.mem (State.addr st + BitVec.ofNat 64 48)) 0 D n s :=
    ⟨he, h4, h5, by rw [h6], he.r8, hR, ⟨hd.of_eq hk.rd hk.wr, by rw [hk.wr]; exact hwD, hcD⟩⟩
  exact ⟨⟨_, _, _, rfl, ci⟩, WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s' ⟨co, rd', wr', sp'⟩ =>
    ⟨k7, co.env, hk.frame hf co.frame hA sp' rd' wr'⟩⟩

theorem tg_wpI [VG.Proof.Gcm.Arm.GhashLaw] (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hT : ∀ r ∈ tagFrame st w sp o, (args t₀ na).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State}
    (hs : FT na t₀ c st w sp R s) : WP isa (tag o) s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  exact WP.mono (WP.with_rdwr (tag_ok L ho he rfl hR rfl rfl)) fun s' ⟨tg, rd', wr', sp'⟩ =>
    ⟨k7, tg.env, hk.frame hf tg.frame hT sp' rd' wr'⟩

end

/-! ## Both runs -/

theorem one_aadOk {n wi : Nat} {t : State} (h : onePre n wi t) :
    DataOk (oSt t wi) (arg t wi) t.sp t (arg t 0) (arg t 1).toNat := by
  have hp := h
  obtain ⟨hrd, -, -, -, -, -, -, daW, -, -, -, -, -, ba, -, -, -, -, fa, -⟩ := hp
  exact ⟨covers_of_mem (List.mem_append_left _ hrd.2.2.1), (arg t 1).isLt, fa, oSt_disj h daW, daW, ba⟩

theorem one_argsCr {n wi : Nat} {t : State} (h : onePre n wi t)
    (hw : (⟨State.addr (arg t 2), (arg t 3).toNat⟩ : Region) ∈ t.wr) :
    ∀ r ∈ crFrame (oSt t wi) (arg t wi) t.sp (arg t 2) (arg t 3).toNat, (args t n).Disjoint r := by
  obtain hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, dDA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (dDA hw).symm
  · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args t spf).symm

/-- A run's state, with the public data of `s₀` and the stack arguments of `t₀`. -/
abbrev OF (na wi : Nat) (s₀ t₀ s : State) : Prop :=
  FT na t₀ (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp (s₀.gpr .r1).toNat s

section
variable {na wi : Nat} {s₀ s₀' : State} (h0 : onePre na wi s₀) (h0' : onePre na wi s₀') (hq : onePub na s₀ s₀')
  (hn : 5 ≤ na) (hwi : wi < na)
include h0 h0' hq hn hwi

theorem oneAad_rel [VG.Proof.Gcm.Arm.GhashLaw] :
    RelCT isa (fun a b => SO1 na wi s₀ a ∧ SO1 na wi s₀' b) oneAad fun a b => OF na wi s₀ s₀ a ∧ OF na wi s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  obtain L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ na ∈ s₀.rd := h0.1.2.2.2
  have hin' : args s₀' na ∈ s₀'.rd := h0'.1.2.2.2
  obtain e4 : arg s₀' wi = arg s₀ wi := (qa wi hwi).symm
  obtain est : oSt s₀' wi = oSt s₀ wi := by show arg s₀' wi + _ = arg s₀ wi + _; rw [e4]
  obtain hJ := one_argsJ0 h0
  obtain hJ' : ∀ r ∈ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp, (args s₀' na).Disjoint r := by
    have := one_argsJ0 h0'; rwa [est, e4, ← q₀] at this
  obtain so : ∀ s, SO1 na wi s₀ s → OF na wi s₀ s₀ s := fun s h1 => so1_FT h1 rfl rfl rfl rfl
  obtain so' : ∀ s, SO1 na wi s₀' s → OF na wi s₀ s₀' s := fun s h1 => so1_FT h1 q₁.symm e4 q₀.symm (by rw [q₂])
  -- `J₀`
  obtain x1 := rel_wp (F := SO1 na wi s₀) (F' := SO1 na wi s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (rel_of_ct (j0_ct L (Np := s₀.gpr .r2) (n := (s₀.gpr .r3).toNat) (s₀.gpr .r3).isLt)
      (fun s h1 => (j0_wpI h0 rfl rfl rfl (so s h1) h1.r4 h1.r5).1)
      (fun s h1 => by
        have := (j0_wpI h0' q₁.symm e4 q₀.symm (so' s h1) h1.r4 h1.r5).1
        rwa [← q₃, ← q₄] at this))
    (fun s h1 => (j0_wpI h0 rfl rfl rfl (so s h1) h1.r4 h1.r5).2)
    (fun s h1 => (j0_wpI h0' q₁.symm e4 q₀.symm (so' s h1) h1.r4 h1.r5).2)
  -- the additional data's arguments
  let B1 : State → State → Prop := fun t₀ s => OF na wi s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 0 ∧
    s.gpr .r5 = arg s₀ 1 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  obtain x2 := rel_wp (F := OF na wi s₀ s₀) (F' := OF na wi s₀ s₀') (G := B1 s₀) (G' := B1 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b1_wpI spf hin hn h)
    (fun s h => WP.mono (b1_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 0 (by omega_arith)], by rw [y₃, qa 1 (by omega_arith)], y₄⟩)
  -- absorbed
  obtain hda := one_aadOk h0
  obtain hda' : DataOk (oSt s₀ wi) (arg s₀ wi) s₀.sp s₀' (arg s₀ 0) (arg s₀ 1).toNat := by
    have := one_aadOk h0'; rwa [est, e4, ← q₀, ← qa 0 (by omega_arith), ← qa 1 (by omega_arith)] at this
  obtain x3 := rel_wp (F := B1 s₀) (F' := B1 s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 0) (n := (arg s₀ 1).toNat) (q := 0) (by decide))
      (fun s h => (abs_wpI L spf hJ hda h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (abs_wpI L spf' hJ' hda' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (abs_wpI L spf hJ hda h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (abs_wpI L spf' hJ' hda' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  -- padded
  let B2 : State → State → Prop := fun t₀ s => OF na wi s₀ t₀ s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 1).toNat % 16)
  obtain x4 := rel_wp (F := OF na wi s₀ s₀) (F' := OF na wi s₀ s₀') (G := B2 s₀) (G' := B2 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b2_wpI spf hin hn h)
    (fun s h => WP.mono (b2_wpI spf' hin' hn h) fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, qa 1 (by omega_arith)]⟩)
  obtain x5 := rel_wp (F := B2 s₀) (F' := B2 s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (arg s₀ 1).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => fl_wpI L spf hJ (Nat.mod_lt _ (by decide)) h.1 h.2)
    (fun s h => fl_wpI L spf' hJ' (Nat.mod_lt _ (by decide)) h.1 h.2)
  exact x1.seq (x2.seq (x3.seq (x4.seq x5)))

theorem oneCrypt_rel (hw : (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region) ∈ s₀.wr)
    (hw' : (⟨State.addr (arg s₀' 2), (arg s₀' 3).toNat⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => OF na wi s₀ s₀ a ∧ OF na wi s₀ s₀' b) oneCrypt fun a b => OF na wi s₀ s₀ a ∧ OF na wi s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  obtain L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR : roundsOk s₀ := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ na ∈ s₀.rd := h0.1.2.2.2
  have hin' : args s₀' na ∈ s₀'.rd := h0'.1.2.2.2
  obtain e4 : arg s₀' wi = arg s₀ wi := (qa wi hwi).symm
  obtain est : oSt s₀' wi = oSt s₀ wi := by show arg s₀' wi + _ = arg s₀ wi + _; rw [e4]
  let D1 : State → State → Prop := fun t₀ s => OF na wi s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 2 ∧
    s.gpr .r5 = arg s₀ 3 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  obtain x1 := rel_wp (F := OF na wi s₀ s₀) (F' := OF na wi s₀ s₀') (G := D1 s₀) (G' := D1 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => da_wpI spf hin hn h)
    (fun s h => WP.mono (da_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by omega_arith)], by rw [y₃, qa 3 (by omega_arith)], y₄⟩)
  obtain hd := one_dataOk h0 (ArgsKeep.refl na s₀)
  obtain hd' : DataOk (oSt s₀ wi) (arg s₀ wi) s₀.sp s₀' (arg s₀ 2) (arg s₀ 3).toNat := by
    have := one_dataOk h0' (ArgsKeep.refl na s₀'); rwa [est, e4, ← q₀, ← qa 2 (by omega_arith), ← qa 3 (by omega_arith)] at this
  obtain hwD : Covers [⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩] s₀.wr := by
    exact covers_of_mem hw
  obtain hwD' : Covers [⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩] s₀'.wr := by
    rw [qa 2 (by omega_arith), qa 3 (by omega_arith)]; exact covers_of_mem hw'
  obtain hcD' : (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint ⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ := by
    rw [q₁, qa 2 (by omega_arith), qa 3 (by omega_arith)]; exact h0'.2.2.1 hw'
  obtain hA := one_argsCr h0 hw
  obtain hA' : ∀ r ∈ crFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp (arg s₀ 2) (arg s₀ 3).toNat, (args s₀' na).Disjoint r := by
    have := one_argsCr h0' hw'; rwa [est, e4, ← q₀, ← qa 2 (by omega_arith), ← qa 3 (by omega_arith)] at this
  obtain x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (rel_of_ct (crypt_ct L (k8 := BitVec.ofNat 32 (s₀.gpr .r1).toNat) (R := (s₀.gpr .r1).toNat) (D := arg s₀ 2)
        (n := (arg s₀ 3).toNat) (q := 0))
      (fun s h => (cr_wpI L spf hd hwD (h0.2.2.1 hw) hA hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (cr_wpI L spf' hd' hwD' hcD' hA' hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (cr_wpI L spf hd hwD (h0.2.2.1 hw) hA hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (cr_wpI L spf' hd' hwD' hcD' hA' hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  exact x1.seq x2

theorem oneTag_rel [VG.Proof.Gcm.Arm.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) :
    RelCT isa (fun a b => OF na wi s₀ s₀ a ∧ OF na wi s₀ s₀' b) (oneTag o)
      fun a b => OF na wi s₀ s₀ a ∧ OF na wi s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  obtain L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR : roundsOk s₀ := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ na ∈ s₀.rd := h0.1.2.2.2
  have hin' : args s₀' na ∈ s₀'.rd := h0'.1.2.2.2
  obtain e4 : arg s₀' wi = arg s₀ wi := (qa wi hwi).symm
  obtain est : oSt s₀' wi = oSt s₀ wi := by show arg s₀' wi + _ = arg s₀ wi + _; rw [e4]
  obtain hJ := one_argsJ0 h0
  obtain hJ' : ∀ r ∈ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp, (args s₀' na).Disjoint r := by
    have := one_argsJ0 h0'; rwa [est, e4, ← q₀] at this
  obtain hT := disj_sub (one_argsOt h0 ho) tag_otSub
  obtain hT' : ∀ r ∈ tagFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o, (args s₀' na).Disjoint r := by
    have := disj_sub (one_argsOt h0' ho) tag_otSub; rwa [est, e4, ← q₀] at this
  obtain ag : RelCT isa (fun a b => OF na wi s₀ s₀ a ∧ OF na wi s₀ s₀' b) (.block dataArgs) fun _ _ => True :=
    argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2)
  let D1 : State → State → Prop := fun t₀ s => OF na wi s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 2 ∧
    s.gpr .r5 = arg s₀ 3 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  obtain x1 := rel_wp (F := OF na wi s₀ s₀) (F' := OF na wi s₀ s₀') (G := D1 s₀) (G' := D1 s₀') ag
    (fun s h => da_wpI spf hin hn h)
    (fun s h => WP.mono (da_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by omega_arith)], by rw [y₃, qa 3 (by omega_arith)], y₄⟩)
  obtain hd := one_dataOk h0 (ArgsKeep.refl na s₀)
  obtain hd' : DataOk (oSt s₀ wi) (arg s₀ wi) s₀.sp s₀' (arg s₀ 2) (arg s₀ 3).toNat := by
    have := one_dataOk h0' (ArgsKeep.refl na s₀'); rwa [est, e4, ← q₀, ← qa 2 (by omega_arith), ← qa 3 (by omega_arith)] at this
  obtain x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 2) (n := (arg s₀ 3).toNat) (q := 0) (by decide))
      (fun s h => (abs_wpI L spf hJ hd h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (abs_wpI L spf' hJ' hd' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (abs_wpI L spf hJ hd h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (abs_wpI L spf' hJ' hd' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  let B3 : State → State → Prop := fun t₀ s => OF na wi s₀ t₀ s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 3).toNat % 16)
  obtain x3 := rel_wp (F := OF na wi s₀ s₀) (F' := OF na wi s₀ s₀') (G := B3 s₀) (G' := B3 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b3_wpI spf hin hn h)
    (fun s h => WP.mono (b3_wpI spf' hin' hn h) fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, qa 3 (by omega_arith)]⟩)
  obtain x4 := rel_wp (F := B3 s₀) (F' := B3 s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (arg s₀ 3).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => fl_wpI L spf hJ (Nat.mod_lt _ (by decide)) h.1 h.2)
    (fun s h => fl_wpI L spf' hJ' (Nat.mod_lt _ (by decide)) h.1 h.2)
  obtain x5 := rel_wp (F := OF na wi s₀ s₀) (F' := OF na wi s₀ s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b4_wpI spf hin hn h) (fun s h => b4_wpI spf' hin' hn h)
  obtain x6 := rel_wp (F := OF na wi s₀ s₀) (F' := OF na wi s₀ s₀') (G := OF na wi s₀ s₀) (G' := OF na wi s₀ s₀')
    (rel_of_ct (tag_ct L ho hR) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩))
    (fun s h => tg_wpI L spf ho hT hR h) (fun s h => tg_wpI L spf' ho hT' hR h)
  exact x1.seq (x2.seq (x3.seq (x4.seq (x5.seq x6))))

end

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_seal` and `vg_aes_gcm_open` are constant time

Untrusted: everything here is checked by Lean. `open` decrypts only if the
tags are equal, which its contract makes public: the comparison, done
without a branch, is related across the runs by what each run computes
(`rel_ghost`, `open_head`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

theorem one_entry_agree {n wi : Nat} {rs : List Reg} (hrs : ∀ r ∈ rs, r = .r0 ∨ r = .r1 ∨ r = .r2 ∨ r = .r3)
    {s₀ s₀' : State} (h0 : onePre n wi s₀) (h0' : onePre n wi s₀') (hq : onePub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (argTaint rs (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 qa (one_hw h0) (one_hw h0') fun r hr => ?_
  rcases hrs r hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : sealArm.pre s₀) (h0' : sealArm.pre s₀') (hq : sealArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «seal» fun _ _ => True := by
  obtain h6 : onePre 6 5 s₀ := sealPreArm.one h0
  obtain h6' : onePre 6 5 s₀' := sealPreArm.one h0'
  have hq6 : onePub 6 s₀ s₀' := hq
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  obtain L := oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨-, hwr', -, -, -, -, -, -, -, -, -, -, -, -, tW', -, -, -, -, -, -, -, -, -, -, -, -, fT', -⟩ := h0'
  obtain a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SO1 6 5 s₀) (G' := SO1 6 5 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 6)) (c := .block (oneEntry 20))
    (one_entry_agree (by simp) h6 h6' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact one1_wp h6 (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact one1_wp h6' (by decide) (by decide) fun _ h => h)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 5
  obtain c := rel_agree (F := OF 6 5 s₀ s₀) (F' := OF 6 5 s₀ s₀') (G := W) (G' := W) (argTaint [.r11] (4 * 6))
    (c := .block tagOut)
    (fun s s' ⟨_, he, hk⟩ ⟨_, he', hk'⟩ => hk.agree hk' q₀ spf qa (one_hw h6) (one_hw h6') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (by decide) he hk spf h6.1.2.2.2 (by rw [hwr]; simp) fT
      (tW.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (by decide) he hk spf' h6'.1.2.2.2 (by rw [hwr']; simp) fT'
      (by rw [qa 5 (by decide)]; exact tW'.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  obtain d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2]) hB
  exact a.seq ((oneAad_rel h6 h6' hq6 (by decide) (by decide)).seq ((oneCrypt_rel h6 h6' hq6 (by decide) (by decide)
    (by rw [hwr]; simp) (by rw [hwr']; simp)).seq
    ((oneTag_rel h6 h6' hq6 (by decide) (by decide) (.inl rfl)).seq (c.seq d))))

theorem seal_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `open` -/

theorem openRes_isSome {to : Bool} {t : State} (hok : Spec.Gcm.tagLenOk (arg t (oLi to)).toNat = true) :
    (openResG to t).isSome = decide (openTagOk to t) := by
  simp only [openResG, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  by_cases h : openTagOk to t
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), decide_eq_true h]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), decide_eq_false h]; rfl

section
variable {c st w sp : BitVec 32} {R : Nat} {t₀ : State}

theorem blk_wp {na : Nat} {s : State} (h : P7n na c st w sp R t₀ s) :
    WP isa (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) s (FT na t₀ c st w sp R) := by
  obtain ⟨⟨k7, he, hk⟩, -⟩ := h
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  exact ⟨_, he.set7 rfl (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_subFlags, gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem mov07_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (.reg .r7)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

theorem daTo_wpI (hf : t₀.sp.toNat + 4 * oNa true ≤ 2 ^ 32) (hin : args t₀ (oNa true) ∈ t₀.rd) {s : State}
    (hs : FT (oNa true) t₀ c st w sp R s) :
    WP isa (.block dataArgsTo) s fun s' => FT (oNa true) t₀ c st w sp R s' ∧
      s'.gpr .r4 = arg t₀ 2 ∧ s'.gpr .r5 = arg t₀ 3 ∧ s'.gpr .r6 = arg t₀ 4 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨s', run, h4, h5, h6, g, k⟩ := dataArgsTo_run hk hf hin
  exact WP.of_runBlock ⟨s', run, ⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, h4, h5, h6⟩

end

/-- The source decrypted to the destination, in both runs. -/
theorem oneCryptTo_rel {s₀ s₀' : State} (ho : OPre true s₀) (ho' : OPre true s₀')
    (hq : onePub (oNa true) s₀ s₀') :
    RelCT isa (fun a b => OF (oNa true) (oWi true) s₀ s₀ a ∧ OF (oNa true) (oWi true) s₀ s₀' b) (oneCryptG true)
      fun a b => OF (oNa true) (oWi true) s₀ s₀ a ∧ OF (oNa true) (oWi true) s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq
  have h0 := ho.one
  have h0' := ho'.one
  have L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa true) ∈ s₀.rd := h0.1.2.2.2
  have hin' : args s₀' (oNa true) ∈ s₀'.rd := h0'.1.2.2.2
  have e4 : arg s₀' (oWi true) = arg s₀ (oWi true) := (qa (oWi true) (by decide)).symm
  have est : oSt s₀' (oWi true) = oSt s₀ (oWi true) := by show arg s₀' _ + _ = arg s₀ _ + _; rw [e4]
  let D1 : State → State → Prop := fun t₀ s => OF (oNa true) (oWi true) s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 2 ∧
    s.gpr .r5 = arg s₀ 3 ∧ s.gpr .r6 = arg s₀ 4
  have x1 := rel_wp (F := OF (oNa true) (oWi true) s₀ s₀) (F' := OF (oNa true) (oWi true) s₀ s₀')
    (G := D1 s₀) (G' := D1 s₀')
    (argsR (by decide) q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => daTo_wpI spf hin h)
    (fun s h => WP.mono (daTo_wpI spf' hin' h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by decide)], by rw [y₃, qa 3 (by decide)], by rw [y₄, qa 4 (by decide)]⟩)
  have eR : (s₀'.gpr .r1).toNat = (s₀.gpr .r1).toNat := by rw [q₂]
  have ek : ∀ t : State, (t.gpr .r1).toNat = (s₀.gpr .r1).toNat →
      t.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat := fun t e => by rw [← e]; simp
  have run : ∀ {t : State} (hot : OPre true t) (ec : t.gpr .r0 = s₀.gpr .r0)
      (ew : arg t (oWi true) = arg s₀ (oWi true)) (esp : t.sp = s₀.sp) (eR : (t.gpr .r1).toNat = (s₀.gpr .r1).toNat)
      (eS : arg t 2 = arg s₀ 2) (eT : arg t 4 = arg s₀ 4) (en : arg t 3 = arg s₀ 3) {s : State} (h : D1 t s),
      CrMG true (s₀.gpr .r0) (oSt s₀ (oWi true)) (arg s₀ (oWi true)) s₀.sp (BitVec.ofNat 32 (s₀.gpr .r1).toNat)
        (s₀.gpr .r1).toNat (arg s₀ 2) (arg s₀ 4) (arg s₀ 3).toNat 0 0 s ∧
      WP isa cryptTo s (OF (oNa true) (oWi true) s₀ t) := fun {t} hot ec ew esp eR eS eT en s h =>
    have r := cryptTo_in hot ec ew (by show arg t _ + _ = arg s₀ _ + _; rw [ew]) esp (ek t eR) eR eS eT
      (by rw [en]) h.1.choose_spec.1 h.1.choose_spec.2 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2 (Spec.Gcm.blockAt s.mem 0)
    ⟨⟨_, _, 0, _, rfl, r.1⟩, WP.mono r.2 fun _ ⟨co, hk⟩ => ⟨_, co.env, hk⟩⟩
  have r₀ := @run s₀ ho rfl rfl rfl rfl rfl rfl rfl
  have r₁ := @run s₀' ho' q₁.symm e4 q₀.symm eR (qa 2 (by decide)).symm (qa 4 (by decide)).symm
    (qa 3 (by decide)).symm
  have x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := OF (oNa true) (oWi true) s₀ s₀)
    (G' := OF (oNa true) (oWi true) s₀ s₀')
    (rel_of_ct (cryptTo_ct L) (fun s h => (r₀ h).1) (fun s h => (r₁ h).1))
    (fun s h => (r₀ h).2) (fun s h => (r₁ h).2)
  exact x1.seq x2

/-- The body of `open` (`to = false`) and `open_to`, up to their ends, in
both runs: whether the tags are equal is public. -/
theorem openBody_rel [VG.Proof.Gcm.Arm.GhashLaw] {to : Bool} {s₀ s₀' : State} (ho : OPre to s₀) (ho' : OPre to s₀')
    (hq6 : onePub (oNa to) s₀ s₀') (hres : (openResG to s₀).isSome = (openResG to s₀').isSome)
    {Q : State → State → Prop} (hend : RelCT isa (fun a b => OB to s₀ a ∧ OB to s₀' b) (openEnd to) Q) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (openG to) Q := by
  have h6 := ho.one
  have h6' := ho'.one
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  obtain L := oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ (oNa to) ∈ s₀.rd := h6.1.2.2.2
  have hin' : args s₀' (oNa to) ∈ s₀'.rd := h6'.1.2.2.2
  obtain hn : 5 ≤ oNa to := by cases to <;> decide
  obtain hwi : oWi to < oNa to := by cases to <;> decide
  obtain hli : oLi to < oNa to := by cases to <;> decide
  obtain hti : oTi to < oNa to := by cases to <;> decide
  obtain e4 : arg s₀' (oWi to) = arg s₀ (oWi to) := (qa _ hwi).symm
  obtain h5' : (arg s₀' (oLi to)).toNat = (arg s₀ (oLi to)).toNat := by rw [qa _ hli]
  obtain eT : arg s₀' (oTi to) = arg s₀ (oTi to) := (qa _ hti).symm
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ (oWi to)
  obtain r11 : ∀ {t₀ s : State}, OF (oNa to) (oWi to) s₀ t₀ s → W s := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  let G1 : State → State → Prop := fun t₀ s =>
    SO1 (oNa to) (oWi to) t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg s₀ (oLi to)).toNat
  obtain a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G1 s₀) (G' := G1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * oNa to))
    (c := .block (oneEntry (workOff to) ++ [.ldrSp .r6 (tagLenOff to)]))
    (one_entry_agree (by simp) h6 h6' hq6) (by cases to <;> exact ⟨_, by taint_decide⟩)
    (fun s e => by rw [e]; exact openEntry_wp h6)
    (fun s e => by rw [e]; exact WP.mono (openEntry_wp h6') fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, h5']⟩)
  let G2 : State → State → Prop := fun t₀ s =>
    SO1 (oNa to) (oWi to) t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat
  obtain tl : ∀ {t₀ s : State}, G1 t₀ s → WP isa tagLenOk s (G2 t₀) := fun {t₀ s} ⟨h1, h6r⟩ =>
    WP.mono (tagLenOk_ok h6r (arg s₀ (oLi to)).isLt) fun s' ⟨hz, g, k⟩ => ⟨h1.keep (fun r a _ => g r a) k, hz⟩
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  obtain b := rel_wp (F := G1 s₀) (F' := G1 s₀') (G := G2 s₀) (G' := G2 s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tl h) (fun s h => tl h)
  -- the branches
  let rest6 : Prog isa := .seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.block [])
  let rest5 : Prog isa := .seq (cmp uO) rest6
  let rest4 : Prog isa := .seq (recvAt (tagOff to)) rest5
  let rest3 : Prog isa := .seq (.block [.ldrSp .r6 (tagLenOff to)]) rest4
  let rest2 : Prog isa := .seq (oneTag uO) rest3
  let Z : State → State → Prop := fun t₀ s => s.z = decide (¬openTagOk to t₀)
  obtain mid : RelCT isa (fun a b => G2 s₀ a ∧ G2 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) (openGood to)) fun a b => W a ∧ W b := by
    refine rel_iteQ (!Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat) (fun s h => h.2) (fun s h => h.2)
      (fun _ => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := G2 s₀) (F' := G2 s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => mov0_wp h.1.env.r11) (fun s h => mov0_wp (by rw [h.1.env.r11, e4]))
    · have hok : Spec.Gcm.tagLenOk (arg s₀ (oLi to)).toNat = true := by simpa using hb
      obtain hok' : Spec.Gcm.tagLenOk (arg s₀' (oLi to)).toNat = true := by rw [h5']; exact hok
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      obtain eZ : decide (¬openTagOk to s₀') = decide (¬openTagOk to s₀) := by
        rw [decide_not, decide_not, ← openRes_isSome hok, ← openRes_isSome hok', hres]
      -- what each run reaches: whether the tags are equal
      obtain pfx : ∀ {t₀ s : State}, OPre to t₀ → Spec.Gcm.tagLenOk (arg t₀ (oLi to)).toNat = true →
          SO1 (oNa to) (oWi to) t₀ s → WP isa (.seq oneAad rest2) s (Z t₀) := fun ht hk h2 =>
        open_head ht h2 hk (T := .block []) fun s₈ om => WP.block_nil om.z
      obtain y1 := rel_ghost (R := rest2) (Z := Z s₀) (Z' := Z s₀') (oneAad_rel h6 h6' hq6 hn hwi)
      obtain y2 := rel_ghost (R := rest3) (Z := Z s₀) (Z' := Z s₀')
        (oneTag_rel h6 h6' hq6 hn hwi (o := uO) (.inr rfl))
      let P6s : State → State → Prop := P6n (oNa to) (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp
        (s₀.gpr .r1).toNat (arg s₀ (oLi to)).toNat
      let P7s : State → State → Prop := P7n (oNa to) (s₀.gpr .r0) (oSt s₀ (oWi to)) (arg s₀ (oWi to)) s₀.sp
        (s₀.gpr .r1).toNat
      obtain y3 := rel_ghost (R := rest4) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree (F := OF (oNa to) (oWi to) s₀ s₀) (F' := OF (oNa to) (oWi to) s₀ s₀')
          (G := P6s s₀) (G' := P6s s₀')
          (argTaint [] (4 * oNa to)) (c := .block [.ldrSp .r6 (tagLenOff to)])
          (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (one_hw h6) (one_hw h6') (rs := [])
            (by simp)) (by cases to <;> exact ⟨_, by taint_decide⟩)
          (fun s h => ld6n_wp (tagLenOff_lt to) hli (tagLenOff_eq to) spf hin rfl h)
          (fun s h => ld6n_wp (tagLenOff_lt to) hli (tagLenOff_eq to) spf' hin' h5' h))
      obtain hD : ∀ {d k : Nat}, d + k ≤ 2560 →
          (args s₀ (oNa to)).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h6.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      obtain hD' : ∀ {d k : Nat}, d + k ≤ 2560 →
          (args s₀' (oNa to)).Disjoint ⟨State.addr (arg s₀ (oWi to)) + BitVec.ofNat 64 d, k⟩ := fun hd => by
        rw [← e4]; exact (h6'.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      obtain y4 := rel_ghost (R := rest5) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree (F := P6s s₀) (F' := P6s s₀') (G := P6s s₀) (G' := P6s s₀')
          (argTaint [.r6, .r11] (4 * oNa to)) (c := recvAt (tagOff to))
          (fun s s' h h' => h.1.choose_spec.2.agree h'.1.choose_spec.2 q₀ spf qa (one_hw h6) (one_hw h6')
            fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · rw [h.2, h'.2]
              · rw [r11 h.1, r11 h'.1]) (by cases to <;> exact ⟨_, by taint_decide⟩)
          (fun s h => recvn_wp L (tagOff_lt to) hti (tagOff_eq to) spf hin (hD (by decide)) ho.trd ho.fT
            (ho.tW.sub_right (Lay.wSub (by decide))) t1 t16 h)
          (fun s h => recvn_wp L (tagOff_lt to) hti (tagOff_eq to) spf' hin' (hD' (by decide))
            (by rw [← h5']; exact ho'.trd) (by rw [← h5']; exact ho'.fT)
            (by rw [← h5', ← e4]; exact ho'.tW.sub_right (Lay.wSub (by decide))) t1 t16 h))
      obtain ⟨_, c5⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp uO) h).isSome = true :=
        ⟨_, by taint_decide⟩
      obtain y5 := rel_ghost (R := rest6) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp (F := P6s s₀) (F' := P6s s₀') (G := P7s s₀) (G' := P7s s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h.2.2]
            · rw [r11 h.1.1, r11 h.2.1]) c5)
          (fun s h => cmpn_wp L spf (.inr rfl) (hD (by decide)) t1 t16 h)
          (fun s h => cmpn_wp L spf' (.inr rfl) (hD' (by decide)) t1 t16 h))
      obtain ⟨_, c6⟩ : ∃ h, (taint.check (Taint.ofRegs [])
          (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
      obtain y6 := rel_ghost (R := .block []) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp (F := P7s s₀) (F' := P7s s₀')
          (G := OF (oNa to) (oWi to) s₀ s₀) (G' := OF (oNa to) (oWi to) s₀ s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp at hr) c6)
          (fun s h => blk_wp h) (fun s h => blk_wp h))
      -- the data decrypted only if the tags are equal, which is public
      obtain cr : RelCT isa (fun a b => OF (oNa to) (oWi to) s₀ s₀ a ∧ OF (oNa to) (oWi to) s₀ s₀' b)
          (oneCryptG to) fun a b => OF (oNa to) (oWi to) s₀ s₀ a ∧ OF (oNa to) (oWi to) s₀ s₀' b := by
        cases to
        · exact oneCrypt_rel h6 h6' hq6 hn hwi ho.dst ho'.dst
        · exact oneCryptTo_rel ho ho' hq6
      obtain y7 : RelCT isa (fun a b => (OF (oNa to) (oWi to) s₀ s₀ a ∧ WP isa (.block []) a (Z s₀)) ∧
          (OF (oNa to) (oWi to) s₀ s₀' b ∧ WP isa (.block []) b (Z s₀'))) (.ite .eq (.block []) (oneCryptG to))
          fun a b => W a ∧ W b :=
        rel_iteQ (decide (¬openTagOk to s₀)) (fun s h => wp_nil h.2) (fun s h => (wp_nil h.2).trans eZ)
          (fun _ => RelCT.block_nil fun x y h => ⟨r11 h.1.1, r11 h.2.1⟩)
          (fun _ => cr.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => ⟨r11 h.1, r11 h.2⟩)
      obtain ⟨_, c8⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block [.mov .r0 (.reg .r7)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      obtain y8 := rel_wp (F := W) (F' := W) (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) c8)
        (fun s h => mov07_wp h) (fun s h => mov07_wp h)
      refine RelCT.mono (y1.seq (y2.seq (y3.seq (y4.seq (y5.seq (y6.seq (y7.seq y8))))))) (fun s s' h => ?_)
        fun _ _ h => h
      exact ⟨⟨h.1.1, pfx ho hok h.1.1⟩, ⟨h.2.1, pfx ho' hok' h.2.1⟩⟩
  -- what each run computes
  obtain mid' := rel_ghost (R := .block []) (Z := OB to s₀) (Z' := OB to s₀') mid
  refine a.seq (b.seq ((RelCT.mono mid' (fun s s' h => ⟨⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩)
    fun _ _ h => ⟨wp_nil h.1.2, wp_nil h.2.2⟩).seq hend))
  · exact WP.seq (WP.mono (openMid_wp ho h.1.1 h.1.2) fun _ h => WP.block_nil h)
  · exact WP.seq (WP.mono (openMid_wp ho' h.2.1 (by rw [h.2.2, h5'])) fun _ h => WP.block_nil h)

theorem open_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : openArm.pre s₀) (h0' : openArm.pre s₀') (hq : openArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «open» fun _ _ => True := by
  obtain ho := openPreArm.oPre h0
  obtain ho' := openPreArm.oPre h0'
  have hR : roundsOk s₀ := ho.one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain e4 : arg s₀' 6 = arg s₀ 6 := (hq.1.2.2.2.2.2 6 (by decide)).symm
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  obtain d := RelCT.taint (A := taint) (P := fun s₁ s₂ => OB false s₀ s₁ ∧ OB false s₀' s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.env.choose_spec.r11, h.2.env.choose_spec.r11]; exact e4.symm) hB
  exact openBody_rel ho ho' hq.1 (hq.2 hR) d

theorem open_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa openArm.pre openArm.pub «open» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm
