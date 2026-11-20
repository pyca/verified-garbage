module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareFn
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareZ
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareAvx.Ok
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Preparing AES-GCM's key context on x86-64, without secret residue

Each implementation of `vg_aes_gcm_prepare` and `vg_aes_gcm_wipe_prepared`,
followed by the clearing of every register it may write
(`Impl.Gcm.X86_64.Fn`): none has stack. Their postconditions read the memory
on return only within the context (`prepareOut`, `wipePreparedOut`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.PrepareScrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem bytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this])

theorem readW_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d w : Nat} (hn : d + w / 8 ≤ L) :
    m₂.readW (p + BitVec.ofNat 64 d) w = m₁.readW (p + BitVec.ofNat 64 d) w :=
  Mem.readW_congr fun i hi => by
    rw [VG.Offset.add_add]
    exact agree_le h hn _ (by omega_using [hi])

theorem ctxH_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : 256 ≤ L) :
    Spec.Gcm.ctxH m₂ p = Spec.Gcm.ctxH m₁ p := by
  simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
  rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl, bytesAt_of h (by omega_using [hn])]

theorem powerCount_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : 1032 ≤ L) :
    Spec.Gcm.powerCount m₂ p = Spec.Gcm.powerCount m₁ p := by
  simp only [Spec.Gcm.powerCount]
  rw [show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, readW_of h (by omega_using [hn])]

theorem preparedRepr_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : 1032 ≤ L)
    (hr : Spec.Gcm.PreparedRepr m₁ p) : Spec.Gcm.PreparedRepr m₂ p := by
  obtain ⟨h16, h48⟩ := hr
  simp only [Spec.Gcm.PreparedRepr, powerCount_of h hn]
  refine ⟨fun hc k hk => ?_, fun hc k hk => ?_⟩
  · rw [readW_of h (by omega_using [hn, hk]), readW_of h (by omega_using [hn, hk]), ctxH_of h (by omega_using [hn])]
    exact h16 hc k hk
  · rw [readW_of h (by omega_using [hn, hk]), readW_of h (by omega_using [hn, hk]), ctxH_of h (by omega_using [hn])]
    exact h48 hc k hk

end

/-! ## The postcondition -/

theorem prepareOut (stack : Nat) :
    PostOut (Spec.Gcm.prepareContract X86_64.abi stack) (Spec.Gcm.prepareSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx], _ =>
      simp only [Spec.Gcm.prepareSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
      change Spec.Aes.bytesAt m₁ ctx 256 = _ ∧ Spec.Gcm.PreparedRepr m₁ ctx at h
      change Spec.Aes.bytesAt m₂ ctx 256 = _ ∧ Spec.Gcm.PreparedRepr m₂ ctx
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, preparedRepr_of hb (by decide) h2⟩
      have := bytesAt_of hb (d := 0) (n := 256) (by decide)
      simp only [BitVec.add_zero] at this
      rw [this]
      exact h1

theorem wipePreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.wipePreparedContract X86_64.abi stack) (Spec.Gcm.wipePreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx], _ =>
      simp only [Spec.Gcm.wipePreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
      change Spec.Aes.bytesAt m₁ ctx (Spec.Gcm.wipePreparedLen m ctx) = _ at h
      change Spec.Aes.bytesAt m₂ ctx (Spec.Gcm.wipePreparedLen m ctx) = _
      have hl : Spec.Gcm.wipePreparedLen m ctx ≤ 1032 := by
        unfold Spec.Gcm.wipePreparedLen; split
        · decide
        · split <;> decide
      have := bytesAt_of hb (d := 0) (n := Spec.Gcm.wipePreparedLen m ctx) (by simp only [Elem.size]; omega_using [hl])
      simp only [BitVec.add_zero] at this
      rw [this]
      exact h

/-! ## The registrations -/

/-- `vg_aes_gcm_prepare_vpclmul_avx512` as emitted (`Impl.Gcm.X86_64.Fn.prepareZ`) meets its contract in
constant time and returns without secret residue. -/
theorem z_scrubbed :
    VerifiedScrubbed target Impl.Gcm.X86_64.Fn.prepareZ (Spec.Gcm.prepareApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.prepareApi) { code := Impl.Gcm.X86_64.Flag.prepareFlagged 48 Impl.Gcm.X86_64.PrepareZ.prepare, verified := Proof.Gcm.X86_64.PrepareZ.prepareFlagged_verified } .avx
    (prepareOut _)

/-- `vg_aes_gcm_prepare_vpclmul_avx512`. -/
def zReg : Registration Spec.Gcm.prepareApi X86_64.target where
  suffix := "_vpclmul_avx512"
  code := Impl.Gcm.X86_64.Fn.prepareZ
  verified := .scrubbed z_scrubbed
  spSafe := scrubKs_spSafe (by lit_decide)

/-- `vg_aes_gcm_prepare_vpclmul` as emitted (`Impl.Gcm.X86_64.Fn.prepare16`) meets its contract in
constant time and returns without secret residue. -/
theorem p16_scrubbed :
    VerifiedScrubbed target Impl.Gcm.X86_64.Fn.prepare16 (Spec.Gcm.prepareApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.prepareApi) { code := Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.Prepare16.prepare16, verified := Proof.Gcm.X86_64.Prepare16.prepareFlagged_verified } .avx
    (prepareOut _)

/-- `vg_aes_gcm_prepare_vpclmul`. -/
def p16Reg : Registration Spec.Gcm.prepareApi X86_64.target where
  suffix := "_vpclmul"
  code := Impl.Gcm.X86_64.Fn.prepare16
  verified := .scrubbed p16_scrubbed
  spSafe := scrubKs_spSafe (by lit_decide)

/-- `vg_aes_gcm_prepare_pclmul_avx` as emitted (`Impl.Gcm.X86_64.Fn.prepareAvx`) meets its contract in
constant time and returns without secret residue. -/
theorem avx_scrubbed :
    VerifiedScrubbed target Impl.Gcm.X86_64.Fn.prepareAvx (Spec.Gcm.prepareApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.prepareApi) { code := Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.PrepareAvx.prepare16, verified := Proof.Gcm.X86_64.PrepareAvx.prepareFlagged_verified } .avx
    (prepareOut _)

/-- `vg_aes_gcm_prepare_pclmul_avx`. -/
def avxReg : Registration Spec.Gcm.prepareApi X86_64.target where
  suffix := "_pclmul_avx"
  code := Impl.Gcm.X86_64.Fn.prepareAvx
  verified := .scrubbed avx_scrubbed
  spSafe := scrubKs_spSafe (by lit_decide)

/-- `vg_aes_gcm_prepare` as emitted (`Impl.Gcm.X86_64.Fn.prepareAbsent`) meets its contract in
constant time and returns without secret residue. -/
theorem absent_scrubbed :
    VerifiedScrubbed target Impl.Gcm.X86_64.Fn.prepareAbsent (Spec.Gcm.prepareApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.prepareApi) { code := Impl.Gcm.X86_64.Flag.prepareAbsent, verified := Proof.Gcm.X86_64.Prepare.absent_verified } .sse
    (prepareOut _)

/-- `vg_aes_gcm_prepare`. -/
def absentReg : Registration Spec.Gcm.prepareApi X86_64.target where
  suffix := ""
  code := Impl.Gcm.X86_64.Fn.prepareAbsent
  verified := .scrubbed absent_scrubbed
  spSafe := scrubKs_spSafe (by lit_decide)

/-- `vg_aes_gcm_wipe_prepared` as emitted, with AVX if `avx`
(`Impl.Gcm.X86_64.Fn.wipe`), meets its contract in constant time and returns
without secret residue. -/
theorem wipe_scrubbed (avx : Bool) :
    VerifiedScrubbed target (Impl.Gcm.X86_64.Fn.wipe avx) (Spec.Gcm.wipePreparedApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.wipePreparedApi)
    { code := Impl.Gcm.X86_64.Flag.wipe avx, verified := Proof.Gcm.X86_64.Prepare.wipe_verified avx
      spSafe := by cases avx <;> lit_decide } _ (wipePreparedOut _)
    (hs := by cases avx <;> lit_decide)

/-- `vg_aes_gcm_wipe_prepared`, with AVX if `avx`. -/
def wipeReg (avx : Bool) : Registration Spec.Gcm.wipePreparedApi X86_64.target where
  suffix := if avx then "_avx" else ""
  code := Impl.Gcm.X86_64.Fn.wipe avx
  verified := .scrubbed (wipe_scrubbed avx)
  spSafe := scrubKs_spSafe (by cases avx <;> lit_decide)

end VG.Proof.Gcm.X86_64.PrepareScrub
